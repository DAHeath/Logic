module Javalib = Javalib_pack.Javalib
module JCode = Javalib_pack.JCode
module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JRTA = Sawja_pack.JRTA
module JBir = Sawja_pack.JBir

open Core

let char_list_to_string cl = String.concat ~sep:"" (List.map cl (String.make 1))

let parse_method_sig text =
  let primitive_type = function
    | 'B' -> Some `Byte
    | 'C' -> Some `Char
    | 'D' -> Some `Double
    | 'F' -> Some `Float
    | 'I' -> Some `Int
    | 'J' -> Some `Long
    | 'S' -> Some `Short
    | 'Z' -> Some `Bool
    | _ -> None
  in

  let rec parse = function
    | [] -> []
    | (c :: cs) ->
       (match (c, primitive_type c) with
        | (_, Some prim) -> Some (JBasics.TBasic prim) :: parse cs
        | ('V', _) -> None :: parse cs
        | ('[', _) -> (match (parse cs) with
                       | ((Some jtype) :: ts) ->
                          Some (JBasics.TObject (JBasics.TArray jtype)) :: ts
                       | _ -> failwith "'[' must be followed by a type.\n"
                      )
        | ('L', _) ->
           let rec class_name = function
             | (n :: ns) when n <> ';' ->
                let (curr_name, leftover) = class_name ns in
                (n :: curr_name, leftover)
             | (n :: ns) when n = ';' -> ([], ns)
             | _ -> failwith "'L' must have an ending ';'.\n"
           in
           let (name_chars, leftover) = class_name cs in
           let name = char_list_to_string name_chars in
           let jclass = JBasics.TClass (JBasics.make_cn name) in
           Some (JBasics.TObject jclass) :: parse leftover
        | _ -> failwith ("Unknown type char: '" ^ (String.make 1 c) ^ "'.\n")
       )
  in

  match String.split_on_chars text ~on:['('; ')'] with
  | [method_name; args; ret_val] ->
     let ret_val_chars = String.to_list ret_val  in
     let args_chars = String.to_list args in
     JBasics.make_ms
       method_name
       (parse args_chars |> List.filter_map ~f:Fn.id)
       (parse ret_val_chars |> List.filter_map ~f:Fn.id |> List.hd)
  | _ -> failwith "Method needs to be formatted name(args)retval\n"


let local_var_table classpath cname =
  let jl_class_or_iface = Javalib.get_class (Javalib.class_path classpath) cname in

  let get_concrete ms jl_method map = match jl_method with
    | Javalib.AbstractMethod _ -> map
    | Javalib.ConcreteMethod ({Javalib.cm_implementation}) ->
      (match cm_implementation with
        | Javalib.Native -> map
        | Javalib.Java lazy_code ->
          let ({JCode.c_local_variable_table}) = Lazy.force lazy_code in
          (match c_local_variable_table with
            | None -> map
            | Some vars -> JBasics.MethodMap.add ms vars map
          )
      )
  in

  match jl_class_or_iface with
    | Javalib.JClass ({Javalib.c_methods}) ->
      JBasics.MethodMap.fold (get_concrete) c_methods (JBasics.MethodMap.empty)
    | _ -> JBasics.MethodMap.empty


let parse classpath classfile method_sig =
  let method_sig = match method_sig with
    | Some text -> parse_method_sig text
    | None -> JProgram.main_signature
  in
  let class_and_method =
    String.chop_suffix classfile ~suffix:".class"
    |> Option.value ~default:classfile
    |> Filename.basename
    |> JBasics.make_cn
    |> fun name -> JBasics.make_cms name method_sig
  in
  let (class_name, _) = JBasics.cms_split class_and_method in
  let vartable = local_var_table classpath class_name in
  let (program, classes) = JRTA.parse_program classpath class_and_method in
  let local_vartable = JBasics.MethodMap.find method_sig vartable in
  let parsed =
    JProgram.map_program2
      (fun _ -> JBir.transform ~bcv:false ~ch_link:false ~formula:false ~formula_cmd:[])
      (Some (fun code pp -> (JBir.pc_ir2bc code).(pp)))
      program
  in
  (parsed, class_and_method, local_vartable)

