module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JBir = Sawja_pack.JBir
module QID = QualifiedIdentity

open Core

module Instr = struct
  type t = QID.t * JBir.instr

  let equal (a, _) (b, _) = a = b
  let hash (id, _) = QID.to_string "/" id |> String.hash
  let compare (a, _) (b, _) =
    String.compare (QID.to_string "/" a) (QID.to_string "/" b)
end

module Branch = struct
  type t = Goto
         | True
         | False

  let hash = function
    | False -> 0
    | True -> 1
    | Goto -> 2
  let equal a b = a = b
  let compare a b = (hash a) - (hash b)
  let default = Goto
  let to_string = function
    | Goto -> "goto"
    | True -> "true"
    | False -> "false"
end

include Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Instr)(Branch)


let cms_to_qid cms =
  let (jclass, jmethod) = JBasics.cms_split cms in
  QID.QID [JBasics.cn_name jclass; JBasics.ms_name jmethod]


let cms_to_instrs program cms =
  let open JProgram in
  let open Javalib_pack.Javalib in

  let (entry_class, entry_method) =
    JBasics.ClassMethodMap.find cms program.parsed_methods in

  match entry_method.cm_implementation with
    | Native -> Error `Native
    | Java java -> let code = Lazy.force java in Ok (JBir.code code, code)


let append_instrs
      (prefix: QID.t)
      (instrs: JBir.instr array)
      (start_graph: t)
  =
  let collect_vertices i graph instr =
    let path = QID.specify prefix (string_of_int i) in
    let vertex = (path, instr) in

    let dest_i = match instr with
      | JBir.Goto target -> [(Branch.Goto, target)]
      | JBir.Ifd (_, target) -> [(Branch.False, i + 1); (Branch.True, target)]
      | JBir.Throw _ -> []
      | JBir.Return _ -> []
      | _ -> [(Branch.Goto, i + 1)]
    in
    let connect_vertices graph (br, j) =
      let instr = Array.nget instrs j in
      let v = (QID.specify prefix (string_of_int j), instr) in
      add_edge_e graph (E.create vertex br v)
    in

    List.fold dest_i ~init:graph ~f:connect_vertices
  in
  Array.foldi instrs ~init:start_graph ~f:collect_vertices


let squash_gotos (graph: t) =
  let rec find_nongoto = function
    | (_, JBir.Goto _) as v ->
       succ graph v |> List.hd |> Option.bind ~f:find_nongoto
    | found -> Some found
  in
  let remove_gotos ((v: V.t), (e: E.label), (v': V.t)) (out: t) =
    match v with
    | (_, JBir.Goto _) -> out
    | _ ->
       (* walk the graph until we don't have a goto statement *)
       let nongoto = match find_nongoto v' with
         | Some g -> g
         | None -> failwith "Goto to unknown loc"
       in
       add_edge_e out (E.create v e nongoto)
  in
  fold_edges_e remove_gotos graph empty


let build_graph
      (program: JBir.t JProgram.program)
      (method_sig: JBasics.class_method_signature)
  =
  let (instrs, code) = match cms_to_instrs program method_sig with
    | Error `Native -> failwith "Cannot analyze native methods!"
    | Ok instrs -> instrs
  in
  append_instrs (cms_to_qid method_sig) instrs empty
  |> squash_gotos


let unimplemented () = failwith "unimplemented"


let ( $:: ) a b = Ir.ExprCons (a, b)


let var_name var =
  let _ = Printf.printf "var_name: %s\n" (JBir.var_name var) in
  let _ = Printf.printf "var_name_g: %s\n" (JBir.var_name_g var) in
  let _ = Printf.printf "var_name_debug: %s\n" (Option.value (JBir.var_name_debug var) ~default:"No debug name.") in
  JBir.var_name_debug var
  |> Option.value ~default:(JBir.var_name var)


let java_to_kind = function
  | `Bool -> Ir.Bool
  | `Int2Bool
  | `Byte
  | `Char
  | `Long
  | `Short
  | `Int -> Ir.Int
  | `Float
  | `Double -> Ir.Real


let java_to_var
      (vartable: (int * int * string * JBasics.value_type * int) list)
      (value_type: JBasics.value_type option)
      (var: JBir.var)
  =
  let name = var_name var in
  let table = List.find vartable ~f:(fun (_, _, n, _, _) -> n = name) in
  let kind =
    (match (table, value_type) with
     | (Some (_, _, _, (JBasics.TBasic t), _), _) -> java_to_kind t
     | (Some (_, _, _, (JBasics.TObject _), _), _) -> unimplemented ()
     | (None, Some (JBasics.TBasic t)) -> java_to_kind t
     | (None, Some (JBasics.TObject _)) -> unimplemented ()
     | (None, None) -> failwith (Printf.sprintf "No type info for var: %s" name)
    )
  in
  let name = var_name var in
  (Ir.Var (Ir.Free (name, kind)), kind)


let rec java_to_expr vartable = function
  | JBir.Const const ->
     (match const with
      | `Double real -> (Ir.LReal real, Ir.Real)
      | `Float real -> (Ir.LReal real, Ir.Real)
      | `Int integer -> (Ir.LInt (Int32.to_int_exn integer), Ir.Int)
      | `Long integer -> (Ir.LInt (Int64.to_int_exn integer), Ir.Int)
      | `ANull
      | `Class _
      | `String _ -> unimplemented ()
     )
  | JBir.Var (value_type, var) -> java_to_var vartable (Some value_type) var
  | JBir.Unop (op, expr) ->
     let (ir_expr, t) = java_to_expr vartable expr in
     (match op with
      | JBir.Neg _ -> (Ir.Not $:: ir_expr, t)
      | JBir.ArrayLength
      | JBir.InstanceOf _
      | JBir.Cast _
      | JBir.Conv _ -> unimplemented ()
     )
  | JBir.Binop (op, expr_a, expr_b) ->
     let (ir_expr_a, _) = java_to_expr vartable expr_a in
     let (ir_expr_b, _) = java_to_expr vartable expr_b in
     let (ir_op, kind) = match op with
      | JBir.Add basic_type -> let t = java_to_kind basic_type in (Ir.Add t, t)
      | JBir.Sub basic_type -> let t = java_to_kind basic_type in (Ir.Sub t, t)
      | JBir.Mult basic_type -> let t = java_to_kind basic_type in (Ir.Mul t, t)
      | JBir.Div basic_type -> let t = java_to_kind basic_type in (Ir.Mul t, t)
      | JBir.Rem basic_type -> let t = java_to_kind basic_type in (Ir.Mod t, t)
      | JBir.IShl
      | JBir.IShr
      | JBir.IAnd
      | JBir.IOr
      | JBir.IXor
      | JBir.IUshr
      | JBir.LShl
      | JBir.LShr
      | JBir.LAnd
      | JBir.LOr
      | JBir.LXor
      | JBir.LUshr
      | JBir.CMP _
      | JBir.ArrayLoad _ -> unimplemented ()
     in
     (ir_op $:: ir_expr_a $:: ir_expr_b, kind)
  | JBir.Field _ -> unimplemented ()
  | JBir.StaticField _ -> unimplemented ()


let java_to_condition vartable cond a b =
  let (expr_a, t_a) = (java_to_expr vartable a) in
  let (expr_b, t_b) = (java_to_expr vartable b) in
  let kind = if t_a = t_b
             then t_a
             else failwith "Mismatched types in condition."
  in
  let op = match cond with
    | `Eq -> Ir.Eql kind
    | `Ge -> Ir.Ge kind
    | `Gt -> Ir.Gt kind
    | `Le -> Ir.Le kind
    | `Lt -> Ir.Lt kind
    | `Ne -> Ir.Distinct kind
  in
  op $:: expr_a $:: expr_b


let instr_to_expr vartable = function
  | JBir.AffectVar (var, expr) ->
     let (irvar, t_a) = java_to_var vartable None var in
     let (irexpr, t_b) = java_to_expr vartable expr in
     let open Sexplib.Std in
     let _ = Printf.printf "instr: %s\n" (JBir.print_instr ~show_type:true (JBir.AffectVar (var, expr))) in
     let _ = Printf.printf "instr_expr: %s\n" (JBir.print_expr ~show_type:true expr) in
     let _ = Printf.printf "var (%s): %s\n" (Ir.sexp_of_kind t_a |> Sexp.to_string) (Ir.sexp_of_expr irvar |> Sexp.to_string) in
     let _ = Printf.printf "expr (%s): %s\n" (Ir.sexp_of_kind t_b |> Sexp.to_string) (Ir.sexp_of_expr irexpr |> Sexp.to_string) in
     let _ = Printf.printf "\n" in
     let kind = if t_a = t_b
                then t_a
                else failwith "Mismatched types in condition."
     in
     Some ((Ir.Eql kind) $:: irvar $:: irexpr)
  | JBir.Ifd ((comp, a, b), i) -> Some (java_to_condition vartable comp a b)
  | JBir.Nop -> None
  (* we're in a graph we can just delete this vertex *)
  | JBir.Goto i -> None
  (* things we haven't translated yet *)
  | JBir.Return _
  | JBir.Throw _
  | JBir.New _
  | JBir.NewArray _
  | JBir.InvokeStatic _
  | JBir.InvokeVirtual _
  | JBir.InvokeNonVirtual _
  | JBir.MonitorEnter _
  | JBir.MonitorExit _
  | JBir.MayInit _
  | JBir.Check _
  | JBir.Formula _
  | JBir.AffectArray _
  | JBir.AffectField _
  | JBir.AffectStaticField _ -> None

