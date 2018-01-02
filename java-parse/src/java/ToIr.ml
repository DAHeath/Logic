module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JBir = Sawja_pack.JBir
module QID = QualifiedIdentity

open Core

let var_name var =
  JBir.var_name_debug var
  |> Option.value ~default:(JBir.var_name var)

let qid_var_name loc var prime =
  var
  |> QID.specify (QID.unspecify loc)
  |> (Fn.flip QID.specify) prime

let unimplemented () = failwith "unimplemented"

let ( $:: ) a b = Ir.Apply (a, b)

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
    (loc: QID.t)
    (value_type: JBasics.value_type option)
    (var: JBir.var) =
  let name = qid_var_name loc (var_name var) "0" in
  let kind =
    match value_type with
     | Some (JBasics.TBasic t) -> java_to_kind t
     | Some (JBasics.TObject _) -> unimplemented ()
     | None -> failwith (Printf.sprintf "No type info for var: %s" (QID.as_path name)) in
  Ir.Var (name, kind)

let rename_var f = function
  | Ir.Var (name, t) -> Ir.Var (f name, t)

let rec java_to_expr loc = function
  | JBir.Const const ->
     (match const with
      | `Double r -> Ir.LReal r
      | `Float r  -> Ir.LReal r
      | `Int i    -> Ir.LInt (Int32.to_int_exn i)
      | `Long i   -> Ir.LInt (Int64.to_int_exn i)
      | `ANull
      | `Class _
      | `String _ -> unimplemented ())
  | JBir.Var (value_type, var) -> Ir.V (java_to_var loc (Some value_type) var)
  | JBir.Unop (op, expr) ->
     let ir_expr = java_to_expr loc expr in
     (match op with
      | JBir.Neg _ -> Ir.Not $:: ir_expr
      | JBir.ArrayLength
      | JBir.InstanceOf _
      | JBir.Cast _
      | JBir.Conv _ -> unimplemented ())
  | JBir.Binop (op, a, b) ->
     let ir_op = match op with
      | JBir.Add  t -> let t' = java_to_kind t in Ir.Add t'
      | JBir.Sub  t -> let t' = java_to_kind t in Ir.Sub t'
      | JBir.Mult t -> let t' = java_to_kind t in Ir.Mul t'
      | JBir.Div  t -> let t' = java_to_kind t in Ir.Mul t'
      | JBir.Rem  t -> let t' = java_to_kind t in Ir.Mod t'
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
     let a' = java_to_expr loc a in
     let b' = java_to_expr loc b in
     ir_op $:: a' $:: b'
  | JBir.Field _ -> unimplemented ()
  | JBir.StaticField _ -> unimplemented ()

let java_to_condition loc cond a b =
  let op kind = match cond with
    | `Eq -> Ir.Eql kind
    | `Ge -> Ir.Ge kind
    | `Gt -> Ir.Gt kind
    | `Le -> Ir.Le kind
    | `Lt -> Ir.Lt kind
    | `Ne -> Ir.Nql kind
  in
  let a' = (java_to_expr loc a) in
  let b' = (java_to_expr loc b) in
  op (Ir.form_kind a') $:: a' $:: b'

let instr loc = function
  | JBir.AffectVar (var, expr) ->
     let var' = java_to_var loc None var in
     let expr' = java_to_expr loc expr in
     let var'' = rename_var (fun v -> QID.specify (QID.unspecify v) "1") var' in
     Ir.Assign (var'', expr')

  | JBir.Ifd ((comp, a, b), i) ->
      Ir.Cond (java_to_condition loc comp a b, i)

  | JBir.Nop ->
      Ir.Skip

  | JBir.Goto i ->
      Ir.Cond (Ir.LBool true, i)

  | JBir.InvokeStatic (v, cn, ms, args) ->
    let args = List.map ~f:(java_to_expr loc) args in
    let outs = match v with
    | None -> []
    | Some v' -> [java_to_var loc None v'] in 
    Ir.Call (QID.of_list [JBasics.cn_name cn], args, outs)

  | JBir.InvokeNonVirtual _
  | JBir.InvokeVirtual _
  | JBir.Return _
  | JBir.Throw _
  | JBir.New _
  | JBir.NewArray _
  | JBir.MonitorEnter _
  | JBir.MonitorExit _
  | JBir.MayInit _
  | JBir.Check _
  | JBir.Formula _
  | JBir.AffectArray _
  | JBir.AffectField _
  | JBir.AffectStaticField _ -> Ir.Skip

let proc
  (p: JBir.t JProgram.program)
  (cms: JBasics.class_method_signature) =

  let open JProgram in
  let open Javalib_pack.Javalib in

  let (entry_class, entry_method) =
    JBasics.ClassMethodMap.find cms p.parsed_methods in

  let (is, code) =
    match entry_method.cm_implementation with
    | Native -> failwith "Cannot analyze native methods!"
    | Java java -> let code = Lazy.force java in (JBir.code code, code) in

  Array.mapi (fun i ins ->
    (instr (QID.of_list ["l" ^ string_of_int i]) ins, Sawja_pack.Live_bir.run code i)) is
  |> Array.to_list
