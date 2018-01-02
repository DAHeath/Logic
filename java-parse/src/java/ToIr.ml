module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JBir = Sawja_pack.JBir
module Live = Sawja_pack.Live_bir

let var_name var =
  JBir.var_name_debug var
  |> Option.default (JBir.var_name var)

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

let java_to_var (ty: JBasics.value_type) (var: JBir.var) =
  let name = var_name var in
  let kind =
    match ty with
     | (JBasics.TBasic t) -> java_to_kind t
     | (JBasics.TObject _) -> unimplemented () in
  Ir.Var (name, kind)

let rec java_to_expr = function
  | JBir.Const const ->
     (match const with
      | `Double r -> Ir.LReal r
      | `Float r  -> Ir.LReal r
      | `Int i    -> Ir.LInt (Int32.to_int i)
      | `Long i   -> Ir.LInt (Int64.to_int i)
      | `ANull
      | `Class _
      | `String _ -> unimplemented ())
  | JBir.Var (t, var) -> Ir.V (java_to_var t var)

  | JBir.Unop (op, expr) ->
     let ir_expr = java_to_expr expr in
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
     let a' = java_to_expr a in
     let b' = java_to_expr b in
     ir_op $:: a' $:: b'
  | JBir.Field _ -> unimplemented ()
  | JBir.StaticField _ -> unimplemented ()

let java_to_condition cond a b =
  let op kind = match cond with
    | `Eq -> Ir.Eql kind
    | `Ge -> Ir.Ge kind
    | `Gt -> Ir.Gt kind
    | `Le -> Ir.Le kind
    | `Lt -> Ir.Lt kind
    | `Ne -> Ir.Nql kind
  in
  let a' = (java_to_expr a) in
  let b' = (java_to_expr b) in
  op (Ir.form_kind a') $:: a' $:: b'

let instr = function
  | JBir.AffectVar (var, expr) ->
     let var' = java_to_var (JBir.type_of_expr expr) var in
     let expr' = java_to_expr expr in
     Ir.Assign (var', expr')

  | JBir.Ifd ((comp, a, b), i) ->
      Ir.Cond (java_to_condition comp a b, i)

  | JBir.Nop ->
      Ir.Skip

  | JBir.Goto i ->
      Ir.Cond (Ir.LBool true, i)

  | JBir.InvokeStatic (v, cn, ms, args) ->
    let args = List.map java_to_expr args in
    let outs = match (v, JBasics.ms_rtype ms) with
    | (Some v', Some t) -> [java_to_var t v']
    | _ -> [] in
    Ir.Call (JBasics.cn_name cn, args, outs)

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
    (instr ins, List.map var_name (Live.Env.elements (Live.run code i)))) is
  |> Array.to_list
