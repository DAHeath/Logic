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

(**
 * Convert a single JBir instruction to the unstructured IR.
 * There are three entries which are maintained: The list of instructions themselves
 * (annotated with live variable names) an offset list, and a called procedure list.
 *
 * The offset list allows jump instructions to be renumbered to
 * account for when more unstructured ir instructions are generated than there were
 * JBir instructions originally.
 * The offset list is an ordered list of instructions which generate an additional
 * instruction. To convert a jump, add 1 to the jump target for each entry in the
 * offset list which is less than the jump target.
 *)
let instr (is, offs, called) (instruction, loc, live) = match instruction with
  | JBir.AffectVar (var, expr) ->
      let var' = java_to_var (JBir.type_of_expr expr) var in
      let expr' = java_to_expr expr in
      (is @ [Ir.Assign (var', expr'), live], offs, called)

  | JBir.Ifd ((comp, a, b), i) ->
      (is @ [Ir.Cond (java_to_condition comp a b, i), live], offs, called)

  | JBir.Goto i ->
      (is @ [Ir.Cond (Ir.LBool true, i), live], offs, called)

  | JBir.InvokeStatic (v, cn, ms, args) ->
      let args = List.map java_to_expr args in
      let outs = match (v, JBasics.ms_rtype ms) with
      | (Some v', Some t) -> [java_to_var t v']
      | _ -> [] in
      (is @ [Ir.Call (JBasics.ms_name ms, args, outs), live], offs, JBasics.make_cms cn ms :: called)

  | JBir.Return e ->
      (match e with
        | None -> (is @ [Ir.Done, live], offs, called)
        | Some e ->
            let e' = java_to_expr e in
            (is @
              [ Ir.Assign (Ir.Var ("__RESULT__", Ir.form_kind e'), e'), live
              ; Ir.Done, ("__RESULT__" :: live)
              ], offs @ [loc], called))

  | JBir.Nop
  | JBir.InvokeNonVirtual _
  | JBir.InvokeVirtual _
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
  | JBir.AffectStaticField _ -> (is @ [Ir.Skip, live], offs, called)

(**
 * Calculate the adjustment required to convert the jump instruction target.
 *)
let rec adjust off i = match off with
  | [] -> 0
  | (j::rest) -> if i > j then 1 + adjust rest i else 0

(**
 * Renumber all jump instructions in the instruction list using the offset list.
 *)
let renumber off = function
  | Ir.Jump i -> Ir.Jump (i + adjust off i)
  | Ir.Cond (f, i) -> Ir.Cond (f, i + adjust off i)
  | ir -> ir

let completed = ref []

let rec proc (p: JBir.t JProgram.program) (cms: JBasics.class_method_signature) =
  let open JProgram in
  let open Javalib_pack.Javalib in

  completed := cms :: !completed;

  let (_, meth) =
    JBasics.ClassMethodMap.find cms p.parsed_methods in

  let (is, jbir) =
    match meth.cm_implementation with
    | Native -> failwith "Cannot analyze native methods!"
    | Java java -> let jbir = Lazy.force java in (JBir.code jbir, jbir) in

  let annotated_insts =
    Array.mapi (fun i ins -> (ins, i, List.map var_name (Live.Env.elements (Live.run jbir i)))) is in
  let (unst, off, called) = Array.fold_left instr ([], [], []) annotated_insts in

  let insts = List.map (fun (i, vs) -> (renumber off i, vs)) unst in
  let (_, ms) = JBasics.cms_split cms in
  let ps = List.map (fun (t, v) -> java_to_var t v) (JBir.params jbir) in
  let this_proc = Ir.Proc (JBasics.ms_name ms, ps, [Ir.Var ("__RESULT__", Ir.Int)], insts) in

  let to_produce = List.sort_uniq JBasics.cms_compare
    (List.filter (fun pname -> not (List.mem pname !completed)) called) in
  this_proc :: List.concat (List.map (proc p) to_produce)

let rec program (p: JBir.t JProgram.program) (cms: JBasics.class_method_signature) =
  let (_, ms) = JBasics.cms_split cms in
  Ir.Program (JBasics.ms_name ms, proc p cms)
