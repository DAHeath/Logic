module JProgram = Sawja_pack.JProgram
module JBasics = Javalib_pack.JBasics
module JBir = Sawja_pack.JBir
module QID = QualifiedIdentity

open Core

module Instr = struct
  type t = {
      loc: QualifiedIdentity.t;
      instr: JBir.instr;
      live: Sawja_pack.Live_bir.Env.t;
    }

  let equal a b = a = b
  let hash a = QID.to_string "/" a.loc |> String.hash
  let compare a b =
    String.compare (QID.to_string "/" a.loc) (QID.to_string "/" b.loc)
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

let var_name var =
  JBir.var_name_debug var
  |> Option.value ~default:(JBir.var_name var)

let qid_var_name loc var prime =
  var
  |> QID.specify (QID.unspecify loc)
  |> (Fn.flip QID.specify) prime

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
      live
  =
  let open Instr in
  let collect_vertices i graph instr =
    let path = QID.specify prefix (string_of_int i) in
    let vertex = { loc = path; instr = instr; live = (live i) } in

    let dest_i = match instr with
      | JBir.Goto target -> [(Branch.Goto, target)]
      | JBir.Ifd (_, target) -> [(Branch.False, i + 1); (Branch.True, target)]
      | JBir.Throw _ -> []
      | JBir.Return _ -> []
      | _ -> [(Branch.Goto, i + 1)]
    in
    let connect_vertices graph (br, j) =
      let instr = Array.nget instrs j in
      let v: Instr.t = {
          loc = QID.specify prefix (string_of_int j);
          instr = instr;
          live = live j;
        }
      in
      add_edge_e graph (E.create vertex br v)
    in

    List.fold dest_i ~init:graph ~f:connect_vertices
  in
  Array.foldi instrs ~init:start_graph ~f:collect_vertices


let squash_gotos (graph: t) =
  let rec find_nongoto: (Instr.t -> Instr.t option) = function
    | { Instr.instr = JBir.Goto _; _ } as v ->
       succ graph v |> List.hd |> Option.bind ~f:find_nongoto
    | found -> Some found
  in
  let remove_gotos ((v: V.t), (e: E.label), (v': V.t)) (out: t) =
    match v with
    | { Instr.instr = JBir.Goto _; _ } -> out
    | _ ->
       (* walk the graph until we don't have a goto statement *)
       let nongoto = match find_nongoto v' with
         | Some g -> g
         | None -> failwith "Goto to unknown loc"
       in
       add_edge_e out (E.create v e nongoto)
  in
  fold_edges_e remove_gotos graph empty


let infer_bools
    (vartable: (int * int * string * JBasics.value_type * int) list)
    (graph: t)
  =
  let bool_assigns v m =
    match v.Instr.instr with
    | JBir.AffectVar (var, expr) ->
      let vname = var_name var in
      if List.exists vartable ~f:(fun (_, _, n, _, _) -> n = vname)
      then m
      else (match (expr, Map.find m vname) with
          | (JBir.Const (`Int n), None) when n = Int32.zero || n = Int32.one ->
            Map.add m ~key:vname ~data:true
          | (_, None)
          | (_, Some true) -> Map.add m ~key:vname ~data:false
          | (_, Some false) -> m
        )
    | _ -> m
  in
  let append_vartable ~key:key ~data:data vtable =
    (0, 0, key, JBasics.TBasic `Bool, 0) :: vtable
  in
  let found_bools = fold_vertex bool_assigns graph String.Map.empty in
  Map.fold found_bools ~init:vartable ~f:append_vartable


let build_graph
      (program: JBir.t JProgram.program)
      (method_sig: JBasics.class_method_signature)
  =
  let (instrs, code) = match cms_to_instrs program method_sig with
    | Error `Native -> failwith "Cannot analyze native methods!"
    | Ok instrs -> instrs
  in
  let live i = Sawja_pack.Live_bir.run code i in
  append_instrs (cms_to_qid method_sig) instrs empty live
  |> squash_gotos


let unimplemented () = failwith "unimplemented"


let rec collect_vars = function
  | JBir.Const const -> []
  | JBir.Var (_, var) -> [var]
  | JBir.Unop (_, expr) -> collect_vars expr
  | JBir.Binop (_, expr_a, expr_b) ->
     List.append (collect_vars expr_a) (collect_vars expr_a)
  | JBir.Field _ -> unimplemented ()
  | JBir.StaticField _ -> unimplemented ()


let ( $:: ) a b = Ir.ExprCons (a, b)


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
      (loc: QID.t)
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
  let name = qid_var_name loc name "0" in
  (Ir.Free (name, kind), kind)


let resolve_types = function
  | (Ir.Bool, Ir.Int)
  | (Ir.Int, Ir.Bool) -> Ir.Bool
  | (a, b) when a = b -> a
  | _ -> failwith "Mismatched types in condition."


let rename_var f = function
  | Ir.Free (name, t) -> Ir.Free (f name, t)
  | other -> other


let invoke cn ms v args =
  match BuiltIn.call_built_in_method cn ms v args with
  | Some i -> i
  | None -> failwith "Non-builtin functions not supported yet."


let rec java_to_expr vartable loc = function
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
  | JBir.Var (value_type, var) ->
    let (var, kind) = java_to_var vartable loc (Some value_type) var in
    (Ir.Var var, kind)
  | JBir.Unop (op, expr) ->
     let (ir_expr, t) = java_to_expr vartable loc expr in
     (match op with
      | JBir.Neg _ -> (Ir.Not $:: ir_expr, t)
      | JBir.ArrayLength
      | JBir.InstanceOf _
      | JBir.Cast _
      | JBir.Conv _ -> unimplemented ()
     )
  | JBir.Binop (op, expr_a, expr_b) ->
     let (ir_expr_a, _) = java_to_expr vartable loc expr_a in
     let (ir_expr_b, _) = java_to_expr vartable loc expr_b in
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


let java_to_condition vartable loc cond a b =
  let (expr_a, t_a) = (java_to_expr vartable loc a) in
  let (expr_b, t_b) = (java_to_expr vartable loc b) in
  let op kind = match cond with
    | `Eq -> Ir.Eql kind
    | `Ge -> Ir.Ge kind
    | `Gt -> Ir.Gt kind
    | `Le -> Ir.Le kind
    | `Lt -> Ir.Lt kind
    | `Ne -> Ir.Distinct kind
  in
  match (t_a, t_b, expr_a, expr_b) with
    | (a, b, _, _) when a = b -> (op a) $:: expr_a $:: expr_b
    | (Ir.Bool, Ir.Int, _, Ir.LInt 0) -> Ir.Not $:: expr_a
    | (Ir.Bool, Ir.Int, _, Ir.LInt 1) -> expr_a
    | _ ->
       let mkstr e = Ir.sexp_of_expr e |> Sexp.to_string in
       Printf.sprintf "Mismatched types: %s and %s."
                      (mkstr expr_a) (mkstr expr_b)
       |> failwith


let instr_to_expr vartable loc = function
  | JBir.AffectVar (var, expr) ->
     let (irvar, t_a) = java_to_var vartable loc None var in
     let (irexpr, t_b) = java_to_expr vartable loc expr in
     let kind = resolve_types (t_a, t_b) in
     let irexpr = match (kind, irexpr) with
       | (Ir.Bool, Ir.LInt 0) -> Ir.LBool false
       | (Ir.Bool, Ir.LInt 1) -> Ir.LBool true
       | (_, e) -> e
     in
     let irvar' = rename_var (fun v -> QID.specify (QID.unspecify v) "1") irvar in
     let expr = (Ir.Eql kind) $:: (Ir.Var irvar') $:: irexpr in
     Some (expr, [(irvar, irvar')], Ir.Instance)
  | JBir.Ifd ((comp, a, b), i) ->
     Some (java_to_condition vartable loc comp a b, [], Ir.Instance)
  | JBir.Nop -> None
  (* we're in a graph we can just delete this vertex *)
  | JBir.Goto i -> None
  (* Static methods! These include `ensure` and friends *)
  | JBir.InvokeStatic (v, cn, ms, args) ->
    let args = List.map ~f:(java_to_expr vartable loc) args in
    let (kind, ir) = invoke cn ms v args in
    Some (kind, [], ir)
  (* things we haven't translated yet *)
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
  | JBir.AffectStaticField _ -> None

