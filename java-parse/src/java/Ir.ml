module QID = QualifiedIdentity

open Core

type id = QID.t

let show_id = QID.as_path

type kind
  = Unit
  | Bool
  | Int
  | Real
  | Array of kind * kind
  | Arrow of kind * kind

let rec show_kind = function
  | Unit -> "Unit"
  | Bool -> "Bool"
  | Int  -> "Int"
  | Real -> "Real"
  | Array (k, v) -> "Arr" ^ "{" ^ show_kind k ^ ", " ^ show_kind v ^ "}"
  | Arrow (t1, t2) -> "(" ^ show_kind t1 ^ " => " ^ show_kind t2 ^ ")"

type var = Var of id * kind

let show_var (Var (id, k)) = show_id id ^ show_kind k

type form
  = V of var
  | If of kind
  | Not
  | And
  | Or
  | Add of kind
  | Mul of kind
  | Sub of kind
  | Div of kind
  | Mod of kind
  | Eql of kind
  | Nql of kind
  | Lt of  kind
  | Le of  kind
  | Gt of  kind
  | Ge of  kind
  | Store of kind * kind
  | Select of kind * kind
  | LUnit
  | LBool of bool
  | LInt of int
  | LReal of float
  | Apply of form * form

let tail_kind = function
  | Arrow (_, k) -> k
  | _ -> failwith "bad kind applied"

let rec form_kind = function
  | V (Var (_, k)) -> k
  | If k           -> Arrow (Bool, (Arrow (k, (Arrow (k, k)))))
  | Not            -> Arrow (Bool, Bool)
  | And            -> Arrow (Bool, (Arrow (Bool, Bool)))
  | Or             -> Arrow (Bool, (Arrow (Bool, Bool)))
  | Add k          -> Arrow (k, (Arrow (k, k)))
  | Mul k          -> Arrow (k, (Arrow (k, k)))
  | Sub k          -> Arrow (k, (Arrow (k, k)))
  | Div k          -> Arrow (k, (Arrow (k, k)))
  | Mod k          -> Arrow (k, (Arrow (k, k)))
  | Eql k          -> Arrow (k, (Arrow (k, Bool)))
  | Nql k          -> Arrow (k, (Arrow (k, Bool)))
  | Lt k           -> Arrow (k, (Arrow (k, Bool)))
  | Le k           -> Arrow (k, (Arrow (k, Bool)))
  | Gt k           -> Arrow (k, (Arrow (k, Bool)))
  | Ge k           -> Arrow (k, (Arrow (k, Bool)))
  | Store (k, v)   -> Arrow (k, (Arrow (v, (Arrow (Array (k, v), Array (k, v))))))
  | Select (k, v)  -> Arrow (k, (Arrow (Array (k, v), v)))
  | LUnit          -> Unit
  | LBool b        -> Bool
  | LInt i         -> Int
  | LReal r        -> Real
  | Apply (f1, f2) -> tail_kind (form_kind f1)

let rec show_form = function
  | V v          -> show_var v
  | If k           -> "if"
  | Not            -> "not"
  | And            -> "and"
  | Or             -> "or"
  | Add k          -> "add"
  | Mul k          -> "mul"
  | Sub k          -> "sub"
  | Div k          -> "div"
  | Mod k          -> "mod"
  | Eql k          -> "eql"
  | Nql k          -> "neql"
  | Lt k           -> "lt"
  | Le k           -> "le"
  | Gt k           -> "gt"
  | Ge k           -> "ge"
  | Store (k, v)   -> "store"
  | Select (k, v)  -> "select"
  | LUnit          -> "unit"
  | LBool b        -> if b then "true" else "false"
  | LInt i         -> string_of_int i
  | LReal r        -> string_of_float r
  | Apply (f1, f2) -> "(" ^ show_form f1 ^ " " ^ show_form f2 ^ ")"

type com
  = Assign of var * form
  | Jump of int
  | Cond of form * int
  | Call of id * form list * var list
  | Skip
  | Done

let comma_list f xs = "(" ^ String.concat ?sep:(Some ", ") (List.map xs f) ^ ")"

let show_com = function
  | Assign (v, e)        -> show_var v ^ " := " ^ show_form e
  | Jump i               -> "jump " ^ string_of_int i
  | Cond (e, i)          -> "cond (" ^ show_form e ^ ") " ^ string_of_int i
  | Call (f, args, outs) -> "call " ^ show_id f
                                    ^ comma_list show_form args
                                    ^ " "
                                    ^ comma_list show_var outs
  | Skip                 -> "skip"
  | Done                 -> "done"

type imp = (com * var list) list

let show_imp is =
  let show_instr (c, vs) = show_com c ^ comma_list show_var vs in
  String.concat ?sep:(Some ";\n") (List.map is show_instr)

type proc = Proc of id * var list * var list * imp

type program = Program of id * proc list

let show_proc (Proc (f, ins, outs, instrs)) =
  show_id f
  ^ comma_list show_var ins
  ^ " "
  ^ comma_list show_var outs
  ^ " = {\n"
  ^ show_imp instrs
  ^ "\n}"

let show_program (Program (entry, ps)) =
  show_id entry
  ^ "\n"
  ^ String.concat ?sep:(Some "\n\n") (List.map ps show_proc)
