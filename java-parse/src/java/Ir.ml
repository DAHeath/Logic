module QID = QualifiedIdentity

open Core

type name = string
[@@deriving hash, compare, sexp]


type kind = Unit
          | Bool
          | Int
          | Real
          (* TODO: how to express arrays / array access? *)
          | List of kind
          (* What are these? *)
          (* | Type :=> Type *)
          (* | Array Type Type *)
[@@deriving hash, compare, sexp]


type var = Bound of int * kind
         | Free of QID.t * kind
[@@deriving hash, compare, sexp]


type expr = Var of var
          | If of kind

          | Not
          | Impl
          | Iff
          | And
          | Or

          | Add of kind
          | Mul of kind
          | Sub of kind
          | Div of kind
          | Mod of kind

          (* TODO: does `Distinct` mean not equal? *)
          | Distinct of kind
          | Eql of kind
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

          | ExprCons of expr * expr
[@@deriving hash, compare, sexp]


(* -- | The right hand side of an assignment. *)
type rhs = Expr of expr
         | Arbitrary of kind
         | Load of name * expr
[@@deriving hash, compare, sexp]


(* The space of imperative programs are represented as inductively constructed *)
(* commands. *)
type command = Seq of command * command
             | Case of expr * command * command
             | Loop of expr * command
             | Assign of var * rhs
             | Lbl of int * command
             | Jump of int
             | Save of name * expr * expr
             | Skip
[@@deriving hash, compare, sexp]


let rec pprint_kind = function
  | Unit -> "V"
  | Bool -> "B"
  | Int -> "I"
  | Real -> "F"
  | List k -> Printf.sprintf "[%s]" (pprint_kind k)

let pprint_var = function
  | Bound (i, k) -> Printf.sprintf "(%d):%s" i (pprint_kind k)
  | Free (n, k) -> Printf.sprintf "%s:%s" (QID.as_path n) (pprint_kind k)

let rec pprint_binop op a b parens =
  if parens
  then Printf.sprintf "(%s %s %s)" (pprint_expr true a) op (pprint_expr true b)
  else Printf.sprintf "%s %s %s" (pprint_expr true a) op (pprint_expr true b)

and pprint_expr parens = function
  (* Binops *)
  | ExprCons (ExprCons (Distinct _, a), b) -> pprint_binop "!=" a b parens
  | ExprCons (ExprCons (Eql _, a), b) -> pprint_binop "=" a b parens
  | ExprCons (ExprCons (Lt _, a), b) -> pprint_binop "<" a b parens
  | ExprCons (ExprCons (Le _, a), b) -> pprint_binop "<=" a b parens
  | ExprCons (ExprCons (Gt  _, a), b) -> pprint_binop ">" a b parens
  | ExprCons (ExprCons (Ge _, a), b) -> pprint_binop ">=" a b parens
  | ExprCons (ExprCons (Add _, a), b) -> pprint_binop "+" a b parens
  | ExprCons (ExprCons (Mul _, a), b) -> pprint_binop "*" a b parens
  | ExprCons (ExprCons (Sub _, a), b) -> pprint_binop "-" a b parens
  | ExprCons (ExprCons (Div _, a), b) -> pprint_binop "/" a b parens
  | ExprCons (ExprCons (Mod _, a), b) -> pprint_binop "%" a b parens
  | ExprCons (ExprCons (Impl, a), b) -> pprint_binop "->" a b parens
  | ExprCons (ExprCons (Iff, a), b) -> pprint_binop "<->" a b parens
  | ExprCons (ExprCons (And, a), b) -> pprint_binop "&&" a b parens
  | ExprCons (ExprCons (Or, a), b) -> pprint_binop "||" a b parens

  (* Uniops *)
  | ExprCons (Not, a) -> Printf.sprintf "!%s" (pprint_expr true a)

  (* Literals *)
  | LUnit -> "()"
  | LBool b -> Printf.sprintf "%B" b
  | LInt i -> Printf.sprintf "%d" i
  | LReal f -> Printf.sprintf "%f" f
  | Var v -> pprint_var v

  | other -> sexp_of_expr other |> Sexp.to_string


let jsonsexp cons args =
  String.concat ~sep:"," args
  |> Printf.sprintf "{\"%s\":[%s]}" cons

let wrapstr = Printf.sprintf "\"%s\""

let rec jsonsexp_kind = function
  | Unit -> jsonsexp "unit" []
  | Bool -> jsonsexp "bool" []
  | Int -> jsonsexp "int" []
  | Real -> jsonsexp "real" []
  | List k -> jsonsexp "list" [jsonsexp_kind k]

let jsonsexp_qid (QID.QID l) =
  let wrap_if_str s = try
      int_of_string s |> string_of_int
    with
      _ -> wrapstr s
  in
  List.map l ~f:wrap_if_str |> jsonsexp "qid"

let jsonsexp_var = function
  | Bound (i, k) -> jsonsexp "bound" [string_of_int i; jsonsexp_kind k]
  | Free (n, k) -> jsonsexp "free" [jsonsexp_qid n; jsonsexp_kind k]

let rec jsonsexp_expr = function
  | Var var -> jsonsexp "var" [jsonsexp_var var]
  | If k -> jsonsexp "if" [jsonsexp_kind k]

  | Not -> jsonsexp "not" []
  | Impl -> jsonsexp "impl" []
  | Iff -> jsonsexp "iff" []
  | And -> jsonsexp "and" []
  | Or -> jsonsexp "or" []

  | Add kind -> jsonsexp "add" [jsonsexp_kind kind]
  | Mul kind -> jsonsexp "mul" [jsonsexp_kind kind]
  | Sub kind -> jsonsexp "sub" [jsonsexp_kind kind]
  | Div kind -> jsonsexp "div" [jsonsexp_kind kind]
  | Mod kind -> jsonsexp "mod" [jsonsexp_kind kind]

  | Distinct kind -> jsonsexp "distinct" [jsonsexp_kind kind]
  | Eql kind -> jsonsexp "eql" [jsonsexp_kind kind]
  | Lt kind -> jsonsexp "lt" [jsonsexp_kind kind]
  | Le kind -> jsonsexp "le" [jsonsexp_kind kind]
  | Gt kind -> jsonsexp "gt" [jsonsexp_kind kind]
  | Ge kind -> jsonsexp "ge" [jsonsexp_kind kind]

  | Store (ka, kb) -> jsonsexp "store" [jsonsexp_kind ka; jsonsexp_kind kb]
  | Select (ka, kb) -> jsonsexp "select" [jsonsexp_kind ka; jsonsexp_kind kb]

  | LUnit -> jsonsexp "lunit" []
  | LBool b -> jsonsexp "lbool" [string_of_bool b]
  | LInt i -> jsonsexp "lint" [string_of_int i]
  | LReal f -> jsonsexp "lreal" [string_of_float f]

  | ExprCons (a, b) -> jsonsexp "exprcons" [jsonsexp_expr a; jsonsexp_expr b]
