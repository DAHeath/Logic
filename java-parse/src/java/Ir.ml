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
         | Free of name * kind
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

