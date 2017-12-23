Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Background.
Require Import Maps.

Inductive com : Type :=
  | CAss : id -> aexp -> com
  | CJump : bexp -> nat -> com
  | CCall : id -> list id -> list aexp -> com
  | CDone : com

with proc : Type :=
  | Proc : list id -> list id -> list com -> proc.

Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "b 'JUMP' loc" := (CJump b loc) (at level 60).
Notation "'DONE'" := CDone.
Notation "is '<==' p 'CALL' es" := (CCall p is es) (at level 60).

Definition call_table := total_map proc.
Definition empty_table := t_empty (Proc [] [] []).

Inductive context : Type :=
  | Context : call_table -> list com -> nat -> com -> context.

Definition com_at (n:nat) c := List.nth n c DONE.
Definition context_at (ct : call_table) (c : list com) (n : nat) : context :=
  Context ct c n (com_at n c).

(* Update all of the ids to the corresponding values. *)
Fixpoint t_update_nats (st : state) (ids : list id) (exps : list nat) : state :=
  match (ids, exps) with
  | (nil, _) => st
  | (_, nil) => st
  | (id :: ids', exp :: exps') => t_update_nats (t_update st id exp) ids' exps' 
  end.

Definition t_update_exps (st : state) (exps : list aexp)
                         (st' : state) (ids : list id) :=
  t_update_nats st' ids (map (aeval st) exps).

(* copy the value of the ids in the first state to the ids in the second state *)
Definition t_copy_ids (st : state) (ids : list id)
                      (st' : state) (ids' : list id) :=
  t_update_nats st' ids (map st ids').

Definition next (ctx : context) : context :=
  match ctx with
  | Context ct p i _ => context_at ct p (S i)
  end.

Definition focus (ctx : context) : com :=
  match ctx with
  | Context _ _ _ c => c
  end.

Definition move_context (i : nat) (ctx : context) : context :=
  match ctx with
  | Context ct p _ _ => context_at ct p i
  end.

Definition proc_named (ctx : context) (name : id) :=
  match ctx with
  | Context ct _ _ _ => ct name
  end.

Definition change_body (cs : list com) (ctx : context) : context :=
  match ctx with
  | Context ct _ _ _ => context_at ct cs 0
  end.

Reserved Notation "ps '/' st '\\' st'" (at level 40, st at level 39).
Inductive ceval_n :
  context -> state -> state -> Prop :=
  | E_Done : forall ctx st,
      focus ctx = DONE ->
      ctx / st \\ st
  | E_Ass : forall ctx st st' a v x,
      focus ctx = (x ::= a) ->
      aeval st a = v ->
      next ctx / t_update st x v \\ st' ->
      ctx / st \\ st'
  | E_JumpTrue : forall ctx st st' b i,
      focus ctx = (b JUMP i) ->
      beval st b = true ->
      move_context i ctx / st \\ st' ->
      ctx / st \\ st'
  | E_JumpFalse : forall ctx st st' b i,
      focus ctx = (b JUMP i) ->
      beval st b = false ->
      next ctx / st \\ st' ->
      ctx / st \\ st'
  | E_Call : forall ctx st st' st'' es is name args outs cs,
      focus ctx = (is <== name CALL es) ->
      (* The table defines the procedure. *)
      proc_named ctx name = Proc args outs cs ->
      (* The commands in the procedure evaluate to some state starting from
       * just arguments. *)
      change_body cs ctx / t_update_exps st es empty_state args \\ st' ->
      (* The next command evaluates to the final state starting from the initial
       * state updated to reflect the outputs of the procedure. *)
      next ctx / t_copy_ids st' outs st is \\ st'' ->
      (* The CALL evaluates from the initial state to the final state. *)
      ctx / st \\ st''
  where "ps '/' st '\\' st'" := (ceval_n ps st st').

Definition ceval (ct : call_table)
                 (c : list com) (st : state) (st' : state) : Prop :=
  ceval_n (context_at ct c 0) st st'.

Definition pup_to_n : list com :=
  [ Y ::= ANum 0
  ; BEq (AId X) (ANum 0) JUMP 5
  ; Y ::= APlus (AId Y) (AId X)
  ; X ::= AMinus (AId X) (ANum 1)
  ; BTrue JUMP 1
  ].

Ltac act x :=
  eapply x; try reflexivity; simpl.

Theorem pup_to_2_ceval :
  ceval empty_table pup_to_n (t_update empty_state X 2)
    (t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0).
Proof.
  act E_Ass.
  act E_JumpFalse.
  act E_Ass.
  act E_Ass.
  act E_JumpTrue.
  act E_JumpFalse.
  act E_Ass.
  act E_Ass.
  act E_JumpTrue.
  act E_JumpTrue.
  act E_Done.
Qed.

Definition fact_sym : id := Id "fact".

Definition fact : proc :=
  Proc [X] [Z]
    [ BEq (AId X) (ANum 0) JUMP 4
    ; [Z] <== fact_sym CALL [AMinus (AId X) (ANum 1)]
    ; Z ::= AMult (AId X) (AId Z)
    ; BTrue JUMP 5
    ; Z ::= ANum 1
    ].

Definition call_fact :=
  [ [Z] <== fact_sym CALL [ANum 3] ].

Theorem fact_3 :
  ceval (t_update empty_table fact_sym fact)
    call_fact
    empty_state
    (t_update empty_state Z 6).
Proof.
  act E_Call. act E_JumpFalse.
  act E_Call. act E_JumpFalse.
  act E_Call. act E_JumpFalse.
  act E_Call. act E_JumpTrue.
  act E_Ass. act E_Done.
  act E_Ass. act E_JumpTrue. act E_Done.
  act E_Ass. act E_JumpTrue. act E_Done.
  act E_Ass. act E_JumpTrue. act E_Done.
  act E_Done.
Qed.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:context) (Q:Assertion) : Prop :=
  forall st st', c / st \\ st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).
Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).
Open Scope hoare_spec_scope.

Theorem hoare_asgn : forall Q x a ctx,
  focus ctx = (x ::= a) ->
  {{Q [X |-> a]}} ctx {{Q}}.
Proof.
