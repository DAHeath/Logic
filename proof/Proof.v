Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Background.

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

Definition proc_body p : list com :=
  match p with
  | Proc _ _ cs => cs
  end.

Definition call (p : id) (ctx : context) : context :=
  match ctx with
  | Context ct p' _ _ =>
      let cs := proc_body (ct p) in
      context_at ct cs 0
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

Module Single.

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

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Theorem hoare_asgn : forall P Q x a ctx,
  focus ctx = (x ::= a) ->
  {{P}} next ctx {{Q}} ->
  {{P [x |-> a]}} ctx {{Q}}.
Proof.
  unfold hoare_triple, assn_sub.
  intros.
  inversion H1; subst; try congruence.
  rewrite H3 in H; inversion H; subst; clear H.
  apply H0 in H5.
  assumption.
  assumption.
Qed.

Theorem hoare_jump : forall P Q ctx b i,
  focus ctx = (b JUMP i) ->
  {{fun st => P st /\ bassn b st}} move_context i ctx {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} next ctx {{Q}} ->
  {{P}} ctx {{Q}}.
Proof.
  unfold hoare_triple, assn_sub, bassn.
  intros.
  inversion H2; subst; try congruence.
  - rewrite H4 in H; inversion H; subst; clear H.
    apply H0 in H6.
    assumption.
    split; assumption.
  - rewrite H4 in H; inversion H; subst; clear H.
    apply H1 in H6.
    assumption.
    split.
    + assumption.
    + rewrite Bool.not_true_iff_false.
      assumption.
Qed.

Theorem hoare_done : forall P ctx,
  focus ctx = DONE ->
  {{P}} ctx {{P}}.
Proof.
  unfold hoare_triple, assn_sub.
  intros.
  inversion H0; congruence.
Qed.

Theorem hoare_invoke : forall P Q ctx outs p args,
  focus ctx = (outs <== p CALL args) ->
  ({{P}} ctx {{Q}} -> {{P}} call p ctx {{Q}}) ->
  {{P}} ctx {{Q}}.
Admitted.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption.
Qed.

End Single.

Module Equiv.

Definition Assertion := state -> state -> Prop.

Definition triple
           (P:Assertion) (c0 c1:context) (Q:Assertion) : Prop :=
  forall st0 st0' st1 st1'
  ,  c0 / st0 \\ st0'
  -> c1 / st1 \\ st1'
  -> P st0 st1 -> Q st0' st1'.

Notation "{{ P }}  c0 , c1  {{ Q }}" :=
  (triple P c0 c1 Q) (at level 90, c0, c1 at next level).

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st0 st1, P st0 st1 -> Q st0 st1.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80).

Definition assn_sub_l X a P : Assertion :=
  fun (st0 st1 : state) =>
    P (t_update st0 X (aeval st0 a)) st1.
Definition assn_sub_r X a P : Assertion :=
  fun (st0 st1 : state) =>
    P st0 (t_update st1 X (aeval st1 a)).
Notation "P [[ X |-> a ]" := (assn_sub_l X a P) (at level 10).
Notation "P [ X |-> a ]]" := (assn_sub_r X a P) (at level 10).

Definition bassn_l b : Assertion :=
  fun st0 st1 => (beval st0 b = true).

Definition bassn_r b : Assertion :=
  fun st0 st1 => (beval st1 b = true).

Theorem asgn_l : forall P Q x a c0 c1,
  focus c0 = (x ::= a) ->
  {{P}} next c0, c1 {{Q}} ->
  {{P [[x |-> a]}} c0, c1 {{Q}}.
Proof.
  unfold triple, assn_sub_l.
  intros.
  inversion H1; subst; try congruence.
  rewrite H4 in H; inversion H; subst; clear H.
  eapply H0 in H6.
  - apply H6.
  - apply H2.
  - apply H3.
Qed.

Theorem asgn_r : forall P Q x a c0 c1,
  focus c1 = (x ::= a) ->
  {{P}} c0, next c1 {{Q}} ->
  {{P [x |-> a]]}} c0, c1 {{Q}}.
Proof.
  unfold triple, assn_sub_l.
  intros.
  inversion H2; subst; try congruence.
  rewrite H4 in H; inversion H; subst; clear H.
  eapply H0 in H6.
  - apply H6.
  - apply H1.
  - apply H3.
Qed.

Theorem jump_l : forall P Q c0 c1 b i,
  focus c0 = (b JUMP i) ->
  {{fun st0 st1 => P st0 st1 /\ bassn_l b st0 st1}} move_context i c0, c1 {{Q}} ->
  {{fun st0 st1 => P st0 st1 /\ ~(bassn_l b st0 st1)}} next c0, c1 {{Q}} ->
  {{P}} c0, c1 {{Q}}.
Proof.
  unfold triple, bassn_l.
  intros.
  inversion H2; subst; try congruence.
  - rewrite H5 in H; inversion H; subst; clear H.
    eapply H0 in H7.
    + apply H7.
    + apply H3.
    + split; assumption.
  - rewrite H5 in H; inversion H; subst; clear H.
    eapply H1 in H7.
    + apply H7.
    + apply H3.
    + split.
      * assumption.
      * rewrite Bool.not_true_iff_false.
        assumption.
Qed.

Theorem jump_r : forall P Q c0 c1 b i,
  focus c1 = (b JUMP i) ->
  {{fun st0 st1 => P st0 st1 /\ bassn_r b st0 st1}} c0, move_context i c1 {{Q}} ->
  {{fun st0 st1 => P st0 st1 /\ ~(bassn_r b st0 st1)}} c0, next c1 {{Q}} ->
  {{P}} c0, c1 {{Q}}.
Proof.
  unfold triple, bassn_r.
  intros.
  inversion H3; subst; try congruence.
  - rewrite H5 in H; inversion H; subst; clear H.
    eapply H0 in H7.
    + apply H7.
    + apply H2.
    + split; assumption.
  - rewrite H5 in H; inversion H; subst; clear H.
    eapply H1 in H7.
    + apply H7.
    + apply H2.
    + split.
      * assumption.
      * rewrite Bool.not_true_iff_false.
        assumption.
Qed.

Theorem done : forall P c0 c1,
  focus c0 = DONE ->
  focus c1 = DONE ->
  {{P}} c0, c1 {{P}}.
Proof.
  unfold triple.
  intros.
  inversion H1; try congruence.
  inversion H2; try congruence.
Qed.

Theorem consequence_pre : forall (P P' Q : Assertion) c0 c1,
  {{P'}} c0, c1 {{Q}} ->
  P ->> P' ->
  {{P}} c0, c1 {{Q}}.
Proof.
  unfold triple, assert_implies.
  intros.
  apply (H st0 st0' st1 st1'); try assumption.
  apply H0. assumption.
Qed.

Theorem consequence_post : forall (P Q Q' : Assertion) c0 c1,
  {{P}} c0, c1 {{Q'}} ->
  Q' ->> Q ->
  {{P}} c0, c1 {{Q}}.
Proof.
  unfold triple, assert_implies.
  intros.
  apply H0.
  apply (H st0 st0' st1 st1'); try assumption.
Qed.

End Equiv.
