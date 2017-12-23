Require Import Maps.
Require Import Background.
Require Import Proof.

Definition pup_to_n : list com :=
  [ Y ::= ANum 0
  ; BEq (AId X) (ANum 0) JUMP 5
  ; Y ::= APlus (AId Y) (AId X)
  ; X ::= AMinus (AId X) (ANum 1)
  ; BTrue JUMP 1
  ].

Theorem pup_to_2_ceval :
  ceval empty_table pup_to_n (t_update empty_state X 2)
    (t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0).
Proof.
  apply E_Ass with 0. reflexivity.
  apply E_JumpFalse.  reflexivity.
  apply E_Ass with 2. reflexivity.
  apply E_Ass with 1. reflexivity.
  apply E_JumpTrue.   reflexivity.
  apply E_JumpFalse.  reflexivity.
  apply E_Ass with 3. reflexivity.
  apply E_Ass with 0. reflexivity.
  apply E_JumpTrue.   reflexivity.
  apply E_JumpTrue.   reflexivity.
  apply E_Done.
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
  eapply E_Call. reflexivity. apply E_JumpFalse. reflexivity.
  eapply E_Call. reflexivity. apply E_JumpFalse. reflexivity.
  eapply E_Call. reflexivity. apply E_JumpFalse. reflexivity.
  eapply E_Call. reflexivity. apply E_JumpTrue. reflexivity.
  eapply E_Ass. reflexivity. apply E_Done.
  eapply E_Ass. reflexivity. apply E_JumpTrue. reflexivity. apply E_Done.
  eapply E_Ass. reflexivity. apply E_JumpTrue. reflexivity. apply E_Done.
  eapply E_Ass. reflexivity. apply E_JumpTrue. reflexivity. apply E_Done.
  apply E_Done.
Qed.
