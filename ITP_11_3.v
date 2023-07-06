
Require Import Imp.
Require Import Maps.
Require Import Hoare.

(* Definitions from Hoare Logic Chapter II. *)

Inductive dcom : Type :=
  | DCSkip : Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : string -> aexp -> Assertion -> dcom
  | DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom
           -> Assertion -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion ->  dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

Delimit Scope default with default.
Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90) : dcom_scope.
Delimit Scope dcom_scope with dcom.
Open Scope dcom_scope.


Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq d1 d2 => (extract d1 ;; extract d2)
  | DCAsgn X a _ => X ::= a
  | DCIf b _ d1 _ d2 _ => TEST b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.
Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq d1 d2 => post d2
  | DCAsgn X a Q => Q
  | DCIf _ _ d1 _ d2 Q => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d => post d
  | DCPost c Q => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.
Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X !-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~(bassn b st)) ->> P2)
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((fun st => post d st /\ bassn b st) ->> Pbody)
      /\ ((fun st => post d st /\ ~(bassn b st)) ->> Ppost)
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d; intros P H; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence_post with (Q':=post d1); eauto.
         eapply hoare_consequence_pre; eauto.
      + eapply hoare_consequence_post with (Q':=post d2); eauto.
         eapply hoare_consequence_pre; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1 Hd]]].
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import PeanoNat.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.



(*********************************************************************************************************
** Exercises
**********************************************************************************************************)

(* Exercise 1 *)
(* Consider the following informal program with a pre- and postcondition. *)
(*
{{ X = m }}
  Y ::= 0;;
  WHILE ~(X = 0) DO
    X ::= X - 1;;
    Y ::= Y + 1
  END
{{ Y = m }}
*)
(* Translate this into a formal decorated program and prove it correct. *)

Definition slow_assignment_dec m : decorated.
(* Your task *)
Admitted.

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof.
(* Your task *)
admit.
Admitted.
