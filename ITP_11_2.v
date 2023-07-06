Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.

(* Exercise 2: Tactic Automation *)

(* Exercise 2.1 *)
Ltac odd_even_tac := idtac (* TODO *).


Theorem even_42 : even 42.
Proof.
  odd_even_tac.
Qed.

Theorem odd_55 : odd 55.
Proof.
  odd_even_tac.
Qed.

(* Exercise 2.2 *)
Definition AllEven : list nat -> Prop := Forall even.

Lemma AllEvenApp : forall xs ys,  AllEven (xs ++ ys) -> AllEven xs /\ AllEven ys.
Proof. admit. Admitted.
  
Lemma AllEvenApp2 : forall xs ys,  AllEven xs /\ AllEven ys -> AllEven (xs ++ ys).
Proof. admit. Admitted.

(* The tactic all_even_tac_helper should do the following thing:
  - Look if there is a hypothesis of the form "AllEven (xs ++ ys)" in the context.
    In that case, apply AllEvenApp to that hypothesis and destruct the result.
  - Look if the Goal to be proven is "AllEven (xs ++ ys)". In that case, apply AllEvenApp2
    and split the goal in order to get 2 subgoals.
*)
Ltac all_even_tac_helper := idtac (* TODO *).

(* Use all_even_tac_helper to solve each of the following theorems.
   Do not change the proofs of any of the theorems given below! *)
Ltac all_even_tac := idtac (* TODO *).


Theorem th1 : forall xs ys, AllEven (xs ++ ys) -> AllEven (ys ++ xs).
Proof.
  intros. all_even_tac.
Qed.

Theorem th2 : forall xs ys zs, AllEven (xs ++ (ys ++ zs)) -> AllEven ((xs ++ zs) ++ ys).
Proof.
  intros. all_even_tac.
Qed.

Theorem th3 : forall xs ys, AllEven (xs ++ ys) -> AllEven xs.
Proof.
  intros. all_even_tac.
Qed.

  
