Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.

(* The definition of subset types from "Coq.Init.Specif":

Inductive sig (A:Type) (P:A -> Prop) : Type :=
    exist : forall x:A, P x -> sig P.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
 *)

Definition even_nat := { n : nat | even n }.
Example even_two : even_nat := exist _ 2 (even_S _ (odd_S _ (even_O))).


(* The definition of dependent pairs from "Coq.Init.Specif":
Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
 *)

Inductive Vec (A : Type) : nat ->  Type :=
| Vec_nil : Vec A 0
| Vec_cons : forall {n}, A -> Vec A n -> Vec A (S n).

Definition vec_pair := { n : nat & Vec nat n }.
Definition vec_3 : Vec nat 3 := Vec_cons _ 9 (Vec_cons _ 9 (Vec_cons _ 9 (Vec_nil _))).
Example vec_example : vec_pair := existT _ 3 vec_3.

(* Exercise 1.1: More examples *)

(* Give three examples of subtypes and three examples of dependent pairs.
You can write them down as a comment. *)

(* Exercise 1.2: List of vectors *)

(* The type of lists of vectors of natural numbers, where each vector has the same length. *)
Definition listOfVectors1 := True (* TODO *).

(* The type of lists of vectors of natural numbers, where each vector may have a different length. *)
Definition listOfVectors2 := True (* TODO *).

(* Exercise 1.3: Addition of even numbers *)
Fixpoint even_add (x y : even_nat) : even_nat := (* TODO *).

Lemma even_add_is_add : forall x y : even_nat, proj1_sig (even_add x y) = proj1_sig x + proj1_sig y.
Proof.
  admit.
Admitted.  

