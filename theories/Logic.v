From LF Require Export Tactics.

Check (3 = 3) : Prop.
Check (forall n m : nat, n + m = m + n) : Prop.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.
Definition plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

(* Functions that return propositions are said to define
   properties of their arguments. *)
Definition is_three (n : nat) : Prop := n = 3.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof. intros n m H. injection H as H1. apply H1. Qed.

(* The equality operator `=` is a binary function that returns a Prop. *)
Check @eq : forall A : Type, A -> A -> Prop.
