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

(* Logical Connectives *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split; reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof. intros A B HA HB. split.
       - apply HA.
       - apply HB. Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof. intros n m. induction n.
       - simpl. rewrite <- plus_n_O. reflexivity.
       - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity. Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. intros n m H. split.
       - induction n.
         + reflexivity.
         + discriminate H.
       - induction m.
         + reflexivity.
         + rewrite -> plus_comm in H. discriminate H. Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. intros n m H. destruct H as [Hn Hm].
       rewrite Hn. rewrite Hm. reflexivity. Qed.

(* Shortcut: *)
Lemma and_example2'' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. intros n m [Hn Hm]. rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof. intros n m H. apply and_exercise in H.
       destruct H as [Hn Hm]. rewrite Hn. reflexivity. Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q HPQ. destruct HPQ as [HP _]. apply HP. Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q [_ HQ]. apply HQ. Qed.

Theorem and_cummut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof. intros P Q [HP HQ]. split.
       - apply HQ.
       - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. intros P Q R [HP [HQ HR]]. split.
       - split.
         + apply HP.
         + apply HQ.
       - apply HR. Qed.

Lemma mult_n_0 : forall n : nat, n * 0 = 0.
Proof. intros n. induction n.
       - reflexivity.
       - simpl. rewrite -> IHn. reflexivity. Qed.

Lemma factor_is_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof. intros n m [Hn |Hm].
       - rewrite -> Hn. reflexivity.
       - rewrite -> Hm. rewrite -> mult_n_0. reflexivity. Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof. intros A B HA. left. apply HA. Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof. intros [ | n'].
       - left. reflexivity.
       - right. reflexivity. Qed.

Lemma mult_is_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. intros n m H. destruct n.
       - left. reflexivity.
       - right. destruct m.
         + reflexivity.
         + discriminate H. Qed.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof. intros P Q H. inversion H as [HP | HQ].
       - right. apply HP.
       - left. apply HQ. Qed.
