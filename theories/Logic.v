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

Theorem zero_not_one : 0 <> 1.
Proof. unfold not. intros contra. discriminate contra. Qed.

Theorem not_False : ~ False.
Proof. unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop, (P /\ ~P) -> Q.
Proof. intros P Q [HP HNA]. unfold not in HNA.
       apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof. intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof. intros P Q H0. unfold not. intros H1 H2. apply H1, H0, H2. Qed.

Theorem not_both_true_and_false : forall P : Prop, ~(P /\ ~P).
Proof. intros P. unfold not. intros [H1 H2]. apply H2, H1. Qed.

Theorem de_morgan_not_or : forall (P Q : Prop), ~(P \/ Q) -> ~P /\ ~Q.
Proof. intros P Q NPQ. split.
       - intro P1. apply NPQ. left. apply P1.
       - intro Q1. apply NPQ. right. apply Q1. Qed.

Theorem not_true_is_false : forall b : bool, b <> true -> b = false.
Proof. intros [] H.
       - unfold not in H. exfalso. apply H. reflexivity.
       - reflexivity. Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof. intros P Q [HPQ HQP]. split.
       - apply HQP.
       - apply HPQ. Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof. intros b. split.
       - apply not_true_is_false.
       - intros H. rewrite -> H. intros H'. discriminate H'. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. intros P Q R H. inversion H as [HP | [HQ HR]].
       - split.
         + left. apply HP.
         + left. apply HP.
       - split.
         + right. apply HQ.
         + right. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof. intros P Q R H. inversion H as [HPQ HPR].
       inversion HPQ as [HP | HQ].
       left. apply HP.
       inversion HPR as [HP | HR].
       left. apply HP.
       right. split.
       - apply HQ.
       - apply HR. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. intros P Q R. split.
       - intros H. apply or_distributes_over_and_1. apply H.
       - intros H. apply or_distributes_over_and_2. apply H. Qed.

(* Existential Quantification *)

Definition Even x := exists n : nat, x = double n.
Lemma four_is_Even : Even 4.
Proof. unfold Even. exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof. intros n [m Hm]. exists (2 + m). apply Hm. Qed.

(* P holds for all x implies there is not x for which P does not hold. *)
Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. intros X P H. unfold not. intros [x H0]. apply H0. apply H. Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
Proof. intros X P Q [x [HP | HQ]].
       - left. exists x. apply HP.
       - right. exists x. apply HQ. Qed.

(* Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof. simpl. right. right. right. left. reflexivity. Qed.

Example In_example_2 : forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof. simpl. intros n [H | [H | []]].
       - exists 1. rewrite <- H. reflexivity.
       - exists 2. rewrite <- H. reflexivity. Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof. intros A B f l x. induction l as [ | x' l' IHl'].
       - simpl. intros [].
       - simpl. intros [H | H].
         + rewrite -> H. left. reflexivity.
         + right. apply IHl'. apply H. Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => (P h) /\ (All P t)
  end.

Theorem ex_falso_quodlibet : forall P : Prop, False -> P.
Proof. intros P contra. destruct contra. Qed.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof. intros T P l. split.
       - intros H. induction l.
         + reflexivity.
         + simpl. simpl in H. split.
           * apply H. left. reflexivity.
           * apply IHl. intros y. intros H'. apply H. right. apply H'.
       - intros H. induction l.
         + simpl. intros x. apply ex_falso_quodlibet.
         + simpl. intros x0 H'. destruct H'.
           * simpl in H. rewrite <- H0. apply H.
           * simpl in H. apply IHl. apply H. apply H0. Qed.

Lemma add_comm3 : forall x y z, x + (y + z) = (z + y) + x.
Proof. intros x y z.
       rewrite -> add_comm.
       rewrite -> (add_comm y z).
       reflexivity. Qed.
