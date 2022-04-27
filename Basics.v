(* Type inference *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Check day.
Check next_weekday.

(* Examples *)

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

From Coq Require Export String.

(* Multi-argument functions *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Check orb.

(* Truth table for the orb function *)

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* New symbolic notation *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise *)
Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => false
            | false => true
            end
  | false => true
  end.

Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2 : (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4 : (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Check type with assertion *)
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black | white => true
  | primary _ => false
  end.

Definition isred c :=
  match c with
  | primary red => true
  | _ => false
  end.

Module TuplePlayground.
  Inductive bit : Type :=
    | B0
    | B1.

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  (**
     The definition of <<nat>> says how expressions in the set <<nat>>
     can be built:

     - the constructor expression O belongs to the set <<nat>>;
     - If <<n>> is a constructor expression belonging to the set <<nat>>,
     then <<S n>> is also a constructor expression belonging to the set
     <<nat>>; and
     - constructor expressions formed in these two ways are the ones
     belonging to the set <<nat>>.
   *)

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2 : oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Example test_plus1 : plus 3 2 = 5.
  Proof. reflexivity. Qed.

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1 : mult 3 3 = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

  Example test_minus1 : minus 5 2 = 3.
  Proof. simpl. reflexivity. Qed.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint eqb' (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => eqb' n' m'
  end.

Theorem eq_eqb_eqb' : forall n : nat, eqb n = eqb' n.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S n', O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1 : leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2 : leb 2 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3 : leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3' : (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  andb (negb (eqb n m)) (leb n m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1 : (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2 : (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3 : (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Given datatypes and functions, now let's prove properties of their
   behaviour. *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m;
  intros H;
  rewrite -> H;
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H0 H1.
  rewrite -> H0.
  rewrite <- H1.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + simpl.
      trivial.
  - destruct c eqn:Ec.
    + simpl.
      trivial.
    + simpl.
      trivial.
Qed.

Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall x : bool, f x = x) -> forall b : bool, f (f b) = b.
Proof.
  intros f.
  destruct b eqn:Eb.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem andb_eq_orb : forall b c : bool,
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
    destruct c eqn:Ec.
    + reflexivity.
    + discriminate.
  - simpl.
    destruct c eqn:Ec.
    + discriminate.
    + reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 Z => B0 Z
  | B0 (B1 m') => B1 (B1 m')
  | B0 (B0 m') => B1 (B0 m')
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 m' => S (bin_to_nat m')
  | B1 (B1 m') => S (S (S (bin_to_nat m')))
  | B1 m' => S (bin_to_nat m')
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Eval simpl in (incr (B1 Z)).
Eval simpl in (incr (incr (B1 Z))).
Eval simpl in bin_to_nat (B1 Z).
Eval simpl in bin_to_nat (B0 (B1 Z)).
Eval simpl in bin_to_nat (B1 (B1 Z)).

Example test_bin_incr6 :
  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.
