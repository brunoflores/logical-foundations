From LF Require Export Basics.

(* The point here is to show we need induction to prove things over
   all naturals. *)

Theorem plus_n_O_left :
  forall n : nat, n = 0 + n.
Proof.
  reflexivity.
Qed.

Theorem plus_n_O_firsttry :
  forall n : nat, n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry :
  forall n : nat, n = n + 0.
Proof.
  intros n. destruct n as [ | n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem plus_n_O :
  forall n : nat, n = n + 0.
Proof.
  induction n as [ | n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_n_n :
  forall n, minus n n = 0.
Proof.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise 2: *)

Theorem mult_0_r :
  forall n : nat, n * 0 = 0.
Proof.
  induction n as [ | n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm :
  forall n m : nat, S (n + m) = n + (S m).
Proof.
  induction n as [ | n' IHn'].
  - intros m.
    simpl.
    reflexivity.
  - simpl.
    intros m.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - intros m.
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - intros m.
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc :
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    intros m p.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H0: n + (m + p) = (n + m) + p).
  { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H0.
  assert (H1: m + (n + p) = m + n + p).
  { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H1.
  assert (H2: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H2.
  reflexivity.
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
