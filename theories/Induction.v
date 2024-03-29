From LF Require Export Basics.

(* The point here is to show that we need induction to prove things over
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
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  induction n as [ | n' IHn'].
  - (* n = O *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  induction n as [ | n' IHn'].
  - intros m. simpl. reflexivity.
  - simpl. intros m. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [ | n' IHn'].
  - intros m. simpl. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. intros m p. rewrite -> IHn'. reflexivity. Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n.
  - (* double of zero is zero *) simpl. reflexivity.
  - simpl double. rewrite -> IHn. rewrite -> plus_n_Sm. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_rearrange :
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_swap :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H0: n + (m + p) = (n + m) + p). { rewrite -> add_assoc. reflexivity. }
  rewrite -> H0.
  assert (H1: m + (n + p) = m + n + p). { rewrite -> add_assoc. reflexivity. }
  rewrite -> H1.
  assert (H2: n + m = m + n). { rewrite -> add_comm. reflexivity. }
  rewrite -> H2. reflexivity. Qed.

Theorem add_shuffle3 :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H0: forall n0 m0 p0 : nat, n0 + (m0 + p0) = n0 + m0 + p0).
  {
    intros n0 m0 p0. induction n0.
    - simpl. reflexivity.
    - simpl. rewrite -> IHn0. reflexivity.
  }
  assert (H1: m + (n + p) = m + n + p).
  {
    induction m.
    - simpl. reflexivity.
    - simpl. rewrite -> IHm. reflexivity.
  }
  rewrite -> H0.
  rewrite -> H1.
  assert (H2 : n + m = m + n).
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H2.
  reflexivity. Qed.

Theorem add_shuffle3' :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_comm.
  assert (H0: n + p = p + n).
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H0.
  rewrite -> add_assoc.
  reflexivity. Qed.

Theorem mul_comm :
  forall m n : nat, m * n = n * m.
Proof.
  induction n as [ | n' IHn' ].
  - simpl. auto.
  - simpl.
    assert (H0: m * S n' = m * n' + m). { auto. }
    rewrite -> H0.
    rewrite -> add_comm.
    rewrite -> IHn'.
    reflexivity. Qed.

Inductive bin : Type :=
  | Z
  | B0 (_ : bin)
  | B1 (_ : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.

Example test_bin_incr5 :
  bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr6 :
  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

(* Incrementing a binary number and then converting it to a unary natural
   number yields the same result as first converting it to a natural number
   and then incrementing. *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  induction b as [ | b' | b'' IHb''].
  - reflexivity.
  - simpl incr. simpl bin_to_nat. simpl. reflexivity.
  - simpl incr. simpl bin_to_nat.
    rewrite -> IHb''. simpl.
    replace (bin_to_nat b'' + 0)
      with  (bin_to_nat b'').
    replace (S (bin_to_nat b'' + bin_to_nat b''))
      with  ((bin_to_nat b'')  + S (bin_to_nat b'')).
    reflexivity.
    rewrite -> plus_n_Sm.
    reflexivity.
    rewrite <- plus_n_O.
    reflexivity. Qed.
