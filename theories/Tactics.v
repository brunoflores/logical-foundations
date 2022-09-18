From LF Require Export Poly.

Theorem silly1 : forall (n m : nat), n = m -> n = m.
Proof. intros n m eq. apply eq. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof. intros n m o p eq1 eq2.
       apply eq2. apply eq1. Qed.

Theorem silly3 : forall (n m : nat), n = m -> m = n.
Proof. intros n m H. symmetry. apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof. intros l l' H. rewrite -> H. symmetry. apply rev_involutive. Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof. intros a b c d e f eq1 eq2.
       rewrite -> eq1.
       rewrite -> eq2.
       reflexivity. Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof. intros X n m o eq1 eq2.
       rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof. intros a b c d e f eq1 eq2.
       apply trans_eq with (m := [c;d]).
       apply eq1. apply eq2. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof. intros a b c d e f eq1 eq2.
       transitivity [c;d].
       apply eq1. apply eq2. Qed.

Theorem S_injective : forall (n m : nat), S n = S m -> n = m.
Proof. intros n m H1.
       assert (H2: n = pred (S n)). { reflexivity. }
       rewrite -> H2. rewrite -> H1. simpl. reflexivity. Qed.

Theorem S_injective' : forall (n m : nat), S n = S m -> n = m.
Proof. intros n m H. injection H as Hnm. apply Hnm. Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof. intros n m o H.
       injection H. intros H1 H2. rewrite -> H1. rewrite -> H2. reflexivity.
       Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof. intros X x y z l j H1 H2.
       injection H1 as H3 H4. Abort.
