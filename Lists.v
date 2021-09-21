From LF Require Export Induction.
Module NatList.

  Inductive natprod : Type :=
    | pair (n1 n2 : nat).

  Check (pair 3 5) : natprod.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x, y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x, y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

  Theorem surjective_pairing' :
    forall (n m : nat), (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity. Qed.

  Theorem surjective_pairing :
    forall (p : natprod), p = (fst p, snd p).
  Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity. Qed.

  Theorem snd_fst_is_swap :
    forall (p : natprod), (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity. Qed.

  Theorem fst_swap_is_snd :
    forall (p : natprod), fst (swap_pair p) = snd p.
  Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity. Qed.

  Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).

  Notation "[  ]" := nil.

  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
