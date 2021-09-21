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

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof.
    simpl. reflexivity. Qed.

  Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

  Definition odd (n : nat) : bool :=
    negb (even n).

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => if odd h then h :: oddmembers t else oddmembers t
    end.

  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof.
    simpl. reflexivity. Qed.

  Fixpoint countoddmembers (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => if odd h then S (countoddmembers t) else countoddmembers t
    end.

  Example test_countoddmembers:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof.
    simpl. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | [], [] => []
    | l1', [] => l1'
    | [], l2' => l2'
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    end.

  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof.
    simpl. reflexivity. Qed.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof.
    simpl. reflexivity. Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof.
    simpl. reflexivity. Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof.
    simpl. reflexivity. Qed.
