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

  (* Bags *)

  Definition bag := natlist.

  Fixpoint beq_nat (n m : nat) : bool :=
    match n, m with
    | O, O => true
    | S _, O => false
    | O, S _ => false
    | S n', S m' => beq_nat n' m'
    end.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => O
    | h :: t => match beq_nat h v with
                | true => S (count v t)
                | false => count v t
                end
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof.
    reflexivity. Qed.

  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof.
    reflexivity. Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v : nat) (s : bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Definition member (v : nat) (s : bag) : bool :=
  if beq_nat (count v s) 0 then false else true.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: t => match (beq_nat v h) with
                | true => t (* Halt recursion. *)
                | false => h :: remove_one v t
                end
    end.

  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;5;5;1;4]) = 2.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: t => match beq_nat v h with
                | true => remove_all v t
                | false => h :: remove_all v t
                end
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | nil => true
    | h :: t => match member h s2 with
                | true => subset t (remove_one h s2)
                | false => false
                end
    end.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.

  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.

  Theorem beq_nat_refl:
    forall n : nat, beq_nat n n = true.
  Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite -> IHn. reflexivity. Qed.

  Theorem bag_theorem:
    forall v s, count v (add v s) = S (count v s).
  Proof.
    intros v s.
    induction s as [ | h t ].
    - simpl.
      rewrite -> beq_nat_refl.
      reflexivity.
    - simpl.
      rewrite -> beq_nat_refl. reflexivity. Qed.

  Theorem nil_app:
    forall l : natlist, [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem tl_length_pred:
      forall l : natlist, pred (length l) = length (tl l).
  Proof.
    intros l. destruct l as [ | n l' ]; reflexivity. Qed.

  Theorem app_assoc:
    forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [ | n l1' IHl1' ].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity. Qed.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => (rev t) ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem app_length:
    forall l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [ | n l1' IHl1' ].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity. Qed.

  Theorem rev_length:
    forall l : natlist, length (rev l) = length l.
  Proof.
    intros l. induction l as [ | n l' IHl' ].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite -> add_comm.
      reflexivity.
  Qed.

  Theorem app_nil_r:
    forall l : natlist, l ++ [] = l.
  Proof.
    intros l. induction l as [ | n l' IHl' ].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity. Qed.

  Theorem rev_app_distr:
    forall l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2. induction l1 as [ | n l1' IHl1' ].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite <- app_assoc. reflexivity. Qed.

  Theorem rev_involutive:
    forall l : natlist, rev (rev l) = l.
  Proof.
    intros l. induction l as [ | n l' IHl' ].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity. Qed.

  Theorem app_assoc4:
    forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    replace (((l1 ++ l2) ++ l3) ++ l4) with ((l1 ++ l2) ++ l3 ++ l4).
    rewrite -> app_assoc. reflexivity.
    rewrite <- app_assoc. reflexivity. Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [ | h1 t1 ].
    - reflexivity.
    - simpl.
  Abort.
End NatList.
