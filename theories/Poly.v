From LF Require Export Lists.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list : Type -> Type.
Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X}.

Fixpoint repeat {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat x count')
  end.

Example test_repeat1 : repeat 4 2 = cons 4 (cons 4 nil).
Proof. reflexivity. Qed.

Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Example test_app :
  app (cons 1 (cons 2 nil)) (cons 3 nil) = (cons 1 (cons 2 (cons 3 nil))).
Proof. reflexivity. Qed.

Fixpoint rev {X:Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Example test_rev1 : rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2 : rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Fixpoint length {X:Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_length : length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                    (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123 := [1; 2; 3].

(* Exercises *)

Theorem app_nil_r : forall (X:Type), forall l:list X, l ++ [] = l.
Proof. induction l.
       - reflexivity.
       - simpl. rewrite -> IHl. reflexivity. Qed.

Theorem app_assoc : forall (A:Type) (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof. intros A l m n. induction l.
       - reflexivity.
       - simpl. rewrite -> IHl. reflexivity. Qed.

Theorem app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof. intros X l1 l2. induction l1.
       - reflexivity.
       - simpl length. rewrite -> IHl1. reflexivity. Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. intros X l1 l2. induction l1.
       - simpl. rewrite -> app_nil_r. reflexivity.
       - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity. Qed.

Theorem rev_involutive : forall X : Type, forall l : list X, rev (rev l) = l.
Proof. intros X l. induction l.
       - reflexivity.
       - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity. Qed.

(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.
Compute (combine [1; 2] [false; false; true; true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => match (split t) with
                 | (xs, ys) => (x :: xs, y :: ys)
                 end
  end.

Example test_split :
  split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof. reflexivity. Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.
Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
             | O => Some a
             | S n' => nth_error l' n'
             end
  end.

Example test_nth_error1 : nth_error [4; 5; 6; 7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1]; [2]] 1 = Some [2].
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1; 2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
            else filter test t
  end.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example test_filter1 : filter even [1; 2; 3; 4] = [2; 4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool := (length l) =? 1.

Example test_filter2 :
  filter length_is_1
         [ [1; 2]; [3]; [4]; [5; 6; 7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
