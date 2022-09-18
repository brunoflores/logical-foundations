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
