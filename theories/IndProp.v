From LF Require Export Logic.
From Coq Require Import Lia.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T}.
Arguments App {T}.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
         (H1 : s1 =~ re1)
         (H2 : s2 =~ re2)
         : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
         (H1 : s1 =~ re1)
         : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
         (H2 : s2 =~ re2)
         : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
         (H1 : s1 =~ re)
         (H2 : s2 =~ (Star re))
         : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).
