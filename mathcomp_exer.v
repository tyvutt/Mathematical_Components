(*******    Mathematical Components    *******)
(* Part One  : Basics for Formal Mathematics *)
(* Chapter 1 : Functions and Computation     *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example Gauss n : \sum_(0 <= i < n.+1) i = (n * n.+1) %/ 2.
Proof.
elim: n =>[|n IHn]; first by apply: big_nat1.
rewrite big_nat_recr //= IHn addnC -divnMDl //.
by rewrite mulnS muln1 -addnA -mulSn -mulnS.
Qed.

Definition f (n : nat) : nat := n + 1.
Print f.
Eval compute in f 3.

Definition g (n m : nat) : nat := n + m * 2.
Definition h (n : nat) : nat -> nat := fun m => n + m * 2.
Print g.
Print h.

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).
Eval compute in repeat_twice f 98.

Inductive bool := true | false.
Definition twoVthree (b : bool) := if b is true then 2 else 3.
Eval compute in twoVthree true.
Eval compute in twoVthree false.

Inductive nat := O | S (n : nat).

Definition predn n := if n is p.+1 then p else n.
Eval compute in predn 5.
Definition pred5 n := if n is u.+1.+1.+1.+1.+1 then u else 0.
Eval compute in pred5 11.

Definition three_patterns n :=
  match n with
    u.+1.+1.+1.+1.+1 => u 
  | v.+1 => v
  | 0 => n
  end.
Eval compute in three_patterns 7.

Definition same_bool b1 b2 :=
  match b1, b2 with
    true, true => true
  | false, false => true
  | _, _ => false
  end.

Fixpoint addn n m :=
  match n with
    0 => m
  | p.+1 => (addn p m).+1 
  end.

About cons.
Check 1 :: 2 :: 3 :: nil.

Definition head T (x0 : T) (s : seq T) :=
  if s is x :: _ then x else x0.

Fixpoint size A (s : seq A) :=
  if s is _ :: tl then (size tl).+1 else 0.

Fixpoint map A B (f : A -> B) s :=
  if s is e :: tl then f e :: map f tl else nil.

Notation "[ ’seq’ E | i <- s ]" := (map (fun i => E) s).
Eval compute in [seq i.+1 | i <- [:: 1; 2]].

Inductive option A := None | Some (a : A).

Print foldr.
Print iota.
Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).
Eval compute in \sum_( 1 <= i < 3 ) (i * 2 - 1).
Eval compute in \sum_( 1 <= i < 5 ) i.

(* Exercise 1 The triple data type *)
(* Exercise 2 Addition with iteration *)
(* Exercise 3 Multiplication with iteration *)
(* Exercise 4 Find the n-th element *)
(* Exercise 5 List reversal *)
(* ** Exercise 7 All words of size n *)

(* Chapter 2 : First Steps in Formal Proofs *)
Section Chap2.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check 3 = 3.
Check 3 = 4.

Locate "=".
About eq.

Lemma negbK b : ~~ (~~ b) = b.
Proof. by case: b. Qed.

Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
move: n.
case.
by[].
move=> k.
by[].
(* by case: => [|k]. *)
Qed.

(* Exercise 8 Truth tables *)
(* Exercise 9 Rewriting *)
(* * Exercise 10 Induction *)
(* ** Exercise 11 Multiple induction *)

End Chap2.
(* Chapter 3 : Type Theory *)
Check ex.
Check or_ind.

Inductive True : Prop := I.
Inductive False : Prop := .
Print not.

Definition not (A : Prop) := A -> False.
Definition exfalso (P : Prop) (f : False) : P :=
  match f with end. (* no constructors, no branches *)

(* Chapter 4 : First Steps in Formal Proofs *)
Definition bool_Prop_equiv (P : Prop) (b : bool) :=
  b = true <-> P. (* Reflection views *)
Lemma test_bool_Prop_equiv b P : bool_Prop_equiv P b -> P \/ ~ P.
Proof.
case b.
case.
move => hlr hrl.
left.
apply: hlr.
reflexivity.
case.
move => hlr hrl.
right.
move => hP.
move: (hrl hP).
by[].
Qed.
(* Part Two  : Formalization Techniques *)
(* Chapter 5 : Implicit Parameters *)
(* Chapter 6 : Sub-Types *)
(* Chapter 7 : Natural numbers *)


(* Part Three : Synopsis *)