(* From mathcomp Require Import all_ssreflect. *)
Set Implicit Arguments.
(* Unset Strict Implicit. *)
(* Import Prenex Implicits. *)

(* Require Import Ensembles. *)

(* 集合 *)
(* R(a) ⇔ a ∈ {x ∈ M | R(x)} *)
Definition mySet (M: Type) := M -> Prop.
(* 部分集合 *)
Definition belong {M: Type}(A: mySet M)(x: M) :Prop
 := A x.
Notation "x ∈ A" := (belong A x) (at level 11).
(* 補集合の補集合は元の集合 *)
Axiom axiom_mySet : forall (M: Type)(A: mySet M),
 forall (x: M), (x ∈ A) \/ ~(x ∈ A).
(* 包含関係*)
Definition mySub {M} := fun (A B : mySet M) =>
 (forall (x: M), (x ∈ A) -> (x ∈ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).
(* 空集合 *)
Definition myEmptySet {M: Type} : mySet M :=
 fun _ => False.
(* 母集合 *)
Definition myMotherSet {M: Type} : mySet M :=
 fun _ => True.

Section 包含関係.
Variable M: Type.

Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
Proof.
 unfold mySub.
 unfold belong.
 unfold myMotherSet.
 intros.
 trivial.
Qed.

Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
Proof. 
 unfold mySub.
 unfold belong.
 unfold myEmptySet.
 intros.
 contradiction.
Qed.

Lemma rfl_Sub (A :mySet M) : (A ⊂ A).
Proof.
 unfold mySub.
 unfold belong.
 intros.
 assumption. (* trivial *)
Qed.

Lemma transitive_Sub (A B C : mySet M) :
  (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
Proof. 
intros h1 h2.
intros x.
intros h3.
apply h2.
apply h1.
apply h3.
Qed.
End 包含関係.

(* 集合の等号 *)
Definition eqmySet {M: Type} :=
 fun (A B: mySet M) => (A ⊂ B /\ B ⊂ A).
Axiom axiom_ExteqmySet : forall {M: Type}(A B: mySet M),
 eqmySet A B -> A = B.

Section 等号.
Variable Mother: Type.

Lemma rfl_eqS (A: mySet Mother) : eqmySet A A.
Proof. 
unfold eqmySet.
split.
apply rfl_Sub.
apply rfl_Sub.
Qed.

Lemma sym_eqS (A B : mySet Mother) : eqmySet A B -> eqmySet B A.
Proof.
unfold eqmySet.
intros H.
split.
destruct H. (* as [H H0] *)
apply H0.
apply H.
Qed.
End 等号.

(* 補集合 *)
Definition myComplement {M: Type}(A: mySet M) : mySet M :=
 fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A)(at level 11).
(* 和集合 *)
Definition myCup {M: Type} (A B: mySet M) : mySet M :=
 fun (x : M) => (x ∈ A) \/ (x ∈ B).
Notation "A ∪ B" := (myCup A B)(at level 11).  

Section 演算.
Variable M: Type.

Lemma cEmpty_Mother : (@myEmptySet M)^c = myMotherSet.
Proof.
apply axiom_ExteqmySet.
unfold eqmySet.
unfold mySub.
unfold myComplement.
unfold myMotherSet.
unfold belong.
unfold myEmptySet.
split. 
intros x h.
trivial.
intros x.
intros.
auto. (* intuition. *)
Qed.

Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
Proof.
apply axiom_ExteqmySet.
unfold eqmySet.
unfold mySub.
unfold myComplement.
split.
intros.
generalize (axiom_mySet A x).
(* intros. *)
intuition.
contradiction.

intuition.
intros H0.
contradiction.
Qed.

Lemma cMother_Empty : (@myMotherSet M)^c = myEmptySet.
Proof.
rewrite <- cEmpty_Mother.
apply cc_cancel.
Qed.
End 演算.

(* 集合間の写像 *)
Definition myMap {M1 M2: Type}
(A: mySet M1)(B: mySet M2)(f: M1 -> M2) :=
  (forall (x : M1), (x ∈ A) -> ((f x) ∈ B)).
Notation " f ∈Map A \to B" := (myMap A B f) (at level 11).

Definition MapCompo {M1 M2 M3 : Type}
(f: M2 -> M3)(g: M1 -> M2) : M1 -> M3 := 
  fun (x: M1) => f (g x).
Notation "f ・ g" := (MapCompo f g)(at level 11).

(* Image: f(x) *)
Definition ImgOf {M1 M2: Type}(f: M1 -> M2)
{A: mySet M1}{B: mySet M2}
(_: f ∈Map A \to B) : mySet M2 :=
  fun (y: M2) => (exists (x: M1), y = f x /\ x ∈ A).

(* Injection *)
Definition mySetInj {M1 M2: Type}(f: M1 -> M2)
(A: mySet M1)(B: mySet M2)
(_: f ∈Map A \to B) :=
 forall (x y: M1), (x ∈ A) -> (y ∈ A) -> (f x = f y) -> (x = y).

(* Surjection *)
Definition mySetSur {M1 M2: Type}(f: M1 -> M2)
{A: mySet M1}{B: mySet M2}
(_: f ∈Map A \to B) :=
 forall (y : M2), (y ∈ B) -> (exists (x : M1), (x ∈ A) -> (f x = y)).

(* Bijection *)
Definition mySetBi {M1 M2: Type}(f: M1 -> M2)
(A: mySet M1)(B: mySet M2)
(fAB: f ∈Map A \to B) :=
  (mySetInj fAB) /\ (mySetSur fAB).

Section 写像.
Variable M1 M2 M3: Type.
Variable f: M2 -> M3.
Variable g: M1 -> M2.
Variable A: mySet M1.
Variable B: mySet M2.
Variable C: mySet M3.
Hypothesis gAB: g ∈Map A \to B.
Hypothesis fBC: f ∈Map B \to C.

Lemma transitive_Inj (fgAC: (f ・ g) ∈Map A \to C) :
mySetInj fBC -> mySetInj gAB -> mySetInj fgAC.
Proof.
unfold mySetInj.
intros.
apply (H0 x y H1 H2).
apply (H (g x)(g y)).
apply gAB.
apply H1.
apply gAB.
apply H2.
apply H3.
Qed.

Lemma CompoTrans : (f ・ g) ∈Map A \to C.
Proof.
unfold MapCompo.
unfold myMap.
intros.
revert gAB. (* generalize gAB x H *)
revert fBC. (* generalize fBC x H *)
auto.
Qed.

(* ImSub: Im g ⊂ B *)
Lemma ImSub : (ImgOf gAB) ⊂ B.
Proof.
unfold mySub.
unfold belong.
unfold ImgOf.
intros.
destruct H.
intuition.
rewrite H0.
apply gAB.
assumption.
Qed.
End 写像.