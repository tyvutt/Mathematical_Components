(* From mathcomp Require Import all_ssreflect. *)
Set Implicit Arguments.
Unset Strict Implicit.
(* Import Prenex Implicits. *)

(* 集合 *)
Definition mySet (M: Type) := M -> Prop.
(* 部分集合 *)
Definition belong {M: Type}(A: mySet M)(x: M) :Prop
 := A x.
Notation "x ∈ A" := (belong A x) (at level 11).
Axiom axiom_mySet : forall (M: Type)(A: mySet M),
 forall (x: M), (x ∈ A) \/ ~(x ∈ A).
(* 空集合 *)
Definition myEmptySet {M: Type} : mySet M :=
 fun _ => False.
(* 母集合 *)
Definition myMotherSet {M: Type} : mySet M :=
 fun _ => True.
(* 包含関係・等号 *)
Definition mySub {M} := fun (A B : mySet M) =>
 (forall (x: M), (x ∈ A) -> (x ∈ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
Variable M: Type.

Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
Proof.
 unfold mySub.
 unfold belong.
 intros x h.
 unfold myMotherSet.
 trivial.
Qed.

Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
Proof. 
 unfold mySub.
 unfold belong.
 unfold myEmptySet.
 intros x h.
 contradiction.
Qed.

Lemma rfl_Sub (A :mySet M) : (A ⊂ A).
Proof.
 unfold mySub.
 unfold belong.
 intros x h.
 apply h. (* assumption. *)
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

Section 集合の等号.
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
intros h.
split.
destruct h as [h1 h2].
apply h2.
apply h.
Qed.
End 集合の等号.

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
split. 
unfold mySub.
unfold myComplement.
intros x h.
unfold myMotherSet.
unfold belong.
trivial.

intros x.
intros Hfull.
unfold myComplement.
unfold belong.
unfold myEmptySet.
auto. (* intuition. *)
Qed.

Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
Proof.
apply axiom_ExteqmySet.
unfold eqmySet.
split.
unfold mySub.
unfold myComplement.
intros x H.
generalize (axiom_mySet A x).
intros h.
intuition.
contradiction.

unfold mySub.
unfold myComplement.
intros x H.
intuition.
intros H0.
contradiction.
Qed.

Lemma cMother_Empty : (@myMotherSet M)^c = myEmptySet.
Proof.
rewrite <- cEmpty_Mother.
rewrite cc_cancel.
reflexivity.
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
intros Hinjf.
intros Hinjg.
intros x y HxA HyA H.
apply (Hinjg x y HxA HyA).
apply (Hinjf (g x)(g y)).
apply gAB.
apply HxA.
apply gAB.
apply HyA.
apply H.
Qed.

Lemma CompoTrans : (f ・ g) ∈Map A \to C.
Proof.
revert fBC.
revert gAB.
unfold MapCompo.
unfold myMap.
intros Hab Hbc.
intros t Ha.
generalize (Hab t Ha).
generalize (Hbc (g t)). (* g t : M2 *)
trivial.
Qed.

(* ImSub: Im g ⊂ B *)
Lemma ImSub : (ImgOf gAB) ⊂ B.
Proof.
unfold mySub.
unfold belong.
unfold ImgOf.
intros x h.
destruct h as [x0 h].
intuition.
rewrite H.
apply gAB.
apply H0.
Qed.
End 写像.

(* 有限型のライブラリ *)
Variable M : finType.

Definition p2S (pA: pred M) : mySet M := 
  fun(x: M) => if (x \in pA) then True else False.

Notation "\{ x 'in' pA \}" := (p2S pA).
Print pred.
Section finTypeを用いた有限集合.
Lemma Mother_predT : myMotherSet = \{ x in M \}.
Proof. exact. Qed.

(* reflect
   : Prop -> bool -> Set *)
Lemma myFinBelongP (x: M) (pA: pred M) :
reflect (x ∈ \{ x in pA \}) (x \in pA).
Proof.
unfold p2S.
unfold belong.
(* iffP
   : forall (P Q : Prop) (b : bool),
       reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b
   idP
   : reflect ?b1 ?b1
   iffP idP
   : (?b -> ?Q) -> (?Q -> ?b) -> reflect ?Q ?b *)
apply (iffP idP) => H.
by rewrite (_ : (x \in pA) = true).
have testH : (x \in pA) || ~~(x \in pA).
set t := x \in pA.
revert t.
elim.
done.
done.
revert testH.
move /orP.
elim.
done.
intros Harg.
rewrite (_: (x \in pA) = false) in H.
done.
(* negbTE
   : forall b : bool, ~~ b -> b = false *)
apply negbTE.
done.
Qed.

Lemma myFinSubsetP (pA pB : pred M) :
  reflect (\{ x in pA \} ⊂ \{ x in pB \})
  (pA \subset pB).
Proof.
rewrite /mySub.
apply /(iffP idP) => H.
move => x.
move=> /myFinBelongP.
move => H2.
apply /myFinBelongP.
move: H.
(* subsetP
   : reflect {subset ?A <= ?B} (?A \subset ?B) *)
move => /subsetP.
(* Definition sub_mem {T} mp1 mp2 := 
    forall x : T, in_mem x mp1 -> in_mem x mp2. *)
rewrite /sub_mem.
apply.
by[].
apply /subsetP.
rewrite /sub_mem.
move => x.
move /myFinBelongP.
move => HpA.
apply /myFinBelongP.
apply H.
by[].
Qed.

Lemma  Mother_Sub (pA : pred M) :
  myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
Proof.
rewrite Mother_predT.
move => /myFinSubsetP.
move => H.
move => x.
apply /myFinBelongP.
(* predT_subset
	 : forall (T : finType) (A : {pred T}),
       T \subset A -> forall x : T, x \in A *)
apply predT_subset.
apply H.
Qed.

Check subset_trans.
Lemma transitive_Sub' (pA pB pC : pred M):
 \{ x in pA \} ⊂ \{ x in pB \}
 -> \{ x in pB \} ⊂ \{ x in pC \}
 -> \{ x in pA \} ⊂ \{ x in pC \}.
Proof.
move /myFinSubsetP.
move => HAB.
move => /myFinSubsetP.
move => HBC.
apply /myFinSubsetP.
apply /(subset_trans HAB HBC).
Qed.

Lemma transitive_Sub'' (pA pB pC : pred M):
 \{ x in pA \} ⊂ \{ x in pB \}
 -> \{ x in pB \} ⊂ \{ x in pC \}
 -> \{ x in pA \} ⊂ \{ x in pC \}.
Proof. apply transitive_Sub. Qed.
End finTypeを用いた有限集合.


Section ライブラリfinsetの利用.
From mathcomp Require Import finset.

Variable M : finType.
Lemma deMorgan (A B C : {set M}) :
  (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof.
(* setP
   : forall (T : finType) (A B : {set T}), 
     A =i B <-> A = B   *)
(* Notation "A =i B" := 
     (eq_mem (mem A) (mem B)) : type_scope. *)
apply /setP.
intros x.
(* in_setU
	 : forall (T : finType) (x : T) (A B : {set T}),
     (x \in A :|: B) = (x \in A) || (x \in B)   *)
(* in_setI
	 : forall (T : finType) (x : T) (A B : {set T}),
       (x \in A :&: B) = (x \in A) && (x \in B) *)
rewrite inE.
rewrite inE.
rewrite inE.
rewrite inE.
rewrite inE.
(* rewrite  5!inE. *)
(* rewrite   !inE  *)
(* orb_andl
	 : left_distributive orb andb *)
rewrite <- orb_andl.
done.
Qed.
End ライブラリfinsetの利用.