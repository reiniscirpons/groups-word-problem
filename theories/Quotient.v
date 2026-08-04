From Stdlib Require Import Relations RelationClasses Ensembles Morphisms.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import monoid.

Open Scope group_scope.

(* TODO(reiniscirpons):

   Should we use the mathcomp-analysis classical_sets library?
   It builds up a sizeable library of set theory in the style
   of mathcomp, but with Prop instead of bool, which is what 
   we (generally) need.

   However, using this library means accepting propext,
   funext and CID (i.e. every existential prop allows us to
   find its witness) axioms.

   Maybe not in the first instance?
*)

(* NOTE(reiniscirpons): Duplicate notations, but
   capitalize to indicate they are Prop variants? *)
Notation "{ 'Pred' U }" := (Ensemble U)
  (at level 0, format "{ 'Pred'  U }").
Notation "x \In A" := (In _ A x)
  (at level 70, no associativity, format "'[hv' x '/ '  \In  A ']'").
Notation "A =I B" := (Same_set _ A B)
  (at level 70, no associativity,
  format "'[hv' A '/ '  =I  B ']'").
Notation "{ 'Subset' A <= B }" := (Included _ A B)
  (at level 0, A, B at level 69,
  format "'[hv' { 'Subset'  A '/ '  <=  B } ']'").
Notation "[ 'Set' u ]" := (Singleton _ u)
  (u at level 99, format "[ 'Set'  u ]").


Instance SameSetReflexivity U : Reflexive (Same_set U).
Proof. by move => A; split. Qed.
Instance SameSetSymmetry U: Symmetric (Same_set U).
Proof. by move => A B []; split. Qed.
Global Instance IncludedTransitivity U : Transitive (Included U).
Proof. by move => A B C HAB HBC x /HAB /HBC. Qed.
Instance SameSetTransitivity U : Transitive (Same_set U).
Proof.
  move => A B C [HAB HBA] [HBC HCB]; split;
  by apply transitivity with B.
Qed.
Global Instance SameSetEquivalence U: Equivalence (Same_set U) | 10 := { }.

Section MonoidPred.
(* Monoid of propositional predicate defined subsets of a
   base monoid U. *)
Context {U: monoidType}.

Definition Pred_mul (A B: {Pred U}): {Pred U} :=
  fun u => exists v w, (v \In A) /\ (w \In B) /\ u = v * w.

Local Notation "A *@: B" := (Pred_mul A B)
  (at level 24, left associativity): group_scope.

Lemma Pred_mulgA: forall A B C,
  A *@: (B *@: C) =I A *@: B *@: C.
Proof.
  move => A B C; split => u.
  - case => [v [w [Hv [[x [y [Hx [Hy Hw]]]] Hu]]]].
    exists (v * x); exists y.
    split;
      last by split => [//|]; rewrite -mulgA -Hw.
    by exists v; exists x.
  - case => [v [w [[x [y [Hx [Hy Hv]]]] [Hw Hu]]]].
    exists x; exists (y * w).
    split => [//|]; split;
      last by rewrite mulgA -Hv.
    by exists y; exists w.
Qed.

Lemma Pred_mulg1: forall A,
  A *@: [Set 1] =I A.
Proof.
  move => A; split => [u [v [w [Hv [[] ->]]]]|u Hu].
  - by rewrite gsimp.
  - exists u; exists 1; split => [//|]; split => [//|].
    by rewrite gsimp.
Qed.

Lemma Pred_mul1g: forall A,
  [Set 1] *@: A =I A.
Proof.
  move => A; split => [u [v [w [[] [Hw ->]]]]|u Hu].
  - by rewrite gsimp.
  - exists 1; exists u;
    split => [//|]; split => [//|];
    by rewrite gsimp.
Qed.
End MonoidPred.
Notation "A *@: B" := (Pred_mul A B)
  (at level 24, left associativity): group_scope.

(* NOTE(reiniscirpons): mirrors Corelib.Relations.Relation_Definitions *)
Section CongruenceRelation.
Import Relation_Definitions.

Context {U: monoidType}.
Variable rho: relation U.

Definition left_extensional: Prop :=
  forall z x y, rho x y -> rho (z * x) (z * y).

Definition right_extensional: Prop :=
  forall z x y, rho x y -> rho (x * z) (y * z).

Record congruence : Prop :=
  { congr_refl : reflexive U rho;
    congr_trans : transitive U rho;
    congr_sym : symmetric U rho;
    congr_extl: left_extensional;
    congr_extr: right_extensional}.
End CongruenceRelation.

#[global]
Create HintDb monoid_sets.

#[global]
Hint Unfold left_extensional right_extensional: monoid_sets.

#[global]
Hint Resolve Build_congruence congr_refl congr_trans
  congr_sym congr_extl congr_extr: monoid_sets.

(* NOTE(reiniscirpons): mirrors Corelib.Classes.RelationClasses *)
Section CongruenceRelationClass.

Context {U: monoidType}.


Class LeftExtensional (rho : relation U) :=
  left_extensionality:
    forall z x y, rho x y -> rho (z * x) (z * y).

Class RightExtensional (rho : relation U) :=
  right_extensionality:
  forall z x y, rho x y -> rho (x * z) (y * z).

Class Congruence (rho : relation U) : Prop := {
  #[global] Congruence_Reflexive :: Reflexive rho ;
  #[global] Congruence_Symmetric :: Symmetric rho ;
  #[global] Congruence_Transitive :: Transitive rho ;
  #[global] Congruence_LeftExtensional :: LeftExtensional rho ;
  #[global] Congruence_RightExtensional :: RightExtensional rho ;
}.

Global Instance Congruence_Equivalence {R}
  `(E: Congruence R) : Equivalence R | 10 := { }.

End CongruenceRelationClass.

#[global]
Instance Congruence_proper_type U rho `(Congruence U rho) :
  Proper (rho ==> rho ==> rho) *%g.
Proof.
  move => x y Hxy z w Hzw.
  apply transitivity with (x * w).
  - by apply left_extensionality.
  - by apply right_extensionality.
Qed.

Section CongruenceCongruence.

Context {U: monoidType} {rho: relation U}.
Hypothesis Hcong: congruence rho.

#[global]
Canonical Structure congruence_Congruence: Congruence rho.
Proof.
  split.
  - by apply congr_refl.
  - by apply congr_sym.
  - by apply congr_trans.
  - by apply congr_extl.
  - by apply congr_extr.
Defined.
End CongruenceCongruence.

Section CongruenceRelationQuotient.
Context {U: monoidType}.
Variable rho: relation U.

Definition congruence_range: {Pred {Pred U}} :=
  fun A => exists u, A =I rho u.

Record congruence_class_of : Type :=
  CongruenceClass {
    pred_of_class :> {Pred U};
    _ : congruence_range pred_of_class
  }.
Arguments CongruenceClass {_} _.

Lemma congruence_class_one_proof : congruence_range (rho 1).
Proof.
  (* Is it not possible to avoid having the explicitly
     write reflexivity here? *)
  by exists 1; reflexivity.
Qed.
Definition congruence_class_one :=
  CongruenceClass congruence_class_one_proof.

Hypothesis Hcong: congruence rho.

Lemma congruence_range_mul: forall A B : congruence_class_of,
  congruence_range (A *@: B).
Proof.
  move => [A /= [u Hu]] [B /= [v Hv]];
  exists (u * v); split => [w [x [y [Hx [Hy ->]]]]|].
  - apply Hu in Hx; apply Hv in Hy.
    rewrite /(_ \In _).
    rewrite /(_ \In _) in Hx.
    rewrite Hx.



Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv (B : coset_of) : coset_range B^-1.
Proof.



Definition coset_inv B := Coset (coset_range_inv B).
Hypothesis Hcongr: congruence rho.





End CongruenceRelationQuotient.
