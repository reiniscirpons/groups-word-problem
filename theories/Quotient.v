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

(* NOTE(reiniscirpons): Duplicate notations from mathcomp, but
   capitalize to indicate they are Prop variants. *)
Notation "{ 'Pred' U }" := (Ensemble U)
  (at level 0, format "{ 'Pred'  U }").
Notation "x \In A" := (In _ A x)
  (at level 70, no associativity, format "'[hv' x '/ '  \In  A ']'").
Notation "A =I B" := (Same_set _ A B)
  (at level 70, no associativity,
  format "'[hv' A '/ '  =I  B ']'").
Notation "A :/\: B" := (Intersection _ A B)
  (at level 48, left associativity, format "A  :/\:  B").
Notation "A \Intersects B" := (Inhabited _ (A :/\: B))
  (at level 70, no associativity,
  format "A  \Intersects  B").
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

Local Notation "A :*: B" := (Pred_mul A B)
  (at level 24, left associativity): group_scope.

Lemma Pred_mulgA: forall A B C,
  A :*: (B :*: C) =I A :*: B :*: C.
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
  A :*: [Set 1] =I A.
Proof.
  move => A; split => [u [v [w [Hv [[] ->]]]]|u Hu].
  - by rewrite gsimp.
  - exists u; exists 1; split => [//|]; split => [//|].
    by rewrite gsimp.
Qed.

Lemma Pred_mul1g: forall A,
  [Set 1] :*: A =I A.
Proof.
  move => A; split => [u [v [w [[] [Hw ->]]]]|u Hu].
  - by rewrite gsimp.
  - exists 1; exists u;
    split => [//|]; split => [//|];
    by rewrite gsimp.
Qed.
End MonoidPred.
Notation "A :*: B" := (Pred_mul A B)
  (at level 24, left associativity): group_scope.


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

Lemma congruenceP: congruence -> Congruence rho.
Proof.
  move => Hcong; split.
  - by exact: congr_refl.
  - by exact: congr_sym.
  - by exact: congr_trans.
  - by exact: congr_extl.
  - by exact: congr_extr.
Qed.

End CongruenceRelation.

#[global]
Create HintDb monoid_sets.

#[global]
Hint Unfold left_extensional right_extensional: monoid_sets.

#[global]
Hint Resolve Build_congruence congr_refl congr_trans
  congr_sym congr_extl congr_extr: monoid_sets.

Section CongruenceRelationQuotient.
Context {U: monoidType}.
Variable rho: relation U.

(* NOTE(reiniscirpons): Sadly we cannot improve the below
   requirement that A is a subset of rho u. Ideally we would
   want this to be set equivalence =I, but this is not
   possible.

   Indeed, consider the monoid on {0, 1, a, b} defined by
   the following multiplication table

   *|1ab0
   ------
   1|1ab0
   a|abb0
   b|bbb0
   0|0000
   
   Then the equivalence rho with classes {1}, {a} and {b, 0} is a
   congruence relation whose quotient is a monoid.
   But the product of the class {a} with itself {a} is
   {a} * {a} = {b}, which is not a congruence class.

   So in fact, the best we can do is to require that the
   product is a subset of a congruence class.
*)
Definition congruence_range: {Pred {Pred U}} :=
  fun A => exists u, {Subset A <= rho u}.

Record congruence_class_of : Type :=
  CongruenceClass {
    pred_of_class :> {Pred U};
    _ : congruence_range pred_of_class
  }.
Arguments CongruenceClass {_} _.

Hypothesis Hcong: congruence rho.

Lemma congruence_class_one_proof : congruence_range [Set 1].
Proof.
  (* TODO(reiniscirpons): Can we make Hcong automatically
     register rho as a Congruence instance without this line? *)
  move/congruenceP: Hcong => Hcong'.
  (* TODO(reiniscirpons): Can we make it so that \In auto
     expands when needed? *)
  exists 1 => x [] {x}.
  (* TODO(reiniscirpons): Can we make it so that *)
  by rewrite /(_ \In _); reflexivity.
Qed.

Definition congruence_class_one :=
  CongruenceClass congruence_class_one_proof.
Local Notation "1_" := congruence_class_one.

Lemma congruence_range_mul: forall A B : congruence_class_of,
  congruence_range (A :*: B).
Proof.
  (* TODO(reiniscirpons): Can we make Hcong automatically
     register rho as a Congruence instance without this line? *)
  move/congruenceP: Hcong => Hcong'.
  move => [A /= [u Hu]] [B /= [v Hv]].
  exists (u * v) => w [x [y [/Hu Hx [/Hv Hy -> {w}]]]].
  (* TODO(reiniscirpons): Can we make it so that \In auto
     expands when needed? *)
  rewrite /(_ \In _); transitivity (u * y).
  - by apply congr_extl.
  - by apply congr_extr.
Qed.

Definition congruence_class_mul A B :=
  CongruenceClass (congruence_range_mul A B).
Local Notation "A *_ B" := (congruence_class_mul A B)
  (at level 24, left associativity).

Lemma congruence_class_mulgA: forall A B C,
  A *_ (B *_ C) =I A *_ B *_ C.
Proof.
  by move => A B C; apply Pred_mulgA.
Qed.

Lemma congruence_class_mulg1: forall A,
  A *_ 1_ =I A.
Proof.
  by move => A; apply Pred_mulg1.
Qed.

Lemma congruence_class_mul1g: forall A,
  1_ *_ A =I A.
Proof.
  by move => A; apply Pred_mul1g.
Qed.

(* TODO(reiniscirpons): This gives us a monoid structure, but what
   about equality? We cant use =I since, as we remarked above,
   we may shrink the equivalence class when multiplying.
  
   I was thingking maybe A \Intersects B, i.e. to consider
   two sets equal if they have non-empty intersection, but this
   is also no good, since its possible to have two disjoint
   subsets of an equivalence class of rho.

   We don't want to use rho precisely because we want the
   objects to have equality independent of the underlying relation.
*)

(* TODO(reiniscirpons): I conclude that subsets are the wrong
   primitive for monoids.

   I think the correct primitive is pointed relations,
   i.e. a tuple (u, rho) consisting of an element u in U and a
   relation rho on U, i.e. U * (U -> U -> Prop).
   Define multiplication componentwise, using intersection of
   relations as the operation on relations so
   (u, rho) * (v, nu) = (u * v, rho /\ nu).
   Equality operator is given by checking if the elements belong
   to the intersection, i.e. (u, rho) =R (v, nu) if and only if
   (u, v) in (rho /\ nu), i.e. if both rho u v and nu u v hold
   (need to flip one of the relations for this to be symmetric, but
   maybe it doesn't matter?).

   Then, for a given rho, we just instantiate the elements of
   -/rho as precisely those of the form (u, rho), and reap the
   benefits.
*)

End CongruenceRelationQuotient.
