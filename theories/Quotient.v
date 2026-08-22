From Stdlib Require Import Relations Morphisms Ensembles.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

Declare Scope setoid_group_scope.
Delimit Scope setoid_group_scope with sg.
Local Open Scope setoid_group_scope.

(* NOTE: Subsets are the wrong primitive for quotients of monoids.
   This is different to groups, where subsets work to model
   cosets for quotients.

   The problem is precisely that, unlike cosets, a single
   equivalence class of a congruence does not necessarily
   determine the whole congruence. On the other hand, if we
   are given a coset C, then we can recover the group that
   made it by computing C*g^-1 for any element g in C.

   I believe the correct primitive is pointed relations,
   i.e. a tuple (u, rho) consisting of an element u in U and a
   relation rho on U, i.e. U * (U -> U -> Prop).
   Define multiplication componentwise, with some reasonable
   definition of multiplying two relations (see below).
   Then, for a given rho, we just instantiate the elements of
   -/rho as precisely those of the form (u, rho).
*)
Reserved Notation "A ~* B"
  (at level 48, left associativity, format "A  ~*  B").
Reserved Notation "A *~ B"
  (at level 48, left associativity, format "A  *~  B").
Reserved Notation "A \approx B"
  (at level 70, no associativity).
Reserved Notation "A ≈ B"
  (at level 70, no associativity, format "A  ≈  B").
Reserved Notation "{ 'Set' T }"
  (at level 0, format "{ 'Set'  T }").
Reserved Notation "x \In A"
  (at level 70, no associativity, format "'[hv' x '/ '  \In  A ']'").
Reserved Notation "[ x ]_ rho"
  (at level 0, format "[ x ]_ rho").

(* A pointed relation is simply a relation together with
    a point in that relation. *)
Record pointed_relation (U: Type) := PointedRelation {
  relation_of: relation U;
  point_of: U
}.

Section PointedRelation.
  Context {U: semigroupType}.

  (* NOTE: If the underlying type is a monoid (or semigroup),
     we can define multiplication on pointed relations.
     There are many reasonable multiplications we could use:

     1. (u, rho)*(v, sigma) = (u*v, rho \vee sigma),
        where vee is the congruence join operation, i.e.
        rho \vee sigma is the least congruence containing
        both rho and sigma. This is in some sense the most
        mathematically accurate definition.
        Accordingly, if we try to multiply two elements
        such that rho >= sigma, i.e. U/rho is a smaller quotient
        than U/sigma, then the product will drop down to U/rho.
        So e.g. U * U/rho = U/rho for all rho in this case.

        The main drawback: the congruence join is a fairly
        difficult object to reason about, and could lead
        to some pains later on.

     2. (u, rho)*(v, sigma) = (u*v, rho \cap sigma), where
        \cap is the intersection operation. Here we get
        the opposite effect of the above: if rho >= sigma
        then the product will ascend to sigma.
        So e.g. U * U/rho = U with this convention.
        The intersection is a much simpler object to reason about.
        However, we still have a drawback that we need to
        reason using setoid equality (since prop intersection is
        is only associative in the weak sense, i.e.
        <-> instead of =). And furthermore, always dropping
        above is problematic, since we sometimes want to
        stay in the lower level.

     3. Have two operations for left and right multiplication,
        respectively. I.e.
          (u, rho) ~* (v, sigma) = (u * v, rho)
          (u, rho) *~ (v, sigma) = (u * v, sigma)
        In this manner, we can always choose which
        of the two monoids we drop down to.
        With this convention U ~* U/rho = U and
        U *~ U/rho = U/rho. Its also pretty simple to
        implement and as a bonus associativity holds without
        setoid. This is the approach we take below.
        Note that when rho = sigma, both products coincide.
     *)
  Definition pointed_relation_lmul (A B: pointed_relation U):
    pointed_relation U :=
    match A, B with
    | PointedRelation rho u, PointedRelation sigma v =>
      PointedRelation rho (u * v)
    end.

  Definition pointed_relation_rmul (A B: pointed_relation U):
    pointed_relation U :=
    match A, B with
    | PointedRelation rho u, PointedRelation sigma v =>
      PointedRelation sigma (u * v)
    end.

  Lemma pointed_relation_lmulA: associative pointed_relation_lmul.
  Proof.
    move => [u rho] [v sigma] [w tau] /=.
    by rewrite mulgA.
  Qed.

  Lemma pointed_relation_rmulA: associative pointed_relation_rmul.
  Proof.
    move => [u rho] [v sigma] [w tau] /=.
    by rewrite mulgA.
  Qed.

  Definition pointed_relation_equiv (A B: pointed_relation U): Prop :=
    (forall u v, relation_of A u v <-> relation_of B u v) /\
    (relation_of A (point_of A) (point_of B)).

End PointedRelation.
Notation "A ~* B" := (pointed_relation_lmul A B).
Notation "A *~ B" := (pointed_relation_rmul A B).
Notation "A \approx B" :=
  (pointed_relation_equiv A B) (only parsing).
Notation "A ≈ B" := 
  (pointed_relation_equiv A B) (only printing, format "A  ≈  B").

Notation "[ u ]_ rho" := (PointedRelation rho u) : setoid_group_scope.

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
Arguments congruenceP {_} _.

#[global]
Create HintDb congruences.

#[global]
Hint Unfold left_extensional right_extensional: congruences.

#[global]
Hint Resolve Build_congruence congr_refl congr_trans
  congr_sym congr_extl congr_extr: congruences.

Notation "{ 'Set' T }" := (Ensemble T).
Section CongruenceRelationQuotient.
Context {U: monoidType}.
Variable rho: relation U.
Hypothesis Hcong: congruence rho.

Definition congruence_range (A: pointed_relation U): Prop := 
  relation_of A = rho.
Arguments congruence_range / _.

Record congruence_class_of : Type :=
  CongruenceClass {
    pointed_relation_of_class :> pointed_relation U;
    _ : congruence_range pointed_relation_of_class
  }.
Arguments CongruenceClass {_} _.

Lemma relation_of_class: forall (A: congruence_class_of),
  relation_of A = rho.
Proof. by case. Qed.

Lemma congruence_class_one_proof : congruence_range (PointedRelation rho 1).
Proof. done. Qed.

Definition congruence_class_one :=
  CongruenceClass congruence_class_one_proof.

Notation "1" := congruence_class_one: setoid_group_scope.

Lemma point_of_one: point_of 1 = 1%g.
Proof. done. Qed.

(* NOTE: This choice subtly forces left actions. *)
Lemma congruence_range_mul: forall A B : congruence_class_of,
  congruence_range (A ~* B).
Proof.
  by move => [[sigma u] /= ->] [[tau v] /= _].
Qed.

Definition congruence_class_mul A B :=
  CongruenceClass (congruence_range_mul A B).

Notation "A * B" := (congruence_class_mul A B): setoid_group_scope.

Lemma point_of_mul: forall A B,
  point_of (A * B) = ((point_of A) * (point_of B))%g.
Proof. 
  by move => [[sigma u /=] Hu] [[]].
Qed.

Lemma congruence_class_mulgA: forall A B C,
  A * (B * C) \approx A * B * C.
Proof.
  (* TODO(reiniscirpons): why do I need to do this,
     why can't Rocq just automatically figure this out? *)
  move/congruenceP: Hcong => Hcong'.
  move => A B C; split => [u v|].
  - by rewrite !relation_of_class.
    (* TODO(reiniscirpons): Why do I need to call reflexivity here?
      Shouldn't the "by" tactic close it? *)
  - by rewrite relation_of_class !point_of_mul mulgA; reflexivity.
Qed.

Lemma congruence_class_mulg1: forall A,
  A * 1 \approx A.
Proof.
  move/congruenceP: Hcong => Hcong'.
  move => A; split => [u v|].
  - by rewrite !relation_of_class.
  - rewrite relation_of_class point_of_mul mulg1;
    by reflexivity.
Qed.

Lemma congruence_class_mul1g: forall A,
  1 * A \approx A.
Proof.
  move/congruenceP: Hcong => Hcong'.
  move => A; split => [u v|].
  - by rewrite !relation_of_class.
  - rewrite relation_of_class point_of_mul mul1g;
    by reflexivity.
Qed.

Variable Q: {Set U}.

Definition quotient: {Set congruence_class_of} :=
  fun A => exists u, Q u /\ (relation_of A (point_of A) u).

End CongruenceRelationQuotient.
(* TODO(reiniscirpons): canonical instances for base group,
   left, right multiplication etc. *)
Arguments quotient {_} _.
Notation "Q / rho" := (quotient rho Q) : setoid_group_scope.
Notation "1" := congruence_class_one: setoid_group_scope.
Notation "A * B" := (congruence_class_mul A B): setoid_group_scope.

Notation "x \In A" := (In _ A x).
Section Submonoids.
  Context {U: monoidType}.
  Variable M: {Set U}.
  Variable rho: relation U.

  Definition mulg_closed: Prop :=
    forall (u v: U), u \In M -> v \In M -> (u * v)%g \In M.

  Definition mul_closed (Q: {Set (congruence_class_of rho)}): Prop :=
    forall (A B: congruence_class_of rho), A \In Q -> B \In Q -> A * B \In Q.

  Lemma quotient_mul_closed:
    mulg_closed ->
    congruence rho ->
    mul_closed (M / rho).
  Proof.
    move => HM /congruenceP Hrho A B [u [HMu HAu]] [v [HMv HBv]].
    exists (u * v)%g; split.
    - by apply HM.
    - rewrite relation_of_class in HAu;
      rewrite relation_of_class in HBv.
      by rewrite relation_of_class point_of_mul HAu HBv; reflexivity.
  Qed.
End Submonoids.
