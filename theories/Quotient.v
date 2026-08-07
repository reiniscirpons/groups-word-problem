From Stdlib Require Import Relations Morphisms.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import monoid.

Open Scope group_scope.


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
  (at level 70, no associativity, format "A ≈ B").

(* A pointed relation is simply a relation together with
    a point in that relation. *)
Definition pointed_relation (U: Type) := (U * relation U)%type.

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
    pointed_relation U:=
    match A, B with
    | (u, rho), (v, sigma) => (u * v, rho)
    end.

  Definition pointed_relation_rmul (A B: pointed_relation U):
    pointed_relation U:=
    match A, B with
    | (u, rho), (v, sigma) => (u * v, sigma)
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
End PointedRelation.
Notation "A ~* B" := (pointed_relation_lmul A B).
Notation "A *~ B" := (pointed_relation_rmul A B).

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

Section CongruenceRelationQuotient.
Context {U: monoidType}.
Variable rho: relation U.

Definition congruence_range (A: pointed_relation U): Prop := 
  snd A = rho.
Arguments congruence_range / _.

Record congruence_class_of : Type :=
  CongruenceClass {
    pointed_relation_of_class :> pointed_relation U;
    _ : congruence_range pointed_relation_of_class
  }.
Arguments CongruenceClass {_} _.

Definition congruence_class_equiv (A B: congruence_class_of) :=
  rho
    (fst (pointed_relation_of_class A))
    (fst (pointed_relation_of_class B)).

Notation "A \approx B" :=
  (congruence_class_equiv A B) (only parsing).
Notation "A ≈ B" := 
  (congruence_class_equiv A B) (only printing, format "A  ≈  B").

Hypothesis Hcong: congruence rho.

Lemma congruence_class_one_proof : congruence_range (1, rho).
Proof. done. Qed.

Definition congruence_class_one :=
  CongruenceClass congruence_class_one_proof.

Notation "1" := congruence_class_one.

(* NOTE: This choice subtly forces left actions. *)
Lemma congruence_range_mul: forall A B : congruence_class_of,
  congruence_range (A ~* B).
Proof.
  by move => [[u sigma] /= ->] [[v tau] /= _].
Qed.

Definition congruence_class_mul A B :=
  CongruenceClass (congruence_range_mul A B).

Notation "A * B" := (congruence_class_mul A B).

Lemma congruence_class_mulgA: forall A B C,
  A * (B * C) \approx A * B * C.
Proof.
  (* TODO(reiniscirpons): why do I need to do this,
     why can't Rocq just automatically figure this out? *)
  move/congruenceP: Hcong => Hcong'.
  move => [[u sigma] /= Hs] [[v tau] /= Ht] [[w ypsilon] /= Hy].
  (* TODO(reiniscirpons): Why do I need to call reflexivity here?
     Shouldn't the "by" tactic close it? *)
  by rewrite /(_ \approx _) /= mulgA; reflexivity.
Qed.

Lemma congruence_class_mulg1: forall A,
  A * 1 \approx A.
Proof.
  move/congruenceP: Hcong => Hcong'.
  move => [[u sigma Hu] /=];
  by rewrite /(_ \approx _) /= mulg1; reflexivity.
Qed.

Lemma congruence_class_mul1g: forall A,
  A * 1 \approx A.
Proof.
  move/congruenceP: Hcong => Hcong'.
  move => [[u sigma Hu] /=];
  by rewrite /(_ \approx _) /= mulg1; reflexivity.
Qed.
End CongruenceRelationQuotient.
Notation "A \approx B" :=
  (congruence_class_equiv A B) (only parsing).
Notation "A ≈ B" := 
  (congruence_class_equiv A B) (only printing, format "A  ≈  B").
(* TODO(reiniscirpons): canonical instances for base group,
   left, right multiplication etc. *)
