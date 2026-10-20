From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x \approx y"
  (at level 70, no associativity).
Reserved Notation "x ≈ y"
  (at level 70, no associativity, format "x  ≈  y").
Reserved Notation "x \approx y :> T"
  (at level 70, no associativity).
Reserved Notation "x ≈ y :> T"
  (at level 70, no associativity, format "x  ≈  y  :>  T").

Declare Scope setoid_group_scope.
Delimit Scope setoid_group_scope with sg.
Local Open Scope setoid_group_scope.

(* NOTE: Setoids are sometimes defined in terms of their apartness relation,
   such is the approach taken e.g. in CoRN. I believe this has to do with
   the fact that for the real numbers, there is a simple witness of
   apartness, but not necessarily a simple witness of equality.

   We are in the opposite case: equivalence modulo a congruence has a simple
   positive witness: the elementary sequence, but there is no simple negative
   witness in general. So we take the equivalence as the basic relation
   defining a setoid.
*)

HB.mixin Record hasEquiv T := {
  equiv : T -> T -> Prop;

  equiv_refl : forall x, equiv x x;
  equiv_sym : forall x y, equiv x y -> equiv y x;
  equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z;
}.
#[short(type = "setoidType")]
HB.structure Definition Setoid := { T of hasEquiv T }.

Bind Scope setoid_group_scope with Setoid.sort.

Local Notation "x \approx y" := (equiv x y)
  (only parsing): setoid_group_scope.
Local Notation "x ≈ y" := (x \approx y)
  (only printing) : setoid_group_scope.
Local Notation "x \approx y :> T" := ((x: T) \approx (y: T))
  (only parsing): setoid_group_scope.
Local Notation "x ≈ y :> T" := (x \approx y :> T)
  (only printing) : setoid_group_scope.

Hint Resolve equiv_refl equiv_sym equiv_trans : core.

#[deprecated(since="2026-09-11", note="Use hasEquiv instead.", use=hasEquiv)]
Notation hasEq T := (hasEquiv T).
#[deprecated(since="2026-09-11", note="Use equiv instead.", use=equiv)]
Definition eq {T} := @equiv T.
#[deprecated(since="2026-09-11", note="Use equiv_refl instead.", use=equiv_refl)]
Definition refl {T} := @equiv_refl T.
#[deprecated(since="2026-09-11", note="Use equiv_sym instead.", use=equiv_sym)]
Definition symm {T} := @equiv_sym T.
#[deprecated(since="2026-09-11", note="Use equiv_trans instead.", use=equiv_trans)]
Definition trans {T} := @equiv_trans T.
#[deprecated(since="2026-09-11", note="Use setoidType instead.", use=setoidType)]
Notation equivType := setoidType.
#[deprecated(since="2026-09-11", note="Use Setoid instead.", use=Setoid)]
Notation EqProp T := (Setoid T).

Hint Resolve equiv_refl : core.

#[deprecated(since="2026-09-11", note="Use \approx instead.")]
Infix "==" := equiv (at level 70, no associativity).
#[deprecated(since="2026-09-11", note="Use x \approx y :> T instead.")]
Notation "x == y :> T" := ((x: T) \approx (y: T)) (at level 70, no associativity).

(* Defining Rocq relation classes.
   This enables the `reflexivity`/`symmetry`/`transitivity` tactics to work
   with `setoidType`s. *)
Section EqEquivalence.
  Variable sT: setoidType.
  Let equiv := @equiv sT.

  Instance EquivReflexivity : Reflexive equiv.
  Proof. exact: equiv_refl. Qed.
  Instance EquivSymmetry : Symmetric equiv.
  Proof. exact: equiv_sym. Qed.
  Instance EquivTransitivity : Transitive equiv.
  Proof. exact: equiv_trans. Qed.
  Instance EquivEquivalence : Equivalence equiv := {}.
End EqEquivalence.
Existing Instance EquivReflexivity.
Existing Instance EquivSymmetry.
Existing Instance EquivTransitivity.
Existing Instance EquivEquivalence.

HB.mixin Record isSetoidMorphism (S T: setoidType) (f: S -> T) := {
  equivfM: forall x y,
    x \approx y -> f x \approx f y;
}.
#[short(type="setoidMorphism")]
HB.structure Definition SetoidMorphism (G H: setoidType) :=
  { f of isSetoidMorphism G H f }.

#[deprecated(since="2026-09-11", note="Use equivfM instead.", use=equivfM)]
Definition morphism_preserve_equiv {S T f} := @equivfM S T f.

Section ProperMorphism.
  Context {S T: setoidType}.
  Variable f: setoidMorphism S T.

  Instance SetoidMorphismProper: Proper (equiv ==> equiv) f.
  Proof. exact: equivfM. Qed.
End ProperMorphism.
Existing Instance SetoidMorphismProper.

Section SetoidMorphismComp.
  Context {A B C: setoidType}.
  Variable (f: setoidMorphism A B).
  Variable (g: setoidMorphism B C).

  Lemma comp_equiv: forall x y,
    x \approx y -> (g \o f) x \approx (g \o f) y.
  Proof.
    move => x y H;
    by apply /equivfM /equivfM.
  Qed.

  HB.instance Definition _ :=
    isSetoidMorphism.Build A C (g \o f) comp_equiv.
End SetoidMorphismComp.

HB.mixin Record isInjective (A B: setoidType) (f: A -> B) := {
  injfM: forall x y, f x \approx f y -> x \approx y;
}.

#[short(type="injectiveFunType")]
HB.structure Definition Injective (A B: setoidType) :=
  { f of isInjective A B f
       & isSetoidMorphism A B f}.

HB.mixin Record isSurjective (A B: setoidType) (f: A -> B) := {
  surjfM: forall y, exists x, f x \approx y;
}.

#[short(type="surjectiveFunType")]
HB.structure Definition Surjective (A B: setoidType) :=
  { f of isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="bijectiveFunType")]
HB.structure Definition Bijective (A B: setoidType) :=
  { f of isInjective A B f
       & isSurjective A B f
       & isSetoidMorphism A B f}.

#[deprecated(since="2026-09-11", note="Use injfM instead.", use=equivfM)]
Notation injectivity_property := injfM.

#[deprecated(since="2026-09-11", note="Use surjfM instead.", use=equivfM)]
Notation surjectivity_property := surjfM.

#[deprecated(since="2026-09-11", note="Use comp_equiv instead.", use=equivfM)]
Notation comp_preserve_equiv := comp_equiv.

Prenex Implicits equiv.
Notation "x \approx y" := (equiv x y)
  (only parsing): setoid_group_scope.
Notation "x ≈ y" := (x \approx y)
  (only printing) : setoid_group_scope.
Notation "x \approx y :> T" := ((x: T) \approx (y: T))
  (only parsing): setoid_group_scope.
Notation "x ≈ y :> T" := (x \approx y :> T)
  (only printing) : setoid_group_scope.
