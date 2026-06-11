From HB Require Import structures.
Require Import ssreflect ssrfun RelationClasses Setoid Morphisms.

(* Types with an equality, noted `\approx`.
   
   All types have an equality in Rocq: `eq`.
   However this equality type is essentially definitional equality,
   while our `\approx` can be any equivalence relation.
   This is useful to represent quotiented types. *)

HB.mixin Record isSetoid T := {
  approx : T -> T -> Prop;

  approx_refl : forall x, approx x x;
  approx_sym : forall x y, approx x y -> approx y x;
  approx_trans : forall x y z,
    approx x y -> approx y z -> approx x z;
}.
#[short(type = "setoid")]
HB.structure Definition _ := { T of isSetoid T }.

Hint Resolve approx_refl : core.

Infix "\approx" := approx (at level 70, no associativity).
Infix "≈" := approx (at level 70, no associativity).
Notation "x \approx y :> T" :=
  ((x: T) \approx (y: T)) (at level 70, no associativity).
Notation "x ≈ y :> T" := (x \approx y :> T).

(* Defining Rocq relation classes.
   This enables the `reflexivity`/`symmetry`/`transitivity` tactics to work with `eqType`s. *)
Section ApproxEquivalence.
Variable T: setoid.
Let approx := @approx T.

Instance ApproxReflexivity : Reflexive approx.
Proof. exact: isSetoid.approx_refl. Qed.
Instance ApproxSymmetry : Symmetric approx.
Proof. exact: isSetoid.approx_sym. Qed.
Instance ApproxTransitivity : Transitive approx.
Proof. exact: isSetoid.approx_trans. Qed.
Instance ApproxEquivalence : Equivalence approx := {}.
End ApproxEquivalence.
Existing Instance ApproxReflexivity.
Existing Instance ApproxSymmetry.
Existing Instance ApproxTransitivity.
Existing Instance ApproxEquivalence.

(* TODO(reiniscirpons): Is this already part of the library? *)
HB.mixin Record isSetoidMorphism
    (S T: setoid) (f: S -> T) := {
  morphism_preserve_approx: forall x y,
    x \approx y -> f x \approx f y;
}.
#[short(type="setoidMorphism")]
HB.structure Definition SetoidMorphism (G H: setoid) :=
  { f of isSetoidMorphism G H f }.

Section ProperMorphism.
Context {S T: setoid}.
Variable f: setoidMorphism S T.

(* NOTE(reiniscirpons): *)
(* Ad-hoc polymorphism resolution *)
(* 
   (C t1), search C in known instances of Proper
   not found, then tactic tries to decompose into
   succession of proper Terms. Composition might
   require other relations.
   C1, C2 should be known as proper constants, if
   not more decomposition. If no solution found then
   error. Otherwise compose proofs.
*)
Global Instance : Proper (approx ==> approx) f.
Proof. exact: morphism_preserve_approx. Qed.
End ProperMorphism.

Section SetoidMorphismComp.
Context {A B C: setoid}.
Variable (f: setoidMorphism A B).
Variable (g: setoidMorphism B C).

Lemma comp_preserve_equiv :
  forall x y, x \approx y -> (g \o f) x \approx (g \o f) y.
Proof.
  move => x y H; by repeat apply /morphism_preserve_approx.
Qed.

HB.instance Definition _ :=
  isSetoidMorphism.Build A C (g \o f) comp_preserve_equiv.
End SetoidMorphismComp.
