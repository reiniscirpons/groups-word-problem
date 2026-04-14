From HB Require Import structures.
Require Import ssreflect ssrfun RelationClasses Setoid Morphisms.

(* TODO(reiniscirpons): How does this differ from eqType? *)

(* Types with an equality, noted `==`.
   
   All types have an equality in Rocq: `eq`.
   However this equality type is essentially definitional equality,
   while our `==` can be any equivalence relation. This is useful to
   represent quotiented types. *)
HB.mixin Record hasEq T := {
  eq : T -> T -> Prop;

  refl : forall x, eq x x;
  symm : forall x y, eq x y -> eq y x;
  trans : forall x y z, eq x y -> eq y z -> eq x z;
}.
#[short(type = "equivType")]
HB.structure Definition EqProp := { T of hasEq T }.

Hint Resolve refl : core.

Infix "==" := eq (at level 70, no associativity).
Notation "x == y :> T" := ((x: T) == (y: T)) (at level 70, no associativity).

(* Defining Rocq relation classes.
   This enables the `reflexivity`/`symmetry`/`transitivity` tactics to work with `eqType`s. *)
Section EqEquivalence.
Variable T: equivType.
Let eq := @eq T.

Instance EqReflexivity : Reflexive eq.
Proof. exact: hasEq.refl. Qed.
Instance EqSymmetry : Symmetric eq.
Proof. exact: hasEq.symm. Qed.
Instance EqTransitivity : Transitive eq.
Proof. exact: hasEq.trans. Qed.
Instance EqEquivalence : Equivalence eq := {}.
End EqEquivalence.
Existing Instance EqReflexivity.
Existing Instance EqSymmetry.
Existing Instance EqTransitivity.
Existing Instance EqEquivalence.

(* TODO(reiniscirpons): Is this already part of the library? *)
HB.mixin Record isSetoidMorphism (S T: equivType) (f: S -> T) := {
  morphism_preserve_equiv: forall x y, x == y -> f x == f y;
}.
#[short(type="setoidMorphism")]
HB.structure Definition SetoidMorphism (G H: equivType) := { f of isSetoidMorphism G H f }.

Section ProperMorphism.
Variable S T: equivType.
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
Global Instance : Proper (eq ==> eq) f.
Proof. exact: morphism_preserve_equiv. Qed.
End ProperMorphism.

Section SetoidMorphismComp.

Variables (A B C: equivType).
Variable (f: setoidMorphism A B).
Variable (g: setoidMorphism B C).

Lemma comp_preserve_equiv :
  forall x y, x == y -> (g \o f) x == (g \o f) y.
Proof.
  move => x y H;
  by apply /morphism_preserve_equiv /morphism_preserve_equiv.
Qed.

HB.instance Definition _ := isSetoidMorphism.Build A C (g \o f) comp_preserve_equiv.
End SetoidMorphismComp.
Arguments comp_preserve_equiv {_ _ _}.
