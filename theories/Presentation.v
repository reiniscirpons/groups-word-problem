From HB Require Import structures.
Require Import RelationClasses.
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype.

From GWP Require Import Equivalence EquivalenceAlgebra.

Open Scope setoid_group_scope.

(* a rewriting rule u -> v *)
Definition relation (Sigma: Type) := ((seq Sigma) * (seq Sigma)) % type.

(* NOTE(reiniscirpons): Instead of using hierarchy builder to define a
   presentation, we instead define it using a Structure like its done in
   MonoidPresentation. I think this is mathematically cleaner, and we 
   can now have the same alphabet used for different presentations. *)
(* NOTE(reiniscirpons): We only consider finitely presented monoids
   and groups, so the finType restriction is ok. *)
Structure presentation := Pres {
  sigma: finType;
  relations: seq (relation sigma);
}.

Section WordProblem.

Variable P: presentation.

Let word := (seq (sigma P)).
Let relation := (relation (sigma P)).

(* Whether a rewriting relation `r` is a part of the presentation. *)
Let isRelationOf (r: relation) := r \in relations P.

Let initialWord (r: relation) : word := fst r.
Let finalWord (r: relation) : word := snd r.

(* `Derivation u v` is the type of witnesses of derivations from
  `u: word` to `v: word` in `P: Presentation` *)
Inductive Derivation : word -> word -> Prop :=
  | Derivation_reduction (r: relation) (a c: word) :
      isRelationOf r ->
      Derivation (a ++ (initialWord r) ++ c) (a ++ (finalWord r) ++ c)
  | Derivation_refl (u: word): Derivation u u
  | Derivation_symm (u u': word) : Derivation u u' -> Derivation u' u
  | Derivation_trans (u v w: word) :
      Derivation u v -> Derivation v w -> Derivation u w.

(* The word problem of the presentation `P`. *)
Definition word_problem (u v: word) : Prop := Derivation u v.
End WordProblem.

(* `presented P` is the structure associated to the presentation `P := (Sigma; R)`.
   ie. `presented P` is Sigma^* quotiented by the smallest equivalence relation compatible with R *)
Definition presented P := (seq (sigma P)).

(* TODO(reiniscirpons): Do we need this still? *)
Section InstancesFromList.
Variable P: presentation.
HB.instance Definition _ := Equality.copy (presented P) (seq (sigma P)).
End InstancesFromList.

(* In a presented structure, equality is given as whether two words are derived. *)
Section PresentedEq.
Variable P: presentation.

(* Note: a Notation must be used here otherwise HB declares the mixin on the constant M. *)
Local Notation M := (presented P).

Let eq := word_problem P.

Lemma M_refl : forall x, eq x x.
Proof. exact: Derivation_refl. Qed.
Lemma M_symm : forall x y, eq x y -> eq y x.
Proof. exact: Derivation_symm. Qed.
Lemma M_trans : forall x y z, eq x y -> eq y z -> eq x z.
Proof. exact: Derivation_trans. Qed.

(* HB bug: having a duplicate (P: presentation) results in a Ocaml assertion failure *)
HB.instance Definition _ := @isSetoid.Build M eq M_refl M_symm M_trans.
End PresentedEq.

(* All presented structures have a monoid structure *)
Section PresentedMonoid.

Variable P: presentation.

Local Notation M := (presented P).


Let concat := @cat (sigma P).
Let epsilon : seq (sigma P) := nil.

Local Infix ".@" := (concat: M -> M -> M) (at level 50).

Let concatA : forall (x y z : M),
  x .@ (y .@ z) \approx (x .@ y) .@ z.
Proof. by move=> x y w; rewrite /concat catA. Qed.
Let concat1s : forall (x: M),
  epsilon .@ x \approx x.
Proof. by move=> x; rewrite /concat /=. Qed.
Let concats1 : forall (x: M),
  x .@ epsilon \approx x.
Proof. by move=> x; rewrite /concat cats0. Qed.

Let concat_extl: forall (u v a: M),
  u \approx v -> a .@ u \approx a .@ v.
Proof.
move=> u v a; elim => [|//||].
- move=> r c b H.
  rewrite /concat !(catA a).
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- by symmetry.
- by move=> ? v'; transitivity (a .@ v').
Qed.

Let concat_extr: forall (u v b: M),
  u \approx v -> u .@ b \approx v .@ b.
Proof.
move=> u v a; elim => [|//||].
- move=> r c b H.
  rewrite /concat -!catA.
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- by symmetry.
- by move=> ? v'; transitivity (v' .@ a).
Qed.

HB.instance Definition _ := isMonoid.Build M
  concat epsilon
  concatA concat1s concats1
  concat_extl concat_extr.
End PresentedMonoid.


Section Reduction.

Context {P: presentation}.
Local Notation M := (presented P).

Lemma reduction:
  forall (a b u v: M),
  (u, v) \in relations P -> a * u * b \approx a * v * b.
Proof.
  move=> a b u v H; rewrite /mul /= -!catA.
  by apply: (Derivation_reduction _ (u, v)).
Qed.

Lemma reduction_rule: forall (u v: presented P),
  (u, v) \in relations P -> u \approx v.
Proof.
move=> u v Hin.
transitivity (1 * u * 1)%sg;
  first by rewrite mul1g mulg1.
transitivity (1 * v * 1)%sg;
  last by rewrite mul1g mulg1.
exact: (reduction 1 1)%sg.
Qed.

End Reduction.
Module PresentationNotations.
Notation "\epsilon" := ([::] : presented _)
  (at level 10, only parsing).
Notation "\ε" := ([::] : presented _) (at level 10, only printing).
Notation "x \mod P" := (x : presented P)
  (at level 10, only parsing).
Notation "x % P" := (x \mod P)
  (at level 10, only printing, format "x % P").
End PresentationNotations.


Import PresentationNotations.

(* NOTE(reiniscirpons): Declaring cat and cons to multiplication
   law conversions to simplify future lemmas. *)
Lemma cat_law: forall P (x y: presented P),
  (x ++ y) \mod P = x * y.
Proof. by []. Qed.

Lemma cons_law: forall P (a: sigma P) (x: presented P),
  (a :: x) \mod P = [:: a] \mod P * x.
Proof. by []. Qed.

Lemma rcons_law: forall P (a: sigma P) (x: presented P),
  (rcons x a) \mod P = x * [:: a] \mod P.
Proof. move => P a; by elim => [//|b w /= ->]. Qed.

(* Show that preserving relations and multiplication is enough to define
   monoid morphism out of presented monoid. *)
(* TODO(reiniscirpons): How can reuse the IsMonoidMorphism axioms here? *)
HB.factory Record isRelationPreservingMorphism
  (P: presentation) (B: monoid) (f: presented P -> B)
    (* TODO(reiniscirpons): Why does this caause a bug?*)
    (* & isMonoidMorphism (presented P) B f*)
    := {
    morphism_preserve_relations: 
      forall u v, (u, v) \in relations P -> f u \approx f v;
    morphism_preserve_e:
      f 1 \approx 1;
    morphism_preserve_law:
      forall x y, f (x * y) \approx (f x) * (f y);
}.

HB.builders Context (P: presentation) (M: monoid) f of 
  isRelationPreservingMorphism P M f.

  Fact f_preserve_equiv: forall x y,
    x \approx y -> f x \approx f y.
  Proof.
    move => x y; elim => [[u v] p s |//||] /=.
    - move/morphism_preserve_relations => H.
      by rewrite !morphism_preserve_law H.
    - move => u v _ H; by apply approx_sym.
    - move => u v w _ H1 _ H2; by apply approx_trans with (f v).
  Qed.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ f f_preserve_equiv.
  
  HB.instance Definition _ :=
    isMonoidMorphism.Build _ _ f morphism_preserve_e morphism_preserve_law.
HB.end.

Section ExtensionToMonoidMorphism.

Variable P: presentation.
Variable M: monoid.
Variable f: sigma P -> M.

Definition extension: presented P -> M :=
  fun l => prod (map f l).
Arguments extension / !_.

Lemma extension_cons:
  forall (a: sigma P) (w: presented P),
  extension (a::w) = (f a) * (extension w).
Proof. done. Qed.

Lemma extension_universality:
  forall (varphi: morphism (presented P) M),
    (forall a: sigma P, varphi ([::a] \mod P) \approx f a) -> 
    (forall w: presented P, 
      varphi w \approx extension w).
Proof.
  move => varphi Heq; elim => [|a w' IH].
  - exact morphism_preserve_one.
  by rewrite {1}cons_law morphism_preserve_mul extension_cons IH Heq.
Qed.

Lemma extension_preserve_one: extension 1 \approx 1.
Proof. done. Qed.

Lemma extension_preserve_singleton:
  forall (c: sigma P), extension ([:: c] \mod P) \approx f c.
Proof.
  by move => c /=; rewrite mulg1.
Qed.

Lemma extension_preserve_mul: forall (x y: presented P),
  extension (x * y) \approx (extension x) * (extension y).
Proof.
  move => x y; by rewrite /extension -prod_cat map_cat.
Qed.

(* TODO(reiniscirpons): No new instance was generated but thats ok,
   we intend to use the isRelationPreservingMorphism factory later
   on when we need it. Right? *)
HB.instance Definition _ := 
  isMonoidMorphism.Build _ _
    extension
    extension_preserve_one
    extension_preserve_mul.

End ExtensionToMonoidMorphism.
Arguments extension {_ _} _ / !_. 

HB.mixin Record hasInvertibleLetters (P: presentation) := {
  invl : sigma P -> sigma P;
  invlK : forall c, invl (invl c) = c;
  invlgV : forall c, [::c] \mod P * [:: invl c] \mod P \approx 1;
  invlVg : forall c, [:: invl c] \mod P * [:: c] \mod P \approx 1;
}.
#[short(type="invertiblePresentationType")]
HB.structure Definition InvertiblePresentation :=
  { P & hasInvertibleLetters P }.

Notation "c ^~1" := (invl c): setoid_group_scope.

Lemma invl_inj:
  forall (P: invertiblePresentationType) (x y: sigma P),
    x^~1 = y^~1 <-> x = y.
Proof.
  split => [H|-> //]; by rewrite -(invlK x) -(invlK y) H.
Qed.

Section InvertiblePresentedGroup.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Definition inv_word (w: G) : G := map invl (rev w).

Lemma inv_word_mul : forall x y: G, inv_word (x * y) \approx (inv_word y) * (inv_word x).
Proof. by move=> x y; rewrite /inv_word/=/mul/= !map_rev map_cat rev_cat. Qed.

Lemma inv_word_left : forall w: G, w * (inv_word w) \approx 1.
Proof.
elim=> [|a w IH]; first exact: mul1g.
rewrite /inv_word/mul/= rev_cons map_rcons -rcons_cat -cats1 -cat1s.
have: [:: a] \mod P * (w \mod P * inv_word w) * [:: a^~1] \mod P \approx 1;
  last by done.
by rewrite IH invlgV.
Qed.

Lemma inv_word_right : forall w: G, (inv_word w) * w \approx 1.
Proof.
elim=> [|a w IH]; first exact: mul1g.
rewrite /inv_word/mul/= rev_cons map_rcons cat_rcons -cat1s -(cat1s a) !(catA _ _ w).
have: (inv_word w) * ([:: a^~1] \mod P * [:: a]\mod P) * w \approx 1;
  last by done.
by rewrite invlVg mulg1 IH.
Qed.

(* TODO(reiniscirpons): In general many of the prior lemmas we have developed
   in EquivalenceAlgebra, like power_inv hold not only with setoid equality
   but with full = rocq equality for finitely presented groups.
   This is because the specific choice of multiplication and inversion
   we made. This causes some weird level switching however
   (group -> underlying free monoid), and looks a bit ugly in the theory.
   We should figure out how to fix, but maybe after the main essence of the
   theory is there.
*)
Lemma inv_word_cons:
  forall w a, inv_word (a::w) = (inv_word w) ++ [:: a^~1].
Proof.
  by move => w a; rewrite /inv_word rev_cons map_rcons cats1.
Qed.

Lemma inv_word_rcons:
  forall w a, inv_word (rcons w a) =  a^~1 :: inv_word w.
Proof.
  by move => w a; rewrite /inv_word rev_rcons.
Qed.

Lemma inv_word_cat:
  forall x y, inv_word (x ++ y) = inv_word y ++ inv_word x.
Proof.
  by move => x y; rewrite /inv_word !map_rev map_cat rev_cat.
Qed.

Lemma inv_word_involutive:
  forall x, inv_word (inv_word x) = x.
Proof.
  move => x; rewrite /inv_word !map_rev revK -map_comp.
  elim: x => [//|hx tx IH].
  by rewrite /= IH invlK.
Qed.


HB.instance Definition _ := isGroup.Build G inv_word inv_word_mul inv_word_left inv_word_right.

End InvertiblePresentedGroup.

Section Cancellation.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Variable a x y : G.

Lemma cancel_left : a * x \approx a * y -> x \approx y.
Proof.
move=> H.
rewrite -(mul1g x) -(mul1g y) -(invVg a) -!mulgA.
by rewrite H.
Qed.

Lemma cancel_right : x * a \approx y * a -> x \approx y.
Proof.
move=> H.
rewrite -(mulg1 x) -(mulg1 y) -(invgV a) !mulgA.
by rewrite H.
Qed.

End Cancellation.
Arguments cancel_left {_}.
Arguments cancel_right {_}.
