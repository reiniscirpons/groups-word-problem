From elpi.apps Require Import coercion.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool Morphisms.
From mathcomp Require Import seq eqtype choice bigop.
From mathcomp Require Import
  ssrnat ssrint ssralg monoid all_algebra zify.
Import GRing.Theory.
From GWP Require Import Equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "*%sg" (at level 0).

Local Open Scope setoid_group_scope.

HB.mixin Record isSetoidMonoid M of hasEquiv M := {
  mul : M -> M -> M;
  one : M;
  mulsA : forall x y z,
    mul x (mul y z) \approx mul (mul x y) z;
  mul1s : forall x,
    mul one x \approx x;
  muls1 : forall x,
    mul x one \approx x;
  muls_extl : forall x y z,
    y \approx z -> mul x y \approx mul x z;
  muls_extr : forall x y z,
    y \approx z -> mul y x \approx mul z x;
}.
#[short(type="setoidMonoidType")]
HB.structure Definition SetoidMonoid := { G of isSetoidMonoid G & hasEquiv G }.

Bind Scope setoid_group_scope with SetoidMonoid.sort.

(* Every monoid is a setoid monoid wrt the trivial setoid. *)
HB.builders Context M of isMonoid M.
  
  HB.instance Definition _ :=
    hasEquiv.Build M eq_Reflexive eq_Symmetric eq_Transitive.

  Fact mulg_extl : forall (x y z: M),
    y \approx z -> mul x y \approx mul x z.
  Proof. by move => x y z ->. Qed.

  Fact mulg_extr : forall (x y z: M),
    y \approx z -> mul y x \approx mul z x.
  Proof. by move => x y z ->. Qed.

  HB.instance Definition _ :=
    isSetoidMonoid.Build M mulgA mul1g mulg1 mulg_extl mulg_extr.

HB.end.  

Local Notation "*%sg" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : setoid_group_scope.
Local Notation "1" := one : setoid_group_scope.

#[deprecated(since="2026-09-11", note="Use isSetoidMonoid instead.")]
Notation isMonoid M := (isSetoidMonoid M).
#[deprecated(since="2026-09-11", note="Use mul instead.")]
Notation law := mul.
#[deprecated(since="2026-09-11", note="Use one instead.")]
Notation e := one.
#[deprecated(since="2026-09-11", note="Use mulsA instead.")]
Notation associativity := mulsA.
#[deprecated(since="2026-09-11", note="Use mul1s instead.")]
Notation neutral_left := mul1s.
#[deprecated(since="2026-09-11", note="Use muls1 instead.")]
Notation neutral_right := muls1.
#[deprecated(since="2026-09-11", note="Use muls_extl instead.")]
Notation congruent_left := muls_extl.
#[deprecated(since="2026-09-11", note="Use muls_extr instead.")]
Notation congruent_right := muls_extr.
#[deprecated(since="2026-09-11", note="Use setoidMonoidType instead.")]
Notation monoid := setoidMonoidType.
#[deprecated(since="2026-09-11", note="Use SetoidMonoid instead.")]
Notation Monoid M := (SetoidMonoid M).


#[deprecated(since="2026-09-11", note="Use * instead.")]
Infix "@" := mul (at level 50).

Section ProperMonoid.
  HB.declare Context G of hasEquiv G & isSetoidMonoid G.

  Global Instance : Proper (equiv ==> equiv ==> equiv) (mul: G -> G -> G).
  Proof.
  move=> a b eq_ab u v eq_uv.
  transitivity (a * v).
  - by exact: muls_extl.
  - by exact: muls_extr.
  Qed.
End ProperMonoid.

(* If `l = [a; b; c; ...; z]`, `prod l = a @ b @ ... @ z` *)
Definition prod {M: setoidMonoidType} (l: seq M) : M :=
  foldr (fun y acc => y * acc) 1 l.
Arguments prod {_} / !_.

Lemma prod0 {M: setoidMonoidType} : @prod M [::] = 1.
Proof. done. Qed.

Lemma prod1s {M: setoidMonoidType} (a: M) (l: seq M):
  prod (a :: l) = a * prod l.
Proof. done. Qed.

Lemma prod_cat {M: setoidMonoidType} (l1 l2: seq M):
  prod (l1 ++ l2) \approx (prod l1) * (prod l2).
Proof.
elim: l1 => [|a l1 /= ->];
  first by rewrite /= mul1s.
by rewrite mulsA.
Qed.

(** Some theory about morphisms *)

HB.mixin Record isMonoidMorphism (G H: setoidMonoidType) (f: G -> H) := {
  onefM: f 1 \approx 1;
  mulfM: forall x y,
    f (x * y) \approx (f x) * (f y);
}.

#[short(type="morphism")]
HB.structure Definition Morphism (G H: setoidMonoidType) :=
  { f of isSetoidMorphism G H f 
       & isMonoidMorphism G H f}.

#[deprecated(since="2026-09-11", note="Use onefM instead.")]
Notation morphism_preserve_e := onefM.
#[deprecated(since="2026-09-11", note="Use mulfM instead.")]
Notation morphism_preserve_law := mulfM.

#[short(type="injectiveMorphism")]
HB.structure Definition InjectiveMorphism (G H: setoidMonoidType) :=
  { f of isInjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

#[short(type="surjectiveMorphism")]
HB.structure Definition SurjectiveMorphism (G H: setoidMonoidType) :=
  { f of isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

#[short(type="isomorphism")]
HB.structure Definition Isomorphism (G H: setoidMonoidType) :=
  { f of isInjective G H f
       & isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.factory Record isIsomorphismInverse (S T: setoidMonoidType)
  (f: isomorphism S T) (g: T -> S) := {
    equivfM:
      forall x y, x \approx y -> g x \approx g y;
    isominvKl: forall x, g (f x) \approx x;
    isominvKr: forall x, f (g x) \approx x;
}.

#[deprecated(since="2026-09-11", note="Use equivfM instead.")]
Notation morphism_preserve_equiv' := isIsomorphismInverse.equivfM.
#[deprecated(since="2026-09-11", note="Use isominvKl instead.")]
Notation morphism_inverse_left := isIsomorphismInverse.isominvKl.
#[deprecated(since="2026-09-11", note="Use isominvKr instead.")]
Notation morphism_inverse_right := isIsomorphismInverse.isominvKr.

HB.builders Context 
  (S T: setoidMonoidType) (f: isomorphism S T) g of 
    isIsomorphismInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build T S g equivfM.

  Fact surjgM: forall y, exists x, g x \approx y.
  Proof.
    move => y; exists (f y); by apply isominvKl.
  Qed.

  HB.instance Definition _ :=
    isSurjective.Build T S g surjgM.
  
  Fact injgM: forall x y, g x \approx g y -> x \approx y.
  Proof.
    move => x y Hg; have: f (g x) \approx f (g y);
      first by rewrite Hg.
    by rewrite !isominvKr.
  Qed.

  HB.instance Definition _ :=
    isInjective.Build T S g injgM.

  Fact onegM: g 1 \approx 1.
  Proof.
    by rewrite -(isominvKl 1) onefM.
  Qed.

  Fact mulgM: forall x y, g (x * y) \approx g x * g y.
  Proof.
    move => x y.
    (* TODO(reiniscirpons): make this nicer? *)
    move: (@surjfM _ _ f x) => [x'] <-.
    move: (@surjfM _ _ f y) => [y'] <-.
    by rewrite -mulfM !isominvKl.
  Qed.

  HB.instance Definition _ :=
    isMonoidMorphism.Build T S g onegM mulgM.
HB.end.

HB.factory Record isIsomorphismLeftInverse (S T: setoidMonoidType)
  (f: isomorphism S T) (g: T -> S) := {
    equivfM': forall x y,
      x \approx y -> g x \approx g y;
    isominvKl': forall x,
      g (f x) \approx x;
}.

HB.builders Context 
  (S T: setoidMonoidType) (f: isomorphism S T) g of 
    isIsomorphismLeftInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g equivfM'.

  Fact isominvKr': forall y, f (g y) \approx y.
  Proof.
    move => y.
    move: (@surjfM _ _ f y) => [x] <-;
    by apply /equivfM /isominvKl'.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      equivfM
      isominvKl'
      isominvKr'.
HB.end.

HB.factory Record isIsomorphismRightInverse (S T: setoidMonoidType)
  (f: isomorphism S T) (g: T -> S) := {
    equivfM': forall x y,
      x \approx y -> g x \approx g y;
    isominvKr': forall x,
      f (g x) \approx x;
}.

HB.builders Context 
  (S T: setoidMonoidType) (f: isomorphism S T) g of 
    isIsomorphismRightInverse S T f g.

  Fact isominvKl': forall x, g (f x) \approx x.
  Proof.
    (* TODO(reiniscirpons): make this nicer *)
    move => x; apply (@injfM _ _ f).
    by apply isominvKr'.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      equivfM'
      isominvKl'
      isominvKr'.
HB.end.

(** Composition of morphisms *)

(* TODO(reiniscirpons): This feels like something that 
   has already been done. *)
Section MorphismComposition.

Context {S T U: setoidMonoidType}.
Variable f: morphism S T.
Variable g: morphism T U.

Lemma comp_onefM: (g \o f) 1 \approx 1.
Proof. by rewrite /comp !onefM. Qed.

Lemma comp_mulfM: forall x y,
  (g \o f) (x * y) \approx ((g \o f) x) * ((g \o f) y).
Proof. move => x y; by rewrite /comp !mulfM. Qed.

#[deprecated(since="2026-10-23", note="Use comp_onefM instead.")]
Notation comp_preserve_e := comp_onefM.
#[deprecated(since="2026-10-23", note="Use comp_mulfM instead.")]
Notation comp_preserve_law := comp_mulfM.

HB.instance Definition _ :=
  isMonoidMorphism.Build S U (g \o f) comp_onefM comp_mulfM.
End MorphismComposition.

Section InjectionComposition.
Context {A B C: setoidType}.
Variable f: injectiveFunType A B.
Variable g: injectiveFunType B C.

Lemma comp_injfM: forall x y,
  (g \o f) x \approx (g \o f) y -> x \approx y.
Proof.
  move => x y; rewrite /comp;
  by move /injfM /injfM.
Qed.

#[deprecated(since="2026-10-23", note="Use comp_injfM instead.")]
Notation comp_preserve_injectivity_property := comp_injfM.

HB.instance Definition _ :=
  isInjective.Build A C (g \o f) comp_injfM.
End InjectionComposition.

Section SurjectionComposition.
Context {A B C: setoidType}.
Variable f: surjectiveFunType A B.
Variable g: surjectiveFunType B C.


Lemma comp_surjfM: forall y, exists x,
  (g \o f) x \approx y.
Proof.
  move => y.
  move: (@surjfM _ _ g y) => [z] Hz.
  move: (@surjfM _ _ f z) => [x] Hx.
  by exists x; rewrite /= Hx Hz.
Qed.

#[deprecated(since="2026-10-23", note="Use comp_surjfM instead.")]
Notation comp_preserve_surjectivity_property := comp_surjfM.

HB.instance Definition _ :=
  isSurjective.Build A C (g \o f) comp_surjfM.
End SurjectionComposition.

Section IsomorphismComposition.
Context {S T U: setoidMonoidType}.
Variable f: isomorphism S T.
Variable g: isomorphism T U.

(* TODO(reiniscirpons): Without this line isomorphism composition
  is not an isomorphism. Why? *)
HB.instance Definition _ :=
  isSetoidMorphism.Build S U (g \o f) equivfM.

End IsomorphismComposition.


(** Theory of groups *)

HB.mixin Record isSetoidGroup G of
  hasEquiv G & isSetoidMonoid G := {
  inv : G -> G;
  invsM : forall x y,
    inv (x * y) \approx (inv y) * (inv x);
  mulsV : forall x,
    x * (inv x) \approx 1;
  mulVs : forall x,
    (inv x) * x \approx 1;
}.
#[short(type="setoidGroupType")]
HB.structure Definition SetoidGroup :=
  { G of isSetoidGroup G & hasEquiv G & isSetoidMonoid G }.

Bind Scope setoid_group_scope with SetoidGroup.sort.

Local Notation "x ^-1" := (inv x) : setoid_group_scope.

#[deprecated(since="2026-10-23", note="Use invsM instead.")]
Notation inverse_law := invsM.

#[deprecated(since="2026-10-23", note="Use mulsV instead.")]
Notation inverse_left := mulsV.

#[deprecated(since="2026-10-23", note="Use mulVs instead.")]
Notation inverse_right := mulVs.


#[deprecated(since="2026-10-23", note="Use isSetoidGroup instead.")]
Notation isGroup M := (isSetoidGroup M).
#[deprecated(since="2026-10-23", note="Use setoidGroupType instead.")]
Notation group := setoidGroupType.
#[deprecated(since="2026-10-23", note="Use SetoidGroup instead.")]
Notation Group M := (SetoidGroup M).


Lemma muls1_eq {G: setoidGroupType}: forall (x y: G),
  x * y \approx 1 -> x^-1 \approx y.
Proof.
  move => x y.
  rewrite -[x^-1]muls1 => <-.
  by rewrite mulsA mulVs mul1s.
Qed.

Lemma invsK {G: setoidGroupType}: forall (g: G),
  (g^-1)^-1 \approx g.
Proof.
  move=> g.
  apply muls1_eq.
  by rewrite mulVs.
Qed.

#[deprecated(since="2026-10-23", note="Use invsK instead.")]
Notation inv_involutive := invsK.

Lemma invs1 {G: setoidGroupType}:
  1^-1 \approx 1 :> G.
Proof.
  apply muls1_eq.
  by rewrite muls1.
Qed.

#[deprecated(since="2026-10-23", note="Use invs1 instead.")]
Notation inverse_e := invs1.

Section ProperGroup.

HB.declare Context G of
  hasEquiv G & isSetoidMonoid G & isSetoidGroup G.

Global Instance : Proper (equiv ==> equiv) (inv : G -> G).
Proof.
  move => /= a b Hab.
  have H: (a^-1) * b \approx 1;
    first by rewrite -Hab mulVs.
  have: a^-1 * b * b^-1 \approx b^-1;
    first by rewrite H mul1s.
  by rewrite -mulsA mulsV muls1.
Qed.

End ProperGroup.

#[deprecated(since="2026-10-23", note="Use invs1 instead.")]
Notation inv_e := invs1.

Lemma prod_inv {G: setoidGroupType} (l: seq G):
  (prod l)^-1 \approx (prod [seq g^-1 | g <- (rev l)]).
Proof.
elim: l => [/=|c l].
  by rewrite invs1.
rewrite -cat1s rev_cat map_cat !prod_cat invsM => ->.
by rewrite /= !muls1.
Qed.

Lemma prod_rcons {G: setoidGroupType} (l: seq G) (c: G):
  prod (rcons l c) \approx (prod l) * c.
Proof.
elim: l => /= [|a l ->].
  by rewrite mul1s muls1.
by rewrite mulsA.
Qed.

Lemma invfM:
  forall (G H: setoidGroupType) (f: morphism G H) x,
    (f x)^-1 \approx f (x^-1).
Proof.
  move => G H f x.
  apply muls1_eq.
  by rewrite -mulfM mulsV onefM.
Qed.

#[deprecated(since="2026-10-23", note="Use invfM instead.")]
Notation morphism_preserve_inv := invfM.

(* TODO (reiniscirpons):
  do some stuff to split into positive and negative powers*)
Definition exp {G: setoidGroupType} (w: G) (k: int) : G :=
  match k with
  | Posz k =>
    iter k (fun acc => w * acc) 1
  | Negz k =>
    iter k.+1 (fun acc => (w^-1) * acc) 1 (* Negx 0 is -1 *)
  end.

#[deprecated(since="2026-10-23", note="Use exp instead.")]
Notation power := exp.

Local Notation "w ^ k" := (@exp _ w k): setoid_group_scope.

Lemma exps0 {G: setoidGroupType} (w: G): w ^ 0 = 1.
Proof. done. Qed.

Lemma exps1 {G: setoidGroupType} (w: G): w ^ 1 = w * 1.
Proof. done. Qed.

Lemma exps1N {G: setoidGroupType} (w: G): w ^ (-1) = w^-1 * 1.
Proof. done. Qed.

Lemma expsS {G: setoidGroupType} (w: G) (x: nat):
  w ^ x.+1 = w * (w ^ x).
Proof. done. Qed.

Lemma expsP {G: setoidGroupType} (w: G) (x: nat):
  w ^ (- (x.+1: int)) = (w^-1) * (w ^ (- (x:int))).
Proof. by case: x. Qed.

#[deprecated(since="2026-10-23", note="Use exps0 instead.")]
Notation power0 := exps0.

#[deprecated(since="2026-10-23", note="Use exps1 instead.")]
Notation power1 := exps1.

#[deprecated(since="2026-10-23", note="Use expsS instead.")]
Notation powerS := expsS.

#[deprecated(since="2026-10-23", note="Use expsP instead.")]
Notation powerP := expsP.

(* TODO(reiniscirpons): I locked power here to avoid it being simplified
   in contexts where we dont want it to be later on.
   But now, it won't evaluate powers with a concrete, e.g.
   power w (-1) is left unexpanded. Is there some intermediate that would
   work? *)
Arguments exp {_} _ _: simpl never.

Lemma exp1n {G: setoidGroupType} (k: int):
  1^k \approx 1 :> G.
Proof.
  elim: k => [//||] k.
  - by rewrite expsS => ->; rewrite mul1s.
  - by rewrite expsP => ->; rewrite muls1 invs1.
Qed.

#[deprecated(since="2026-10-23", note="Use exp1n instead.")]
Notation power_e := exp1n.

(* TODO(reiniscirpons): Should I be defining my own induction principles?*)
Definition nat_pairs_ind: forall (P: nat -> Prop),
  P 0 -> P 1%N -> (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move => P H0 H1 HnSn n; enough (H: P n /\ P n.+1).
  - by case: H.
  elim: n => [//|n [Hn HSn]]; split => [//|].
  by apply HnSn.
Qed.

Lemma expsN {G: setoidGroupType} (w: G) (x:int):
  w ^ (- x) \approx (w ^ x)^-1.
Proof.
case: x; elim/nat_pairs_ind => [||k].
  - by rewrite /exp /= invs1.
  - by rewrite /exp /=
      invsM muls1 invs1 mul1s.
- rewrite !expsS !expsP !invsM => <- H.
  by rewrite H -{2}H mulsA.
- by rewrite /exp /= !muls1 invsK.
- by rewrite /exp /= !muls1 invsM invsK.
(* TODO(reiniscirpons): Fix this up. *)
(*- rewrite !powerS !powerP !inverse_law !inv_involutive => <- H.*)
(*  by rewrite H -{2}H !associativity.*)
Admitted.

#[deprecated(since="2026-10-23", note="Use expsN instead.")]
Notation power_inv := expsN.

Lemma expsC' {G: setoidGroupType} (w: G) (x: int):
  (w ^ x) * w \approx w * (w ^ x).
Proof.
elim: x => [|x H|x].
- by rewrite exps0 mul1s muls1.
- by rewrite expsS -{2}H mulsA.
- rewrite !expsN expsS /= invsM => eq.
  rewrite mulsA -eq.
  by rewrite -!mulsA mulsV mulVs muls1.
Qed.

#[deprecated(since="2026-10-23", note="Use expC' instead.")]
Notation powerC' := expsC'.

Lemma expsC'' {G: setoidGroupType} (w: G) (x: int):
  (w ^ x) * (w^-1) \approx (w^-1) * (w ^ x).
Proof.
  case: x.
  - case => [|k].
  -- by rewrite /exp /= muls1 mul1s.
  -- rewrite expsS -{1}expsC'.
    by rewrite -mulsA mulsV mulsA
               mulVs mul1s muls1.
  - elim => [|n H].
  -- by rewrite /exp /= muls1.
  -- by rewrite expsP -{2}H mulsA.
Qed.

#[deprecated(since="2026-10-23", note="Use expC'' instead.")]
Notation powerC'' := expsC''.

Lemma expsC {G: setoidGroupType} (w: G) (x y: int):
  (w ^ x) * (w ^ y) \approx (w ^ y) * (w ^ x).
Proof.
  elim: x => [|n IH|n IH].
  - by rewrite exps0 mul1s muls1.
  - by rewrite expsS -mulsA IH mulsA -expsC' mulsA.
  - by rewrite expsP -mulsA IH mulsA -expsC'' mulsA.
Qed.

#[deprecated(since="2026-10-23", note="Use expC instead.")]
Notation powerC := expsC.

Lemma expsS' {G: setoidGroupType} (w: G) (x: int):
  w ^ (1 + x) \approx w * (w ^ x).
Proof.
  case: x => n /=.
  - by rewrite /exp /=.
  - case: n => [|n].
  -- by rewrite /exp /= muls1 mulsV.
  -- rewrite /exp /= !mulsA mulsV mul1s.
     by have ->: (n.+1 - 1 = n)%N by case: n.
Qed.

#[deprecated(since="2026-10-23", note="Use expS' instead.")]
Notation powerS' := expsS'.

Lemma expsP' {G: setoidGroupType} (w: G) (x: int):
  w ^ (-1 + x) \approx (w^-1) * (w ^ x).
Proof.
  case: x => n /=.
  - case: n => [|n].
  -- by rewrite /exp /= muls1.
  -- rewrite /exp /= mulsA mulVs mul1s.
     by have ->: (n.+1 - 1 = n)%N by case: n.
  - by rewrite /exp /=.
Qed.

#[deprecated(since="2026-10-23", note="Use expP' instead.")]
Notation powerP' := expsP'.

Lemma expsnDr {G: setoidGroupType} (w: G) (x y: int):
  w ^ (x + y) \approx (w ^ x) * (w ^ y).
Proof.
elim: x => [|x H|x H].
- by rewrite add0r exps0 mul1s.
- have ->: (x.+1%:Z + y)%R = (1 + (x%:Z + y))%R by lia.
  by rewrite expsS expsS' -mulsA H.
- have ->: (- x.+1%:Z + y)%R = (-1 + (- x%:Z + y))%R by lia.
  by rewrite expsP expsP' H mulsA.
Qed.

#[deprecated(since="2026-10-23", note="Use expsnA instead.")]
Notation power_add := expsnDr.

Lemma power_switch_sign {G: setoidGroupType} (w: G) (x y: int):
  power (power w x) (- y) == power (power w (-x)) y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !exps0.
- rewrite powerP expsS => ->.
  by rewrite -power_inv.
- rewrite !opprK expsS powerP => ->.
  by rewrite -power_inv opprK.
Qed.

Lemma powerC'_tower {G: setoidGroupType} (w: G) (x y: int):
  power (power w x) y @ w == w @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite exps0 mul1s muls1.
- rewrite expsS -mulsA => ->.
  by rewrite mulsA powerC' mulsA.
- rewrite powerP -mulsA => ->.
  by rewrite mulsA -power_inv powerC' mulsA.
Qed.

Lemma powerC''_tower {G: setoidGroupType} (w: G) (x y: int):
  power (power w x) y @ (inv w) == (inv w) @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite exps0 mul1s muls1.
- rewrite expsS -mulsA => ->.
  by rewrite mulsA powerC'' mulsA.
- rewrite powerP -mulsA => ->.
  by rewrite mulsA -power_inv powerC'' mulsA.
Qed.

Lemma power_mul {G: setoidGroupType} (w: G) (x y: int):
  power w (x * y) == power (power w x) y.
Proof.
elim: x => [|x|x].
- by rewrite mul0r !exps0 power_e.
- rewrite expsS.
  have ->: (x.+1%:Z * y)%R = (x%:Z * y + y)%R by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !exps0 mul1s.
  - rewrite !expsS => <-.
    by rewrite !mulsA -[w @ _]powerC' -![((_ @ w) @ _)]mulsA
            -powerC'_tower !mulsA.
  - rewrite !power_switch_sign !powerP => <-.
    rewrite expsS inverse_law -power_inv.
    by rewrite mulsA -[(_ @ _) @ inv w]mulsA
            -mulsA powerC''_tower !mulsA.
- have ->: (- x.+1%:Z * y)%R = (- x%:Z*y + (-y))%R by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !exps0 mul1s.
  - rewrite !expsS !powerP => <-.
    by rewrite !mulsA -[inv w @ _]powerC'' -![((_ @ inv w) @ _)]mulsA
            -powerC''_tower !mulsA.
  - have ->: ((- - y%:Z) = y%:Z)%R by lia.
    have ->: ((- - y.+1%:Z) = y.+1%:Z)%R by lia.
    rewrite expsS ![power _ (- y.+1%:Z)]powerP => <-.
    rewrite powerP inverse_law inv_involutive.
    by rewrite !mulsA -[(_ @ _) @ w]mulsA
            -mulsA  powerC'_tower  !mulsA.
Qed.

Lemma power_proper_pos {G: setoidGroupType} (x y: G) (k: nat):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
elim: k => [//|k IH].
by rewrite !expsS IH Heq.
Qed.
Lemma power_proper {G: setoidGroupType} (x y: G) (k: int):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
case: k => k.
  exact: power_proper_pos.
have ->: Negz k = (- (k.+1)%:Z)%R by done.
by rewrite !power_inv power_proper_pos.
Qed.
Arguments power_proper {_ _ _}.

Global Instance: forall G, Proper (eq ==> Logic.eq ==> eq) (@power G).
Proof.
  by move => G x y Hxy h k ->; apply power_proper.
Qed.

Lemma morphism_preserve_power_pos {G G': group} (f: morphism G G') (x: G) (k: nat):
  f (power x k) == power (f x) k.
Proof.
elim: k => [/=|k].
  by rewrite morphism_preserve_e.
by rewrite !expsS morphism_preserve_law => <-.
Qed.
Lemma morphism_preserve_power {G G': group} (f: morphism G G') (x: G) (k: int):
  f (power x k) == power (f x) k.
Proof.
case: k => k.
  exact: morphism_preserve_power_pos.
have ->: Negz k = (- (k.+1)%:Z)%R by done.
rewrite !power_inv -morphism_preserve_inv.
by rewrite morphism_preserve_power_pos.
Qed.


(*#[short(type="deceqGroupType")]*)
(*HB.structure Definition DecEqGroup := { G of isGroup G & hasEq G & isMonoid G & hasDecEq G }.*)

HB.mixin Record isSubgroup (G: group) (H: group) := {
  subgroup_inj: injectiveMorphism H G;
}.

#[short(type="subgroup")]
HB.structure Definition Subgroup (G: group) := { H of isSubgroup G (* super group *) H (* sub group *)}.

(* NOTE(reiniscirpons): I don't understand this well enough to change. Assume ok for now. *)

Elpi Accumulate coercion.db lp:{{

% See https://rocq-prover.zulipchat.com/#narrow/channel/237868-Hierarchy-Builder-devs-.26-users/topic/Missing.20instance.20in.20a.20hierarchy.20for.20subtypes/with/561428680
coercion _ T {{ Type }} ExpectedType Solution :-
  ExpectedType = {{ subgroup _ }},
  coq.elaborate-skeleton {{ ( lp:T : group) }} ExpectedType Solution Diagnostics,
  ok = Diagnostics.

}}.

(* TODO: it would be cool to "register" subgroup_inj as a coercion.
   I don't think it can be done via the vanilla Rocq coercions, and doing so via a coercion hook
   seems difficult without triggering an infinite coercion chain. *)

(* TODO(reiniscirpons): Dont do this, the issue is the parametricity,
  if we have G as a parameter for the coercion this will cause bad bad things
  to happen.
  Coercion subgroup_to_group {G} {H: subgroup G}:
    H -> G := @subgroup_inj G H.
*)

Definition in_subgroup {G: setoidGroupType} (K: subgroup G) (x: G) :=
  exists x': K, subgroup_inj x' == x.
Notation "x '\insubgroup' K" := (in_subgroup K x) (at level 10).

(* this definition is useful as due to non-forgetful inheritance, seeing a subgroup of a subgroup of a group as a subgroup of the group is not easy *)
Definition in_subsubgroup (G: group) (H: subgroup G) (I: subgroup H) (x: G) :=
  exists x': I, subgroup_inj (subgroup_inj x') == x.
Notation "x '\insubsubgroup[' Subgroup ']' Subsubgroup" := (@in_subsubgroup _ Subgroup Subsubgroup x) (at level 10).

Lemma in_subgroup_proper {Group: group} (Subgroup: subgroup Group) (x x': Group):
  (x == x') ->
  (x \insubgroup Subgroup) ->
  (x' \insubgroup Subgroup).
Proof.
move=> Heq [xS ?].
exists xS.
by rewrite -Heq.
Qed.

Lemma in_subgroup_e {Group: group} {Subgroup: subgroup Group}:
  e \insubgroup Subgroup.
Proof. exists e; by rewrite morphism_preserve_e. Qed.

Lemma in_subgroup_law {Group: group} {Subgroup: subgroup Group} (x y: Group):
  (x \insubgroup Subgroup) -> (y \insubgroup Subgroup) -> ((x @ y) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
case=> [y' Hy'].
exists (x' @ y').
by rewrite morphism_preserve_law -Hx' -Hy'.
Qed.

Lemma in_subgroup_inv {Group: group} {Subgroup: subgroup Group} (x: Group):
  (x \insubgroup Subgroup) -> ((inv x) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
exists (inv x').
by rewrite -Hx' morphism_preserve_inv.
Qed.

Lemma in_subsubgroup_proper {G: setoidGroupType} (H: subgroup G) (I: subgroup H) (x x': G) :
  x == x' ->
  (x \insubsubgroup[H] I) ->
  (x' \insubsubgroup[H] I).
Proof.
move=> Heq [xK eq].
exists xK.
by rewrite eq.
Qed.


Definition is_subgroup_stable {G: setoidGroupType} {H1 H2: subgroup G} (f: morphism H1 H2) (K: subgroup G) :=
  forall (x: H1), ((subgroup_inj x) \insubgroup K) -> subgroup_inj (f x) \insubgroup K.

Record local_morphism (G: group) := {
  lm_source_subgroup : subgroup G;
  lm_target_subgroup : subgroup G;
  lm_morphism :> morphism lm_source_subgroup lm_target_subgroup;
}.
Arguments lm_source_subgroup {_}.
Arguments lm_target_subgroup {_}.
Coercion morphism_to_local_morphism {G} {H1 H2: subgroup G}: morphism H1 H2 -> local_morphism G :=
  fun f => {| lm_morphism := f |}.


Section RightCoset.

Context {G: setoidGroupType}.
Variable H: subgroup G.

Definition right_coset_eq (x y: G): Prop := in_subgroup H (x @ inv y).

Lemma right_coset_eq': forall x y,
  right_coset_eq x y <-> (exists w: H, (subgroup_inj w) @ y == x).
Proof.
  move => x y; split.
  - rewrite /right_coset_eq /in_subgroup.
    case => w Hw; exists w;
    by rewrite Hw -mulsA mulVs muls1.
  - case => w Hw; exists w;
    by rewrite -Hw -mulsA mulsV muls1.
Qed.

Instance RightCosetEqReflexivity : Reflexive right_coset_eq.
Proof.
  move => x; rewrite right_coset_eq'; exists e;
  by rewrite morphism_preserve_e mul1s.
Qed.
Instance RightCosetEqSymmetry : Symmetric right_coset_eq.
Proof.
  move => x y; rewrite !right_coset_eq'.
  case => w Hw; exists (inv w).
  by rewrite -morphism_preserve_inv -Hw mulsA mulVs mul1s.
Qed.
Instance RightCosetEqTransitivity : Transitive right_coset_eq.
Proof.
  move => x y z; rewrite !right_coset_eq'.
  move => [w1 H1] [w2 H2]; exists (w1 @ w2).
  by rewrite morphism_preserve_law -mulsA H2 H1.
Qed.
Instance RightCosetEqEquivalence : Equivalence right_coset_eq := {}.
End RightCoset.
Existing Instance RightCosetEqReflexivity.
Existing Instance RightCosetEqSymmetry.
Existing Instance RightCosetEqTransitivity.
Existing Instance RightCosetEqEquivalence.
Check right_coset_eq.

HB.mixin Record isRightCosetRep
  (G: group) (H: subgroup G) (f: G -> G) := {
  right_coset_rep_correct: forall (x: G),
    right_coset_eq H x (f x);
  right_coset_rep_unique: forall (x y: G),
    right_coset_eq H x y -> f x = f y;
}.

#[short(type="rightCosetRep")]
HB.structure Definition RightCosetRep (G: group) (H: subgroup G) :=
  { f of isRightCosetRep G H f }.

Lemma right_coset_eq_spec: forall (G: group) H (f: rightCosetRep H) (x y: G),
  (right_coset_eq H x y) <-> (f x = f y).
Proof.
  move => G H f x y; split.
  - by apply right_coset_rep_unique.
  move => Hf; transitivity (f x).
  - by apply right_coset_rep_correct.
  rewrite Hf; symmetry; by apply right_coset_rep_correct.
Qed.

HB.mixin Record isSubgroupCharacterizer (G: group) (P: G -> Type) := {
  P_law: forall x y, P x -> P y -> P (x @ y);
  P_neutral: P e;
  P_inv: forall x, P x -> P (inv x);
}.
#[short(type = "subgroup_characterizer")]
HB.structure Definition SubgroupCharacterizer (G: group) := { P of isSubgroupCharacterizer G P }.

Section SubgroupByCharacterization.
Context {G: setoidGroupType}.
Variable P: subgroup_characterizer G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point :> G;
  sb_point_characterization: P sb_point;
}.

Definition subgroupby_inj (x: subgroup_by): G := x.

Definition subgroupby_eq (x y: subgroup_by) := (subgroupby_inj x) == (subgroupby_inj y).
Lemma subgroupby_eq_refl: forall x, subgroupby_eq x x.
Proof. by move=> x; rewrite /subgroupby_eq. Qed.
Lemma subgroupby_eq_sym: forall x y, subgroupby_eq x y -> subgroupby_eq y x.
Proof. move=> x y; rewrite /subgroupby_eq; by symmetry. Qed.
Lemma subgroupby_eq_trans: forall x y z, subgroupby_eq x y -> subgroupby_eq y z -> subgroupby_eq x z.
Proof. move=> x y z; rewrite /subgroupby_eq => ? ?; by transitivity (subgroupby_inj y). Qed.

HB.instance Definition _ :=
  hasEquiv.Build subgroup_by subgroupby_eq_refl subgroupby_eq_sym subgroupby_eq_trans.

Definition subgroupby_law (x y : subgroup_by): subgroup_by.
Proof.
exists (x.(sb_point) @ y.(sb_point)).
apply /P_law; exact /sb_point_characterization.
Defined.

Definition subgroupby_neutral: subgroup_by.
Proof. exists e; exact: P_neutral. Defined.

Lemma subgroupby_mulsA: forall (x y z: subgroup_by), subgroupby_law x (subgroupby_law y z) == subgroupby_law (subgroupby_law x y) z.
Proof. by move=> x y z; rewrite /subgroupby_law/= /equiv/= /subgroupby_eq/= /subgroupby_inj/= mulsA. Qed.

Lemma subgroupby_mul1s: forall (x: subgroup_by), subgroupby_law subgroupby_neutral x == x.
Proof. move=> x; by rewrite /subgroupby_law/= /equiv/= /subgroupby_eq/= /subgroupby_inj/= mul1s. Qed.

Lemma subgroupby_muls1: forall (x: subgroup_by), subgroupby_law x subgroupby_neutral == x.
Proof. move=> x; by rewrite /subgroupby_law/= /equiv/= /subgroupby_eq/= /subgroupby_inj/= muls1. Qed.

Lemma subgroupby_congruent_left: forall (x y z: subgroup_by), y == z -> subgroupby_law x y == subgroupby_law x z.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_left.
Qed.

Lemma subgroupby_congruent_right: forall (x y z: subgroup_by), y == z -> subgroupby_law y x == subgroupby_law z x.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_right.
Qed.

HB.instance Definition _ := isSetoidMonoid.Build subgroup_by subgroupby_mulsA subgroupby_mul1s subgroupby_muls1 subgroupby_congruent_left subgroupby_congruent_right.

Definition subgroupby_inv: subgroup_by -> subgroup_by.
Proof. move=> x; exists (inv x.(sb_point)); exact /P_inv /sb_point_characterization. Defined.

Lemma subgroupby_inverse_law: forall x y, subgroupby_inv (x @ y) == (subgroupby_inv y) @ (subgroupby_inv x).
Proof. move=> x y; by rewrite /subgroupby_inv/=/equiv/=/subgroupby_eq/subgroupby_inj/= inverse_law. Qed.

Lemma subgroupby_mulsV : forall x, x @ (subgroupby_inv x) == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/mul/=/subgroupby_law/=/equiv/=/subgroupby_eq/=/subgroupby_inj/= mulsV. Qed.

Lemma subgroupby_mulVs : forall x, (subgroupby_inv x) @ x == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/mul/=/subgroupby_law/=/equiv/=/subgroupby_eq/=/subgroupby_inj/= mulVs. Qed.

HB.instance Definition _ := isSetoidGroup.Build subgroup_by subgroupby_inverse_law subgroupby_mulsV subgroupby_mulVs.

Lemma subgroupby_inj_preserve_equiv: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isSetoidMorphism.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_preserve_equiv.

Lemma subgroupby_inj_injectivity: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isInjective.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_injectivity.

Lemma subgroupby_inj_preserve_e: subgroupby_inj one == one.
Proof. done. Qed.
Lemma subgroupby_inj_preserve_law: forall x y, subgroupby_inj (law x y) == law (subgroupby_inj x) (subgroupby_inj y).
Proof. done. Qed.

HB.instance Definition _ := 
  isMonoidMorphism.Build _ _
    subgroupby_inj 
    subgroupby_inj_preserve_e 
    subgroupby_inj_preserve_law.

HB.instance Definition _ :=
  isSubgroup.Build G subgroup_by subgroupby_inj.

End SubgroupByCharacterization.
Arguments subgroup_by {_}.
Arguments sb_point_characterization {_ _}.
Arguments sb_point {_ _}.

(* {e}, the subgroup! *)
Section SingletonSubgroup.
Variable K: group.

Definition singleton_subgroup_char (x: K): Type := (x == e).

Lemma ssc_neutral: singleton_subgroup_char e.
Proof. by rewrite /singleton_subgroup_char. Qed.

Lemma ssc_inv (x: K): singleton_subgroup_char x -> singleton_subgroup_char (inv x).
Proof. by rewrite /singleton_subgroup_char => ->; rewrite inv_e. Qed.

Lemma ssc_law (x y: K): singleton_subgroup_char x -> singleton_subgroup_char y -> singleton_subgroup_char (x @ y).
Proof. by rewrite /singleton_subgroup_char => -> ->; rewrite mul1s. Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build K singleton_subgroup_char ssc_law ssc_neutral ssc_inv.

Definition singleton_subgroup := subgroup_by singleton_subgroup_char.

Definition singleton_morphism: singleton_subgroup -> singleton_subgroup := id.

Lemma sm_preserve_equiv: forall x y, x == y -> singleton_morphism x == singleton_morphism y.
Proof. done. Qed.
Lemma sm_preserve_e: singleton_morphism e == e.
Proof. done. Qed.
Lemma sm_preserve_law: forall x y, singleton_morphism (x @ y) == (singleton_morphism x) @ (singleton_morphism y).
Proof. done. Qed.

HB.instance Definition _ :=
  isSetoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_preserve_equiv.
HB.instance Definition _ :=
  isMonoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_preserve_e
    sm_preserve_law.

End SingletonSubgroup.

(* TODO(reiniscirpons): Do we need this? *)
(* Intersection of subgroups *)
Section SubgroupIntersection.
Context {G: setoidGroupType}.
Variable (H1 H2: subgroup G).

Record is_in_intersection (x: G) : Prop := {
  intersection_in_left: x \insubgroup H1;
  intersection_in_right: x \insubgroup H2;
}.

Definition iii_P_law : forall (x y: G), is_in_intersection x -> is_in_intersection y -> is_in_intersection (x @ y).
Proof.
move=> x y [[x1 x1_eq] [x2 x2_eq]] [[y1 y1_eq] [y2 y2_eq]]; eexists.
- by exists (x1 @ y1); rewrite morphism_preserve_law -x1_eq -y1_eq.
- by exists (x2 @ y2); rewrite morphism_preserve_law -x2_eq -y2_eq.
Qed.

Definition iii_P_neutral : is_in_intersection e.
Proof. by eexists; exists e; rewrite morphism_preserve_e. Qed.

Definition iii_P_inv : forall (x: G), is_in_intersection x -> is_in_intersection (inv x).
Proof.
move=> x [[x1 x1_eq] [x2 x2_eq]]; eexists.
- by exists (inv x1); rewrite -morphism_preserve_inv -x1_eq.
- by exists (inv x2); rewrite -morphism_preserve_inv -x2_eq.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G is_in_intersection iii_P_law iii_P_neutral iii_P_inv.

(* we could also prove that H1 /\ H2 is a subgroup of H1 and H2 *)

Definition intersection := subgroup_by is_in_intersection.

End SubgroupIntersection.
