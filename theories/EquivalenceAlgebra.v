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

#[deprecated(since="2026-10-23", note="Use expsC' instead.")]
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

#[deprecated(since="2026-10-23", note="Use expsC'' instead.")]
Notation powerC'' := expsC''.

Lemma expsC {G: setoidGroupType} (w: G) (x y: int):
  (w ^ x) * (w ^ y) \approx (w ^ y) * (w ^ x).
Proof.
  elim: x => [|n IH|n IH].
  - by rewrite exps0 mul1s muls1.
  - by rewrite expsS -mulsA IH mulsA -expsC' mulsA.
  - by rewrite expsP -mulsA IH mulsA -expsC'' mulsA.
Qed.

#[deprecated(since="2026-10-23", note="Use expsC instead.")]
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

#[deprecated(since="2026-10-23", note="Use expsS' instead.")]
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

#[deprecated(since="2026-10-23", note="Use expsP' instead.")]
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

#[deprecated(since="2026-10-23", note="Use expsnDr instead.")]
Notation power_add := expsnDr.

Lemma expsnN {G: setoidGroupType} (w: G) (x y: int):
  (w ^ x) ^ (- y) \approx (w ^ (-x)) ^ y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !exps0.
- rewrite expsP expsS => ->.
  by rewrite -expsN.
- rewrite !opprK expsS expsP => ->.
  by rewrite -expsN opprK.
Qed.

#[deprecated(since="2026-10-28", note="Use expsnN instead.")]
Notation power_switch_sign := expsnN.

Lemma expsnns {G: setoidGroupType} (w: G) (x y: int):
  (w ^ x) ^ y * w \approx w * (w ^ x) ^ y.
Proof.
elim: y => [|y|y].
- by rewrite exps0 mul1s muls1.
- rewrite expsS -mulsA => ->.
  by rewrite mulsA expsC' mulsA.
- rewrite expsP -mulsA => ->.
  by rewrite mulsA -expsN expsC' mulsA.
Qed.

#[deprecated(since="2026-10-28", note="Use expsnns instead.")]
Notation powerC'_tower := expsnns.

Lemma expsnnV {G: setoidGroupType} (w: G) (x y: int):
  (w ^ x) ^ y * (w^-1) \approx (w^-1) * (w ^ x) ^ y.
Proof.
  elim: y => [|y|y].
  - by rewrite exps0 mul1s muls1.
  - rewrite expsS -mulsA => ->.
    by rewrite mulsA expsC'' mulsA.
  - rewrite expsP -mulsA => ->.
    by rewrite mulsA -expsN expsC'' mulsA.
Qed.

#[deprecated(since="2026-10-28", note="Use expsnnV instead.")]
Notation powerC''_tower := expsnnV.

Lemma expsnA {G: setoidGroupType} (w: G) (x y: int):
  w ^ (x * y) \approx (w ^ x) ^ y.
Proof.
  elim: x => [|x|x].
  - by rewrite mul0r !exps0 exp1n.
  - rewrite expsS.
    have ->: (x.+1%:Z * y)%R = (x%:Z * y + y)%R by lia.
    rewrite expsnDr => ->.
    elim: y => [|y|y].
    + by rewrite !exps0 mul1s.
    + rewrite !expsS => <-.
      by rewrite !mulsA -[w * _]expsC' -![((_ * w) * _)]mulsA
              -expsnns !mulsA.
    + rewrite !expsnN !expsP => <-.
      rewrite expsS invsM -expsN.
      by rewrite mulsA -[(_ * _) * w^-1]mulsA
              -mulsA expsnnV !mulsA.
  - have ->: (- x.+1%:Z * y)%R = (- x%:Z*y + (-y))%R by lia.
    rewrite expsnDr => ->.
    elim: y => [|y|y].
    + by rewrite !exps0 mul1s.
    + rewrite !expsS !expsP => <-.
      by rewrite !mulsA -[w^-1 * _]expsC''
                 -![((_ * w^-1) * _)]mulsA -expsnnV !mulsA.
    + have ->: ((- - y%:Z) = y%:Z)%R by lia.
      have ->: ((- - y.+1%:Z) = y.+1%:Z)%R by lia.
      rewrite expsS ![_ ^ (- y.+1%:Z)]expsP => <-.
      rewrite expsP invsM invsK.
      by rewrite !mulsA -[(_ * _) * w]mulsA
              -mulsA  expsnns  !mulsA.
Qed.

#[deprecated(since="2026-10-28", note="Use expsnA instead.")]
Notation power_mul := expsnA.

Lemma exps_extl' {G: setoidGroupType} (x y: G) (k: nat):
  x \approx y -> x ^ k \approx y ^ k.
Proof.
  move=> Heq.
  elim: k => [//|k IH].
  by rewrite !expsS IH Heq.
Qed.

#[deprecated(since="2026-10-28", note="Use exps_extl' instead.")]
Notation power_proper_pos := exps_extl'.

Lemma exps_extl {G: setoidGroupType} (x y: G) (k: int):
  x \approx y -> x ^ k \approx y ^ k.
Proof.
  move=> Heq.
  case: k => k;
    first by exact: exps_extl'.
  have ->: Negz k = (- (k.+1)%:Z)%R by done.
  by rewrite !expsN exps_extl'.
Qed.

#[deprecated(since="2026-10-28", note="Use exps_extl instead.")]
Notation power_proper := exps_extl.

Arguments exps_extl {_ _ _}.

Global Instance: forall G,
  Proper (equiv ==> Logic.eq ==> equiv) (@exp G).
Proof.
  by move => G x y Hxy h k ->; apply exps_extl.
Qed.

Lemma expfM' {G G': setoidGroupType}
  (f: morphism G G') (x: G) (k: nat):
  f (x ^ k) \approx (f x) ^ k.
Proof.
  elim: k => [/=|k];
    first by rewrite onefM.
  by rewrite !expsS mulfM => <-.
Qed.

#[deprecated(since="2026-10-28", note="Use expfM' instead.")]
Notation morphism_preserve_power_pos := expfM'.

Lemma expfM {G G': setoidGroupType}
  (f: morphism G G') (x: G) (k: int):
  f (x ^ k) \approx (f x) ^ k.
Proof.
  case: k => k;
    first by exact: expfM'.
  have ->: Negz k = (- (k.+1)%:Z)%R by done.
  rewrite !expsN -invfM.
  by rewrite expfM'.
Qed.

#[deprecated(since="2026-10-28", note="Use expfM instead.")]
Notation morphism_preserve_power := expfM.

(* TODO(reiniscirpons): move to generated subgroup *)
(* TODO(reiniscirpons): Should we not use this definition given
   what we spoke about with Assia, or is this ok because we
   do some magic later on? *)
HB.mixin Record isSubgroup (G H: setoidGroupType) := {
  subgroup_inj: injectiveMorphism H G;
}.

#[short(type="subgroup")]
HB.structure Definition Subgroup (G: setoidGroupType) :=
  { H of isSubgroup G (* super group *) H (* sub group *)}.

Notation "'[og' x ']'" := (@subgroup_inj _ _ x)
  (at level 10, format "[og  x ]").


(* NOTE(reiniscirpons): I don't understand this well enough to change. Assume ok for now. *)

Elpi Accumulate coercion.db lp:{{
% See https://rocq-prover.zulipchat.com/#narrow/channel/237868-Hierarchy-Builder-devs-.26-users/topic/Missing.20instance.20in.20a.20hierarchy.20for.20subtypes/with/561428680
coercion _ T {{ Type }} ExpectedType Solution :-
  ExpectedType = {{ subgroup _ }},
  coq.elaborate-skeleton {{ ( lp:T : setoidGroupType) }} ExpectedType Solution Diagnostics,
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

Definition insubg
  {G: setoidGroupType} (H: subgroup G) (x: G) :=
  exists x': H, [og x'] \approx x.

Notation "x '\insubgroup' H" := (@insubg _ H x) (at level 10).

#[deprecated(since="2026-10-28", note="Use insubg instead.")]
Notation in_subgroup := insubg.

(* this definition is useful as due to non-forgetful inheritance, seeing a subgroup of a subgroup of a group as a subgroup of the group is not easy *)
Definition insubsubg (G: setoidGroupType)
  (H: subgroup G) (I: subgroup H) (x: G) :=
  exists x': I, [og [og x']] \approx x.

Notation "x '\insubsubgroup' '[' H ']' I" :=
  (@insubsubg _ H I x)
  (at level 10,
    format "x  '\insubsubgroup' [ H ]  I").

#[deprecated(since="2026-10-28", note="Use insubsubg instead.")]
Notation in_subsubgroup := insubsubg.

Lemma insubg_extl {G: setoidGroupType} (H: subgroup G) (x x': G):
  (x \approx x') ->
  (x \insubgroup H) ->
  (x' \insubgroup H).
Proof.
  move=> Heq [xS ?].
  exists xS.
  by rewrite -Heq.
Qed.

#[deprecated(since="2026-10-28", note="Use insubg_extl instead.")]
Notation in_subgroup_proper := insubg_extl.

Lemma insubg1 {G: setoidGroupType} {H: subgroup G}:
  1 \insubgroup H.
Proof. exists 1; by rewrite onefM. Qed.

#[deprecated(since="2026-10-28", note="Use insubg1 instead.")]
Notation in_subgroup_e := insubg1.

Lemma insubgM {G: setoidGroupType} {H: subgroup G} (x y: G):
  x \insubgroup H ->
  y \insubgroup H ->
  (x * y) \insubgroup H.
Proof.
  case=> [x' Hx'].
  case=> [y' Hy'].
  exists (x' * y').
  by rewrite mulfM -Hx' -Hy'.
Qed.

#[deprecated(since="2026-10-28", note="Use insubgM instead.")]
Notation in_subgroup_law := insubgM.

Lemma insubgV {G: setoidGroupType} {H: subgroup G} (x: G):
  x \insubgroup H ->
  x^-1 \insubgroup H.
Proof.
  case=> [x' Hx'].
  exists (inv x').
  by rewrite -Hx' invfM.
Qed.

#[deprecated(since="2026-10-28", note="Use insubgV instead.")]
Notation in_subgroup_inv := insubgV.

Lemma insubsubg_extl {G: setoidGroupType} (H: subgroup G)
  (I: subgroup H) (x x': G):
  x \approx x' ->
  (x \insubsubgroup[H] I) ->
  (x' \insubsubgroup[H] I).
Proof.
  move=> Heq [xK eq].
  exists xK.
  by rewrite eq.
Qed.

#[deprecated(
  since="2026-10-28",
  note="Use insubsubg_extl instead.")]
Notation in_subsubgroup_proper := insubsubg_extl.


Definition is_insubgfM {G: setoidGroupType}
  {H1 H2: subgroup G} (f: morphism H1 H2) (K: subgroup G) :=
  forall (x: H1),
    [og x] \insubgroup K ->
    [og (f x)] \insubgroup K.

#[deprecated(
  since="2026-10-28",
  note="Use is_insubgfM instead.")]
Notation is_subgroup_stable := is_insubgfM.

Record local_morphism (G: setoidGroupType) := {
  lm_source_subgroup : subgroup G;
  lm_target_subgroup : subgroup G;
  lm_morphism :> morphism lm_source_subgroup lm_target_subgroup;
}.
Arguments lm_source_subgroup {_}.
Arguments lm_target_subgroup {_}.
Coercion morphism_to_local_morphism {G} {H1 H2: subgroup G}:    
  morphism H1 H2 -> local_morphism G :=
  fun f => {| lm_morphism := f |}.


Section RightCoset.

Context {G: setoidGroupType}.
Variable H: subgroup G.
Implicit Types (x y: G).

Definition rcequiv (K: subgroup G) x y: Prop :=
  (x * y^-1) \insubgroup K.

Notation "x '\inrcoset' '[' H ']' y" := (rcequiv H x y)
  (at level 60, no associativity, format "x  \inrcoset [ H ]  y").
 
Lemma right_coset_eq': forall x y,
  (x \inrcoset[H] y) <->
  (exists w: H, x \approx [og w] * y).
Proof.
  move => x y; split.
  - rewrite /rcequiv /insubg.
    case => w Hw; exists w;
    by rewrite Hw -mulsA mulVs muls1.
  - case => w Hw; exists w;
    by rewrite Hw -mulsA mulsV muls1.
Qed.

Instance RightCosetEqReflexivity: Reflexive (rcequiv H).
Proof.
  move => x; rewrite right_coset_eq'; exists 1;
  by rewrite onefM mul1s.
Qed.

Instance RightCosetEqSymmetry : Symmetric (rcequiv H).
Proof.
  move => x y; rewrite !right_coset_eq'.
  case => w Hw; exists (inv w).
  by rewrite -invfM Hw mulsA mulVs mul1s.
Qed.

Instance RightCosetEqTransitivity : Transitive (rcequiv H).
Proof.
  move => x y z; rewrite !right_coset_eq'.
  move => [w1 H1] [w2 H2]; exists (w1 * w2).
  by rewrite mulfM -mulsA -H2 -H1.
Qed.

Instance RightCosetEqEquivalence :
  Equivalence (rcequiv H) := {}.
End RightCoset.
Existing Instance RightCosetEqReflexivity.
Existing Instance RightCosetEqSymmetry.
Existing Instance RightCosetEqTransitivity.
Existing Instance RightCosetEqEquivalence.

#[deprecated(since="2026-10-28", note="Use rcequiv instead.")]
Notation right_coset_eq := rcequiv.

Notation "x '\inrcoset' '[' H ']' y" := (rcequiv H x y)
  (at level 60,
    no associativity,
    format "x  \inrcoset [ H ]  y"): setoid_group_scope.

HB.mixin Record isRightCosetRep
  (G: setoidGroupType) (H: subgroup G) (f: G -> G) := {
  rcrepE: forall (x: G),
    x \inrcoset[H] (f x);
  rcrep_extl: forall (x y: G),
    x \inrcoset[H] y -> f x = f y;
}.

#[short(type="rightCosetRep")]
HB.structure Definition RightCosetRep
  (G: setoidGroupType) (H: subgroup G) :=
  { f of isRightCosetRep G H f }.

#[deprecated(since="2026-10-28", note="Use rcrepE instead.")]
Notation right_coset_rep_correct := rcrepE.

#[deprecated(since="2026-10-28", note="Use rcrep_extl instead.")]
Notation right_coset_rep_unique := rcrep_extl.

Lemma rcequivP: forall (G: setoidGroupType) H
  (f: rightCosetRep H) (x y: G),
  (x \inrcoset[H] y) <-> (f x = f y).
Proof.
  move => G H f x y; split.
  - by apply rcrep_extl.
  move => Hf; transitivity (f x).
  - by apply rcrepE.
  (* TODO: How to make reflexivity of the new equivalence relation
  get tried automatically? *)
  by rewrite Hf -rcrepE; reflexivity.
Qed.

#[deprecated(since="2026-10-28", note="Use rcequivP instead.")]
Notation right_coset_eq_spec := rcequivP.

HB.mixin Record isSubgroupCharacterizer
  (G: setoidGroupType) (P: G -> Type) := {
  sgcharM: forall x y,
    P x -> P y -> P (x * y);
  sgchar1: P 1;
  sgcharV: forall x,
    P x -> P (x^-1);
}.
#[short(type = "subgroupChar")]
HB.structure Definition SubgroupCharacterizer
  (G: setoidGroupType) :=
  { P of isSubgroupCharacterizer G P }.

#[deprecated(since="2026-10-28", note="Use sgcharM instead.")]
Notation P_law := sgcharM.

#[deprecated(since="2026-10-28", note="Use sgchar1 instead.")]
Notation P_neutral := sgchar1.

#[deprecated(since="2026-10-28", note="Use sgcharV instead.")]
Notation P_inv := sgcharV.

#[deprecated(since="2026-10-28", note="Use subgroupChar instead.")]
Notation subgroup_characterizer := subgroupChar.

Section SubgroupByCharacterization.
Context {G: setoidGroupType}.
Variable P: subgroupChar G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point :> G;
  sb_char: P sb_point;
}.

#[deprecated(since="2026-10-28", note="Use sb_char instead.")]
Notation sb_point_characterization := sb_char.

Definition sb_inj (x: subgroup_by): G := x.

#[deprecated(since="2026-10-28", note="Use sb_inj instead.")]
Notation subgroupby_inj := sb_inj.

Definition sb_equiv (x y: subgroup_by) :=
  (sb_inj x) \approx (sb_inj y).

#[deprecated(since="2026-10-28", note="Use sb_equiv instead.")]
Notation subgroupby_eq := sb_equiv.

Lemma sb_equiv_refl: forall x, sb_equiv x x.
Proof. by move=> x; rewrite /sb_equiv. Qed.

Lemma sb_equiv_sym: forall x y,
  sb_equiv x y ->
  sb_equiv y x.
Proof. move=> x y; rewrite /sb_equiv; by symmetry. Qed.

Lemma sb_equiv_trans: forall x y z,
  sb_equiv x y ->
  sb_equiv y z ->
  sb_equiv x z.
Proof.
  move=> x y z; rewrite /sb_equiv => ? ?;
  by transitivity (sb_inj y).
Qed.

HB.instance Definition _ :=
  hasEquiv.Build subgroup_by
  sb_equiv_refl sb_equiv_sym sb_equiv_trans.

Definition sb_mul (x y : subgroup_by): subgroup_by.
Proof.
exists ((sb_point x) * (sb_point y)).
by apply /sgcharM; exact /sb_char.
Defined.

Definition sb_one: subgroup_by.
Proof. by exists 1; exact: sgchar1. Defined.

Lemma sb_mulsA: forall (x y z: subgroup_by),
  sb_mul x (sb_mul y z) \approx sb_mul (sb_mul x y) z.
Proof.
  move=> x y z.
  rewrite /sb_mul /= /equiv/= /sb_equiv /= /sb_inj /=.
  by rewrite mulsA.
Qed.

Lemma sb_mul1s: forall (x: subgroup_by),
  sb_mul sb_one x \approx x.
Proof.
  move=> x;
  rewrite /sb_mul /= /equiv /= /sb_equiv /= /sb_inj /=.
  by rewrite mul1s.
Qed.

Lemma sb_muls1: forall (x: subgroup_by),
  sb_mul x sb_one \approx x.
Proof.
  move=> x;
  rewrite /sb_mul /= /equiv /= /sb_equiv /= /sb_inj /=.
  by rewrite muls1.
Qed.

Lemma sb_muls_extl: forall (x y z: subgroup_by),
  y \approx z -> sb_mul x y \approx sb_mul x z.
Proof.
  move => x y z ?.
  rewrite /sb_mul /= /equiv /= /sb_equiv /= /sb_inj /=.
  exact: muls_extl.
Qed.

Lemma sb_muls_extr: forall (x y z: subgroup_by),
  y \approx z -> sb_mul y x \approx sb_mul z x.
Proof.
  move => x y z ?.
  rewrite /sb_mul /= /equiv /= /sb_equiv /= /sb_inj /=.
  exact: muls_extr.
Qed.

HB.instance Definition _ := isSetoidMonoid.Build subgroup_by
  sb_mulsA sb_mul1s sb_muls1 sb_muls_extl sb_muls_extr.

Definition sb_inv: subgroup_by -> subgroup_by.
Proof.
  move=> x; exists (sb_point x)^-1;
  by exact /sgcharV /sb_char.
Defined.

Lemma sb_invsM: forall x y,
  sb_inv (x * y) \approx (sb_inv y) * (sb_inv x).
Proof.
  move=> x y;
  rewrite /sb_inv /= /equiv /= /sb_equiv /sb_inj /=;
  by rewrite invsM.
Qed.

Lemma sb_mulsV : forall x,
  x * (sb_inv x) \approx 1.
Proof.
  move=> x;
  rewrite /sb_inv /= /equiv /= /sb_equiv /sb_inj /=;
  by rewrite mulsV.
Qed.

Lemma sb_mulVs : forall x,
  (sb_inv x) * x \approx 1.
Proof.
  move=> x;
  rewrite /sb_inv /= /equiv /= /sb_equiv /sb_inj /=;
  by rewrite mulVs.
Qed.

HB.instance Definition _ := isSetoidGroup.Build subgroup_by
  sb_invsM sb_mulsV sb_mulVs.

Lemma sb_equivfM: forall x y,
  x \approx y ->
  sb_inj x \approx sb_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isSetoidMorphism.Build _ _ sb_inj sb_equivfM.

Lemma sb_injfM: forall x y,
  x \approx y ->
  sb_inj x \approx sb_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isInjective.Build _ _ 
    sb_inj 
    sb_injfM.

Lemma sb_onefM: sb_inj 1 \approx 1.
Proof. done. Qed.

Lemma sb_mulfM: forall x y,
  sb_inj (x * y) \approx (sb_inj x) * (sb_inj y).
Proof. done. Qed.

HB.instance Definition _ := 
  isMonoidMorphism.Build _ _
    sb_inj 
    sb_onefM 
    sb_mulfM.

HB.instance Definition _ :=
  isSubgroup.Build G subgroup_by sb_inj.

End SubgroupByCharacterization.
Arguments subgroup_by {_}.
Arguments sb_char {_ _}.
Arguments sb_point {_ _}.

#[deprecated(since="2026-10-28", note="Use sb_char instead.")]
Notation sb_point_characterization := sb_char.
#[deprecated(since="2026-10-28", note="Use sb_inj instead.")]
Notation subgroupby_inj := sb_inj.
#[deprecated(since="2026-10-28", note="Use sb_equiv instead.")]
Notation subgroupby_eq := sb_equiv.

(* TODO(reiniscirpons): Do we need this? *)
(* {e}, the subgroup! *)
Section SingletonSubgroup.
Variable K: setoidGroupType.

Definition ssc_char (x: K): Prop :=
  (x \approx 1).

Lemma ssc_one: ssc_char 1.
Proof. by rewrite /ssc_char. Qed.

Lemma ssc_inv (x: K): ssc_char x -> ssc_char (x^-1).
Proof.
  by rewrite /ssc_char => ->; rewrite invs1.
Qed.

Lemma ssc_mul (x y: K):
  ssc_char x ->
  ssc_char y ->
  ssc_char (x * y).
Proof.
  by rewrite /ssc_char => -> ->; rewrite mul1s.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build K
  ssc_char ssc_mul ssc_one ssc_inv.

Definition singleton_subgroup := subgroup_by ssc_char.

Definition singleton_morphism:
  singleton_subgroup -> singleton_subgroup := id.

Lemma sm_equivfM: forall x y,
  x \approx y ->
  singleton_morphism x \approx singleton_morphism y.
Proof. done. Qed.

Lemma sm_onefM:
  singleton_morphism 1 \approx 1.
Proof. done. Qed.

Lemma sm_mulfM: forall x y,
  singleton_morphism (x * y) \approx
  (singleton_morphism x) * (singleton_morphism y).
Proof. done. Qed.

HB.instance Definition _ :=
  isSetoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_equivfM.

HB.instance Definition _ :=
  isMonoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_onefM
    sm_mulfM.

End SingletonSubgroup.

(* TODO(reiniscirpons): Do we need this? *)
(* Intersection of subgroups *)
Section SubgroupIntersection.
Context {G: setoidGroupType}.
Variable (H1 H2: subgroup G).

Definition is_in_intersection (x: G): Prop :=
  (x \insubgroup H1) /\ (x \insubgroup H2).

Definition iii_charM : forall (x y: G),
  is_in_intersection x ->
  is_in_intersection y ->
  is_in_intersection (x * y).
Proof.
move=> x y [[x1 x1_eq] [x2 x2_eq]] [[y1 y1_eq] [y2 y2_eq]]; 
eexists.
- by exists (x1 * y1); rewrite mulfM -x1_eq -y1_eq.
- by exists (x2 * y2); rewrite mulfM -x2_eq -y2_eq.
Qed.

Definition iii_char1 : is_in_intersection 1.
Proof. by eexists; exists 1; rewrite onefM. Qed.

Definition iii_charV : forall (x: G),
  is_in_intersection x ->
  is_in_intersection (x^-1).
Proof.
move=> x [[x1 x1_eq] [x2 x2_eq]]; eexists.
- by exists (inv x1); rewrite -invfM -x1_eq.
- by exists (inv x2); rewrite -invfM -x2_eq.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G is_in_intersection iii_charM iii_char1 iii_charV.

(* we could also prove that H1 /\ H2 is a subgroup of H1 and H2 *)

Definition intersection := subgroup_by is_in_intersection.

End SubgroupIntersection.
