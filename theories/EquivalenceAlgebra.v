From elpi.apps Require Import coercion.
From HB Require Import structures.
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Utils Equivalence.

Open Scope int_scope.
Open Scope ring_scope.

Set Implicit Arguments.

Reserved Notation "*%sg" (at level 0).

Declare Scope setoid_group_scope.
Delimit Scope setoid_group_scope with sg.
Local Open Scope setoid_group_scope.

HB.mixin Record isMonoid M of isSetoid M := {
  mul: M -> M -> M;
  one: M;
  mulgA: forall x y z,
    mul x (mul y z) \approx mul (mul x y) z;
  mul1g: forall x,
    mul one x \approx x;
  mulg1: forall x,
    mul x one \approx x;
  mul_ext: Proper (approx ==> approx ==> approx) mul;
}.
#[short(type="monoid")]
HB.structure Definition Monoid := { G of isMonoid G & isSetoid G }.

Bind Scope setoid_group_scope with Monoid.sort.

Local Notation "*%sg" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : setoid_group_scope.
Local Notation "1" := (@one _) : setoid_group_scope.

Section ProperMonoid.
HB.declare Context G of isSetoid G & isMonoid G.

Global Instance :
  Proper (approx ==> approx ==> approx) (mul : G -> G -> G).
Proof. exact: mul_ext. Qed.

End ProperMonoid.

(* If `l = [a; b; c; ...; z]`, `prod l = a @ b @ ... @ z` *)
Definition prod {M: monoid} (l: seq M) : M :=
  foldr (fun y acc => y * acc) 1 l.
Arguments prod {_} / !_.

Lemma prod0 {M: monoid} : @prod M nil = 1.
Proof. done. Qed.

Lemma prod1s {M: monoid} (a: M) (l: seq M) :
  prod (a :: l) \approx a * prod l.
Proof. done. Qed.

Lemma prod_cat {M: monoid} (l1 l2: seq M):
  prod (l1 ++ l2) \approx (prod l1) * (prod l2).
Proof.
  elim: l1 => [|a l1 /= ->]; first by rewrite /= mul1g.
  by rewrite mulgA.
Qed.

(** Some theory about morphisms *)

HB.mixin Record isMonoidMorphism (G H: monoid) (f: G -> H) := {
  morphism_preserve_one:
    f 1 \approx 1;
  morphism_preserve_mul: forall x y,
    f (x * y) \approx (f x) * (f y);
}.
#[short(type="morphism")]
HB.structure Definition Morphism (G H: monoid) :=
  { f of isSetoidMorphism G H f 
       & isMonoidMorphism G H f}.


HB.mixin Record isInjective (A B: setoid) (f: A -> B) := {
  injectivity_property:
    forall x y, f x \approx f y -> x \approx y;
}.

#[short(type="injectiveFunType")]
HB.structure Definition Injective (A B: setoid) :=
  { f of isInjective A B f
       & isSetoidMorphism A B f}.

#[short(type="injectiveMorphism")]
HB.structure Definition InjectiveMorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.mixin Record isSurjective (A B: setoid) (f: A -> B) := {
  surjectivity_property: forall y, exists x,
    f x \approx y;
}.

#[short(type="surjectiveFunType")]
HB.structure Definition Surjective (A B: setoid) :=
  { f of isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="surjectiveMorphism")]
HB.structure Definition SurjectiveMorphism (G H: monoid) :=
  { f of isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

#[short(type="bijectiveFunType")]
HB.structure Definition Bijective (A B: setoid) :=
  { f of isInjective A B f
       & isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="isomorphism")]
HB.structure Definition Isomorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.factory Record isIsomorphismInverse
  (S T: monoid) (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_approx': forall x y,
      x \approx y -> g x \approx g y;
    morphism_inverse_left: forall x,
      g (f x) \approx x;
    morphism_inverse_right: forall x,
      f (g x) \approx x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_approx'.

  Fact g_surjectivity_property: forall y, exists x,
    g x \approx y.
  Proof.
    move => y; exists (f y); by apply morphism_inverse_left.
  Qed.

  HB.instance Definition _ :=
    isSurjective.Build _ _ g g_surjectivity_property.
  
  Fact g_injectivity_property: forall x y,
    g x \approx g y -> x \approx y.
  Proof.
    move => x y Hg; have: f (g x) \approx f (g y).
    - by apply morphism_preserve_approx.
    by rewrite !morphism_inverse_right.
  Qed.

  HB.instance Definition _ :=
    isInjective.Build _ _ g g_injectivity_property.

  Fact g_preserve_e: g 1 \approx 1.
  Proof.
    by rewrite -(morphism_inverse_left 1) morphism_preserve_one.
  Qed.

  Fact g_preserve_law: forall x y,
    g (x * y) \approx g x * g y.
  Proof.
    move => x y.
    move: (@surjectivity_property _ _ f x) => [x'] <-.
    move: (@surjectivity_property _ _ f y) => [y'] <-.
    by rewrite -morphism_preserve_mul !morphism_inverse_left.
  Qed.

  HB.instance Definition _ :=
    isMonoidMorphism.Build _ _ g g_preserve_e g_preserve_law.
HB.end.

HB.factory Record isIsomorphismLeftInverse
  (S T: monoid) (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_approx': forall x y,
      x \approx y -> g x \approx g y;
    morphism_inverse_left: forall x,
      g (f x) \approx x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismLeftInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_approx'.

  Fact morphism_inverse_right': forall y,
    f (g y) \approx y.
  Proof.
    move => y.
    move: (@surjectivity_property _ _ f y) => [x] <-;
    by apply /morphism_preserve_approx /morphism_inverse_left.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      morphism_preserve_approx'
      morphism_inverse_left
      morphism_inverse_right'.
HB.end.

HB.factory Record isIsomorphismRightInverse
  (S T: monoid) (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_approx': forall x y,
      x \approx y -> g x \approx g y;
    morphism_inverse_right: forall x,
      f (g x) \approx x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismRightInverse S T f g.

  Fact morphism_inverse_left': forall x,
    g (f x) \approx x.
  Proof.
    move => x; apply (@injectivity_property _ _ f).
    by apply morphism_inverse_right.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      morphism_preserve_approx'
      morphism_inverse_left'
      morphism_inverse_right.
HB.end.

(** Composition of morphisms *)

(* TODO(reiniscirpons): This feels like something that 
   has already been done. *)
Section MorphismComposition.

Context {S T U: monoid}.
Variable f: morphism S T.
Variable g: morphism T U.

Lemma comp_preserve_e: (g \o f) 1 \approx 1.
Proof. by rewrite /comp !morphism_preserve_one. Qed.

Lemma comp_preserve_law: forall x y,
  (g \o f) (x * y) \approx ((g \o f) x) * ((g \o f) y).
Proof. move => x y; by rewrite /comp !morphism_preserve_mul. Qed.

HB.instance Definition _ :=
  isMonoidMorphism.Build S U (g \o f) comp_preserve_e comp_preserve_law.
End MorphismComposition.

Section InjectionComposition.
Context {A B C: setoid}.
Variable f: injectiveFunType A B.
Variable g: injectiveFunType B C.

Lemma comp_preserve_injectivity_property: forall x y,
  (g \o f) x \approx (g \o f) y -> x \approx y.
Proof.
  move => x y; rewrite /comp;
  by move/injectivity_property/injectivity_property.
Qed.
HB.instance Definition _ :=
  isInjective.Build A C (g \o f) comp_preserve_injectivity_property.
End InjectionComposition.

Section SurjectionComposition.
Context {A B C: setoid}.
Variable f: surjectiveFunType A B.
Variable g: surjectiveFunType B C.


Lemma comp_preserve_surjectivity_property: forall y, exists x,
  (g \o f) x \approx y.
Proof.
  move => y.
  move: (@surjectivity_property _ _ g y) => [z] Hz.
  move: (@surjectivity_property _ _ f z) => [x] Hx.
  by exists x; rewrite /= Hx Hz.
Qed.
HB.instance Definition _ :=
  isSurjective.Build A C (g \o f) comp_preserve_surjectivity_property.
End SurjectionComposition.

Section IsomorphismComposition.
Context {S T U: monoid}.
Variable f: isomorphism S T.
Variable g: isomorphism T U.

(* TODO(reiniscirpons): Without this line isomorphism composition
  is not an isomorphism. Why? *)
HB.instance Definition _ :=
  isSetoidMorphism.Build S U
  (g \o f) morphism_preserve_approx.
End IsomorphismComposition.


(** Theory of groups *)

HB.mixin Record isGroup G of isSetoid G & isMonoid G := {
  inv : G -> G;
  invgM : forall x y,
    inv (x * y) \approx (inv y) * (inv x);
  invgV : forall x,
    x * (inv x) \approx 1;
  invVg : forall x,
    (inv x) * x \approx 1;
}.
#[short(type="group")]
HB.structure Definition Group :=
  { G of isGroup G & isSetoid G & isMonoid G }.

Bind Scope setoid_group_scope with Group.sort.

Local Notation "x ^-1" := (inv x) : setoid_group_scope.
Local Notation "x ^- n" := ((x ^+ n)^-1) : setoid_group_scope.

Lemma invgK {G: group}: forall (g: G),
  g^-1^-1 \approx g.
Proof.
move=> g.
have: g * (g^-1 * g^-1^-1) \approx g * (g^-1 * g).
  by rewrite invgV invVg.
by rewrite !mulgA invgV !mul1g.
Qed.

Lemma invg1 {G: group}: 1^-1 \approx 1 :> G.
Proof.
  have: 1^-1 * 1 \approx 1 :> G => [|{2}<-];
    first by rewrite invVg.
  by rewrite mulg1.
Qed.


Section ProperGroup.
HB.declare Context G of isSetoid G & isMonoid G & isGroup G.

Global Instance : Proper (approx ==> approx) (@inv G).
Proof.
move=> a b eq_ab.
have H: a^-1 * b \approx 1;
  first by rewrite -eq_ab invVg.
have: a^-1 * b * b^-1 \approx b^-1;
  first by rewrite H mul1g.
by rewrite -mulgA invgV mulg1.
Qed.

End ProperGroup.

Lemma prod_inv {G: group} (l: seq G):
  (prod l)^-1 \approx prod (map inv (rev l)).
Proof.
elim: l => [/=|c l].
  by rewrite invg1.
rewrite -cat1s rev_cat map_cat !prod_cat invgM => ->.
by rewrite /= !mulg1.
Qed.

Lemma prod_rcons {G: group} (l: seq G) (c: G):
  prod (rcons l c) \approx (prod l) * c.
Proof.
elim: l => /= [|a l ->].
  by rewrite mul1g mulg1.
by rewrite mulgA.
Qed.

Lemma morphism_preserve_inv:
  forall (G H: group) (f: morphism G H) x,
  (f x)^-1 \approx f (x^-1).
Proof.
  move => G H f x.
  have H1: (f x) * (f (x^-1)) \approx 1.
  - rewrite -morphism_preserve_mul -morphism_preserve_one;
    apply morphism_preserve_approx; by rewrite invgV.
  - by rewrite -(mul1g (f (inv x))) -(invVg (f x))
            -mulgA H1 mulg1.
Qed.

Definition power {G: group} (w: G) (k: int) : G :=
  match k with
  | Posz k => iter k (fun acc => w * acc) 1
  | Negz k => iter k.+1 (fun acc => w^-1 * acc) 1 (* Negx 0 is -1 *)
  end.

Notation "x ^ n" := (power x n) : setoid_group_scope.

Lemma power0 {G: group} (w: G): w ^ 0 = 1.
Proof. done. Qed.

Lemma powerS {G: group} (w: G) (x: nat):
  w ^ x.+1 = w * w ^ x.
Proof. done. Qed.

Lemma powerP {G: group} (w: G) (x: nat):
  w ^ (- (x.+1%:Z)) = w^-1 * w ^(- x%:Z).
Proof. by case: x. Qed.

(* TODO(reiniscirpons): I locked power here to avoid it being simplified
   in contexts where we dont want it to be later on.
   But now, it wont evaluate powers with a concrete, e.g.
   power w (-1) is left unexpanded. Is there some intermediate that would
   work? *)
Arguments power {_} _ _: simpl never.

Lemma power_e {G: group} (k: int) :
  1 ^ k \approx 1 :> G.
Proof.
  elim: k => [//||] k.
  - by rewrite powerS => ->; rewrite mul1g.
  - by rewrite powerP => ->; rewrite mulg1 invg1.
Qed.

(* TODO(reiniscirpons): Should I be defining my own induction principles?*)
Definition nat_pairs_ind: forall (P: nat -> Prop),
  P 0 -> P (1: nat) -> (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move => P H0 H1 HnSn n; enough (H: P n /\ P n.+1).
  - by case: H.
  elim: n => [//|n [Hn HSn]]; split => [//|].
  by apply HnSn.
Qed.

Lemma power_inv {G: group} (w: G) (x:int):
  w ^ (- x) \approx (w ^ x)^-1.
Proof.
case: x; elim/nat_pairs_ind => [||k].
- by rewrite /power /= invg1.
- by rewrite /power /= invgM mulg1 invg1 mul1g.
- rewrite !powerS !powerP !invgM => <- H.
  by rewrite H -{2}H mulgA.
- by rewrite /power /= !mulg1 invgK.
- by rewrite /power /= !mulg1 invgM invgK.
- rewrite !powerS !powerP !invgM !invgK => <- H.
  by rewrite H -{2}H !mulgA.
Qed.

Lemma powerC' {G: group} (w: G) (x: int):
  (w ^ x) * w \approx w * (w ^ x).
Proof.
elim: x => [|x H|x].
- by rewrite power0 mul1g mulg1.
- by rewrite powerS -{2}H mulgA.
- rewrite !power_inv powerS /= invgM => eq.
  rewrite mulgA -eq.
  by rewrite -!mulgA invgV invVg mulg1.
Qed.

Lemma powerC'' {G: group} (w: G) (x: int):
  (w ^ x) * w^-1 \approx w^-1 * (w ^ x).
Proof.
  case: x.
  - case => [|k].
  -- by rewrite /power /= mulg1 mul1g.
  -- rewrite powerS -{1}powerC'.
    by rewrite -mulgA invgV mulgA
               invVg mul1g mulg1.
  - elim => [|n H].
  -- by rewrite /power /= mulg1.
  -- by rewrite powerP -{2}H mulgA.
Qed.

Lemma powerC {G: group} (w: G) (x y: int):
  w ^ x * w ^ y \approx w ^ y * w ^ x.
Proof.
  elim: x => [|n IH|n IH].
  - by rewrite power0 mul1g mulg1.
  - by rewrite powerS -mulgA IH mulgA -powerC' mulgA.
  - by rewrite powerP -mulgA IH mulgA -powerC'' mulgA.
Qed.

Lemma powerS' {G: group} (w: G) (x: int):
  w ^ (1 + x) \approx w * (w ^ x).
Proof.
  case: x => n /=.
  - by rewrite /power /=.
  - case: n => [|n].
  -- by rewrite /power /= mulg1 invgV.
  -- rewrite /power /= !mulgA invgV mul1g.
     by have ->: (n.+1 - 1 = n)%N by case: n.
Qed.

Lemma powerP' {G: group} (w: G) (x: int):
  w ^ (-1 + x) \approx w^-1 * (w ^ x).
Proof.
  case: x => n /=.
  - case: n => [|n].
  -- by rewrite /power /= mulg1.
  -- rewrite /power /= mulgA invVg mul1g.
     by have ->: (n.+1 - 1 = n)%N by case: n.
  - by rewrite /power /=.
Qed.

Lemma power_add {G: group} (w: G) (x y: int):
  w ^ (x + y) \approx (w ^ x) * (w ^ y).
Proof.
elim: x => [|x H|x H].
- by rewrite add0r power0 mul1g.
- have ->: x.+1%:Z + y = 1 + (x%:Z + y) by lia.
  by rewrite powerS powerS' -mulgA H.
- have ->: - x.+1%:Z + y = -1 + (- x%:Z + y) by lia.
  by rewrite powerP powerP' H mulgA.
Qed.

Lemma power_switch_sign {G: group} (w: G) (x y: int):
  (w ^ x) ^ (- y) \approx (w ^ (-x)) ^ y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !power0.
- rewrite powerP powerS => ->.
  by rewrite -power_inv.
- rewrite !opprK powerS powerP => ->.
  by rewrite -power_inv opprK.
Qed.

Lemma powerC'_tower {G: group} (w: G) (x y: int):
  (w ^ x) ^ y * w \approx w * (power w x) ^ y.
Proof.
elim: y => [|y|y].
- by rewrite power0 mul1g mulg1.
- rewrite powerS -mulgA => ->.
  by rewrite mulgA powerC' mulgA.
- rewrite powerP -mulgA => ->.
  by rewrite mulgA -power_inv powerC' mulgA.
Qed.

Lemma powerC''_tower {G: group} (w: G) (x y: int):
  (w ^ x) ^ y * (w^-1) \approx (w^-1) * (w ^ x) ^ y.
Proof.
elim: y => [|y|y].
- by rewrite power0 mul1g mulg1.
- rewrite powerS -mulgA => ->.
  by rewrite mulgA powerC'' mulgA.
- rewrite powerP -mulgA => ->.
  by rewrite mulgA -power_inv powerC'' mulgA.
Qed.

Lemma power_mul {G: group} (w: G) (x y: int):
  w ^ (x * y) \approx (w ^ x) ^ y.
Proof.
elim: x => [|x|x].
- by rewrite mul0r !power0 power_e.
- rewrite powerS.
  have ->: (x.+1%:Z * y)%R = x%:Z * y + y by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 mul1g.
  - rewrite !powerS => <-.
    by rewrite !mulgA -[w * _]powerC' -![((_ * w) * _)]mulgA
            -powerC'_tower !mulgA.
  - rewrite !power_switch_sign !powerP => <-.
    rewrite powerS invgM -power_inv.
    by rewrite mulgA -[(_ * _) * inv w]mulgA
            -mulgA powerC''_tower !mulgA.
- have ->: (- x.+1%:Z * y)%R = - x%:Z*y + (-y) by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 mul1g.
  - rewrite !powerS !powerP => <-.
    by rewrite !mulgA -[inv w * _]powerC''
            -![((_ * inv w) * _)]mulgA
            -powerC''_tower !mulgA.
  - have ->: (- - y%:Z) = y%:Z by lia.
    have ->: (- - y.+1%:Z) = y.+1%:Z by lia.
    rewrite powerS ![power _ (- y.+1%:Z)]powerP => <-.
    rewrite powerP invgM invgK.
    by rewrite !mulgA -[(_ * _) * w]mulgA
            -mulgA  powerC'_tower  !mulgA.
Qed.

Lemma power_proper_pos {G: group} (x y: G) (k: nat):
  x \approx y -> x ^ k \approx y ^ k.
Proof.
move=> Heq.
elim: k => [//|k IH].
by rewrite !powerS IH Heq.
Qed.

Lemma power_proper {G: group} (x y: G) (k: int):
  x \approx y -> x ^ k \approx y ^ k.
Proof.
move=> Heq.
case: k => k.
  exact: power_proper_pos.
have ->: Negz k = - (k.+1)%:Z by done.
by rewrite !power_inv power_proper_pos.
Qed.
Arguments power_proper {_ _ _}.

Global Instance: forall G, Proper
  (approx ==> eq ==> approx) (@power G).
Proof.
  by move => G x y Hxy h k ->; apply power_proper.
Qed.

Lemma morphism_preserve_power_pos {G G': group} (f: morphism G G') (x: G) (k: nat):
  f (x ^ k) \approx (f x) ^ k.
Proof.
elim: k => [/=|k].
  by rewrite morphism_preserve_one.
by rewrite !powerS morphism_preserve_mul => <-.
Qed.
Lemma morphism_preserve_power {G G': group} (f: morphism G G') (x: G) (k: int):
  f (x ^ k) \approx (f x) ^ k.
Proof.
case: k => k.
  exact: morphism_preserve_power_pos.
have ->: Negz k = - (k.+1)%:Z by done.
rewrite !power_inv -morphism_preserve_inv.
by rewrite morphism_preserve_power_pos.
Qed.


#[short(type="deceqGroupType")]
HB.structure Definition DecEqGroup :=
  { G of isGroup G & isSetoid G & isMonoid G & hasDecEq G }.

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

Definition in_subgroup {G: group} (K: subgroup G) (x: G) :=
  exists x': K, subgroup_inj x' \approx x.
Notation "x '\insubgroup' K" := (in_subgroup K x) (at level 10).

(* this definition is useful as due to non-forgetful inheritance, seeing a subgroup of a subgroup of a group as a subgroup of the group is not easy *)
Definition in_subsubgroup (G: group) (H: subgroup G) (I: subgroup H) (x: G) :=
  exists x': I, subgroup_inj (subgroup_inj x') \approx x.
Notation "x '\insubsubgroup[' Subgroup ']' Subsubgroup" :=
  (@in_subsubgroup _ Subgroup Subsubgroup x) (at level 10).

Lemma in_subgroup_proper {Group: group} (Subgroup: subgroup Group) (x x': Group):
  (x \approx x') ->
  (x \insubgroup Subgroup) ->
  (x' \insubgroup Subgroup).
Proof.
move=> Heq [xS ?].
exists xS.
by rewrite -Heq.
Qed.

Lemma in_subgroup_e {Group: group} {Subgroup: subgroup Group}:
  1 \insubgroup Subgroup.
Proof. exists 1; by rewrite morphism_preserve_one. Qed.

Lemma in_subgroup_law {Group: group} {Subgroup: subgroup Group} (x y: Group):
  (x \insubgroup Subgroup) ->
  (y \insubgroup Subgroup) ->
  ((x * y) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
case=> [y' Hy'].
exists (x' * y').
by rewrite morphism_preserve_mul -Hx' -Hy'.
Qed.

Lemma in_subgroup_inv {Group: group} {Subgroup: subgroup Group} (x: Group):
  (x \insubgroup Subgroup) -> ((inv x) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
exists (inv x').
by rewrite -Hx' morphism_preserve_inv.
Qed.

Lemma in_subsubgroup_proper {G: group} (H: subgroup G) (I: subgroup H) (x x': G) :
  x \approx x' ->
  (x \insubsubgroup[H] I) ->
  (x' \insubsubgroup[H] I).
Proof.
move=> Heq [xK eq].
exists xK.
by rewrite eq.
Qed.


Definition is_subgroup_stable {G: group} {H1 H2: subgroup G} (f: morphism H1 H2) (K: subgroup G) :=
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

Context {G: group}.
Variable H: subgroup G.

Definition right_coset_eq (x y: G): Prop :=
  in_subgroup H (x * inv y).

Lemma right_coset_eq': forall x y,
  right_coset_eq x y <->
  (exists w: H, (subgroup_inj w) * y \approx x).
Proof.
  move => x y; split.
  - rewrite /right_coset_eq /in_subgroup.
    case => w Hw; exists w;
    by rewrite Hw -mulgA invVg mulg1.
  - case => w Hw; exists w;
    by rewrite -Hw -mulgA invgV mulg1.
Qed.

Instance RightCosetEqReflexivity : Reflexive right_coset_eq.
Proof.
  move => x; rewrite right_coset_eq'; exists 1;
  by rewrite morphism_preserve_one mul1g.
Qed.
Instance RightCosetEqSymmetry : Symmetric right_coset_eq.
Proof.
  move => x y; rewrite !right_coset_eq'.
  case => w Hw; exists (inv w).
  by rewrite -morphism_preserve_inv -Hw mulgA invVg mul1g.
Qed.
Instance RightCosetEqTransitivity : Transitive right_coset_eq.
Proof.
  move => x y z; rewrite !right_coset_eq'.
  move => [w1 H1] [w2 H2]; exists (w1 * w2).
  by rewrite morphism_preserve_mul -mulgA H2 H1.
Qed.
Instance RightCosetEqEquivalence : Equivalence right_coset_eq := {}.
End RightCoset.
Existing Instance RightCosetEqReflexivity.
Existing Instance RightCosetEqSymmetry.
Existing Instance RightCosetEqTransitivity.
Existing Instance RightCosetEqEquivalence.
Arguments right_coset_eq {_}.

HB.mixin Record isRightCosetRep
  (G: group) (H: subgroup G) (f: G -> G) := {
  right_coset_rep_correct: forall (x: G),
    right_coset_eq H x (f x);
  right_coset_rep_unique: forall (x y: G),
    right_coset_eq H x y -> f x = f y;
}.

#[short(type="rightCosetRep")]
HB.structure Definition RightCosetRep {G: group} (H: subgroup G) :=
  { f of isRightCosetRep G H f }.

Lemma right_coset_eq_spec: forall G (H: subgroup G)
  (f: rightCosetRep H) (x y: G),
  (right_coset_eq H x y) <-> (f x = f y).
Proof.
  move => G H f x y; split.
  - by apply right_coset_rep_unique.
  move => Hf; transitivity (f x).
  - by apply right_coset_rep_correct.
  rewrite Hf; symmetry; by apply right_coset_rep_correct.
Qed.

HB.mixin Record isSubgroupCharacterizer (G: group) (P: G -> Type) := {
  P_law: forall x y, P x -> P y -> P (x * y);
  P_neutral: P 1;
  P_inv: forall x, P x -> P (x^-1);
}.
#[short(type = "subgroup_characterizer")]
HB.structure Definition SubgroupCharacterizer (G: group) := { P of isSubgroupCharacterizer G P }.

Section SubgroupByCharacterization.
Context {G: group}.
Variable P: subgroup_characterizer G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point: G;
  sb_point_characterization: P sb_point;
}.

Definition subgroupby_inj (x: subgroup_by): G := x.(sb_point).

Definition subgroupby_eq (x y: subgroup_by) :=
  (subgroupby_inj x) \approx (subgroupby_inj y).
Lemma subgroupby_eq_refl: forall x, subgroupby_eq x x.
Proof. by move=> x; rewrite /subgroupby_eq. Qed.
Lemma subgroupby_eq_sym: forall x y,
  subgroupby_eq x y -> subgroupby_eq y x.
Proof.
  move=> x y; rewrite /subgroupby_eq; by symmetry.
Qed.
Lemma subgroupby_eq_trans: forall x y z,
  subgroupby_eq x y -> subgroupby_eq y z -> subgroupby_eq x z.
Proof.
  move=> x y z; rewrite /subgroupby_eq => ? ?;
  by transitivity (subgroupby_inj y).
Qed.

HB.instance Definition _ := isSetoid.Build subgroup_by subgroupby_eq subgroupby_eq_refl subgroupby_eq_sym subgroupby_eq_trans.

Definition subgroupby_law (x y : subgroup_by): subgroup_by.
Proof.
exists (x.(sb_point) * y.(sb_point)).
apply /P_law; exact /sb_point_characterization.
Defined.

Definition subgroupby_neutral: subgroup_by.
Proof. exists 1; exact: P_neutral. Defined.

Lemma subgroupby_mulgA: forall (x y z: subgroup_by),
  subgroupby_law x (subgroupby_law y z) \approx subgroupby_law (subgroupby_law x y) z.
Proof.
  move=> x y z;
  by rewrite /subgroupby_law/= /approx/= /subgroupby_eq/= /subgroupby_inj /= mulgA.
Qed.

Lemma subgroupby_mul1g: forall (x: subgroup_by), subgroupby_law subgroupby_neutral x \approx x.
Proof. move=> x; by rewrite /subgroupby_law/= /approx/= /subgroupby_eq/= /subgroupby_inj/= mul1g. Qed.

Lemma subgroupby_mulg1: forall (x: subgroup_by), subgroupby_law x subgroupby_neutral \approx x.
Proof. move=> x; by rewrite /subgroupby_law/= /approx/= /subgroupby_eq/= /subgroupby_inj/= mulg1. Qed.

Lemma subgroupby_mul_ext: Proper (approx ==> approx ==> approx) subgroupby_law.
Proof.
move=> x y H x1 y1.
rewrite /subgroupby_law/= /approx/= /subgroupby_eq/= /subgroupby_inj/=.
exact: mul_ext.
Qed.


HB.instance Definition _ := isMonoid.Build
  subgroup_by
  subgroupby_neutral subgroupby_mulgA
  subgroupby_mul1g subgroupby_mulg1 subgroupby_mul_ext.

Definition subgroupby_inv: subgroup_by -> subgroup_by.
Proof.
  move=> x; exists (inv x.(sb_point)); exact /P_inv /sb_point_characterization.
Defined.

Lemma subgroupby_invgM: forall x y,
  subgroupby_inv (x * y) \approx (subgroupby_inv y) * (subgroupby_inv x).
Proof.
  move=> x y;
  by rewrite /subgroupby_inv/=/approx/=/subgroupby_eq/subgroupby_inj/= invgM.
Qed.

Lemma subgroupby_inverse_left : forall x, x * (subgroupby_inv x) \approx 1.
Proof. move=> x; by rewrite /subgroupby_inv/=/mul/=/subgroupby_law/=/approx/=/subgroupby_eq/=/subgroupby_inj/= invgV. Qed.

Lemma subgroupby_inverse_right : forall x, (subgroupby_inv x) * x \approx 1.
Proof. move=> x; by rewrite /subgroupby_inv/=/mul/=/subgroupby_law/=/approx/=/subgroupby_eq/=/subgroupby_inj/= invVg. Qed.

HB.instance Definition _ := isGroup.Build subgroup_by subgroupby_inv subgroupby_invgM subgroupby_inverse_left subgroupby_inverse_right.

Lemma subgroupby_inj_preserve_equiv: forall x y, x \approx y -> subgroupby_inj x \approx subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isSetoidMorphism.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_preserve_equiv.

Lemma subgroupby_inj_injectivity: forall x y, x \approx y -> subgroupby_inj x \approx subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isInjective.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_injectivity.

Lemma subgroupby_inj_preserve_e: subgroupby_inj 1 \approx 1.
Proof. done. Qed.
Lemma subgroupby_inj_preserve_law: forall x y,
  subgroupby_inj (x * y) \approx (subgroupby_inj x) * (subgroupby_inj y).
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

Definition singleton_subgroup_char (x: K): Type := (x \approx 1).

Lemma ssc_neutral: singleton_subgroup_char 1.
Proof. by rewrite /singleton_subgroup_char. Qed.

Lemma ssc_inv (x: K): singleton_subgroup_char x -> singleton_subgroup_char (inv x).
Proof. by rewrite /singleton_subgroup_char => ->; rewrite invg1. Qed.

Lemma ssc_law (x y: K): singleton_subgroup_char x -> singleton_subgroup_char y -> singleton_subgroup_char (x * y).
Proof. by rewrite /singleton_subgroup_char => -> ->; rewrite mul1g. Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build K singleton_subgroup_char ssc_law ssc_neutral ssc_inv.

Definition singleton_subgroup := subgroup_by singleton_subgroup_char.

Definition singleton_morphism: singleton_subgroup -> singleton_subgroup := id.

Lemma sm_preserve_equiv: forall x y, x \approx y -> singleton_morphism x \approx singleton_morphism y.
Proof. done. Qed.
Lemma sm_preserve_e: singleton_morphism 1 \approx 1.
Proof. done. Qed.
Lemma sm_preserve_law: forall x y, singleton_morphism (x * y) \approx (singleton_morphism x) * (singleton_morphism y).
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
Context {G: group}.
Variable (H1 H2: subgroup G).

Record is_in_intersection (x: G) : Prop := {
  intersection_in_left: x \insubgroup H1;
  intersection_in_right: x \insubgroup H2;
}.

Definition iii_P_law : forall (x y: G), is_in_intersection x -> is_in_intersection y -> is_in_intersection (x * y).
Proof.
move=> x y [[x1 x1_eq] [x2 x2_eq]] [[y1 y1_eq] [y2 y2_eq]]; eexists.
- by exists (x1 * y1); rewrite morphism_preserve_mul -x1_eq -y1_eq.
- by exists (x2 * y2); rewrite morphism_preserve_mul -x2_eq -y2_eq.
Qed.

Definition iii_P_neutral : is_in_intersection 1.
Proof. by eexists; exists 1; rewrite morphism_preserve_one. Qed.

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
