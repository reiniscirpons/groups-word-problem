From elpi.apps Require Import coercion.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.
Require Import Setoid Morphisms.

From GWP Require Import Utils Equivalence.

Open Scope int_scope.
Open Scope ring_scope.

HB.mixin Record isMonoid M of hasEq M := {
  law : M -> M -> M;
  e : M;
  associativity : forall x y z, law x (law y z) == law (law x y) z;
  neutral_left : forall x, law e x == x;
  neutral_right : forall x, law x e == x;
  congruent_left : forall x y z, y == z -> law x y == law x z;
  congruent_right : forall x y z, y == z -> law y x == law z x;
}.
#[short(type="monoid")]
HB.structure Definition Monoid := { G of isMonoid G & hasEq G }.
Infix "@" := law (at level 50).

Section ProperMonoid.
HB.declare Context G of hasEq G & isMonoid G.

Global Instance : Proper (eq ==> eq ==> eq) (law : G -> G -> G).
Proof.
move=> a b eq_ab u v eq_uv.
transitivity (a @ v); do [exact: congruent_left|exact: congruent_right].
Qed.

End ProperMonoid.

(* If `l = [a; b; c; ...; z]`, `prod l = a @ b @ ... @ z` *)
Definition prod {M: monoid} (l: seq M) : M :=
  foldr (fun y acc => y @ acc) e l.

Lemma prod0 {M: monoid} : @prod M nil = e.
Proof. done. Qed.

Lemma prod1s {M: monoid} (a: M) (l: seq M) : prod (a :: l) == a @ prod l.
Proof. by rewrite /prod. Qed.

Lemma prod_cat {M: monoid} (l1 l2: seq M): prod (l1 ++ l2) == (prod l1) @ (prod l2).
Proof.
elim: l1 => [|a l1 /= ->]; first by rewrite /= neutral_left.
by rewrite associativity.
Qed.

(** Some theory about morphisms *)

HB.mixin Record isMonoidMorphism (G H: monoid) (f: G -> H) := {
  morphism_preserve_e: f e == e;
  morphism_preserve_law: forall x y, f (x @ y) == (f x) @ (f y);
}.
#[short(type="morphism")]
HB.structure Definition Morphism (G H: monoid) :=
  { f of isSetoidMorphism G H f 
       & isMonoidMorphism G H f}.


HB.mixin Record isInjective (A B: equivType) (f: A -> B) := {
  injectivity_property: forall x y, f x == f y -> x == y;
}.

#[short(type="injectiveFunType")]
HB.structure Definition Injective (A B: equivType) :=
  { f of isInjective A B f
       & isSetoidMorphism A B f}.

#[short(type="injectiveMorphism")]
HB.structure Definition InjectiveMorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.mixin Record isSurjective (A B: equivType) (f: A -> B) := {
  surjectivity_property: forall y, exists x, f x == y;
}.

#[short(type="surjectiveFunType")]
HB.structure Definition Surjective (A B: equivType) :=
  { f of isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="surjectiveMorphism")]
HB.structure Definition SurjectiveMorphism (G H: monoid) :=
  { f of isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

#[short(type="bijectiveFunType")]
HB.structure Definition Bijective (A B: equivType) :=
  { f of isInjective A B f
       & isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="isomorphism")]
HB.structure Definition Isomorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.factory Record isBijectionInverse (A B: equivType)
  (f: bijectiveFunType A B) (g: B -> A) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    cancel_left: forall x, g (f x) == x;
    cancel_right: forall x, f (g x) == x;
}.

HB.builders Context 
  (A B: equivType) (f: bijectiveFunType A B) g of 
    isBijectionInverse A B f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_equiv'.

  Fact surjectivity_property': forall y, exists x, g x == y.
  Proof.
    move => y; exists (f y); by apply cancel_left.
  Qed.

  HB.instance Definition _ :=
    isSurjective.Build _ _ g surjectivity_property'.
  
  Fact injectivity_property': forall x y, g x == g y -> x == y.
  Proof.
    move => x y Hg; have Hf: f (g x) == f (g y).
    - by apply morphism_preserve_equiv.
    by rewrite !cancel_right in Hf.
  Qed.

  HB.instance Definition _ :=
    isInjective.Build _ _ g injectivity_property'.
HB.end.

HB.factory Record isBijectionLeftInverse (A B: equivType)
  (f: bijectiveFunType A B) (g: B -> A) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    cancel_left: forall x, g (f x) == x;
}.

HB.builders Context 
  (A B: equivType) (f: bijectiveFunType A B) g of 
    isBijectionLeftInverse A B f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_equiv'.

  Fact cancel_right': forall y, f (g y) == y.
  Proof.
    move => y; have H: exists x, f x == y.
    - by apply surjectivity_property.
    case: H => x <-; apply morphism_preserve_equiv.
    by apply cancel_left.
  Qed.
  
  HB.instance Definition _ :=
    isBijectionInverse.Build _ _ f g
      morphism_preserve_equiv'
      cancel_left
      cancel_right'.
HB.end.

HB.factory Record isBijectionRightInverse (A B: equivType)
  (f: bijectiveFunType A B) (g: B -> A) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    cancel_right: forall x, f (g x) == x;
}.

HB.builders Context 
  (A B: equivType) (f: bijectiveFunType A B) g of 
    isBijectionRightInverse A B f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_equiv'.

  Fact cancel_left': forall x, g (f x) == x.
  Proof.
    move => x; apply (@injectivity_property _ _ f).
    by apply cancel_right.
  Qed.
  
  HB.instance Definition _ :=
    isBijectionInverse.Build _ _ f g
      morphism_preserve_equiv'
      cancel_left'
      cancel_right.
HB.end.

(** Composition of morphisms *)

(* TODO(reiniscirpons): This feels like something that 
   has already been done. *)
Section MorphismComposition.

Variables S T U: monoid.
Variable f: morphism S T.
Variable g: morphism T U.

Lemma comp_preserve_e: (g \o f) e == e.
Proof. by rewrite /comp !morphism_preserve_e. Qed.

Lemma comp_preserve_law: forall x y,
  (g \o f) (x @ y) == ((g \o f) x) @ ((g \o f) y).
Proof. move => x y; by rewrite /comp !morphism_preserve_law. Qed.

HB.instance Definition _ := isMonoidMorphism.Build S U (g \o f) comp_preserve_e comp_preserve_law.
End MorphismComposition.

(** Theory of groups *)

HB.mixin Record isGroup G of hasEq G & isMonoid G := {
  inv : G -> G;
  inverse_law : forall x y, inv (x @ y) == (inv y) @ (inv x);
  inverse_left : forall x, x @ (inv x) == e;
  inverse_right : forall x, (inv x) @ x == e;
}.
#[short(type="group")]
HB.structure Definition Group := { G of isGroup G & hasEq G & isMonoid G }.

Lemma inv_involutive {G: group}: forall (g: G), inv (inv g) == g.
Proof.
move=> g.
have: (inv g) @ (inv (inv g)) == (inv g) @ g.
  by rewrite inverse_left inverse_right.
move=> /(congruent_left g).
by rewrite !associativity inverse_left !neutral_left.
Qed.

Lemma inverse_e: forall G: group, (@inv G e) == e.
Proof.
  move => G.
  have: (@inv G e) @ e == e => [|{2}<-]; first by rewrite inverse_right.
  by rewrite neutral_right.
Qed.


Section ProperGroup.
HB.declare Context G of hasEq G & isMonoid G & isGroup G.

Global Instance : Proper (eq ==> eq) (inv : G -> G).
Proof.
move=> a b eq_ab.
have H: (inv a) @ b == e; first by rewrite -eq_ab inverse_right.
have: (inv a) @ b @ (inv b) == (inv b); first by rewrite H neutral_left.
by rewrite -associativity inverse_left neutral_right.
Qed.

End ProperGroup.

Lemma inv_e {G: group}: inv (s:=G) e == e.
Proof. by rewrite -{1}[inv e]neutral_right inverse_right. Qed.

Lemma prod_inv {G: group} (l: seq G):
  inv (prod l) == prod (map inv (rev l)).
Proof.
elim: l => [/=|c l].
  by rewrite inv_e.
rewrite -cat1s rev_cat map_cat !prod_cat inverse_law => ->.
by rewrite /= !neutral_right.
Qed.

Lemma prod_rcons {G: group} (l: seq G) (c: G):
  prod (rcons l c) == (prod l) @ c.
Proof.
elim: l => /= [|a l ->].
  by rewrite neutral_left neutral_right.
by rewrite associativity.
Qed.

Lemma morphism_preserve_inv:
  forall (G H: group) (f: morphism G H) x,
    inv (f x) == f (inv x).
Proof.
  move => G H f x.
  have H1: (f x) @ (f (inv x)) == e.
  - rewrite -morphism_preserve_law -morphism_preserve_e;
    apply morphism_preserve_equiv; by rewrite inverse_left.
  - by rewrite -(neutral_left (f (inv x))) -(inverse_right (f x))
            -associativity H1 neutral_right.
Qed.

Definition power {G: group} (w: G) (k: int) : G :=
  match k with
  | Posz k => iter k (fun acc => w @ acc) e
  | Negz k => iter k.+1 (fun acc => (inv w) @ acc) e (* Negx 0 is -1 *)
  end.

Lemma power0 {G: group} (w: G): power w 0 = e.
Proof. done. Qed.

Lemma powerS {G: group} (w: G) (x: nat):
  power w x.+1 = w @ (power w x).
Proof. done. Qed.

Lemma powerP {G: group} (w: G) (x: nat):
  power w (- (x.+1: int)) = (inv w) @ (power w (- (x:int))).
Proof. by case: x. Qed.

(* TODO(reiniscirpons): I locked power here to avoid it being simplified
   in contexts where we dont want it to be later on.
   But now, it wont evaluate powers with a concrete, e.g.
   power w (-1) is left unexpanded. Is there some intermediate that would
   work? *)
Arguments power {_} _ _: simpl never.

Lemma power_e {G: group} (k: int) : power (e (s:=G)) k == (e (s:=G)).
Proof.
  elim: k => [//||] k.
  - by rewrite powerS => ->; rewrite neutral_left.
  - by rewrite powerP => ->; rewrite neutral_right inv_e.
Qed.

(* TODO(reiniscirpons): Should I be defining my own induction principles?*)
Definition nat_pairs_ind: forall (P: nat -> Prop),
  P 0 -> P 1 -> (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move => P H0 H1 HnSn n; enough (H: P n /\ P n.+1).
  - by case: H.
  elim: n => [//|n [Hn HSn]]; split => [//|].
  by apply HnSn.
Qed.

Lemma power_inv {G: group} (w: G) (x:int):
  power w (- x) == inv (power w x).
Proof.
case: x; elim/nat_pairs_ind => [||k].
- by rewrite /power /= inv_e.
- by rewrite /power /= inverse_law neutral_right inv_e neutral_left.
- rewrite !powerS !powerP !inverse_law => <- H.
  by rewrite H -{2}H associativity.
- by rewrite /power /= !neutral_right inv_involutive.
- by rewrite /power /= !neutral_right inverse_law inv_involutive.
- rewrite !powerS !powerP !inverse_law !inv_involutive => <- H.
  by rewrite H -{2}H !associativity.
Qed.

Lemma powerC' {G: group} (w: G) (x: int):
  (power w x) @ w == w @ (power w x).
Proof.
elim: x => [|x H|x].
- by rewrite power0 neutral_left neutral_right.
- by rewrite powerS -{2}H associativity.
- rewrite !power_inv powerS /= inverse_law => eq.
  rewrite associativity -eq.
  by rewrite -!associativity inverse_left inverse_right neutral_right.
Qed.

Lemma powerC'' {G: group} (w: G) (x: int):
  (power w x) @ (inv w) == (inv w) @ (power w x).
Proof.
  case: x.
  - case => [|k].
  -- by rewrite /power /= neutral_right neutral_left.
  -- rewrite powerS -{1}powerC'.
    by rewrite -associativity inverse_left associativity
               inverse_right neutral_left neutral_right.
  - elim => [|n H].
  -- by rewrite /power /= neutral_right.
  -- by rewrite powerP -{2}H associativity.
Qed.

Lemma powerC {G: group} (w: G) (x y: int):
  (power w x) @ (power w y) == (power w y) @ (power w x).
Proof.
  elim: x => [|n IH|n IH].
  - by rewrite power0 neutral_left neutral_right.
  - by rewrite powerS -associativity IH associativity -powerC' associativity.
  - by rewrite powerP -associativity IH associativity -powerC'' associativity.
Qed.

Lemma powerS' {G: group} (w: G) (x: int):
  power w (1 + x) == w @ (power w x).
Proof.
  case: x => n /=.
  - by rewrite /power /=.
  - case: n => [|n].
  -- by rewrite /power /= neutral_right inverse_left.
  -- rewrite /power /= !associativity inverse_left neutral_left.
     by have ->: (n.+1 - 1 = n)%N by case: n.
Qed.

Lemma powerP' {G: group} (w: G) (x: int):
  power w (-1 + x) == (inv w) @ (power w x).
Proof.
  case: x => n /=.
  - case: n => [|n].
  -- by rewrite /power /= neutral_right.
  -- rewrite /power /= associativity inverse_right neutral_left.
     by have ->: (n.+1 - 1 = n)%N by case: n.
  - by rewrite /power /=.
Qed.

Lemma power_add {G: group} (w: G) (x y: int):
  power w (x + y) == (power w x) @ (power w y).
Proof.
elim: x => [|x H|x H].
- by rewrite add0r power0 neutral_left.
- have ->: x.+1%:Z + y = 1 + (x%:Z + y) by lia.
  by rewrite powerS powerS' -associativity H.
- have ->: - x.+1%:Z + y = -1 + (- x%:Z + y) by lia.
  by rewrite powerP powerP' H associativity.
Qed.

Lemma power_switch_sign {G: group} (w: G) (x y: int):
  power (power w x) (- y) == power (power w (-x)) y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !power0.
- rewrite powerP powerS => ->.
  by rewrite -power_inv.
- rewrite !opprK powerS powerP => ->.
  by rewrite -power_inv opprK.
Qed.

Lemma powerC'_tower {G: group} (w: G) (x y: int):
  power (power w x) y @ w == w @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity => ->.
  by rewrite associativity powerC' associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC' associativity.
Qed.

Lemma powerC''_tower {G: group} (w: G) (x y: int):
  power (power w x) y @ (inv w) == (inv w) @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity => ->.
  by rewrite associativity powerC'' associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC'' associativity.
Qed.

Lemma power_mul {G: group} (w: G) (x y: int):
  power w (x * y) == power (power w x) y.
Proof.
elim: x => [|x|x].
- by rewrite mul0r !power0 power_e.
- rewrite powerS.
  have ->: x.+1%:Z * y = x%:Z * y + y by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS => <-.
    by rewrite !associativity -[w @ _]powerC' -![((_ @ w) @ _)]associativity
            -powerC'_tower !associativity.
  - rewrite !power_switch_sign !powerP => <-.
    rewrite powerS inverse_law -power_inv.
    by rewrite associativity -[(_ @ _) @ inv w]associativity
            -associativity powerC''_tower !associativity.
- have ->: - x.+1%:Z * y = - x%:Z*y + (-y) by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS !powerP => <-.
    by rewrite !associativity -[inv w @ _]powerC'' -![((_ @ inv w) @ _)]associativity
            -powerC''_tower !associativity.
  - have ->: (- - y%:Z) = y%:Z by lia.
    have ->: (- - y.+1%:Z) = y.+1%:Z by lia.
    rewrite powerS ![power _ (- y.+1%:Z)]powerP => <-.
    rewrite powerP inverse_law inv_involutive.
    by rewrite !associativity -[(_ @ _) @ w]associativity
            -associativity  powerC'_tower  !associativity.
Qed.

Lemma power_proper_pos {G: group} (x y: G) (k: nat):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
elim: k => [//|k IH].
by rewrite !powerS IH Heq.
Qed.
Lemma power_proper {G: group} (x y: G) (k: int):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
case: k => k.
  exact: power_proper_pos.
have ->: Negz k = - (k.+1)%:Z by done.
by rewrite !power_inv power_proper_pos.
Qed.
Arguments power_proper {_ _ _}.

Lemma morphism_preserve_power_pos {G G': group} (f: morphism G G') (x: G) (k: nat):
  f (power x k) == power (f x) k.
Proof.
elim: k => [/=|k].
  by rewrite morphism_preserve_e.
by rewrite !powerS morphism_preserve_law => <-.
Qed.
Lemma morphism_preserve_power {G G': group} (f: morphism G G') (x: G) (k: int):
  f (power x k) == power (f x) k.
Proof.
case: k => k.
  exact: morphism_preserve_power_pos.
have ->: Negz k = - (k.+1)%:Z by done.
rewrite !power_inv -morphism_preserve_inv.
by rewrite morphism_preserve_power_pos.
Qed.


#[short(type="deceqGroupType")]
HB.structure Definition DecEqGroup := { G of isGroup G & hasEq G & isMonoid G & hasDecEq G }.

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

Lemma in_subsubgroup_proper {G: group} (H: subgroup G) (I: subgroup H) (x x': G) :
  x == x' ->
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

Variable G: group.
Variable H: subgroup G.

Definition right_coset_eq (x y: G): Prop := in_subgroup H (x @ inv y).

Lemma right_coset_eq': forall x y,
  right_coset_eq x y <-> (exists w: H, (subgroup_inj w) @ y == x).
Proof.
  move => x y; split.
  - rewrite /right_coset_eq /in_subgroup.
    case => w Hw; exists w;
    by rewrite Hw -associativity inverse_right neutral_right.
  - case => w Hw; exists w;
    by rewrite -Hw -associativity inverse_left neutral_right.
Qed.

Instance RightCosetEqReflexivity : Reflexive right_coset_eq.
Proof.
  move => x; rewrite right_coset_eq'; exists e;
  by rewrite morphism_preserve_e neutral_left.
Qed.
Instance RightCosetEqSymmetry : Symmetric right_coset_eq.
Proof.
  move => x y; rewrite !right_coset_eq'.
  case => w Hw; exists (inv w).
  by rewrite -morphism_preserve_inv -Hw associativity inverse_right neutral_left.
Qed.
Instance RightCosetEqTransitivity : Transitive right_coset_eq.
Proof.
  move => x y z; rewrite !right_coset_eq'.
  move => [w1 H1] [w2 H2]; exists (w1 @ w2).
  by rewrite morphism_preserve_law -associativity H2 H1.
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
HB.structure Definition RightCosetRep (G: group) (H: subgroup G) :=
  { f of isRightCosetRep G H f }.

Lemma right_coset_eq_spec: forall G H (f: rightCosetRep G H) (x y: G),
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
Variable G: group.
Variable P: subgroup_characterizer G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point: G;
  sb_point_characterization: P sb_point;
}.

Definition subgroupby_inj (x: subgroup_by): G := x.(sb_point).

Definition subgroupby_eq (x y: subgroup_by) := (subgroupby_inj x) == (subgroupby_inj y).
Lemma subgroupby_eq_refl: forall x, subgroupby_eq x x.
Proof. by move=> x; rewrite /subgroupby_eq. Qed.
Lemma subgroupby_eq_sym: forall x y, subgroupby_eq x y -> subgroupby_eq y x.
Proof. move=> x y; rewrite /subgroupby_eq; by symmetry. Qed.
Lemma subgroupby_eq_trans: forall x y z, subgroupby_eq x y -> subgroupby_eq y z -> subgroupby_eq x z.
Proof. move=> x y z; rewrite /subgroupby_eq => ? ?; by transitivity (subgroupby_inj y). Qed.

HB.instance Definition _ := hasEq.Build subgroup_by subgroupby_eq subgroupby_eq_refl subgroupby_eq_sym subgroupby_eq_trans.

Definition subgroupby_law (x y : subgroup_by): subgroup_by.
Proof.
exists (x.(sb_point) @ y.(sb_point)).
apply /P_law; exact /sb_point_characterization.
Defined.

Definition subgroupby_neutral: subgroup_by.
Proof. exists e; exact: P_neutral. Defined.

Lemma subgroupby_associativity: forall (x y z: subgroup_by), subgroupby_law x (subgroupby_law y z) == subgroupby_law (subgroupby_law x y) z.
Proof. move=> x y z; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= associativity. Qed.

Lemma subgroupby_neutral_left: forall (x: subgroup_by), subgroupby_law subgroupby_neutral x == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_left. Qed.

Lemma subgroupby_neutral_right: forall (x: subgroup_by), subgroupby_law x subgroupby_neutral == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_right. Qed.

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

HB.instance Definition _ := isMonoid.Build subgroup_by subgroupby_law subgroupby_neutral subgroupby_associativity subgroupby_neutral_left subgroupby_neutral_right subgroupby_congruent_left subgroupby_congruent_right.

Definition subgroupby_inv: subgroup_by -> subgroup_by.
Proof. move=> x; exists (inv x.(sb_point)); exact /P_inv /sb_point_characterization. Defined.

Lemma subgroupby_inverse_law: forall x y, subgroupby_inv (x @ y) == (subgroupby_inv y) @ (subgroupby_inv x).
Proof. move=> x y; by rewrite /subgroupby_inv/=/eq/=/subgroupby_eq/subgroupby_inj/= inverse_law. Qed.

Lemma subgroupby_inverse_left : forall x, x @ (subgroupby_inv x) == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_left. Qed.

Lemma subgroupby_inverse_right : forall x, (subgroupby_inv x) @ x == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_right. Qed.

HB.instance Definition _ := isGroup.Build subgroup_by subgroupby_inv subgroupby_inverse_law subgroupby_inverse_left subgroupby_inverse_right.

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

Lemma subgroupby_inj_preserve_e: subgroupby_inj e == e.
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
Proof. by rewrite /singleton_subgroup_char => -> ->; rewrite neutral_left. Qed.

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
Variable G: group.
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
