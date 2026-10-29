From elpi.apps Require Import coercion.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra div.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.
Require Import Setoid Morphisms.

From GWP Require Import Utils Equivalence EquivalenceAlgebra Presentation FreeGroup.

Open Scope setoid_group_scope.
Import SetoidGroupNotations.

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
  (f: rightCosetRep G H) (x y: G),
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


Open Scope int_scope.
Open Scope ring_scope.
Import PresentationNotations.

(* Subgroup generated by a sequence of group elements *)
Section GeneratedSubgroup.

Context {G: group}.
Variable gens: seq G.

Let Sigma := (ordinal (size gens)).
Definition nth_gen := fun (n: Sigma) => nth e gens n.

Definition in_generated_subgroup (x: G): Prop :=
  exists (w: FreeGroup Sigma), \hat nth_gen w == x.

Lemma igs_law 
  (x y: G) (Hx: in_generated_subgroup x) (Hy: in_generated_subgroup y):
  in_generated_subgroup (x @ y).
Proof.
case: Hx => [wx Hx].
case: Hy => [wy Hy].
exists (wx @ wy).
by rewrite morphism_preserve_law /= Hx Hy.
Defined.

Lemma igs_e: in_generated_subgroup e.
Proof. by exists e. Defined.

Lemma igs_inv (x: G) (Hx: in_generated_subgroup x):
  in_generated_subgroup (inv x).
Proof.
case: Hx => [astx Hx].
exists (inv astx).
by rewrite -morphism_preserve_inv /= Hx.
Defined.

HB.instance Definition _ := isSubgroupCharacterizer.Build 
  G in_generated_subgroup igs_law igs_e igs_inv.

(* TODO(reiniscirpons): Would be nicer to have 
   the lemma use (g: G) and then have
   g \in gens as a condition, but that doesn't typecheck.
*)
Lemma igs_gen (s: Sigma): in_generated_subgroup (nth_gen s).
Proof.
  exists ([word [:: Base s]]_(FGP Sigma)).
  by rewrite /= neutral_right.
Defined.

Definition generatedSubgroup :=
  subgroup_by in_generated_subgroup.

Definition subgroup_projection:
  (FreeGroup Sigma) -> generatedSubgroup.
Proof.
  by move => w; exists (\hat nth_gen w); exists w.
Defined.

Lemma subgroup_projection_preserve_equiv:
  forall x y: FreeGroup Sigma,
    x == y -> subgroup_projection x == subgroup_projection y.
Proof.
  move => x y Heq; enough (H: \hat nth_gen x == \hat nth_gen y) => [//|].
  by apply morphism_preserve_equiv.
Qed.

HB.instance Definition _ := isSetoidMorphism.Build 
  _ _ subgroup_projection subgroup_projection_preserve_equiv.

Lemma subgroup_projection_preserve_e:
    subgroup_projection e == e.
Proof. by []. Qed.

Lemma subgroup_projection_preserve_law:
  forall x y,
    subgroup_projection (x @ y) == 
      subgroup_projection x @ subgroup_projection y.
Proof.
  move => x y;
  enough (H: \hat nth_gen (x @ y) == \hat nth_gen x @ \hat nth_gen y) => [//|].
  by rewrite morphism_preserve_law.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build 
  _ _ subgroup_projection
  subgroup_projection_preserve_e
  subgroup_projection_preserve_law.

Lemma subgroup_projection_surjective:
  forall x: generatedSubgroup, exists w: FreeGroup Sigma,
    subgroup_projection w == x.
Proof.
  move => [x [w Hw]]; by exists w.
Qed.

HB.instance Definition _ := isSurjective.Build 
  _ _ subgroup_projection subgroup_projection_surjective.

End GeneratedSubgroup.
Arguments generatedSubgroup {_}.
Arguments in_generated_subgroup {_}.
Arguments igs_gen {_}.
Arguments subgroup_projection {_} _ / !_.
Arguments nth_gen {_} _ / !_.

Section GeneratedSubgroupIsomorphisms.

Context {G: group}.

(* If two sets of generators are permutations of each other, then
  there is an isomorphism. *)
Section GeneratedSubgroupPermMorphism.
  Variable gens: seq G.
  Variable gens': seq G.
  Variable perm: ordinal (size gens) -> ordinal (size gens').
  Hypothesis Hequiv: forall n, nth_gen gens n == nth_gen gens' (perm n).

  Lemma in_generated_subgroup_perm_morphism (Hperm: bijective perm): forall x,
    in_generated_subgroup gens x ->
    in_generated_subgroup gens' x.
  Proof.
    move => x [w].
    elim: w x => [x /= H|wh wt IH x].
    - by exists e.
    - rewrite hat_cons; case: wh => wh /=.
    -- move/(congruent_left (inv (nth_gen gens wh))).
      rewrite associativity inverse_right neutral_left.
      move/IH => [w Hw]; exists (([word [::Base (perm wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= -Hequiv.
      by rewrite associativity inverse_left neutral_left.
    -- move/(congruent_left (nth_gen gens wh)).
      rewrite associativity inverse_left neutral_left.
      move/IH => [w Hw]; exists (([word [::Inverse (perm wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= -Hequiv.
      by rewrite associativity inverse_right neutral_left.
  Qed.

  Hypothesis Hperm: bijective perm.

  Definition generatedSubgroup_perm_morphism: 
    generatedSubgroup gens ->
    generatedSubgroup gens'.
  Proof.
    move => [] x /(in_generated_subgroup_perm_morphism Hperm) H.
    by exists x.
  Defined.

  Lemma generatedSubgroup_perm_morphism_equiv: forall x y,
    x == y -> generatedSubgroup_perm_morphism x == generatedSubgroup_perm_morphism y.
  Proof. done. Qed.

  HB.instance Definition _ := isSetoidMorphism.Build _ _
    generatedSubgroup_perm_morphism generatedSubgroup_perm_morphism_equiv.

  Lemma generatedSubgroup_perm_morphism_e: generatedSubgroup_perm_morphism e == e.
  Proof.
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  Lemma generatedSubgroup_perm_morphism_law: forall x y,
    generatedSubgroup_perm_morphism (x @ y) ==
    generatedSubgroup_perm_morphism x @ generatedSubgroup_perm_morphism y.
  Proof.
    move => [x Hx] [y Hy].
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  HB.instance Definition _ := isMonoidMorphism.Build _ _
    generatedSubgroup_perm_morphism generatedSubgroup_perm_morphism_e
    generatedSubgroup_perm_morphism_law.

  Lemma generatedSubgroup_perm_morphism_injective: forall x y,
    generatedSubgroup_perm_morphism x == generatedSubgroup_perm_morphism y -> x == y.
  Proof. done. Qed.

  HB.instance Definition _ := isInjective.Build _ _
    generatedSubgroup_perm_morphism generatedSubgroup_perm_morphism_injective.
End GeneratedSubgroupPermMorphism.

Lemma generatedSubgroup_perm_morphism_surjective (gens gens': seq G)
  perm Hequiv Hperm:
    forall y, exists x,
      generatedSubgroup_perm_morphism gens gens' perm Hequiv Hperm x == y.
Proof.
  move/esym: (bij_eq_card Hperm); rewrite !card_ord => E.
  move: (inj_comp (bij_inj Hperm) (@cast_ord_inj _ _ E)) => Hperm_inv.
  set perm_inv := ((cast_ord E) \o (invF Hperm_inv)).
  move => y;
  have: (forall n, nth_gen gens' n == nth_gen gens (perm_inv n)) => [|Hequiv'];
    first by move => n; rewrite /perm_inv /= -{1}(f_invF Hperm_inv n) /= -Hequiv.
  have: bijective perm_inv => [|Hperm'].
  - apply inj_card_bij.
  -- apply inj_comp.
  --- by apply cast_ord_inj.
  --- by apply (can_inj (f_invF Hperm_inv)).
  -- by rewrite E leqnn.
  - exists (generatedSubgroup_perm_morphism gens' gens perm_inv Hequiv' Hperm' y).
    by rewrite /(_ == _) /= /subgroupby_eq /=.
Qed.
HB.instance Definition _ (gens gens': seq G) perm Hequiv Hperm := isSurjective.Build _ _
  (generatedSubgroup_perm_morphism gens gens' perm Hequiv Hperm)
  (generatedSubgroup_perm_morphism_surjective gens gens' perm Hequiv Hperm).

(* The map x |-> inv x is an isomorphism *)
Section GeneratedSubgroupInvMorphism.
  Variable gens: seq G.
  Let inv_gens := [seq inv g | g <- gens].

  Lemma in_generated_subgroup_inv_morphism: forall x,
    in_generated_subgroup gens x ->
    in_generated_subgroup inv_gens x.
  Proof.
    move/esym: (size_map inv gens) => E.
    move => x [w].
    elim: w x => [x /= H|wh wt IH x].
    - by exists e.
    - rewrite hat_cons; case: wh => wh /=.
    -- move/(congruent_left (inv (nth_gen gens wh))).
      rewrite associativity inverse_right neutral_left.
      move/IH => [w Hw]; exists (([word [::Inverse (cast_ord E wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= (nth_map e) => [|//].
      by rewrite inv_involutive associativity inverse_left neutral_left.
    -- move/(congruent_left (nth_gen gens wh)).
      rewrite associativity inverse_left neutral_left.
      move/IH => [w Hw]; exists (([word [::Base (cast_ord E wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= (nth_map e) => [|//].
      by rewrite associativity inverse_right neutral_left.
  Qed.

  Definition generatedSubgroup_inv_morphism: 
    generatedSubgroup gens ->
    generatedSubgroup inv_gens.
  Proof.
    move => [] x /in_generated_subgroup_inv_morphism H.
    by exists x.
  Defined.

  Lemma generatedSubgroup_inv_morphism_equiv: forall x y,
    x == y -> generatedSubgroup_inv_morphism x == generatedSubgroup_inv_morphism y.
  Proof. done. Qed.

  HB.instance Definition _ := isSetoidMorphism.Build _ _
    generatedSubgroup_inv_morphism generatedSubgroup_inv_morphism_equiv.

  Lemma generatedSubgroup_inv_morphism_e: generatedSubgroup_inv_morphism e == e.
  Proof.
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  Lemma generatedSubgroup_inv_morphism_law: forall x y,
    generatedSubgroup_inv_morphism (x @ y) ==
    generatedSubgroup_inv_morphism x @ generatedSubgroup_inv_morphism y.
  Proof.
    move => [x Hx] [y Hy].
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  HB.instance Definition _ := isMonoidMorphism.Build _ _
    generatedSubgroup_inv_morphism generatedSubgroup_inv_morphism_e
    generatedSubgroup_inv_morphism_law.

  Lemma generatedSubgroup_inv_morphism_injective: forall x y,
    generatedSubgroup_inv_morphism x == generatedSubgroup_inv_morphism y -> x == y.
  Proof. done. Qed.

  HB.instance Definition _ := isInjective.Build _ _
    generatedSubgroup_inv_morphism generatedSubgroup_inv_morphism_injective.
End GeneratedSubgroupInvMorphism.

Lemma generatedSubgroup_inv_morphism_surjective (gens: seq G):
  forall y, exists x, generatedSubgroup_inv_morphism gens x == y.
Proof.
  move => y.
  set gens_inv_inv := map inv (map inv gens).
  have: size gens_inv_inv = size gens => [|Hsize];
    first by rewrite /gens_inv_inv !size_map.
  have: (forall n, nth_gen gens_inv_inv n == nth_gen gens (cast_ord Hsize n)) => [n|Hequiv].
  - rewrite /gens_inv_inv; rewrite /nth_gen !(nth_map e) => [|//|].
  -- by rewrite inv_involutive.
  -- by rewrite -Hsize.
  -- by rewrite (size_map inv gens) -Hsize.
  have: (bijective (cast_ord Hsize)) => [|Hperm].
  - apply inj_card_bij.
  -- by apply cast_ord_inj.
  -- by rewrite Hsize leqnn.
  - exists (generatedSubgroup_perm_morphism gens_inv_inv gens (cast_ord Hsize) Hequiv Hperm
      (generatedSubgroup_inv_morphism [seq inv g | g <- gens] y)).
  by rewrite /(_ == _) /= /subgroupby_eq /=.
Qed.

HB.instance Definition _ gens := isSurjective.Build _ _
  (generatedSubgroup_inv_morphism gens)
  (generatedSubgroup_inv_morphism_surjective gens).

(* Adding a generator induces an isomorphism. *)
Section GeneratedSubgroupRconsMorphism.
  Variable gens: seq G.
  Variable g: G.
  Let rcons_gens := rcons gens g.

  Lemma in_generated_subgroup_rcons_morphism (Hg: in_generated_subgroup gens g): forall x,
    in_generated_subgroup gens x ->
    in_generated_subgroup rcons_gens x.
  Proof.
    have: (size gens <= size rcons_gens)%N = true => [|E];
      first by rewrite size_rcons leqnSn.
    move => x [w].
    elim: w x => [x /= H|wh wt IH x].
    - by exists e.
    - rewrite hat_cons; case: wh => wh /=.
    -- move/(congruent_left (inv (nth_gen gens wh))).
      rewrite associativity inverse_right neutral_left.
      move/IH => [w Hw]; exists (([word [::Base (widen_ord E wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= nth_rcons.
      case: wh Hw => m H Hw /=; rewrite H.
      by rewrite associativity inverse_left neutral_left.
    -- move/(congruent_left (nth_gen gens wh)).
      rewrite associativity inverse_left neutral_left.
      move/IH => [w Hw]; exists (([word [::Inverse (widen_ord E wh)]]_(FGP _)) @ w).
      rewrite hat_cons Hw /= nth_rcons.
      case: wh Hw => m H Hw /=; rewrite H.
      by rewrite associativity inverse_right neutral_left.
  Qed.

  Hypothesis Hg: in_generated_subgroup gens g.

  Definition generatedSubgroup_rcons_morphism: 
    generatedSubgroup gens ->
    generatedSubgroup rcons_gens.
  Proof.
    move => [] x /(in_generated_subgroup_rcons_morphism Hg) H.
    by exists x.
  Defined.

  Lemma generatedSubgroup_rcons_morphism_equiv: forall x y,
    x == y -> generatedSubgroup_rcons_morphism x == generatedSubgroup_rcons_morphism y.
  Proof. done. Qed.

  HB.instance Definition _ := isSetoidMorphism.Build _ _
    generatedSubgroup_rcons_morphism generatedSubgroup_rcons_morphism_equiv.

  Lemma generatedSubgroup_rcons_morphism_e: generatedSubgroup_rcons_morphism e == e.
  Proof.
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  Lemma generatedSubgroup_rcons_morphism_law: forall x y,
    generatedSubgroup_rcons_morphism (x @ y) ==
    generatedSubgroup_rcons_morphism x @ generatedSubgroup_rcons_morphism y.
  Proof.
    move => [x Hx] [y Hy].
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  HB.instance Definition _ := isMonoidMorphism.Build _ _
    generatedSubgroup_rcons_morphism generatedSubgroup_rcons_morphism_e
    generatedSubgroup_rcons_morphism_law.

  Lemma generatedSubgroup_rcons_morphism_injective: forall x y,
    generatedSubgroup_rcons_morphism x == generatedSubgroup_rcons_morphism y -> x == y.
  Proof. done. Qed.

  HB.instance Definition _ := isInjective.Build _ _
    generatedSubgroup_rcons_morphism generatedSubgroup_rcons_morphism_injective.


  Lemma in_generated_subgroup_rcons_morphism': forall x,
    in_generated_subgroup rcons_gens x ->
    in_generated_subgroup gens x.
  Proof.
    have: (size gens <= size rcons_gens)%N = true => [|E];
      first by rewrite size_rcons leqnSn.
    move => x [w].
    elim: w x => [x /= H|wh wt IH x].
    - by exists e.
    - rewrite hat_cons; case: wh => wh /=.
    -- move/(congruent_left (inv (nth_gen rcons_gens wh))).
       rewrite associativity inverse_right neutral_left.
       move/IH => [w Hw]; case H: (wh < size gens)%N.
    --- exists (([word [::Base (Ordinal H)]]_(FGP _)) @ w).
        rewrite hat_cons Hw /= /nth_gen nth_rcons H.
        by rewrite associativity inverse_left neutral_left.
    --- move: Hg => [wg Hwg]; exists (wg @ w).
        rewrite morphism_preserve_law /= Hw Hwg /nth_gen nth_rcons H.
        case: wh {Hw} H => /= n; rewrite size_rcons => Hn Hn'.
        have: (n == size gens)%B => [|->]; first by lia.
        by rewrite associativity inverse_left neutral_left.
    -- move/(congruent_left (nth_gen rcons_gens wh)).
       rewrite associativity inverse_left neutral_left.
       move/IH => [w Hw]; case H: (wh < size gens)%N.
    --- exists (([word [::Inverse (Ordinal H)]]_(FGP _)) @ w).
        rewrite hat_cons Hw /= /nth_gen nth_rcons H.
        by rewrite associativity inverse_right neutral_left.
    --- move: Hg => [wg Hwg]; exists ((inv wg) @ w).
        rewrite morphism_preserve_law -morphism_preserve_inv /= Hw Hwg /nth_gen nth_rcons H.
        case: wh {Hw} H => /= n; rewrite size_rcons => Hn Hn'.
        have: (n == size gens)%B => [|->]; first by lia.
        by rewrite associativity inverse_right neutral_left.
  Qed.

  Definition generatedSubgroup_rcons_morphism': 
    generatedSubgroup rcons_gens ->
    generatedSubgroup gens.
  Proof.
    move => [] x /in_generated_subgroup_rcons_morphism' H.
    by exists x.
  Defined.

  Lemma generatedSubgroup_rcons_morphism_equiv': forall x y,
    x == y -> generatedSubgroup_rcons_morphism' x == generatedSubgroup_rcons_morphism' y.
  Proof. done. Qed.

  Lemma generatedSubgroup_rcons_morphism_right_inverse: forall x,
    generatedSubgroup_rcons_morphism (generatedSubgroup_rcons_morphism' x) == x.
  Proof.
    move => [x Hx].
    by rewrite /(_ == _) /= /subgroupby_eq /=.
  Qed.

  Lemma generatedSubgroup_rcons_morphism_surjective: forall y, exists x,
    generatedSubgroup_rcons_morphism x == y.
  Proof.
    move => y; exists (generatedSubgroup_rcons_morphism' y).
    by apply generatedSubgroup_rcons_morphism_right_inverse.
  Qed.

  HB.instance Definition _ := isSurjective.Build _ _
    generatedSubgroup_rcons_morphism generatedSubgroup_rcons_morphism_surjective.

  HB.instance Definition _ := isIsomorphismRightInverse.Build _ _
    generatedSubgroup_rcons_morphism generatedSubgroup_rcons_morphism'
    generatedSubgroup_rcons_morphism_equiv'
    generatedSubgroup_rcons_morphism_right_inverse.
End GeneratedSubgroupRconsMorphism.
End GeneratedSubgroupIsomorphisms.
Arguments generatedSubgroup_perm_morphism {_}.
Arguments generatedSubgroup_inv_morphism {_}.
Arguments generatedSubgroup_rcons_morphism {_}.
Arguments generatedSubgroup_rcons_morphism' {_}.
