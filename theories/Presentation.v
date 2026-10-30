From HB Require Import structures.
Require Import RelationClasses Setoid Morphisms.
Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype choice ssrnat.
From mathcomp Require Import ssrint ring lra zify all_algebra.

From GWP Require Import Equivalence EquivalenceAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import EquivalenceAlgebra.SetoidGroupNotations.

Local Open Scope setoid_group_scope.

(* an bidirectional rewriting rule u -> v and v -> u *)
Definition relation (Sigma: Type) :=
  ((seq Sigma) * (seq Sigma)) % type.

(* NOTE(reiniscirpons): Instead of using hierarchy builder to
   define a presentation, we instead define it using a
   Structure like its done in MonoidPresentation.
   I think this is mathematically cleaner, and we 
   can now have the same alphabet used for different
   presentations. *)
(* NOTE(reiniscirpons): We only consider finitely presented monoids
   and groups, so the finType restriction is ok. *)
Structure presentation := Presentation {
  sigma: finType;
  relations: seq (relation sigma);
}.

Section WordProblem.

Variable P: presentation.
Definition word := (seq (sigma P)).
Implicit Types (r: relation (sigma P)) (u v w a c: word).

(* `Derivation u v` is the type of witnesses of derivations from
  `u: word` to `v: word` in `P: Presentation` *)
Inductive Derivation : word -> word -> Prop :=
  | Derivation_reduction r a c:
    r \in relations P ->
    Derivation ((a ++ r.1) ++ c) ((a ++ r.2) ++ c)
  | Derivation_refl u:
    Derivation u u
  | Derivation_symm u v:
    Derivation u v ->
    Derivation v u
  | Derivation_trans u v w:
      Derivation u v ->
      Derivation v w ->
      Derivation u w.

(* The word problem of the presentation `P`. *)
Definition word_problem (u v: word) : Prop := Derivation u v.
End WordProblem.

(* `presented P` is the structure associated to the presentation `P := (Sigma; R)`.
   ie. `presented P` is Sigma^* quotiented by the smallest equivalence relation compatible with R *)
Definition presented (P: presentation): Type := (seq (sigma P)).

(* TODO: Is the canonical projection stuff ok? *)
Section InstancesFromList.
Variable P: presentation.
HB.instance Definition _ :=
  Equality.copy (presented P) (seq (sigma P)).
HB.instance Definition _ :=
  Choice.copy (presented P) (seq (sigma P)).
End InstancesFromList.

(* In a presented monoid, equality coincides with existence
   of derivations. *)
Section PresentedEquiv.
Variable P: presentation.
Implicit Types (x y z: presented P).

Lemma wp_refl : forall x,
  word_problem x x.
Proof.
  by exact: Derivation_refl.
Qed.

Lemma wp_symm : forall x y,
  word_problem x y ->
  word_problem y x.
Proof.
  by exact: Derivation_symm.
Qed.

Lemma wp_trans : forall x y z,
  word_problem x y ->
  word_problem y z ->
  word_problem x z.
Proof.
  by exact: Derivation_trans.
Qed.

(* HB bug: having a duplicate (P: presentation) results in a Ocaml assertion failure *)
HB.instance Definition _ := @hasEquiv.Build
  (presented P) (@word_problem P)
  wp_refl wp_symm wp_trans.
End PresentedEquiv.

(* All presented structures have a monoid structure *)
Section PresentedMonoid.

Variable P: presentation.
Implicit Types (x y z a u v: presented P).


Fact pm_mulsA : forall x y z,
  x ++ (y ++ z) \approx (x ++ y) ++ z :> presented P.
Proof.
  by move => x y z; rewrite catA.
Qed.

Fact pm_mul1s : forall x,
  [::] ++ x \approx x :> presented P.
Proof.
  by move => x; rewrite cat0s.
Qed.

Fact pm_muls1 : forall x,
  x ++ [::] \approx x :> presented P.
Proof.
  by move => x; rewrite cats0.
Qed.

Let pm_muls_extl: forall a u v,
  u \approx v ->
  a ++ u \approx a ++ v :> presented P.
Proof.
  move=> a u v; elim => [r b c Hr|//||u' v'].
  - rewrite !catA.
    by apply Derivation_reduction.
  - by symmetry.
  - by transitivity (a ++ v').
Qed.

Let pm_muls_extr: forall a u v,
  u \approx v ->
  u ++ a \approx v ++ a :> presented P.
Proof.
  move=> a u v; elim => [r b c Hr|//||u' v'].
  - rewrite -catA -[(_ ++ _) ++ a]catA.
    by apply Derivation_reduction.
  - by symmetry.
  - by transitivity (v' ++ a).
Qed.

HB.instance Definition _ := isSetoidMonoid.Build (presented P)
  pm_mulsA pm_mul1s pm_muls1 pm_muls_extl pm_muls_extr.
End PresentedMonoid.

Lemma red1E {P: presentation}: forall (a b u v: presented P),
  (u, v) \in relations P ->
  a * u * b \approx a * v * b.
Proof. 
  move=> a b u v H.
  by apply Derivation_reduction with (r := (u, v)).
Qed.

#[deprecated(since="2026-10-29", note="Use red1E instead.")]
Notation morphism_preserve_power_pos := red1E.

Lemma red1rel {P: presentation}: forall (u v: presented P),
  (u, v) \in relations P ->
  u \approx v.
Proof.
  move => u v H.
  have H1: (forall (x: presented P), x \approx 1 * x * 1);
    first by move => x; rewrite muls1 mul1s.
  rewrite [u]H1 [v]H1.
  by apply red1E.
Qed.

#[deprecated(since="2026-10-29", note="Use red1rel instead.")]
Notation reduction_rule := red1rel.

Module PresentationNotations.

Notation "\epsilon" := ([::] : presented _)
  (at level 10): setoid_group_scope.
Notation "'\epsilon_' P" := ([::] : presented P)
  (at level 10): setoid_group_scope.
Notation "'[word' x ']'" := ([:: x] : presented _)
  (at level 10, format "[word  x ]"): setoid_group_scope.
Notation "'[word' x ']_' P" := ([:: x] : presented P)
  (at level 10, format "[word  x ]_ P").
Notation "'[word' x ; y ; .. ; z ']'" :=
  ((x :: (cons y .. [:: z] ..)) : presented _)
  (at level 10,
  format "[word  '[' x ; '/' y ; '/' .. ; '/' z ']' ]")
  :setoid_group_scope.
Notation "'[word' x ; y ; .. ; z ']_' P" :=
  ((x :: (cons y .. [:: z] ..)) : presented P)
  (at level 10,
  format "[word  '[' x ; '/' y ; '/' .. ; '/' z ']' ]_ P")
  :setoid_group_scope.
Notation "'[word' x ']_' P" := ([:: x] : presented P)
  (at level 10, format "[word  x ]_ P").
Notation "x %% P" := (x : presented P)
  (at level 40).
Notation "x '\approx' y '%[mod' P ']'" :=
  (x \approx y :> presented P)
  (at level 70, only parsing): setoid_group_scope.
Notation "x '≈' y '%[mod' P ']'" :=
  (x \approx y %[mod P])
  (at level 70,
    only printing,
    format "x  ≈  y %[mod  P ]"): setoid_group_scope.

#[deprecated(since="2026-10-29", note="Use \epsilon_ instead.")]
Notation "`[ ]_ P" := ([::] : presented P)
  (at level 10, format "`[  ]_ P").
#[deprecated(
  since="2026-10-29",
  note="Use [word x]_P instead.")]
Notation "`[ x ]_ P" := ([word x]_P)
  (at level 10, format "`[ x ]_ P").
#[deprecated(
  since="2026-10-29",
  note="Use [word x; y; ... ; z]_P instead.")]
Notation "`[ x ; y ; .. ; z ]_ P" :=
  ((x :: (cons y .. [:: z] ..)) : presented P)
  (format "`[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]_ P").
#[deprecated(
  since="2026-10-29",
  note="Use x %% P instead.")]
Notation "x \mod P" := (x : presented P)
  (at level 10, format "x  \mod  P").

End PresentationNotations.

Import PresentationNotations.

(* NOTE(reiniscirpons): Declaring cat and cons to multiplication
   law conversions to simplify future lemmas. *)
(* TODO(reiniscirpons: Do we still need this?) *)
Lemma catmulE: forall P (x y: presented P),
    x ++ y %% P = x * y.
Proof. by done. Qed.

#[deprecated(since="2026-10-29", note="Use catmulE instead.")]
Notation cat_law := catmulE.

Lemma consmulE: forall P (a: sigma P) (x: presented P),
    (a::x) %% P = [word a] * x.
Proof. by []. Qed.

#[deprecated(since="2026-10-29", note="Use consmulE instead.")]
Notation cons_law := consmulE.

Lemma rconsmulE: forall P (a: sigma P) (x: presented P),
    (rcons x a) %% P = x * [word a].
Proof. 
  move => P a;
  by elim => [//|b w /= ->].
Qed.

#[deprecated(since="2026-10-29", note="Use rconsmulE instead.")]
Notation rcons_law := rconsmulE.

(* Show that preserving relations and multiplication is enough to define
   monoid morphism out of presented monoid. *)
(* TODO(reiniscirpons): How can reuse the IsMonoidMorphism axioms here? *)
HB.factory Record isRelationPreservingMorphism
  (P: presentation) (B: setoidMonoidType) (f: presented P -> B)
    (* TODO(reiniscirpons): Why does this caause a bug?*)
    (* & isMonoidMorphism (presented P) B f*)
    := {
  relsfM: forall u v,
    (u, v) \in relations P ->
    f u \approx f v;
  onefM: f 1 \approx 1;
  mulfM: forall x y,
    f (x * y) \approx (f x) * (f y);
}.

HB.builders Context (P: presentation) (M: monoid) f of 
  isRelationPreservingMorphism P M f.

  Fact f_equivfM: forall x y,
    x \approx y ->
    f x \approx f y.
  Proof.
    move => x y; elim => [[u v] p s |//||] /=.
    - move/relsfM => H.
      by rewrite !mulfM H.
    - move => u v _ H;
      by symmetry.
    - move => u v w _ H1 _ H2;
      by transitivity (f v).
  Qed.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ f f_equivfM.
  
  HB.instance Definition _ :=
    isMonoidMorphism.Build _ _ f onefM mulfM.
HB.end.

(* Some induction principles for presented monoids *)
Lemma pres_ind: forall (P: presentation)
  (p: presented P -> Prop),
  p (\epsilon) ->
  (forall (a: sigma P) (x: presented P),
    p x -> p ([word a] * x)) ->
  forall (x: presented P), p x.
Proof.
  move => P p Hnil Hcons.
  by elim => [//|a x /(Hcons a) //].
Qed.

Lemma pres_last_ind: forall (P: presentation)
  (p: presented P -> Prop),
  p (\epsilon) ->
  (forall (a: sigma P) (x: presented P),
    p x -> p (x * [word a])) ->
  forall (x: presented P), p x.
Proof.
  move => P p Hnil Hrcons.
  elim/last_ind => [//|x a /(Hrcons a)].
  by rewrite rconsmulE.
Qed.

Definition cat_ind: forall (T: Type) (P: seq T -> Prop),
  P [::] ->
  (forall a, P [:: a]) ->
  (forall x y, P x -> P y -> P (x ++ y)) ->
  forall x, P x :=
  fun T P Hnil Hcons1 Hcat =>
    fix f x :=
      match x with
      | [::] => Hnil
      | a::x' => Hcat [::a] x' (Hcons1 a) (f x')
      end.

Lemma pres_cat_ind: forall (P: presentation)
  (p: presented P -> Prop),
  p (\epsilon) ->
  (forall (a: sigma P), p ([word a])) ->
  (forall (x y: presented P),
    p x -> p y -> p (x * y)) ->
  forall (x: presented P), p x.
Proof.
  move => P p Hnil Hcons1 Hcat.
  by elim/cat_ind.
Qed.

Section ExtensionToMonoidMorphism.

Variable P: presentation.
Variable M: setoidMonoidType.
Variable f: sigma P -> M.

Definition extension: presented P -> M :=
  fun l => prod [seq f x | x <- l].
Arguments extension / !_.

Lemma extension_cons:
  forall (a: sigma P) (w: presented P),
  extension (a::w) = (f a) * (extension w).
Proof. done. Qed.

Lemma extension_universality:
  forall (varphi: morphism (presented P) M),
    (forall a: sigma P,
      varphi ([word a]) \approx f a) -> 
    (forall w: presented P, 
      varphi w \approx extension w).
Proof.
  move => varphi Heq; elim/pres_ind => [|a w' IH].
  - by exact onefM.
  by rewrite mulfM extension_cons Heq IH.
Qed.

Lemma extension_onefM: extension 1 \approx 1.
Proof. done. Qed.

Lemma extension_mulfM: forall (x y: presented P),
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
    extension_onefM
    extension_mulfM.

End ExtensionToMonoidMorphism.
Arguments extension {_ _} _ / !_. 
#[deprecated(since="2026-10-29", note="Use extension_onefM instead.")]
Notation extension_preserve_e := extension_onefM.
#[deprecated(since="2026-10-29", note="Use extension_mulfM instead.")]
Notation extension_preserve_law := extension_mulfM.


HB.mixin Record hasInvertibleLetters (P: presentation) := {
  invol:
    sigma P -> sigma P;
  involsK:
    forall c, invol (invol c) = c;
  involsV: forall c,
    [word c] * [word invol c] \approx 1;
  involVs: forall c,
    [word invol c] * [word c] \approx 1;
}.
#[short(type="invertiblePresentationType")]
HB.structure Definition InvertiblePresentation :=
  { P & hasInvertibleLetters P }.

(*TODO: move all notations at end*)
Notation "a ^~1" := (invol a).

#[deprecated(since="2026-10-29", note="Use a^~1 instead.")]
Notation invl := invol.
#[deprecated(since="2026-10-29", note="Use involsK instead.")]
Notation invlK := involsK.
#[deprecated(since="2026-10-29", note="Use involsW instead.")]
Notation invl_left := involsV.
#[deprecated(since="2026-10-29", note="Use involVs instead.")]
Notation invl_right := involVs.

Lemma invol_inj: forall (P: invertiblePresentationType),
  injective (@invol P).
Proof.
  move => P x y H.
  by rewrite -(involsK x) -(involsK y) H.
Qed.

#[deprecated(since="2026-10-29", note="Use invol_inj instead.")]
Notation invl_inj := invol_inj.

Section InvertiblePresentedGroup.

Variable P: invertiblePresentationType.
Implicit Types (w x y: presented P) (a c: sigma P).

Definition word_inv w : presented P :=
  [seq invol c | c <- (rev w)].

Lemma word_invsM : forall x y,
  word_inv (x * y) \approx (word_inv y) * (word_inv x).
Proof.
  move=> x y.
  by rewrite /word_inv /= -catmulE rev_cat map_cat.
Qed.

Lemma word_mulsV : forall w,
  w * (word_inv w) \approx 1.
Proof.
  elim/pres_ind => [|a x IH];
    first by rewrite mul1s.
  rewrite word_invsM mulsA -[_ * x * _]mulsA IH muls1.
  by rewrite /word_inv /= involsV.
Qed.

Lemma word_mulVs : forall w,
  (word_inv w) * w \approx 1.
Proof.
  elim/pres_last_ind => [|a x IH];
    first by rewrite mul1s.
  rewrite word_invsM mulsA -[_ * _ * x]mulsA IH muls1.
  by rewrite /word_inv /= involVs.
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
(* TODO: do we even need these anymore? I now think this was just
   a skill issue on my part. *)
Lemma word_inv_cons:
  forall w a, word_inv (a::w) = (word_inv w) ++ [:: invol a].
Proof.
  by move => w a; rewrite /word_inv rev_cons map_rcons cats1.
Qed.

Lemma word_inv_rcons:
  forall w a, word_inv (rcons w a) = invol a :: word_inv w.
Proof.
  by move => w a; rewrite /word_inv rev_rcons.
Qed.

Lemma word_inv_cat:
  forall x y, word_inv (x ++ y) = word_inv y ++ word_inv x.
Proof.
  by move => x y; rewrite /word_inv !map_rev map_cat rev_cat.
Qed.

Lemma word_invK:
  forall x, word_inv (word_inv x) = x.
Proof.
  move => x; rewrite /word_inv !map_rev revK -map_comp.
  elim: x => [//|hx tx IH].
  by rewrite /= IH involsK.
Qed.

HB.instance Definition _ := isSetoidGroup.Build
  (presented P) word_invsM word_mulsV word_mulVs.

(* TODO: This might be in the wrong place? Really these are
   lemmas about the free monoid and are only loosely
   related to inversion and not related to presentations at
   all! *)
Lemma exps_word_inv' w (x: nat):
  w ^ (- (x: int)) = word_inv (w ^ x).
Proof.
  elim/nat_pairs_ind: x => [//||n IH1 IH2].
  - by rewrite expsP expsS exps0 -!catmulE !cats0.
  - rewrite expsP expsS IH2 {1}expsS.
    rewrite word_inv_cat word_inv_cat.
    by rewrite -IH2 expsP IH1 -catA.
Qed.

Lemma exps_word_inv w (x: int):
  w ^ (- x) = word_inv (w ^ x).
Proof.
  case: x => n; first by exact: exps_word_inv'.
  by rewrite NegzE exps_word_inv' word_invK. 
Qed.

Lemma exps_catC' w (x: nat):
  w ^ x ++ w = w ++ w ^ x.
Proof.
  elim/nat_pairs_ind: x => [||n IH1 IH2].
  - by rewrite exps0 /= cats0.
  - by rewrite !expsS exps0 -!catmulE cats0.
  - by rewrite expsS -catmulE -{2}IH2 catA.
Qed.

Lemma exps_catC'' w (x: nat):
  w ^ (- (x:int)) ++ w^-1 = w^-1 ++ w ^ (- (x: int)).
Proof.
  elim/nat_pairs_ind: x => [||n IH1 IH2].
  - by rewrite exps0 /= cats0.
  - by rewrite !expsP exps0 -!catmulE cats0.
  - by rewrite expsP -catmulE -{2}IH2 catA.
Qed.

Lemma exps_seq1 w:
  w ^ 1 = w.
Proof.
  by rewrite expsS exps0 -catmulE cats0.
Qed.
Lemma invs_cons1 (c: sigma P):
  ([word c])^-1 = [word c^~1].
Proof. done. Qed.

Lemma exps_rev1 c (x: int):
  rev ([word c] ^ x) = [word c] ^ x.
Proof.
  elim: x => [//||] n IH.
  - by rewrite expsS rev_cat -!catmulE -exps_catC' IH.
  - by rewrite expsP rev_cat -!catmulE -exps_catC'' IH.
Qed.

Lemma size_expsN0 c (x: int):
  x != 0 -> (size ([word c] ^ x) > 0).
Proof.
  case: (intP x) => [//|n|n].
  - by rewrite expsS -catmulE size_cat /=.
  - by rewrite expsP -catmulE size_cat /=.
Qed.

Lemma size_expcn c (x: int):
  size ([word c] ^ x) = absz x.
Proof.
  case x => n; elim n => [//|n0 IH].
  - by rewrite expsS -catmulE size_cat /= IH.
  - rewrite expsP /=.
    rewrite /= in IH.
    by rewrite IH.
Qed.

    
End InvertiblePresentedGroup.

#[deprecated(since="2026-10-29", note="Use word_inv instead.")]
Notation inv_word := word_inv.
#[deprecated(since="2026-10-29", note="Use word_invsM instead.")]
Notation inv_word_law := word_invsM.
#[deprecated(since="2026-10-29", note="Use word_mulsV instead.")]
Notation inv_word_left := word_mulsV.
#[deprecated(since="2026-10-29", note="Use word_mulVs instead.")]
Notation inv_word_right := word_mulVs.
#[deprecated(
  since="2026-10-29",
  note="Use word_inv_cons instead, or remove it?")]
Notation inv_word_cons := word_inv_cons.
#[deprecated(
  since="2026-10-29",
  note="Use word_inv_rcons instead, or remove it?")]
Notation inv_word_rcons := word_inv_rcons.
#[deprecated(
  since="2026-10-29",
  note="Use word_inv_cat instead, or remove it?")]
Notation inv_word_cat := word_inv_cat.
#[deprecated(
  since="2026-10-29",
  note="Use word_invK instead, or remove it?")]
Notation inv_word_involutive := word_invK.
#[deprecated(
  since="2026-10-29",
  note="Use exps_word_inv' instead, or remove it?")]
Notation power_inv_word' := exps_word_inv'.
#[deprecated(
  since="2026-10-29",
  note="Use exps_word_inv instead, or remove it?")]
Notation power_inv_word := exps_word_inv.
#[deprecated(
  since="2026-10-29",
  note="Use exps_catC' instead, or remove it?")]
Notation FreeGroup_powerC' := exps_catC'.
#[deprecated(
  since="2026-10-29",
  note="Use exps_catC'' instead, or remove it?")]
Notation FreeGroup_powerC'' := exps_catC''.
#[deprecated(
  since="2026-10-29",
  note="Use exps_seq1 instead, or remove it?")]
Notation FreeGroup_power1 := exps_seq1.
#[deprecated(
  since="2026-10-29",
  note="Use inv_cons1 instead, or remove it?")]
Notation FreeGroup_inv1 := invs_cons1.
#[deprecated(
  since="2026-10-29",
  note="Use exps_rev1 instead, or remove it?")]
Notation power_rev1 := exps_rev1.
#[deprecated(
  since="2026-10-29",
  note="Use size_expsN0 instead, or remove it?")]
Notation size0_power := size_expsN0.
#[deprecated(
  since="2026-10-29",
  note="Use size_expsN0 instead, or remove it?")]
Notation size_power := size_expcn.


Section Cancellation.

Variable P: invertiblePresentationType.
Implicit Types (a x y : presented P).

Lemma cancel_left: forall a x y,
  a * x \approx a * y ->
  x \approx y.
Proof.
  move=> a x y H.
  rewrite -(mul1s x) -(mul1s y) -(mulVs a) -!mulsA.
  by rewrite H.
Qed.

Lemma cancel_right: forall a x y,
  x * a \approx y * a ->
  x \approx y.
Proof.
  move=> a x y H.
  rewrite -(muls1 x) -(muls1 y) -(mulsV a) !mulsA.
  by rewrite H.
Qed.

End Cancellation.
Arguments cancel_left {_}.
Arguments cancel_right {_}.
