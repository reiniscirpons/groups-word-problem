From HB Require Import structures.
Require Import RelationClasses.
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrint ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype choice
  ssrnat ssrint ring lra zify all_algebra.
Import GRing.Theory.

From GWP Require Import Equivalence EquivalenceAlgebra.


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
Local Infix "@" := cat (at level 50).

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
      Derivation (a @ (initialWord r) @ c) (a @ (finalWord r) @ c)
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
HB.instance Definition _ := Countable.copy (presented P) (seq (sigma P)).

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
HB.instance Definition _ := @hasEq.Build M eq M_refl M_symm M_trans.
End PresentedEq.

(* All presented structures have a monoid structure *)
Section PresentedMonoid.

Variable P: presentation.

Local Notation M := (presented P).

Let concat := @cat (sigma P).
Let epsilon : seq (sigma P) := nil.

Infix ".@" := (concat: M -> M -> M) (at level 50).

Let associativity : forall (x y z : M), x .@ (y .@ z) == (x .@ y) .@ z.
Proof. by move=> x y w; rewrite /concat catA. Qed.
Let neutral_left : forall (x: M), epsilon .@ x == x.
Proof. by move=> x; rewrite /concat /=. Qed.
Let neutral_right : forall (x: M), x .@ epsilon == x.
Proof. by move=> x; rewrite /concat cats0. Qed.

Let congruent_left: forall (a u v: M),
  u == v -> a .@ u == a .@ v.
Proof.
move=> a u v; elim => [|//||].
- move=> r c b H.
  rewrite /concat -!(catA c) !(catA a) !(catA (a ++ c)).
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- by symmetry.
- by move=> ? v'; transitivity (a .@ v').
Qed.

Let congruent_right: forall (b u v: M),
  u == v -> u .@ b == v .@ b.
Proof.
move=> b u v; elim => [|//||].
- move=> r a c H.
  rewrite /concat -!(catA a) -!(catA _ _ b) !(catA a).
  apply: (Derivation_reduction _ (r.1, r.2)).
  by move: H; case r.
- by symmetry.
- by move=> ? a; transitivity (a .@ b).
Qed.

HB.instance Definition _ := isMonoid.Build M concat epsilon associativity neutral_left neutral_right congruent_left congruent_right.
End PresentedMonoid.

Lemma reduction {P: presentation}:
  forall (a b u v: presented P),
  (u, v) \in relations P -> a @ u @ b == a @ v @ b.
Proof. by move=> a b u v H; apply: (Derivation_reduction _ (u, v)); done. Qed.

Lemma reduction_rule {P: presentation}:
  forall (u v: presented P),
  (u, v) \in relations P -> u == v.
Proof.
move=> u v Hin.
transitivity (e @ u @ e).
  by symmetry; apply: neutral_right.
transitivity (e @ v @ e); last first.
  by apply: neutral_right.
exact: (reduction e e).
Qed.


Module PresentationNotations.
Notation "`[ ]_ P" := ([::] : presented P)
  (at level 10, format "`[  ]_ P").
Notation "`[ x ]_ P" := ([:: x] : presented P)
  (at level 10, format "`[ x ]_ P").
Notation "`[ x ; y ; .. ; z ]_ P" :=
  ((x :: (cons y .. [:: z] ..)) : presented P)
  (format "`[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]_ P").
Notation "x \mod P" := (x : presented P)
  (at level 10, format "x  \mod  P").
End PresentationNotations.

Import PresentationNotations.

(* NOTE(reiniscirpons): Declaring cat and cons to multiplication
   law conversions to simplify future lemmas. *)
Lemma cat_law: forall P (x y: presented P),
    (x ++ y: presented P) = x @ y.
Proof. by []. Qed.

Lemma cons_law: forall P (a: sigma P) (x: presented P),
    (a :: x: presented P) = `[a]_P @ x.
Proof. by []. Qed.

Lemma rcons_law: forall P (a: sigma P) (x: presented P),
    (rcons x a: presented P) = x @ `[a]_P.
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
      forall u v, (u, v) \in relations P -> f u == f v;
    morphism_preserve_e:
      f e == e;
    morphism_preserve_law:
      forall x y, f (x @ y) == (f x) @ (f y);
}.

HB.builders Context (P: presentation) (M: monoid) f of 
  isRelationPreservingMorphism P M f.

  Fact f_preserve_equiv: forall x y, x == y -> f x == f y.
  Proof.
    move => x y; elim => [[u v] p s |//||] /=.
    - move/morphism_preserve_relations => H.
      by rewrite !morphism_preserve_law H.
    - move => u v _ H; by apply symm.
    - move => u v w _ H1 _ H2; by apply trans with (f v).
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
  extension (a::w) = (f a) @ (extension w).
Proof. done. Qed.

Lemma extension_universality:
  forall (varphi: morphism (presented P) M),
    (forall a: sigma P, varphi (`[a]_P) == f a) -> 
    (forall w: presented P, 
      varphi w == extension w).
Proof.
  move => varphi Heq; elim => [|a w' IH].
  - exact morphism_preserve_e.
  by rewrite {1}cons_law morphism_preserve_law extension_cons IH Heq.
Qed.

Lemma extension_preserve_e: extension e == e.
Proof. done. Qed.

Lemma extension_preserve_1: forall (c: sigma P), extension (`[c]_P) == f c.
Proof.
  by move => c /=; rewrite neutral_right.
Qed.

Lemma extension_preserve_law: forall (x y: presented P),
  extension (x @ y) == (extension x) @ (extension y).
Proof.
  move => x y; by rewrite /extension -prod_cat map_cat.
Qed.

(* TODO(reiniscirpons): No new instance was generated but thats ok,
   we intend to use the isRelationPreservingMorphism factory later
   on when we need it. Right? *)
HB.instance Definition _ := 
  isMonoidMorphism.Build _ _
    extension
    extension_preserve_e
    extension_preserve_law.

End ExtensionToMonoidMorphism.
Arguments extension {_ _} _ / !_. 

HB.mixin Record hasInvertibleLetters (P: presentation) := {
  invl : sigma P -> sigma P;
  invlK : forall c, invl (invl c) = c;
  invl_left : forall c, `[c]_P @ `[invl c]_P == e;
  invl_right : forall c, `[invl c]_P @ `[c]_P == e;
}.
#[short(type="invertiblePresentationType")]
HB.structure Definition InvertiblePresentation := { P & hasInvertibleLetters P }.

Lemma invl_inj: forall (P: invertiblePresentationType) (x y: sigma P),
  invl x = invl y <-> x = y.
Proof.
  split => [H|-> //]; by rewrite -(invlK x) -(invlK y) H.
Qed.

Section InvertiblePresentedGroup.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Definition inv_word (w: G) : G := map invl (rev w).

Lemma inv_word_law : forall x y: G, inv_word (x @ y) == (inv_word y) @ (inv_word x).
Proof. by move=> x y; rewrite /inv_word/=/law/= !map_rev map_cat rev_cat. Qed.

Lemma inv_word_left : forall w: G, w @ (inv_word w) == e.
Proof.
elim=> [|a w IH]; first exact: neutral_left.
rewrite /inv_word/law/= rev_cons map_rcons -rcons_cat -cats1 -cat1s.
have: `[a]_P @ ((w: presented P) @ inv_word w) @ `[invl a]_P == e;
  last by done.
by rewrite IH invl_left.
Qed.

Lemma inv_word_right : forall w: G, (inv_word w) @ w == e.
Proof.
elim=> [|a w IH]; first exact: neutral_left.
rewrite /inv_word/law/= rev_cons map_rcons cat_rcons -cat1s -(cat1s a) !(catA _ _ w).
have: (inv_word w) @ (`[invl a]_P @ `[a]_P) @ w == e; last by done.
by rewrite invl_right neutral_right IH.
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
  forall w a, inv_word (a::w) = (inv_word w) ++ [:: invl a].
Proof.
  by move => w a; rewrite /inv_word rev_cons map_rcons cats1.
Qed.

Lemma inv_word_rcons:
  forall w a, inv_word (rcons w a) = invl a :: inv_word w.
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

HB.instance Definition _ := isGroup.Build G inv_word inv_word_law inv_word_left inv_word_right.


Lemma power_inv_word' (w: G) (x: nat):
  power w (- (x: int)) = inv_word (power w x).
Proof.
  elim/nat_pairs_ind: x => [//||n IH1 IH2].
  - by rewrite powerP powerS power0 -!cat_law !cats0.
  - by rewrite powerP powerS IH2 {1}powerS inv_word_cat inv_word_cat
    -IH2 powerP IH1 -catA.
Qed.

Lemma power_inv_word (w: G) (x: int):
  power w (- x) = inv_word (power w x).
Proof.
  case: x => n; first by exact: power_inv_word'.
  by rewrite NegzE power_inv_word' inv_word_involutive. 
Qed.

Lemma FreeGroup_powerC' (w: G) (x: nat):
  power w x ++ w = w ++ power w x.
Proof.
  elim/nat_pairs_ind: x => [||n IH1 IH2].
  - by rewrite power0 /= cats0.
  - by rewrite !powerS power0 -!cat_law cats0.
  - by rewrite powerS -cat_law -{2}IH2 catA.
Qed.

Lemma FreeGroup_powerC'' (w: G) (x: nat):
  power w (- (x:int)) ++ inv w = inv w ++ power w (- (x: int)).
Proof.
  elim/nat_pairs_ind: x => [||n IH1 IH2].
  - by rewrite power0 /= cats0.
  - by rewrite !powerP power0 -!cat_law cats0.
  - by rewrite powerP -cat_law -{2}IH2 catA.
Qed.

Lemma FreeGroup_power1 (w: G):
  power w 1 = w.
Proof.
  by rewrite powerS power0 -cat_law cats0.
Qed.

Lemma FreeGroup_inv1 (c: sigma P):
  inv ([:: c] \mod P) = [:: invl c].
Proof. done. Qed.

Lemma power_rev1 c (x: int):
  rev (power ([::c]: G) x) = power ([::c]: G) x.
Proof.
  elim: x => [//||] n IH.
  - by rewrite powerS rev_cat -!cat_law -FreeGroup_powerC' IH.
  - by rewrite powerP rev_cat -!cat_law -FreeGroup_powerC'' IH.
Qed.

Lemma size0_power c (x: int):
  x != 0 -> (size (power ([::c]: G) x) > 0)%N.
Proof.
  case: (intP x) => [//|n|n].
  - by rewrite powerS -cat_law size_cat /=.
  - by rewrite powerP -cat_law size_cat /=.
Qed.

Lemma size_power c (x: int):
  size (power ([::c]: G) x) = absz x.
Proof.
  case x => n; elim n => [//|n0 IH].
  - by rewrite powerS -cat_law size_cat /= IH.
  - rewrite powerP /=.
    rewrite /= in IH.
    by rewrite IH.
Qed.

    
End InvertiblePresentedGroup.

Section Cancelation.

Variable P: invertiblePresentationType.
Notation G := (presented P).

Variable a x y : G.

Lemma cancel_left : a @ x == a @ y -> x == y.
Proof.
move=> H.
rewrite -(neutral_left x) -(neutral_left y) -(inverse_right a) -!associativity.
by rewrite H.
Qed.

Lemma cancel_right : x @ a == y @ a -> x == y.
Proof.
move=> H.
rewrite -(neutral_right x) -(neutral_right y) -(inverse_left a) !associativity.
by rewrite H.
Qed.

End Cancelation.
Arguments cancel_left {_}.
Arguments cancel_right {_}.
