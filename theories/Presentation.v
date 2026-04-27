From HB Require Import structures.
Require Import Setoid Morphisms RelationClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype.

From GWP Require Import Equivalence EquivalenceAlgebra.


Section Words.
(* C is the carrier type for the letters of the alphabet *)
Variable C: eqType.
Variable Alphabet: seq C.

(* A word uses the alphabet whenever every letter of the word is also
   a letter of the alphabet. *)
Definition uses_alphabet (word: seq C): bool :=
    all (fun letter => letter \in Alphabet) word.

Lemma uses_alphabetP (word: seq C):
  reflect {subset word <= Alphabet} (uses_alphabet word).
Proof. by apply/(iffP allP). Qed.

Lemma uses_alphabet_alphabet (a: C): a \in Alphabet -> uses_alphabet [:: a].
Proof.
  by rewrite /uses_alphabet /= => ->.
Qed.

(* A word over the alphabet is a sequence of letters in the alphabet *)
Structure wordType := Word { wval :> seq C; wcond : uses_alphabet wval }.
Arguments Word {_}.

Canonical alphabet_inj {a: C} (H: a \in Alphabet): wordType :=
  Word (uses_alphabet_alphabet a H).

Lemma uses_alphabet_cons {a} (Ha: a\in Alphabet) {w} (Hw: uses_alphabet w):
  uses_alphabet (a :: w).
Proof.
  by rewrite /= Ha Hw.
Qed.

Infix "::" := uses_alphabet_cons.


Definition wordType_eq word1 word2 := (wval word1 == wval word2)%B.
Arguments wordType_eq / _ _.

Lemma wordType_eqP: Equality.axiom wordType_eq.
Proof.
  move=> x y; apply: (iffP eqP); last first.
  by move=> ->.
  case: x; case: y => s1 p1 s2 p2 /= E.
  rewrite E in p2 *.
  by rewrite (eq_irrelevance p1 p2).
Qed.

HB.instance Definition _ := hasDecEq.Build wordType wordType_eqP.

(*Definition wordType_equiv word1 word2 := wval word1 = wval word2.*)
(*Arguments wordType_equiv / _ _.*)
(**)
(*Lemma wordType_equiv_refl (x: wordType): wordType_equiv x x.*)
(*Proof. done. Qed.*)
(**)
(*Lemma wordType_equiv_symm (x y: wordType):*)
(*  wordType_equiv x y -> wordType_equiv y x.*)
(*Proof. done. Qed.*)
(**)
(*Lemma wordType_equiv_trans (x y z: wordType):*)
(*  wordType_equiv x y -> wordType_equiv y z -> wordType_equiv x z.*)
(*Proof. by rewrite /wordType_equiv => -> ->. Qed.*)
(**)
(*HB.instance Definition _ := hasEq.Build*)
(*  wordType wordType_equiv*)
(*  wordType_equiv_refl wordType_equiv_symm wordType_equiv_trans.*)

HB.instance Definition _ := hasEq.Build
  wordType Logic.eq reflexivity symmetry transitivity.

Lemma wordType_subset (word: wordType): {subset (word: seq C) <= Alphabet}.
Proof. by case: word => w /= /uses_alphabetP. Qed.


Lemma uses_alphabet_nil: uses_alphabet [::].
Proof. done. Qed.

Canonical wordType_nil: wordType := Word uses_alphabet_nil.

Lemma uses_alphabet_cat (word1 word2: wordType):
  uses_alphabet (word1 ++ word2).
Proof.
  apply /uses_alphabetP => word3.
  by rewrite mem_cat => /orP [|] /wordType_subset.
Qed.

Canonical wordType_cat (word1 word2: wordType): wordType :=
  Word (uses_alphabet_cat word1 word2).

Arguments wordType_cat / _ _.

Infix "++" := wordType_cat.

Lemma wordType_catA (x y z: wordType):
  x ++ y ++ z == (x ++ y) ++ z.
Proof. 
  apply /eqP; by rewrite /(_ == _)%B /= catA.
Qed.

Lemma wordType_cat0s (x: wordType): [::] ++ x == x.
Proof. apply /eqP; by rewrite /(_ == _)%B /=. Qed.

Lemma wordType_cats0 (x: wordType): x ++ [::] == x.
Proof. apply /eqP; by rewrite /(_ == _)%B /= cats0. Qed.

Lemma wordType_cat_congruence_left (x y z: wordType):
  y == z -> x ++ y == x ++ z.
Proof.
  by rewrite !/(_ == _) /= => ->.
Qed.

Lemma wordType_cat_congruence_right (x y z: wordType):
  y == z -> y ++ x == z ++ x.
Proof.
  by rewrite !/(_ == _) /= => ->.
Qed.

HB.instance Definition _ := isMonoid.Build
  wordType wordType_cat wordType_nil
  wordType_catA wordType_cat0s wordType_cats0
  wordType_cat_congruence_left wordType_cat_congruence_right.


Definition wordType_ind: forall (cond: wordType -> Prop),
  cond e ->
  (forall a (Ha: a \in Alphabet) w,
    cond w -> cond ((alphabet_inj Ha) @ w)) ->
  (forall w, cond w).
Proof.
  move => cond He Hcons []; elim => [|h t IH] H.
  - have: (H = uses_alphabet_nil) => [|-> //];
    by apply bool_irrelevance.
  - have: (uses_alphabet (h::t)) => [//|/= /andP [Hh Ht]].
    have: (Word H = (alphabet_inj Hh) @ (Word Ht)) => [|->].
  -- by apply /f_equal /bool_irrelevance.
  -- by apply /Hcons /IH.
Qed.
End Words.
Arguments uses_alphabet {_}.
Arguments uses_alphabetP {_}.
Arguments uses_alphabet_nil {_ _}.
Arguments uses_alphabet_cat {_ _ _ _}.
Arguments wordType {_}.
Arguments Word {_} _ {_}.
Arguments alphabet_inj {_ _ _}.
Arguments wordType_nil {_ _}.
Arguments wordType_cat {_ _} / _ _.
Arguments wordType_eq {_ _} / _ _.
(*Arguments wordType_equiv {_ _} / _ _.*)

(* a relation is a pair of words (u, v) over an alphabet Sigma *)
Definition relationType {C: eqType} (Alphabet: seq C) :=
  (wordType Alphabet * wordType Alphabet)%type.

Structure presentation (C: eqType):= mkPresentation {
  alphabet: seq C;
  relations:> seq (relationType alphabet);
  (* Every letter in the alphabet is distinct *)
  alphabet_uniq: uniq alphabet;
}.
Arguments alphabet {_}.
Arguments relations {_}.
Arguments alphabet_uniq {_}.

Section WordProblem.
Variable C: eqType.
Variable P: presentation C.

Let word := wordType (alphabet P).
Let relation := relationType (alphabet P).
Let source (r: relation) : word := fst r.
Let target (r: relation) : word := snd r.
(* `Derivation u v` is the type of witnesses of derivations from
  `u: word` to `v: word` in `P: Presentation` *)
Inductive Derivation : word -> word -> Prop :=
  (* Every relation replacement is a valid derivation. *)
  | Derivation_reduction (r: relation) (p s: word) :
      r \in (relations P) ->
      Derivation (p @ (source r) @ s) (p @ (target r) @ s)
  (* The derivation is an equivalence. *)
  | Derivation_refl (u: word): Derivation u u
  | Derivation_symm (u u': word) : Derivation u u' -> Derivation u' u
  | Derivation_trans (u v w: word) :
      Derivation u v -> Derivation v w -> Derivation u w
  (* The derivation respects the equivalence of words.
     Only need this because words over an alphabet form a setoid
     (identifying equal words with distinct proofs of correctness
     of alphabet usage). *)
  | Derivation_proper (u v u' v': word):
      u == v -> u' == v' -> Derivation u u' -> Derivation v v'.

(* The word problem of the presentation `P`. *)
Definition word_problem (u v: word) : Prop := Derivation u v.

Instance : Reflexive word_problem.
Proof. exact: Derivation_refl. Qed.
Instance : Symmetric word_problem.
Proof. exact: Derivation_symm. Qed.
Instance : Transitive word_problem.
Proof. exact: Derivation_trans. Qed.
Global Instance : Equivalence word_problem := {}.

Global Instance : Proper (eq ==> eq ==> iff) word_problem.
Proof.
  move => u v H1 u' v' H2; split; by apply Derivation_proper.
Qed.

(* TODO(reiniscirpons): Is there a better way to derive this induction
                        principle? *)

Definition word_problem_ind:
  forall (cond: word -> word -> Prop),
  (forall r p s, r \in relations P -> cond (p @ r.1 @ s) (p @ r.2 @ s)) ->
  (forall u, cond u u) ->
  (forall u u', word_problem u u' -> cond u u' -> cond u' u) ->
  (forall u v w,
    word_problem u v -> word_problem v w ->
    cond u v -> cond v w -> cond u w) ->
  (forall u v u' v',
    u == v -> u' == v' -> word_problem u u' ->
    cond u u' -> cond v v') ->
  forall x y, word_problem x y -> cond x y :=
    fun cond Hred Hrefl Hsymm Htrans Hproper =>
      fix f x y H :=
        match H with
        | Derivation_reduction r p s Hr => Hred r p s Hr
        | Derivation_refl u => Hrefl u
        | Derivation_symm u u' Hu => Hsymm u u' Hu (f u u' Hu)
        | Derivation_trans u v w Huv Hvw =>
            Htrans u v w Huv Hvw (f u v Huv) (f v w Hvw)
        | Derivation_proper u v u' v' Hu Hv H' =>
            Hproper u v u' v' Hu Hv H' (f u u' H')
        end.

End WordProblem.
Arguments Derivation {_}.
Arguments word_problem {_}.
Hint Resolve Derivation_refl : core.




(* In a monoid defined by a presentation, two words are equal whenever
   one can derive the other using the relations of P. *)
Section PresentedEq.
Variable C: eqType.
Variable P: presentation C.

End PresentedEq.

(* All monoids defined by a presentation have a monoid structure *)
Section PresentedMonoid.
Variable C: eqType.
Variable P: presentation C.

(* The monoid presented by the presentation `P` is the quotient
   monoid of the free monoid (`wordType (alphabet P)` in our case)
   by the least two-sided congruence generated by the relayions of `P`,
   (`word_problem P` in our case). *)
Structure presented_monoid := PresentedMonoid {
  word_of:> wordType (alphabet P)
}.

Definition generator a (Ha: a \in alphabet P): presented_monoid :=
  {| word_of := alphabet_inj Ha |}.

Definition presented_monoid_eq (x y: presented_monoid) :=
  word_problem P x y.

Arguments presented_monoid_eq / _ _.

Lemma presented_monoid_eq_refl x: presented_monoid_eq x x.
(* TODO(reiniscirpons): Why do I need to do reflexivity manually here?? *)
Proof. done. Qed.
Lemma presented_monoid_eq_symm x y:
  presented_monoid_eq x y -> presented_monoid_eq y x.
Proof. by rewrite /=; symmetry. Qed.
Lemma presented_monoid_eq_trans x y z:
  presented_monoid_eq x y ->
  presented_monoid_eq y z ->
  presented_monoid_eq x z.
Proof. by rewrite /=; transitivity y. Qed.

HB.instance Definition _ :=
  hasEq.Build presented_monoid presented_monoid_eq
  presented_monoid_eq_refl presented_monoid_eq_symm presented_monoid_eq_trans.

Canonical presented_monoid_e: presented_monoid := PresentedMonoid [::].

Notation eps := presented_monoid_e.

Canonical presented_monoid_law
  (word1 word2: presented_monoid): presented_monoid :=
    PresentedMonoid (@law (wordType _) word1 word2).

Infix ".@" := presented_monoid_law (at level 50). 

Lemma presented_monoid_lawA (x y z : presented_monoid):
  x .@ (y .@ z) == (x .@ y) .@ z.
Proof.
  by rewrite !/(_ .@ _) !/(_ == _) /= associativity.
Qed.

Lemma presented_monoid_law0s (x: presented_monoid):  eps .@ x == x.
Proof.
  by rewrite !/(_ .@ _) !/(_ == _) /= neutral_left.
Qed.

Lemma presented_monoid_laws0 (x: presented_monoid):  x .@ eps == x.
Proof.
  by rewrite !/(_ .@ _) !/(_ == _) /= neutral_right.
Qed.

Lemma presented_monoid_congruent_left (a u v: presented_monoid):
  u == v -> a .@ u == a .@ v.
Proof.
  rewrite !/(_ .@ _) !/(_ == _) /=.
  elim => [r p s Hr|u' //|u' v' _|u' v' w' _ H1 _ H2| u' v' u'' v'' -> -> //].
  - rewrite !associativity; by apply Derivation_reduction.
  - by symmetry.
  - by transitivity (a @ v' :> wordType _).
Qed.

Lemma presented_monoid_congruent_right (b u v: presented_monoid):
  u == v -> u .@ b == v .@ b.
Proof.
  rewrite !/(_ .@ _) !/(_ == _) /=.
  elim => [r p s Hr|u' //|u' v' _|u' v' w' _ H1 _ H2| u' v' u'' v'' -> -> //].
  - rewrite -!(associativity _ s); by apply Derivation_reduction.
  - by symmetry.
  - by transitivity (v' @ b :> wordType _).
Qed.

HB.instance Definition _ := isMonoid.Build
  presented_monoid presented_monoid_law presented_monoid_e
  presented_monoid_lawA presented_monoid_law0s presented_monoid_laws0
  presented_monoid_congruent_left presented_monoid_congruent_right.

Lemma presented_monoid_preserve_law: forall x y,
  PresentedMonoid (x @ y) = (PresentedMonoid x) @ (PresentedMonoid y).
Proof. by case. Qed.

(*Lemma PresentedMonoid_preserve_equiv: forall x y,*)
(*  x == y -> PresentedMonoid x == PresentedMonoid y.*)
(*Proof.*)
(*  move => x y /eqP H;*)
(*  have: (PresentedMonoid x = PresentedMonoid y) => [|-> //].*)
(*  by apply /f_equal /eqP.*)
(*Qed.*)
(**)
(*HB.instance Definition _ := isSetoidMorphism.Build*)
(*  (wordType (alphabet P)) presented_monoid PresentedMonoid*)
(*  PresentedMonoid_preserve_equiv.*)
(**)
(*Lemma PresentedMonoid_preserve_neutral: PresentedMonoid e == e.*)
(*Proof. done. Qed.*)
(**)
(*Lemma PresentedMonoid_preserve_law: forall x y,*)
(*  PresentedMonoid (x @ y) == (PresentedMonoid x) @ (PresentedMonoid y).*)
(*Proof. done. Qed.*)
(**)
(*HB.instance Definition _ := isMonoidMorphism.Build*)
(*  (wordType (alphabet P)) presented_monoid PresentedMonoid*)
(*  PresentedMonoid_preserve_neutral PresentedMonoid_preserve_law.*)


End PresentedMonoid.
Arguments presented_monoid_eq {_ _} / _ _.
Arguments presented_monoid {_}.
Arguments PresentedMonoid {_}.
Arguments word_of {_ _}.
Arguments generator {_ _ _}.

(* TODO(reiniscirpons): Do we still need these proofs? *)
(*Lemma reduction {C: eqType} {P: presentation C}:*)
(*  forall (a b u v: presented P),*)
(*  (u, v) \in relations P -> a @ u @ b == a @ v @ b.*)
(*Proof. by move=> a b u v H; apply: (Derivation_reduction _ (u, v)); done. Qed.*)
(**)
(*Lemma reduction_rule {P: presentation}:*)
(*  forall (u v: presented P),*)
(*  (u, v) \in relations P -> u == v.*)
(*Proof.*)
(*move=> u v Hin.*)
(*transitivity (e @ u @ e).*)
(*  by symmetry; apply: neutral_right.*)
(*transitivity (e @ v @ e); last first.*)
(*  by apply: neutral_right.*)
(*exact: (reduction e e).*)
(*Qed.*)

(* TODO(reiniscirpons): Do we still need these?*)
(* NOTE(reiniscirpons): Declaring cat and cons to multiplication
   law conversions to simplify future lemmas. *)
(*Lemma cat_law: forall P (x y: presented P),*)
(*    (x ++ y: presented P) = x @ y.*)
(*Proof. by []. Qed.*)
(**)
(*Lemma cons_law: forall P (a: sigma P) (x: presented P),*)
(*    (a :: x: presented P) = `[a]_P @ x.*)
(*Proof. by []. Qed.*)
(**)
(*Lemma rcons_law: forall P (a: sigma P) (x: presented P),*)
(*    (rcons x a: presented P) = x @ `[a]_P.*)
(*Proof. move => P a; by elim => [//|b w /= ->]. Qed.*)

(* Show that preserving relations and multiplication is enough to define
   monoid morphism out of presented monoid. *)
(* TODO(reiniscirpons): How can reuse the IsMonoidMorphism axioms here? *)
HB.factory Record isRelationPreservingMorphism
  (C: eqType) (P: presentation C) (M: monoid)
  (f: presented_monoid P -> M)
    (* TODO(reiniscirpons): Why does this caause a bug?*)
    (* & isMonoidMorphism (presented P) B f*)
    := {
    morphism_preserve_relations: forall u v,
      (u, v) \in relations P ->
      f ({| word_of := u |}) == f ({| word_of := v|});
    morphism_preserve_e':
      f e == e;
    morphism_preserve_law':
      forall x y, f (x @ y) == (f x) @ (f y);
}.

HB.builders Context (C: eqType) (P: presentation C) (M: monoid) f of 
  isRelationPreservingMorphism C P M f.

  Fact f_preserve_equiv: forall x y, x == y -> f x == f y.
  Proof.
    move => [x] [y]; rewrite /(_ == _) /=; move: x y;
    apply word_problem_ind =>
      [[u v] p s Hr|//|? ? _ -> //|? ? ? _ _ -> //|? ? ? ? -> -> //].
    by rewrite !presented_monoid_preserve_law !morphism_preserve_law'
                 (morphism_preserve_relations u v).
  Qed.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ f f_preserve_equiv.
  
  HB.instance Definition _ :=
    isMonoidMorphism.Build _ _ f morphism_preserve_e' morphism_preserve_law'.
HB.end.

Section ExtensionToMonoidMorphism.

Variable C: eqType.
Variable P: presentation C.
Variable M: monoid.
Variable f: C -> M.

Definition extension: presented_monoid P -> M :=
  fun l => prod (map f l).
Arguments extension / !_.

(*Lemma extension_cons:*)
(*  forall (a: C) (w:  P),*)
(*  extension (a::w) = (f a) @ (extension w).*)
(*Proof. done. Qed.*)
Lemma extension_universality:
  forall (varphi: morphism (presented_monoid P) M),
    (forall a (Ha: a \in alphabet P),
      (* TODO(reiniscirpons): Make this nicer. Notation perhaps? *)
      varphi (generator Ha) == f a) -> 
    (forall w: presented_monoid P, 
      varphi w == extension w).
Proof.
  move => varphi Heq []; elim/wordType_ind => /= [|h Hh t <-].
  - by rewrite morphism_preserve_e.
  - by rewrite -(Heq h Hh) -morphism_preserve_law.
Qed.

Lemma extension_preserve_e: extension e == e.
Proof. done. Qed.

Lemma extension_preserve_1: forall a (Ha: a \in alphabet P),
  extension (generator Ha) == f a.
Proof.
  by move => c /=; rewrite neutral_right.
Qed.

Lemma extension_preserve_law: forall (x y: presented_monoid P),
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

HB.mixin Record hasInvertibleLetters (C: eqType) (P: presentation C) := {
  invl : C -> C;
  invl_in_alphabet: forall c (Hc: c \in alphabet P), invl c \in alphabet P;
  invlK : forall c, c \in alphabet P -> invl (invl c) = c;
  invl_right : forall c (Hc: c \in alphabet P),
    (generator Hc) @ (generator (invl_in_alphabet c Hc)) == e;
  invl_left : forall c (Hc: c \in alphabet P),
    (generator (invl_in_alphabet c Hc)) @ (generator Hc) == e;
}.
#[short(type="invertiblePresentationType")]
HB.structure Definition InvertiblePresentation (C: eqType) :=
  { P & hasInvertibleLetters C P }.
Arguments invl_in_alphabet {_ _ _}.
Arguments invlK {_ _ _}.
Arguments invl_right {_ _ _}.
Arguments invl_left {_ _ _}.

Section InvertiblePresentedGroup.

Variable C: eqType.
Variable P: invertiblePresentationType C.
Let G := presented_monoid P.

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
