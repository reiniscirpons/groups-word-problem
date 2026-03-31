From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq fintype choice ssrnat all_algebra.
From mathcomp Require Import ring lra zify.
Require Import Setoid Morphisms.

From GWP Require Import Presentation Equivalence EquivalenceAlgebra.

Import PresentationNotations.

Inductive InverseAlphabet (Sigma: eqType) :=
| Base: Sigma -> InverseAlphabet Sigma
  | Inverse: Sigma -> InverseAlphabet Sigma.
Arguments Base {_}.
Arguments Inverse {_}.

Section InverseAlphabetEqType.
Variable (Sigma: eqType).

Definition InverseAlphabet_eq (u v: InverseAlphabet Sigma) :=
  match (u, v) with
  (* TODO(reiniscirpons): how do I use the usual == notation here? *)
  | (Base a, Base b) => (eq_op a b)
  | (Inverse a, Inverse b) => (eq_op a b)
  | _ => false
  end.

Lemma InverseAlphabet_eqP: eq_axiom InverseAlphabet_eq.
Proof.
(* TODO(reiniscirpons): how do I make this proof nicer? *)
rewrite /InverseAlphabet_eq; case => x; case => y; apply (iffP idP) => //.
- move/eqP => H; by rewrite H.
- case => H; by rewrite H.
- move/eqP => H; by rewrite H.
- case => H; by rewrite H.
Qed.

HB.instance Definition _ := hasDecEq.Build (InverseAlphabet Sigma) InverseAlphabet_eqP.
End InverseAlphabetEqType.

Section InverseAlphabetCountType.
Variable (Sigma: countType).

Definition InverseAlphabet_pickle (x: InverseAlphabet Sigma) :=
  match x with
  | Base a => (pickle a).*2
  | Inverse a => (pickle a).*2.+1
  end.

Definition InverseAlphabet_unpickle (n: nat):
  option (InverseAlphabet Sigma) :=
    match unpickle n./2, odd n with
    | Some a, false => Some (Base a)
    | Some a, true => Some (Inverse a)
    | None, _ => None
    end.


Lemma InverseAlphabet_pickleK:
  pcancel InverseAlphabet_pickle InverseAlphabet_unpickle.
Proof.
  case => a /=; rewrite /InverseAlphabet_unpickle /=.
  - by rewrite doubleK pickleK odd_double.
  - by rewrite uphalf_double pickleK odd_double.
Qed.

(* TODO(reiniscirpons): Are the "Ignoring canonical projection ..."
   warnings an issue? *)
HB.instance Definition _ := isCountable.Build
  (InverseAlphabet Sigma)
  InverseAlphabet_pickleK.
End InverseAlphabetCountType.

Section InverseAlphabetFinType.
Variable (Sigma: finType).

Definition InverseAlphabet_enum:
  seq (InverseAlphabet Sigma) :=
    [seq Base a | a: Sigma] ++ [seq Inverse a | a: Sigma].

Lemma InverseAlphabet_enum_in:
  forall (a: InverseAlphabet Sigma),
    a \in InverseAlphabet_enum.
Proof.
  move => a; rewrite /InverseAlphabet_enum mem_cat.
  apply/orP; case: a => a.
  - left; apply map_f; by rewrite mem_enum.
  - right; apply map_f; by rewrite mem_enum.
Qed.

Lemma InverseAlphabet_enum_uniq: uniq InverseAlphabet_enum.
Proof.
  rewrite /InverseAlphabet_enum cat_uniq; apply /andP; split.
  - rewrite map_inj_uniq.
  -- by apply enum_uniq.
  -- move => x y; by case.
  apply /andP; split; last first.
  - rewrite map_inj_uniq.
  -- by apply enum_uniq.
  -- move => x y; by case.
  - apply/hasP; case => a.
    move/codomP => [b H]; move/codomP => [c]; by rewrite H.
Qed.

Lemma InverseAlphabet_enumP:
  Finite.axiom InverseAlphabet_enum.
Proof.
  move => a; rewrite /InverseAlphabet_enum.
  (* TODO(reiniscirpons): Should I import ssrnat? *)
  have H: ssrnat.nat_of_bool (a \in InverseAlphabet_enum) = 1%N.
  - by rewrite InverseAlphabet_enum_in.
  rewrite -H; apply count_uniq_mem.
  by exact InverseAlphabet_enum_uniq.
Qed.

HB.instance Definition _ := isFinite.Build
  (InverseAlphabet Sigma)
  InverseAlphabet_enumP.

End InverseAlphabetFinType.

Section FreeGroup.

(* NOTE(reiniscirpons): Only finitely generated free groups are formalized. *)
Variable (Sigma: finType).

Definition free_group_relations:
  seq (relation (InverseAlphabet Sigma)) :=
  [seq pair [:: Base a; Inverse a] [::] | a: Sigma] ++
  [seq pair [:: Inverse a; Base a] [::] | a: Sigma].

Definition FGP :=
  Pres (InverseAlphabet Sigma) free_group_relations.

Definition FreeGroup := (presented FGP).

(* NOTE(reiniscirpons): Need to use the sigma here instead of
   InverseAlphabet Sigma because of technical reasons. *)
Definition FreeGroup_invl (c: sigma FGP): sigma FGP :=
  match c with
  | Base a => Inverse a
  | Inverse a => Base a
  end.

Lemma FreeGroup_invlK : forall c: sigma FGP,
  FreeGroup_invl (FreeGroup_invl c) = c.
Proof. by case. Qed.

Lemma FreeGroup_invl_left : forall c: sigma FGP,
  `[c; FreeGroup_invl c]_FGP == `[]_FGP.
Proof.
  move=> c; apply: reduction_rule; case: c => a;
  rewrite /relations /= /free_group_relations mem_cat; apply /orP.
  - left; apply/mapP; exists a => [|//]; by apply mem_enum.
  - right; apply/mapP; exists a => [|//]; by apply mem_enum.
Qed.

Lemma FreeGroup_invl_right : forall c: sigma FGP,
  `[FreeGroup_invl c; c]_FGP == `[]_FGP.
(* TODO(reiniscirpons): fix *)
Proof.
  case => a /=.
  - set c := Inverse a; have: Base a = FreeGroup_invl c => [//|->].
    by apply FreeGroup_invl_left.
  - set c := Base a; have: Inverse a = FreeGroup_invl c => [//|->].
    by apply FreeGroup_invl_left.
Qed.

HB.instance Definition _ :=
  hasInvertibleLetters.Build
    FGP
    FreeGroup_invl
    FreeGroup_invlK
    FreeGroup_invl_left
    FreeGroup_invl_right.


(* NOTE(reiniscirpons): in theory we could do this more efficiently with the
 complete rewriting system *)
Fixpoint FreeGroup_norm (w: FreeGroup): FreeGroup := match w with
  | [::] => `[]_FGP
  | c::w' => match (FreeGroup_norm w') with
    | [::] => `[c]_FGP
    | d::n =>
      if (c == invl d)%B then n
      else c::(d::n)
    end
  end.

Lemma FreeGroup_norm_e:
  FreeGroup_norm e = e.
Proof. done. Qed.

Lemma FreeGroup_norm_1: forall (c: sigma FGP),
  FreeGroup_norm (`[c]_FGP) = (`[c]_FGP).
Proof.
  by case => c.
Qed.

Lemma FreeGroup_norm_correct w:
  FreeGroup_norm w == w.
Proof.
  elim: w => [//|c w IH /=]; rewrite (cons_law _ c w).
  case Hn: (FreeGroup_norm w) => [//|d w']; rewrite -IH Hn.
  - by rewrite -cons_law.
  case Heq: (c == invl d)%B; last first.
  - by rewrite -cons_law.
  move/eqP: Heq => ->;
  by rewrite (cons_law _ d) associativity invl_right.
Qed.

Definition FreeGroup_dec_eq (w w': FreeGroup): bool :=
  ((FreeGroup_norm w) == (FreeGroup_norm w'))%B.

Lemma FreeGroup_refl p: FreeGroup_dec_eq p p.
Proof. by rewrite /FreeGroup_dec_eq. Qed.

Lemma FreeGroup_dec_eq_to_eqprop w w':
  (FreeGroup_dec_eq w w') -> (w == w').
Proof.
  by move=> eq;
  rewrite -[w]FreeGroup_norm_correct -[w']FreeGroup_norm_correct (eqP eq).
Qed.

Lemma FreeGroup_norm_cat_back w1 w2 w3:
  FreeGroup_norm w1 = FreeGroup_norm w2 ->
    FreeGroup_norm (w3 @ w1) = FreeGroup_norm (w3 @ w2).
Proof.
  move=> H; by elim: w3 => [//|c w3 /= ->].
Qed.

Lemma FreeGroup_norm_rcons w c:
  FreeGroup_norm (rcons w c) =
  match rev (FreeGroup_norm w) with
  | [::] => `[c]_FGP
  | d :: n => 
      if (c == invl d)%B then rev n
      else rcons (rcons (rev n) d) c
  end.
Proof.
  elim: w => [//|d w].
  rewrite rcons_cons /= => ->.
  case: (FreeGroup_norm w) => [| e n] /=.
  - case H1: (c == invl d)%B;
    case H2: (d == invl c)%B => //; exfalso;
    move/eqP: H1 => H1; move/eqP: H2 => H2.
  -- apply H2; by rewrite H1 invlK.
  -- apply H1; by rewrite H2 invlK.
  rewrite !rev_cons;
  case Hrev: (rev n) => [|f n'] /=.
  - case H1: (c == invl e)%B;
    case H2: (d == invl e)%B => /=.
  -- by rewrite Hrev; move/eqP: H1 => ->; move/eqP: H2 => ->.
  -- by rewrite !rev_cons Hrev /= H1.
  -- by rewrite Hrev.
  -- by rewrite !rev_cons Hrev /= H1.
  rewrite rev_rcons.
  - case H1: (c == invl f)%B;
    case H2: (d == invl e)%B => /=.
  -- by rewrite Hrev H1.
  -- by rewrite !rev_cons Hrev !rcons_cons H1 !rev_rcons.
  -- by rewrite H2 Hrev H1.
  -- by rewrite H2 !rev_cons Hrev !rcons_cons H1 !rev_rcons.
Qed.

Lemma FreeGroup_norm_rev w:
  FreeGroup_norm (rev w) = rev (FreeGroup_norm w).
Proof.
elim: w => // c w /= eq.
have <-: rev (FreeGroup_norm (rev w)) = FreeGroup_norm w.
  by rewrite eq revK.
rewrite rev_cons FreeGroup_norm_rcons eq !revK;
case: (FreeGroup_norm w) => [//|d l].
case: (c == invl d)%B; first done; by rewrite !rev_cons.
Qed.

Lemma FreeGroup_norm_map_invl w:
  FreeGroup_norm (map invl w) = map invl (FreeGroup_norm w).
Proof.
  elim: w => [//|c w /= ->].
  case: (FreeGroup_norm w) => {w} [//|d w /=].
  rewrite invlK; case H1: (invl c == d)%B;
  case H2: (c == invl d)%B => //; exfalso;
  move/eqP: H1 => H1; move/eqP: H2 => H2.
  - apply H2; by rewrite -(invlK c) invl_inj.
  - apply H1; by rewrite -(invlK d) invl_inj.
Qed.

Lemma FreeGroup_norm_inv w:
  FreeGroup_norm (inv w) = inv (FreeGroup_norm w).
Proof.
  by rewrite /inv/=/inv_word/= -FreeGroup_norm_rev FreeGroup_norm_map_invl.
Qed.

Lemma FreeGroup_norm_cat w1 w2 w3:
  FreeGroup_norm w1 = FreeGroup_norm w2 -> FreeGroup_norm (w1 @ w3) = FreeGroup_norm (w2 @ w3).
Proof.
rewrite -[w1 @ w3]revK -[w2 @ w3]revK.
rewrite ![FreeGroup_norm (rev (rev _))]FreeGroup_norm_rev => eq.
have -> //: FreeGroup_norm (rev (w1 @ w3)) = FreeGroup_norm (rev (w2 @ w3)).
rewrite /law/= !rev_cat; apply /FreeGroup_norm_cat_back.
by rewrite !FreeGroup_norm_rev eq.
Qed.

Lemma FreeGroup_norm_unique w w':
  w == w' -> FreeGroup_norm w = FreeGroup_norm w'.
Proof.
elim=> [[r1 r2] w1 w2|//|? ? _ -> //|? ? ? _ -> _ -> //].
rewrite /relations /= /free_group_relations;
rewrite mem_cat => /orP []; move/mapP => [a Henum [-> ->]];
apply /FreeGroup_norm_cat /FreeGroup_norm_cat_back => /=;
by rewrite eq_refl.
Qed.

Lemma FreeGroup_norm_involutive:
  forall w, FreeGroup_norm (FreeGroup_norm w) = FreeGroup_norm w.
Proof.
  move => w; apply FreeGroup_norm_unique; by rewrite FreeGroup_norm_correct.
Qed.

Lemma FreeGroup_norm_law:
  forall x y, FreeGroup_norm (x @ y) = FreeGroup_norm(FreeGroup_norm x @ FreeGroup_norm y).
Proof.
  move => x y; apply FreeGroup_norm_unique; by rewrite !FreeGroup_norm_correct.
Qed.

Lemma FreeGroup_norm_cons_invl: forall c (w: FreeGroup),
  FreeGroup_norm ([:: c, invl c & w]) = FreeGroup_norm w.
Proof.
  move => c w; apply FreeGroup_norm_unique;
  by rewrite cons_law (cons_law _ _ w) associativity invl_left neutral_left.
Qed.

Lemma FreeGroup_norm_subseq: forall (w: FreeGroup),
  subseq (FreeGroup_norm w) w.
Proof.
  elim => [//|c w /=].
  case: (FreeGroup_norm w) => [_|d n /=].
  - have: (c == c)%B => [//|->]; by apply sub0seq.
  case: (c == invl d)%B => [|IH]; last first.
  - by have: (c == c)%B => [//|->].
  case: n => [//|e n IH].
  case: (e == c)%B.
  - by apply cons_subseq with e; apply cons_subseq with d.
  - by apply cons_subseq with d.
Qed.

Lemma FreeGroup_norm_minimality: forall (w: FreeGroup),
  (forall x, w == x -> subseq w x) <-> w = FreeGroup_norm w.
Proof.
  move => w; split.
  - move => H; apply /subseq_anti /andP; split.
  -- by apply H; rewrite FreeGroup_norm_correct.
  -- by apply FreeGroup_norm_subseq.
  - move => {2} -> x; move/FreeGroup_norm_unique => ->.
    by apply FreeGroup_norm_subseq.
Qed.

Lemma eqprop_to_FreeGroup_dec_eq w w':
  (w == w') -> (FreeGroup_dec_eq w w').
Proof. by move=> eq; exact /eqP /FreeGroup_norm_unique. Qed.

Lemma FreeGroup_dec_eqP w w':
  reflect (w == w') (FreeGroup_dec_eq w w').
Proof.
apply /(iffP idP) => eq.
- exact: FreeGroup_dec_eq_to_eqprop.
- exact: eqprop_to_FreeGroup_dec_eq.
Qed.

Global Instance : Proper (eq ==> eq_op) FreeGroup_norm.
Proof.
  by move => x y; move/FreeGroup_norm_unique => ->.
Qed.


Lemma FreeGroup_norm_power1: forall c n,
  FreeGroup_norm (power (`[c]_FGP) n) = power (`[c]_FGP) n.
Proof.
  (*move => c; elim => [//||] [//|n IH].*)
  (* TODO: Why does it not allow me to do this rewrite despite FreeGroup_norm
           being Proper? *)
  (*- apply/eqP; rewrite {1}powerS powerC'.*)
  move => c; case; elim/nat_pairs_ind => [//|//|n IH1 _].
  - rewrite !powerS /= {}IH1; case: n; by case: c.
  - by case: c.
  - move: IH1; rewrite !powerP => /= -> /=; by case: c.
Qed.


End FreeGroup.
Arguments FreeGroup_norm {_}.

Section FreelyReduced.

Variable Sigma: finType.

Definition freely_reduced (w: FreeGroup Sigma): Prop :=
  forall p s c, w <> p ++ [:: invl c; c] ++ s.

Lemma freely_reduced_nil: freely_reduced [::].
Proof. by case. Qed.

Lemma freely_reduced_cons1: forall c, freely_reduced [::c].
Proof. move => c; case => [//|d]; by case. Qed.

Lemma freely_reduced_cons2: forall c d w,
  c <> invl d -> freely_reduced (d::w) -> freely_reduced (c::(d::w)).
Proof.
  move => c d w Hcd Hw [|f s] p e /=.
  - case => Hc Hd _; apply Hcd; by rewrite Hc Hd.
  - case => _ H; by apply (Hw s p e).
Qed.

Lemma freely_reduced_behead:
  forall c w, freely_reduced (c::w) -> freely_reduced w.
Proof.
  move => c w H p s d He.
  apply (H (c::p) s d); by rewrite He.
Qed.

Lemma freely_reduced_cat:
  forall w1 c1 c2 w2,
    c1 <> invl c2 ->
    freely_reduced (rcons w1 c1) ->
    freely_reduced (c2::w2) ->
    freely_reduced ((rcons w1 c1) ++ (c2 :: w2)).
Proof.
  move => w1 c1 c2 w2 Hc Hw1 Hw2 p s d.
  case Hp: (size p + 1 <= size w1)%N.
  - move/(f_equal (take (size w1).+1)).
    rewrite take_cat size_rcons ltnn subnn take0 cats0.
    rewrite take_cat leq_gtF; last by move: Hp => /=; lia.
    rewrite take_cat leq_gtF; last by move: Hp => /=; lia.
    by apply Hw1.
  - move/(f_equal (drop (size p))).
    rewrite cat_rcons drop_cat leq_gtF; last by move: Hp => /=; lia.
    rewrite drop_cat ltnn drop_cat subnn /=.
    rewrite (drop_cat _ [::c1]) /=.
    case Hpe: (eqn (size p) (size w1)).
  -- move/eqP: Hpe => ->.
     rewrite subnn /=; case => Hc1 Hc2 _.
     by apply Hc; rewrite Hc1 Hc2.
  -- rewrite leq_gtF; last by move: Hp Hpe => /=; lia.
     move => H.
     apply /(Hw2 (take (size p - size w1 - 1) (c2::w2)) s d).
     by rewrite /= -H cat_take_drop.
Qed.


Lemma freely_reduced_correct:
  forall w, freely_reduced w <-> w = FreeGroup_norm w.
Proof.
  move => w; split.
  - elim: w => [//|c w IH Hcw].
    have: (w = FreeGroup_norm w).
      by apply /IH /freely_reduced_behead.
    move => /= <-; case: w {IH} Hcw => [//|d w H].
    case Hcd: (c == invl d)%B => [|//];
    move/eqP: Hcd => -> in H; exfalso;
    by apply (H [::] w d).
  - move => H p s c Hps.
    enough (Hfalse: (p++s) = w).
  -- move: Hfalse; rewrite Hps => {}Hps.
     have: subseq (p ++ [:: invl c; c] ++ s) (p++s).
  --- by rewrite Hps.
  --- by rewrite subseq_cat2l -{2}(cat0s s) subseq_cat2r.
  -- apply /subseq_anti /andP; split.
  --- rewrite Hps; apply cat_subseq => [//|]; by apply suffix_subseq.
  --- apply FreeGroup_norm_minimality => [//|].
      by rewrite Hps !cat_law cons_law invl_right neutral_left.
Qed.

Lemma freely_reduced_rev:
  forall w, freely_reduced w -> freely_reduced (rev w).
Proof.
  move => w; rewrite !freely_reduced_correct => {1}->.
  by rewrite FreeGroup_norm_rev.
Qed.

Lemma freely_reduced_power1: forall c n,
  freely_reduced (power (`[c]_(FGP Sigma)) n).
Proof.
  by move => c n; rewrite freely_reduced_correct FreeGroup_norm_power1.
Qed.

End FreelyReduced.
Arguments freely_reduced {_}.

Section FreeGroupUniversal.

Variable (Sigma: finType).
Variable (G: group).
Variable (f: Sigma -> G).

Definition FreeGroup_alphabet_extension:
  sigma (FGP Sigma) -> G :=
    fun c =>
      match c with
      | Base a => f a
      | Inverse a => inv (f a)
      end.

Lemma FreeGroup_alphabet_extension_preserve_inv_on_sigma:
  forall (a: sigma (FGP Sigma)),
    inv (FreeGroup_alphabet_extension a) == 
    (FreeGroup_alphabet_extension) (invl a).
Proof.
  case => [//|a]. by apply inv_involutive.
Qed.

Definition FreeGroup_universal_extension: (FreeGroup Sigma) -> G :=
      extension FreeGroup_alphabet_extension.

Lemma FreeGroup_alphabet_extension_preserve_relations:
  forall u v,
    (u, v) \in relations (FGP Sigma) ->
    FreeGroup_universal_extension u == FreeGroup_universal_extension v.
Proof.
  move => u v; rewrite mem_cat; case/orP; move/mapP => [a _ [-> ->]];
  rewrite/FreeGroup_universal_extension
         /extension /FreeGroup_alphabet_extension /=
         associativity neutral_right.
  - by rewrite inverse_left.
  - by rewrite inverse_right.
Qed.

HB.instance Definition _ := isRelationPreservingMorphism.Build
  (FGP Sigma) G
  FreeGroup_universal_extension
  FreeGroup_alphabet_extension_preserve_relations
  (extension_preserve_e _ _ FreeGroup_alphabet_extension)
  (extension_preserve_law _ _ FreeGroup_alphabet_extension).

(* TODO(reiniscirpons): Is it possible to make Rocq treat sigma
  (FreeGroup_presentation Sigma) and InverseAlphabet Sigma as the same? *)
(*Lemma FreeGroup_universal: forall {Sigma: finType} {G: group} (f: Sigma -> G),*)
(*  exists (varphi: morphism (FreeGroup Sigma) G), *)
(*    forall a: Sigma, f a == varphi `[Base a].*)
(*Proof.*)
(*  move => G f.*)
(*  exists (FreeGroup_universal_extension f).*)
(*  move => a.*)
(*  by [].*)
(*  (* TODO(reiniscirpons): Why are we not done by computation?*) *)
(*Qed.*)
(*Admitted.*)
End FreeGroupUniversal.
Arguments FreeGroup_universal_extension {_ _}.
Notation "\hat f" := (FreeGroup_universal_extension f) (at level 5). 

