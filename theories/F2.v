From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq fintype choice ssrnat.

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
unfold InverseAlphabet_eq; case => x; case => y; apply (iffP idP) => //.
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
  case => a /=; unfold InverseAlphabet_unpickle => /=.
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
  move => a; unfold InverseAlphabet_enum; rewrite mem_cat.
  apply/orP; case: a => a.
  - left; apply map_f; by rewrite mem_enum.
  - right; apply map_f; by rewrite mem_enum.
Qed.

Lemma InverseAlphabet_enum_uniq: uniq InverseAlphabet_enum.
Proof.
  unfold InverseAlphabet_enum.
  Search (uniq (_ ++ _)).
  rewrite cat_uniq; apply /andP; split.
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
  move => a; unfold InverseAlphabet_enum.
  (* TODO(reiniscirpons): Should I import ssrnat? *)
  have H: ssrnat.nat_of_bool (a \in InverseAlphabet_enum) = 1.
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

Definition FreeGroup_presentation :=
  Pres (InverseAlphabet Sigma) free_group_relations.

Definition FreeGroup := (presented FreeGroup_presentation).

(* NOTE(reiniscirpons): Need to use the sigma here instead of
   InverseAlphabet Sigma because of technical reasons. *)
Definition FreeGroup_invl (c: sigma FreeGroup_presentation):
  sigma FreeGroup_presentation :=
  match c with
  | Base a => Inverse a
  | Inverse a => Base a
  end.

Lemma FreeGroup_invl_left : forall c: sigma FreeGroup_presentation,
  `[c; FreeGroup_invl c] == `[].
Proof.
  move=> c; apply: reduction_rule; case: c => a; unfold relations => /=;
  unfold free_group_relations; rewrite mem_cat; apply /orP.
  - left; apply/mapP; exists a => [|//]; by apply mem_enum.
  - right; apply/mapP; exists a => [|//]; by apply mem_enum.
Qed.

Lemma FreeGroup_invl_right : forall c: sigma FreeGroup_presentation,
  `[FreeGroup_invl c; c] == `[].
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
    FreeGroup_presentation
    FreeGroup_invl
    FreeGroup_invl_left
    FreeGroup_invl_right.


(* NOTE(reiniscirpons): in theory we could do this more efficiently with the
 complete rewriting system *)
Fixpoint FreeGroup_norm (w: FreeGroup): FreeGroup := match w with
  | [::] => [::]
  | c::w => match c, FreeGroup_norm w with
    | Base a, Inverse b::n => 
      if a == b then n else (Base a)::(Inverse b)::n
    | Inverse a, Base b::n =>
      if a == b then n else (Inverse a)::(Base b)::n
    | c, w => c::w
    end
  end.


Lemma FreeGroup_norm_e:
  FreeGroup_norm e = e.
Proof. done. Qed.

Lemma FreeGroup_norm_correct w:
  FreeGroup_norm w == w.
Proof.
elim: w => // c w /=.
case: (FreeGroup_norm w) => [eq|c' n eq].
  transitivity (([:: c]: FreeGroup) @ w); last done;
  case: c => s; by rewrite -eq neutral_right.
transitivity (([:: c]: FreeGroup) @ w); last done.
case: c eq => s; case: c' => s' <- //;
case Heq: (eq_op s s').
- move: Heq; move/eqP => <-. 
  transitivity (([:: Base s]: FreeGroup) @ (([::Inverse s]: FreeGroup) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
- by transitivity (([:: Base s]: FreeGroup) @ (([::Inverse s']: FreeGroup) @ n)); last done.
- move: Heq; move/eqP => <-. 
  transitivity (([:: Inverse s]: FreeGroup) @ (([::Base s]: FreeGroup) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
- by transitivity (([:: Inverse s]: FreeGroup) @ (([::Base s']: FreeGroup) @ n)); last done.
Qed.

Definition FreeGroup_dec_eq (w w': FreeGroup): bool :=
  (FreeGroup_norm w) == (FreeGroup_norm w').

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
move=> H.
elim: w3 => // c w3.
by case: c => s /= ->.
Qed.

Lemma FreeGroup_norm_rcons w c:
  FreeGroup_norm (rcons w c) = match c, rev (FreeGroup_norm w) with
  | Base a, Inverse b :: n =>
      if a == b then rev n else rcons (rcons (rev n) (Inverse b)) (Base a)
  | Inverse a, Base b :: n =>
      if a == b then rev n else rcons (rcons (rev n) (Base b)) (Inverse a)
  | c, n => rcons (rev n) c
  end.
(* TODO(reiniscirpons): Do this*)
Admitted.


Lemma FreeGroup_norm_rev w:
  FreeGroup_norm (rev w) = rev (FreeGroup_norm w).
Proof.
elim: w => // c w /= eq.
have <-: rev (FreeGroup_norm (rev w)) = FreeGroup_norm w.
  by rewrite eq revK.
  rewrite rev_cons FreeGroup_norm_rcons; case: c => {eq} a;
  case: (rev (FreeGroup_norm (rev w))) => [//|c l];
  case: c => // b.
- by rewrite !rev_cons.
- case: (a == b)%B; first done; by rewrite !rev_cons.
- case: (a == b)%B; first done; by rewrite !rev_cons.
- by rewrite !rev_cons.
Qed.

Lemma FreeGroup_norm_map_invl w:
  FreeGroup_norm (map invl w) = map invl (FreeGroup_norm w).
Proof.
elim: w => // c w /= ->.
case: c => /= a;
case: (FreeGroup_norm w) => // c' w' /=;
case: c' => b //;
case H: (a == b)%B; move => /=; by rewrite H.
Qed.

Lemma FreeGroup_norm_inv w:
  FreeGroup_norm (inv w) = inv (FreeGroup_norm w).
Proof. by rewrite /inv/=/inv_word/= -FreeGroup_norm_rev FreeGroup_norm_map_invl. Qed.

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
rewrite /relations/=; unfold free_group_relations;
rewrite mem_cat => /orP []; move/mapP => [a Henum [-> ->]];
apply /FreeGroup_norm_cat /FreeGroup_norm_cat_back => /=;
by rewrite eq_refl.
Qed.

Lemma eqprop_to_FreeGroup_dec_eq w w':
  (w == w') -> (FreeGroup_dec_eq w w').
Proof. by move=> eq; exact /eqP /FreeGroup_norm_unique. Qed.

Lemma FreeGroup_dec_eq_reflect w w':
  reflect (w == w') (FreeGroup_dec_eq w w').
Proof.
apply /(iffP idP) => eq.
- exact: FreeGroup_dec_eq_to_eqprop.
- exact: eqprop_to_FreeGroup_dec_eq.
Qed.
End FreeGroup.

Section FreeGroupUniversal.

Variable (Sigma: finType).
Variable (G: group).
Variable (f: Sigma -> G).

Definition FreeGroup_alphabet_extension:
  sigma (FreeGroup_presentation Sigma) -> G :=
    fun c =>
      match c with
      | Base a => f a
      | Inverse a => inv (f a)
      end.

Lemma FreeGroup_alphabet_extension_preserve_inv_on_sigma:
  forall (a: sigma (FreeGroup_presentation Sigma)),
    inv (FreeGroup_alphabet_extension a) == 
    (FreeGroup_alphabet_extension) (invl a).
Proof.
  case => [//|a]. by apply inv_involutive.
Qed.

Definition FreeGroup_universal_extension: (FreeGroup Sigma) -> G :=
      extension FreeGroup_alphabet_extension.

Lemma FreeGroup_alphabet_extension_preserve_relations:
  forall u v,
    (u, v) \in relations (FreeGroup_presentation Sigma) ->
    FreeGroup_universal_extension u == FreeGroup_universal_extension v.
Proof.
  move => u v; rewrite mem_cat; case/orP; move/mapP => [a _ [-> ->]];
  unfold FreeGroup_universal_extension;
  unfold extension; unfold FreeGroup_alphabet_extension;
  move => /=; rewrite associativity neutral_right.
  - by rewrite inverse_left; reflexivity.
  - by rewrite inverse_right; reflexivity.
Qed.

HB.instance Definition _ := isRelationPreservingMorphism.Build
  (FreeGroup_presentation Sigma) G
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

Notation "\hat f" := (FreeGroup_universal_extension f) (at level 5). 

