From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.

From GWP Require Import Presentation Equivalence EquivalenceAlgebra.

Import PresentationNotations.

Inductive F2_sigma : Type := a | a_inv | b | b_inv.

Definition F2_sigma_eq (u v: F2_sigma) := match (u, v) with
  | (a, a) | (a_inv, a_inv) | (b, b) | (b_inv, b_inv) => true
  | _ => false
  end.
Lemma F2_sigma_eqP : eq_axiom F2_sigma_eq.
Proof. by elim=> [] []; apply: (iffP idP). Qed.
HB.instance Definition _ := hasDecEq.Build F2_sigma F2_sigma_eqP.

HB.instance Definition _ := isPresentation.Build F2_sigma [::
    (pair [:: a; a_inv] [::]);
    (pair [:: b; b_inv] [::]);
    (pair [:: a_inv; a] [::]);
    (pair [:: b_inv; b] [::])
  ].

Notation F2 := (presented F2_sigma).

Definition F2_invl (c: F2_sigma) := match c with
  | a => a_inv
  | a_inv => a
  | b => b_inv
  | b_inv => b
  end.

Lemma F2_invl_left : forall c: F2_sigma, `[c; F2_invl c] == `[].
Proof. move=> c; apply: reduction_rule; by case: c. Qed.

Lemma F2_invl_right : forall c: F2_sigma, `[F2_invl c; c] == `[].
Proof. move=> c; apply: reduction_rule; by case: c. Qed.

HB.instance Definition _ := hasInvertibleLetters.Build F2_sigma F2_invl F2_invl_left F2_invl_right.

Fixpoint F2_norm (w: F2): F2 := match w with
  | [::] => [::]
  | c::w => match c, F2_norm w with
      | a, a_inv::n => n
      | b, b_inv::n => n
      | a_inv, a::n => n
      | b_inv, b::n => n
      | c, w => c::w
      end
  end.

Lemma F2_norm_e:
  F2_norm e = e.
Proof. done. Qed.

Lemma F2_norm_correct w:
  F2_norm w == w.
Proof.
elim: w => // c w /=.
case: (F2_norm w) => [eq|c' n eq].
  transitivity (([:: c]: F2) @ w); last done;
  by case: c; rewrite -eq.
transitivity (([:: c]: F2) @ w); last done.
case: c eq; case: c' => <- //.
- transitivity (([::a]: F2) @ (([::a_inv]: F2) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
- transitivity (([::a_inv]: F2) @ (([::a]: F2) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
- transitivity (([::b]: F2) @ (([::b_inv]: F2) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
- transitivity (([::b_inv]: F2) @ (([::b]: F2) @ n)); last done.
  by rewrite associativity inverse_left neutral_left.
Qed.

Definition F2_dec_eq (w w': F2): bool :=
  (F2_norm w) == (F2_norm w').

Lemma F2_refl p: F2_dec_eq p p.
Proof. by rewrite /F2_dec_eq. Qed.

Lemma F2_dec_eq_to_eqprop w w':
  (F2_dec_eq w w') -> (w == w').
Proof. by move=> eq; rewrite -[w]F2_norm_correct -[w']F2_norm_correct (eqP eq). Qed.

Lemma F2_norm_cat_back w1 w2 w3:
  F2_norm w1 = F2_norm w2 -> F2_norm (w3 @ w1) = F2_norm (w3 @ w2).
Proof.
move=> H.
elim: w3 => // c w3.
by case: c => /= ->.
Qed.

Lemma F2_norm_rcons_a w:
  F2_norm (rcons w a) = match rev (F2_norm w) with
  | a_inv :: n => rev n
  | n => rcons (rev n) a
  end.
Proof.
elim: w => // c w.
rewrite rcons_cons /= => ->.
case: c;
case: (F2_norm w) => //;
case=> n;
rewrite !rev_cons;
case: (rev n) => // c m /=;
rewrite -!rcons_cons;
by case: c; rewrite !rev_rcons // !rcons_cons.
Qed.

Lemma F2_norm_rcons_a_inv w:
  F2_norm (rcons w a_inv) = match rev (F2_norm w) with
  | a :: n => rev n
  | n => rcons (rev n) a_inv
  end.
Proof.
elim: w => // c w.
rewrite rcons_cons /= => ->.
case: c;
case: (F2_norm w) => //;
case=> n;
rewrite !rev_cons;
case: (rev n) => // c m /=;
rewrite -!rcons_cons;
by case: c; rewrite !rev_rcons // !rcons_cons.
Qed.

Lemma F2_norm_rcons_b w:
  F2_norm (rcons w b) = match rev (F2_norm w) with
  | b_inv :: n => rev n
  | n => rcons (rev n) b
  end.
Proof.
elim: w => // c w.
rewrite rcons_cons /= => ->.
case: c;
case: (F2_norm w) => //;
case=> n;
rewrite !rev_cons;
case: (rev n) => // c m /=;
rewrite -!rcons_cons;
by case: c; rewrite !rev_rcons // !rcons_cons.
Qed.

Lemma F2_norm_rcons_b_inv w:
  F2_norm (rcons w b_inv) = match rev (F2_norm w) with
  | b :: n => rev n
  | n => rcons (rev n) b_inv
  end.
Proof.
elim: w => // c w.
rewrite rcons_cons /= => ->.
case: c;
case: (F2_norm w) => //;
case=> n;
rewrite !rev_cons;
case: (rev n) => // c m /=;
rewrite -!rcons_cons;
by case: c; rewrite !rev_rcons // !rcons_cons.
Qed.

Lemma F2_norm_rev w:
  F2_norm (rev w) = rev (F2_norm w).
Proof.
elim: w => // c w /= eq.
have <-: rev (F2_norm (rev w)) = F2_norm w.
  by rewrite eq revK.
case: c => {eq}.
- rewrite rev_cons F2_norm_rcons_a.
  case: (rev (F2_norm (rev w))) => [//|c l].
  case: c => //;
  by rewrite !rev_cons.
- rewrite rev_cons F2_norm_rcons_a_inv.
  case: (rev (F2_norm (rev w))) => [//|c l].
  case: c => //;
  by rewrite !rev_cons.
- rewrite rev_cons F2_norm_rcons_b.
  case: (rev (F2_norm (rev w))) => [//|c l].
  case: c => //;
  by rewrite !rev_cons.
- rewrite rev_cons F2_norm_rcons_b_inv.
  case: (rev (F2_norm (rev w))) => [//|c l].
  case: c => //;
  by rewrite !rev_cons.
Qed.

Lemma F2_norm_map_invl w:
  F2_norm (map invl w) = map invl (F2_norm w).
Proof.
elim: w => // c w /= ->.
case: c => /=;
case: (F2_norm w) => // c' w' /=;
by case: c'.
Qed.

Lemma F2_norm_inv w:
  F2_norm (inv w) = inv (F2_norm w).
Proof. by rewrite /inv/=/inv_word/= -F2_norm_rev F2_norm_map_invl. Qed.

Lemma F2_norm_cat w1 w2 w3:
  F2_norm w1 = F2_norm w2 -> F2_norm (w1 @ w3) = F2_norm (w2 @ w3).
Proof.
rewrite -[w1 @ w3]revK -[w2 @ w3]revK.
rewrite ![F2_norm (rev (rev _))]F2_norm_rev => eq.
have -> //: F2_norm (rev (w1 @ w3)) = F2_norm (rev (w2 @ w3)).
rewrite /law/= !rev_cat; apply /F2_norm_cat_back.
by rewrite !F2_norm_rev eq.
Qed.

Lemma F2_norm_unique w w':
  w == w' -> F2_norm w = F2_norm w'.
Proof.
elim=> [[r1 r2] w1 w2|//|? ? _ -> //|? ? ? _ -> _ -> //].
rewrite /relations/= !inE => /orP [/eqP [-> ->]|/orP [/eqP [-> ->]|/orP [/eqP [-> ->]|/eqP [-> ->]]]];
exact /F2_norm_cat /F2_norm_cat_back.
Qed.

Lemma eqprop_to_F2_dec_eq w w':
  (w == w') -> (F2_dec_eq w w').
Proof. by move=> eq; exact /eqP /F2_norm_unique. Qed.

Lemma F2_dec_eq_reflect w w':
  reflect (w == w') (F2_dec_eq w w').
Proof.
apply /(iffP idP) => eq.
- exact: F2_dec_eq_to_eqprop.
- exact: eqprop_to_F2_dec_eq.
Qed.
