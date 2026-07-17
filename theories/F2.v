From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq fintype choice ssrnat all_algebra.
From mathcomp Require Import ring lra zify.
Require Import Setoid Morphisms.
From Stdlib Require Import Btauto.

From GWP Require Import Presentation Equivalence EquivalenceAlgebra.

Import PresentationNotations.

Inductive InverseAlphabet (Sigma: eqType) :=
| Base: Sigma -> InverseAlphabet Sigma
| Inverse: Sigma -> InverseAlphabet Sigma.
Arguments Base {_}.
Arguments Inverse {_}.

Definition inverse_alphabet_map {Sigma Gamma: eqType} (f: Sigma -> Gamma):
  InverseAlphabet Sigma -> InverseAlphabet Gamma :=
    fun a =>
      match a with
      | Base a' => Base (f a')
      | Inverse a' => Inverse (f a')
      end.

Section InverseAlphabetEqType.
Context {Sigma: eqType}.

Definition InverseAlphabet_eq (u v: InverseAlphabet Sigma) :=
  match (u, v) with
  | (Base a, Base b) => (a == b)%B
  | (Inverse a, Inverse b) => (a == b)%B
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
Context {Sigma: countType}.

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
Context {Sigma: finType}.

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
  [:: c; FreeGroup_invl c] \mod FGP == [::] \mod FGP.
Proof.
  move=> c; apply: reduction_rule; case: c => a;
  rewrite /relations /= /free_group_relations mem_cat; apply /orP.
  - left; apply/mapP; exists a => [|//]; by apply mem_enum.
  - right; apply/mapP; exists a => [|//]; by apply mem_enum.
Qed.

Lemma FreeGroup_invl_right : forall c: sigma FGP,
  [:: FreeGroup_invl c; c] \mod FGP == [:: ] \mod FGP.
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
  | [::] => [:: ] \mod FGP
  | c::w' => match (FreeGroup_norm w') with
    | [::] => [:: c] \mod FGP
    | d::n =>
      if (c == invl d)%B then n
      else c::(d::n)
    end
  end.

Lemma FreeGroup_norm_e:
  FreeGroup_norm e = e.
Proof. done. Qed.

Lemma FreeGroup_norm_1: forall (c: sigma FGP),
  FreeGroup_norm ([:: c] \mod FGP) = ([:: c] \mod FGP).
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
  | [::] => [:: c] \mod FGP
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

Global Instance : Proper (eq ==> Logic.eq) FreeGroup_norm.
Proof.
  by move => x y; move/FreeGroup_norm_unique => ->.
Qed.


Lemma FreeGroup_norm_power1: forall c n,
  FreeGroup_norm (power ([:: c] \mod FGP) n) = power ([:: c] \mod FGP) n.
Proof.
  (*move => c; elim => [//||] [//|n IH].*)
  (* TODO: Why does it not allow me to do this rewrite despite FreeGroup_norm
           being Proper? *)
  (*- apply/eqP; rewrite {1}powerS.*)
  move => c; case; elim/nat_pairs_ind => [//|//|n IH1 _].
  - rewrite !powerS /= {}IH1; case: n; by case: c.
  - by case: c.
  - move: IH1; rewrite !powerP => /= -> /=; by case: c.
Qed.

Lemma FreeGroup_norm_power2': forall x y (n: nat) m,
  let xy :=  ([:: x; y] \mod FGP) in
  let xnym := 
    ((power ([:: x] \mod FGP) n) @ (power ([:: y] \mod FGP)) m) in
      x != y ->
      FreeGroup_norm xy = xy ->
      FreeGroup_norm xnym = xnym.
Proof.
  move => x y n m xy xnym;
  rewrite /xy /xnym => {xy xnym}.
  move: n m; elim/nat_pairs_ind => [||n IH1 IH2] m Hneq H.
  - by rewrite power0 -cat_law /= FreeGroup_norm_power1.
  - case: m; elim/nat_pairs_ind => [//|//|m IH1 IH2];
    rewrite {2}[power]lock /= -lock FreeGroup_norm_power1.
  -- move: H Hneq; case: ifP => [/eqP -> /=| //];
    by rewrite eq_refl.
  1-3: rewrite /= invlK; move: Hneq; by case: ifP.
  - rewrite powerS [power]lock /= -lock IH2 => [|//|//].
    rewrite powerS /=; case: ifP => [|//]; by case: x IH1 IH2 Hneq H.
Qed.

Lemma FreeGroup_norm_power2: forall x y n m,
  let xy :=  ([:: x; y] \mod FGP) in
  let xnym := 
    ((power ([:: x] \mod FGP) n) @ (power ([:: y] \mod FGP)) m) in
      x != y ->
      FreeGroup_norm xy = xy ->
      FreeGroup_norm xnym = xnym.
Proof.
  move => x y n m xy xnym;
  rewrite /xy /xnym => {xy xnym}.
  case: n => n Heq Hnorm.
  - by rewrite FreeGroup_norm_power2'.
  - case: m => m;
    rewrite !NegzE; last first.
  -- rewrite {1}power_inv {1}power_inv -inverse_law.
     rewrite FreeGroup_norm_inv FreeGroup_norm_power2'.
  --- by rewrite !power_inv_word /inv /= inv_word_cat.
  --- by apply /eqP; symmetry; apply/eqP.
  --- by move/(f_equal rev): Hnorm; rewrite -FreeGroup_norm_rev.
  -- rewrite -[FreeGroup_norm _]revK -{2}[_ @ _]revK.
     apply/(f_equal rev).
     rewrite -FreeGroup_norm_rev rev_cat !power_rev1 FreeGroup_norm_power2' => [//||].
  --- by apply /eqP; symmetry; apply/eqP.
  --- by move/(f_equal rev): Hnorm; rewrite -FreeGroup_norm_rev.
Qed.


End FreeGroup.
Arguments FreeGroup_norm {_}.

Section FreelyReduced.

Variable (Sigma: finType).

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
  freely_reduced (power ([:: c] \mod (FGP Sigma)) n).
Proof.
  by move => c n; rewrite freely_reduced_correct FreeGroup_norm_power1.
Qed.

(* freely reduced lemmas *)

Lemma freely_reducedW (x y : FreeGroup Sigma) (fry: freely_reduced y) (sub: infix x y):
  freely_reduced x.
Proof.
  rewrite /freely_reduced /=.
  move => p s c.
  move => Habs.
  move/infixP: sub => [s0 [s0' eqy]].
  rewrite Habs -[(p ++ [:: invl (c: sigma(FGP Sigma)),  c  & s]) ++ s0']catA !cat_cons catA in eqy.
  have hcontradict: y <> (s0 ++ p) ++ [:: invl (c: sigma(FGP Sigma)), c & s ++ s0'].
    rewrite /freely_reduced in fry.
    apply (fry (s0 ++ p) (s ++ s0') c).
  contradiction.
Qed.

Lemma freely_reduced_cat_overlap (q r s: FreeGroup Sigma) (frqr: freely_reduced (q ++ r)) (frrs: freely_reduced (r ++ s)) (Hsz: (size r >= 1)%N):
  freely_reduced (q ++ r ++ s).
Proof.
  rewrite /freely_reduced /=.
  move => a b c habs.
  case: (boolP (size a < size q)%N) => [Hlt | /negPf Hf]; last first.
  + have sfx: suffix [:: invl (c :> sigma (FGP Sigma)),  c  & b] (r ++ s).
      have eqsz: (size a - size q = (size (r ++ s) - size [:: invl (c: sigma (FGP Sigma)),  c  & b]))%N.
        move/(f_equal size) in habs; rewrite !size_cat in habs.
        move/(f_equal (fun n => subn n (size q))) in habs.
        rewrite -addnCBA in habs.
        rewrite subnn addn0 in habs.
        move/(f_equal (fun n => subn n (size [:: invl (c:>sigma (FGP Sigma)),  c  & b]))) in habs.
        have eqswap : (size a + size [:: invl (c:> sigma (FGP Sigma)), c & b] - size q - size [:: invl (c: sigma (FGP Sigma)), c & b] 
          = size a - size q)%N.
          rewrite subnAC -addnBA.
          by rewrite subnn addn0.
          by done.
        rewrite eqswap in habs.
        by rewrite size_cat; symmetry.
        by done.

      move/(f_equal (drop (size a))) in habs.
      rewrite [drop (size a) (a ++ [:: invl (c: sigma (FGP Sigma)),  c  & b])]drop_size_cat in habs => //.
      by rewrite drop_cat Hf eqsz in habs; move/eqP in habs; rewrite -suffixE in habs.

    move/suffixP: sfx => [z eqrs].
    rewrite /(freely_reduced) in frrs; move: (frrs z b c) => frrs'.
    rewrite eqrs in frrs'.
    contradiction.
  + have prfx: prefix (a ++ [:: invl (c:> sigma (FGP Sigma));  c]) (q ++ r).
      have lesz: (size (a ++ [:: invl (c:> sigma (FGP Sigma));  c]) <= size (q ++ r))%N.
        rewrite !size_cat /=.
        rewrite addn2 -addn1.
        by apply: leq_add.
      rewrite prefixE.
      move/(f_equal (take (size (a ++ [:: invl (c:> sigma (FGP Sigma));  c])))) in habs.
      rewrite catA take_cat in habs.
      case: (boolP ((size (a ++ [:: invl (c :> sigma ((FGP Sigma)));  c]) < size (q ++ r))%N)) => [Ht | Hf].
      + rewrite ifT // in habs.
        have eqtake: take (size (a ++ [:: invl (c :> sigma ((FGP Sigma)));  c])) (a ++ [:: invl (c :> sigma ((FGP Sigma))),  c  & b]) = (a ++ [:: invl (c :> sigma ((FGP Sigma)));  c]).
          apply/eqP; rewrite -prefixE.
          change (a ++ [:: invl (c :> sigma ((FGP Sigma))), c & b]) with (a ++ [:: invl (c :> sigma ((FGP Sigma))); c] ++ b).
          by rewrite catA prefix_prefix.
        apply/eqP.
        by rewrite eqtake in habs.
      + move/negPf in Hf.
        rewrite ifF // in habs.
        move/negP in Hf.
        rewrite ltnNge in Hf.
        move/negP in Hf. rewrite negbK in Hf.
        have eq: (size (q ++ r) = size (a ++ [:: invl (c: sigma (FGP Sigma));  c]))%N.
          by apply/eqP; rewrite eqn_leq Hf lesz.
        rewrite eq subnn take0 cats0 in habs.
        have eqtake: take (size (a ++ [:: invl (c :> sigma ((FGP Sigma)));  c])) (a ++ [:: invl (c :> sigma ((FGP Sigma))),  c  & b]) = (a ++ [:: invl (c :> sigma ((FGP Sigma)));  c]).
          apply/eqP; rewrite -prefixE.
          change (a ++ [:: invl (c :> sigma ((FGP Sigma))), c & b]) with (a ++ [:: invl (c :> sigma ((FGP Sigma))); c] ++ b).
          by rewrite catA prefix_prefix.
        rewrite eqtake in habs.
        by rewrite habs take_size.
    move/prefixP: prfx => [z eqz].
    rewrite /freely_reduced in frqr.
    move: (frqr a z c) => habs'.
    by rewrite eqz catA in habs'.
Qed.

Fixpoint freely_reduced_helper (x: FreeGroup Sigma): bool :=
  match x with
  | [::] => true
  | [:: c & y] =>
    match y with
    | [::] => true
    | [:: d & z] => (c != d) && freely_reduced_helper y
    end
  end.


Lemma freely_reduced_helper_cons2: forall c d x,
  freely_reduced_helper [:: c, d & x] =
  (c != d) && freely_reduced_helper x &&
  freely_reduced_helper [:: d & x].
Proof.
  move => c d x; elim: x c d => [c d/=|e x IH c d];
    first by case: (c != d).
  rewrite IH /=; case: x {IH} => [|f x] /=;
    by btauto.
Qed.

Lemma freely_reduced_helperP: forall x,
  reflect
    (forall p q c d, p ++ [:: c; d] ++ q = x -> c != d)
    (freely_reduced_helper x).
Proof.
  move => x; apply/(iffP idP).
  - elim: x => [_ [//|//]|c [_ _ [//|? [//|//]]|d x IH]].
    rewrite freely_reduced_helper_cons2 =>
      /andP [/andP [Hcd _ /IH {}IH]] [|e y] q c' d' /=;
      first by move => [-> -> _].
    by case => [_ /IH].
  - elim: x => [//|c x IH H /=];
    case: x IH H => [//|d x IH H].
    apply/andP; split.
  -- by apply H with [::] x.
  -- apply IH => p q c' d' Hpcdq.
     apply H with (c::p) q => /=.
     by rewrite Hpcdq.
Qed.

Lemma freely_reduced_power
    (w: FreeGroup Sigma)
    (ks: seq int)
    (Hsize: (size w == size ks)%B)
    (Hn0: all (fun k => k != 0) ks)
    (Hdistinct: freely_reduced_helper w):
  (w == FreeGroup_norm w)%B ->
  freely_reduced (prod (map (fun '(x, k) => power (`[x]_(FGP Sigma)) k) (zip w ks))).
Proof.
  move/eqP in Hsize.
  move/allP in Hn0.
  move/freely_reduced_helperP in Hdistinct.
  elim: w ks Hn0 Hsize Hdistinct => [|x t IH].
  - move => ks Hn0 Q; rewrite /= in Q; symmetry in Q; move/size0nil in Q; rewrite {}Q.
    by rewrite /= => _ _; apply freely_reduced_nil.
  - move => [|k kt] Hn0.
  --- by done.
  - case: t IH => [|y t'] IH Hsize Hdistinct.
  --- rewrite /= in Hsize; case: Hsize => Hsize; symmetry in Hsize; move/size0nil in Hsize; rewrite Hsize.
      rewrite /= !freely_reduced_correct -{1}cat_law cats0 neutral_right.
      by rewrite FreeGroup_norm_power1.
  --- case: kt Hn0 Hsize => [|k' kt'] Hn0 Hsize /eqP /freely_reduced_correct frw.
      + by done.

      rewrite /= in Hsize; case: Hsize => Hsize.
      have frxy: freely_reduced (power ([:: x] \mod (FGP Sigma)) k @ power ([::y] \mod (FGP Sigma)) k').
        rewrite freely_reduced_correct.
        rewrite FreeGroup_norm_power2 //.
        by apply: (Hdistinct [::] t' x y).
        symmetry; rewrite -freely_reduced_correct; apply: (@freely_reducedW _ [:: x, y & t']) => //.
        by apply: prefix_infix.

        rewrite [power]lock /= -lock.
      pose ks' := [:: k' & kt'].
      have Hn0': forall k, k \in ks' -> k != 0.
        move => n inks'.
        apply: Hn0.
        change [:: k, k' & kt'] with ([:: k] ++ [:: k' & kt']).
        by rewrite mem_cat; apply/orP; right.
      have Hsize': size [:: y & t'] = size [:: k' & kt'].
        by rewrite /=; lia.
      have Hdistinct': forall p q x' y', p ++ [:: x'; y'] ++ q = y :: t' -> x' != y'.
        move => p q x' y' Heq.
        apply: (Hdistinct [::x & p] q).
        by rewrite /= Heq.

      have fryt: freely_reduced [::y & t'].
        apply: (@freely_reducedW _ [:: x, y & t']); first by apply: frw.
        apply/infixP; exists ([::x]); exists([::]).
        by rewrite cats0.
      move/freely_reduced_correct/eqP in fryt. 
      move: (IH [:: k' & kt'] Hn0' Hsize' Hdistinct' fryt) => frIH.
      rewrite [power]lock /= -lock in frIH.
      rewrite -cat_law in frIH; rewrite -cat_law.

      apply: freely_reduced_cat_overlap.
      by exact: frxy.
      by exact: frIH.

      apply: size0_power.
      apply: Hn0.
      rewrite (@mem_drop 1) //.
      by rewrite /= mem_head.
Qed.

End FreelyReduced.
Arguments freely_reduced {_}.
Arguments freely_reducedW {_}.

Section FreeGroupUniversal.

Context {Sigma: finType} {G: group}.
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
Arguments FreeGroup_universal_extension / !_.

Lemma FreeGroup_alphabet_extension_preserve_relations:
  forall u v,
    (u, v) \in relations (FGP Sigma) ->
    FreeGroup_universal_extension u == FreeGroup_universal_extension v.
Proof.
  move => u v; rewrite mem_cat; case/orP; move/mapP => [a _ [-> ->]] /=;
  rewrite associativity neutral_right.
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
Arguments FreeGroup_alphabet_extension {_ _} / _ _.
Arguments FreeGroup_universal_extension {_ _} _ / !_.
Notation "\hat f" := (FreeGroup_universal_extension f) (at level 5). 

Lemma hat_cons: forall (Sigma: finType) (G: group) (f: Sigma -> G)
  (a: sigma (FGP Sigma)) w,
  \hat f (a::w) = FreeGroup_alphabet_extension f a @ (\hat f w).
Proof. done. Qed.
