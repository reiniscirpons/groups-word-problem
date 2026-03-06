From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From Stdlib Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN Utils.


Record GWPArguments := {
  P : invertiblePresentationType;
  u : presented P;
  v : presented P;
}.
Definition GWP_uncurried args := word_problem (P args) (u args) (v args).

Section Reduction.

Variable A: Machine.
Variable z m: int.
Let n := size A.

Import PresentationNotations.
Import intZmod.

(* `encoding k` is `a_k = b^k a b^-k` *)
Definition encoding (k: int) : F2 := (power (`[b]: F2) k) @ `[a] @ (power (`[b]: F2) (oppz k)).

(* affine_state_encoding will be defined as `affine_state_encoding': group` later. *)
Definition affine_state_encoding' (s: State) := F2.

Section AffineStateEncoding.
Variable s: State.

Let affine_state_encoding' := affine_state_encoding' s.

HB.instance Definition _ := EqProp.copy affine_state_encoding' F2.
HB.instance Definition _ := Monoid.copy affine_state_encoding' F2.
HB.instance Definition _ := Group.copy affine_state_encoding' F2.

Definition affine_state_encoding_inj_letter (l: F2_sigma): F2 := match l with
  | a => encoding s.1
  | a_inv => inv (encoding s.1)
  | b => power (`[b]: F2) s.2
  | b_inv => inv (power (`[b]: F2) s.2)
  end.

Definition affine_state_encoding_inj (w: affine_state_encoding'): F2 :=
  prod (map affine_state_encoding_inj_letter (F2_norm w)).

Lemma affine_state_encoding_inj_injectivity_e (w: affine_state_encoding'):
  affine_state_encoding_inj w == e ->
  w == e.
Proof.
Admitted.

Lemma affine_state_encoding_inj_injectivity: forall (w w': affine_state_encoding'),
  affine_state_encoding_inj w == affine_state_encoding_inj w' ->
  w == w'.
Proof.
move=> w w'.
move=> /F2_dec_eq_reflect /eqP.
rewrite /affine_state_encoding_inj => eq.
apply /F2_dec_eq_reflect /eqP.
Admitted.

HB.instance Definition _ := isInjective.Build _ _ affine_state_encoding_inj affine_state_encoding_inj_injectivity.

Lemma affine_state_encoding_inj_preserve_equiv: forall w w',
  w == w' ->
  affine_state_encoding_inj w == affine_state_encoding_inj w'.
Proof.
move=> w w' /F2_dec_eq_reflect /eqP.
by rewrite /affine_state_encoding_inj => ->.
Qed.

Lemma affine_state_encoding_inj_preserve_e:
  affine_state_encoding_inj e == e.
Proof. by rewrite /affine_state_encoding_inj F2_norm_e. Qed.

Lemma F2_norm1 c:
  F2_norm ([:: c]: F2) = ([:: c]: F2).
Proof. by case: c. Qed.

Lemma prod_affine_state_encoding_inj_F2_norm w:
  prod [seq affine_state_encoding_inj_letter i | i <- F2_norm w] ==
  prod [seq affine_state_encoding_inj_letter i | i <- w].
Proof.
elim: w => // c w /=.
set norm := F2_norm w.
case: c => <-;
case: norm => // c w' /=;
case: c => //=;
by rewrite associativity ?inverse_left ?inverse_right.
Qed.

Lemma affine_state_encoding_inj_preserve_law w w':
  affine_state_encoding_inj (w @ w') == (affine_state_encoding_inj w) @ (affine_state_encoding_inj w').
Proof. by rewrite /affine_state_encoding_inj !prod_affine_state_encoding_inj_F2_norm /law/= map_cat prod_cat. Qed.

HB.instance Definition _ := isMonoidMorphism.Build _ _ affine_state_encoding_inj affine_state_encoding_inj_preserve_equiv affine_state_encoding_inj_preserve_e affine_state_encoding_inj_preserve_law.

Lemma affine_state_encoding_inj_inv (c: F2_sigma):
  (affine_state_encoding_inj_letter \o F2_invl) c ==
  (inv \o affine_state_encoding_inj_letter) c.
Proof.
case: c => // /=;
by rewrite inv_involutive.
Qed.

Lemma affine_state_encoding_inj_preserve_inv w:
  inv (affine_state_encoding_inj w) == affine_state_encoding_inj (inv w).
Proof.
rewrite /affine_state_encoding_inj prod_inv F2_norm_inv -map_comp !map_rev -map_comp.
set norm := F2_norm w.
elim: norm => // c norm /=.
rewrite !rev_cons !prod_rcons => ->.
by have /= <- := affine_state_encoding_inj_inv c.
Qed.

HB.instance Definition _ := isInvMorphism.Build _ _ affine_state_encoding_inj affine_state_encoding_inj_preserve_inv.

(* I don't really understand what's going on, but without these definitions the instance can't be defined. Weird.
  *)
Definition affine_state_encoding := affine_state_encoding': group.
Definition affine_state_encoding_inj' := affine_state_encoding_inj: injectiveMorphism affine_state_encoding F2.
HB.instance Definition _ := isSubgroup.Build F2 affine_state_encoding affine_state_encoding_inj'.

End AffineStateEncoding.

Definition encoding_p_state_encoding (s: State): affine_state_encoding s.
Proof. exact (`[a]: F2). Defined.

Definition power_b_state_encoding (s: State): affine_state_encoding s.
Proof. exact (`[b]: F2). Defined.

Definition encoding_state_k (s: State) (k: int) : affine_state_encoding s.
Proof.
exact: (
  (power (power_b_state_encoding s) k) @
  (encoding_p_state_encoding s) @
  (power (power_b_state_encoding s) (-k))
).
Defined.

Lemma encoding_state_k_value: forall s k,
  subgroup_inj (s:=(affine_state_encoding s)) (encoding_state_k s k) == encoding (s.1 + (s.2: int) * k).
Proof.
move=> s k /=.
rewrite /encoding.
have ->: oppz (s.1 + (s.2: int) * k) = -s.1 + (s.2: int) * (-k) by lia.
rewrite /encoding_state_k -[s.1 + _]addrC !poweradd !powermul.
rewrite !morphism_preserve_law/=.
transitivity (
  power (power ([:: b]: F2) s.2) k @ (encoding s.1) @ power (power ([:: b]: F2) s.2) (- k)
); last first.
  by rewrite !associativity.
rewrite !morphism_preserve_power.
rewrite /encoding_p_state_encoding /power_b_state_encoding /=.
by rewrite /affine_state_encoding_inj/= /law/= !cats0.
Qed.

Lemma encoding_free k:
  ~ (encoding k) \insubgroup (generatedSubgroup (fun x => exists k', (k != k') /\ (x == encoding k'))).
Proof.
Admitted.

Section IsoOfTransition.
Variable t: Transition.

(* the canonical morphism <a_p, b^q> -> <a_p', b^q'> *)
Definition iso_of_transition: (affine_state_encoding t.1) -> affine_state_encoding t.2 :=
  (* thanks to the well-chosen definition of `affine_state_encoding s` as F2, this is free *)
  id.

Lemma iot_preserve_equiv: forall x y, x == y -> iso_of_transition x == iso_of_transition y.
Proof. done. Qed.
Lemma iot_preserve_e: iso_of_transition e == e.
Proof. done. Qed.
Lemma iot_preserve_law: forall x y, iso_of_transition (x @ y) == (iso_of_transition x) @ (iso_of_transition y).
Proof. done. Qed.
Lemma iot_preserve_inv: forall x, iso_of_transition (inv x) == inv (iso_of_transition x).
Proof. done. Qed.

HB.instance Definition _ := isMonoidMorphism.Build _ _ iso_of_transition iot_preserve_equiv iot_preserve_e iot_preserve_law.
HB.instance Definition _ := isInvMorphism.Build _ _ iso_of_transition iot_preserve_inv.
End IsoOfTransition.
Arguments iso_of_transition: clear implicits.

Definition iso_of_transition_lm (t: Transition): local_morphism F2 :=
  {| lm_morphism := iso_of_transition t |}.

Let transitions_isos := map iso_of_transition_lm A.

Let F := HNNI_extension transitions_isos.
Let ts := HNNI_ts transitions_isos.

(* Hlike z = <a_z, t_1, ..., t_n> *)
Let Hlike_gens k := [:: (subgroup_inj (encoding k : HNNI_extension_base F2)) ] ++ ts.

(* H = <a_m, t_1, ..., t_n> *)
Let H_gens := Hlike_gens m.
Let H := finGeneratedSubgroup H_gens.

Definition encset_defining_property (P: int -> Prop) (w: F2) :=
  exists (z': int), (P z') /\ (w == encoding z').
(* [P] = {a_k, k \in P} *)
Let encoding_set P := generatedSubgroup (encset_defining_property P).

Lemma encoding_in_encset_char P k:
  (encoding k: HNNI_extension_base F2) \insubgroup (encoding_set P)
    ->
  P k.
Proof.
Admitted. (* independence + injectivity of encoding *)

Let K := encoding_set (fun k => equivalence_problem A k m).

Lemma inK_if_equiv_m:
    equivalence_problem A z m
      ->
    (encoding z) \insubgroup K.
Proof.
move=> E.
unshelve eexists.
  exists (encoding z).
  apply: igs_gen.
  by exists z; split.
done.
Qed.

Lemma encoding_equiv_m_if_inK (k: int):
    (encoding k) \insubgroup K
      ->
    equivalence_problem A k m.
Proof. exact: encoding_in_encset_char. Qed.

Lemma H'_invariance: forall i: 'I_(size transitions_isos),
    is_subgroup_stable (HNNI_nth_iso _ transitions_isos i) K.
Proof.
move=> i x Hx.
(* TODO: propriété "<a_p, b^q> inter [ZZ] = [p + qZ]" *) (* arith + properties of norma forms *)
Admitted.

(* K_extended = <K, t1, ..., tn> *)
Let K_extended := generatedSubgroup (HNNI_subgroup_ts_extension_gen _ transitions_isos K).

(* <K, t1, ..., tn> \cap G = K *)

(* G \subset <a_m, t1, ..., tn> *)
(* x \in F2 -> x \in <K, t1, ..., tn> *)
Lemma inK_if_in_Kextended_inter_F2: forall (x: F),
  x \insubgroup K_extended
    ->
  x \insubgroup (HNNI_extension_base F2)
    ->
  x \insubsubgroup[HNNI_extension_base F2] K.
Proof. exact: HNNI_stable_extended_inter_G_is_stable _ _ H'_invariance. Qed.

Lemma inKextended_if_inH (x: F):
  x \insubgroup H
    ->
  x \insubgroup K_extended.
Proof.
case; case=> [x' [x'_ast] /= ->].
elim: x'_ast x => /= [x Heq|x||].
- apply: in_subgroup_proper.
    exact: Heq.
  by exists e.
- rewrite /H_gens/Hlike_gens cat1s => Hx.
  case: (in_list_inv Hx) => [-> xF Heq|x_in_ts xF Heq].
    unshelve eexists.
      exists (subgroup_inj (encoding m: HNNI_extension_base F2)) => //.
      unshelve eexists (sa_gen (subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (s:=K) _)) _).
        exists (encoding m).
        apply: igs_gen.
        exists m; split=> //.
        exact: Relation_Operators.rst_refl.
      exact /steg_K.
    done.
    done.
  unshelve eexists.
    exists x.
    exact /igs_gen /steg_t.
  done.
- move=> ast_x IHx ast_y IHy x'' /=.
  case: (IHx (interpret_subgroup_ast ast_x))=> // x {IHx} Hx.
  case: (IHy (interpret_subgroup_ast ast_y))=> // y {IHy} Hy Heq.
  exists (x @ y).
  rewrite morphism_preserve_law. 
  move: Heq.
  by rewrite -Hx -Hy.
- move=> ast_x IHx x'' /=.
  case: (IHx (interpret_subgroup_ast ast_x)) => // x {IHx} Hx Heq.
  exists (inv x).
  by rewrite -morphism_preserve_inv -Heq -Hx.
Qed.

Definition dummyTransition: Transition.
Proof. split; refine (0, _); exists 1; lia. Qed.

Lemma nth_index_ord {T: eqType} default (x: T) (l: seq T):
  x \in l -> exists i: 'I_(size l), nth default l i = x.
Proof.
move=> /[dup] Hmem.
rewrite -index_mem => Hle.
exists (Ordinal Hle) => /=.
exact: nth_index.
Qed.

Lemma encoding_state_k_value_subgroup s k:
  encoding_state_k s k
    ==
  (power (power_b_state_encoding s) k) @ (encoding_p_state_encoding s) @ (power (power_b_state_encoding s) (-k)).
Proof. done. Qed.

Lemma iso_of_transition_image_power s1 s2:
  iso_of_transition (s1, s2) (power_b_state_encoding s1) == power_b_state_encoding s2.
Proof. done. Qed.

Lemma iso_of_transition_image_encoding_p s1 s2:
  iso_of_transition (s1, s2) (encoding_p_state_encoding s1) == encoding_p_state_encoding s2.
Proof. done. Qed.

Lemma iso_of_transition_image_encoding s1 s2 k:
  iso_of_transition (s1, s2) (encoding_state_k s1 k) == encoding_state_k s2 k.
Proof.
have -> := morphism_preserve_equiv (s:=iso_of_transition (s1, s2)) _ _ (encoding_state_k_value_subgroup s1 k).
rewrite (encoding_state_k_value_subgroup s2 k) !morphism_preserve_law.
rewrite -(iso_of_transition_image_encoding_p s1 s2).
(* at this point everything is so mysteriously broken that these don't rewrite directly anymore. woah *)
have := power_proper k (iso_of_transition_image_power s1 s2).
have := power_proper (- k) (iso_of_transition_image_power s1 s2).
have := morphism_preserve_power (iso_of_transition (s1, s2)) (power_b_state_encoding s1) k.
have := morphism_preserve_power (iso_of_transition (s1, s2)) (power_b_state_encoding s1) (-k).
move=> /= -> -> -> ->.
done.
Qed.

Let T := finGeneratedSubgroup ts.

Lemma transA_implies_conjugateT s1 s2 x y:
  transitionStep A (s1, s2) x y ->
  exists (t_prod: T),
    (subgroup_inj (s:=HNNI_extension_base F2) (encoding x))
      ==
    (subgroup_inj (s:=T) t_prod) @ (subgroup_inj (s:=HNNI_extension_base F2) (encoding y)) @ inv (subgroup_inj (s:=T) t_prod).
Proof.
case: s1 => [p q]; case: s2 => [p' q'].
case=> inA [k /andP [/eqP -> /eqP ->]].
move: inA => /(nth_index_ord dummyTransition).
have ->: size A = size transitions_isos.
  by rewrite /transitions_isos size_map.
case=> i Hi.

have /= := iso_representation _ transitions_isos i.

have ->: HNNI_nth_iso _ transitions_isos i = iso_of_transition_lm ((p, q), (p', q')).
  rewrite /HNNI_nth_iso /transitions_isos (nth_map dummyTransition) ?Hi //.
  have := ltn_ord i.
  rewrite /transitions_isos/=.
  by have <- := size_map iso_of_transition_lm A.

set t := tnth ts i.

move=> /(_ (encoding_state_k (p, q) k)) Heq.

unshelve eexists.
  exists (inv t).
  apply /igs_inv /igs_gen.
  rewrite /t (tnth_nth e).
  apply: nth_in_list.
  by rewrite size_tuple.
simpl.
move: Heq.
have ->: iso_of_transition_lm (p, q, (p', q')) (encoding_state_k (p, q) k) =
         iso_of_transition (p, q, (p', q')) (encoding_state_k (p, q) k) by done.
rewrite iso_of_transition_image_encoding !encoding_state_k_value /= => ->.
by rewrite !associativity inverse_right neutral_left -!associativity inverse_left neutral_right.
Qed.

Lemma equiv_implies_conjugateT u v:
  equivalence_problem A u v ->
  exists (t_prod: T),
    (subgroup_inj (s:=HNNI_extension_base F2) (encoding u))
      ==
    (subgroup_inj (s:=T) t_prod) @ (subgroup_inj (s:=HNNI_extension_base F2) (encoding v)) @ inv (subgroup_inj (s:=T) t_prod).
Proof.
move=> Heq; dependent induction Heq.
- case: H0 => [[[p q] [p' q']]].
  exact: transA_implies_conjugateT.
- exists e => /=.
  by rewrite inv_e neutral_left neutral_right.
- case: IHHeq => // t_prod' x_prod.
  exists (inv t_prod').
  by rewrite x_prod !associativity inverse_right neutral_left -!associativity inverse_left neutral_right.
- case: IHHeq1 => // t_prod1 u_eq.
  case: IHHeq2 => // t_prod2 v0_eq.
  exists (t_prod1 @ t_prod2).
  rewrite [subgroup_inj (s:=T) (t_prod1 @ t_prod2)]morphism_preserve_law.
  by rewrite inverse_law u_eq v0_eq !associativity.
Qed.

Lemma equiv_x_y_implies_encoding_in_ts_subgroup x y:
  equivalence_problem A x y
    ->
  (subgroup_inj (s:=HNNI_extension_base F2) (encoding x)) \insubgroup (finGeneratedSubgroup (Hlike_gens y)).
Proof.
move=> /equiv_implies_conjugateT [prod eq].

have ?: in_generated_subgroup (in_list^~ (Hlike_gens y)) (subgroup_inj (s:=T) prod).
  clear eq.
  case: prod => [t [ast]] /=.
  elim: ast t => /= [t ?|gen gen_in_gens t ?|ast1 IH1 ast2 IH2 prod|ast IH inv].
  - by exists (sa_e _).
  - unshelve eexists.
      apply /sa_gen /in_tail.
        exact: gen_in_gens.
      done.
  - case: (IH1 (interpret_subgroup_ast ast1)) => // ast1' eq1.
    case: (IH2 (interpret_subgroup_ast ast2)) => // ast2' eq2.
    exists (sa_law ast1' ast2').
    by rewrite /= -eq1 -eq2.
  - case: (IH (interpret_subgroup_ast ast)) => // ast' eq.
    exists (sa_inv ast').
    by rewrite /= -eq.

unshelve eexists.
  exists (((subgroup_inj (s:=T) prod) @ subgroup_inj (s:=HNNI_extension_base F2) (encoding y)) @ inv (subgroup_inj (s:=T) prod)).
  apply /igs_law.
    apply /igs_law => //.
    exact /igs_gen /in_head.
  exact /igs_inv.
by rewrite eq.
Qed.

Lemma encoding_inH_if_inK (k: int):
  ((encoding k) \insubgroup K)
    ->
  ((subgroup_inj (s:=HNNI_extension_base F2) (encoding k)) \insubgroup H).
Proof. by move=> /encoding_equiv_m_if_inK /equiv_x_y_implies_encoding_in_ts_subgroup. Qed.

Lemma inK_if_inH (x: F2):
  ((subgroup_inj (s:=HNNI_extension_base F2) x) \insubgroup H)
    ->
  (x \insubgroup K).
Proof.
move=> /inKextended_if_inH inKextended.
case: (inK_if_in_Kextended_inter_F2 inKextended) => [|xK HxK].
  by exists x.
exists xK.
exact /injectivity_property /HxK.
Qed.

Let E_presentation := HNNSG_extension_presentation H_gens.
Let E := presented E_presentation.
Let t := HNNSG_t H_gens.

Lemma Eeq_if_inH: forall x : F,
   x \insubgroup H
     ->
   (subgroup_inj (s:=HNNSG_extension_base F) x) @ t
     ==
   (t @ subgroup_inj (s:=HNNSG_extension_base F) x).
Proof. exact: HNNSG_subgroup_characterization. Qed.

Lemma inH_if_Eeq: forall x : F,
   (subgroup_inj (s:=HNNSG_extension_base F) x) @ t
     ==
   (t @ subgroup_inj (s:=HNNSG_extension_base F) x)
     ->
   x \insubgroup H.
Proof. exact: HNNSG_subgroup_characterization'. Qed.

Definition reduction_output : GWPArguments := {|
  P := E_presentation;
  (* (encoding z) @ t *)
  u := (subgroup_inj (s:=HNNSG_extension_base F) (subgroup_inj (s:=HNNI_extension_base F2) (encoding z))) @ t;
  (* t @ (encoding z) *)
  v := t @ (subgroup_inj (s:=HNNSG_extension_base F) (subgroup_inj (s:=HNNI_extension_base F2) (encoding z)));
|}.

End Reduction.

Lemma novikov_bool_reduction : equivalence_problem_uncurried ⪯ GWP_uncurried.
Proof.
exists (fun '(A, z, m) => reduction_output A z m).
move=> [] [A z] m.
rewrite /equivalence_problem_uncurried /GWP_uncurried; split.
- move=> /inK_if_equiv_m ?.
  exact /Eeq_if_inH /encoding_inH_if_inK.
- move=> /inH_if_Eeq /inK_if_inH.
  exact: encoding_equiv_m_if_inK.
Qed.

Theorem novikov_boone : undecidable GWP_uncurried.
Proof.
apply: (undecidability_from_reducibility equivalence_problem_undecidable).
exact: novikov_bool_reduction.
Qed.
