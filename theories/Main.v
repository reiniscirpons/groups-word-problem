From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From Stdlib Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN.

(* TODO: factor out those proof into a separate file *)
Lemma catE {T: Type} (x y: seq T): x ++ y = (x ++ y)%list.
Proof. by elim: x => [//|a l /= ->]. Qed.

(* + LM2.sizeE *)

Lemma nthE {T: Type} (default: T) (l: seq T) k:
  nth default l k = ListDef.nth k l default.
Proof.
elim: k l => [l|k IH l].
  by case: l.
elim: l k IH => [k|a l IHk k IHl /=].
  by case: k.
exact: IHl.
Qed.

(*
HB.factory Record isMorphismBase (G: group) (gens gens': seq G) (map: G -> G) := {
  mb_preserve_eq x y: x == y -> map x == map y;
  mb_preserve_e: map e == e;
  mb_preserve_gen x: List.In x gens -> List.In (map x) gens'
}.

HB.builders Context G gens gens' map of isMorphismBase G gens gens' map.

Let H := finGeneratedSubgroup gens.
Let H' := finGeneratedSubgroup gens'.

Definition map_extended (x: H): H'.
Proof.
case: x => [point_x] Hx.
induction Hx.
- exists (map x).
  exact /igs_gen /mb_preserve_gen.
- exact: e.
- exact: (IHHx1 @ IHHx2).
- exact: (inv IHHx).
Defined.

Lemma extension_preserve_e: map_extended e == e.
Proof. done. Qed.

Lemma extension_preserve_law x y: map_extended (x @ y) == (map_extended x) @ (map_extended y).
Proof. done. Qed.

Lemma extension_preserve_inv x: map_extended (inv x) == inv (map_extended x).
Proof. done. Qed.

Lemma extension_preserve_equiv' x:
  x == e -> map_extended x == e.
Proof.
Admitted.
(*
case: x => x x_in_subgroup Heq.
elim: x_in_subgroup Heq.
- move=> x' x'_in_gens /=.
  rewrite /eq/=/subgroupby_eq/=.
  rewrite -{2}map_preserve_e.
  exact: map_preserve_eq.
- by rewrite /eq/=/subgroupby_eq/=.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' y' x'_in_gens IHx'.
  move=> y'_in_gens IHy'.
  move=> Heq.
  transitivity (
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
      @
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) y' y'_in_gens))
  ); first done.
  rewrite IHx' //.
  rewrite IHy' //.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' x'_in_gens IHx' Hinvx'.
  transitivity (
    inv (
      subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
        (map_extended
          (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
    )
  ); first done.
  by rewrite -inv_e IHx' // -inv_e -[x']inv_involutive Hinvx'.
Admitted.
*)

Lemma extension_preserve_equiv x y:
  x == y -> map_extended x == map_extended y.
Proof.
have Heq: x @ (inv y) == e -> (map_extended x) @ (map_extended (inv y)) == e; last first.
  move=> H1.
  have {}H1: x @ (inv y) == e by rewrite H1 inverse_left.
  move: Heq => /(_ H1) {H1}.
  rewrite extension_preserve_inv => H1.
  transitivity (((map_extended x) @ (inv (map_extended y))) @ (map_extended y)).
    by rewrite -associativity inverse_right neutral_right.
  by rewrite H1 neutral_left.
move=> Heq.
rewrite -extension_preserve_law.
exact: extension_preserve_equiv'.
Qed.

HB.instance Definition _ := isMonoidMorphism.Build H H' map_extended extension_preserve_equiv extension_preserve_e extension_preserve_law.
HB.instance Definition _ := isInvMorphism.Build H H' map_extended extension_preserve_inv.

HB.end.
*)

(*
Section GeneratedSubgroupNormalizer.
Variable G: group.
Variable P: G -> Prop.

Hypothesis dec_eq_G: G -> G -> bool.
Hypothesis dec_eq_G_reflect: forall (x y: G), reflect (x == y) (dec_eq_G x y).

Inductive subgroup_element_ast: Type :=
  | sea_e : subgroup_element_ast
  | sea_mul_gen : forall gen: G, P gen -> subgroup_element_ast -> subgroup_element_ast
  | sea_mul_inv_gen : forall gen: G, P gen -> subgroup_element_ast -> subgroup_element_ast.

Fixpoint simplify_subgroup_ast (ast: subgroup_element_ast) := match ast with
  | sea_e => sea_e
  | sea_mul_gen gen Pgen ast => (match simplify_subgroup_ast ast with
      | sea_mul_inv_gen gen' Pgen' ast =>
          if dec_eq_G gen gen'
          then ast
          else sea_mul_gen Pgen (sea_mul_inv_gen Pgen' ast)
      | ast => sea_mul_gen Pgen ast
      end
      )
  | sea_mul_inv_gen gen Pgen ast => (match simplify_subgroup_ast ast with
      | sea_mul_gen gen' Pgen' ast =>
          if dec_eq_G gen gen'
          then ast
          else sea_mul_inv_gen Pgen (sea_mul_gen Pgen' ast)
      | ast => sea_mul_inv_gen Pgen ast
      end
      )
  end.

Fixpoint interp (ast: subgroup_element_ast) := match ast with
  | sea_e => e
  | sea_mul_gen gen Pgen ast => gen @ (interp ast)
  | sea_mul_inv_gen gen Pgen ast => (inv gen) @ (interp ast)
  end.

Lemma simplify_preserve_interp: forall ast,
    interp ast == interp (simplify_subgroup_ast ast).
Proof.
elim => [//|gen Pgen ast /= ->|gen Pgen ast /= ->].
- set l := simplify_subgroup_ast ast.
  case: l => //.
  move=> gen' Pgen' ast'.
  have /orP [/[dup] /dec_eq_G_reflect H -> /=|/negbTE -> //] := orbN (dec_eq_G gen gen').
  by rewrite associativity H inverse_left neutral_left.
- set l := simplify_subgroup_ast ast.
  case: l => //.
  move=> gen' Pgen' ast'.
  have /orP [/[dup] /dec_eq_G_reflect H -> /=|/negbTE -> //] := orbN (dec_eq_G gen gen').
  by rewrite associativity H inverse_right neutral_left.
Qed.

(*
Lemma preserve_eq_interp_e: forall ast,
  (interp ast) == e -> (simplify_subgroup_ast ast) = sea_e.
Proof.
Admitted.

Fixpoint sea_law (ast ast': subgroup_element_ast) := match ast with
  | sea_e => ast'
  | sea_mul_gen gen Pgen ast => sea_mul_gen Pgen (sea_law ast ast')
  | sea_mul_inv_gen gen Pgen ast => sea_mul_inv_gen Pgen (sea_law ast ast')
  end.

Lemma sea_law_correct ast ast': interp (sea_law ast ast') == (interp ast) @ (interp ast').
Proof.
elim: ast => [/=|gen Pgen ast /= ->|gen Pgen ast /= ->].
- by rewrite neutral_left.
- by rewrite associativity.
- by rewrite associativity.
Qed.

Fixpoint sea_inv (ast: subgroup_element_ast) := match ast with
  | sea_e => sea_e
  | sea_mul_gen gen Pgen ast => sea_law (sea_inv ast) (sea_mul_inv_gen Pgen sea_e)
  | sea_mul_inv_gen gen Pgen ast => sea_law (sea_inv ast) (sea_mul_gen Pgen sea_e)
  end.

Lemma sea_mul_gen_is_sea_law gen (Pgen: P gen) ast:
  simplify_subgroup_ast (sea_mul_gen Pgen ast)
    =
  simplify_subgroup_ast (sea_law (sea_mul_gen Pgen sea_e) ast).
Admitted.

Lemma sea_law_introduce_simplify ast ast':
  simplify_subgroup_ast (sea_law ast ast') = simplify_subgroup_ast (sea_law (simplify_subgroup_ast ast) (simplify_subgroup_ast ast')).
Proof.  

Lemma sea_law_associativity ast ast' ast'':
  simplify_subgroup_ast (sea_law (sea_law ast ast') ast'')
    =
  simplify_subgroup_ast (sea_law ast (sea_law ast' ast'')).
Proof.
elim: ast ast' ast'' => [//|gen Pgen ast IH ast' ast''|gen Pgen ast IH ast' ast''].

Admitted.

Lemma simplify_sea_law_mul_gen_left gen (Pgen: P gen) ast ast':
  simplify_subgroup_ast (sea_law (sea_mul_gen Pgen ast) ast')
    = 
  simplify_subgroup_ast (sea_mul_gen Pgen (sea_law ast ast')).
Proof.
Admitted.

Lemma simplify_sea_law_mul_inv_gen_left gen (Pgen: P gen) ast ast':
  simplify_subgroup_ast (sea_law (sea_mul_inv_gen Pgen ast) ast')
    = 
  simplify_subgroup_ast (sea_mul_inv_gen Pgen (sea_law ast ast')).
Proof.
Admitted.

Lemma simplify_sea_law_right_e ast:
  simplify_subgroup_ast (sea_law ast sea_e) = simplify_subgroup_ast ast.
Proof.
elim: ast => [//|gen Pgen ast IH|gen Pgen ast IH].
- by rewrite simplify_sea_law_mul_gen_left /= IH.
- by rewrite simplify_sea_law_mul_inv_gen_left /= IH.
Qed.

Lemma simplify_sea_inv ast:
  simplify_subgroup_ast (sea_inv ast) = sea_e
    ->
  simplify_subgroup_ast ast = sea_e.
Proof.
elim: ast => [//|gen Pgen ast IH|].
- 
Admitted.

Lemma simplify_sea_law_comm ast ast':
  simplify_subgroup_ast (sea_law ast ast') = sea_e
    ->
  simplify_subgroup_ast (sea_law ast' ast) = sea_e.
Proof.
elim: ast ast' => [/= ast'|gen Pgen ast IH ast'|gen Pgen ast IH ast' H].
- by rewrite simplify_sea_law_right_e.
- rewrite simplify_sea_law_mul_gen_left.
  rewrite 
- admit.
Admitted.

Lemma simplify_sea_law ast ast': 
  simplify_subgroup_ast (sea_law ast (sea_inv ast')) = sea_e
    ->
  simplify_subgroup_ast ast = simplify_subgroup_ast ast'.
Proof.
elim: ast ast' => [/= ast'||].
- admit.
- move=> gen Pgen ast IH ast' H.
  have := IH.
Admitted.

Lemma sea_inv_correct ast: interp (sea_inv ast) == inv (interp ast).
Proof.
elim: ast => [/=|gen Pgen ast /=|gen Pgen ast /=].
- by rewrite inv_e.
- by rewrite sea_law_correct inverse_law /= neutral_right => ->.
- by rewrite sea_law_correct inverse_law /= neutral_right inv_involutive => ->.
Qed.
*)

Lemma preserve_eq_interp: forall ast ast',
  (interp ast) == (interp ast') -> (simplify_subgroup_ast ast) = (simplify_subgroup_ast ast').
Proof.
Admitted.
(*
move=> ast ast' H.
have {H}: (interp ast) @ (inv (interp ast')) == e.
  by rewrite H inverse_left.
rewrite -sea_inv_correct -sea_law_correct.
move=> /preserve_eq_interp_e /=.
elim: ast => [/=|gen Pgen ast IH|gen Pgen].
- admit.
- 
- move=> gen Pgen ast IH ast'.
  elim: ast' ast IH.
  + move=> ast IH H.
    have: interp ast == interp (sea_mul_inv_gen Pgen sea_e) by admit.
    move=> /IH /= ->.
    by have ->: dec_eq_G gen gen by apply /dec_eq_G_reflect.

done.
*)

*)

Section MapSubgroupGens.
Variable G: group.
Variable gens gens': seq G.

Variable map: G -> G.
Hypothesis map_preserve_gen: forall x, List.In x gens -> List.In (map x) gens'.
(* these hypotheses are not minimal *)
Hypothesis map_preserve_eq: forall x y, x == y -> map x == map y.
Hypothesis map_preserve_e: map e == e.

Let H := finGeneratedSubgroup gens.
Let H' := finGeneratedSubgroup gens'.

Definition map_extended (x: H): H'.
Proof.
Admitted.
(*
  rewrite /gens'.
  apply in_list_map.
 /map_preserve_gen.
- exact: e.
- exact: (IHHx1 @ IHHx2).
- exact: (inv IHHx).
Defined.
*)

Lemma extension_preserve_e: map_extended e == e.
Proof. Admitted. (*done. Qed.*)

Lemma extension_preserve_law x y: map_extended (x @ y) == (map_extended x) @ (map_extended y).
Proof. Admitted. (*done. Qed.*)

Lemma extension_preserve_inv x: inv (map_extended x) == map_extended (inv x).
Proof. Admitted. (*done. Qed.*)

Lemma extension_preserve_equiv' x:
  x == e -> map_extended x == e.
Proof.
Admitted.
(*
case: x => x x_in_subgroup Heq.
elim: x_in_subgroup Heq.
- move=> x' x'_in_gens /=.
  rewrite /eq/=/subgroupby_eq/=.
  rewrite -{2}map_preserve_e.
  exact: map_preserve_eq.
- by rewrite /eq/=/subgroupby_eq/=.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' y' x'_in_gens IHx'.
  move=> y'_in_gens IHy'.
  move=> Heq.
  transitivity (
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
      @
    subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
      (map_extended
         (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) y' y'_in_gens))
  ); first done.
  rewrite IHx' //.
  rewrite IHy' //.
- rewrite /eq/=/subgroupby_eq/=.
  move=> x' x'_in_gens IHx' Hinvx'.
  transitivity (
    inv (
      subgroupby_inj G (in_generated_subgroup ((List.In (A:=G))^~ gens'))
        (map_extended
          (Build_subgroup_by G (in_generated_subgroup ((List.In (A:=G))^~ gens)) x' x'_in_gens))
    )
  ); first done.
  by rewrite -inv_e IHx' // -inv_e -[x']inv_involutive Hinvx'.
Admitted.
*)

Lemma extension_preserve_equiv x y:
  x == y -> map_extended x == map_extended y.
Proof.
Admitted.
(*
have Heq: x @ (inv y) == e -> (map_extended x) @ (map_extended (inv y)) == e; last first.
  move=> H1.
  have {}H1: x @ (inv y) == e by rewrite H1 inverse_left.
  move: Heq => /(_ H1) {H1}.
  rewrite extension_preserve_inv => H1.
  transitivity (((map_extended x) @ (inv (map_extended y))) @ (map_extended y)).
    by rewrite -associativity inverse_right neutral_right.
  by rewrite H1 neutral_left.
move=> Heq.
rewrite -extension_preserve_law.
exact: extension_preserve_equiv'.
Qed.
*)

HB.instance Definition _ := isMonoidMorphism.Build H H' map_extended extension_preserve_equiv extension_preserve_e extension_preserve_law.
HB.instance Definition _ := isInvMorphism.Build H H' map_extended extension_preserve_inv.

End MapSubgroupGens.

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

Definition affine_state_encoding_gens (s: State) := [::
    (encoding s.1);
    (power (`[b]: F2) s.2)
  ].
Definition affine_state_encoding (s: State) := finGeneratedSubgroup (affine_state_encoding_gens s).

Definition admit {T: Type}: T. Admitted.

Definition encoding_state_k (s: State) (k: int) : affine_state_encoding s.
Proof.
exists (encoding (s.1 + (s.2: int) * k)).
exact: admit.
Defined.

Lemma encoding_state_k_value: forall s k,
  subgroup_inj (s:=(affine_state_encoding s)) (encoding_state_k s k) = encoding (s.1 + (s.2: int) * k).
Proof. done. Qed.

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_map: forall {M N: monoid} (s: seq M) (f: monoidMorphism M N), prod (map f s) == f (prod s).
Proof.
move=> M N s f; elim: s => /= [|a l eq].
  by rewrite morphism_preserve_e.
by rewrite morphism_preserve_law eq.
Qed.

(* TODO: move to EquivalenceAlgebra.v *)
Lemma prod_inv {G: group} (decomp: seq G) :
  inv (prod decomp) == prod (rev (map inv decomp)).
Proof.
elim: decomp => [/=|a decomp IH /=]; first by rewrite inv_e.
by rewrite inverse_law IH -cat1s rev_cat prod_cat /= neutral_right.
Qed.

(*
Definition normalize_F2_letter (c: F2_sigma): F2_sigma * int := match c with
  | a => (a, 1)
  | a_inv => (a, -1)
  | b => (b, 1)
  | b_inv => (b, -1)
  end.

(*
Definition append_letters_to_count_head (a: F2_sigma) (occ: int) (count_head: F2_sigma * int) :=
  let '(topn, topc) := count_head in
  let '(an, ac) := normalize_F2_letter a in
  if an == topn then (
    let count := topc + ac * occ in
    [::(topn, count)]
  )
  else [:: (an, ac * occ); (topn, topc)].

Definition append_letters_to_count_prefilter (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  match count with
  | nil => let '(an, ac) := normalize_F2_letter a in [::(an, ac * occ)]
  | top::l => (append_letters_to_count_head a occ top) ++ l
  end.

Definition counts_remove_zeroes (count: seq (F2_sigma * int)) :=
  filter (fun '(c, x) => x != 0) count.

Lemma remove_zeroes_cat l l': counts_remove_zeroes (l ++ l') = (counts_remove_zeroes l) ++ (counts_remove_zeroes l').
Proof. by rewrite /counts_remove_zeroes filter_cat. Qed.

Definition append_letters_to_count (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  counts_remove_zeroes (append_letters_to_count_prefilter a occ count).

Fixpoint F2_count_letters (w: F2): seq (F2_sigma * int) := match w with
  | nil => nil
  | c::l => append_letters_to_count c 1 (F2_count_letters l)
  end.
*)

Definition append_letters_to_count (a: F2_sigma) (occ: int) (count: seq (F2_sigma * int)) :=
  match count with
  | nil => if occ == 0 then nil else [::(a, occ)]
  | (c, k)::l =>
      if a == c then (
        if k + occ == 0 then l
        else (a, occ + k)::l
      )
      else (
        if occ == 0 then (c, k)::l
        else (a, occ)::(c, k)::l
      )
  end.

Fixpoint compress_count (l: seq (F2_sigma * int)): seq (F2_sigma * int) := match l with
  | nil => nil
  | (c, k)::l => append_letters_to_count c k (compress_count l)
  end.

Definition F2_count_letters (w: F2): seq (F2_sigma * int) := compress_count (map normalize_F2_letter w).

Definition F2_dec_eq (w w': F2): bool :=
  (F2_count_letters w) == (F2_count_letters w').

Lemma F2_dec_eq_reflect (w w': F2): reflect (w == w') (F2_dec_eq w w').
Admitted.

Definition counts_inv l: seq (F2_sigma * int) := map (fun '(c, n) => (c, -n)) (rev l).

Lemma count_letters_e: F2_count_letters e = nil.
Proof. by rewrite /F2_count_letters. Qed.

Lemma append_letters_same c k k' l:
  append_letters_to_count c k (append_letters_to_count c k' l) = append_letters_to_count c (k + k') l.
Proof.
Admitted.

Lemma append_letters_cancel c k l:
  append_letters_to_count c (-k) (append_letters_to_count c k l) = l.
Proof.
Admitted.

Lemma compress_countK c: compress_count (compress_count c) = compress_count c.
Proof.
elim: c => // [[p k] c] IH.
move: IH => /=.
set l' := compress_count c.
case: l' => [_ |[c' k'] l] /=.
  have /orP [/eqP -> //=|/negbTE /[dup] H -> /=] := orbN (k == 0).
  by rewrite H.
have /orP [/eqP ->|/negbTE /[dup] H -> /=] := orbN (p == c'); last first.
  have /orP [/eqP -> //=|/negbTE /[dup] H' -> /= -> /=] := orbN (k == 0).
  by rewrite H H'.
rewrite eq_refl.  
have /orP [/eqP -> /=|/negbTE /[dup] H -> /=] := orbN (k' + k == 0); last first.
  rewrite -append_letters_same => -> /=.
  by rewrite eq_refl H.
rewrite -{2}(@append_letters_cancel c' k' (compress_count l)) => -> /=.
by rewrite subr_eq0 !eq_refl.
Qed.

Lemma append_letters_compress_cat c k l1 l2:
  append_letters_to_count c k (compress_count (l1 ++ l2)) =
  compress_count (append_letters_to_count c k l1 ++ l2).
Proof.
Admitted.

Lemma compress_count_cat l1 l2:
  compress_count (l1 ++ l2) = compress_count ((compress_count l1) ++ (compress_count l2)).
Proof.
elim: l1 => [/=|[c k] l /= ->].
  by rewrite compress_countK.
exact: append_letters_compress_cat.
Qed.

Lemma count_letters_cons c l:
  F2_count_letters (c :: l) =
  compress_count ((normalize_F2_letter c) :: (F2_count_letters l)).
Proof.
rewrite /F2_count_letters map_cons /=.
by rewrite compress_countK.
Qed.

Lemma count_letters_cat l1 l2:
  F2_count_letters (l1 ++ l2) = compress_count ((F2_count_letters l1) ++ (F2_count_letters l2)).
Proof. by rewrite /F2_count_letters map_cat compress_count_cat. Qed.

Lemma count_letters1 c:
  F2_count_letters [:: c] = [:: normalize_F2_letter c].
Proof. by case: c. Qed.

Lemma rev_compress l:
  rev (compress_count l) =
  compress_count (rev l).
Proof.
Admitted.

Lemma negate_append_letters_comm c k l:
  append_letters_to_count c (- k) [seq (c0, - n0) | '(c0, n0) <- l] =
  [seq (c0, - n0) | '(c0, n0) <- append_letters_to_count c k l].
Proof.
(*
case: l => [/=|[c' k'] l].
  rewrite oppr_eq0.
  by have /orP [/eqP ->|/negbTE ->] := orbN (k == 0).
rewrite map_cons /=.
have /orP [/eqP ->|/negbTE ->] := orbN (c == c'); last done.
have ->: - k' - k = -(k' + k) by lia.
rewrite eq_refl oppr_eq0.
have /orP [-> //|/negbTE -> /=] := orbN (k' + k == 0).
by have <-: - k - k' = -(k + k') by lia.
*)
Admitted.

Lemma append_letters_zero c l:
  append_letters_to_count c 0 l = l.
Proof.
elim: l => // [[c' k] l] /=.
rewrite addr0 add0r.
have /orP [/eqP ->|/negbTE ->] := orbN (c == c').

Admitted.

Lemma compress_negate_counts_comm l:
  compress_count (map (fun '(c, n) => (c, -n)) l) =
  map (fun '(c, n) => (c, -n)) (compress_count l).
Proof.
Admitted.
(*
elim: l => // [[c k]] l.
rewrite map_cons -cat1s.
rewrite compress_count_cat => /=.
rewrite oppr_eq0.
have /orP [/eqP ->|/negbTE -> ->] := orbN (k == 0).
  rewrite eq_refl cat0s compress_countK => ->.
  by rewrite append_letters_zero.
rewrite cat1s /=.
rewrite compress_countK => ->.
exact: negate_append_letters_comm.
Qed.
*)

Lemma counts_inv_compress l:
  counts_inv (compress_count l) =
  compress_count (counts_inv l).
Proof. by rewrite /counts_inv rev_compress compress_negate_counts_comm. Qed.

Lemma counts_inv_cat l1 l2: counts_inv (l1 ++ l2) = (counts_inv l2) ++ (counts_inv l1).
Proof. by rewrite /counts_inv rev_cat map_cat. Qed.

Lemma count_letters_inv (w: F2):
  F2_count_letters (inv w) = counts_inv (F2_count_letters w).
Proof.
rewrite /inv/=/inv_word/=.
elim: w => [|c l].
  by rewrite count_letters_e.
rewrite count_letters_cons -cat1s rev_cat map_cat count_letters_cat => ->.
rewrite count_letters1 -[(normalize_F2_letter c) :: _]cat1s counts_inv_compress.
rewrite counts_inv_cat.
by case: c.
Qed.

Lemma count_letters_preserve_eq (w w': F2):
  w == w' -> F2_count_letters w = F2_count_letters w'.
Proof.
move=> /F2_dec_eq_reflect.
rewrite /F2_dec_eq.
by move=> /eqP.
Qed.

Lemma count_letters_power_a: forall k, F2_count_letters (power (`[a] : F2) k) =
  if k != 0 then [:: (a, k)] else nil.
Proof.
elim => // [k IH|k IH].
- rewrite powerS count_letters_cat {}IH /=.
  have /orP [/eqP -> //|-> /=] := orbN (k == 0).
  by have ->: k%:Z + 1 = k.+1 by lia.
- rewrite (count_letters_preserve_eq (powerP (`[a]: F2) _)) oppr_eq0.
  rewrite count_letters_cons /=.
  rewrite {}IH oppr_eq0 /=.
  have /orP [/eqP -> //|/[dup] H -> /=] := orbN (k == 0).
  have /negbTE -> /=: - Posz k != 0 by lia.
  have ->: -k%:Z - 1 = - (k.+1)%:Z by lia.
  rewrite oppr_eq0 /=.
  by have ->: - 1 - k%:Z = - k.+1%:Z by lia.
Qed.  

Lemma count_letters_power_b: forall k, F2_count_letters (power (`[b] : F2) k) =
  if k != 0 then [:: (b, k)] else nil.
Proof.
elim => // [k IH|k IH].
- rewrite powerS count_letters_cat {}IH /=.
  have /orP [/eqP -> //|-> /=] := orbN (k == 0).
  by have ->: k%:Z + 1 = k.+1 by lia.
- rewrite (count_letters_preserve_eq (powerP (`[b]: F2) _)) oppr_eq0.
  rewrite count_letters_cons /=.
  rewrite {}IH oppr_eq0 /=.
  have /orP [/eqP -> //|/[dup] H -> /=] := orbN (k == 0).
  have /negbTE -> /=: - Posz k != 0 by lia.
  have ->: -k%:Z - 1 = - (k.+1)%:Z by lia.
  by have ->: - 1 - k%:Z = - k.+1%:Z by lia.
Qed.  

Lemma count_letters_encoding z':
  F2_count_letters (encoding z') = (
    if z' == 0
    then [::(a, 1)]
    else [::(b, z'); (a, 1); (b, -z')]
  ).
Proof.
rewrite /encoding !count_letters_cat !count_letters_power_b.
have /orP [/eqP -> //|/[dup] H /negbTE -> /=] := orbN (z' == 0).
rewrite oppr_eq0 H /=.
(*
by have /negbTE ->: oppz z' != 0 by lia.
*)
Admitted.
*)
Definition F2_dec_eq: F2 -> F2 -> bool.
Admitted.

Definition iso_of_transition_gens (t: Transition) (w: F2) :=
       if F2_dec_eq w (encoding t.1.1)       then encoding t.2.1
  else if F2_dec_eq w (inv (encoding t.1.1)) then inv (encoding t.2.1)
  else if F2_dec_eq w (power (`[b]: F2) t.1.2) then power (`[b]: F2) t.2.2
  else if F2_dec_eq w (inv (power (`[b]: F2) t.1.2)) then inv (power (`[b]: F2) t.2.2)
  else w (* whatever but using w allows more general lemma to be stated below *).

(*
Lemma affine_state_encoding_gens_transition (s1 s2: State):
    (affine_state_encoding_gens s2) = map (iso_of_transition_gens (s1, s2)) (affine_state_encoding_gens s1).
Proof.
rewrite /iso_of_transition_gens /=.
have ->: F2_dec_eq (encoding s1.1) (encoding s1.1) = true.
  by rewrite /F2_dec_eq eq_refl.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (encoding s1.1) = false.
  case: s1 => [p q] /=.
  rewrite /F2_dec_eq.
  rewrite count_letters_power_b count_letters_encoding.
  rewrite (nzint_non_nul q).
  have /orP [-> //|/negbTE ->] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (inv (encoding s1.1)) = false.
  case: s1 => [p q] /=.
  rewrite /F2_dec_eq.
  rewrite count_letters_power_b count_letters_inv count_letters_encoding.
  rewrite (nzint_non_nul q).
  have /orP [-> //|/negbTE -> /=] := orbN (p == 0).
  apply /negbTE.
  by rewrite seq_diff_sizes.
have ->: F2_dec_eq (power (`[b]: F2) s1.2) (power (`[b]: F2) s1.2) = true.
  by rewrite /F2_dec_eq eq_refl.
done.
Qed.
*)

Lemma iso_of_transition_gens_preserve_gen t: forall w,
  List.In w (affine_state_encoding_gens t.1) -> List.In (iso_of_transition_gens t w) (affine_state_encoding_gens t.2).
Admitted.

Lemma iso_of_transition_gens_preserve_eq t: forall x y,
  x == y -> iso_of_transition_gens t x == iso_of_transition_gens t y.
Admitted.

Lemma iso_of_transition_gens_preserve_e t:
  iso_of_transition_gens t e == e.
Admitted.

Definition iso_of_transition (t: Transition): morphism (affine_state_encoding t.1) (affine_state_encoding t.2) :=
  (* ugly but using "map_extended (@iso_of_transition_gens_preserve_gen t)" has unresolved implicit arguments *)
  Main_map_extended__canonical__EquivalenceAlgebra_Morphism (iso_of_transition_gens_preserve_gen (t:=t))
  (iso_of_transition_gens_preserve_eq t) (iso_of_transition_gens_preserve_e t).
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
case=> [[x x_in_subgroup] /= eq].
Admitted.

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
(* TODO: propriété "<a_p, b^q> inter [ZZ] = [p + qZ]" *)
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
case; case=> [x' x'_in_subgroup /=].
elim: x'_in_subgroup x => /= [x|x Heq||].
- case=> [<- xF Heq|x_in_ts xF Heq].
    unshelve eexists.
      unshelve eexists (subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (s:=K) _)).
        exists (encoding m).
        apply /igs_gen.
        exists m; split=> //.
        exact: Relation_Operators.rst_refl.
      exact /igs_gen /steg_K.
    done.
  unshelve eexists.
    exists x.
    exact /igs_gen /steg_t.
  done.
- exists e.
  by rewrite -Heq.
- move=> x y Hx IHx Hy IHy x'' Heq.
  case: (IHx x) => // x2 {IHx} Hx2.
  case: (IHy y) => // y2 {IHy} Hy2.
  exists (x2 @ y2).
  rewrite morphism_preserve_law. 
  move: Heq.
  by rewrite -Hx2 -Hy2.
- move=> x Hx IH x'' Heq.
  case: (IH x) => // x2 {IH} Hx2.
  exists (inv x2).
  by rewrite -morphism_preserve_inv -Heq -Hx2.
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

Lemma iso_of_transition_image_encoding s1 s2 k:
  iso_of_transition (s1, s2) (encoding_state_k s1 k) == encoding_state_k s2 k.
Proof.
Admitted.

Lemma transA_implies_inHlike s1 s2 x y:
  transitionStep A (s1, s2) x y ->
  (subgroup_inj (encoding x: HNNI_extension_base F2)) \insubgroup (finGeneratedSubgroup ([:: subgroup_inj (encoding y: HNNI_extension_base F2)] ++ ts)).
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

have {Heq}:
  (inv t) @ subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (iso_of_transition_lm (p, q, (p', q')) (encoding_state_k (p, q) k))) @ t
    ==
  subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (s:=affine_state_encoding (p, q)) (encoding_state_k (p, q) k)).
  rewrite Heq.
  rewrite !associativity inverse_right neutral_left.
  by rewrite -!associativity inverse_right neutral_right.

have ->: lm_morphism _ (iso_of_transition_lm ((p, q), (p', q'))) = iso_of_transition ((p, q), (p', q')) by done.

rewrite iso_of_transition_image_encoding => Heq.

have <- := encoding_state_k_value (p, q) k.

apply /in_subgroup_proper.
  exact: Heq.

set u := subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (s:=affine_state_encoding (p', q')) (encoding_state_k (p', q') k)).

have t_in_subgroup: in_generated_subgroup (fun x => List.In x (u::ts)) t.
  apply /igs_gen /List.in_cons.
  rewrite /t (tnth_nth e) nthE.
  apply /List.nth_In /ltP.
  rewrite -LM2.sizeE.
  rewrite size_tuple.
  exact: ltn_ord.

unshelve eexists.
  exists ((inv t) @ u @ t).
  apply /igs_law => //.
  apply /igs_law.
    exact /igs_inv.
  by apply /igs_gen; left.
done.
Qed.

(* this lemma is badly-named, it is not specific to the Hlike definition *)
Lemma Hlike_transitivity p q x' y':
  in_generated_subgroup (fun x => List.In x (Hlike_gens p)) x' ->
  in_generated_subgroup (fun x => List.In x (Hlike_gens q)) y' ->
  y' == subgroup_inj (encoding p: HNNI_extension_base F2) ->
  x' \insubgroup (finGeneratedSubgroup (Hlike_gens q)).
Proof.
elim=> [x|_ _|x y Hx IHx Hy IHy Hy' eq_y'|x Hx IHx Hy' eq_y'].
- rewrite /Hlike_gens cat1s => Hx.
  case: (List.in_inv Hx) => [-> ? ?|? ? ?]; last first.
    unshelve eexists.
      exists x.
      exact /igs_gen /List.in_cons.
    done.
  unshelve eexists.
    by exists y'.
  done.
- unshelve eexists.
    exists e.
    exact: igs_e.
  done.
- case: IHx => // [[x'' /=] Hx'' eq_x''].
  case: IHy => // [[y'' /=] Hy'' eq_y''].
  unshelve eexists.
    exists (x'' @ y'').
    apply: igs_law.
      exact /Hx''.
    exact /Hy''.
  by rewrite /= eq_x'' eq_y''.
- case: IHx => // [[x'' /=] Hx'' eq_x''].
  unshelve eexists.
    exists (inv x'').
    exact: igs_inv.
  by rewrite /= eq_x''.
Qed.

Lemma Hlike_symmetry o p:
  (subgroup_inj (encoding o: HNNI_extension_base F2)) \insubgroup (finGeneratedSubgroup (Hlike_gens p)) ->
  (subgroup_inj (encoding p: HNNI_extension_base F2)) \insubgroup (finGeneratedSubgroup (Hlike_gens o)).
Proof.
(* more complicated than the proof attempted below: this is true only because encoding o and encoding p are free or = *)
Admitted.
(*
move=> Henco.
elim=> [||x y Hx IHx Hy IHy|x Hx IHx].
- move=> x.
  rewrite /Hlike_gens cat1s => Hx.
  case: (List.in_inv Hx) => {Hx} [<-|]; last first.
    unshelve eexists.
      exists x.
      exact /igs_gen /List.in_cons.
    done.
  admit.
- unshelve eexists.
    exists e.
    exact: igs_e.
  done.
- case: IHx => [[x'' /=] Hx'' eq_x''].
  case: IHy => [[y'' /=] Hy'' eq_y''].
  unshelve eexists.
    exists (x'' @ y'').
    exact: igs_law.
  by rewrite /= eq_x'' eq_y''.
- case: IHx => [[x'' /=] Hx'' eq_x''].
  unshelve eexists.
    exists (inv x'').
    exact: igs_inv.
  by rewrite /= eq_x''.
Admitted.
*)

Lemma equiv_x_y_implies_encoding_in_ts_subgroup x y:
  equivalence_problem A x y
    ->
  (subgroup_inj (s:=HNNI_extension_base F2) (encoding x)) \insubgroup (finGeneratedSubgroup (Hlike_gens y)).
Proof.
move=> E.
dependent induction E.
- case: H0 => [[[p q] [p' q']]].
  exact: transA_implies_inHlike.
- unshelve eexists.
    exists (subgroup_inj (encoding x: HNNI_extension_base F2)).
    apply /igs_gen.
    rewrite /Hlike_gens cat1s.
    exact: List.in_eq.
  done.
- exact: Hlike_symmetry.
- case: IHE1 => [[] x' x'_in_subgroup /= Heqx'].
  case: IHE2 => [[] y' y'_in_subgroup /= Heqy'].
  have := (Hlike_transitivity x'_in_subgroup y'_in_subgroup Heqy').
  exact: in_subgroup_proper.
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
