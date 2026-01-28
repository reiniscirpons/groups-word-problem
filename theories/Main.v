From HB Require Import structures.
From Undecidability Require Import Synthetic.Definitions Synthetic.Undecidability.
From Stdlib Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra tuple.
From mathcomp Require Import ring lra zify.
Import GRing.Theory.

From GWP Require Import Presentation AffineMachines F2 EquivalenceAlgebra Equivalence HNN Utils.

Section NormalizeSubgroupAST.
Variable G: deceqGroupType.
Variable P: G -> Type.

Record subgroupBase := {
  gen: G;
  Pgen: P gen;
  inverted: bool;
}.
Definition comb := list subgroupBase.

Definition invert_base (b: subgroupBase): subgroupBase := {|
  gen := gen b;
  Pgen := Pgen b;
  inverted := negb (inverted b);
|}.

Fixpoint comb_ast (ast: subgroup_ast P): comb :=
  match ast with
  | sa_e => [::]
  | sa_gen gen Pgen => [:: {| Pgen := Pgen; inverted := false |}]
  | sa_inv ast => rev (map invert_base (comb_ast ast))
  | sa_law ast1 ast2 => (comb_ast ast1) ++ (comb_ast ast2)
  end.

Definition subgroup_base_to_ast (b: subgroupBase): subgroup_ast P :=
  match inverted b with
  | true => sa_inv (sa_gen (gen b) (Pgen b))
  | false => sa_gen (gen b) (Pgen b)
  end.

Fixpoint comb_to_ast (c: comb): subgroup_ast P := match c with
  | [::] => sa_e P
  | base::rest => sa_law (subgroup_base_to_ast base) (comb_to_ast rest)
  end.

Definition invertible_base (b1 b2: subgroupBase): bool :=
  ((gen b1) == (gen b2)) && (inverted b1 != inverted b2).

Fixpoint simplify_comb (c: comb): comb := match c with
  | [::] => [::]
  | h::c => match c with
     | [::] => [:: h]
     | h'::c => if invertible_base h h' then simplify_comb c else h::h'::(simplify_comb c)
     end
  end.

Definition normalize_ast (ast: subgroup_ast P): subgroup_ast P :=
  comb_to_ast (simplify_comb (comb_ast ast)).

Lemma ast_combing_correct ast:
  interpret_subgroup_ast ast == interpret_subgroup_ast (comb_to_ast (comb_ast ast)).
Proof.
elim: ast => //= [gen _|ast1 IH1 ast2 IH2|ast IH].
- by rewrite neutral_right.
- rewrite {}IH1 {}IH2.
  set l1 := comb_ast ast1.
  set l2 := comb_ast ast2.
  elim: l1 => /= [|b1 l1 IH].
  + by rewrite neutral_left.
  + by rewrite -IH associativity.
- rewrite {}IH.
  set l := comb_ast ast.
  elim/last_ind: l => //= [|l1 b1 IH].
    by rewrite inv_e.
  rewrite map_rcons rev_rcons /= -{}IH.
  elim: l1 => //= [|b2 l1 IH]; last first.
    by rewrite !inverse_law {}IH associativity.
  rewrite inverse_law inv_e neutral_left neutral_right.
  case: b1 => gen Pgen [] //=.
  by rewrite inv_involutive.
Qed.

Lemma normalize_ast_correct (ast: subgroup_ast P):
  interpret_subgroup_ast ast == interpret_subgroup_ast (normalize_ast ast).
Proof.
rewrite ast_combing_correct /normalize_ast.
set c := comb_ast ast.
elim: c => //= base l ->.
elim: l base => //= base' l IH base.
rewrite -{}IH.
have /orP [/[dup] H ->|/negbTE -> //] := orbN (invertible_base base base').
rewrite associativity.
move: H=> /andP /= [/eqP H].
rewrite /subgroup_base_to_ast /=.
case: (inverted base); case: (inverted base') => //= _;
by rewrite H ?inverse_left ?inverse_right neutral_left.
Qed.

Lemma normalize_inv_inv (ast: subgroup_ast P):
  normalize_ast (sa_inv (sa_inv ast)) = normalize_ast ast.
Proof. by rewrite /normalize_ast/= map_rev revK mapK // => [[gen Pgen []]]. Qed.

Lemma normalize_distr_inv_law (ast1 ast2: subgroup_ast P):
  normalize_ast (sa_inv (sa_law ast1 ast2)) = normalize_ast (sa_law (sa_inv ast2) (sa_inv ast1)).
Proof. by rewrite /normalize_ast/= map_cat rev_cat. Qed.

Lemma normalize_law_associativity (ast1 ast2 ast3: subgroup_ast P):
  normalize_ast (sa_law (sa_law ast1 ast2) ast3) = normalize_ast (sa_law ast1 (sa_law ast2 ast3)).
Proof. by rewrite /normalize_ast/= catA. Qed.

Lemma simplify_comb_cons b1 (c: comb):
  simplify_comb (b1::c) =
  match simplify_comb c with
  | nil => [::b1]
  | b2::simplified =>
      if invertible_base b1 b2
      then simplified
      else b1::b2::simplified
  end.
Admitted.

Lemma unique_comb_simplification_e c:
  interpret_subgroup_ast (comb_to_ast c) == e ->
  simplify_comb c = [::].
Proof.
Admitted.

Lemma unique_comb_simplification c c':
  interpret_subgroup_ast (comb_to_ast c) == interpret_subgroup_ast (comb_to_ast c') ->
  simplify_comb c = simplify_comb c'.
Proof.
elim: c' c => [c|b' c' IH c].
  exact: unique_comb_simplification_e.
move=> Heq.
have /IH {Heq IH}: interpret_subgroup_ast (comb_to_ast (invert_base b' :: c)) == interpret_subgroup_ast (comb_to_ast c').
  rewrite /= {}Heq /= associativity.
  case: b' => [gen Pgen []] /=;
  by rewrite ?inverse_right ?inverse_left neutral_left.
Admitted.

Lemma unique_normalization (ast ast': subgroup_ast P):
  interpret_subgroup_ast ast == interpret_subgroup_ast ast' ->
  normalize_ast ast = normalize_ast ast'.
Proof.
move=> H.
rewrite /normalize_ast.
rewrite (@unique_comb_simplification (comb_ast ast) (comb_ast ast')) //.
by rewrite -!ast_combing_correct.
Qed.

End NormalizeSubgroupAST.


Section MapSubgroupGens.
Variable G: deceqGroupType.
Variable gens gens': seq G.

Variable map: G -> G.
Hypothesis map_preserve_gen: forall x, in_list x gens -> in_list (map x) gens'.

Let H := finGeneratedSubgroup gens.
Let H' := finGeneratedSubgroup gens'.

Let H_char := (fun x => in_list x gens).
Let H'_char := (fun x => in_list x gens').

Fixpoint extend_ast (ast: subgroup_ast H_char): subgroup_ast H'_char :=
  match ast with
  | sa_e => sa_e H'_char
  | sa_law ast_l ast_r => sa_law (extend_ast ast_l) (extend_ast ast_r)
  | sa_inv ast => sa_inv (extend_ast ast)
  | sa_gen gen Pgen => sa_gen (map gen) (map_preserve_gen Pgen)
  end.

Definition map_extended (x: H): H'.
Proof.
case: x => [x]; elim=> [ast Hx].
have@ ast' := extend_ast (normalize_ast ast).
exists (interpret_subgroup_ast ast').
by exists ast'.
Defined.

Lemma extension_preserve_e: map_extended e == e.
Proof. done. Qed.

Lemma interpret_extend_comb_cas b c:
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb (b::c)))) ==
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb [::b]))) @
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb c))).
Proof.
elim: c b => [/= b|a c IH b].
  by rewrite !neutral_right.
rewrite IH.
rewrite /=.
have /orP [/[dup] Hinv ->|/negbTE -> /=] := orbN (invertible_base b a); last first.
  by rewrite !neutral_right.
rewrite !neutral_right.
move: Hinv => /andP [/eqP Heq].
rewrite /subgroup_base_to_ast.
case: (inverted b); case: (inverted a) => //= _;
by rewrite !associativity Heq ?inverse_left ?inverse_right neutral_left.
Qed.

Lemma interpret_extend_comb_cat c1 c2:
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb (c1 ++ c2)))) ==
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb c1))) @
  interpret_subgroup_ast (extend_ast (comb_to_ast (simplify_comb c2))).
Proof.
elim: c1 c2 => // [c2|b1 c1 IH c2].
  by rewrite neutral_left.
rewrite -cat1s -catA !cat1s.
rewrite interpret_extend_comb_cas (interpret_extend_comb_cas b1 c1).
by rewrite IH !associativity.
Qed.

Lemma interpret_extend_ast_law ast_x ast_y:
  interpret_subgroup_ast (extend_ast (normalize_ast (sa_law ast_x ast_y))) ==
  interpret_subgroup_ast (extend_ast (normalize_ast ast_x)) @
  interpret_subgroup_ast (extend_ast (normalize_ast ast_y)).
Proof. by rewrite /normalize_ast/= interpret_extend_comb_cat. Qed.

Lemma extension_preserve_law x y: map_extended (x @ y) == (map_extended x) @ (map_extended y).
Proof. 
case: x => [x [ast_x eqx]].
case: y => [y [ast_y eqy]].
rewrite /eq/=/subgroupby_eq/=.
exact: interpret_extend_ast_law.
Qed.

Lemma extension_preserve_inv x: inv (map_extended x) == map_extended (inv x).
Proof.
case: x => [x [ast_x]].
rewrite /eq/=/subgroupby_eq/= => _.
elim: ast_x => [|gen Pgen /=|ast1 IH1 ast2 IH2|ast Hast].
- by rewrite inv_e.
- by rewrite !neutral_right.
- by rewrite normalize_distr_inv_law !interpret_extend_ast_law inverse_law IH1 IH2.
- by rewrite normalize_inv_inv -Hast inv_involutive.
Qed.

Lemma extension_preserve_equiv x y:
  x == y -> map_extended x == map_extended y.
Proof.
case: x => [x [ast_x Hx]].
case: y => [y [ast_y Hy]].
rewrite /eq/=/subgroupby_eq/= => Heq.
have /unique_normalization -> //: interpret_subgroup_ast ast_x == interpret_subgroup_ast ast_y.
transitivity x; first by symmetry.
transitivity y => //.
Qed.

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

Definition encoding_p_state_encoding (s: State): affine_state_encoding s.
Proof.
exists (encoding s.1).
by apply: igs_gen; left.
Defined.

Definition power_b_state_encoding (s: State): affine_state_encoding s.
Proof.
exists (power (`[b]: F2) s.2).
by apply: igs_gen; right; left.
Defined.  

(*
Definition power_subgroup_pos_value {G: group} (P: G -> Type) (x: generatedSubgroup P) (k: nat):
  subgroup_inj (s:=generatedSubgroup P) (power_subgroup_pos x k) == power (subgroup_inj (s:=generatedSubgroup P) x) k.
Proof.
elim: k => [//|k H].
rewrite powerS.
transitivity (power (subgroup_inj (s:=generatedSubgroup P) x) k @ power (subgroup_inj (s:=generatedSubgroup P) x) 1); last first.
  by rewrite /= neutral_left.
rewrite powerC.
move: H.
have ->: power_subgroup_pos x k.+1 = x @ (power_subgroup_pos x k).
  by elim: k => [//|k //].
rewrite morphism_preserve_law => <- /=.
by rewrite neutral_left.
Qed.
*)

Lemma power_subgroup_in_generated_subgroup {G: group} (P: G -> Type) (x: generatedSubgroup P) (k: int):
  in_generated_subgroup P (subgroup_inj (s:=generatedSubgroup P) x) ->
  in_generated_subgroup P (subgroup_inj (s:=generatedSubgroup P) (power x k)).
Proof.
case: k; elim=> [/= Px|k IH Px].
- exact: igs_e.
- move: (IH Px) => {IH} Hx.
  rewrite powerS.
  exact: igs_law.
- exact /igs_inv /Px.
- move: (IH Px) => {IH}.
  have ->: Negz k = - (k.+1)%:Z by done.
  have ->: Negz k.+1 = - (k.+2)%:Z by done.
  case=> [ast H].
  case: Px => [ast_x Hx].
  exists (sa_law (sa_inv ast_x) ast).
  simpl interpret_subgroup_ast.
  by rewrite -H -Hx powerP.
Qed.

Definition encoding_state_k (s: State) (k: int) : affine_state_encoding s.
Proof.
exists (
    subgroup_inj (s:=affine_state_encoding s) (power (power_b_state_encoding s) k) @
      subgroup_inj (s:=affine_state_encoding s) (encoding_p_state_encoding s) @
    subgroup_inj (s:=affine_state_encoding s) (power (power_b_state_encoding s) (-k))
).
apply: igs_law; do [apply: igs_law|simpl].
- apply: power_subgroup_in_generated_subgroup => /=.
  by apply: igs_gen; right; left.
- by apply: igs_gen; left.
- apply: power_subgroup_in_generated_subgroup => /=.
  by apply: igs_gen; right; left.
Defined.

Lemma encoding_state_k_value: forall s k,
  subgroup_inj (s:=(affine_state_encoding s)) (encoding_state_k s k) == encoding (s.1 + (s.2: int) * k).
Proof.
move=> s k.
rewrite /encoding power_inv /encoding_state_k/= !morphism_preserve_power /=.
by rewrite addrC !poweradd !powermul inverse_law -!power_inv !associativity.
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
  in_list w (affine_state_encoding_gens t.1) -> in_list (iso_of_transition_gens t w) (affine_state_encoding_gens t.2).
Admitted.

Lemma iso_of_transition_gens_preserve_eq t: forall x y,
  x == y -> iso_of_transition_gens t x == iso_of_transition_gens t y.
Admitted.

Lemma iso_of_transition_gens_preserve_e t:
  iso_of_transition_gens t e == e.
Admitted.

Definition iso_of_transition (t: Transition): morphism (affine_state_encoding t.1) (affine_state_encoding t.2) :=
  map_extended (@iso_of_transition_gens_preserve_gen t).
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
move=> i x Hx.
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
Proof. by rewrite /encoding_state_k/= /eq/=/subgroupby_eq/=. Qed.

Lemma iso_of_transition_image_power s1 s2:
  iso_of_transition (s1, s2) (power_b_state_encoding s1) == power_b_state_encoding s2.
Proof.
rewrite /eq/=/subgroupby_eq/= neutral_right.
Admitted.

Lemma iso_of_transition_image_encoding_p s1 s2:
  iso_of_transition (s1, s2) (encoding_p_state_encoding s1) == encoding_p_state_encoding s2.
Proof.
rewrite /eq/=/subgroupby_eq/= neutral_right.
Admitted.

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

rewrite iso_of_transition_image_encoding encoding_state_k_value => Heq.

apply: in_subgroup_proper.
  symmetry.
  have := encoding_state_k_value (p, q) k.
  exact.

apply /in_subgroup_proper.
  exact: Heq.

set u' := subgroup_inj (s:=HNNI_extension_base F2) (encoding (p' + (q': int) * k)).
set u := subgroup_inj (s:=HNNI_extension_base F2) (subgroup_inj (s:=affine_state_encoding (p', q')) (encoding_state_k (p', q') k)).

have t_in_subgroup: in_generated_subgroup (fun x => in_list x (u'::ts)) t.
  apply /igs_gen /in_tail.
  rewrite /t (tnth_nth e).
  apply: nth_in_list.
  by rewrite size_tuple.

apply: in_subgroup_law; do [apply: in_subgroup_law; do [apply in_subgroup_inv|]|].
- by unshelve eexists; first exists t.
- unshelve eexists.
    exists u'.
    by apply: igs_gen; left.
  by rewrite /=/u/u' encoding_state_k_value.
- by unshelve eexists; first exists t.
Qed.

(* this lemma is badly-named, it is not specific to the Hlike definition *)
Lemma Hlike_transitivity p q x' y':
  in_generated_subgroup (fun x => in_list x (Hlike_gens p)) x' ->
  in_generated_subgroup (fun x => in_list x (Hlike_gens q)) y' ->
  y' == subgroup_inj (encoding p: HNNI_extension_base F2) ->
  x' \insubgroup (finGeneratedSubgroup (Hlike_gens q)).
Proof.
case=> ast.
elim: ast x' y' => /= [x' y' Heq _ _|gen||].
- apply: in_subgroup_proper.
    symmetry.
    exact: Heq.
  by exists e.
- rewrite /H_gens/Hlike_gens cat1s => Hx.
  case: (in_list_inv Hx) => [<- x' y' H' y'_in_subgroup|Hgen x' y' Hx' y'_in_subgroup Hy'].
    rewrite -H' => {H'}Hx'y'.
    apply: in_subgroup_proper.
      exact: Hx'y'.
    unshelve eexists.
      by exists y'.
    done.
  apply: in_subgroup_proper.
    symmetry.
    exact: Hx'.
  unshelve eexists.
    exists gen.
    by apply: igs_gen; right.
  done.
- move=> ast_x IHx' ast_y IHy' x' y' Hlaw y'_in_subgroup Hy'.
  apply: in_subgroup_proper.
    symmetry.
    exact: Hlaw.
  case: (IHx' (interpret_subgroup_ast ast_x) y' (refl _) y'_in_subgroup Hy') => [[x Hx] /= eqx] {IHx'}.
  case: (IHy' (interpret_subgroup_ast ast_y) y' (refl _) y'_in_subgroup Hy') => [[y Hy] /= eqy] {IHy'}.
  unshelve eexists.
    exists (x @ y).
    exact: igs_law.
  by rewrite /= eqx eqy.
- move=> ast_x IH x' y' Hx' y'_in_subgroup Hy'.
  case: (IH (interpret_subgroup_ast ast_x) y') => // [[x Hx] /= eqx].
  apply: in_subgroup_proper.
    symmetry.
    exact: Hx'.
  apply: in_subgroup_inv.
  apply: in_subgroup_proper.
    exact: eqx.
  by unshelve eexists; first by exists x.
Qed.

Lemma Hlike_symmetry o p:
  (subgroup_inj (encoding o: HNNI_extension_base F2)) \insubgroup (finGeneratedSubgroup (Hlike_gens p)) ->
  (subgroup_inj (encoding p: HNNI_extension_base F2)) \insubgroup (finGeneratedSubgroup (Hlike_gens o)).
Proof.
case=> [[x [ast_x /=] ? ?]].

have: interpret_subgroup_ast ast_x == subgroup_inj (encoding o: HNNI_extension_base F2).
  transitivity x; last done.
  by symmetry.
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
    exact: in_head.
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
