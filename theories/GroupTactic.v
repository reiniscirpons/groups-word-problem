From elpi.apps Require Import coercion.
From Ltac2 Require Import Ltac2.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import eqtype seq fintype zify.
Import GRing.Theory.
Require Import Setoid Morphisms.

From GWP Require Import Equivalence EquivalenceAlgebra Presentation F2.

Import PresentationNotations.

(*
  The work done in this section is adapted from the
  Rocq implementation of the ring tactic, see
    Grégoire, B., Mahboubi, A. (2005).
    Proving Equalities in a Commutative Ring Done Right in Coq.
    In: Hurd, J., Melham, T. (eds) Theorem Proving in Higher Order Logics.
    TPHOLs 2005. Lecture Notes in Computer Science, vol 3603.
    Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/11541868_7
  and from the Ltac2 tutorial by Yiyun Liu, see
    https://github.com/yiyunliu/ltac2-tutorial
*)

Section FreeGroupTactic.

Context {Sigma: finType}.
Let P := FGP Sigma.
Let FG := FreeGroup Sigma.

Inductive FGExpr :=
  | FGnil : FGExpr
  | FGcons : Sigma -> int -> FGExpr -> FGExpr.

Fixpoint FGEval (fge: FGExpr): FG :=
  match fge with
  | FGnil => [::] \mod P
  | FGcons a n fge' =>
    (power ([:: Base a] \mod P) n) @ FGEval fge'
  end.

(* TODO(reiniscirpons): move this before and introduce in general
                        context *)
Inductive GExpr :=
| Gmul : GExpr -> GExpr -> GExpr
| Gidn : GExpr
| Ginv : GExpr -> GExpr
| Gpow : GExpr -> int -> GExpr
| Gvar : FG -> GExpr.

Fixpoint GEval (ge: GExpr): FG :=
  match ge with
  | Gmul ge1 ge2 => (GEval ge1) @ (GEval ge2)
  | Gidn => e
  | Ginv ge' => inv (GEval ge')
  | Gpow ge' n => power (GEval ge') n
  | Gvar fg => fg
  end.

Section FreeGroupNormalizeTactic.

Fixpoint FGreduced (fge: FGExpr): bool :=
  match fge with
  | FGnil => true
  | FGcons a n fge =>
    (n != 0) &&
    (FGreduced fge) &&
    (if fge is FGcons a' _ _ then
      a != a'
    else
      true)
  end.

Definition mkFGcons a (n: int) fge :=
  if (n == 0)%B
    then fge
  else
    match fge with
    | FGnil => FGcons a n FGnil
    | FGcons a' n' fge' =>
      if (a == a')%B then
        if (n + n' == 0) then
          fge'
        else
          FGcons a (n + n') fge'
      else
        FGcons a n fge
    end.

Lemma mkFGconsE: forall a n fge,
  FGEval (mkFGcons a n fge) ==
  power ([:: Base a] \mod P) n @ FGEval fge.
Proof.
  ltac1:(
    move => a n fge; rewrite /mkFGcons; case: ifP => [/eqP ->|_];
      first by rewrite power0 neutral_left
  ).
  ltac1:(
    case: fge => [//|a' n' fge'];
    case: ifP => [/eqP <-|//];
    case: ifP => [/eqP|];
    rewrite associativity -power_add // => ->;
    by rewrite power0 neutral_left
  ).
Qed.

Lemma mkFGcons_reduced: forall a n fge,
  FGreduced fge -> FGreduced (mkFGcons a n fge).
Proof.
  ltac1: (
    move => a n fge; rewrite /mkFGcons; case: ifP => [//|Hn]
  ).
  ltac1: (
    case: fge => [_|a' n' fge' /= /andP [/andP [Hn' Hfge'] Ha]] /=;
      first by rewrite Hn
  ).
  ltac1: (
    case: ifP => [/eqP Ha'|/= ->]; last by rewrite Hn Hn' Ha Hfge'
  ).
  ltac1: (
    case: ifP => [//|/= ->]; by rewrite Hfge' Ha' Ha
  ).
Qed.

Fixpoint mkFGrcons (fge: FGExpr) a n: FGExpr :=
  match fge with
  | FGnil => mkFGcons a n FGnil
  | FGcons a' n' fge' => mkFGcons a' n' (mkFGrcons fge' a n)
  end.

Lemma mkFGrconsE: forall a n fge,
  FGEval (mkFGrcons fge a n) ==
  FGEval fge @ power ([:: Base a] \mod P) n.
Proof.
  ltac1:(
    move => a n; elim => [|a' n' fge' IH] /=;
      first by rewrite mkFGconsE neutral_left neutral_right
  ).
  ltac1:(
    by rewrite mkFGconsE IH associativity
  ).
Qed.

Lemma mkFGrcons_reduced: forall a n fge,
  FGreduced fge -> FGreduced (mkFGrcons fge a n).
Proof.
  ltac1:(
    move => a n; elim => [|a' n' fge' IH] H /=; rewrite mkFGcons_reduced //;
    by apply IH; move: H => /= /andP [/andP [_ ->]]
  ).
Qed.

(*Fixpoint Frev (fge: FGExpr): FGExpr :=*)
(*  match fge with*)
(*  | FGnil => FGnil*)
(*  | FGcons a' n' fge' => Frcons (Frev fge') a' n'*)
(*  end.*)

Fixpoint FGinv (fge: FGExpr): FGExpr :=
  match fge with
  | FGnil => FGnil
  | FGcons a' n' fge' => mkFGrcons (FGinv fge') a' (-n')
  end.

Lemma FGinvE: forall fge,
  FGEval (FGinv fge) == inv (FGEval fge).
Proof.
  ltac1:(
    elim => [|a n fge H] /=; first by rewrite inv_e
  ).
  ltac1:(
    by rewrite mkFGrconsE H inverse_law power_inv
  ).
Qed.

Lemma FGinv_reduced: forall fge,
  FGreduced fge -> FGreduced (FGinv fge).
Proof.
  ltac1:(
    elim => [//|a n fge IH /= /andP [/andP [Hn /IH Hfge] Ha]];
    by apply mkFGrcons_reduced
  ).
Qed.

(*Fixpoint Fcat (fge1 fge2: FGExpr) {struct fge1}: FGExpr :=*)
(*match fge1 with*)
(*| FGnil => fge2*)
(*| FGcons a' n' fge1' => FGcons a' n' (Fcat fge1' fge2)*)
(*end.*)

Fixpoint FGmul (fge1 fge2: FGExpr) {struct fge1}: FGExpr :=
match fge1 with
| FGnil => fge2
| FGcons a' n' fge1' => mkFGcons a' n' (FGmul fge1' fge2)
end.

Lemma FGmulE: forall fge1 fge2,
  FGEval (FGmul fge1 fge2) == (FGEval fge1) @ (FGEval fge2).
Proof.
  ltac1:(
    elim => [|a n fge H] fge2 /=;
      first by rewrite neutral_left
  ).
  ltac1:(
    by rewrite mkFGconsE H associativity
  ).
Qed.

Lemma FGmul_reduced: forall fge1 fge2,
  FGreduced fge1 -> FGreduced fge2 -> FGreduced (FGmul fge1 fge2).
Proof.
  ltac1:(
    elim => [//|a n fge1 IH fge2 /= /andP [/andP [Hn /IH Hfge] Ha]];
    move /Hfge => {}Hfge; by apply mkFGcons_reduced
  ).
Qed.

Fixpoint FGpower' (fge: FGExpr) (k: nat): FGExpr :=
  match k with 
  | 0%N => FGnil
  | k'.+1 =>
    match fge with
    | FGnil => FGnil
    | FGcons a n FGnil => FGcons a (n * k) FGnil
    | FGcons a n _ => FGmul fge (FGpower' fge k')
    end
  end.

Lemma FGpowerE': forall fge k,
  FGEval (FGpower' fge k) == power (FGEval fge) k.
Proof.
  ltac1:(
    move => fge k; elim: k fge => [[//|a' n' [|a'' n'' fge''] /=]|k IH /=]
  ).
  ltac1:(
    by rewrite power0
  ).
  ltac1:(
    by rewrite power0
  ).
  ltac1:(
    case => [/=|a' n' [/=|a'' n'' fge'']]; first by rewrite power_e
  ).
  ltac1:(
    by rewrite !neutral_right power_mul
  ).
  ltac1:(
    by rewrite FGmulE IH powerS
  ).
Qed.

Lemma FGpower_reduced': forall fge k,
  FGreduced fge -> FGreduced (FGpower' fge k).
Proof.
  ltac1:(
    move => fge k; elim: k fge =>
      [//|k IH [//|a' n' [/= /andP [/andP [Hn _] _]|a'' n'' fge'']]]
  ).
  ltac1:(
    by rewrite andbC /= andbC /= mulf_neq0
  ).
  ltac1:(
    move => /= /andP [/andP [Hn /andP [/andP [Hn' Hfge] Ha] Ha']];
    apply /mkFGcons_reduced /mkFGcons_reduced /FGmul_reduced => [//|];
    by apply /IH; rewrite /= Hn Hn' Hfge Ha Ha'
  ).
Qed.

Definition FGpower (fge: FGExpr) (k: int): FGExpr :=
  match k with
  | Posz k' => FGpower' fge k'
  | Negz k' => FGinv (FGpower' fge (k'.+1))
  end.

Lemma FGpowerE: forall fge k,
  FGEval (FGpower fge k) == power (FGEval fge) k.
Proof.
  ltac1:(
    move => fge [|] k; first by rewrite FGpowerE'
  ).
  ltac1:(
    by rewrite FGinvE FGpowerE' NegzE power_inv
  ).
Qed.

Lemma FGpower_reduced: forall fge k,
  FGreduced fge -> FGreduced (FGpower fge k).
Proof.
  ltac1:(
    move => fge [|] k H; first by apply FGpower_reduced'
  ).
  ltac1:(
    rewrite FGinv_reduced //; by apply FGpower_reduced'
  ).
Qed.

Fixpoint FGvar (fg: FG): FGExpr :=
  match fg with
  | [::] => FGnil
  | [:: Base a & fg'] => mkFGcons a 1 (FGvar fg')
  | [:: Inverse a & fg'] => mkFGcons a (-1) (FGvar fg')
  end.

Lemma FGvarE: forall fg,
  FGEval (FGvar fg) == fg.
Proof.
  ltac1:(
    elim => [//|[|] a fg IH /=];
      by rewrite mkFGconsE IH ?power_inv power1 neutral_right
  ).
Qed.

Lemma FGvar_reduced: forall fg,
  FGreduced (FGvar fg).
Proof.
  ltac1:(
    elim => [//|[|] a fg IH /=];
      by rewrite mkFGcons_reduced
  ).
Qed.


Fixpoint GExpr_norm (ge: GExpr): FGExpr :=
  match ge with
  | Gmul ge1 ge2 => FGmul (GExpr_norm ge1) (GExpr_norm ge2)
  | Gidn => FGnil
  | Ginv ge' => FGinv (GExpr_norm ge')
  | Gpow ge' n => FGpower (GExpr_norm ge') n
  | Gvar fg => FGvar fg
  end.

Lemma GExpr_normE: forall ge,
  FGEval (GExpr_norm ge) == GEval ge.
Proof.
  ltac1:(
    elim => /= [ge1 IH1 ge2 IH2|//|ge <-|ge IH n|ge]
  ).
  ltac1:(
    by rewrite FGmulE IH1 IH2
  ).
  ltac1:(
    by rewrite FGinvE
  ).
  ltac1:(
    by rewrite FGpowerE IH
  ).
  ltac1:(
    by rewrite FGvarE
  ).
Qed.

Lemma GExpr_norm_reduced: forall ge,
  FGreduced (GExpr_norm ge).
Proof.
  ltac1:(
    elim => /= [ge1 IH1 ge2 IH2|//|ge IH|ge IH n|ge]
  ).
  ltac1:(
    by apply FGmul_reduced
  ).
  ltac1:(
    by apply FGinv_reduced
  ).
  ltac1:(
    by apply FGpower_reduced
  ).
  ltac1:(
    by apply FGvar_reduced
  ).
Qed.

Lemma FGreduced_freely_reduced: forall fge,
  FGreduced fge -> freely_reduced (FGEval fge).
Proof.
  ltac1:(
    elim => [_|a n fge /= IH /andP [/andP [Hn H]]];
      first by apply freely_reduced_nil
  ).
  ltac1:(
    move: {IH} H (IH H);
    case: fge => [/= _ _ _|a' n' fge' /= /andP [/andP [Hn' Hfge'] Ha IH Ha']];
      first by rewrite /law /= cats0; apply freely_reduced_power1
  ).
  ltac1:(
    rewrite /law /=; apply freely_reduced_cat_overlap => [|//|];
      last by rewrite size_power; lia
  ).
  ltac1:(
    case: n Hn => [[//|]|] n _; case: n' Hn' {IH} => [[//|]|] n' _
  ).
    ltac1:(
      rewrite powerS -cat_law -FreeGroup_powerC' cats1 powerS -cat_law /=;
      apply freely_reduced_cat => [//||]
    ).
      ltac1:(
        rewrite -cats1 FreeGroup_powerC' cat_law -powerS;
        by apply freely_reduced_power1
      ).
      ltac1:(
        rewrite cons_law -powerS;
        by apply freely_reduced_power1
      ).
    ltac1:(
      rewrite powerS -cat_law -FreeGroup_powerC' cats1 powerP -cat_law /=;
      apply freely_reduced_cat => [[] H||];
        first by move: Ha'; rewrite H => /eqP
    ).
      ltac1:(
        rewrite -cats1 FreeGroup_powerC' cat_law -powerS;
        by apply freely_reduced_power1
      ).
      ltac1:(
        rewrite cons_law -FreeGroup_inv1 -powerP;
        by apply freely_reduced_power1
      ).
    ltac1:(
      rewrite powerP -cat_law -FreeGroup_powerC'' cats1 powerS -cat_law /=;
      apply freely_reduced_cat => [[] H||];
        first by move: Ha'; rewrite H => /eqP
    ).
      ltac1:(
        rewrite -cats1 FreeGroup_powerC'' cat_law -powerP;
        by apply freely_reduced_power1
      ).
      ltac1:(
        rewrite cons_law -powerS;
        by apply freely_reduced_power1
      ).
    ltac1:(
      rewrite powerP -cat_law -FreeGroup_powerC'' cats1 powerP -cat_law /=;
      apply freely_reduced_cat => [//||]
    ).
      ltac1:(
        rewrite -cats1 FreeGroup_powerC'' cat_law -powerP;
        by apply freely_reduced_power1
      ).
      ltac1:(
        rewrite cons_law -FreeGroup_inv1 -powerP;
        by apply freely_reduced_power1
      ).
Qed.

Lemma FreeGroup_norm_GEval:
  forall ge, FreeGroup_norm (GEval ge) = FGEval (GExpr_norm ge).
Proof.
  ltac1:(
    move => ge; rewrite -GExpr_normE;
    symmetry; rewrite -freely_reduced_correct;
    apply FGreduced_freely_reduced;
    by apply GExpr_norm_reduced
  ).
Qed.


(*| Gmul : GExpr -> GExpr -> GExpr*)
(*| Gidn : GExpr*)
(*| Ginv : GExpr -> GExpr*)
(*| Gpow : GExpr -> int -> GExpr*)
(*| Gvar : FG -> GExpr.*)

End FreeGroupNormalizeTactic.

Section FreeGroupPowersTactic.

Definition cFGcons a (n: int) fge :=
  match fge with
  | FGnil => FGcons a n FGnil
  | FGcons a' n' fge' =>
    if (a == a')%B then
      FGcons a (n + n') fge'
    else
      FGcons a n fge
  end.

Lemma cFGconsE: forall a n fge,
  FGEval (cFGcons a n fge) ==
  power ([:: Base a] \mod P) n @ FGEval fge.
Proof.
  ltac1:(
    move => a n [//|a' n' fge'] /=;
    case: ifP => [/eqP <-|//];
    rewrite associativity -power_add // => ->;
    by rewrite power0 neutral_left
  ).
Qed.

Fixpoint cFGrcons (fge: FGExpr) a n: FGExpr :=
  match fge with
  | FGnil => cFGcons a n FGnil
  | FGcons a' n' fge' => cFGcons a' n' (cFGrcons fge' a n)
  end.

Lemma cFGrconsE: forall a n fge,
  FGEval (cFGrcons fge a n) ==
  FGEval fge @ power ([:: Base a] \mod P) n.
Proof.
  ltac1:(
    move => a n; elim => [|a' n' fge' IH] /=;
      first by rewrite neutral_left neutral_right
  ).
  ltac1:(
    by rewrite cFGconsE IH associativity
  ).
Qed.

Fixpoint cFGinv (fge: FGExpr): FGExpr :=
  match fge with
  | FGnil => FGnil
  | FGcons a' n' fge' => cFGrcons (cFGinv fge') a' (-n')
  end.

Lemma cFGinvE: forall fge,
  FGEval (cFGinv fge) == inv (FGEval fge).
Proof.
  ltac1:(
    elim => [|a n fge H] /=; first by rewrite inv_e
  ).
  ltac1:(
    by rewrite cFGrconsE H inverse_law power_inv
  ).
Qed.

Fixpoint cFGmul (fge1 fge2: FGExpr) {struct fge1}: FGExpr :=
match fge1 with
| FGnil => fge2
| FGcons a' n' fge1' => cFGcons a' n' (cFGmul fge1' fge2)
end.

Lemma cFGmulE: forall fge1 fge2,
  FGEval (cFGmul fge1 fge2) == (FGEval fge1) @ (FGEval fge2).
Proof.
  ltac1:(
    elim => [|a n fge H] fge2 /=;
      first by rewrite neutral_left
  ).
  ltac1:(
    by rewrite cFGconsE H associativity
  ).
Qed.

Fixpoint cFGpower' (fge: FGExpr) (k: nat): FGExpr :=
  match k with
  | 0%N => FGnil
  | k'.+1 => cFGmul fge (cFGpower' fge k')
  end.

Lemma cFGpowerE': forall fge k,
  FGEval (cFGpower' fge k) == power (FGEval fge) k.
Proof.
  ltac1:(
    move => fge k; elim: k fge => [//|k IH fge /=];
    by rewrite cFGmulE IH
  ).
Qed.

Definition cFGpower (fge: FGExpr) (k: int): FGExpr :=
  match fge with
  | FGnil => FGnil
  | FGcons a n FGnil => FGcons a (n * k) FGnil
  | FGcons a n _ =>
    match k with 
    | Posz k' => cFGpower' fge k'
    | Negz k' => cFGinv (cFGpower' fge k'.+1)
    end
  end.

Arguments cFGpower fge / k.

Lemma cFGpowerE: forall fge k,
  FGEval (cFGpower fge k) == power (FGEval fge) k.
Proof.
  ltac1:(
    move => [/= k|a n [/= k|a' n' fge' [|] k /=]]
  ).
  ltac1:(
    by rewrite power_e
  ).
  ltac1:(
    by rewrite !neutral_right power_mul
  ).
  ltac1:(
    by rewrite cFGpowerE'
  ).
  ltac1:(
    by rewrite cFGinvE !cFGconsE cFGmulE cFGpowerE' /=
               NegzE power_inv powerS !associativity
  ).
Qed.


Fixpoint GExpr_collect (ge: GExpr): FGExpr :=
  match ge with
  | Gmul ge1 ge2 =>
    cFGmul (GExpr_collect ge1) (GExpr_collect ge2)
  | Gidn => FGnil
  | Ginv ge' => cFGinv (GExpr_collect ge')
  | Gpow ge' n => cFGpower (GExpr_collect ge') n
  | Gvar fg => FGvar fg
  end.

Lemma GExpr_collectE: forall ge,
  FGEval (GExpr_collect ge) == GEval ge.
Proof.
  ltac1:(
    elim => /= [ge1 IH1 ge2 IH2|//|ge <-|ge IH n|ge]
  ).
  ltac1:(
    by rewrite cFGmulE IH1 IH2
  ).
  ltac1:(
    by rewrite cFGinvE
  ).
  ltac1:(
    by rewrite cFGpowerE IH
  ).
  ltac1:(
    by rewrite FGvarE
  ).
Qed.


End FreeGroupPowersTactic.
End FreeGroupTactic.

Ltac2 rec reify g :=
  lazy_match! g with
  | law ?g1 ?g2  =>
    let ge1 := reify g1 in
    let ge2 := reify g2 in
      '(Gmul $ge1 $ge2)
  | e => 'Gidn
  | inv ?g' =>
    let ge' := reify g' in
      '(Ginv $ge')
  | power ?g' ?n' =>
    let ge' := reify g' in
      '(Gpow $ge' $n')
  | _ => '(Gvar $g)
  end.

Ltac2 free_group_normalize () :=
  lazy_match! goal with
  | [|- context [FreeGroup_norm ?g]] =>
      let ge := reify g in
        ltac1:(x |- rewrite (FreeGroup_norm_GEval x) /=) (Ltac1.of_constr ge)
  end.

Ltac2 free_group_collect_powers () :=
  lazy_match! goal with
  | [|- context [FreeGroup_norm ?g]] =>
      let ge := reify g in
        ltac1:(x |- move: (GExpr_collectE x) => /= <-) (Ltac1.of_constr ge)
  | [|- context [?g1 == ?g2]] =>
      let ge1 := reify g1 in
      let ge2 := reify g2 in
        ltac1:(x y |-
          move: (GExpr_collectE x) => /= <-;
          move: (GExpr_collectE y) => /= <-)
          (Ltac1.of_constr ge1)
          (Ltac1.of_constr ge2)
  end.
