Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.


From mathcomp Require Import seq preorder order eqtype choice.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra div.
From mathcomp Require Import ring lra zify.

From GWP Require Import Equivalence EquivalenceAlgebra Presentation F2 WellFounded Sizelexi.

Local Open Scope order_scope.

Reserved Notation "x <=^pre y" (at level 70, y at next level).
Reserved Notation "x >=^pre y" (at level 70, y at next level).
Reserved Notation "x <^pre y" (at level 70, y at next level).
Reserved Notation "x >^pre y" (at level 70, y at next level).
Reserved Notation "x <=^pre y :> T" (at level 70, y at next level).
Reserved Notation "x >=^pre y :> T" (at level 70, y at next level).
Reserved Notation "x <^pre y :> T" (at level 70, y at next level).
Reserved Notation "x >^pre y :> T" (at level 70, y at next level).
Reserved Notation "<=^pre y" (at level 35).
Reserved Notation ">=^pre y" (at level 35).
Reserved Notation "<^pre y" (at level 35).
Reserved Notation ">^pre y" (at level 35).
Reserved Notation "<=^pre y :> T" (at level 35, y at next level).
Reserved Notation ">=^pre y :> T" (at level 35, y at next level).
Reserved Notation "<^pre y :> T" (at level 35, y at next level).
Reserved Notation ">^pre y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^pre y" (at level 70, no associativity).
Reserved Notation ">=<^pre x" (at level 35).
Reserved Notation ">=<^pre y :> T" (at level 35, y at next level).
Reserved Notation "x ><^pre y" (at level 70, no associativity).
Reserved Notation "><^pre x" (at level 35).
Reserved Notation "><^pre y :> T" (at level 35, y at next level).

Reserved Notation "x <=^pre y <=^pre z" (at level 70, y, z at next level).
Reserved Notation "x <^pre y <=^pre z" (at level 70, y, z at next level).
Reserved Notation "x <=^pre y <^pre z" (at level 70, y, z at next level).
Reserved Notation "x <^pre y <^pre z" (at level 70, y, z at next level).
Reserved Notation "x <=^pre y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^pre  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^pre y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^pre  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^pre".

Import Order.


Fact cmp_display (disp : disp_t) : disp_t.
Proof. exact: disp. Qed.

Fact InverseAlphabet_display: Order.disp_t.
Proof. exact: Order.Disp tt tt. Qed.

Fact prod_display: Order.disp_t.
Proof. exact: Order.Disp tt tt. Qed.

Module Import CmpSyntax.

Notation "<=^pre%O" := (@le (cmp_display _ _) _) : function_scope.
Notation ">=^pre%O" := (@ge (cmp_display _ _) _) : function_scope.
Notation ">=^pre%O" := (@ge (cmp_display _ _) _) : function_scope.
Notation "<^pre%O" := (@lt (cmp_display _ _) _) : function_scope.
Notation ">^pre%O" := (@gt (cmp_display _ _) _) : function_scope.
Notation "<?=^pre%O" := (@leif (cmp_display _ _) _) : function_scope.
Notation ">=<^pre%O" := (@comparable (cmp_display _ _) _) : function_scope.
Notation "><^pre%O" := (fun x y => ~~ (@comparable (cmp_display _ _) _ x y)) :
  function_scope.

Notation "<=^pre y" := (>=^pre%O y) : order_scope.
Notation "<=^pre y :> T" := (<=^pre (y : T)) (only parsing) : order_scope.
Notation ">=^pre y"  := (<=^pre%O y) : order_scope.
Notation ">=^pre y :> T" := (>=^pre (y : T)) (only parsing) : order_scope.

Notation "<^pre y" := (>^pre%O y) : order_scope.
Notation "<^pre y :> T" := (<^pre (y : T)) (only parsing) : order_scope.
Notation ">^pre y" := (<^pre%O y) : order_scope.
Notation ">^pre y :> T" := (>^pre (y : T)) (only parsing) : order_scope.

Notation "x <=^pre y" := (<=^pre%O x y) : order_scope.
Notation "x <=^pre y :> T" := ((x : T) <=^pre (y : T)) (only parsing) : order_scope.
Notation "x >=^pre y" := (y <=^pre x) (only parsing) : order_scope.
Notation "x >=^pre y :> T" := ((x : T) >=^pre (y : T)) (only parsing) : order_scope.

Notation "x <^pre y"  := (<^pre%O x y) : order_scope.
Notation "x <^pre y :> T" := ((x : T) <^pre (y : T)) (only parsing) : order_scope.
Notation "x >^pre y"  := (y <^pre x) (only parsing) : order_scope.
Notation "x >^pre y :> T" := ((x : T) >^pre (y : T)) (only parsing) : order_scope.

Notation "x <=^pre y <=^pre z" := ((x <=^pre y) && (y <=^pre z)) : order_scope.
Notation "x <^pre y <=^pre z" := ((x <^pre y) && (y <=^pre z)) : order_scope.
Notation "x <=^pre y <^pre z" := ((x <=^pre y) && (y <^pre z)) : order_scope.
Notation "x <^pre y <^pre z" := ((x <^pre y) && (y <^pre z)) : order_scope.

Notation "x <=^pre y ?= 'iff' C" := (<?=^pre%O x y C) : order_scope.
Notation "x <=^pre y ?= 'iff' C :> T" := ((x : T) <=^pre (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^pre y" := [pred x | >=<^pre%O x y] : order_scope.
Notation ">=<^pre y :> T" := (>=<^pre (y : T)) (only parsing) : order_scope.
Notation "x >=<^pre y" := (>=<^pre%O x y) : order_scope.

Notation "><^pre y" := [pred x | ~~ (>=<^pre%O x y)] : order_scope.
Notation "><^pre y :> T" := (><^pre (y : T)) (only parsing) : order_scope.
Notation "x ><^pre y" := (~~ (><^pre%O x y)) : order_scope.

End CmpSyntax.

Module CmpOrder.
Section CmpOrder.

Definition half {T: eqType} (w: seq T) :=
  let len := size w in
  take (divn (len + 1) 2) w.

Definition upperhalf {T: eqType} (w: seq T) :=
  let len := size w in
  drop (divn len 2) w.

Lemma half_oversized {T: eqType} (a u v : seq T) (leua: (size u <= size a)%N) (luva: (size v <= size a)%N) (eqsz: size u = size v):
  CmpOrder.half (a ++ u) = CmpOrder.half (a ++ v).
Proof.
  have eqsz_simpl: forall m w: seq T, ((size (m ++ w) + 1) %/ 2 < size m)%N = false -> (size w <= size m)%N -> ((size (m ++ w) + 1) %/2 = size m)%N.
    move => m w Heq2 Hleq.
    rewrite ltn_divLR //= in Heq2.
    rewrite size_cat muln2 -addnn -addnA ltn_add2l addn1  in Heq2.
    move/negbT in Heq2.
    rewrite -ltnNge ltnS in Heq2.
    case: (eqVneq (size m) (size w)) => [Heq | Hneq].
    - by rewrite size_cat Heq addnn -muln2 divnMDl // divn_small // addn0.
    - have Heq : size m = (size w).+1.
        rewrite eq_sym in Hneq.
        by apply/eqP; rewrite eqn_leq Heq2 (ltn_neqAle _ _) Hneq Hleq.
      by rewrite size_cat Heq addnS addSn addn0 addnn -muln2 -addn2 divnMDl // divnn /= addn1.

  have sz0: forall m w: seq T, ((size (m ++ w) + 1) %/ 2 < size m)%N = false -> (size w <= size m)%N -> ((size (m ++ w) + 1) %/2 - size m = 0)%N.
    move => m w Heq2 Hleq.
    rewrite eqsz_simpl; by lia.
  
  rewrite /CmpOrder.half !take_cat.

  case: ifP => [_ | Heq1].
  case: ifP => [_ | Heq2].
  by rewrite !size_cat eqsz.
  + rewrite sz0 //. 
    rewrite take0 cats0.
    rewrite eqsz_simpl //.
    by rewrite take_size.
    + by rewrite size_cat eqsz; rewrite size_cat in Heq2.

  case: ifP => [Heq1' | Heq2].
  + rewrite sz0 //.
    rewrite take0 cats0.
    rewrite eqsz_simpl //.
    by rewrite take_size.
    + by rewrite size_cat; rewrite size_cat eqsz in Heq1.
  + rewrite !sz0 //.
    by rewrite !take0 !cats0.
Qed.

Definition type (disp : Order.disp_t) T (Normalisation : seq T -> seq T) (inv: seq T -> seq T) := seq T.
Definition type_ (disp : Order.disp_t) (T : orderType disp) :=
  type (cmp_display disp) T.

Context {disp disp' : Order.disp_t}.

Local Notation seq := (type disp').


#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T id id).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T id id).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T id id).

Section Preorder.

Context (T : orderType disp) (Normalisation: seq.seq T -> seq.seq T) (inv: seq.seq T -> seq.seq T).

Hypothesis lt_wf : well_founded (@Order.lt _ T).

Definition min_word (w w': seq T Normalisation inv) :=
  if ((w <= w')%O) then w else w'.

Definition max_word (w w': seq T Normalisation inv) :=
  if ((w <= w')%O) then w' else w.

Lemma min_word_correct (w w' : seq T Normalisation inv) :
  (w <= w')%O -> min_word w w' = w.
Proof.
  move => H.
  rewrite /min_word.
  rewrite ifT //.
Qed.

Lemma min_wordC (w w' : seq T Normalisation inv) :
  min_word w w' = min_word w' w.
Proof.
  rewrite /min_word.
  rewrite /Order.le /=.
  case: ifP => [Ht | Hf].
  case: ifP => [Ht' | Hf'].
  + apply: sizelexi_anti; apply/andP; split; by done.
  + by [].
  case: ifP => [Ht' | Hf'].
  + by [].
  + move: (@sizelexi_total disp T (Order.le_total) w w') => Ht.
    rewrite Hf /= in Ht.
    move: (@sizelexi_total disp T (Order.le_total) w' w) => Ht'.
    rewrite Hf' /= in Ht'.
    apply: sizelexi_anti; apply/andP; split; by done.
Qed.  

Lemma max_word_correct (w w' : seq T Normalisation inv) :
  (w <= w')%O -> max_word w w' = w'.
Proof.
  move => H.
  rewrite /max_word.
  rewrite ifT //.
Qed.

Lemma max_wordC (w w' : seq T Normalisation inv) :
  max_word w w' = max_word w' w.
Proof.
  rewrite /max_word.
  rewrite /Order.le /=.
  case: ifP => [Ht | Hf].
  case: ifP => [Ht' | Hf'].
  + apply: sizelexi_anti; apply/andP; split; by done.
  + by [].
  case: ifP => [Ht' | Hf'].
  + by [].
  + move: (@sizelexi_total disp T (Order.le_total) w w') => Ht.
    rewrite Hf /= in Ht.
    move: (@sizelexi_total disp T (Order.le_total) w' w) => Ht'.
    rewrite Hf' /= in Ht'.
    apply: sizelexi_anti; apply/andP; split; by done.
Qed.  

Definition transform (w: seq T Normalisation inv) :=
  let l1 := (half (Normalisation w)) in
  let l2 := (inv (upperhalf (Normalisation w))) in
  [:: min_word l1 l2; max_word l1 l2].

Definition sz w := size (Normalisation w).

Definition cmp_le (w w': seq T Normalisation inv) :=
  (sz w < sz w')%N || ((sz w == sz w') && (transform w <= transform w')%O).

Definition cmp_lt (w w': seq T Normalisation inv) :=
  (sz w < sz w')%N || ((sz w == sz w') && (transform w < transform w')%O).

Lemma cmp_lt_le_def (w w': seq T Normalisation inv) : cmp_lt w w' = cmp_le w w' && ~~ cmp_le w' w.
Proof.
  case: (boolP (sz w < sz w')%N) => [Ht | Hf] /=.
  - rewrite /cmp_lt /cmp_le /= Ht /=.
    have H_nvleu: (sz w' <= sz w)%B = false.
      by apply: ltn_geF.
    have H_nvlte: ((sz w' < sz w)%N)%B = false.
      apply/negP; move => H; move/negP in H_nvleu.
      move/ltnW in H.
      contradiction.
    have H_nvequ: (sz w' == sz w)%B = false.
      rewrite eq_sym ltn_eqF => [ // | ].
      by rewrite Ht.
    by rewrite H_nvlte H_nvequ /=.
  - move/negPf in Hf.
    rewrite /cmp_le /cmp_lt Hf /=.
    case: (boolP (sz w == sz w')) => [HeqT | HeqF]; rewrite /=; last first.
      - by [].
      - rewrite eq_sym in HeqT.
        rewrite HeqT /=.
        have H_nlt: ((sz w' < sz w)%N)%B = false.
          move/eqP: HeqT => ->.
          by rewrite ltnn.
        rewrite H_nlt /=.
        by elim: w w' Hf HeqT H_nlt => [|x1 u H] [|x2 v] // /=.
Qed.

Fact cmp_refl: reflexive cmp_le.
Proof.
  move => x.
  rewrite /cmp_le; apply/orP; right; apply/andP; split; first by done.
  by apply: sizelexi_refl.
Qed.

Lemma cmp_sz_le u v : cmp_le u v -> sz u <= sz v.
Proof. by move=> /orP[/ltnW | /andP[/eqP -> _]]. Qed.

Fact cmp_trans: transitive cmp_le.
Proof.
  move=> v u w /orP[ltsz /cmp_sz_le | /andP[/eqP eqszuv leuv]].
  by move=> /(leq_trans ltsz) {}ltsz; apply/orP; left.
  move=> /orP[ltsz | /andP[/eqP eqszvw levw]].
    by apply/orP; left; rewrite eqszuv.
  apply/orP; right; rewrite eqszuv eqszvw eqxx /=.
  exact: (le_trans leuv levw).
Qed.

Lemma cmp_congr_left (u w w' : seq T Normalisation inv):
  (Normalisation u) = (Normalisation w) -> (cmp_le w w')%O -> (cmp_le u w')%O.
Proof.
  move => equw leww'.
  have eqszuw: sz u = sz w.
    by rewrite /sz equw.
  by rewrite /cmp_le /transform !equw !eqszuw; apply: leww'.
Qed.

Lemma wf_prodlexi {T1 T2 : eqType} (le1: T1 -> T1 -> bool)
    (lt1 : T1 -> T1 -> bool) (Hanti: forall x y, le1 x y = (x == y) || (lt1 x y)) (Hrefl: reflexive le1) (lt2 : T2 -> T2 -> bool)
    (wf1 : well_founded lt1) (wf2 : well_founded lt2) :
  well_founded (fun (p q : T1 * T2) => 
    le1 p.1 q.1 && (le1 q.1 p.1 ==> lt2 p.2 q.2)).
Proof.
  move => [a b]; move: b.
  elim/(well_founded_induction wf1): a => u0 IH1 b.
  elim/(well_founded_induction wf2): b => u1 IH2.
  apply: Acc_intro => [[x y] Pc].
  move/andP: Pc => [Hle Himp]; rewrite /= in Hle Himp.
  rewrite Hanti in Hle; move/orP in Hle; case: Hle => [/eqP Heq | Hlt]; last first.
    by apply: (IH1 x Hlt y).
    by rewrite Heq in Himp; move/implyP in Himp; move: (Himp (Hrefl u0)) => Hlt; rewrite Heq; apply: (IH2 y Hlt).
Qed.

Fact cmp_wf: well_founded (fun x y : seq T Normalisation inv => cmp_lt x y).
Proof.
  pose g w := (sz w, transform w) : nat *lexi[prod_display] _.
  rewrite /cmp_lt /=.
  apply: (@wf_f _ _ _ (Order.lt) g).
    move => x y; rewrite /cmp_lt /g; move => hcmp; rewrite ltEprodlexi /=; apply/andP; split.
    + case: (boolP (sz x < sz y)%N) => [Ht | Hf].
      - by apply: ltnW.
      - move/negPf in Hf; rewrite Hf /= in hcmp; move/andP: hcmp => [/eqP eqsz _].
        by rewrite eqsz.
    + apply/implyP => lesz; change (sz y <= sz x) with (sz y <= sz x)%N in lesz.
      by rewrite leqNgt in lesz; move/negPf in lesz; rewrite lesz /= in hcmp; move/andP: hcmp => [_ H].

    apply: wf_prodlexi; first by apply: leq_eqVlt.
    by done.
    by apply: wf_ltnat.
    rewrite /Order.lt /=.
    apply /sizelexi_wf /sizelexi_wf  /lt_wf.
Qed.

Section Total.

#[local] HB.instance Definition _  := Order.Le_isPreorder.Build sizelexidisplay
                               (seq T Normalisation inv) sizelexi_refl sizelexi_trans.

Lemma szlexi_ofseq_total: total (fun a b: seq.seq (seq T Normalisation inv) => (a <= b)%O).
Proof.
  move => w w'.
  rewrite /Order.le /=.
  by move: (@sizelexi_total sizelexidisplay (seq T Normalisation inv) (@sizelexi_total disp T (Order.le_total))) => H.
Qed.

Lemma cmp_total: total cmp_le.
Proof.
  move => x y.
  rewrite /cmp_le.
  case: (boolP (sz x < sz y)%N) => [Hlt | Hle]; rewrite /= => //.
  apply/orP; rewrite ltnNge negbK leq_eqVlt in Hle; move/orP: Hle => [/eqP Heq | Hlt].
  + rewrite !Heq ltnn /= !eqxx /=.
    rewrite /Order.le /=; apply/orP.
    by move: (@szlexi_ofseq_total) => Q; rewrite /total in Q; move: (Q (transform x) (transform y)) => Qinst.
  + by rewrite Hlt /=; right.
Qed.

End Total.

#[export]
HB.instance Definition _ := isPreorder.Build disp' (seq T Normalisation inv) cmp_lt_le_def cmp_refl cmp_trans.

End Preorder.

End CmpOrder.

Module Exports.

HB.reexport CmpOrder.

Notation seqcmp_with := type.
Notation seqcmp := type_.

End Exports.
End CmpOrder.
HB.export CmpOrder.Exports.

Module DefaultCmpOrder.
Section DefaultCmpOrder.

Context {disp: disp_t}.
Notation seqcmp := (seqcmp_with (cmp_display disp)).

HB.instance Definition _ (T : orderType disp) (Normalisation: seq T -> seq T) (inv: seq T -> seq T) :=
  Preorder.copy (seq T) (seqcmp T Normalisation inv).

Context {Sigma: finType}.

End DefaultCmpOrder.
End DefaultCmpOrder.



(* --------- *)

Section SigmaOrder.

Context {Sigma: finType}.

Definition lt_Sigma (x y : InverseAlphabet Sigma) :=
  (index x (InverseAlphabet_enum) < index y (InverseAlphabet_enum))%N.

Definition le_Sigma (x y : InverseAlphabet Sigma) :=
  (index x (InverseAlphabet_enum) <= index y (InverseAlphabet_enum))%N.

Fact le_refl: reflexive le_Sigma.
Proof.
  move => x.
  by rewrite /le_Sigma.
Qed.

Fact le_trans: transitive le_Sigma.
Proof.
  move => x y z H_xley H_ylez.
  rewrite /le_Sigma in H_xley H_ylez.
  rewrite /le_Sigma.
  apply: leq_trans.
  by apply: H_xley.
  by apply: H_ylez.
Qed.

Fact le_anti: antisymmetric le_Sigma.
Proof.
  move => x y H; move/andP: H => [H_xley  H_ylex].
  rewrite /le_Sigma in H_xley H_ylex.
  have H_eq: (index x (InverseAlphabet_enum)) = (index y (InverseAlphabet_enum)).
    apply: anti_leq.
    rewrite H_xley H_ylex //=.
  apply: index_inj.
  by []. (* to help Rocq realise that InverseAlphabet is an eqType*)
  1-2: by apply: InverseAlphabet_enum_in.
  by apply: H_eq.
Qed.

HB.instance Definition _  := Order.Le_isPOrder.Build InverseAlphabet_display
                                (InverseAlphabet Sigma) le_refl le_anti le_trans.

Fact le_total: ssrbool.total le_Sigma.
Proof.
  rewrite /total.
  move => x y.
  by rewrite /le_Sigma leq_total.
Qed.

HB.instance Definition _  := Order.POrder_isTotal.Build InverseAlphabet_display
                                (InverseAlphabet Sigma) le_total.

Lemma lt_eq (x y : InverseAlphabet Sigma): is_true ((le_Sigma x y) && ~~ (le_Sigma y x)) = is_true (lt_Sigma x y).
Proof.
  rewrite /lt_Sigma /le_Sigma.
  rewrite -ltnNge.
  case: (boolP (index x InverseAlphabet_enum < index y InverseAlphabet_enum)%N) => [Ht | Hf]; last first.
    - by rewrite andbC /=.
    - rewrite /=.
      by rewrite ltnW.
Qed.

(* Note(mathis): weird proof because Rocq doesn't want to rewrite in a lambda *)
Fact le_wf: well_founded (fun (x y: F2_InverseAlphabet__canonical__Order_Total) => (x < y)%O).
Proof.
  rewrite /Order.lt /=.
  rewrite /le_Sigma.
  apply: Wf_nat.well_founded_lt_compat => x y H.
  have H_lt: ((fun z => index z InverseAlphabet_enum) x < (fun z => index z InverseAlphabet_enum) y)%N.
    rewrite ltnNge.
    by move/andP in H; move: H => [_ H].
  by apply/ ltP; apply: H_lt.
Qed.

End SigmaOrder.

(*
Section Test.
Context {Sigma: finType}.
Definition word := seqcmp (InverseAlphabet_display) (sigma (FGP Sigma)).

(* HB.instance Definition _ :=
  Preorder.copy (FreeGroup Sigma) (word). *)

Lemma test (x y : FreeGroup Sigma):
  (x < y :> word)%O -> ~ (y < x :> word)%O.
Proof.
  rewrite /Order.lt /=.

End Test.
*)