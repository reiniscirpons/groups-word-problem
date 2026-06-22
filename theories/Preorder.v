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
  drop (divn (len - 1) 2) w.

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
  + move: (@sizelexi_total disp T w w') => Ht.
    rewrite Hf /= in Ht.
    move: (@sizelexi_total disp T w' w) => Ht'.
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
  + move: (@sizelexi_total disp T w w') => Ht.
    rewrite Hf /= in Ht.
    move: (@sizelexi_total disp T w' w) => Ht'.
    rewrite Hf' /= in Ht'.
    apply: sizelexi_anti; apply/andP; split; by done.
Qed.  

Definition transform (w: seq T Normalisation inv) :=
  let l1 := (half (Normalisation w)) in
  let l2 := (inv (upperhalf (Normalisation w))) in
  [:: min_word l1 l2; max_word l1 l2].

Definition cmp_le (w w': seq T Normalisation inv) :=
  (transform w <= transform w')%O.

Definition cmp_lt (w w': seq T Normalisation inv) :=
  (transform w < transform w')%O.

Lemma lt_le_def (w w': seq T Normalisation inv) : cmp_lt w w' = cmp_le w w' && ~~ cmp_le w' w.
Proof.
  elim: w w' => [|x1 s1 H] [|x2 s2] // /=.
Qed.



Fact cmp_refl: reflexive cmp_le.
Proof.
  move => x.
  rewrite /cmp_le.
  by apply: sizelexi_refl.
Qed.

Fact cmp_trans: transitive cmp_le.
Proof.
  move => x y z H_xley H_ylez.
  rewrite /cmp_le in H_xley H_ylez.
  rewrite /cmp_le.
  apply: sizelexi_trans.
  by apply: H_xley.
  by apply: H_ylez.
Qed.

Lemma cmp_congr_left (u w w' : seq T Normalisation inv):
  (Normalisation u) = (Normalisation w) -> (cmp_le w w')%O -> (cmp_le u w')%O.
Proof.
  move => equw leww'.
  by rewrite /cmp_le /transform !equw; apply: leww'.
Qed.


Fact cmp_wf: well_founded (fun x y : seq T Normalisation inv => cmp_lt x y).
Proof.
  rewrite /cmp_lt /=.
  apply: (@wf_f _ _ cmp_lt (Order.lt) transform).
  by move => x y; rewrite /cmp_lt.
  apply /sizelexi_wf /sizelexi_wf /lt_wf.
Qed.

#[export]
HB.instance Definition _ := isPreorder.Build disp' (seq T Normalisation inv) lt_le_def cmp_refl cmp_trans.

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
