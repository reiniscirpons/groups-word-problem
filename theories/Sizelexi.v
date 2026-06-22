(** * The Short-Lexicographic order on words *)
(******************************************************************************)
(*      Copyright (C) 2025      Florent Hivert <florent.hivert@lri.fr>        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order.


From GWP Require Import WellFounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Order.TTheory.
Import Order.LexiSyntax.


Fact sizelexidisplay : Order.disp_t. Proof. exact: Order.Disp tt tt. Qed.

Section SizeLexi.

Context {d : Order.disp_t} {T : preorderType d}.
Implicit Types (u v w x y : seq T).


Definition sizelexi u v :=
  (size u < size v) || (size u == size v) && (u <= v :> seqlexi _)%O.

Lemma sizelexi_le u v : sizelexi u v -> size u <= size v.
Proof. by move=> /orP[/ltnW | /andP[/eqP -> _]]. Qed.

Fact sizelexi_refl : reflexive sizelexi.
Proof. by move=> u; rewrite /sizelexi eqxx lexx /= orbT. Qed.
(*Fact sizelexi_anti : antisymmetric sizelexi.
Proof.
move=> u v /andP[/orP[ltsz | /andP[/eqP eqsz leuv]]].
  move/orP => []; first by rewrite (leq_gtF (ltnW ltsz)).
  by rewrite (gtn_eqF ltsz).
move=> /orP[| /andP[_ levu]]; first by rewrite eqsz ltnn.
by apply/eqP; rewrite (eq_le (u : seqlexi _)) leuv levu.
Qed.*)
Fact sizelexi_trans : transitive sizelexi.
Proof.
move=> v u w /orP[ltsz /sizelexi_le | /andP[/eqP eqszuv leuv]].
  by move=> /(leq_trans ltsz) {}ltsz; apply/orP; left.
move=> /orP[ltsz | /andP[/eqP eqszvw levw]].
  by apply/orP; left; rewrite eqszuv.
apply/orP; right; rewrite eqszuv eqszvw eqxx /=.
exact: (le_trans leuv levw).
Qed.

HB.instance Definition _  := Order.Le_isPreorder.Build sizelexidisplay
                               (seq T) sizelexi_refl sizelexi_trans.

Fact nil_bot u : ([::] <= u)%O.
Proof.
rewrite /Order.le /= /sizelexi /= eq_sym.
by case: (boolP (size u == 0)) => [/nilP -> |]; last rewrite -lt0n => ->.
Qed.

Fact nil_bot2 u : ~~ (u < [::])%O.
Proof.
    rewrite /Order.lt /= /sizelexi.
    by case: (boolP (size u == 0)) => [/nilP -> |]; last rewrite -lt0n => ->.
Qed.

HB.instance Definition _  := Order.hasBottom.Build sizelexidisplay
                               (seq T) nil_bot.

Lemma le_sizelexiE u v :
  (u <= v)%O =
    (size u < size v) || (size u == size v) && (u <= v :> seqlexi _)%O.
Proof. by []. Qed.

Lemma lt_sizelexiE u v :
  (u < v)%O =
    (size u < size v) || (size u == size v) && (u < v :> seqlexi _)%O.
Proof.
  rewrite /Order.lt /=.
  case: (boolP (size u < size v)) => [Ht | Hf] /=.
  - rewrite /sizelexi Ht /=.
    have H_nvleu: (size v <= size u)%B = false.
      by apply: ltn_geF.
    have H_nvlte: (size v < size u)%B = false.
      apply/negP; move => H; move/negP in H_nvleu.
      move/ltnW in H.
      contradiction.
    have H_nvequ: (size v == size u)%B = false.
      rewrite eq_sym ltn_eqF => [ // | ].
      by rewrite Ht.
    by rewrite H_nvlte H_nvequ /=.
  - move/negPf in Hf.
    rewrite /sizelexi Hf /=.
    case: (boolP (size u == size v)) => [HeqT | HeqF]; rewrite /=; last first.
      - by [].
      - rewrite eq_sym in HeqT.
        rewrite HeqT /=.
        have H_nlt: (size v < size u)%B = false.
          move/eqP: HeqT => ->.
          by rewrite ltnn.
        rewrite H_nlt /=.
        by rewrite -lt_le_def.
Qed.


Lemma size_le_sizelexi u v : (u <= v)%O -> size u <= size v.
Proof. by rewrite le_sizelexiE => /orP[/ltnW|/andP[/eqP-> _]]. Qed.

Lemma lt_sizelexi_stable u v1 v2 w :
  (v1 < v2 -> (u ++ v1 ++ w) < (u ++ v2 ++ w))%O.
Proof.
rewrite !lt_sizelexiE => /orP[ltsz | /andP[/eqP eqsz ltlex12]].
  by rewrite !size_cat ltn_add2l ltn_add2r ltsz.
rewrite !size_cat eqsz ltnn eqxx /=.
elim: u => [/=| a u IHu]; last by rewrite /= ltxi_cons lexx.
elim: v1 v2 eqsz ltlex12 => [|h1 v1 IHv1] [|h2 v2]//= [{}/IHv1 rec].
rewrite !ltxi_cons => /andP[->]/= /implyP H.
by apply/implyP => /H/rec.
Qed.

Lemma lt_set_nth_sizelexi {eu : T} (u : seq T) (i : nat) (bnd: i < size u) (a : T) (alt: (a < nth eu u i)%O):
  ((set_nth eu u i a) < u)%O.
Proof.
  have sz: size (set_nth eu u i a) = size u.
    rewrite size_set_nth /maxn.
    case: (boolP (i.+1 < size u)) => [Hlt | Heq] //=.
      - rewrite -leqNgt in Heq.
        by apply/eqP; rewrite eqn_leq Heq andbT.
  have Hdec_u: u = (rcons (take i u) (nth eu u i)) ++ drop (i.+1) u.
    rewrite -take_nth.
    by rewrite cat_take_drop.
    by [].
  rewrite -cats1 in Hdec_u.
  rewrite {2}Hdec_u.
  rewrite set_nthE bnd -cat1s -catA.
  rewrite lt_sizelexi_stable //=.
  rewrite lt_sizelexiE.
  rewrite /= /Order.lt /=.
  apply/andP; split.
    - by apply:ltW.
    - apply/implyP => Habs.
      have Habs2: (nth eu u i < nth eu u i)%O.
        apply: le_lt_trans.
        by apply: Habs.
        by apply: alt.
      by rewrite -(@ltxx d _ (nth eu u i)).
Qed.

Lemma pointwise_le_seq {eu : T} (u v : seq T) :
  size u = size v ->
  (forall i, i < size u -> nth eu u i <= nth eu v i)%O ->
  (u <= v)%O.
Proof.
  elim: u v => [| a u IHu] [| b v] //= size_eq Hpointwise.
  - rewrite le_sizelexiE /=.
    move/eqP in size_eq; rewrite size_eq /=.
    have Hleq : ((a :: u <= b :: v :> seqlexi _)%O).
      rewrite lexi_cons.
      apply/andP; split.
      + move: (Hpointwise 0) => Hab.
        rewrite /Order.lt /= ltn0Sn in Hab.
        by move: (Hab erefl) => Hab'.
      + apply/implyP; move => Hhead.
        move/eqP in size_eq; move/eq_add_S in size_eq.
        have HpointwiseW : (forall i : nat, (i < size u)%O -> (nth eu u i <= nth eu v i)%O).
          move => i hbound.
          have hinter: (nth eu (a :: u) (i.+1) <= nth eu (b :: v) (i.+1))%O.
            by apply: Hpointwise.
          by rewrite -nth_behead /= in hinter.
        have hleq : (u <= v)%O.
          by apply (@IHu v size_eq HpointwiseW).
        by rewrite le_sizelexiE size_eq eqxx ltnn /= in hleq.
    by rewrite Hleq orbC.
Qed.

End SizeLexi.


Section SizelexiWF.
Context {disp : Order.disp_t} {T : preorderType disp}.
Implicit Types (u v w : seq T).

Hypothesis Twf : well_founded (@Order.lt _ T).

Lemma sizelexi_wf : well_founded (@Order.lt _ (seq T)).
Proof.
pose ltb b u v := ((size v <= b) && (u < v)%O).
suff bwf bnd : well_founded (ltb bnd).
  move=> u; have [n] := ubnPleq (size u).
  elim/(well_founded_induction (bwf n)): u => u IHu szu.
  apply: Acc_intro => y ltyu; apply: IHu; first by rewrite /ltb szu ltyu.
  exact (leq_trans (size_le_sizelexi (ltW ltyu)) szu).
elim: bnd => [| bnd IHbnd].
  move=> u; apply: Acc_intro => y /andP[/[!leqn0]/nilP ->].
  move => H.
  have H_contra: ~~ (y < [::])%O.
    by apply: nil_bot2.
  by move: H => -> in H_contra.

have rec u : size u <= bnd -> Acc (ltb bnd.+1) u.
  elim/(well_founded_induction IHbnd) : u => u IHu szu.
  apply: Acc_intro => v /andP[_ ltvu]; apply IHu; first by rewrite /ltb szu ltvu.
  exact: (leq_trans (size_le_sizelexi (ltW ltvu)) szu).
suff rec' u : size u <= bnd.+1 -> Acc (ltb bnd.+1) u.
  move=> u; apply: Acc_intro => y /andP[szu /ltW/size_le_sizelexi].
  by move/leq_trans/(_  szu); apply: rec'.
rewrite leq_eqVlt => /orP[/eqP szu|]; last exact: rec.
case: u szu => [//| u0 u] /= [szu].

elim/(well_founded_induction Twf): u0 u szu => [u0 IHm].
elim/(well_founded_induction IHbnd) => u IHu szu.

apply: Acc_intro => w /andP[/= _].
rewrite lt_sizelexiE /= ltnS => /orP[|].
  by rewrite szu; apply: rec.
case: w => [//| a v] /= /andP[/eqP[/[!szu] szv]].

rewrite Order.SeqLexiOrder.ltxi_cons.
move=> H_lt.

case: (boolP (u0 <= a)%O) => [H_equiv | H_strict].

- move: H_lt.
  rewrite H_equiv /= => ltlvu.
  move/andP: ltlvu => [H_leau0 H_ltnvu].
  apply: Acc_intro => y Hlty.
  have Hltb: ltb bnd v u.
    rewrite /ltb szu leqnn /= lt_sizelexiE.
    by rewrite szu szv eqxx /= H_ltnvu orbC /=.
  move: (IHu v Hltb szv) => IHuv.
  apply: (Acc_inv IHuv).
  rewrite /ltb /= szv ltnSn /=.
  rewrite /ltb /= szv ltnSn /= in Hlty.
  rewrite lt_sizelexiE in Hlty; move/orP in Hlty.
  rewrite lt_sizelexiE.
  have H_eqsize: size (a :: v) = size (u0 :: v).
      by rewrite /=.
  case: Hlty => [Hsize | Hlex].
    - by rewrite -H_eqsize Hsize /=.
    - move/andP: Hlex => [Hsize Hlex].
      rewrite Hsize /=.
      rewrite /Order.lt /=.
      have Hltu0v: (y < (u0 :: v) :> seqlexi _)%O.
        case: y Hsize Hlex => [| b w Hsize Hlex] //=.
          rewrite Order.SeqLexiOrder.ltxi_cons.
          apply/andP; split.
            - have H_blea: (b <= a)%O.
              rewrite (@Order.SeqLexiOrder.ltxi_lehead _ disp _ _ w _ v) => //.
            rewrite (@Order.PreorderTheory.le_trans _ _ a) => //.
          apply/implyP.
          move => leu0b.
          have leab : (a <= b)%O.
            rewrite (@Order.PreorderTheory.le_trans _ _ u0) => //.
          rewrite Order.SeqLexiOrder.ltxi_cons in Hlex; move/andP: Hlex => [leba H_impl].
          move/implyP in H_impl.
          by apply: H_impl.
      rewrite /Order.lt /= in Hltu0v.
      by rewrite Hltu0v orbC.
- move/andP: H_lt => [leau0 H_impl].
  have ltau0: (a < u0)%O.
    by rewrite Order.PreorderTheory.lt_leAnge leau0 H_strict.
  by apply: IHm.
Qed.

End SizelexiWF.

Lemma sizelexi_nat_wf : well_founded (@Order.lt _ (seq nat)).
Proof. exact: sizelexi_wf wf_ltnat. Qed.

Section SizeLexiOrder.

Context {d : Order.disp_t} {T : orderType d}.
Implicit Types (u v w x y : seq T).

(* Total Orders *)


Fact sizelexi_anti : antisymmetric (@sizelexi d T).
Proof.
move=> u v /andP[/orP[ltsz | /andP[/eqP eqsz leuv]]].
  move/orP => []; first by rewrite (leq_gtF (ltnW ltsz)).
  by rewrite (gtn_eqF ltsz).
move=> /orP[| /andP[_ levu]]; first by rewrite eqsz ltnn.
by apply/eqP; rewrite (eq_le (u : seqlexi _)) leuv levu.
Qed.


Fact sizelexi_total : total (@sizelexi d T).
Proof.
rewrite /sizelexi => u v; case: (ltngtP (size u) (size v)) => cmpsz //=.
by case: (leP (u : seqlexi _) v) => //= /ltW.
Qed.

End SizeLexiOrder.