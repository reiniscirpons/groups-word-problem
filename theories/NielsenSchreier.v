(* TODO(mathis): import only required objects *)
From elpi.apps Require Import coercion.
From HB Require Import structures.

From Stdlib Require Import Recdef Program.
Require Import Setoid Morphisms.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import all_ssreflect path.
From mathcomp Require Import order preorder.
From mathcomp Require Import eqtype seq fintype all_algebra div.
From mathcomp Require Import ring lra zify.

Import GRing.Theory.

From GWP Require Import Utils Equivalence EquivalenceAlgebra Presentation F2 GeneratedSubgroup Sizelexi WellFounded Preorder.

Open Scope ring_scope.

Import PresentationNotations.


Section SeqExtension.

Lemma map_set_nth {A B: Type} {e: A} (l: seq A) (f: A -> B) (k: A):
  forall i, [seq f x | x <- set_nth e l i k] = set_nth (f e) [seq f x | x <- l] i (f k).
Proof.
  elim: l.
    - move => i.
      rewrite /= set_nth_nil set_nth_nil.
      rewrite /ncons.
      elim: i.
        - by rewrite /=.
        - move => n Hn.
          by rewrite /= Hn.
    - move => a l IH i.
      elim: i.
        - by rewrite /=.
        - move => n _.
          rewrite /=.
          move: (IH n) => IHn.
            by rewrite IHn.
Qed.

Lemma mem_zip_nth {A B : eqType} {ea: A} {eb: B} {a: A} {b: B} (l: seq A) (k: seq B) (H_size: size l = size k) (i : nat) (H_in: nth (ea, eb) (zip l k) i = (a, b)):
  nth ea l i = a /\ nth eb k i = b.
Proof.
  have H_zip_size: size (zip l k) = size l.
    by rewrite size_zip H_size minnn.
  rewrite nth_zip in H_in; first last.
    by [].
  case: H_in => [H_ntha H_nthb].
  split.
    - by [].
    - by [].
Qed.

Lemma mem_zip {A B : eqType} {ea: A} {eb: B} {a: A} {b: B} (l: seq A) (k: seq B) (H_size: size l = size k) (s: seq (A * B)) (H_zip: s = zip l k) (H_in: (a, b) \in s):
  a \in l /\ b \in k.
Proof.
  have H_zip_size: size (zip l k) = size l.
    by rewrite size_zip H_size minnn.
  rewrite H_zip in H_in.
  move/nthP in H_in.
  move: (H_in (ea, eb)) => [i [H_bound H_nth]].
  rewrite nth_zip in H_nth; first last.
    by [].
  case: H_nth => [H_ntha H_nthb].
  split.
    -apply/nthP.
      exists (i).
        by rewrite -H_zip_size.
        by apply: H_ntha.
    -apply/nthP.
      exists (i).
        by rewrite -H_size -H_zip_size.
        by apply: H_nthb.
Qed.

Lemma perm_eq_head {A: eqType} (l : seq A) (x : A) (H_in: x \in l):
  perm_eq (x :: rem x l) l.
Proof.
  move: H_in.
  elim l => //=.
  move => a s IH H_xin_as.
  case: (a =P x) => [Ht | Hf].
    - by rewrite Ht.
    - rewrite in_cons in H_xin_as.
      rewrite eq_sym in H_xin_as; move/eqP in Hf; rewrite (negPf Hf) /= in H_xin_as; move/eqP in Hf.
      change [:: x,  a  & rem (T:=A) x s] with ([:: x; a] ++ (rem (T:=A) x s)).
      have H_permeq : perm_eq ([:: x; a] ++ rem (T:=A) x s) ([:: a; x] ++ rem x s).
        rewrite perm_cat2r.
        change [:: x; a] with ([:: x] ++ [:: a]).
        change [:: a; x] with ([:: a] ++ [:: x]).
        rewrite permEl.
        by [].
        by apply: perm_catC.
      apply: perm_trans.
        by apply: H_permeq.
      change ([:: a; x] ++ rem x s) with ([:: a, x & rem x s]).
      rewrite perm_cons.
      by apply: IH.
Qed.

Lemma in_sumn (l : seq nat) (x: nat) (H_in: x \in l):
  (x <= sumn l)%N.
Proof.
  have H_perm: perm_eq (x :: rem x l) l.
    by rewrite perm_eq_head.
  move/nthP in H_in; case (H_in 0) => [i Hbound Heq_nth].
  rewrite (@perm_sumn _ (x :: rem x l)); last first.
    by rewrite perm_sym.
  by rewrite /sumn /= leq_addr.
Qed.

End SeqExtension.

Section Enumerate_Type.

Context {A: Type}.
Context {ea: A}.
Context {enat: nat}.

Definition enumerate (l : seq A) :=
  zip (iota 0 (size l)) l.

Lemma size_enumerate (l : seq A):
  size (enumerate l) = size l.
Proof.
  by rewrite /enumerate size_zip size_iota minnn.
Qed.

Lemma nth_enumerate (l : seq A):
  forall i, (i < size l)%N -> nth (enat, ea) (enumerate l) i = (i, nth ea l i).
Proof.
  move => i H_bound.
  rewrite /enumerate nth_zip.
  f_equal.
  rewrite nth_iota.
  by [].
  by [].
  by apply: size_iota.
Qed.

End Enumerate_Type.

Section Enumerate_eqType.

Context {A : eqType}.
Context {ea : A}.
Context {enat: nat}.

Lemma bound_enumerate (l : seq A) (j : nat) (x : A):
  (j, x) \in enumerate l -> (j < size l)%N.
Proof.
  move => H.
  move/nthP in H.
  move: (H (enat, ea)) => [i H_bound] Heq_nth.
  rewrite nth_enumerate in Heq_nth.
  
  case: Heq_nth => [Heq_ij Heq_res].
  by rewrite size_enumerate Heq_ij in H_bound.
  by rewrite size_enumerate in H_bound.
Qed.


Lemma in_enumerate (l : seq A) (j : nat) (x : A):
  (j, x) \in enumerate l -> nth ea l j = x.
Proof.
  move => H.
  move/nthP in H.
  move: (H (enat, ea)) => [i H_bound] Heq_nth.
  rewrite nth_enumerate in Heq_nth.
  
  case: Heq_nth => [Heq_ij Heq_res].

  rewrite -Heq_ij.
  by [].
  by rewrite size_enumerate in H_bound.      
Qed.

End Enumerate_eqType.

Section CartesianProduct.

Context {A: eqType}.
Context {ea: A}.
Context {enat: nat}.

Function cartesian_product (n: nat) (l : seq A): seq (n.-tuple A) := match n with
  | 0%N => [:: [tuple]]
  | S k => [seq cons_tuple a t | a <- l, t <- (cartesian_product k l)]
  end.

Lemma cartesian_product_correct {n: nat} (l : seq A):
  forall (v: seq A), size v = n -> (forall i, (nth ea v i) \in l) -> v \in [seq tval t | t <- cartesian_product n l].
Proof.
  elim n.
    - rewrite /=.
      move => v H_size; move/eqP in H_size; move: H_size.
      rewrite size_eq0.
      move => Hv.
      move/eqP in Hv.
      by rewrite Hv.
    - move => k IH.
      move => v.
      rewrite /cartesian_product.
      move => H_size.
      case: v H_size => [| a t] //= H_size.
      case: H_size => H_size.
      move => H_allin.
      move: (H_allin 0) => H_ain.
      rewrite /= in H_ain.
      move: (IH t) => H_tin.
      have H_allin_t: (forall i : nat, nth ea t i  \in l).
        move => i.
        move: (H_allin (i.+1)) => H_sol.
        by rewrite -nth_behead /= in H_sol.
      move: (H_tin (H_size) H_allin_t) => H_tin'.
      apply/mapP.
      have H_size_at: size (a :: t) = k.+1.
        rewrite /=.
        by apply f_equal.
      move/eqP in H_size_at.
      have H_size_t: (size t == k)%B.
        by move/eqP in H_size.
      pose t_uple := Tuple (H_size_t).
      exists (cons_tuple a t_uple).
        apply/allpairsP.
        move/mapP in H_tin'.
        case: H_tin' => [x Hx].
        exists ((a, x)).
          split.
            - by rewrite /=.
            - rewrite /=.
              by apply: Hx.
          apply: f_equal.
          rewrite /=.
          by apply/eqP; rewrite -val_eqE /=; apply/eqP.
        rewrite /t_uple.
        apply/eqP.
        by rewrite /cons_tuple /=.
Qed.

Lemma tnth_cartesian_product {n: nat} (l : seq A) (t: n.-tuple A) (H_in: t \in (cartesian_product n l)) (k : 'I_n):
  tnth t k \in l.
Proof.
  move: t H_in k.
  elim n.
  - rewrite /=.
    move => t H_int.
    move => k.
    case: k.
    by [].
  move => n0 IH t.
  rewrite /cartesian_product.
  move => H_tin.
  move/allpairsP in H_tin.
  case: H_tin => p.
  move => H.
  case H => Hin_p1 Hin_p2 H_cons.
  case => k.
  case: (k =P 0) => [Ht | Hf].
    - rewrite Ht.
      move => Hbound_0.
      have H_is_ord0 : (Ordinal (n:=n0.+1) (m:=0) Hbound_0) = ord0 by apply/val_inj.
      rewrite H_is_ord0.
      by rewrite H_cons tnth0.
    - case: k Hf.
        - by [].
        - move => m Hnon0 Hbound_m.
          rewrite H_cons.
          have -> : Ordinal Hbound_m = (lift (ord0 : 'I_n0.+1) (Ordinal (n:=n0) (m:=m) Hbound_m)) by apply/val_inj.
          rewrite tnthS.
          apply: IH.
          by apply: Hin_p2.
Qed.


End CartesianProduct.


Section Nielsen_Construction.

Context {Sigma: finType}.

Notation word := (FreeGroup Sigma).
Notation vec := (seq word).

Definition t3 (v: vec) := 
  filter (fun elm => negb (FreeGroup_dec_eq Sigma elm e)) v. (* need to change *)

Definition t2 (v: vec) (i j : nat) (h: i <> j) :=
  let u_j := nth e v j in
  let u_i := nth e v i in
  set_nth e v i (FreeGroup_norm (u_i @ u_j)).

Definition t1 (v: vec) (i : nat) :=
  let u_i := nth e v i in
  set_nth e v i (FreeGroup_norm (inv u_i)).

End Nielsen_Construction.



Section Definitions.

Context {Sigma: finType}.
Notation word := (FreeGroup Sigma).
Notation vec := (seq word).

Context {gens U : vec}.

Definition bound (x: nat) := (x < size U)%N.
Definition non_trivial (x y : (FreeGroup Sigma)) := FreeGroup_norm (x @ y) <> e.
Definition sz (w: (FreeGroup Sigma)) := (size (FreeGroup_norm w)).

Definition cmp_ordered_word := seqcmp (InverseAlphabet_display) (sigma (FGP Sigma)) (FreeGroup_norm) (inv :> FreeGroup Sigma -> FreeGroup Sigma).
HB.instance Definition _ :=
  Order.Preorder.copy (FreeGroup Sigma) (cmp_ordered_word).

End Definitions.

Section WordSplitting.

Section lprefix.

Context {T: eqType}.

Lemma prefix_size (z x y: seq T) (prefxz: prefix x z) (prefyz: prefix y z) (sz: (size x <= size y)%N):
  prefix x y.
Proof.
  move/prefixP: prefxz => [s eqs].
  move/prefixP: prefyz => [s' eqs'].
  have prefcat: prefix x (y ++ s').
    by apply/prefixP; exists (s); rewrite -eqs.
  rewrite prefixE take_cat in prefcat.
  case: (boolP (size x < size y)%N) => [Ht | Hf].
  - rewrite Ht in prefcat.
    by rewrite prefixE.
  - have eqsz: size x = size y.
      apply/eqP; rewrite eqn_leq.
      by rewrite sz; rewrite ltnNge negbK in Hf; rewrite Hf.
    rewrite eqsz in prefcat.
    rewrite ifF in prefcat; last by apply: ltnn.
    rewrite subnn take0 cats0 in prefcat; move/eqP in prefcat.
    by rewrite prefcat prefix_refl.
Qed.

Lemma prefix_eq (x y: seq T) (Hpref: prefix x y) (Hsz: size x = size y):
  x = y.
Proof.
  move/prefixP: Hpref => [s' eqy].
  rewrite eqy.
  have snil: s' = [::].
    apply: size0nil; move/(@f_equal _ _ size _ (x ++ s')) in eqy.
    rewrite size_cat Hsz in eqy.
    by lia.
  by rewrite snil cats0.
Qed.

Lemma cat_prefix (x y w w': seq T):
  prefix x y -> x ++ w = y ++ w' -> suffix w' w.
Proof.
  move=> /prefixP [v ->] Heq.
  rewrite -catA in Heq.
  move/eqP in Heq; rewrite eqseq_cat // eqxx /= in Heq; move/eqP in Heq.
  apply/suffixP.
  by exists v.
Qed.

Lemma prefix_leq_lexi  {disp: Order.disp_t} {A : preorderType disp} (x y: seq A) :
  prefix x y -> (x <= y :> seqlexi _)%O.
Proof.
  move: x.
  elim: y => [x prefx | a l IH].
  + rewrite prefixs0 in prefx; move/eqP in prefx.
    by rewrite prefx.
  + case => [// | a' l' prefx].
    rewrite prefix_cons in prefx; move/andP: prefx => [eqa'a prefixl'l].
    rewrite lexi_cons; apply/andP; split; first by move/eqP in eqa'a; rewrite eqa'a.
    apply/implyP => leqaa'.
    by apply: IH.
Qed.

Lemma prefix_lt_lexi {disp: Order.disp_t} {A : preorderType disp} (x y z t : seq A) :
  x != [::] -> size x = size z -> prefix x y -> prefix z t ->
  (x < z :> seqlexi _)%O -> (y < t :> seqlexi _)%O.
Proof.
  move: t x z.
  elim: y => [x z t| a l].
  + move => _ eqsz prefx prefzt ltxz.
    rewrite prefixs0 in prefx; move/eqP in prefx.
    rewrite prefx in ltxz.
    apply: Order.PreorderTheory.lt_le_trans.
    + by apply: ltxz.
    + by apply: prefix_leq_lexi.
  move => IH t; elim: t => [ | a' l' IH'] x z hdiff eqsz prefx preft Hlt.
  + rewrite prefixs0 in preft; move/eqP in preft.
    have habs: ([::] <= x :> seqlexi _)%O.
      by apply: lexi0s.
    have habs': ([::] < [::] :> seqlexi A)%O.
      apply: Order.PreorderTheory.le_lt_trans.
      + by apply: habs.
      + by rewrite preft in Hlt; apply: Hlt.
    rewrite Order.PreorderTheory.ltxx in habs'.
    by exfalso.
  + case: x prefx Hlt hdiff eqsz => [// | b s prefx Hlt hdiff eqsz].
  + case: z preft Hlt eqsz => [// | b' s'] preft Hlt eqsz.
    - rewrite prefix_cons in prefx; rewrite prefix_cons in preft; move/andP: prefx preft => [/eqP eqba prefsl] /andP [/eqP eqb'a' prefs'l'].
      rewrite /Order.lt /= in Hlt; move/andP: Hlt => [lebb' imp_le].
      rewrite /Order.lt /=; apply/andP; split.
      + by rewrite -eqba -eqb'a'.
      apply/implyP => lea'a; move/implyP in imp_le.
      rewrite -eqb'a' -eqba in lea'a; move: (imp_le lea'a) => less'.
      rewrite /= in eqsz; case: eqsz => eqsz.
      case: (boolP ((size s) == 0)%B) => [/eqP Habs | Hf].
      + rewrite Habs in eqsz.
        move/size0nil in Habs; symmetry in eqsz; move/size0nil in eqsz.
        rewrite Habs eqsz in less'.
        have  Habs': ([::] < [::] :> seqlexi A)%O.
          by rewrite /Order.lt /=.
        rewrite Order.PreorderTheory.ltxx in Habs'.
        by exfalso.
      + have sdiff0: s != [::].
          by apply/negP; move => /eqP habs; rewrite habs /= in Hf.
        by apply: (IH l' s s').
Qed.

Lemma size_take_simpl (s t: seq T) (k: nat) (eqsz: size s = size t):
  size (take k s) = size (take k t).
Proof.
  rewrite size_take.
  case: ifP => [Ht | Hf].
  + rewrite eqsz in Ht.
    rewrite size_take ifT //.
  + rewrite eqsz in Hf.
    rewrite size_take ifF //.
Qed.

Fixpoint lprefix (x y : seq T) := match x, y with
  | [::], _ => [::]
  | _, [::] => [::]
  | a::t, b::t' =>
    if (a == b) then
      a::(lprefix t t')
    else [::]
  end.

Lemma lprefix_neutral (a a': T) (diff: a <> a') (l l': seq _):
  lprefix (a::l) (a'::l') = [::].
Proof.
  rewrite /lprefix /=.
  rewrite ifF //.
  by apply/eqP.
Qed.

Lemma lprefix0nil (x: seq T):
  lprefix x [::] = [::].
Proof.
  rewrite /lprefix /=.
  case: x => //.
Qed.

Lemma lprefix_cons (a: T) (l l': seq _):
  lprefix (a::l) (a::l') = a::(lprefix l l').
Proof.
  rewrite {1}/lprefix /=.
  rewrite ifT //.
Qed.

Lemma lprefix_cat (v t t': seq T):
  lprefix (v ++ t) (v ++ t') = v ++ (lprefix t t').
Proof.
  elim: v => [|a l IH].
  - by rewrite !cat0s.
  - by rewrite [lprefix ((a :: l) ++ t) ((a :: l) ++ t')]lprefix_cons cat_cons IH.
Qed.

Lemma lprefix_correct_right (x y: seq T):
  prefix (lprefix x y) y.
Proof.
  elim: x y => [y| a l prefixly y].
  - by rewrite /=; apply /prefix0s.
  - elim: y => [| a' l' prefixall'] //.
    case: (a =P a') => [Ht | Hf].
    + by rewrite Ht lprefix_cons prefix_cons (prefixly l') andbC /=.
    + rewrite lprefix_neutral; first by apply /prefix0s.
      by assumption.
Qed.

Lemma lprefixC (x y : seq T):
  lprefix x y = lprefix y x.
Proof.
  elim: x y => [y | a l prefixly y].
  - by rewrite /= lprefix0nil.
  - case: y => [//| a' l'].
    case: (a =P a') => [Ht | Hf].
      - by rewrite Ht !lprefix_cons (prefixly l').
      - rewrite !lprefix_neutral //=.
        by apply /not_eq_sym.
Qed.

Lemma lprefix_correct_left (x y: seq T):
  prefix (lprefix x y) x.
Proof.
  by rewrite lprefixC lprefix_correct_right.
Qed.

End lprefix.

Context {Sigma: finType}.
Notation word := (FreeGroup Sigma).
Notation vec := (seq word).

Variable gens : vec.

Let U := gens ++ [seq (inv w) | w <- gens].

Definition lKprefix (x y : FreeGroup Sigma) :=
  lprefix (inv x) y.

Lemma size_inv (x: FreeGroup Sigma):
  size (inv x) = size x.
Proof.
  by rewrite /inv/=/inv_word/= size_map size_rev.
Qed.

Lemma inv_cat (x y: FreeGroup Sigma):
  inv (x ++ y :> FreeGroup Sigma) = inv y ++ inv x.
Proof.
  by rewrite /inv/=/inv_word/= map_rev map_cat rev_cat -!map_rev.
Qed.

Lemma inv_drop (x: FreeGroup Sigma) (k: nat):
  inv (drop k x:>FreeGroup Sigma) = take (size x - k) (inv x).
Proof.
  by rewrite /inv/=/inv_word/= rev_drop map_take.
Qed.

Lemma inv_eq_invol (x : FreeGroup Sigma):
  inv (inv x) = x.
Proof.
  rewrite /inv/=/inv_word/= !map_rev revK.
  elim: x => [// | a l IH].
  by rewrite map_cons invlK IH.
Qed.

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

Lemma freely_reduced_inv (x: FreeGroup Sigma) (frx: freely_reduced x):
  freely_reduced (inv x).
Proof.
  rewrite /inv /= /inv_word map_rev.
  apply freely_reduced_rev.
  elim: x frx => [ frx| a l IH frx].
  - by rewrite /=.
  - rewrite map_cons.
    elim: l IH frx  => [IH frx|a' l' IH IH' frx].
    - by rewrite /=; apply freely_reduced_cons1.
    - rewrite /=.
      apply /freely_reduced_cons2.
      + move => Habs.
        have Hcontradict: invl (invl a) = invl a'.
          by rewrite invlK in Habs; apply f_equal.
        rewrite invlK in Hcontradict.
        rewrite /freely_reduced in frx.
        move: (frx ([::]) (l') (a')) => frabs.
        rewrite Hcontradict cat0s in frabs.
        by [].
      + apply IH'.
        apply (@freely_reducedW _ ([:: a, a' &l'])) => //.
        apply/infixP.
        exists ([:: a]);
        exists ([::]).
        by rewrite cats0.
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


Lemma inv_cons (a : sigma (FGP Sigma)) (t : FreeGroup Sigma):
  inv (a :: t :> FreeGroup Sigma) = rcons (inv t) (invl a).
Proof.
  by rewrite /inv /= /inv_word map_rev map_cons rev_cons map_rev.
Qed. 


Lemma lKprefix_split (x y: FreeGroup Sigma) (frx: freely_reduced x) (fry: freely_reduced y):
  exists (w w': FreeGroup Sigma), (
    x = w ++ inv (lKprefix x y :> FreeGroup Sigma) /\
    y = (lKprefix x y) ++ w' /\
    freely_reduced (w ++ w')
  ).
Proof.
  have prefixx: prefix (lKprefix x y) (inv x).
    by rewrite /lKprefix lprefix_correct_left.
  have prefixy: prefix (lKprefix x y) y.
    by rewrite /lKprefix lprefix_correct_right.
  move/prefixP: prefixx => [s' eqs'].
  move/prefixP: prefixy => [sy' eqsy'].
  have approx: (x = inv (lKprefix x y ++ s' :> FreeGroup Sigma)).
    rewrite -eqs'.
    have ->: x = FreeGroup_norm x.
      by apply/freely_reduced_correct.
    rewrite -!FreeGroup_norm_inv (@FreeGroup_norm_unique  _ _ (inv (inv x))).
    + by [].
    by apply /symm /inv_involutive.

  rewrite /inv /= inv_word_cat in approx.
  exists (inv (s':>FreeGroup Sigma)).
  exists (sy':>FreeGroup Sigma).
  split.
  - by [].
  split.
  - by rewrite {1}eqsy'.
  case: s' eqs' approx => [eqs' appro | a l eqx approx].
  - rewrite /=.
    have yinfix: infix sy' y.
      apply/infixP.
      exists (lKprefix x y).
      exists ([::]).
      by rewrite cats0.
    by apply (@freely_reducedW _ y).
  - case: sy' eqsy' => [eqsy'|].
    - rewrite cats0; apply freely_reduced_inv.
      have frinvx: freely_reduced (inv x).
        by apply freely_reduced_inv.
      apply (@freely_reducedW _ (inv x)) => //.
      apply/infixP.
      exists (lKprefix x y).
      exists [::].
      by rewrite cats0.
    - move => a' l' eqy.
      rewrite inv_cons.
      apply freely_reduced_cat; last first.
      + apply (@freely_reducedW _ y) => //.
        apply/infixP.
        exists (lKprefix x y).
        exists ([::]).
        by rewrite cats0.
      + rewrite -inv_cons.
        apply freely_reduced_inv.
        apply (@freely_reducedW _ (inv x)).
        + by apply freely_reduced_inv.
        apply/infixP.
        exists (lKprefix x y).
        exists ([::]).
        by rewrite cats0.
      + (* the only part about the function *)
        move => Habs.
        have eqaa': invl (invl a) = invl (invl a').
          by rewrite (@f_equal _ _ invl _ (invl a')).
        rewrite !invlK  in eqaa'.
        rewrite eqaa' in eqx.
        have heq: lprefix (inv x) y = (lKprefix x y) ++ (lprefix (a'::l) (a'::l')).
          by rewrite {1}eqx {2}eqy lprefix_cat lprefix_cons.
        rewrite lprefix_cons /lKprefix in heq.
        have eqszabs: size (lprefix (inv x) y) = size (lprefix (inv x) y ++ a' :: lprefix l l').
          by rewrite (@f_equal _ _ size _ (lprefix (inv x) y ++ a' :: lprefix l l')).
        rewrite size_cat /= in eqszabs.
        by lia.
Qed.

Lemma invol_unique (x: FreeGroup Sigma):
  (x == inv x) -> x == e.
Proof.
  have: forall n (y: FreeGroup Sigma), (size y = n)%N -> y == inv y -> y == e.
    (* 2. Apply well-founded induction on the natural number n *)
    elim/ltn_ind=> n IH y Hsize Hinv.
    (* Case analysis on the size of the word *)
    case: n IH Hsize => [| [| n']] IH.
    - move=> /size0nil -> //.
      
    - move=> Hsize.
      case: y Hinv Hsize => [// | a l approx sz].
      rewrite /= in sz; move/succn_inj: sz => /size0nil sz0.
      rewrite sz0 in approx.
      have fra: [:: a] = FreeGroup_norm [:: a].
        by [].
      have frainv: inv ([:: a]: FreeGroup Sigma) = FreeGroup_norm (inv ([::a ]: FreeGroup Sigma)).
        by [].
      have: [:: a] = inv ([:: a]: FreeGroup Sigma).
        by rewrite fra frainv (@FreeGroup_norm_unique _ _ (inv ([::a]: FreeGroup Sigma))) //=.
      move => habs; rewrite /inv /= /inv_word /= in habs.
      have habs': nth a [:: a] 0 = nth a [:: invl a] 0.
        by rewrite habs.
      rewrite /= in habs'.
      exfalso.
      rewrite /invl /= /FreeGroup_invl in habs'.
      by case: a approx fra frainv habs habs' => approx fra frainv habs habs' //=.
      
    - (* Case n = n' + 2: x has at least 2 letters *)
      move=> Hsize.
      (* Deconstruct x into first letter, middle body, and last letter *)
      case: y Hinv Hsize => [//| a l approx szl].
      have lt0sz: (size l > 0)%N.
          rewrite /= in szl.
          case: szl => szl.
          by rewrite szl ltn0Sn.
      have eql': forall l, (0 < size l)%N -> l = rcons (take (size l - 1) l) (nth a l (size l -1)).
        move => l' lt0szl'.
        rewrite -take_nth.
        have ->: (size l' -1 ).+1 = size l'.
          by rewrite subn1 prednK.
        by rewrite take_size.
        by rewrite subn1 ltn_predL.

      set s := FreeGroup_norm ((a :: l): word).
      have leqsn'2: (size s <= n'.+2)%N.
        rewrite -szl.
        by apply: size_subseq; apply: FreeGroup_norm_subseq.

      have approxs: ((a :: l):>FreeGroup Sigma) == s.
        by apply /symm /FreeGroup_norm_correct.

      have eqsinvs: s = inv s.
        by rewrite -FreeGroup_norm_inv; apply FreeGroup_norm_unique.

      case: (boolP (size s > 0)%N) => [eqszs | eqs0]; last first.
      + rewrite ltnNge negbK leqn0 in eqs0; move/eqP: eqs0 => /size0nil eqs0.
        apply/FreeGroup_dec_eqP; rewrite /FreeGroup_dec_eq.
        change (FreeGroup_norm (a::l)) with s.
        by rewrite eqs0.
      case: s eqsinvs eqszs leqsn'2 approxs => [//| a' l'] eqsinvs eqszs leqsn'2 approxs.
      case: (boolP (size l' > 0)%N) => [eqszl'| habs];  last first.
      + rewrite ltnNge negbK leqn0 in habs; move/eqP: habs => /size0nil eqs0.
        rewrite eqs0 in eqsinvs; move: eqsinvs => habs.
        rewrite /inv /= /inv_word /= in habs.
        have habs': nth a' [:: a'] 0 = nth a' [:: invl a'] 0.
          by rewrite habs.
        rewrite /= in habs'.
        exfalso.
        rewrite /invl /= /FreeGroup_invl in habs'.
        by case: a' eqszs habs habs' leqsn'2 approxs => habs habs' leqsn'2 approxs //=.

      move: (eql' l' eqszl') => decl'; rewrite decl' in eqsinvs.
      rewrite /inv/=/inv_word/= rev_cons rev_rcons map_rcons map_cons rcons_cons in eqsinvs.
      case: eqsinvs => eqhead /rcons_inj [eqtail eqlast].
      rewrite /= in leqsn'2.
      have middle_trivial: (take (size l'-1) l' :> FreeGroup Sigma) == e.
        apply: IH; last first.
        by rewrite {1}eqtail.
        by apply: erefl.
        rewrite size_take.
        rewrite ifT.
        + apply: ltn_trans; last first.
          + by apply: leqsn'2.
           + 1-2: by rewrite subn1 ltn_predL.

      have tail_simpl: (l' :> FreeGroup Sigma) == [:: invl a'].
        rewrite decl' rcons_law eqlast congruent_right.
        + by apply: neutral_left.
        + by assumption.

      have s_trivial: ((a'::l'):>FreeGroup Sigma) == e.
        by rewrite cons_law tail_simpl invl_left.
      apply: trans.
      + by apply: approxs.
      + by assumption.

  move => H approx; apply: (H  (size x) x (erefl) approx).
Qed.

Lemma lKprefix_e (y: FreeGroup Sigma):
  lKprefix y y = y -> y == e.
Proof.
  move => H.
  rewrite /lKprefix in H.
  have pref: prefix y (inv y).
    by rewrite -{1}H; apply: lprefix_correct_left.
  have eqsz: size (inv y) = size y.
    by rewrite /inv/=/inv_word/= map_rev size_rev size_map.
  have eqyinvy: y = inv y.
    by apply: prefix_eq.
  have approxy: y == inv y.
    by rewrite -eqyinvy.
  by apply: invol_unique.
Qed.


Definition lKprefix_all (y: FreeGroup Sigma) :=
  sort (fun a b => (size b <= size a)%N) (
    filter (fun a => a != y) (
      map (fun x => lKprefix x y) U
    )
  ).

Lemma lKprefix_allW (y: FreeGroup Sigma) :
  forall z, z \in (lKprefix_all y) -> z \in [seq lKprefix x y | x <- U].
Proof.
  move => z zin.
  by rewrite /lKprefix_all mem_sort mem_filter in zin; move/andP: zin => [condz zin].
Qed.

Lemma lKprefix_all_nil (y : FreeGroup Sigma):
  (y \in U) -> lKprefix_all y = [::] -> y == e.
Proof.
  move => yinU H; rewrite /lKprefix_all in H. move/(@f_equal _ _ size _ [::]) in H; rewrite size_sort /= in H.
  rewrite size_filter in H; move/eqP in H.
  rewrite -[(count (fun a : presented (FGP Sigma) => a != y) [seq lKprefix x y  | x <- U] == 0%N)%B]negbK -lt0n in H.
  rewrite -has_count in H; move/hasPn in H.
  set l := [seq lKprefix x y | x <- U].
  have inmap: lKprefix y y \in l.
    by apply/mapP; exists (y).
  have eqpref: ~~ (lKprefix y y != y).
    by apply: H.
  rewrite negbK in eqpref; move/eqP in eqpref.
  by apply: lKprefix_e.
Qed.


Lemma lKprefix_all_split (y: FreeGroup Sigma) (yinU: y \in U) (Hnontrivial: FreeGroup_norm y <> e): {w: FreeGroup Sigma |
  w \in lKprefix_all y /\ w != y /\
  ((forall x, (lKprefix x y != y) -> (x \in U) -> prefix (lKprefix x y) w))}.
Proof.
  case eqt: (lKprefix_all y) => [| a l].
  + have habs: y == e  by apply: lKprefix_all_nil.
    have habs': FreeGroup_norm y = FreeGroup_norm e.
      by apply: FreeGroup_norm_unique.
    rewrite /= in habs'.
    contradiction.
  rewrite /lKprefix_all; rewrite /lKprefix_all in eqt.
  set t := sort (fun a b : seq (sigma (FGP Sigma)) => (size b <= size a)%N) [seq a <- [seq lKprefix x y  | x <- U]  | a != y].
  exists (a); split; first by apply: mem_head.
  split.
  + have: a \in t.
      by rewrite /t eqt; apply: mem_head.
    by rewrite /t mem_sort mem_filter => /andP [H _]. 

  move => x lKdiff xinU.
  have aint: a \in t.
    by rewrite /t eqt mem_head.
  rewrite mem_sort in aint.
  rewrite mem_filter in aint; move/andP: aint => [conda ain].
  move/mapP: ain => [z zinU eqza].

  have H_ordered : sorted (fun a b => (size b <= size a)%N) (a :: l).
    rewrite -eqt.
    apply: sort_sorted.
    move => c b; by apply: leq_total.
  rewrite sorted_pairwise in H_ordered; last first.
  + move => k m n leqkm leqnk.
    by apply: (leq_trans leqnk).
  rewrite pairwise_cons in H_ordered; move/andP: H_ordered => [hmax _].
  have all_ext: all (fun b => (size b <= size a)%N) (a::l).
    by rewrite /all; apply/andP; split.

  apply: (prefix_size y); first by apply: lprefix_correct_right.
  by rewrite eqza; apply: lprefix_correct_right.
  move/allP in all_ext.
  apply: all_ext.

  rewrite -eqt mem_sort mem_filter; apply/andP; split; first by [].
  by apply/mapP; exists (x).
Qed.

Hypothesis N0: forall x, (x \in U) -> FreeGroup_norm x <> e.
Hypothesis N1_left: forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) ->
  (sz (x @ y) >= sz(x))%N.
Hypothesis N1_right: forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) ->
  (sz(x @ y) >= sz(y))%N.

Lemma non_trivialC (x y: FreeGroup Sigma):
  non_trivial x y -> non_trivial y x.
Proof.
  move => H; rewrite /non_trivial -FreeGroup_norm_e; move => habs.
  have approx: y @ x == e.
    apply: (trans _ (FreeGroup_norm (y @ x))).
    + by apply /symm /FreeGroup_norm_correct.
    + by rewrite -FreeGroup_norm_e habs.
    move/(congruent_right (inv x)) in approx.
    rewrite -associativity neutral_left inverse_left neutral_right in approx.
    move/(congruent_left x) in approx.
    rewrite inverse_left in approx.
    apply: H.
    by rewrite -FreeGroup_norm_e (@FreeGroup_norm_unique _ _ e).
Qed.

Lemma non_trivial_inv (x a: FreeGroup Sigma) (ntrvxa: non_trivial x a):
  non_trivial (inv x) (inv a).
Proof.
  rewrite /non_trivial.
  have ->: FreeGroup_norm (inv x @ inv a) = inv (FreeGroup_norm (a @ x)).
    by rewrite -FreeGroup_norm_inv; apply: FreeGroup_norm_unique; rewrite inverse_law.
  move => heq; apply: (non_trivialC x a ntrvxa).
  move/(f_equal inv) in heq; rewrite inv_eq_invol in heq.
  by rewrite heq -FreeGroup_norm_e -FreeGroup_norm_inv; apply: FreeGroup_norm_unique; rewrite inverse_e.
Qed. 

Lemma lKprefix_contra (x y: FreeGroup Sigma)
(frx: freely_reduced x) (fry: freely_reduced y):
  FreeGroup_norm (x @ y) = e -> lKprefix x y = y.
Proof.
  move => approx.
  rewrite -FreeGroup_norm_e in approx.
  move/(FreeGroup_norm_cat _ _ e (inv y)) in approx.
  have eqfn: FreeGroup_norm ((x @ y) @ inv y) = FreeGroup_norm (x).
    apply: FreeGroup_norm_unique.
    by rewrite -associativity inverse_left neutral_right.
  have eqfinv: FreeGroup_norm (e @ inv y) = FreeGroup_norm (inv y).
    apply: FreeGroup_norm_unique.
    by rewrite neutral_left.
  rewrite eqfn eqfinv FreeGroup_norm_inv in approx.
  rewrite !freely_reduced_correct in frx fry.
  rewrite -frx -fry in approx. 
  have eqinvx: inv x = y.
    rewrite approx fry -!FreeGroup_norm_inv (@FreeGroup_norm_unique _ _ (y)); first by [].
    by apply: inv_involutive.
  by rewrite /lKprefix eqinvx -[y]cats0 lprefix_cat lprefix0nil.
Qed.

Lemma lKsize_right (x y: FreeGroup Sigma) (xinU: x \in U) (frx: freely_reduced x)
              (yinU: y \in U) (fry: freely_reduced y) (ntrivial: non_trivial x y):
  (size (lKprefix x y) * 2 <= (size y))%N.
Proof.
  move: (lKprefix_split x y frx fry) => [w [w' [eqx [eqy frprod]]]].
  have eqprod: (x @ y) == w ++ w'.
    by rewrite eqx {2}eqy !cat_law -associativity [inv (lKprefix x y :> FreeGroup Sigma) @ ((lKprefix x y :> FreeGroup Sigma) @ w')]associativity inverse_right neutral_left.
  move/FreeGroup_norm_unique in eqprod.
  have eqwcatw': w ++ w' = FreeGroup_norm (w ++ w').
    by rewrite -freely_reduced_correct.
  rewrite -eqwcatw' in eqprod.

  move/(@f_equal _ _ size _ (w++w')) in eqprod; rewrite size_cat in eqprod.
  move: (N1_left x y xinU yinU ntrivial) => leqsz.
  rewrite freely_reduced_correct in frx.
  rewrite /sz eqprod -frx eqx size_cat leq_add2l /inv/=/inv_word/= size_map size_rev in leqsz.
  rewrite {2}eqy size_cat.
  by rewrite muln2 -addnn leq_add2l.
Qed.

Lemma lKsize_left (x y: FreeGroup Sigma) (xinU: x \in U) (frx: freely_reduced x)
  (yinU: y \in U) (fry: freely_reduced y) (ntrivial: non_trivial x y):
  (size (lKprefix x y) * 2 <= (size x))%N.
Proof.
  move: (lKprefix_split x y frx fry) => [w [w' [eqx [eqy frprod]]]].
  have eqprod: (x @ y) == w ++ w'.
    by rewrite eqx {2}eqy !cat_law -associativity [inv (lKprefix x y :> FreeGroup Sigma) @ ((lKprefix x y :> FreeGroup Sigma) @ w')]associativity inverse_right neutral_left.
  move/FreeGroup_norm_unique in eqprod.
  have eqwcatw': w ++ w' = FreeGroup_norm (w ++ w').
    by rewrite -freely_reduced_correct.
  rewrite -eqwcatw' in eqprod.

  move/(@f_equal _ _ size _ (w++w')) in eqprod; rewrite size_cat in eqprod.
  move: (N1_right x y xinU yinU ntrivial) => leqsz.
  rewrite freely_reduced_correct in fry.
  rewrite /sz eqprod -fry eqy size_cat leq_add2r in leqsz.
  rewrite {2}eqx size_cat.
  by rewrite /inv/=/inv_word/= size_map size_rev muln2 -addnn leq_add2r.
Qed.


Lemma triplet_lt (x y z: FreeGroup Sigma) (frx: freely_reduced x) (fry: freely_reduced y) (frz: freely_reduced z)
  (xinU: x \in U) (yinU: y \in U) (zinU: z \in U) (non_trvxy: non_trivial x y) (non_trvyz: non_trivial y z):

  (((x @ y) < x :> word)%O) \/ ((((inv z @ inv y :> word) < (inv z))%O) \/ (exists u, u <> [::] /\ y = (lKprefix x y)  ++ u ++ inv (lKprefix y z :> FreeGroup Sigma))).
Proof.
  move: (lKprefix_split x y frx fry) => [a [w' [eqx [eqy frxy]]]].
  move: (lKsize_right x y xinU frx yinU fry non_trvxy) => Hszxy.
  move: (lKsize_left x y xinU frx yinU fry non_trvxy) => Hszx.

  move: (lKprefix_split y z fry frz) => [v [c [eqy' [eqz fryz]]]].
  move: (lKsize_right y z yinU fry zinU frz non_trvyz) => Hszz.
  move: (lKsize_left y z yinU fry zinU frz non_trvyz) => Hszyz.

  have leqszprefv: ((size v >= size (lKprefix x y))%N).
    rewrite -(leq_pmul2l (ltn0Sn 1)).
    apply: (@leq_trans (size y)).
    + by rewrite mulnC.
    move/(f_equal size) in eqy'; rewrite size_cat in eqy'.
    move/(congr1 (muln 2)) in eqy'; rewrite mulnDr /inv/=/inv_word/= size_map size_rev in eqy'.
    by rewrite -(@leq_add2r (2 * size (lKprefix y z))) -eqy' leq_add2l plusE addn0 mulnC.

  have leqszprefa: ((size a >= size (lKprefix x y))%N).
    rewrite -(leq_pmul2l (ltn0Sn 1)).
    apply: (@leq_trans (size x)).
    + by rewrite mulnC.
    move/(f_equal size) in eqx; rewrite size_cat in eqx.
    move/(congr1 (muln 2)) in eqx; rewrite mulnDr /inv/=/inv_word/= size_map size_rev in eqx.
    by rewrite -(@leq_add2r (2 * size (lKprefix x y))) -eqx leq_add2l plusE addn0 mulnC.

  have leqszprefc: ((size c >= size (lKprefix y z))%N).
    rewrite -(leq_pmul2l (ltn0Sn 1)).
    apply: (@leq_trans (size z)).
    + by rewrite mulnC.
    move/(f_equal size) in eqz; rewrite size_cat in eqz.
    move/(congr1 (muln 2)) in eqz; rewrite mulnDr in eqz.
    by rewrite -(@leq_add2l (2 * size (lKprefix y z))) -eqz mul2n -addnn mul2n -addnn leq_add2r addnn -muln2.

  have pref_lprefv: prefix (lKprefix x y) v.
    apply: (prefix_size y).
    + by rewrite /lKprefix lprefix_correct_right.
    + by rewrite eqy' prefix_prefix.
    + by apply: leqszprefv.
  move/prefixP: pref_lprefv => [u eqv].
  rewrite eqv in eqy'.

  case: (u =P [::]) => [Hempty | Hf]; last first.
  - right; right.
    exists(u); split; first by assumption.
    + by rewrite -catA in eqy'; apply: eqy'.
  rewrite Hempty cats0 in eqy'.

  move: eqy' eqy.
  set p := lKprefix x y.
  set q := lKprefix y z.
  move => eqy' eqy.

  have eqsz: size p = size q.
    move/(f_equal size) in eqy'; rewrite size_cat in eqy'.
    rewrite eqy' muln2 -addnn /inv/=/inv_word/= size_map size_rev leq_add2r in Hszyz.
    rewrite eqy' muln2 -addnn leq_add2l /inv/=/inv_word/= size_map size_rev in Hszxy.
    apply: anti_leq.
    + by rewrite Hszxy Hszyz.
  
  case: ((p =P q)) => [Heq | Hdistinct].
  - rewrite Heq cat_law in eqy'.
    have habs: y == e.
      by rewrite eqy' inverse_left.
    move/FreeGroup_norm_unique in habs.
    rewrite freely_reduced_correct in fry.
    rewrite -fry FreeGroup_norm_e in habs.
    move: (N0 y yinU) => habs'; rewrite -fry in habs'.
    contradiction.

  - rewrite /Order.lt /= /CmpOrder.cmp_lt /CmpOrder.transform  /=.
    set t := FreeGroup_norm (x @ y).
    have eqw'invq: w' = inv (q :> FreeGroup Sigma).
      rewrite eqy in eqy'.
      move/eqP in eqy'; rewrite eqseq_cat //= in eqy'.
      by move/andP: eqy' => [_ /eqP G].

    have dect: t = a ++ inv (q :> FreeGroup Sigma).
      rewrite eqw'invq freely_reduced_correct in frxy.
      rewrite frxy.
      apply: (FreeGroup_norm_unique).
      by rewrite eqx {2}eqy /p -associativity [inv (lKprefix x y :> FreeGroup Sigma) @ (lKprefix x y ++ w')]associativity inverse_right neutral_left eqw'invq.
    rewrite freely_reduced_correct in frx.

    have ->: FreeGroup_norm (inv z @ inv y) = inv (p ++ c :> FreeGroup Sigma).
      rewrite eqv Hempty cats0 freely_reduced_correct in fryz.
      rewrite fryz -FreeGroup_norm_inv.
      apply: FreeGroup_norm_unique.
      rewrite {1}eqy' /inv/= inv_word_law /= inv_word_cat /= inv_word_involutive /=.
      by rewrite eqz /= inv_word_law /= -associativity [( _ @ ((q :> FreeGroup Sigma) @ _))]associativity inverse_right neutral_left {1}/p.
    rewrite freely_reduced_correct in frz.
    rewrite FreeGroup_norm_inv -frz eqz.

    (* *)
    have eqsz_inv: size p = size (inv (q:> FreeGroup Sigma)).
      by rewrite size_inv -eqsz.
    have leqsz_inv: (size (inv (q:> FreeGroup Sigma)) <= size a)%N.
      by rewrite -eqsz_inv.
    have leqsz_invinv: (size (inv (p:>FreeGroup Sigma)) <= size (inv c))%N.
      by rewrite !size_inv eqsz.
    have leqsz_invq: (size (inv (q:> FreeGroup Sigma)) <= size (inv c))%N.
      by rewrite !size_inv.
    have eqsz_inv': size (inv (p: FreeGroup Sigma)) = size (inv (q :> FreeGroup Sigma)).
      by rewrite !size_inv eqsz.
    have leqszp_inv: (size (inv (p:> FreeGroup Sigma)) <= size a)%N.
      by rewrite size_inv.
    have eqszp: size p = size (inv (p :> FreeGroup Sigma)).
      by symmetry; apply: size_inv.
    move: (@CmpOrder.half_oversized _ a p (inv (q:>FreeGroup Sigma)) leqszprefa leqsz_inv eqsz_inv) => eq_firsthalfx.
    move: (@CmpOrder.half_oversized _ (inv c) (inv (p: FreeGroup Sigma)) (inv (q :> FreeGroup Sigma)) leqsz_invinv leqsz_invq eqsz_inv') => eq_firsthalfz.
    move: (@CmpOrder.half_oversized _ a p (inv (p:>FreeGroup Sigma)) leqszprefa leqszp_inv eqszp) => eq_firsthalfpx.
    rewrite -frx eqx dect.

    have rsize: forall n, (n - (n - 1) %/ 2 >= (n + 1) %/ 2)%N.
      by lia.

    have divn_leq_succ: forall n, (n <= ((n + 1)%/2)*2)%N.
      by lia.

    have pnotnil: p != [::].
      apply/negP => /eqP habs.
      rewrite habs /= in eqsz; symmetry in eqsz; move/size0nil in eqsz.
      by rewrite eqsz habs in Hdistinct.
    have qnotnil: q != [::].
      apply/negP => /eqP habs.
      rewrite habs /= in eqsz; move/size0nil in eqsz.
      by rewrite eqsz habs in Hdistinct.

    rewrite !inv_cat.
    rewrite Hempty cats0 in eqv.

    case: (boolP (p < q :> seqlexi _)%O) => [Ht | Hf].
    - right; left; apply/orP; right; apply/andP; split; rewrite /CmpOrder.sz /= -inv_cat.
      + have -> : FreeGroup_norm (inv (lKprefix y z ++ c :> FreeGroup Sigma) @ inv y) = inv (v ++ c :> FreeGroup Sigma).
          rewrite freely_reduced_correct in fryz; rewrite fryz -FreeGroup_norm_inv.
          apply: FreeGroup_norm_unique; rewrite -inverse_law.
          have ->: y @ (lKprefix y z ++ c) == v++c.
            rewrite {1}eqy.
            by rewrite associativity -[(p ++ w' :> FreeGroup Sigma) @ lKprefix y z]associativity eqw'invq inverse_right neutral_right eqv.
          by done.
        rewrite eqz in frz.
        by rewrite FreeGroup_norm_inv !size_inv -frz !size_cat; apply/eqP; rewrite eqv eqsz.
      rewrite !inv_cat.

      rewrite lt_sizelexiE; apply/orP; right; apply/andP; split; first by done.
      set c' := CmpOrder.half (inv c ++ inv (p:>FreeGroup Sigma)).
      set p' := inv (CmpOrder.upperhalf (inv c ++ inv (p:>FreeGroup Sigma)):>FreeGroup Sigma).
      set q' := inv (CmpOrder.upperhalf (inv c ++ inv (lKprefix y z:> FreeGroup Sigma)):>FreeGroup Sigma).

      set t1 := (take (size (inv c ++ inv (p:>FreeGroup Sigma)) - (size (inv c ++ inv (p:>FreeGroup Sigma)) - 1) %/ 2) (inv (inv c ++ inv (p:>FreeGroup Sigma) :> FreeGroup Sigma))).
      set t2 := (take (size (inv c ++ inv (q:>FreeGroup Sigma)) - (size (inv c ++ inv (q:>FreeGroup Sigma)) - 1) %/ 2) (inv (inv c ++ inv (q:>FreeGroup Sigma) :> FreeGroup Sigma))).

      have eqt1p': t1 = p'.
        by rewrite /t1 /p' /CmpOrder.upperhalf inv_drop.
      have eqt2q': t2 = q'.
        by rewrite /t2 /q' /CmpOrder.upperhalf inv_drop.

      have sz_simpl : forall k, (k = size q) -> (k <= (size c + size q - ((size c + size q) - 1)%/2))%N.
        move => k eqk.
        apply: leq_trans; last first.
        + apply: rsize.
        + have csz: size z = size c + size p.
            by rewrite eqz size_cat -eqsz addnC.
          rewrite -(@leq_pmul2l 2) //.
          rewrite mul2n mul2n.
          apply: (@leq_trans (size z)); first by rewrite eqk -muln2.
          by rewrite eqz !size_cat addnC -muln2 divn_leq_succ.

      have prefpt1: prefix p t1.
        rewrite prefixE take_takel.
        rewrite inv_cat !inv_eq_invol take_cat.
        rewrite ifF; last by apply: ltnn.
        by rewrite subnn take0 cats0.
        rewrite !size_cat !size_inv !eqsz.
        by apply: sz_simpl.

      have prefqt2: prefix q t2.
        rewrite prefixE take_takel.
        rewrite inv_cat !inv_eq_invol take_cat.
        rewrite ifF; last by apply: ltnn.
        by rewrite subnn take0 cats0.
        rewrite !size_cat !size_inv.
        by apply: sz_simpl.

      have lt_t1_t2: (t1 < t2 :> seqlexi _)%O.
        apply: (prefix_lt_lexi p t1 q t2 pnotnil eqsz prefpt1 prefqt2 Ht).
      have slt_t1_t2: (t1 < t2)%O.
        rewrite lt_sizelexiE; apply/orP; right; apply/andP; split.
        + apply/eqP; rewrite /t1 /t2 !size_cat !size_inv !eqsz; apply: size_take_simpl.
          by rewrite !inv_cat !inv_eq_invol !size_cat eqsz.
        + by apply: lt_t1_t2.

      case: (boolP (p' <= c')%O) => [leqp'c' | geqp'c'].
      - rewrite CmpOrder.min_wordC CmpOrder.min_word_correct; last rewrite /Order.le /=.
        rewrite CmpOrder.max_wordC CmpOrder.max_word_correct; last by assumption.
        case: (boolP (q' <= c')%O) => [leqq'c' | geqq'c'].
        - rewrite CmpOrder.min_wordC CmpOrder.min_word_correct -eq_firsthalfz; last by assumption.
          rewrite CmpOrder.max_wordC CmpOrder.max_word_correct; last by assumption.
          rewrite /p' /q' /CmpOrder.upperhalf !inv_drop.
          rewrite /Order.lt /=.

          apply/andP; split.
          + rewrite le_sizelexiE; apply/orP; right; apply/andP; split.
            + by rewrite !inv_cat !inv_eq_invol !size_cat !size_inv eqsz; apply/eqP; apply: size_take_simpl; rewrite !size_cat eqsz.
            + by apply: Order.PreorderTheory.ltW.
          + apply/implyP.
            move => habs; exfalso.
            
            have habs': (t2 < t2)%O.
              apply: Order.PreorderTheory.le_lt_trans.
              rewrite /Order.le /= in habs.
              + by apply: habs.
              + by apply: slt_t1_t2.
            by rewrite Order.PreorderTheory.ltxx in habs'.
        - move: (@sizelexi_total _ _ q' c') => Htotal; move/negPf in geqq'c'; rewrite /Order.le /= in geqq'c'; rewrite geqq'c' /= in Htotal.

          rewrite CmpOrder.min_word_correct -eq_firsthalfz; last by assumption.
          rewrite CmpOrder.max_word_correct; last by assumption.
          rewrite /Order.lt /=.

          apply/andP; split; first by assumption.
          apply/implyP => _; apply/andP; split; first by assumption.
          apply/implyP => habs.
          by rewrite /Order.le /= geqq'c' in habs.
          by assumption.
      - move: (@sizelexi_total _ _ p' c') => Htotal; move/negPf in geqp'c'; rewrite /Order.le /= in geqp'c'; rewrite geqp'c' /= in Htotal.
        rewrite CmpOrder.min_word_correct; last by assumption.
        rewrite CmpOrder.max_word_correct; last by assumption.
        case: (boolP (q' <= c')%O) => [leqq'c' | geqq'c'].
        + have leq'p': (q' <= p')%O.
            apply: Order.PreorderTheory.le_trans.
            + by apply: leqq'c'.
            + by apply: Htotal.
          rewrite -eqt1p' -eqt2q' in leq'p'.
          have habs': (t2 < t2)%O.
            apply: Order.PreorderTheory.le_lt_trans.
            + by apply: leq'p'.
            + by apply: slt_t1_t2.
          by rewrite Order.PreorderTheory.ltxx in habs'.
        + move: (@sizelexi_total _ _ q' c') => Hqtotal; move/negPf in geqq'c'; rewrite /Order.le /= in geqq'c'; rewrite geqq'c' /= in Hqtotal.
          rewrite -!eq_firsthalfz.
          rewrite CmpOrder.min_word_correct; last by assumption.
          rewrite CmpOrder.max_word_correct; last by assumption.

          rewrite /Order.lt /=; apply/andP; split; first by done.
          apply/implyP => _; apply/andP; split; first by rewrite -eqt1p' -eqt2q'; apply: Order.PreorderTheory.ltW.
          apply/implyP => habs; rewrite -eqt1p' -eqt2q' in habs.
          have habs': (t2 < t2)%O.
            apply: Order.PreorderTheory.le_lt_trans.
            + by apply: habs.
            + by apply: slt_t1_t2.
          by rewrite Order.PreorderTheory.ltxx in habs'.



    - rewrite -Order.TotalTheory.leNgt in Hf.
      have Ht: (q < p :> seqlexi _)%O.
        by move/eqP in Hdistinct; rewrite Order.POrderTheory.lt_def; apply/andP; split.

      left; apply/orP; right; apply/andP; split; first rewrite /CmpOrder.sz /=.
      + have -> : FreeGroup_norm ((a ++ inv (lKprefix x y :> FreeGroup Sigma):>FreeGroup Sigma) @ y) =
                    (a ++ (inv (q:>FreeGroup Sigma) :> FreeGroup Sigma) :> FreeGroup Sigma).
        by rewrite -dect /t {2}eqx.
      rewrite eqx in frx.
      by rewrite -frx !size_cat; apply/eqP; rewrite !size_inv eqsz.

      rewrite lt_sizelexiE; apply/orP; right; apply/andP; split; first by done.
      set c' := CmpOrder.half (a ++ p).
      set p' := inv (CmpOrder.upperhalf (a ++ inv (lKprefix x y:>FreeGroup Sigma)):>FreeGroup Sigma).
      set q' := inv (CmpOrder.upperhalf (a ++ inv (q:> FreeGroup Sigma)):>FreeGroup Sigma).

      set t1 := (take (size (a ++ inv (p:>FreeGroup Sigma)) - (size (a ++ inv (p:>FreeGroup Sigma)) - 1) %/ 2) (inv (a ++ inv (p:>FreeGroup Sigma) :> FreeGroup Sigma))).
      set t2 := (take (size (a ++ inv (q:>FreeGroup Sigma)) - (size (a ++ inv (q:>FreeGroup Sigma)) - 1) %/ 2) (inv (a ++ inv (q:>FreeGroup Sigma) :> FreeGroup Sigma))).

      have eqt1p': t1 = p'.
        by rewrite /t1 /p' /CmpOrder.upperhalf inv_drop.
      have eqt2q': t2 = q'.
        by rewrite /t2 /q' /CmpOrder.upperhalf inv_drop.

      have sz_simpl : forall k, (k = size q) -> (k <= (size a + size q - ((size a + size q) - 1)%/2))%N.
        move => k eqk.
        apply: leq_trans; last first.
        + apply: rsize.
        + have csz: size x = size a + size p.
            by rewrite eqx size_cat size_inv.
          rewrite -(@leq_pmul2l 2) //.
          rewrite mul2n mul2n.
          apply: (@leq_trans (size x)); first by rewrite eqk -eqsz -muln2.
          by rewrite eqx -eqsz !size_cat size_inv addnC -muln2  divn_leq_succ.

      have prefpt1: prefix p t1.
        rewrite prefixE take_takel.
        rewrite inv_cat !inv_eq_invol take_cat.
        rewrite ifF; last by apply: ltnn.
        by rewrite subnn take0 cats0.
        rewrite !size_cat !size_inv !eqsz.
        by apply: sz_simpl.

      have prefqt2: prefix q t2.
        rewrite prefixE take_takel.
        rewrite inv_cat !inv_eq_invol take_cat.
        rewrite ifF; last by apply: ltnn.
        by rewrite subnn take0 cats0.
        rewrite !size_cat !size_inv.
        by apply: sz_simpl.

      have lt_t1_t2: (t2 < t1 :> seqlexi _)%O.
        apply: (prefix_lt_lexi q t2 p t1 qnotnil (symmetry eqsz) prefqt2 prefpt1 Ht).
      have slt_t1_t2: (t2 < t1)%O.
        rewrite lt_sizelexiE; apply/orP; right; apply/andP; split.
        + apply/eqP; rewrite /t1 /t2 !size_cat !size_inv !eqsz; apply: size_take_simpl.
          by rewrite !inv_cat !inv_eq_invol !size_cat eqsz.
        + by apply: lt_t1_t2.

      case: (boolP (q' <= c')%O) => [leqq'c' | geqq'c'].
      - rewrite -eq_firsthalfx -eq_firsthalfpx.
        rewrite CmpOrder.min_wordC CmpOrder.min_word_correct; last by assumption.
        rewrite CmpOrder.max_wordC CmpOrder.max_word_correct; last by assumption.
        case: (boolP (p' <= c')%O) => [leqp'c' | geqp'c'].
        - rewrite CmpOrder.min_wordC CmpOrder.min_word_correct; last by assumption.
          rewrite CmpOrder.max_wordC CmpOrder.max_word_correct; last by assumption.
          rewrite /p' /q' /CmpOrder.upperhalf !inv_drop.
          rewrite /Order.lt /=.

          apply/andP; split.
          + rewrite le_sizelexiE; apply/orP; right; apply/andP; split.
            + by rewrite !inv_cat !inv_eq_invol !size_cat !size_inv eqsz; apply/eqP; apply: size_take_simpl; rewrite !size_cat eqsz.
            + by apply: Order.PreorderTheory.ltW.
          + apply/implyP.
            move => habs; exfalso.
            
            have habs': (t2 < t2)%O.
              apply: Order.PreorderTheory.lt_le_trans.
              rewrite /Order.le /= in habs.
              + by apply: slt_t1_t2.
              + by apply: habs.
            by rewrite Order.PreorderTheory.ltxx in habs'.
        - move: (@sizelexi_total _ _ p' c') => Htotal; move/negPf in geqp'c'; rewrite /Order.le /= in geqp'c'; rewrite geqp'c' /= in Htotal.

          rewrite CmpOrder.min_word_correct; last by assumption.
          rewrite CmpOrder.max_word_correct; last by assumption.
          rewrite /Order.lt /=.

          apply/andP; split; first by assumption.
          apply/implyP => _; apply/andP; split; first by assumption.
          apply/implyP => habs.
          by rewrite /Order.le /= geqp'c' in habs.
      - rewrite -eq_firsthalfx -eq_firsthalfpx.
        move: (@sizelexi_total _ _ q' c') => Htotal; move/negPf in geqq'c'; rewrite /Order.le /= in geqq'c'; rewrite geqq'c' /= in Htotal.
        rewrite CmpOrder.min_word_correct; last by assumption.
        rewrite CmpOrder.max_word_correct; last by assumption.
        case: (boolP (p' <= c')%O) => [leqp'c' | geqp'c'].
        + have leq'p': (p' <= q')%O.
            apply: Order.PreorderTheory.le_trans.
            + by apply: leqp'c'.
            + by apply: Htotal.
          rewrite -eqt1p' -eqt2q' in leq'p'.
          have habs': (t2 < t2)%O.
            apply: Order.PreorderTheory.lt_le_trans.
            + by apply: slt_t1_t2.
            + by apply: leq'p'.
          by rewrite Order.PreorderTheory.ltxx in habs'.
        + move: (@sizelexi_total _ _ p' c') => Hqtotal; move/negPf in geqp'c'; rewrite /Order.le /= in geqp'c'; rewrite geqp'c' /= in Hqtotal.
          rewrite CmpOrder.min_word_correct; last by assumption.
          rewrite CmpOrder.max_word_correct; last by assumption.

          rewrite /Order.lt /=; apply/andP; split; first by done.
          apply/implyP => _; apply/andP; split; first by rewrite -eqt1p' -eqt2q'; apply: Order.PreorderTheory.ltW.
          apply/implyP => habs; rewrite -eqt1p' -eqt2q' in habs.
          have habs': (t2 < t2)%O.
            apply: Order.PreorderTheory.lt_le_trans.
            + by apply: slt_t1_t2.
            + by apply: habs.
          by rewrite Order.PreorderTheory.ltxx in habs'.
Qed.

Hypothesis frU: forall x, x \in U -> freely_reduced x.
Hypothesis minU: forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) -> ~ ((x @ y) < x :> word)%O.

Lemma inv_inU (x: FreeGroup Sigma):
  (x \in U) -> (inv x \in U).
Proof.
  move => xinU.
  rewrite /U.
  case: (boolP (x \in gens)) => [Ht | /negP Hf].
  + by rewrite mem_cat; apply/orP; right; apply/mapP; exists x.
  + rewrite /U in xinU.
    have xino: x \in [seq inv w | w <- gens].
      rewrite mem_cat in xinU; case/orP: xinU.
      + by move => habs.
      + by done.
    move/mapP: xino => [y yingens eqxinvy].
    by rewrite eqxinvy inv_eq_invol mem_cat yingens /=.
Qed.
    
Lemma prod_leq_size (l: seq (FreeGroup Sigma)) (inU: forall i, (i < size l)%N -> (nth e l i) \in U)
  (non_trvl: forall i, (i < size l - 1)%N -> non_trivial (nth e l i) (nth e l (i.+1))):
  (sz(prod l) >= length l)%N.
Proof.
  case: l inU non_trvl => [//| a l inU non_trvl].
  have ainU: a \in U.
    move: (@inU 0) => finU.
    rewrite /= in finU; apply: finU.
    by apply: ltn0Sn.
  move: (@lKprefix_all_split a ainU (N0 a ainU)) => [w [win [hdistinct Pw]]].
  move: (@lKprefix_allW a w win) => /mapP [x xinU prefx].
  move: (@lKprefix_split x a (frU x xinU) (frU a ainU)) => [u [v]] [eqx [eqa frxa]].

  have ntrvxa: non_trivial x a.
    rewrite /non_trivial => habs.
    move/(lKprefix_contra x a (frU x xinU) (frU a ainU)) in habs; rewrite -prefx in habs.
    by rewrite habs in hdistinct; move/eqP in hdistinct.

  move: (@triplet_lt x a x (frU x xinU) (frU a ainU) (frU x xinU) xinU ainU xinU ntrvxa ((non_trivialC x a ntrvxa))) => Q.
  case: Q => [Ha | [Hb | [q [qnempty eqaq]]]].
  + exfalso.
    by apply: (minU x a xinU ainU ntrvxa).
  + exfalso.
    by apply: (minU (inv x) (inv a) (inv_inU x xinU) (inv_inU a ainU) (non_trivial_inv x a ntrvxa)).
  move: eqaq.
  set t := lKprefix a x.
  move => eqaq.

  have: exists l' q, FreeGroup_norm (prod (a :: l)) = w ++ q ++ l' /\ q <> [::] /\ prefix (w++q) a /\ (size l' >= size l)%N.
    move: a w x u v q t inU xinU non_trvl ainU win prefx eqx eqa ntrvxa eqaq hdistinct Pw frxa qnempty; elim: l => [// | b l IH] a w x u v q t inU xinU non_trvl ainU win prefx eqx eqa ntrvxa eqaq hdistinct Pw frxa qnempty.
    + have ->: FreeGroup_norm (a @ e) = a.
        move: (frU a ainU) => H.
        rewrite freely_reduced_correct in H; rewrite {2}H.
        by apply /FreeGroup_norm_unique /neutral_right.
      
      exists (inv (t:>FreeGroup Sigma));
      exists (q); split; first by rewrite prefx.
      split; first by apply: qnempty.
      split; first by rewrite prefx; apply/prefixP; exists (inv (t:>FreeGroup Sigma)); rewrite -catA. 
      by rewrite /=.
    + have ibound': forall (i: nat) a l, (i < size l)%N -> (((i.+1) < size (a::l))%N).
        move => i ibound.
        rewrite /=.
        by lia.
    
      have inUW: (forall i : nat, (i < size (b :: l))%N -> nth e (b :: l) i  \in U).
        move => i ibound.
        move: (inU (i.+1) (ibound' _ i a (b::l) ibound)) => nthinU.
        by rewrite -nth_behead /= in nthinU.

      have non_trvlW: (forall i : nat, (i < size (b :: l) - 1)%N -> non_trivial (nth e (b :: l) i) (nth e (b :: l) i.+1)).
        move => i ibound.
        rewrite ltn_subRL in ibound.
        move: (ibound' _ (1+i)%N a (b::l) ibound) => i'bound.
        rewrite -addnS -ltn_subRL in i'bound.
        move: (non_trvl (i.+1) i'bound) => ntrvnth.
        by rewrite -nth_behead /= in ntrvnth.

      have binU: b \in U.
        have bnd: (1 < size [:: a,  b  & l])%N.
          by rewrite /=; lia.
        move: (inU (0.+1) bnd) => L.
        by rewrite -nth_behead /= in L.
      move: (@lKprefix_all_split b binU (N0 b binU)) => [wb [wbin [wbdistinct Pwb]]].
      move: (@lKprefix_allW b wb wbin) => /mapP [z zinU prefz].
      move: (lKprefix_split z b(frU z zinU) (frU b binU)) => [f' [g']] [eqz [eqb' frzb]].

      have ntrvzb: non_trivial z b.
        rewrite /non_trivial => habs.
        move/(lKprefix_contra z b (frU z zinU) (frU b binU)) in habs; rewrite -prefz in habs.
        by rewrite habs in wbdistinct; move/eqP in wbdistinct.

      have ntrvab: non_trivial a b.
        have bnd: (0 < size [:: a,  b  & l] - 1)%N.
          by rewrite /= -addn2 -addnBA //= addnS ltn0Sn.
        by move: (non_trvl 0 bnd) => L; rewrite -nth_behead /= in L.

      move: (@triplet_lt x a b (frU x xinU) (frU a ainU) (frU b binU) xinU ainU binU ntrvxa ntrvab) => Q.
      move: q eqaq qnempty => _ _ _.
      case: Q => [Ha | [Hb | [q [qnempty eqaq]]]].
      + exfalso.
        by apply: (minU x a xinU ainU ntrvxa).
      + exfalso.
        by apply (minU (inv b) (inv a) (inv_inU b binU) (inv_inU a ainU) (non_trivialC (inv a) (inv b) (non_trivial_inv a b ntrvab))).
      move: (lKprefix_split a b (frU a ainU) (frU b binU)) => [f [g]] [eqa' [eqb frab]].


      move: (@triplet_lt z b z (frU z zinU) (frU b binU) (frU z zinU) zinU binU zinU ntrvzb (non_trivialC z b ntrvzb)) => Q.
      case: Q => [Ha | [Hb | [m [mnempty eqbm]]]].
      + exfalso.
        by apply: (minU z b zinU binU ntrvzb).
      + exfalso.
        by apply (minU (inv z) (inv b) (inv_inU z zinU) (inv_inU b binU) (non_trivial_inv z b ntrvzb)).

      move: (IH b wb z f' g' m (lKprefix b z) inUW zinU non_trvlW binU wbin prefz eqz eqb' ntrvzb eqbm wbdistinct Pwb frzb mnempty) => [l' [p' [eql' [p'nempty [p'infix leszl']]]]].

      move: (@triplet_lt a b z (frU a ainU) (frU b binU) (frU z zinU) ainU binU zinU ntrvab (non_trivialC z b ntrvzb)) => Q'.
      case: Q' => [Ha | [Hb | [p [pnempty eqbp]]]].
      + exfalso.
        by apply: (minU a b ainU binU ntrvab).
      + exfalso.
        by apply (minU (inv z) (inv b) (inv_inU z zinU) (inv_inU b binU) (non_trivial_inv z b ntrvzb)).


      have prefabwb: prefix (lKprefix a b) wb.
        apply: Pwb.
        + apply/eqP; move => habs.
          rewrite habs in eqbp.
          move/(f_equal size) in eqbp; rewrite !size_cat -{1}[size b]addn0 in eqbp; move/eqP in eqbp.
          by rewrite eqn_add2l eq_sym addn_eq0 in eqbp; move/andP: eqbp => [/eqP /size0nil szp0 _].
        + by apply: ainU.
      move/prefixP: prefabwb => [r eqwb].
      rewrite -prefz eqwb in eqb'.

      exists (r ++ p' ++ l');
      exists (q); split.
      + rewrite /prod /= FreeGroup_norm_law.
        rewrite /prod /= in eql'.
        rewrite eql'.
        move: (frU a ainU) => /freely_reduced_correct fra.
        rewrite -fra eqaq.

        rewrite eqwb -!cat_law !catA -[(((lKprefix x a ++ q) ++ inv (lKprefix a b :> FreeGroup Sigma)) ++ lKprefix a b)]catA.
        rewrite !cat_law FreeGroup_norm_law [FreeGroup_norm (((((lKprefix x a :> FreeGroup Sigma) @ q) @ (inv (lKprefix a b :> FreeGroup Sigma) @ lKprefix a b)) @ r) @ p')]FreeGroup_norm_law.
        rewrite [FreeGroup_norm ((((lKprefix x a :> FreeGroup Sigma) @ q) @ (inv (lKprefix a b :> FreeGroup Sigma) @ lKprefix a b)) @ r)]FreeGroup_norm_law.
        rewrite [FreeGroup_norm (((lKprefix x a :> FreeGroup Sigma) @ q) @ (inv (lKprefix a b :> FreeGroup Sigma) @ lKprefix a b))]FreeGroup_norm_law.
        have ->: FreeGroup_norm (inv (lKprefix a b :> FreeGroup Sigma) @ lKprefix a b) = e.
          rewrite -FreeGroup_norm_e; apply: FreeGroup_norm_unique.
          by apply: inverse_right.
        rewrite -FreeGroup_norm_e.
        have ->: FreeGroup_norm (FreeGroup_norm ((lKprefix x a :> FreeGroup Sigma) @ q) @ FreeGroup_norm e) = FreeGroup_norm ((lKprefix x a :> FreeGroup Sigma) @ q).
          by rewrite -FreeGroup_norm_law; apply: FreeGroup_norm_unique; apply: neutral_right.
        rewrite -[FreeGroup_norm (FreeGroup_norm ((lKprefix x a:>FreeGroup Sigma) @ q) @ FreeGroup_norm r)]FreeGroup_norm_law.
        rewrite -[FreeGroup_norm (FreeGroup_norm (((lKprefix x a :> FreeGroup Sigma) @ q) @ r) @ FreeGroup_norm p')]FreeGroup_norm_law.
        rewrite -!FreeGroup_norm_law.
        symmetry.
        rewrite -!cat_law prefx -freely_reduced_correct.

        have frxq: freely_reduced (lKprefix x a ++ q).
          apply: freely_reducedW; rewrite -freely_reduced_correct in fra.
          by apply: fra.
          by rewrite {2}eqaq catA prefix_infix.
        
        have frqr: freely_reduced (q ++ (r ++ p')).
          have eqg: g = r ++ g'.
            rewrite {1}eqb -catA in eqb'; move/eqP in eqb'.

            rewrite (@eqseq_cat _ (lKprefix a b) (lKprefix a b) g (r ++ g') (erefl)) in eqb'.
            by move/andP: eqb' => [_ /eqP R].
          have eqf: f = lKprefix x a ++ q.
            rewrite {1}eqaq catA in eqa'.
            have eqszf: size (lKprefix x a ++ q) = size f.
              move/(f_equal size) in eqa'; rewrite !size_cat in eqa'; move/eqP in eqa'.
              rewrite eqn_add2r in eqa'; move/eqP in eqa'.
              by rewrite !size_cat.
            move/eqP in eqa'; rewrite (@eqseq_cat _ (lKprefix x a ++ q) f (inv (lKprefix a b :> FreeGroup Sigma)) (inv (lKprefix a b :> FreeGroup Sigma)) eqszf) in eqa';
            move/andP: eqa' => [/eqP R _].
            by symmetry.
          
          move/prefixP: p'infix => [s  eqg']. 
          rewrite eqb' in eqg'.
          rewrite -eqwb -catA in eqg'; move/eqP in eqg'.
          rewrite (@eqseq_cat _ (wb) (wb) (g') (p' ++ s) (erefl)) in eqg';
          move/andP: eqg' => [_ /eqP R].
          rewrite R in eqg.

          rewrite eqf eqg in frab.
          apply: freely_reducedW.
          by apply: frab.
          rewrite !catA -[((lKprefix x a ++ q) ++ r)]catA -[((lKprefix x a ++ q ++ r) ++ p')]catA.
          apply/infixP.
          exists (lKprefix x a).
          exists (s).
          by rewrite !catA.
      
        have frrl: freely_reduced (r ++ p' ++ l').
          rewrite eqwb in eql'.
          have fr: (lKprefix a b ++ r) ++ p' ++ l' = FreeGroup_norm ((lKprefix a b ++ r) ++ p' ++ l').
            by rewrite -!eql' FreeGroup_norm_involutive.
          
          rewrite -freely_reduced_correct in fr.
          apply: freely_reducedW.
          by apply: fr.
          by rewrite -catA; apply: suffix_infix.
          
        have frxr: freely_reduced ((lKprefix x a ++ q) ++ (r ++ p')).
          have leszq: (size q >= 1)%N.
            rewrite ltnNge; apply/negP => habs.
            by rewrite leqn0 in habs; move/eqP: habs => /size0nil habs; rewrite habs in qnempty.
          rewrite -catA.
          by apply: freely_reduced_cat_overlap.

        rewrite -[(((lKprefix x a ++ q) ++ r) ++ p')]catA.
        have leszrp': (size (r ++ p') >= 1)%N.
          rewrite ltnNge; apply/negP => habs.
          rewrite size_cat in habs.
          by rewrite leqn0 addn_eq0 in habs; move/andP: habs => [_ /eqP /size0nil habs]; rewrite habs in p'nempty.
        rewrite -[((lKprefix x a ++ q) ++ r ++ p') ++ l']catA.
        rewrite catA in frrl.
        by apply: freely_reduced_cat_overlap.
      split; first by apply: qnempty.
      split; first by rewrite prefx; apply/prefixP; exists (inv (lKprefix a b:>FreeGroup Sigma)); rewrite -catA {1}eqaq.
      rewrite !size_cat /= ltn_addl //.
      have leszrp': (size p' >= 1)%N.
        rewrite ltnNge; apply/negP => habs.
        by rewrite leqn0 in habs; move/eqP: habs => /size0nil habs; rewrite habs in p'nempty.
      apply: (leq_ltn_trans leszl').
      by rewrite addnC -{1}[size l']addn0 ltn_add2l.

  move => [l' [q' [eql' [q'nempty [_ lesz]]]]].
  have leszq': (size q' >= 1)%N.
    rewrite ltnNge; apply/negP => habs.
    by rewrite leqn0 in habs; move/eqP: habs => /size0nil habs; rewrite habs in q'nempty.
  rewrite /sz eql' !size_cat /= ltn_addl //.
  apply: (leq_ltn_trans lesz).
  by rewrite addnC -{1}[size l']addn0 ltn_add2l.
Qed.
    
End WordSplitting.



Section NielsenConstructionCorrection.

Context {Sigma: finType}.

Notation word := (FreeGroup Sigma).

Notation vec := (seq word).

(* Note(mathis): the normalisation function is already defined in F2.v. Same for the inv function and prod. *)

(* Note(mathis): I did implement t1 since I need it in the proof of t2, not for the algorithm *)

Lemma H_all (gens: vec) (i j : nat) (h: i <> j) (g : 'I_(size gens) -> FreeGroup Sigma) (H_subgroup_f'n : forall n : 'I_(size gens),
in_generated_subgroup (t2 gens i j h) (g n)) wx :
  forall y, (y \in [seq FreeGroup_alphabet_extension g t | t <- wx] ->
  in_generated_subgroup (t2 gens i j h) y).
Proof.
  move => y.
  move/mapP => [n _ ->].
  rewrite /FreeGroup_alphabet_extension.
  case: n.
  move => s.
  apply: H_subgroup_f'n.
  move => s; apply: igs_inv; apply: H_subgroup_f'n.
Qed.

(* Note(mathis): I need to explicitly say FreeGroup Sigma instead of F for unification with the canonical structure *)
Lemma igs_foldr_stable (v: vec) (L : seq (FreeGroup Sigma)) : 
  (forall x, x \in L -> in_generated_subgroup v x) -> 
  forall K, subseq K L -> in_generated_subgroup v (foldr (fun y => [eta law y]) e K).
Proof.
  move => H K.
  elim: K => [| a t].
    - move => H_empty; rewrite /=; by apply: igs_e.
    - move => Ht H_sub.
      rewrite /=; apply: igs_law.
      have Ha : a \in L := mem_subseq H_sub (mem_head a t).
      move: (H a) => Ha_sg; by apply: Ha_sg.
      have: subseq t L.
        apply: cons_subseq H_sub.
      move => H_subt.
      by apply Ht.
Qed.


(* this Lemma already exists inside EquivalenceAlgebra.v *)
Lemma igs_proper (v: vec) (x y : (FreeGroup Sigma)) :
  x == y -> in_generated_subgroup v x -> in_generated_subgroup v y.
Proof.
  move => Hxy [w Hw].
  exists w.
  by rewrite Hw Hxy.
Qed.

Lemma prod_congr (u v : vec) (eqsz: size u = size v) (Happrox: forall i, (i < size u)%N -> (nth e u i == nth e v i)):
  prod u == prod v.
Proof.
  elim: u v eqsz Happrox => [| w].
  + rewrite /=; move => v eqsz0 Happrox.
    have eqv: v = [::].
      by apply size0nil.
    by rewrite eqv /=.
  + move => l IH v eqsz Happrox.
    rewrite /= in eqsz.
    have eqv: v = (nth e v 0) :: (drop 1 v).
      rewrite -(@drop_nth _ e _ _); first by rewrite drop0.
      + by rewrite -eqsz.
    rewrite eqv /prod /=.
    have eqszt: size l = size (drop 1 v).
      by rewrite size_drop; lia.
    apply /trans.
    + apply /congruent_left /IH; first by apply eqszt.
      move => i ibound.
      rewrite nth_drop.
      have eqi: (1+i < size (w::l))%N.
        by rewrite /=; lia.
      move: (Happrox (1+i) (eqi)) => Hinst.
      by rewrite -nth_behead /= in Hinst.
    + apply /congruent_right.
      by apply: (Happrox 0).
Qed.

Lemma igs_set_nth (v: vec) (i: nat) (ibound: (i < size v)%N) (x: FreeGroup Sigma):
  (x == nth e v i) -> forall y, in_generated_subgroup (set_nth e v i x) y <-> in_generated_subgroup v y.
Proof.
  move => approxxnth y.
  have eqsz: size (set_nth e v i x) = size v.
    by rewrite size_set_nth; apply/maxn_idPr.
  split.
  - move => Hin; rewrite /in_generated_subgroup in Hin; move: Hin => [w approxw].
    rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /nth_gen in approxw.
    rewrite eqsz in w approxw.
    exists(w).
    + rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /nth_gen.
      apply /trans.
      apply /prod_congr.
      have eqsz_seq: size (map (fun c : InverseAlphabet 'I_(size v) =>
                      match c with
                      | Base a => nth e v a
                      | Inverse a => inv (nth e v a)
                      end) w) = size (map (fun c : InverseAlphabet 'I_(size v) =>
                      match c with
                      | Base a => nth e (set_nth e v i x) a
                      | Inverse a => inv (nth e (set_nth e v i x) a)
                      end) w).
        by rewrite !size_map.
      + by rewrite eqsz_seq.
      + move => k kbound.
        have hbound : (0 < size v)%N.
          by apply: (leq_ltn_trans (leq0n i) ibound).
        rewrite !(@nth_map _ (Base (Ordinal (hbound)))).
        case: (nth (Base (Ordinal (n:=size v) (m:=0) hbound)) w k).
        + move => s.
          pose s':= nat_of_ord s.
          case: (s' =P i) => [Ht | Hf].
          - rewrite /s' in Ht; rewrite Ht  nth_set_nth /=.
            rewrite ifT //=.
            by apply symm.
          - rewrite /s' in Hf; rewrite nth_set_nth /=.
            rewrite ifF; last by apply/eqP.
            by apply refl.
        + move => s.
          pose s':= nat_of_ord s.
          case: (s' =P i) => [Ht | Hf].
          - rewrite /s' in Ht; rewrite Ht  nth_set_nth /=.
            rewrite ifT //=.
            by apply /symm; rewrite approxxnth.
          - rewrite /s' in Hf; rewrite nth_set_nth /=.
            rewrite ifF; last by apply/eqP.
            by apply refl.
        1-2: by rewrite size_map in kbound.
      + by  assumption.
  - move => Hin; rewrite /in_generated_subgroup in Hin; move: Hin => [w approxw].
    rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /nth_gen in approxw.
    rewrite -eqsz in w approxw.
    exists(w).
    + rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /nth_gen.
      apply /trans.
      apply /symm /prod_congr.
      have eqsz_seq: size (map (fun c : InverseAlphabet 'I_(size (set_nth e v i x)) =>
                      match c with
                      | Base a => nth e v a
                      | Inverse a => inv (nth e v a)
                      end) w) = size (map (fun c : InverseAlphabet 'I_(size (set_nth e v i x)) =>
                      match c with
                      | Base a => nth e (set_nth e v i x) a
                      | Inverse a => inv (nth e (set_nth e v i x) a)
                      end) w).
        by rewrite !size_map.
      + by apply eqsz_seq.
      + move => k kbound.
        have hbound : (0 < size (set_nth e v i x))%N.
          rewrite size_set_nth.
          by lia.
        rewrite !(@nth_map _ (Base (Ordinal (hbound)))).
        case: (nth (Base (Ordinal hbound)) w k).
        + move => s.
          pose s':= nat_of_ord s.
          case: (s' =P i) => [Ht | Hf].
          - rewrite /s' in Ht; rewrite Ht  nth_set_nth /=.
            rewrite ifT //=.
            by apply symm.
          - rewrite /s' in Hf; rewrite nth_set_nth /=.
            rewrite ifF; last by apply/eqP.
            by apply refl.
        + move => s.
          pose s':= nat_of_ord s.
          case: (s' =P i) => [Ht | Hf].
          - rewrite /s' in Ht; rewrite Ht  nth_set_nth /=.
            rewrite ifT //=.
            by apply /symm; rewrite approxxnth.
          - rewrite /s' in Hf; rewrite nth_set_nth /=.
            rewrite ifF; last by apply/eqP.
            by apply refl.
        1-2: by rewrite size_map in kbound.
      + by  assumption.
Qed.

    


Lemma norm_igs (v : vec) (x : FreeGroup Sigma) (H: in_generated_subgroup v (FreeGroup_norm x)):
  in_generated_subgroup v x.
Proof.
  have Heq: FreeGroup_norm x == x.
    by apply: FreeGroup_norm_correct.
  apply: igs_proper.
  by apply /Heq. 
  by [].
Qed.

Lemma igs_norm (v : vec) (x : FreeGroup Sigma) (H: in_generated_subgroup v x):
  in_generated_subgroup v (FreeGroup_norm x).
Proof.
  have Heq: x == FreeGroup_norm x.
    by apply: symm; apply: FreeGroup_norm_correct.
  apply: igs_proper.
  by apply: Heq.
  by [].
Qed.

Definition f' (gens: vec) (i j : nat) (h: i <> j) (n': 'I_(size gens)) :=
    let n := nat_of_ord n' in
    if (n == i) then nth e (t2 gens i j h) i @ inv (nth e (t2 gens i j h) j)
    else nth e (t2 gens i j h) n.

Definition f (gens: vec) (n: 'I_(size gens)) := nth e gens n.

Lemma H_idiffj (i j : nat) (h: i <> j): (j == i)%B = false.
Proof.
  apply/eqP.
  by apply: not_eq_sym h.
Qed.

Lemma H_jnoteqi (i j : nat) (h: i <> j): j <> i.
Proof.
  by apply: not_eq_sym.
Qed.

(* the structure of the proof need to be worked on *)

Lemma t1_preserve_size (gens: vec) (i: nat) (Hibound: (i < size gens)%N):
size (t1 gens i) = size (gens).
Proof.
rewrite /t2 size_set_nth.
have: ((i.+1) <= size gens)%N.
  -apply: Hibound.
  move => Hinf.
  rewrite /max /maxn.
  case: ifP.
  - by [].
  - move => Hniinf.
    apply/eqP.
    rewrite eqn_leq Hinf /=.
    rewrite ltnNge in Hniinf.
    move/negPn in Hniinf.
    by [].
Qed.

Lemma t1_igs_base (gens : vec) (i : nat) (Hibound : (i < size gens)%N) (s: 'I_(size gens)):
  in_generated_subgroup (t1 gens i) (nth_gen gens s).
Proof.
  have Heq_size : size (t1 gens i) = size gens.
    by apply: t1_preserve_size.

  pose i' := Ordinal Hibound.

  case: (i' =P s) => [Ht | Hf].
    - rewrite -Ht.
      have: in_generated_subgroup (t1 gens i) (FreeGroup_norm (inv (inv (nth_gen gens i')))).
        rewrite !FreeGroup_norm_inv.
        apply: igs_inv.
        rewrite /nth_gen.
      have: FreeGroup_norm (inv (nth e gens i)) = nth e (t1 gens i) i.
        rewrite /t1 nth_set_nth /=.
        rewrite ifT.
        by [].
        by [].
      move => Heq.
      rewrite -FreeGroup_norm_inv Heq.
      change (nth e (t1 gens i) i) with (@nth_gen _ (t1 gens i) (cast_ord (esym Heq_size) i')).
      by apply: igs_gen.
      move => H_in_subgroup.
      have: FreeGroup_norm (inv (inv (nth_gen gens i'))) == FreeGroup_norm (nth_gen gens i').
        by rewrite !FreeGroup_norm_inv; apply: inv_involutive.
      move => H_proper.
      apply /norm_igs.
      apply: igs_proper.
      apply: H_proper.
      by apply: H_in_subgroup.
    -have: nth e gens s = nth e (t1 gens i) s.
      rewrite /t1 nth_set_nth /=.
      rewrite ifF.
      by [].
      apply/eqP.
      apply: not_eq_sym.
      move => H.
      apply: Hf.
      exact: ord_inj.
      move => H_t1_eq.
      rewrite /nth_gen H_t1_eq.
      change (nth e (t1 gens i) s) with (@nth_gen _ (t1 gens i) (cast_ord (esym Heq_size) s)).
      by apply: igs_gen.
Qed.

Lemma t1_include_subgroup (gens : vec) (i : nat) (Hibound : (i < size gens)%N):
  forall x, (in_generated_subgroup gens x -> in_generated_subgroup (t1 gens i) x).
Proof.
  move => x [wx Hx].
  rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension in Hx.
  have: forall y, y \in [seq match c with
    | Base a => nth_gen gens a
    | Inverse a => inv (nth_gen gens a)
    end
    | c <- wx] -> in_generated_subgroup (t1 gens i) y.
  move => y.
  move/mapP => [n _ ->].
  case: n => s.
    - by apply: t1_igs_base.
    - apply: igs_inv; by apply: t1_igs_base.
    move => H_forall.
    rewrite /prod in Hx.
    have: in_generated_subgroup (t1 gens i) (
      foldr (fun y => [eta law y]) e [seq match c with
        | Base a => nth_gen gens a
        | Inverse a => inv (nth_gen gens a)
      end | c <- wx
      ]
    ).
    apply: igs_foldr_stable.
    by apply: H_forall.
    by apply: subseq_refl.
    by apply: igs_proper.
Qed.

Lemma t1_inv (gens : vec) (i : nat) :
  nth e (t1 gens i) i = FreeGroup_norm (inv (nth e gens i)).
Proof.
  rewrite /t1 nth_set_nth /=.
  by rewrite ifT.
Qed.

Lemma t1_neutral (gens : vec) (i j : nat) (h: i <> j):
  nth e (t1 gens i) j = nth e gens j.
Proof.
  rewrite /t1 nth_set_nth /=.
  rewrite ifF.
  by [].
  apply/eqP.
  by apply: not_eq_sym h.
Qed.

(* Note(mathis): I would I prefere to have type 'I_(size gens) but to apply, I need this one and cast it *)
Lemma t1_invol (gens : vec) (i : nat) (Hibound : (i < size gens)%N):
  forall k: nat , nth e (t1 (t1 gens i) i) k == nth e gens k.
Proof.
  move => k.
  rewrite /t1 nth_set_nth /=.
  case: (k =P i) => [Ht | Hf].
  - rewrite nth_set_nth /=.
    rewrite ifT.
    rewrite !FreeGroup_norm_inv inv_involutive FreeGroup_norm_involutive Ht.
    by apply: FreeGroup_norm_correct.
    by [].
  - rewrite nth_set_nth /=.
    rewrite ifF.
    by [].
    apply/eqP.
    by [].
Qed.

Lemma t1_equal_subgroup (gens : vec) (i : nat) (Hibound : (i < size gens)%N):
  forall x, in_generated_subgroup gens x <-> in_generated_subgroup (t1 gens i) x.
Proof.
  have Heq_size: size (t1 (t1 gens i) i) = size gens.
    by rewrite t1_preserve_size t1_preserve_size.
  split.
  - move => H_in_sub.
    by apply: t1_include_subgroup.
  -
    have: forall x, in_generated_subgroup (t1 gens i) x -> in_generated_subgroup (t1 (t1 gens i) i) x.
      apply: t1_include_subgroup.
      by rewrite t1_preserve_size.
    move => H_t1t1.
    have: forall x, in_generated_subgroup (t1 (t1 gens i) i) x -> in_generated_subgroup gens x.
    
    pose perm_id (n : 'I_(size (t1 (t1 gens i) i))) := cast_ord (Heq_size) n.
    have Hbij_perm: bijective perm_id.
    exists (cast_ord (esym Heq_size)).
    move => s; rewrite /perm_id.
    by rewrite cast_ordK.
    move => s; rewrite /perm_id; by rewrite cast_ordKV.

    apply: in_generated_subgroup_perm_morphism; last first.
    by apply: Hbij_perm.
    rewrite /nth_gen.
    apply: t1_invol.
    by apply: Hibound.
    move => H h; move: (H x) => H_x; apply: H_x; by apply: (H_t1t1 x).
Qed.

Lemma t2_change (gens : vec) (i j : nat) (h : i <> j):
  (nth e gens i) @ (nth e gens j) == nth e (t2 gens i j h) i.
Proof.
  rewrite /=.
  rewrite /t2.
  rewrite nth_set_nth /=.
  rewrite ifT.
  by apply /symm /FreeGroup_norm_correct.
  by [].
Qed.

Lemma t2_change_inv (gens : vec) (i j : nat) (h : i <> j):
  (nth e (t2 gens i j h) i) @ (inv (nth e (t2 gens i j h) j)) == (nth e gens i).
Proof.
  rewrite /= /t2 nth_set_nth /= eqxx nth_set_nth /=.
  rewrite ifN.
  have Happrox : FreeGroup_norm (nth e gens i @ nth e gens j) @ inv (nth e gens j) == (nth e gens i @ nth e gens j) @ inv (nth e gens j).
    rewrite congruent_right.
    by apply /refl.
    by apply /FreeGroup_norm_correct.
  have Htrans: (nth e gens i @ nth e gens j) @ inv (nth e gens j) == nth e gens i.
    by rewrite  -associativity inverse_left neutral_right.
  rewrite (@trans _ (FreeGroup_norm (nth e gens i @ nth e gens j) @ inv (nth e gens j)) ((nth e gens i @ nth e gens j) @ inv (nth e gens j))).
  by apply /Htrans.
  by apply /Happrox.
  by [].
  move/eqP in h.
  by rewrite eq_sym.
Qed.

Lemma t2_neutral (gens: vec) (i j k : nat) (h: i <> j) (Hk: i <> k):
  nth e (t2 gens i j h) k = nth e gens k.
Proof.
  rewrite /t2 nth_set_nth /=.
  rewrite ifN.
  by [].
  move/eqP in Hk.
  by rewrite eq_sym.
Qed.

Lemma t2_preserve_size (gens: vec) (i j : nat) (Hibound: (i < size gens)%N) (h: i <> j):
  size (t2 gens i j h) = size (gens).
Proof.
  rewrite /t2 size_set_nth.
  have: ((i.+1) <= size gens)%N.
    -apply: Hibound.
    move => Hinf.
    rewrite /max /maxn.
    case: ifP.
    - by [].
    - move => Hniinf.
      apply/eqP.
      rewrite eqn_leq Hinf /=.
      rewrite ltnNge in Hniinf.
      move/negPn in Hniinf.
      by [].
Qed.

Lemma t2_include_subgroup (gens: vec) (i j : nat) (Hibound: (i < size gens)%N) (Hjbound: (j < size gens)%N) (h: i <> j):
  forall x, (in_generated_subgroup gens x -> in_generated_subgroup (t2 gens i j h) x).
Proof.
  move => x.
  - move => [wx Hx].
    rewrite /nth_gen in Hx.
    have: forall n , (f gens) n == (f' gens i j h) n.
    move => n.
      pose n' := nat_of_ord n.
      case: (n' =P i) => [Ht | Hf].
        - rewrite /f /f' /=.
          rewrite ifT.
          rewrite /n' in Ht.
          by rewrite t2_change_inv Ht.
          move/eqP in Ht.
          by [].
        - rewrite /f /f' /=.
          rewrite ifN.
          rewrite t2_neutral.
          by [].
          by apply: not_eq_sym.
          move/eqP in Hf.
          by [].
    - move => Heq.
      have: \hat (f gens) wx == \hat (f' gens i j h) wx.
      apply: extension_universality.
      move => a.
      rewrite /=.
      case: a => [HB | HI].
      - by rewrite Heq neutral_right.
      - by rewrite Heq neutral_right.
    - move => Heqf.
      rewrite Hx in Heqf.
      have: forall n, in_generated_subgroup (t2 gens i j h) (f' gens i j h n).
      move => n;
      rewrite /f'.

      pose n' := nat_of_ord n.
      case: (n' =P i) => [Ht | Hf].
        - apply: igs_law.
          have Heq_size : size (t2 gens i j h) = size gens.
            apply: t2_preserve_size.
            by apply: Hibound.
          
          change (nth e (t2 gens i j h) i) with (@nth_gen _ (t2 gens i j h) (cast_ord (esym Heq_size) (Ordinal Hibound))).
          apply: igs_gen.
          - apply: igs_inv.
          have Heq_size : size (t2 gens i j h) = size gens.
            by apply: t2_preserve_size.
          change (nth e (t2 gens i j h) j) with (@nth_gen _ (t2 gens i j h) (cast_ord (esym Heq_size) (Ordinal Hjbound))).
          apply: igs_gen.
        - have Heq_size : size (t2 gens i j h) = size gens.
            by apply: t2_preserve_size.
          change (nth e (t2 gens i j h) n) with (@nth_gen _ (t2 gens i j h) (cast_ord (esym Heq_size) n)).
          apply: igs_gen.
      move => H_subgroup_f'n.

      have: in_generated_subgroup (t2 gens i j h) (\hat (f' gens i j h) wx).
        rewrite /FreeGroup_universal_extension /extension.
        rewrite /FreeGroup_alphabet_extension.
        rewrite /prod.

        apply: (igs_foldr_stable (t2 gens i j h) [seq match c with
        | Base a => f' gens i j h a
        | Inverse a => inv (f' gens i j h a)
        end  | c <- wx]).
        apply: H_all.
        apply: H_subgroup_f'n.
        apply: subseq_refl.
    move => H_in.
    apply: igs_proper.
    by rewrite Heqf.
    by apply: H_in.
Qed.

Lemma t2_equal_subgroup (gens: vec) (i j : nat) (Hibound : (i < size gens)%N) (Hjbound : (j < size gens)%N) (h: i <> j):
  forall x, (in_generated_subgroup gens x <-> in_generated_subgroup (t2 gens i j h) x).
Proof.
  move => x.
  split.
    - apply: t2_include_subgroup.
      by [].
      by [].
    -have H1: in_generated_subgroup (t2 gens i j h) x <-> in_generated_subgroup (t1 (t2 gens i j h) j) x.
      apply: t1_equal_subgroup.
      rewrite t2_preserve_size.
      by apply: Hjbound.
      by apply: Hibound.
     have H2: in_generated_subgroup (t1 (t2 gens i j h) j) x -> in_generated_subgroup (t2 (t1 (t2 gens i j h) j) i j h) x.
      apply: t2_include_subgroup.
      rewrite t1_preserve_size t2_preserve_size.
      1-4: assumption.
      rewrite t1_preserve_size t2_preserve_size.
      1-4: assumption.
      have H3: forall x, in_generated_subgroup (t2 (t1 (t2 gens i j h) j) i j h) x -> in_generated_subgroup (t1 (t2 (t1 (t2 gens i j h) j) i j h) j)x .
        apply: t1_include_subgroup.
        by rewrite t2_preserve_size t1_preserve_size t2_preserve_size.

      have H4: forall x, in_generated_subgroup (t1 (t2 (t1 (t2 gens i j h) j) i j h) j) x -> in_generated_subgroup gens x.

      have Heq_size: size (t1 (t2 (t1 (t2 gens i j h) j) i j h) j) = size gens.
        by rewrite t1_preserve_size t2_preserve_size t1_preserve_size t2_preserve_size.

      pose perm_id (n : 'I_(size (t1 (t2 (t1 (t2 gens i j h) j) i j h) j))) := cast_ord (Heq_size) n.
      have Hbij: bijective perm_id.
        exists (cast_ord (esym Heq_size)).
        move => s.
        by rewrite cast_ordK.
        move => s.
        by rewrite /perm_id cast_ordKV.
      apply: in_generated_subgroup_perm_morphism; last first. (* swap to force the Goal0? to be perm_id *)
      by apply: Hbij.
      move => n; case: n => [n Hn].
      rewrite /nth_gen /=.
      case: (n =P i)%B => [Htn | Hfn].
        - rewrite Htn t1_neutral.
          rewrite -t2_change.
          rewrite t1_inv t1_neutral.

          apply /trans.
          apply /congruent_left /FreeGroup_norm_correct.
          rewrite -t2_change.
          rewrite t2_neutral.
          by rewrite -associativity inverse_left neutral_right.
          by [].
          1-2: by apply: H_jnoteqi.
        - case: (n =P j)%B => [Htj | Hfj].
          - rewrite Htj t1_inv t2_neutral.
            rewrite t1_inv !FreeGroup_norm_inv inv_involutive FreeGroup_norm_involutive t2_neutral.
            by rewrite FreeGroup_norm_correct.
            by rewrite Htj in Hfn.
            by rewrite Htj in Hfn.
          - rewrite t1_neutral.
            rewrite t2_neutral.
            rewrite t1_neutral.
            rewrite t2_neutral.
            by [].
            1-4: by apply: not_eq_sym.
      move => H0.
      apply: H4; apply: H3; apply: H2.
      case: H1 => H1 _.
      by apply: H1.
Qed.

Lemma t3_neutral (gens: vec) (s: 'I_(size gens)) (Hnon_trivial: FreeGroup_norm (nth_gen gens s) <> e): (* need to change *)
  (nth_gen gens s) \in (t3 gens).
Proof.
  rewrite /t3 /nth_gen.
  rewrite mem_filter.
  apply/andP.
  split.
  - apply/eqP.
    by apply: Hnon_trivial.
  - apply: mem_nth.
    by [].
Qed.

Lemma t3_include_subgroup (gens: vec):
  forall x, in_generated_subgroup gens x -> in_generated_subgroup (t3 gens) x.
Proof.
  move => x [w]. (* proof tactic inspired from in_generated_subgroup_rcons_morphism*)
  elim: w x => [x /= H|wh wt IH x].
    - apply: igs_proper.
      apply: H.
      by apply: igs_e.
    - rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /prod /=.
    case: wh => s.
      case: (FreeGroup_norm (nth_gen gens s) =P e) => [Ht | Hf].
        - rewrite -[nth_gen gens s] FreeGroup_norm_correct.
          rewrite Ht neutral_left.
          rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /prod /= in IH.
          move: (IH x) => IHx.
          by apply: IHx.
        - have: (nth_gen gens s) \in (t3 gens).
            apply: t3_neutral.
            by [].
          move => H_in.

          have: in_generated_subgroup (t3 gens) (nth_gen gens s @
            foldr (fun y : presented (FGP Sigma) => [eta law y]) e
            [seq match c with
            | Base a => nth_gen gens a
            | Inverse a => inv (nth_gen gens a)
            end
            | c <- wt]).
            apply: igs_law.
            move/nthP in H_in.
            move: (H_in e) => [i Hbound Heq].
            rewrite -Heq.
            change (nth e (t3 gens) i) with (nth_gen (t3 gens) (Ordinal Hbound)).
            by apply: igs_gen.
          rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /prod /= in IH.
          move: (IH (foldr (fun y : presented (FGP Sigma) => [eta law y]) e
          [seq match c with
          | Base a => nth_gen gens a
          | Inverse a => inv (nth_gen gens a)
          end
          | c <- wt])) => IHfold.
          by apply: IHfold.
          move => H1 H2; move: H2 H1.
          by apply: igs_proper.
    case: (FreeGroup_norm (nth_gen gens s) =P e) => [Ht | Hf].
      - rewrite -[nth_gen gens s] FreeGroup_norm_correct.
        rewrite Ht neutral_left.
        rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /prod /= in IH.
        move: (IH x) => IHx.
        by apply: IHx.
      - have: (nth_gen gens s) \in (t3 gens).
          apply: t3_neutral.
          by [].
        move => H_in.

        have: in_generated_subgroup (t3 gens) (inv (nth_gen gens s) @
          foldr (fun y : presented (FGP Sigma) => [eta law y]) e
          [seq match c with
          | Base a => nth_gen gens a
          | Inverse a => inv (nth_gen gens a)
          end
          | c <- wt]).
        apply: igs_law.
        -  move/nthP in H_in.
          move: (H_in e) => [i Hbound Heq].
          rewrite -Heq.
          change (nth e (t3 gens) i) with (nth_gen (t3 gens) (Ordinal Hbound)).
          apply: igs_inv.
          by apply: igs_gen.
        - rewrite /FreeGroup_universal_extension /extension /FreeGroup_alphabet_extension /prod /= in IH.
          move: (IH (foldr (fun y : presented (FGP Sigma) => [eta law y]) e
          [seq match c with
          | Base a => nth_gen gens a
          | Inverse a => inv (nth_gen gens a)
          end
          | c <- wt])) => IHfold.
          by apply: IHfold.
        move => H1 H2; move: H2 H1.
        by apply: igs_proper.
Qed.

Lemma t3_inj (gens : vec):
  forall x, x \in (t3 gens) -> x \in gens.
Proof.
  move => x H_in.
  rewrite /t3 in H_in.
  rewrite mem_filter in H_in.
  move/andP: H_in => [_ H_in].
  by [].
Qed.

(* Note(mathis): Once again, there is some code duplication, It would be cool to factor it *)

Lemma t3_equality_subgroup (gens: vec):
  forall x, in_generated_subgroup gens x <-> in_generated_subgroup (t3 gens) x.
Proof.
  split.
  - by apply: t3_include_subgroup.
  - move => [w].
    elim: w x => [x /= H|wh wt IH x].
    - apply: igs_proper.
      by apply: H.
      by apply: igs_e.
    - rewrite hat_cons /FreeGroup_alphabet_extension.
      case: wh => s H_law.
        - have H_in_subgroup: in_generated_subgroup gens (nth_gen (t3 gens) s).
            have H_ingens: (nth_gen (t3 gens) s) \in gens.
              apply: t3_inj.
              by apply: mem_nth.
            move/nthP in H_ingens.
            move: (H_ingens e) => [i Hbound Heq].
            rewrite -Heq.
            change (nth e gens i) with (nth_gen gens (Ordinal Hbound)).
            by apply: igs_gen.
          have H_in_subgroup_hat: in_generated_subgroup gens (\hat (nth_gen (t3 gens)) wt).
            move: (IH (\hat (nth_gen (t3 gens)) wt)) => H.
            by apply: H.
          
          apply: igs_proper.
          apply: H_law.
          apply: igs_law.
            by apply: H_in_subgroup.
            by apply: H_in_subgroup_hat.
        - have H_in_subgroup: in_generated_subgroup gens (inv (nth_gen (t3 gens) s)).
            have H_ingens: (nth_gen (t3 gens) s) \in gens.
              apply: t3_inj.
              by apply: mem_nth.
            move/nthP in H_ingens.
            move: (H_ingens e) => [i Hbound Heq].
            rewrite -Heq.
            apply : igs_inv.
            change (nth e gens i) with (nth_gen gens (Ordinal Hbound)).
            by apply: igs_gen.
          have H_in_subgroup_hat: in_generated_subgroup gens (\hat (nth_gen (t3 gens)) wt).
            move: (IH (\hat (nth_gen (t3 gens)) wt)) => H.
            by apply: H.
          
          apply: igs_proper.
          apply: H_law.
          apply: igs_law.
            by apply: H_in_subgroup.
            by apply: H_in_subgroup_hat.
Qed.


Definition sort_uniq {T: eqType} (h: T -> T -> bool) (u: seq T) :=
    sort h (undup u).

Definition first_reduce_step (gens: vec) :=
  let indices := allpairs (fun a b => (a, b)) (enumerate gens) (enumerate gens)
  in let off_diagonal := filter (fun '((i, _), (j, _)) =>
    i != j) indices in

  let reduction_N1_attempt := [seq (fun '((i, w1), (j, w2)) =>
    map (fun elm => (size (FreeGroup_norm w1), size (FreeGroup_norm w2), (i, j), elm))
    [:: FreeGroup_norm (w1 @ w2);
        FreeGroup_norm (w1 @ (inv w2));
        FreeGroup_norm ((inv w1) @ w2);
        FreeGroup_norm ((inv w1) @ (inv w2))]) x | x <- off_diagonal] in

  let potential_reduc := map (fun '(len1, len2, (i, j), w) => (i, j, w)) (flatten (
    map (filter (fun '(len1, len2, (i, j), w) => ((size (FreeGroup_norm w)) < len1)%N)) reduction_N1_attempt
  )) in
  potential_reduc.

Definition first_reduce_variant (v : vec) : nat := 
  sumn [seq size (FreeGroup_norm w) | w <- v].

Function first_reduce (gens: vec) {measure first_reduce_variant gens} :=
  let assocs := first_reduce_step (gens) in
  match assocs with
    | [::] => t3 gens
    | (i, j, w)::t =>
      let gens' := set_nth e gens i w in
      first_reduce gens'
    end.
Proof.
  move => gens p t p0 w i j Heq_p0 Heq_p Hfrs.
  rewrite /first_reduce_step in Hfrs.
  have H_in: (i, j, w) \in (i, j, w)::t.
    by apply: mem_head.
  rewrite -Hfrs in H_in.
  move/mapP in H_in.
  case: H_in => k H_ink.
  move/flattenP in H_ink.
  case: H_ink => s H_ins.
  move/mapP in H_ins.
  case: H_ins => x H_inx.
  move/mapP in H_inx.
  case: H_inx => [[[yi wi] [yj wj]] Hin_filter].

  move => Heq_x Hs H_kins Hk.
  rewrite Hs mem_filter in H_kins.
  move/andP in H_kins.
  case: H_kins => [H_condition H_kinx].
  rewrite Heq_x in H_kinx.

  move/mapP in H_kinx.
  case: H_kinx => [z H_zin Heq_k].

  rewrite Heq_k /= in Hk.
  case: Hk => [Heq_iyi Heq_jyj Heq_wr].

  rewrite mem_filter in Hin_filter.
  move/andP in Hin_filter.
  move: Hin_filter => [yi_diff_yj H_inallpairs].
  move/allpairsP in H_inallpairs.
  case: H_inallpairs => [q [H1_inenum H2_inenum [Heq_q1 Heq_q2]]].

  (* the bookeeping is done *)

  have H_ibound: (i < size [seq size (FreeGroup_norm x0) | x0 <- gens])%N.
    rewrite -Heq_q1 in H1_inenum.
      
    rewrite size_map.
    by rewrite Heq_iyi (@bound_enumerate _ e 0 gens yi wi).

  have H_size: size (iota 0 (size gens)) = size gens.
    by rewrite size_iota.

  have Heq_nthiwi: nth e gens i = wi.
    rewrite -Heq_q1 in H1_inenum.
    rewrite Heq_iyi. apply: in_enumerate.
    exact: 0.
    by [].

  have Heq_nthmap : nth 0 [seq size (FreeGroup_norm x0)  | x0 <- gens] i = size (FreeGroup_norm wi).
    rewrite (@nth_map _ e _ _ _ _).
    by rewrite Heq_nthiwi.
    rewrite -Heq_q1 in H1_inenum.

    by rewrite Heq_iyi (@bound_enumerate _ e 0 gens yi wi).
  (*----*)

  rewrite Heq_k /= -Heq_wr in H_condition.

  rewrite /first_reduce_variant.
  apply:ltP.
  rewrite map_set_nth sumn_set_nth /= mul0n addn0.

  rewrite H_ibound muln1.
  
  rewrite Heq_nthmap.
  rewrite ltn_subLR.
  rewrite addnC.

  by rewrite ltn_add2r.
  apply: leq_trans; last first.
  - by apply: leq_addr.
  apply /in_sumn /nthP; exists (i).
    by apply: H_ibound.
    by apply: Heq_nthmap.
Qed.


(* Note(mathis): the type annotations are necessary *)
Definition second_reduce_step (gens: vec) :=
  let igens := enumerate gens in
  let potential_reduc := filter (fun '((ix, x), (iy, y)) => ix != iy) (allpairs (fun a b => (a, b)) igens igens) in
  flatten (map (fun '(((ix, x), (iy, y)) : (nat * word) * (nat * word)) => pmap
      (fun '(k, xy) =>
        if ((xy < x)%O) then
          Some(k, ix, iy, xy)
        else
          None: option (nat * nat * nat * word)
      ) (enumerate [:: FreeGroup_norm (x @ y); FreeGroup_norm (x @ inv y); FreeGroup_norm (inv x @ y); FreeGroup_norm (inv x @ inv y)])
  ) potential_reduc).

Lemma decreasing_stepk0 (gens : vec) (ix iy k : nat) (xy: word) (t : seq _) (nempty: second_reduce_step gens = (k, ix, iy, xy)::t):
  (xy < (nth e gens ix))%O.
Proof.
  have Hin: (k, ix, iy, xy) \in (second_reduce_step gens).
    by rewrite nempty mem_head.
  rewrite /second_reduce_step in Hin.
  move/flatten_mapP: Hin => [[[pix px] [piy py]] pin pin'].
  rewrite mem_pmap in pin'; move/mapP: pin' => [[k' w] win weq].

  case: (boolP (w < px)%O) => [Ht | Hf]; last first.
  + by move/negbTE in Hf; rewrite Hf in weq.
  rewrite Ht in weq; move: weq => [eqk eqixpix eqiypiy eqxyw].

  rewrite mem_filter in pin; move/andP: pin => [diffpixpiy pin].

  move/allpairsP: pin => [[[qix qx] [qiy qy]] [q1in q2in [eqpixqix eqpxqx eqpiyqiy eqpyqy]]].
  rewrite /= in q1in q2in.
  rewrite eqixpix eqpixqix eqxyw.
  rewrite eqpxqx in Ht.
  by rewrite (@in_enumerate _ _ 0 _ qix qx).
Qed.

Lemma second_reduce_step_neq (gens: vec) (k ix iy: nat) (xy: word) (t: seq _) (Heq: second_reduce_step gens = (k, ix, iy, xy)::t):
  ix <> iy.
Proof.
  have Hin: (k, ix, iy, xy) \in second_reduce_step gens.
    by rewrite Heq mem_head.
  rewrite /second_reduce_step in Hin.
  move/flattenP: Hin => [s /mapP [[[ix' x] [iy' y]] xin eqs] tins].
  rewrite mem_filter in xin.
  rewrite eqs mem_pmap in tins.
  move/mapP: tins => [[k' xy'] zin eqz].
  move: eqz; case: ifP => [_ [eqkk' eqixix' eqiyiy' eqxyxy']|//].
  rewrite -eqixix' -eqiyiy' in xin.
  by move/andP: xin => [/eqP R _].
Qed.


Definition vec_lexico_ltP (gens gens': vec): Prop := (gens < gens')%O.

(* Note(mathis): The weird function structure inside the match is here to provide a proof of ix <> iy *)
Program Fixpoint second_reduce (gens: vec) {wf vec_lexico_ltP gens} :=
  match second_reduce_step gens with
    | [::] => gens
    | (k, ix, iy, xy)::t =>
      let h := second_reduce_step_neq gens k ix iy xy t (erefl) in
      let gens' :=
        if k==0 then t2 gens ix iy h
        else if k==1 then t1 (t2 (t1 gens iy) ix iy h) iy
        else if k==2 then t2 (t1 gens ix) ix iy h
        else if k==3 then t1 (t2 (t1 (t1 gens iy) ix) ix iy h) iy
        else gens
      in
      second_reduce gens'
  end.

Lemma eq_size_t (gens : vec) (ix iy: nat) (hboundx: (ix < size gens)%N) (hboundy: (iy < size gens)%N) (h : ix <> iy):
  size (t1 (t2 (t1 (t1 gens iy) ix) ix iy h) iy) = size gens.
Proof.
  by rewrite t1_preserve_size t2_preserve_size t1_preserve_size t1_preserve_size.
Qed.

Lemma eq_size_setnth (gens : vec) (ix: nat) (x: word) (hboundx: (ix < size gens)%N) :
 size (set_nth e gens ix x) = size gens.
Proof.
  rewrite size_set_nth /maxn.
  case (boolP (ix.+1 < size gens)%N) => [Ht | Hf].
    - by rewrite Ht.
    move/negbTE in Hf; rewrite Hf; rewrite ltnNge in Hf; move/negbFE in Hf.
    by apply/eqP; rewrite eqn_leq Hf hboundx.
Qed.

Next Obligation.
Proof.
  rewrite /vec_lexico_ltP.
  have Hin: (k, ix, iy, xy) \in (second_reduce_step gens).
    by rewrite -Heq_anonymous mem_head.
  rewrite /second_reduce_step in Hin.
  move/flatten_mapP: Hin => [[[pix px] [piy py]] pin pin'].
  rewrite mem_pmap in pin'; move/mapP: pin' => [[k' w] win weq].
  case: (boolP (w < px)%O) => [Ht | Hf]; last first.
  + by move/negbTE in Hf; rewrite Hf in weq.
  rewrite Ht in weq; move: weq => [eqk eqixpix eqiypiy eqxyw].
  rewrite mem_filter in pin; move/andP: pin => [diffpixpiy pin].
  move/allpairsP: pin => [[[qix qx] [qiy qy]] [q1in q2in [eqpixqix eqpxqx eqpiyqiy eqpyqy]]].
  rewrite /= in q1in q2in.

  have diffixiy : ix <> iy.
    by rewrite eqixpix eqiypiy; apply/eqP.

  have szx : (ix < size gens)%N.
      by rewrite eqixpix eqpixqix (@bound_enumerate _ e 0 gens qix qx q1in).
  have szy : (iy < size gens)%N.
    by rewrite eqiypiy eqpiyqiy (@bound_enumerate _ e 0 gens qiy qy q2in).

  case: eqP => [Hkt | Hdiff0] => /=.
    rewrite -eqk in win; rewrite Hkt in win.
    rewrite /t2 lt_set_nth_sizelexi //=.
    have eqw: w = nth e ([:: FreeGroup_norm (px @ py); FreeGroup_norm (px @ inv py); FreeGroup_norm (inv px @ py); FreeGroup_norm (inv px @ inv py)]) 0.
      by rewrite (@in_enumerate _ _ 0 _ _ w win).
    + rewrite /= in eqw.
    rewrite eqpxqx eqpyqy in eqw Ht;
    by rewrite eqixpix eqpixqix eqiypiy eqpiyqiy (@in_enumerate _ _ 0 _ _ qx q1in) (@in_enumerate _ _ 0 _ _ qy q2in) -eqw.
  case: eqP => [Hkt | Hdiff1] => /=.
    rewrite -eqk in win; rewrite Hkt in win.

    have Hleq : (t1 (t2 (t1 gens iy) ix iy diffixiy) iy <=
      set_nth e gens ix (FreeGroup_norm (nth e gens ix @ inv (nth e gens iy))) :> vec)%O.
      rewrite (@pointwise_le_seq _ _ (e:>word) _ _) //=.
        rewrite t1_preserve_size t2_preserve_size t1_preserve_size.
        rewrite eq_size_setnth //=.
        1-7: by [].
      move => i ibound.
      case: (i =P ix) => [Hixt | Hixf].
      - rewrite Hixt.
        apply /CmpOrder.cmp_congr_left.
        apply /(@FreeGroup_norm_unique _ _ (nth e (set_nth e gens ix (FreeGroup_norm (nth e gens ix @ inv(nth e gens iy)))) ix)).
        + rewrite t1_neutral.
          rewrite -t2_change t1_inv t1_neutral.
          rewrite nth_set_nth /=.
          rewrite ifT.
          apply /trans. apply /congruent_left; apply /FreeGroup_norm_correct.
          apply /symm /FreeGroup_norm_correct.
          + by apply/eqP.
        + by apply /not_eq_sym /diffixiy.
        + by apply /not_eq_sym /diffixiy.
        by apply: CmpOrder.cmp_refl.
      - apply /CmpOrder.cmp_congr_left.
        apply /(@FreeGroup_norm_unique _ _ (nth e (set_nth e gens ix (FreeGroup_norm (nth e gens ix @ inv (nth e gens iy)))) i)).
        case: (i =P iy) => [Hyt | Hyf].
          - rewrite Hyt t1_inv t2_neutral.
            rewrite t1_inv !FreeGroup_norm_inv inv_involutive FreeGroup_norm_involutive.
            rewrite nth_set_nth /=.
            rewrite ifF.
            by apply /FreeGroup_norm_correct.
            + by rewrite -Hyt; apply/eqP.
            + by  rewrite -Hyt; apply/not_eq_sym.
          - rewrite t1_neutral; last first.
            + by apply/not_eq_sym.
            rewrite t2_neutral; last first.
            + by apply/not_eq_sym.
            rewrite t1_neutral; last first.
            + by apply/not_eq_sym.
            rewrite nth_set_nth /=.
            rewrite ifF //=.
            + by apply/eqP.
            by apply /CmpOrder.cmp_refl.
    have Hlt: (set_nth e gens ix (FreeGroup_norm (nth e gens ix @ inv (nth e gens iy))) < gens :> vec)%O.
      rewrite lt_set_nth_sizelexi //=.
      have eqw: w = nth e ([:: FreeGroup_norm (px @ py); FreeGroup_norm (px @ inv py); FreeGroup_norm (inv px @ py); FreeGroup_norm (inv px @ inv py)]) 1.
        by rewrite (@in_enumerate _ _ 0 _ _ w win).
      + rewrite /= in eqw.
      rewrite eqpxqx eqpyqy in eqw Ht.
      by rewrite eqixpix eqpixqix eqiypiy eqpiyqiy (@in_enumerate _ _ 0 _ _ qx q1in) (@in_enumerate _ _ 0 _ _ qy q2in) -eqw //=.
    apply: Order.PreorderTheory.le_lt_trans.
    + by apply: Hleq.
    + by apply: Hlt.

  case: eqP => [Hkt | Hdiff2] => /=.
    rewrite -eqk in win; rewrite Hkt in win.

    have Hleq : (t2 (t1 gens ix) ix iy diffixiy <=
      set_nth e gens ix (FreeGroup_norm (inv(nth e gens ix) @ nth e gens iy)) :> vec)%O.
      rewrite (@pointwise_le_seq _ _ (e:>word) _ _) //=.
        rewrite t2_preserve_size t1_preserve_size.
        rewrite eq_size_setnth //=.
        1-3: by [].
      move => i ibound.
      case: (i =P ix) => [Hixt | Hixf].
      - rewrite Hixt.
        apply /CmpOrder.cmp_congr_left.
        apply /(@FreeGroup_norm_unique _ _ (nth e (set_nth e gens ix (FreeGroup_norm (inv(nth e gens ix) @ nth e gens iy))) ix)).
        + rewrite -t2_change t1_inv t1_neutral.
          rewrite nth_set_nth /=.
          rewrite ifT.
          apply /trans.
          apply /congruent_right; apply /FreeGroup_norm_correct.
          apply /symm /FreeGroup_norm_correct.
          + by apply/eqP.
        + by apply /diffixiy.
        by apply: CmpOrder.cmp_refl.
      - apply /CmpOrder.cmp_congr_left.
        apply /(@FreeGroup_norm_unique _ _ (nth e (set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ nth e gens iy))) i)).
        case: (i =P iy) => [Hyt | Hyf].
          - rewrite Hyt t2_neutral.
            rewrite t1_neutral.
            rewrite nth_set_nth /=.
            rewrite ifF.
            by [].
            + by rewrite -Hyt; apply/eqP.
            + by  rewrite -Hyt; apply/not_eq_sym.
            + by apply /diffixiy.
          - rewrite t2_neutral; last first.
            + by apply/not_eq_sym.
            rewrite t1_neutral; last first.
            + by apply/not_eq_sym.
            rewrite nth_set_nth /=.
            rewrite ifF //=.
            + by apply/eqP.
            by apply /CmpOrder.cmp_refl.
    have Hlt: (set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ nth e gens iy)) < gens :> vec)%O.
      rewrite lt_set_nth_sizelexi //=.
      have eqw: w = nth e ([:: FreeGroup_norm (px @ py); FreeGroup_norm (px @ inv py); FreeGroup_norm (inv px @ py); FreeGroup_norm (inv px @ inv py)]) 2.
        by rewrite (@in_enumerate _ _ 0 _ _ w win).
      + rewrite /= in eqw.
      rewrite eqpxqx eqpyqy in eqw Ht.
      by rewrite eqixpix eqpixqix eqiypiy eqpiyqiy (@in_enumerate _ _ 0 _ _ qx q1in) (@in_enumerate _ _ 0 _ _ qy q2in) -eqw //=.
    apply: Order.PreorderTheory.le_lt_trans.
    + by apply: Hleq.
    + by apply: Hlt.
  
  case: eqP => [Hkt | Hdiff3] => /=.
    rewrite -eqk in win; rewrite Hkt in win.

    have Hleq : (t1 (t2 (t1 (t1 gens iy) ix) ix iy
      diffixiy) iy <=
      set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ inv (nth e gens iy))) :> vec)%O.
      rewrite (@pointwise_le_seq _ _ (e:>word) _ _) //=.
      rewrite [size (set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ inv (nth e gens iy))))] eq_size_setnth.
      by rewrite eq_size_t.
      + by [].
      move => i ibound.
      have happrox: (nth e (t1 (t2 (t1 (t1 gens iy) ix) ix iy
                    diffixiy) iy) i) ==
                    nth e (set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ inv (nth e gens iy)))) i.
        case: (i =P ix) => [Hxt | Hxf].
        - rewrite Hxt t1_neutral.
          rewrite -t2_change t1_inv t1_neutral.
          rewrite t1_neutral.
          rewrite t1_inv.
          apply: trans.
          + by apply /symm /FreeGroup_norm_correct.
          + rewrite -FreeGroup_norm_law nth_set_nth /=.
            rewrite ifT.
            + by [].
            + by [].
            + by apply /diffixiy.
            + by apply /not_eq_sym /diffixiy.
            + by apply /not_eq_sym /diffixiy.
        - case: (i =P iy) => [Hyt | Hyf].
          - rewrite Hyt.
            rewrite t1_inv t2_neutral.
            rewrite t1_neutral.
            rewrite t1_inv !FreeGroup_norm_inv inv_involutive FreeGroup_norm_involutive nth_set_nth /=.
            rewrite ifF.
            by apply /FreeGroup_norm_correct.
            + by rewrite Hyt in Hxf; apply/eqP.
            +1-2 : by apply /diffixiy.
          - rewrite t1_neutral; last first.
            + by apply /not_eq_sym.
            rewrite t2_neutral; last first.
            + by apply /not_eq_sym.
            rewrite t1_neutral; last first.
            + by apply /not_eq_sym.
            rewrite t1_neutral; last first.
            + by apply /not_eq_sym.
            rewrite nth_set_nth /=.
            rewrite ifF //=; last first.
            + by apply/eqP.

      case: (i =P ix) => [HiT | HiF]; last first.
      - apply: CmpOrder.cmp_congr_left.
        by apply /FreeGroup_norm_unique /happrox.
        rewrite !nth_set_nth /=.
        rewrite ifF.
        by rewrite CmpOrder.cmp_refl.
        by apply/eqP.
      - apply: CmpOrder.cmp_congr_left.
        by apply /FreeGroup_norm_unique /happrox.
        rewrite !nth_set_nth /=.
        rewrite ifT.
        by rewrite CmpOrder.cmp_refl.
        by apply/eqP.
        
    have Hlt : (set_nth e gens ix (FreeGroup_norm (inv (nth e gens ix) @ inv(nth e gens iy))) < gens :> vec)%O.
      rewrite lt_set_nth_sizelexi //=.
      have eqw: w = nth e ([:: FreeGroup_norm (px @ py); FreeGroup_norm (px @ inv py); FreeGroup_norm (inv px @ py); FreeGroup_norm (inv px @ inv py)]) 3.
        by rewrite (@in_enumerate _ _ 0 _ _ w win).
      + rewrite /= in eqw.
      rewrite eqpxqx eqpyqy in eqw Ht.
      by rewrite eqixpix eqpixqix eqiypiy eqpiyqiy (@in_enumerate _ _ 0 _ _ qx q1in) (@in_enumerate _ _ 0 _ _ qy q2in) -eqw //=.
    apply: Order.PreorderTheory.le_lt_trans.
    + by apply: Hleq.
    + by apply: Hlt.

    (* the else case cannot happen *)
    exfalso.
    have kofb: (k > 3)%N.
      by lia.
    have kinb: (k < 4)%N.
      rewrite -eqk in win.
      have kinb': (k < (size [:: FreeGroup_norm (px @ py);  FreeGroup_norm (px @ inv py);  FreeGroup_norm (inv px @ py);  FreeGroup_norm (inv px @ inv py)]))%N.
        by rewrite (@bound_enumerate _ _ 0 _ _ w).
      by rewrite /= in kinb'.
    by move: (leq_ltn_trans kofb kinb).
Qed.


Next Obligation.
Proof.
  rewrite /MR /vec_lexico_ltP /Order.lt /=.
  apply: sizelexi_wf.
  by apply /CmpOrder.cmp_wf /le_wf.
Qed.

(* Hypothesis N0: forall x, (x \in U) -> FreeGroup_norm x <> e.
Hypothesis N1_left: forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) ->
  (sz (x @ y) >= sz(x))%N.
Hypothesis N1_right: forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) ->
  (sz(x @ y) >= sz(y))%N. *)

Print second_reduce.

Lemma second_reduce_fixpoint (v : vec) :
  second_reduce_step (second_reduce v) = [::].
Proof.
  elim/(well_founded_ind second_reduce_obligation_3): v.
  move => x y.
Qed.
  

Definition NielsenReduction (gens: vec) :=
  map (FreeGroup_norm) (t3 (second_reduce gens)).

Context {v: vec}.
Let gens := NielsenReduction v.
Let U := gens ++ [seq (inv w) | w <- gens].

Lemma NielsenR_N0:
  forall x, (x \in U) -> FreeGroup_norm x <> e.
Proof.
  move => x xinU.
  rewrite /U mem_cat /gens /NielsenReduction /t3 in xinU; case/orP: xinU => /mapP [y yin xeq].
  + rewrite mem_filter in yin; move/andP: yin => [/eqP H _].
    by rewrite FreeGroup_norm_e in H; rewrite xeq FreeGroup_norm_involutive.
  + move/mapP: yin => [z zin yeq].
    rewrite mem_filter in zin; move/andP: zin => [/eqP H _].
    rewrite FreeGroup_norm_e in H; rewrite xeq yeq -FreeGroup_norm_inv FreeGroup_norm_involutive -FreeGroup_norm_e => habs.
    move/(f_equal inv) in habs.
    rewrite FreeGroup_norm_inv inv_eq_invol /= /inv/=/inv_word/= in habs.
    by rewrite habs in H.
Qed.

Lemma NielsenR_N1_left:
  forall x y, (x \in U) -> (y \in U) -> (non_trivial x y) ->
  (sz (x @ y) >= sz(x))%N.
Proof.
  move => x y xinU yinU.
  rewrite /U !mem_cat /gens /NielsenReduction in yinU xinU.
  case/orP: yinU => [|] /mapP [y' yin yeq] non_trvxy.
  + case/orP: xinU => [|] /mapP [x' xin xeq].
    rewrite /t3 !mem_filter in xin yin; move/andP: xin => [ntrvx x'ins]; move/andP: yin => [ntrvy y'ins].
    rewrite leqNgt; apply/negP => habs.
    rewrite /second_reduce in x'ins y'ins.
    Check second_reduce_equation.




End NielsenConstructionCorrection.
