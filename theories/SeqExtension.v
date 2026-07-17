From elpi.apps Require Import coercion.
From HB Require Import structures.

From Stdlib Require Import Recdef Program.
Require Import Setoid Morphisms.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import all_ssreflect path.
From mathcomp Require Import eqtype seq fintype all_algebra div.
From mathcomp Require Import ring lra zify.

Import GRing.Theory.

Open Scope ring_scope.


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

(* extension of mask and subseq *)


Context {T: eqType}.
Context {et: T}.

(*

Lemma subseq_injection_inj {T: eqType} {et: T} (s t: seq T) (Hsub: subseq s t) (i: nat) (ibnd: (i < size s)%N): injective (subseq_injection s t Hsub).
 *)

Fixpoint compute_mask (s t: seq T) {struct t}: bitseq :=
  if s is a :: l then
    if t is a' :: l' then
      if (a == a') then (true)::(compute_mask l l') else (false)::(compute_mask (a::l) l')
    else [::]
  else nseq (size t) (false).

Lemma compute_mask0 (t: seq T): compute_mask [::] t = nseq (size t) (false).
Proof.
  rewrite /compute_mask.
  case: t => //.
Qed.

Lemma compute_0mask (s: seq T): compute_mask s [::] = [::].
Proof. rewrite /compute_mask /=; case s => //.
Qed.
       
Lemma compute_mask_cons (l l': seq T) (a a': T) :
  compute_mask (a::l) (a'::l') = (a == a')%B::(compute_mask (if (a == a') then l else a::l) l').
Proof.
  rewrite /compute_mask; case: (a == a')%B => //.
Qed.

Lemma size_compute_mask (s t : seq T):
 size (compute_mask s t) = size t.
Proof.
  move: s.
  elim: t => [| a l IH] s.
  + by rewrite compute_0mask /=.
  case: s => [| a' l'].
  + by rewrite compute_mask0 size_nseq.
  rewrite compute_mask_cons /=; apply/eqP; rewrite eqSS.
  by rewrite (IH (if a' == a then l' else a' :: l')).
Qed.
  
Lemma compute_mask_correct (s t : seq T) (Hsub: subseq s t):
  mask (compute_mask s t) t = s.
Proof.
  move: s Hsub.
  elim: t => [| a' l' IH] s Hsub.
  + by rewrite compute_0mask; rewrite subseq0 in Hsub; symmetry; apply/eqP.
  case: s Hsub => [|a l] Hsub.
  + by rewrite compute_mask0 mask_false.
  rewrite compute_mask_cons.
  case eqaa': (a == a')%B; move/eqP in eqaa'.
  rewrite  !eqaa'; rewrite eqaa' in Hsub.
  rewrite mask_cons /=.
  change (a'::l) with ([:: a'] ++ l) in Hsub.
  change (a'::l') with ([:: a'] ++ l') in Hsub.
  rewrite subseq_cat2l in Hsub.
  by move: (IH l Hsub) => ->.
  rewrite mask_cons /=.
  move/eqP: eqaa' => /negbTE diffaa'.
  rewrite /= diffaa' in Hsub.
  by move: (IH (a::l) Hsub) => ->.
Qed.

Definition mask_index (m : bitseq) (i : nat) : nat :=
  nth (size m) [seq j <- iota 0 (size m) | nth false m j] i.

Lemma mask_eq {A B: eqType} (m1 m2: bitseq) (t : seq A) (l: seq B) (huniq: uniq t) (eqmask : mask m1 t = mask m2 t) (eqsz: size l = size t):
  mask m1 l = mask m2 l.
Proof.
  move: l m2 t huniq eqmask eqsz.
  elim: m1 => [l m2 t huniq eqmask eqsz |b s1 IH1].
  + rewrite mask0s in eqmask; rewrite mask0s.
    elim: m2 t l eqsz eqmask huniq  => [//| b' s2 IH2] t l eqsz.
    case: b'.
    - case: l eqsz IH2 => [|a l'] eqsz IH2.
      + rewrite /= in eqsz; symmetry in eqsz; move/size0nil in eqsz.
        by rewrite !eqsz.
      + case: t eqsz => [//|a' t'] eqsz.
        rewrite /= in eqsz; case: eqsz => eqsz.
        by rewrite mask_cons /=.
    - case: l eqsz IH2 => [|a l'] eqsz IH2.
      + by done.
      + case: t eqsz => [//|a' t'] eqsz.
        rewrite /= in eqsz; case: eqsz => eqsz.
        rewrite mask_cons /= => masknil /andP [_ huniq].
        by rewrite (IH2 t' l' eqsz).
  + move => l m2; elim: m2 l => [|b' s2 IH2] l t eqmask eqsz.
    - case: t eqmask eqsz => [|a' t'] huniq eqmask.
      + by rewrite /=; move/size0nil => ->.
      rewrite mask_cons mask0s in eqmask.
      case: b eqmask.
      + by done.
      rewrite /=; case: l => [//|a l'].
      move => eqmask eqsz.
      rewrite mask_cons /=; rewrite /= in eqsz; case: eqsz => eqsz.
      rewrite /= in huniq; move/andP: huniq => [_ huniq'].
      by rewrite (IH1 l' [::] t' _ eqmask eqsz).
    - case: t eqmask eqsz => [|a' t'].
      + by rewrite /= => _ _; move/size0nil => ->.
      case: b IH2.
      case: b' => IH2 huniq.
      + rewrite !mask_cons /= => eqmask; case: eqmask => eqmask.
        case: l => [| a l'].
        - by done.
        - rewrite /= => eqsz; case: eqsz => eqsz.
          rewrite /= in huniq; move/andP: huniq => [_ huniq'].
          by rewrite (IH1 l' s2 t' _ eqmask eqsz).
      + rewrite !mask_cons /=.
        rewrite /= in huniq; move/andP: huniq => [Hnotin Huniq'].
        move => eqmask; have ain: a' \in t'.
          apply: mem_mask.
          Unshelve.
          4: exact: s2.
          by rewrite -eqmask mem_head.
          by rewrite ain /= in Hnotin.
      + case b' => IH2 huniq.
        rewrite !mask_cons /=.
        rewrite /= in huniq; move/andP: huniq => [Hnotin Huniq'].
        move => eqmask; have ain: a' \in t'.
          apply: mem_mask.
          Unshelve.
          4: exact: s1.
          by rewrite eqmask mem_head.
          by rewrite ain /= in Hnotin.
      + rewrite !mask_cons /= => eqmask.
        case: l => [//|a l'] eqsz.
        rewrite /= in eqsz; case: eqsz => eqsz.
        rewrite !mask_cons /=; rewrite /= in huniq; move/andP: huniq => [_ huniq'].
        by rewrite (IH1 l' s2 t' _ eqmask eqsz).
Qed.
        
        
Lemma nth_mask (t: seq T) (m: bitseq) (j: nat): nth et t (nth (size t) (mask m (iota 0 (size t))) j) = nth et (mask m t) j.
Proof.
  move: (@resize_mask nat m (iota 0 (size t))) => [m' eqszm' eqmask].

  have ->: mask m t = mask m' t.
    rewrite (mask_eq m m' (iota 0 (size t)) t) //.
    + by apply: iota_uniq.
    + by rewrite size_iota.

  rewrite {}eqmask.
  rewrite size_iota in eqszm'.
  move: t j eqszm'.
  elim: m' => [| b l IH] t j eqszm.
  + by rewrite !mask0s nth_nil nth_default // nth_nil.
  case: t eqszm => [| a' l'] eqszm.
  + by rewrite /= !nth_nil.
  rewrite /=.
  case: j => [|i].
  + case: b eqszm.
  - by rewrite /=.
  - move => eqszm; rewrite /= in eqszm; case: eqszm => eqszm;  case: (posnP (size (mask l (iota 1 (size l'))))) => [Heq | Hlt].
    + rewrite size_mask in Heq.
      have nhas : ~~ (has id l).
      by rewrite has_count ltnNge negbK Heq.
      move/hasPn in nhas.
      have eql : l = nseq (size l) false.
        apply: (eq_from_nth).
        Unshelve.
        7: exact: false.
        + by rewrite size_nseq.
        + move => k kbnd.
          rewrite nth_nseq ifT //.
          have kinl: (nth false l k) \in l.
           apply/nthP.
           by exists(k) => //.
          apply/negP.
          apply/negP.
          by rewrite nhas.
        rewrite eql !mask_false !nth_nil nth_default //.
        by rewrite size_iota eqszm.
          
        
     + change (iota 1 (size l')) with (iota (1 + 0) (size l')).

       rewrite iotaDl -map_mask (nth_map (size l')).
       rewrite addnC addn1 -nth_behead /=.
       by apply: (IH l' 0).
       rewrite size_mask; rewrite size_mask // in Hlt.
       1-3: by rewrite size_iota.
  + case: b eqszm; rewrite /=; case => eqszm.
    + change (iota 1 (size l')) with (iota (1 + 0) (size l')).

      case: (ltnP i (size (mask l l'))) => [Hlt | Hleq].
      + rewrite iotaDl -map_mask (nth_map (size l')).
        rewrite addnC addn1 -nth_behead /=.
        by apply: (IH l' i).
        rewrite size_mask in Hlt.
        rewrite size_mask //.
        by rewrite size_iota eqszm.
        by done.
      + rewrite size_mask in Hleq.
        rewrite !nth_default //.
        by rewrite size_mask.
        + rewrite size_mask //.
          by rewrite size_iota eqszm.
        by done.
    + change (iota 1 (size l')) with (iota (1 + 0) (size l')).

      case: (ltnP (i.+1) (size (mask l l'))) => [Hlt | Hleq].
      + rewrite iotaDl -map_mask (nth_map (size l')).
        rewrite addnC addn1 -nth_behead /=.
        by apply: (IH l' (i.+1)).
        rewrite size_mask in Hlt.
        rewrite size_mask //.
        by rewrite size_iota eqszm.
        by done.
      + rewrite size_mask in Hleq.
        rewrite !nth_default //.
        by rewrite size_mask.
        + rewrite size_mask //.
          by rewrite size_iota eqszm.
        by done.
Qed.

    
Lemma eq_size_count m:
  count id m = size [seq j <- iota 0 (size m) | nth false m j].
Proof.
  by rewrite -{1}[m](mkseq_nth false) count_map size_filter /=.
Qed.  

Lemma mask_index_inj m i j : (i < count id m)%N -> (j < count id m)%N -> mask_index m i = mask_index m j -> i = j.
Proof.
  move => ibnd jbnd; rewrite /mask_index=> eqf.
  pose positions := [seq j <- iota 0 (size m) | nth false m j].

  have Hsorted : sorted (fun x y => (x < y)%N) positions.
    apply: sorted_filter => //; first by apply: ltn_trans.
    by apply: iota_ltn_sorted.

  have eqsz : count id m = size positions.
    by rewrite /positions; apply eq_size_count.

  rewrite eqsz in ibnd jbnd.

  apply: anti_leq; apply/andP; split.
  - rewrite leqNgt; apply/negP => H.
    by move: (sorted_ltn_nth ltn_trans (size m) Hsorted j i jbnd ibnd H); rewrite eqf ltnn.
  - rewrite leqNgt; apply/negP => H.
    by move: (sorted_ltn_nth ltn_trans (size m) Hsorted i j ibnd jbnd H); rewrite eqf ltnn.
Qed.

Section SubSeqInjection.

Definition subseq_injection (s t: seq T) (Hsub: subseq s t):=
  mask_index (compute_mask s t).

Variable s t : seq T.
Hypothesis Hsub: subseq s t.
Let subs_injection := subseq_injection s t Hsub.
  
Lemma injection_bnd (i: nat) (ibnd: (i < size s)%N): (subs_injection i < size t)%N.
Proof.
  pose m := (compute_mask s t).
  have eqm : s = mask m t.
  by rewrite /m; symmetry; apply: (compute_mask_correct s t Hsub).
  have eqsz : size t = size m by rewrite /m size_compute_mask.
  have eqszs: size s = count id m by rewrite eqm size_mask.

  rewrite /mask_index.
  pose l := [seq j <- iota 0 (size m) | nth false m j].
  pose z := nth (size m) l i.
  have ziniota: z \in iota 0 (size m).
   have: z \in l. 
     apply/nthP; exists(i).
     by rewrite /l -eq_size_count -eqszs.
     by rewrite /z.
   by rewrite /l mem_filter => /andP [zcond zin].

  move: ziniota.
  rewrite mem_iota add0n {1}eqsz => /andP [_ hlt].
  by rewrite /z /l in hlt.
Qed.

Lemma injection_correct (i: nat) (ibnd: (i < size s)%N): nth et s i = nth et t (subs_injection i).
Proof.
  pose m := (compute_mask s t).
  have eqm : s = mask m t.
  by rewrite /m; symmetry; apply: (compute_mask_correct s t Hsub).
  have eqsz : size t = size m by rewrite /m size_compute_mask.
  have eqszs: size s = count id m by rewrite eqm size_mask.

  rewrite /subs_injection /subseq_injection.

  rewrite /mask_index.
  pose l := [seq j <- iota 0 (size m) | nth false m j].
  pose z := nth (size m) l i.
  have ziniota: z \in iota 0 (size m).
   have: z \in l. 
     apply/nthP; exists(i).
     by rewrite /l -eq_size_count -eqszs.
     by rewrite /z.
   by rewrite /l mem_filter => /andP [zcond zin].

  rewrite /mask_index.
  rewrite {1}eqm /m filter_mask.
  by rewrite -nth_mask [[seq nth false (compute_mask s t) j | j <- iota 0 (size (compute_mask s t))]](mkseq_nth false) eqsz /=.
Qed.
                           
Lemma subseq_injection_inj:
  {in [pred i | (i < size s)%N] &, injective subs_injection}.
Proof.
  move => i j ibnd jbnd.

  have eqsz: count id (compute_mask s t) = size s.
    rewrite -{2}[s](compute_mask_correct s t Hsub) size_mask //.
    by apply: size_compute_mask.
    
  rewrite /subs_injection /subseq_injection.
  apply: mask_index_inj.
  by rewrite eqsz.
  by rewrite eqsz.
Qed.

End SubSeqInjection.

Lemma subseq_mapP {T1 T2: eqType} (f: T1 -> T2) (t: seq T1) (s: seq T2):
  (subseq s (map f t)) <-> exists s', (subseq s' t) /\ s = map f s'.
Proof.
  split => [Hsubseq | Hexists].
  + move/subseqP: Hsubseq => [m eqsz eqs].
    exists (mask m t); split.
    - by rewrite size_map in eqsz; apply/subseqP; exists m.
    - by rewrite map_mask.
  + case: Hexists => s' [Hsub eqs].
    by  move/subseqP: Hsub => [m eqsz eqs']; rewrite eqs' map_mask in eqs; apply/subseqP; exists m; first by rewrite size_map.
Qed.

Lemma infix_mapP {T1 T2: eqType} (f: T1 -> T2) (t: seq T1) (s: seq T2):
  (infix s (map f t)) <-> exists s', (infix s' t) /\ s = map f s'.
Proof.
  split => [Hinfix | Hexists].
  + move/infixP: Hinfix => [p [q Q]].
    pose p' := take (size p) t.
    pose s' := take (size s) (drop (size p) t).
    pose q' := drop (size s) (drop (size p) t).

    exists s'; split.
    + apply/infixP; exists p'; exists q'.
      + rewrite /p' /q' /s'.
        by rewrite cat_take_drop cat_take_drop.
      + rewrite /s' map_take map_drop Q drop_cat ifF; last by apply:ltnn.
        rewrite subnn drop0 take_cat ifF; last by apply: ltnn.
        by rewrite subnn take0 cats0.
  + case: Hexists => s' [Hinfix eqs].
    apply/infixP; move/infixP: Hinfix => [p' [q' Q]].
    exists (map f p'); exists (map f q').
    by rewrite eqs -!map_cat -Q.
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

Lemma enumerate_in (l: seq A) (j : nat) (jbnd: (j < size l)%N) (x: A):
  nth ea l j = x -> (j, x) \in enumerate l.
Proof.
  move => H.
  apply/(nthP (0, ea)).
  exists (j); first by rewrite size_enumerate; apply: jbnd.
  rewrite /enumerate.
  rewrite nth_zip /=.
  rewrite H nth_iota.
  + by rewrite addnC addn0.
  + by assumption.
  + by rewrite size_iota.
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
