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

From GWP Require Import Utils Equivalence EquivalenceAlgebra Presentation F2 GeneratedSubgroup sizelexi well_founded preorder.

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


Section WordSplitting.

Context {Sigma: finType}.
Notation word := (FreeGroup Sigma).
Notation vec := (seq word).

Variable gens : vec.

Let U := [seq w | w <- gens] ++ [seq (inv w) | w <- gens].


Lemma prefix_size {T: eqType} (x y z: seq T) (prefxz: prefix x z) (prefyz: prefix y z) (sz: (size x <= size y)%N):
  prefix x y.
Proof.
  apply/prefixP.
  move/prefixP: prefxz => [s eqs].
  move/prefixP: prefyz => [s' eqs'].
  have prefcat: prefix x (y ++ s').
    by apply/prefixP; exists (s); rewrite -eqs.
  


Fixpoint lprefix (x y : FreeGroup Sigma) := match x, y with
  | [::], _ => [::]
  | _, [::] => [::]
  | a::t, b::t' =>
    if (a == b) then
      a::(lprefix t t')
    else [::]
  end.

Lemma lprefix_neutral (a a': sigma (FGP Sigma)) (diff: a <> a') (l l': seq _):
  lprefix (a::l) (a'::l') = [::].
Proof.
  rewrite /lprefix /=.
  rewrite ifF //.
  by apply/eqP.
Qed.

Lemma lprefix0nil (x: FreeGroup Sigma):
  lprefix x [::] = [::].
Proof.
  rewrite /lprefix /=.
  case: x => //.
Qed.

Lemma lprefix_cons (a: sigma (FGP Sigma)) (l l': seq _):
  lprefix (a::l) (a::l') = a::(lprefix l l').
Proof.
  rewrite {1}/lprefix /=.
  rewrite ifT //.
Qed.

Lemma lprefix_cat (v t t': FreeGroup Sigma):
  lprefix (v ++ t) (v ++ t') = v ++ (lprefix t t').
Proof.
  elim: v => [|a l IH].
  - by rewrite !cat0s.
  - by rewrite [lprefix ((a :: l) ++ t) ((a :: l) ++ t')]lprefix_cons cat_cons IH.
Qed.

Definition lKprefix (x y : FreeGroup Sigma) :=
  lprefix (inv x) y.

Lemma lprefix_correct_right (x y: FreeGroup Sigma):
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

Lemma lprefixC (x y : FreeGroup Sigma):
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

Lemma lprefix_correct_left (x y: FreeGroup Sigma):
  prefix (lprefix x y) x.
Proof.
  by rewrite lprefixC lprefix_correct_right.
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

Lemma inv_cons (a : sigma (FGP Sigma)) (t : FreeGroup Sigma):
  inv (a :: t :> FreeGroup Sigma) = rcons (inv t) (invl a).
Proof.
  by rewrite /inv /= /inv_word map_rev map_cons rev_cons map_rev.
Qed. 


Lemma lKprefix_split (x y: FreeGroup Sigma) (frx: freely_reduced x) (fry: freely_reduced y):
  exists (w w': FreeGroup Sigma), (
    x == w ++ inv (lKprefix x y :> FreeGroup Sigma) /\
    y == (lKprefix x y) ++ w' /\
    freely_reduced (w ++ w')
  ).
Proof.
  have prefixx: prefix (lKprefix x y) (inv x).
    by rewrite /lKprefix lprefix_correct_left.
  have prefixy: prefix (lKprefix x y) y.
    by rewrite /lKprefix lprefix_correct_right.
  move/prefixP: prefixx => [s' eqs'].
  move/prefixP: prefixy => [sy' eqsy'].
  have approx: (x == inv (lKprefix x y ++ s' :> FreeGroup Sigma)).
    rewrite -eqs'.
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

Definition lKprefix_all (y: FreeGroup Sigma) :=
  head [::] (
    sort (fun a b => (size a <= size b)%N) (
      filter (fun a => a != y) (
        map (fun x => lKprefix x y) U
      )
    )
  ).

Lemma lKprefix_all_correct (y: FreeGroup Sigma):
    forall x, (x \in U) -> prefix (lKprefix x y) (lKprefix_all y).



End WordSplitting.


Section Nielsen_Axiom.

Context {Sigma: finType}.
Notation word := (FreeGroup Sigma).
Notation vec := (seq word).

Variable gens : vec.

Let U := [seq w | w <- gens] ++ [seq (inv w) | w <- gens].

Let F := generatedSubgroup gens. 

Definition bound (x: nat) := (x < size U)%N.
Definition non_trivial (x y : (FreeGroup Sigma)) := FreeGroup_norm (x @ y) <> e.
Local Notation nthgen := (nth e U).
Definition sz (w: (FreeGroup Sigma)) := (size (FreeGroup_norm w)).

Hypothesis N0: forall k, (bound k) -> FreeGroup_norm (nth e gens k) <> e.
Hypothesis N1_left: forall n m, (bound n) -> (bound m) -> (non_trivial (nthgen n) (nthgen m)) ->
  (sz (nthgen n @ nthgen m) >= sz(nthgen n))%N.
Hypothesis N1_right: forall n m, (bound n) -> (bound m) -> (non_trivial (nthgen n) (nthgen m)) ->
  (sz(nthgen n @ nthgen m) >= sz(nthgen m))%N.

Hypothesis N2 : forall k l m, (bound k) -> (bound l) -> (bound m) ->
  (non_trivial (nthgen k) (nthgen l)) -> (non_trivial (nthgen l) (nthgen m)) ->
  (sz(nthgen k @ nthgen l @ nthgen m) > sz(nthgen k) +sz(nthgen m) - sz(nthgen l))%N.

Variable x y : FreeGroup Sigma.
Hypothesis igsx: in_generated_subgroup gens x.
Hypothesis igsy: in_generated_subgroup gens y.

End Nielsen_Axiom.

(* ############################################################################################

Create a function f : x y -> a decomposition xa xb ya yb such that x @ y =reduc xa @ yb and
x =reduc xa @ xb y =reduc ya @ yb with proof that it is indeed the case

Lemma stating that size w @ w' = size w + size w' is freely reduced (check, may already exist)
Lemmas stating that if t = x ++ y, x <= |t|/2, |x| < |y| and y > (|t|+1)/2 are equivalent.

Combine that into a proof that if x and y satisfy N1, then |xa| > |t|/2 (and same for y).

Create a function computing the maximum all xb for a given x (by taking the longest)
Lemma to show that every xb is a suffix of this one.

Same for prefixes.
Lemma stating that if N1 and N2 are satisfied, then the max suffix and max prefix are both < |t|/2
Lemma stating that if prefix and suffix are < |t|/2, then the word has a non trivial trichotomy

Lemma stating that if N0 N1 N2 are satisfied, then the length of a reduced word is at least as large
as the number of terms in the product (write that with a fold, proof by induction I think).

Lemma stating that |x@x@y|>|y|.

############################################################################################ *)




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

Definition cmp_ordered_word := seqcmp (InverseAlphabet_display) (sigma (FGP Sigma)) FreeGroup_norm.
HB.instance Definition _ :=
  Order.Preorder.copy (FreeGroup Sigma) (cmp_ordered_word).


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
  Admitted.


Definition vec_lexico_ltP (gens gens': vec): Prop := (gens < gens')%O.

(* Note(mathis): The weird function structure inside the match is here to provide a proof of ix <> iy *)
Program Fixpoint second_reduce (gens: vec) {wf vec_lexico_ltP gens} :=
  match second_reduce_step gens as l return (second_reduce_step gens = l -> _) with
    | [::] => fun _ => gens
    | (k, ix, iy, xy)::t => fun Heq =>
      let h := second_reduce_step_neq gens k ix iy xy t Heq in
      let gens' :=
        if k==0 then t2 gens ix iy h
        else if k==1 then t1 (t2 (t1 gens iy) ix iy h) iy
        else if k==2 then t2 (t1 gens ix) ix iy h
        else if k==3 then t1 (t2 (t1 (t1 gens iy) ix) ix iy h) iy
        else gens
      in
      second_reduce gens'
  end erefl.


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
    by rewrite Heq mem_head.
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

End NielsenConstructionCorrection.