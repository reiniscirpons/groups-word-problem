From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype fintype tuple.

From GWP Require Import Presentation EquivalenceAlgebra Equivalence.

(* HNN extension to characterize a subgroup *)
Section HNNSubgroup.
Variable G: group.
Variable genH: seq G.
Let H := finGeneratedSubgroup genH.

Definition HNNSG_extension_presentation: invertiblePresentationType.
Admitted.

Let HNNSG_extension: group := presented HNNSG_extension_presentation.

Definition HNNSG_extension_base := G.

Definition HNNSG_injection: injectiveMorphism HNNSG_extension_base HNNSG_extension.
Admitted.
HB.instance Definition _ := isSubgroup.Build HNNSG_extension HNNSG_extension_base HNNSG_injection.

Definition HNNSG_t: HNNSG_extension.
Admitted.

Lemma HNNSG_subgroup_characterization: forall x: G,
  x \insubgroup H
    ->
  (subgroup_inj (s:=HNNSG_extension_base) x) @ HNNSG_t == HNNSG_t @ (subgroup_inj (s:=HNNSG_extension_base) x).
Admitted.

Lemma HNNSG_subgroup_characterization': forall x: G,
  (subgroup_inj (s:=HNNSG_extension_base) x) @ HNNSG_t == HNNSG_t @ (subgroup_inj (s:=HNNSG_extension_base) x)
    ->
  x \insubgroup H.
Admitted.

End HNNSubgroup.

Arguments HNNSG_extension_presentation {G}.
Arguments HNNSG_t {G}.
Arguments HNNSG_subgroup_characterization {G}.

(* HNN extension to characterize n local morphisms *)
Section HNNIsos.

Variable G: group.
Variable isos: seq (local_morphism G).
Let isos_count := size isos.

Definition HNNI_nth_iso (i: 'I_isos_count): local_morphism G :=
  nth (morphism_to_local_morphism (identity_morphism G)) isos i.

Definition HNNI_extension: group.
Admitted.

Definition HNNI_extension_base := G.

Definition HNNI_injection: injectiveMorphism HNNI_extension_base HNNI_extension.
Admitted.
HB.instance Definition _ := isSubgroup.Build HNNI_extension HNNI_extension_base HNNI_injection.

Definition HNNI_ts: isos_count.-tuple HNNI_extension.
Admitted.

Lemma iso_representation: forall i: 'I_isos_count,
  let t := tnth HNNI_ts i in
  let lm := HNNI_nth_iso i in
  forall (x: lm.(lm_source_subgroup)), subgroup_inj (subgroup_inj (lm x) : HNNI_extension_base) == t @ (subgroup_inj (subgroup_inj x : HNNI_extension_base)) @ (inv t).
Admitted.

Section HNNStableSubgroup.
Variable K: subgroup G.

Hypothesis K_invariance: forall i: 'I_isos_count, is_subgroup_stable (HNNI_nth_iso i) K.

Definition HNNI_subgroup_ts_extension : HNNI_extension -> Prop.
Admitted.

Lemma HNNsgte_law: forall x y : HNNI_extension,
  HNNI_subgroup_ts_extension x ->
  HNNI_subgroup_ts_extension y -> HNNI_subgroup_ts_extension (x @ y).
Admitted.

Lemma HNNsgte_neutral: HNNI_subgroup_ts_extension e.
Admitted.

Lemma HNNsgte_inv: forall x : HNNI_extension,
  HNNI_subgroup_ts_extension x -> HNNI_subgroup_ts_extension (inv x).
Admitted.

HB.instance Definition _ := isSubgroupCharacterizer.Build HNNI_extension HNNI_subgroup_ts_extension HNNsgte_law HNNsgte_neutral HNNsgte_inv.

Let K_extended := subgroup_by HNNI_subgroup_ts_extension.

(* <K, t1, ..., tn> \cap G = G *)
(* x \in G -> x \in <K, t1, ..., tn> *)
Lemma HNNI_stable_inter_G_is_G : forall (x: G),
  (subgroup_inj (x: HNNI_extension_base)) \insubgroup (K_extended: subgroup HNNI_extension).
Admitted.

End HNNStableSubgroup.
End HNNIsos.

Arguments HNNI_stable_inter_G_is_G {G} isos K.
Arguments HNNI_extension {G}.
Arguments HNNI_ts {G}.
