(** * Well founded relations                                                  *)
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
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma wf_f T1 T2 (R : T1 -> T1 -> Prop) (S : T2 -> T2 -> Prop) (f : T1 -> T2) :
  (forall x y : T1, R x y -> S (f x) (f y)) -> well_founded S -> well_founded R.
Proof.
move=> RS WfS x.
move: {2}(f x) (erefl (f x)) => a; move: a x.
apply: (well_founded_induction_type WfS) => a IHa x Hx.
by apply: Acc_intro => y {}/RS; rewrite Hx => /IHa; apply.
Qed.

Lemma wf_impl (T : Type) (R : T -> T -> Prop) (S : T -> T -> Prop) :
  (forall x y : T, R x y -> S x y) -> well_founded S -> well_founded R.
Proof. exact: wf_f. Qed.

Lemma wf_ltnat : well_founded (fun n m => n < m).
Proof. by elim/ltn_ind => n IHn; apply: Acc_intro => m /IHn. Qed.
