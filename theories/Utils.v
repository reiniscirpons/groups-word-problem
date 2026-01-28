From mathcomp Require Import ssreflect ssrfun ssrbool ssrint ssrnat.
From mathcomp Require Import eqtype seq fintype all_algebra.
From mathcomp Require Import ring lra zify.
From Stdlib Require Import Program.Equality.

Inductive in_list {T: Type}: T -> seq T -> Type :=
  | in_head a l : in_list a (a::l)
  | in_tail a b l : in_list a l -> in_list a (b::l).

Inductive or_in_type (P Q: Type) : Type :=
  | oit_left: P -> or_in_type P Q
  | oit_right: Q -> or_in_type P Q.

Lemma in_list_inv {T: Type} (x a: T) (l: seq T):
  in_list x (a::l) -> or_in_type (x = a) (in_list x l).
Proof. move=> H; dependent induction H; do [exact: oit_left|exact: oit_right]. Qed.
Arguments in_list_inv {_ _ _ _}.

Lemma nth_in_list {T: Type} (d: T) (l: seq T) i:
  (i < size l)%N -> in_list (nth d l i) l.
Proof.
elim: l i => [//|a l /= IH].
case=> [_|i ? /=]; first exact: in_head.
apply /in_tail /IH; lia.
Qed.

