From elpi.apps Require Import coercion.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool Morphisms.
From mathcomp Require Import ssrnat seq monoid.
From GWP Require Import Equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "*%sg" (at level 0).

Local Open Scope setoid_group_scope.

HB.mixin Record Setoid_Magma_isSetoidMagma M of Setoid M & Magma M := {
  mul_extl: forall x y z,
    @equiv M y z -> @equiv M (@mul M x y) (@mul M x z);
  mul_extr: forall x y z,
    @equiv M y z -> @equiv M (@mul M y x) (@mul M z x);
}.

#[short(type="setoidMagmaType")]
HB.structure Definition SetoidMagma :=
  {G of Setoid_Magma_isSetoidMagma G & Setoid G & Magma G}.

Bind Scope setoid_group_scope with SetoidMagma.sort.

HB.mixin Record isSetoidMagma M & Setoid M := {
  mul: M -> M -> M;
  mul_extl: forall x y z,
    equiv y z -> equiv (mul x y) (mul x z);
  mul_extr: forall x y z,
    equiv y z -> equiv (mul y x) (mul z x);
}.

HB.builders Context M & isSetoidMagma M.
  HB.instance Definition _ :=
    hasMul.Build M mul.
  HB.instance Definition _ :=
    Setoid_Magma_isSetoidMagma.Build M mul_extl mul_extr.
HB.end.

Local Notation "*%sg" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : setoid_group_scope.


Section SetoidMagmaTheory.

Variable M : setoidMagmaType.
Implicit Types x y : M.

Section ClosedSets.

Variable S : M -> Prop.

Definition muls_closed := forall u v, S u -> S v -> (S (u * v)).

End ClosedSets.

Global Instance : Proper (equiv ==> equiv ==> equiv) (mul : M -> M -> M).
Proof.
move=> a b Hab u v Huv.
transitivity (a * v).
- by exact: mul_extl.
- by exact: mul_extr.
Qed.

End SetoidMagmaTheory.



HB.mixin Record SetoidMagma_isSetoidSemigroup M & SetoidMagma M := {
  mulsA: forall (x y z: M),
    x * (y * z) \approx (x * y) * z;
}.

#[short(type="setoidSemigroupType")]
HB.structure Definition SetoidSemigroup :=
  {M of SetoidMagma_isSetoidSemigroup M & SetoidMagma M}.

Bind Scope setoid_group_scope with SetoidSemigroup.sort.

#[short(type="baseSetoidUMagmaType")]
HB.structure Definition BaseSetoidUMagma := {G of hasOne G & SetoidMagma G}.

Bind Scope setoid_group_scope with BaseSetoidUMagma.sort.

Local Notation "1" := (@one _): setoid_group_scope.
Local Notation "s `_ i" := (nth 1 s i): setoid_group_scope.

Definition natexp (M: baseSetoidUMagmaType) (x: M) n: M := iterop n *%sg x 1.
Arguments natexp: simpl never.

Local Notation "x ^+ n" := (natexp x n) : setoid_group_scope.

Section baseSetoidUMagmaTheory.

Variable M : baseSetoidUMagmaType.
Implicit Types x : M.

Lemma expsnE (x: M) n : x ^+ n = iterop n (@mul M) x 1.
Proof. done. Qed.

Lemma exps0 (x: M) : x ^+ 0 = 1.
Proof. done. Qed.

Lemma exps1 (x: M) : x ^+ 1 = x.
Proof. done. Qed.

Lemma exps2 (x: M) : x ^+ 2 = x * x.
Proof. done. Qed.

Lemma expsSS (x: M) n : x ^+ n.+2 = x * x ^+ n.+1.
Proof. done. Qed.

Lemma expsb (x: M) (b : bool) : x ^+ b = (if b then x else 1).
Proof. by case: b. Qed.

Section ClosedPredicates.

Variable S: M -> Prop.

Definition umagma_closed := (S 1) /\ muls_closed S.

End ClosedPredicates.

End baseSetoidUMagmaTheory.

HB.mixin Record BaseSetoidUMagma_isSetoidUMagma M & BaseSetoidUMagma M := {
  mul1s: forall (x: M),
    1 * x \approx x;
  muls1: forall (x: M),
    x * 1 \approx x;
}.

HB.factory Record SetoidMagma_isSetoidUMagma M & SetoidMagma M := {
  one : M;
  mul1s: forall (x: M),
    one * x \approx x;
  muls1: forall (x: M),
    x * one \approx x;
}.

HB.builders Context M & SetoidMagma_isSetoidUMagma M.
  HB.instance Definition _ :=
    hasOne.Build M one.
  #[warning="-HB.no-new-instance"]
  HB.instance Definition _ :=
    BaseSetoidUMagma_isSetoidUMagma.Build M mul1s muls1.
HB.end.

#[short(type="setoidUMagmaType")]
HB.structure Definition SetoidUMagma :=
  {M of SetoidMagma_isSetoidUMagma M & SetoidMagma M}.

Bind Scope setoid_group_scope with SetoidUMagma.sort.

Section SetoidUMagmaTheory.

Variable M : setoidUMagmaType.
Implicit Types x y : M.

Lemma expsS (x: M) n : x ^+ n.+1 \approx (x * x ^+ n)%sg.
Proof. by case: n => //=; rewrite muls1. Qed.

Lemma exps1n n : 1 ^+ n \approx 1 :> M.
Proof. by elim: n => // n IHn; rewrite expsS mul1s. Qed.

End SetoidUMagmaTheory.

#[short(type="setoidMonoidType")]
HB.structure Definition SetoidMonoid :=
  {M of SetoidMagma_isSetoidUMagma M & SetoidSemigroup M}.

HB.factory Record SetoidSemigroup_isSetoidMonoid M & SetoidSemigroup M := {
  one : M;
  mul1s: forall (x: M),
    one * x \approx x;
  muls1: forall (x: M),
    x * one \approx x;
}.

HB.builders Context M & SetoidSemigroup_isSetoidMonoid M.

  HB.instance Definition _ :=
    SetoidMagma_isSetoidUMagma.Build M mul1s muls1.

HB.end.

HB.factory Record SetoidUMagma_isSetoidMonoid M & SetoidUMagma M := {
  mulsA: forall (x y z: M),
    x * (y * z) \approx (x * y) * z;
}.

HB.builders Context M & SetoidUMagma_isSetoidMonoid M.

  HB.instance Definition _ :=
    SetoidMagma_isSetoidSemigroup.Build M mulsA.

HB.end.

HB.factory Record isSetoidMonoid M & SetoidMagma M := {
  one : M;
  mulsA: forall (x y z: M),
    x * (y * z) \approx (x * y) * z;
  mul1s: forall (x: M),
    one * x \approx x;
  muls1: forall (x: M),
    x * one \approx x;
}.

HB.builders Context M & isSetoidMonoid M.

  HB.instance Definition _ :=
    SetoidMagma_isSetoidSemigroup.Build M mulsA.
  HB.instance Definition _ :=
    SetoidMagma_isSetoidUMagma.Build M mul1s muls1.

HB.end.

Bind Scope setoid_group_scope with SetoidMonoid.sort.

Section SetoidMonoidTheory.

Variable M : setoidMonoidType.
Implicit Types x y : M.

Lemma expsnDr (x: M) m n : x ^+ (m + n) \approx (x ^+ m * x ^+ n)%sg.
Proof.
elim: m => [|m IHm]; rewrite ?mul1s // addSn expsS.
(* TODO(reiniscirpons): Why can't it figure this one out without the
   X in ... match? *)
by rewrite [X in X * x ^+ n]expsS [X in x * X]IHm mulsA.
Qed.

Lemma expsSr x n : x ^+ n.+1 \approx x ^+ n * x.
Proof.
  by rewrite -addn1 expsnDr [X in _ * X]exps1.
Qed.


Lemma expsnA x m n : x ^+ (m * n) \approx x ^+ m ^+ n.
Proof.
by rewrite mulnC; elim: n => //= n IHn; rewrite expsS mulSn expsnDr [X in _ * X]IHn.
Qed.

Lemma expsnAC x m n : x ^+ m ^+ n \approx x ^+ n ^+ m.
Proof.
by rewrite -2!expsnA mulnC.
Qed.

Lemma iter_muls n x y : iter n ( *%sg x) y \approx x ^+ n * y.
Proof.
by elim: n => [|n IHn]; rewrite ?mul1s //= IHn [X in _ \approx X * y]expsS mulsA. Qed.

Lemma iter_muls_1 n x : iter n ( *%sg x) 1 \approx x ^+ n.
Proof.
by rewrite iter_muls muls1.
Qed.

Lemma expgMn x y n : commute x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.

(* TODO: commute stuff*)



End MonoidTheory.

Notation monoid_closed := umagma_closed.

HB.mixin Record hasInv G := {
  inv : G -> G
}.

#[short(type="baseGroupType")]
HB.structure Definition BaseGroup := {G of hasInv G & BaseUMagma G}.

Bind Scope group_scope with BaseGroup.sort.

Local Notation "x ^-1" := (inv x) : group_scope.
Local Notation "x / y" := (x * y^-1) : group_scope.
Local Notation "x ^- n" := ((x ^+ n)^-1) : group_scope.

Definition conjg (G : baseGroupType) (x y : G) := y^-1 * (x * y).
Local Notation "x ^ y" := (conjg x y) : group_scope.

Definition commg (G : baseGroupType) (x y : G) := x^-1 * (conjg x y).
Local Notation "[ ~ x1 , x2 , .. , xn ]" := (commg .. (commg x1 x2) .. xn)
  : group_scope.

Section ClosedPredicates.

Variable (G : baseGroupType) (S : {pred G}).

Definition invg_closed := {in S, forall u, u^-1 \in S}.
Definition divg_closed := {in S &, forall u v, u / v \in S}.
Definition group_closed := 1 \in S /\ divg_closed.

End ClosedPredicates.

HB.mixin Record Monoid_isStarMonoid G & BaseGroup G := {
  invgK : involutive (@inv G);
  invgM : {morph @inv G : x y / x * y >-> y * x}
}.

#[short(type="starMonoidType")]
HB.structure Definition StarMonoid :=
  { G of Monoid_isStarMonoid G & Monoid G & BaseGroup G }.

Prenex Implicits invgK.

Bind Scope group_scope with StarMonoid.sort.

HB.factory Record isStarMonoid G & Choice G := {
  mul : G -> G -> G;
  one : G;
  inv : G -> G;
  mulgA : associative mul;
  mul1g : left_id one mul;
  invgK : involutive inv;
  invgM : {morph inv : x y / mul x y >-> mul y x}
}.

HB.builders Context G & isStarMonoid G.

Lemma invg1 : inv one = one.
Proof.


Lemma mulg1 : right_id one mul.
Proof.

HB.instance Definition _ := isMonoid.Build G mulgA mul1g mulg1.
HB.instance Definition _ := hasInv.Build G inv.
HB.instance Definition _ := Monoid_isStarMonoid.Build G invgK invgM.

HB.end.

Section StarMonoidTheory.
Variable G : starMonoidType.
Implicit Types x y z : G.

Lemma invg_inj : injective (@inv G)
Proof.

Lemma invg1 : 1^-1 = 1 :> G.
Proof.

Lemma invgF x y : (x / y)^-1 = y / x.
Proof.

Lemma prodgV I r (P : pred I) (E : I -> G) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- rev r | P i) E i)^-1.
Proof.




Lemma eqg_inv x y : (x^-1 == y^-1) = (x == y).
Proof.

Lemma eqg_invLR x y : (x^-1 == y) = (x == y^-1).
Proof.

Lemma invg_eq1 x : (x^-1 == 1) = (x == 1).
Proof.

Lemma expVgn x n : x^-1 ^+ n = x ^- n.
Proof.

Lemma conjgE x y : x ^ y = y^-1 * (x * y)
Proof.

Lemma commgEl x y : [~ x, y] = x^-1 * x ^ y
Proof.

Lemma commgEr x y : [~ x, y] = y^-1 ^ x * y.
Proof.

End StarMonoidTheory.

Arguments invg_inj {G} [x1 x2].

HB.mixin Record StarMonoid_isGroup G & BaseGroup G := {
  mulVg : left_inverse one inv (@mul G);
}.

#[short(type="groupType")]
HB.structure Definition Group :=
  {G of StarMonoid_isGroup G & BaseGroup G & StarMonoid G}.

HB.factory Record Monoid_isGroup G & Monoid G & BaseGroup G := {
  mulVg : left_inverse one inv (@mul G);
  mulgV : right_inverse one inv (@mul G);
}.

HB.builders Context G & Monoid_isGroup G.

Fact invgK : involutive (@inv G).
Proof.

Fact mulKg : @left_loop G G inv *%g.
Proof.

Fact invgM : {morph inv : x y / x * y >-> y * x : G}.
Proof.



HB.instance Definition _ := Monoid_isStarMonoid.Build G invgK invgM.
HB.instance Definition _ := StarMonoid_isGroup.Build G mulVg.

HB.end.

HB.factory Record isGroup G & Choice G := {
  one : G;
  inv : G -> G;
  mul : G -> G -> G;
  mulgA : associative mul;
  mul1g : left_id one mul;
  mulg1 : right_id one mul;
  mulVg : left_inverse one inv mul;
  mulgV : right_inverse one inv mul
}.

HB.builders Context G & isGroup G.

HB.instance Definition _ := hasMul.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.
HB.instance Definition _ := Magma_isUMagma.Build G mul1g mulg1.
HB.instance Definition _ := hasInv.Build G inv.
HB.instance Definition _ := Monoid_isGroup.Build G mulVg mulgV.

HB.end.

Bind Scope group_scope with Group.sort.

Section GroupTheory.
Variable G : groupType.
Implicit Types x y : G.

Lemma mulgV : right_inverse one inv (@mul G).
Proof.
Definition divgg := mulgV.

Lemma mulKg : @left_loop G G (@inv G) *%g.
Proof.

Lemma mulVKg : @rev_left_loop G G (@inv G) *%g.
Proof.

Lemma mulgK : @right_loop G G (@inv G) *%g.
Proof.

Lemma mulgVK : @rev_right_loop G G (@inv G) *%g.
Proof.
Definition divgK := mulgVK.

Lemma mulgI : @right_injective G G G *%g.
Proof.

Lemma mulIg : @left_injective G G G *%g.
Proof.

Lemma divgI : @right_injective G G G (fun x y => x / y).
Proof.

Lemma divIg : @left_injective G G G (fun x y => x / y).
Proof.

Lemma divg1 x : x / 1 = x
Proof.

Lemma div1g x : 1 / x = x^-1
Proof.

Lemma divKg x y : commute x y -> x / (x / y) = y.
Proof.

Lemma mulgKA z x y : (x * z) / (y * z) = x / y.
Proof.

Lemma divgKA z x y : (x / z) * (z * y) = x * y.
Proof.

Lemma mulg1_eq x y : x * y = 1 -> x^-1 = y.
Proof.

Lemma divg1_eq x y : x / y = 1 -> x = y.
Proof.

Lemma divg_eq x y z : (x / z == y) = (x == y * z).
Proof.

Lemma divg_eq1 x y : (x / y == 1) = (x == y).
Proof.

Lemma mulg_eq1 x y : (x * y == 1) = (x == y^-1).
Proof.

Lemma commuteV x y : commute x y -> commute x y^-1.
Proof.

Lemma expgnFr x m n : n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.

Lemma expgnFl x y n : commute x y -> (x / y) ^+ n = x ^+ n / y ^+ n.
Proof.

Lemma conjgC x y : x * y = y * x ^ y.
Proof.

Lemma conjgCV x y : x * y = y ^ x^-1 * x.
Proof.

Lemma conjg1 x : x ^ 1 = x.
Proof.

Lemma conj1g x : 1 ^ x = 1.
Proof.

Lemma conjMg x y z : (x * y) ^ z = x ^ z * y ^ z.
Proof.

Lemma conjgM x y z : x ^ (y * z) = (x ^ y) ^ z.
Proof.

Lemma conjVg x y : x^-1 ^ y = (x ^ y)^-1.
Proof.

Lemma conjJg x y z : (x ^ y) ^ z = (x ^ z) ^ y ^ z.
Proof.

Lemma conjXg x y n : (x ^+ n) ^ y = (x ^ y) ^+ n.
Proof.

Lemma conjgK : @right_loop G G (@inv G) (@conjg G).
Proof.

Lemma conjgKV : @rev_right_loop G G (@inv G) (@conjg G).
Proof.

Lemma conjg_inj : @left_injective G G G (@conjg G).
Proof.

Lemma conjg_eq1 x y : (x ^ y == 1) = (x == 1).
Proof.

Lemma conjg_prod I r (P : pred I) (F : I -> G) z :
  (\prod_(i <- r | P i) F i) ^ z = \prod_(i <- r | P i) (F i ^ z).
Proof.


Lemma commgC x y : x * y = y * x * [~ x, y].
Proof.

Lemma commgCV x y : x * y = [~ x^-1, y^-1] * (y * x).
Proof.

Lemma conjRg x y z : [~ x, y] ^ z = [~ x ^ z, y ^ z].
Proof.

Lemma invgR x y : [~ x, y]^-1 = [~ y, x].
Proof.

Lemma commgP x y : reflect (commute x y) ([~ x, y] == 1).
Proof.

Lemma conjg_fix x y : (x ^ y == x) = ([~ x, y] == 1).
Proof.

Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1).
Proof.

Lemma commg1_sym x y : ([~ x, y] == 1) = ([~ y, x] == 1).
Proof.

Lemma commg1 x : [~ x, 1] = 1.
Proof.

Lemma comm1g x : [~ 1, x] = 1.
Proof.

Lemma commgg x : [~ x, x] = 1.
Proof.

Lemma commgXg x n : [~ x, x ^+ n] = 1.
Proof.

Lemma commgVg x : [~ x, x^-1] = 1.
Proof.

Lemma commgXVg x n : [~ x, x ^- n] = 1.
Proof.

Section ClosedPredicates.

Variable S : {pred G}.

Lemma group_closedV : group_closed S -> invg_closed S.
Proof.

Lemma group_closedM : group_closed S -> mulg_closed S.
Proof.



End ClosedPredicates.

End GroupTheory.

#[global] Hint Rewrite @mulg1 @mul1g invg1 @mulVg mulgV (@invgK) mulgK mulgVK
             @invgM @mulgA : gsimpl.

Ltac gsimpl := autorewrite with gsimpl; try done.

Definition gsimp := (@mulg1, @mul1g, (@invg1, @invgK), (@mulgV, @mulVg)).
Definition gnorm := (gsimp, (@mulgK, @mulgVK, (@mulgA, @invgM))).

Arguments mulgI [G].
Arguments mulIg [G].
Arguments conjg_inj {G} x [x1 x2].
Arguments commgP {G x y}.
Arguments conjg_fixP {G x y}.


HB.mixin Record isMultiplicative (G H : magmaType) (apply : G -> H) := {
  gmulfM : {morph apply : x y / x * y}
}.

HB.structure Definition Multiplicative (G H : magmaType) :=
  {f of isMultiplicative G H f}.

HB.mixin Record Multiplicative_isUMagmaMorphism (G H : baseUMagmaType)
  (f : G -> H) := {
  gmulf1 : f 1 = 1
}.

HB.structure Definition UMagmaMorphism (G H : baseUMagmaType) :=
  {f of Multiplicative_isUMagmaMorphism G H f & isMultiplicative G H f}.

Definition monoid_morphism (G H : baseUMagmaType) (f : G -> H) : Prop :=
   (f 1 = 1) * {morph f : x y / x * y}.

HB.factory Record isUMagmaMorphism (G H : baseUMagmaType) (f : G -> H) := {
  monoid_morphism_subproof : monoid_morphism f
}.

HB.builders Context G H apply & isUMagmaMorphism G H apply.
HB.instance Definition _ :=
  isMultiplicative.Build G H apply monoid_morphism_subproof.2.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build G H apply monoid_morphism_subproof.1.
HB.end.

HB.factory Record isGroupMorphism (G H : groupType) (f : G -> H) := {
  gmulfF : {morph f : x y / x / y}
}.

HB.builders Context G H apply & isGroupMorphism G H apply.

Local Lemma gmulf1 : apply 1 = 1.
Proof.

Local Lemma gmulfM : {morph apply : x y / x * y}.
Proof.



HB.instance Definition _ := isMultiplicative.Build G H apply gmulfM.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build G H apply gmulf1.

HB.end.

Module MultiplicativeExports.
Notation "{ 'multiplicative' U -> V }" :=
  (Multiplicative.type U%type V%type) : type_scope.
End MultiplicativeExports.
HB.export MultiplicativeExports.

#[non_forgetful_inheritance]
HB.instance Definition _ G H (f : UMagmaMorphism.type G H) :=
  UMagmaMorphism.on (Multiplicative.sort f).

Section LiftedMagma.
Variables (T : Type) (G : magmaType).
Definition mul_fun (f g : T -> G) x := f x * g x.

End LiftedMagma.
Section LiftedBaseUMagma.
Variables (T : Type) (G : baseUMagmaType).
Definition one_fun : T -> G := fun=> 1.

End LiftedBaseUMagma.

Local Notation "\1" := (one_fun _) : function_scope.
Local Notation "f \* g" := (mul_fun f g) : function_scope.
Arguments one_fun {_} G _ /.
Arguments mul_fun {_ _} f g _ /.

Section MorphismTheory.

Section Magma.
Variables (G H : magmaType) (f : {multiplicative G -> H}).

Lemma can2_gmulfM f' : cancel f f' -> cancel f' f -> {morph f' : x y / x * y}.
Proof.

Lemma gmulf_commute x y : commute x y -> commute (f x) (f y).
Proof.

End Magma.

Section UMagma.
Variables (G H : umagmaType) (f : UMagmaMorphism.type G H).

Lemma gmulf_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof.

Lemma can2_gmulf1 f' : cancel f f' -> cancel f' f -> f' 1 = 1.
Proof.

Lemma gmulfXn n : {morph f : x / x ^+ n}.
Proof.

Lemma gmulf_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof.

End UMagma.

Section Group.
Variables (G H : groupType) (f : UMagmaMorphism.type G H).

Lemma gmulfV : {morph f : x / x^-1}.
Proof.

Lemma gmulfF : {morph f : x y / x / y}.
Proof.

Lemma gmulf_inj : (forall x, f x = 1 -> x = 1) -> injective f.
Proof.

Lemma gmulfXVn n : {morph f : x / x ^- n}.
Proof.

Lemma gmulfJ : {morph f : x y / x ^ y}.
Proof.

Lemma gmulfR : {morph f : x y / [~ x, y]}.
Proof.
End Group.

Section MulFun.
Variables (G H K : magmaType).
Variables (f g : {multiplicative H -> K}) (h : {multiplicative G -> H}).

Fact idfun_gmulfM : {morph @idfun G : x y / x * y}.
Proof.
HB.instance Definition _ := isMultiplicative.Build G G idfun idfun_gmulfM.

Fact comp_gmulfM : {morph f \o h : x y / x * y}.
Proof.
HB.instance Definition _ := isMultiplicative.Build G K (f \o h) comp_gmulfM.
End MulFun.

Section Mul1Fun.
Variables (G : magmaType) (H : umagmaType).

Fact idfun_gmulf1 : idfun 1 = 1 :> H.
Proof.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build H H idfun idfun_gmulf1.

Fact one_fun_gmulfM : {morph @one_fun G H : x y / x * y}.
Proof.
HB.instance Definition _ :=
  isMultiplicative.Build G H (@one_fun G H) one_fun_gmulfM.
End Mul1Fun.

Section Mul11Fun.
Variables (G H K : umagmaType).
Variables (f g : UMagmaMorphism.type H K) (h : UMagmaMorphism.type G H).

Fact comp_gmulf1 : (f \o h) 1 = 1.
Proof.
#[warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build G K (f \o h) comp_gmulf1.

Fact one_fun_gmulf1 : @one_fun G H 1 = 1.
Proof.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build G H (@one_fun G H) one_fun_gmulf1.

Fact mul_fun_gmulf1 : (f \* g) 1 = 1.
Proof.

End Mul11Fun.
End MorphismTheory.


HB.mixin Record isMulClosed (G : magmaType) (S : {pred G}) := {
  gpredM : mulg_closed S
}.

HB.mixin Record isMul1Closed (G : baseUMagmaType) (S : {pred G}) := {
  gpred1 : 1 \in S
}.

HB.mixin Record isInvClosed (G : groupType) (S : {pred G}) := {
  gpredVr : invg_closed S
}.


#[short(type="mulgClosed")]
HB.structure Definition MulClosed G := {S of isMulClosed G S}.

#[short(type="umagmaClosed")]
HB.structure Definition UMagmaClosed G :=
  {S of isMul1Closed G S & isMulClosed G S}.

#[short(type="invgClosed")]
HB.structure Definition InvClosed G := {S of isInvClosed G S}.

#[short(type="groupClosed")]
HB.structure Definition GroupClosed G :=
  {S of isInvClosed G S & isMul1Closed G S & isMulClosed G S}.

Section UMagmaPred.
Variables (G : baseUMagmaType).

Section UMagma.
Variables S : umagmaClosed G.

Lemma gpred_prod I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \prod_(i <- r | P i) F i \in S.
Proof.

Lemma gpredXn n : {in S, forall u, u ^+ n \in S}.
Proof.


End UMagma.
End UMagmaPred.

Section GroupPred.
Variables (G : groupType).

Lemma gpredV (S : invgClosed G) : {mono (@inv G): u / u \in S}.
Proof.

Section Group.
Variables S : groupClosed G.

Lemma gpredF : {in S &, forall u v, u / v \in S}.
Proof.

Lemma gpredFC u v : (u / v \in S) = (v / u \in S).
Proof.

Lemma gpredXNn n: {in S, forall u, u ^- n \in S}.
Proof.

Lemma gpredMr x y : x \in S -> (y * x \in S) = (y \in S).
Proof.



Lemma gpredMl x y : x \in S -> (x * y \in S) = (y \in S).
Proof.



Lemma gpredFr x y : x \in S -> (y / x \in S) = (y \in S).
Proof.

Lemma gpredFl x y : x \in S -> (x / y \in S) = (y \in S).
Proof.

Lemma gpredJ x y : x \in S -> y \in S -> x ^ y \in S.
Proof.

Lemma gpredR x y : x \in S -> y \in S -> [~ x, y] \in S.
Proof.

End Group.
End GroupPred.

HB.mixin Record isSubMagma (G : magmaType) (S : pred G) H
    & SubType G S H & Magma H := {
  valM_subproof : {morph (val : H -> G) : x y / x * y}
}.

#[short(type="subMagmaType")]
HB.structure Definition SubMagma (G : magmaType) S :=
  { H of SubChoice G S H & Magma H & isSubMagma G S H }.

Section subMagma.
Context (G : magmaType) (S : pred G) (H : subMagmaType S).
Notation val := (val : H -> G).
HB.instance Definition _ := isMultiplicative.Build H G val valM_subproof.
Lemma valM : {morph val : x y / x * y}
Proof.
End subMagma.

HB.factory Record SubChoice_isSubMagma (G : magmaType) S H
    & SubChoice G S H := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context G S H & SubChoice_isSubMagma G S H.

HB.instance Definition _ := isMulClosed.Build G S mulg_closed_subproof.

Let inH v Sv : H := Sub v Sv.
Let mulH (u1 u2 : H) := inH (gpredM _ _ (valP u1) (valP u2)).

HB.instance Definition _ := hasMul.Build H mulH.

Lemma valM : {morph (val : H -> G) : x y / x * y}.
Proof.

HB.instance Definition _ := isSubMagma.Build G S H valM.

HB.end.

#[short(type="subSemigroupType")]
HB.structure Definition SubSemigroup (G : semigroupType) S :=
  { H of SubMagma G S H & Semigroup H}.

HB.factory Record SubChoice_isSubSemigroup (G : semigroupType) S H
    & SubChoice G S H := {
  mulg_closed_subproof : mulg_closed S
}.

HB.builders Context G S H & SubChoice_isSubSemigroup G S H.

HB.instance Definition _ :=
  SubChoice_isSubMagma.Build G S H mulg_closed_subproof.

Lemma mulgA : associative (@mul H).
Proof.

HB.instance Definition _ := isSemigroup.Build H mulgA.

HB.end.

HB.mixin Record isSubBaseUMagma (G : baseUMagmaType) (S : pred G) H
    & SubMagma G S H & BaseUMagma H := {
  val1_subproof : (val : H -> G) 1 = 1
}.

#[short(type="subBaseUMagmaType")]
HB.structure Definition SubBaseUMagma (G : umagmaType) S :=
  { H of SubMagma G S H & BaseUMagma H & isSubBaseUMagma G S H}.

#[short(type="subUMagmaType")]
HB.structure Definition SubUMagma (G : umagmaType) S :=
  { H of SubMagma G S H & UMagma H & isSubBaseUMagma G S H}.

Section subUMagma.
Context (G : umagmaType) (S : pred G) (H : subUMagmaType S).
Notation val := (val : H -> G).
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build H G val val1_subproof.
Lemma val1 : val 1 = 1
Proof.
End subUMagma.

HB.factory Record SubChoice_isSubUMagma (G : umagmaType) S H
    & SubChoice G S H := {
  umagma_closed_subproof : umagma_closed S
}.

HB.builders Context G S H & SubChoice_isSubUMagma G S H.

HB.instance Definition _ :=
  SubChoice_isSubMagma.Build G S H (snd umagma_closed_subproof).

Let inH v Sv : H := Sub v Sv.
Let oneH := inH (fst umagma_closed_subproof).

HB.instance Definition _ := hasOne.Build H oneH.

Lemma val1 : (val : H -> G) 1 = 1.
Proof.

HB.instance Definition _ := isSubBaseUMagma.Build G S H val1.

Lemma mul1g : left_id 1 (@mul H).
Proof.
Lemma mulg1 : right_id 1 (@mul H).
Proof.

HB.instance Definition _ := BaseUMagma_isUMagma.Build H mul1g mulg1.

HB.end.

#[short(type="subMonoidType")]
HB.structure Definition SubMonoid (G : monoidType) S :=
  { H of SubUMagma G S H & Monoid H}.

HB.factory Record SubChoice_isSubMonoid (G : monoidType) S H
    & SubChoice G S H := {
  monoid_closed_subproof : monoid_closed S
}.

HB.builders Context G S H & SubChoice_isSubMonoid G S H.

HB.instance Definition _ :=
  SubChoice_isSubUMagma.Build G S H monoid_closed_subproof.
HB.instance Definition _ :=
  SubChoice_isSubSemigroup.Build G S H (snd monoid_closed_subproof).

HB.end.

#[short(type="subGroupType")]
HB.structure Definition SubGroup (G : groupType) S :=
  { H of SubUMagma G S H & Group H}.

HB.factory Record SubChoice_isSubGroup (G : groupType) S H
    & SubChoice G S H := {
  group_closed_subproof : group_closed S
}.

HB.builders Context G S H & SubChoice_isSubGroup G S H.

Lemma umagma_closed : umagma_closed S.
Proof.


HB.instance Definition _ := SubChoice_isSubMonoid.Build G S H umagma_closed.
HB.instance Definition _ :=
  isInvClosed.Build G S (group_closedV group_closed_subproof).

Let inH v Sv : H := Sub v Sv.
Let invH (u : H) := inH (gpredVr _ (valP u)).

HB.instance Definition _ := hasInv.Build H invH.

Lemma mulVg : left_inverse 1%g invH *%g.
Proof.
Lemma mulgV : right_inverse 1%g invH *%g.
Proof.

HB.instance Definition _ := Monoid_isGroup.Build H mulVg mulgV.

HB.end.

Prenex Implicits mul inv natexp conjg commg.

Notation "*%g" := (@mul _) : function_scope.
Notation "x * y" := (mul x y) : group_scope.
Notation "1" := (@one _) : group_scope.
Notation "s `_ i" := (nth 1 s i) : group_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%g/1]_(i <- r | P%B) F%g) : group_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%g/1]_(i <- r) F%g) : group_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%g/1]_(m <= i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%g/1]_(m <= i < n) F%g) : group_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%g/1]_(i | P%B) F%g) : group_scope.
Notation "\prod_ i F" :=
  (\big[*%g/1]_i F%g) : group_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%g/1]_(i : t | P%B) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%g/1]_(i : t) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%g/1]_(i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%g/1]_(i < n) F%g) : group_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%g/1]_(i in A | P%B) F%g) : group_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%g/1]_(i in A) F%g) : group_scope.
Notation "x ^+ n" := (natexp x n) : group_scope.
Notation "x ^-1" := (inv x) : group_scope.
Notation "x / y" := (x * y^-1) : group_scope.
Notation "x ^- n" := ((x ^+ n)^-1) : group_scope.
Notation "x ^ y" := (conjg x y) : group_scope.
Notation "[ ~ x1 , x2 , .. , xn ]" := (commg .. (commg x1 x2) .. xn)
  : group_scope.

Section FinFunMagma.
Variable (aT : finType) (rT : magmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_mul f g := [ffun a => f a * g a].

HB.instance Definition _ := hasMul.Build {ffun aT -> rT} ffun_mul.

End FinFunMagma.

HB.instance Definition _ (aT : finType) (rT : ChoiceMagma.type) :=
  Magma.on {ffun aT -> rT}.

Section FinFunSemigroup.
Variable (aT : finType) (rT : semigroupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mulgA : associative (@ffun_mul aT rT).
Proof.

HB.instance Definition _ := isSemigroup.Build {ffun aT -> rT} ffun_mulgA.

End FinFunSemigroup.

Section FinFunBaseUMagma.
Variable (aT : finType) (rT : baseUMagmaType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_one := [ffun a : aT => (1 : rT)].

HB.instance Definition _ :=
  hasOne.Build {ffun aT -> rT} ffun_one.

End FinFunBaseUMagma.

HB.instance Definition _ (aT : finType) (rT : ChoiceBaseUMagma.type) :=
  BaseUMagma.on {ffun aT -> rT}.

Section FinFunUMagma.
Variable (aT : finType) (rT : umagmaType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mul1g : left_id (@ffun_one aT rT) *%g.
Proof.
Fact ffun_mulg1 : right_id (@ffun_one aT rT) *%g.
Proof.

HB.instance Definition _ :=
  Magma_isUMagma.Build {ffun aT -> rT} ffun_mul1g ffun_mulg1.

End FinFunUMagma.

HB.instance Definition _ (aT : finType) (rT : monoidType) :=
  UMagma.on {ffun aT -> rT}.

Section FinFunBaseGroup.

Variable (aT : finType) (rT : baseGroupType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_inv f := [ffun a => (f a)^-1].

HB.instance Definition _ := hasInv.Build {ffun aT -> rT} ffun_inv.

End FinFunBaseGroup.

Section FinFunGroup.

Variable (aT : finType) (rT : groupType).
Implicit Types f g : {ffun aT -> rT}.

Fact ffun_mulVg :
  left_inverse (@ffun_one aT rT) (@ffun_inv _ _) (@ffun_mul _ _).
Proof.
Fact ffun_mulgV :
  right_inverse (@ffun_one aT rT) (@ffun_inv _ _) (@ffun_mul _ _).
Proof.

HB.instance Definition _ := Monoid_isGroup.Build {ffun aT -> rT}
  ffun_mulVg ffun_mulgV.

End FinFunGroup.

Section PairMagma.
Variables G H : magmaType.

Definition mul_pair (x y : G * H) := (x.1 * y.1, x.2 * y.2).

HB.instance Definition _ := hasMul.Build (G * H)%type mul_pair.

Fact fst_is_multiplicative : {morph fst : x y / x * y}
Proof.
HB.instance Definition _ :=
  isMultiplicative.Build _ _ fst fst_is_multiplicative.

Fact snd_is_multiplicative : {morph snd : x y / x * y}
Proof.
HB.instance Definition _ :=
  isMultiplicative.Build _ _ snd snd_is_multiplicative.

End PairMagma.

Section PairSemigroup.
Variables G H : semigroupType.

Lemma pair_mulgA : associative (@mul (G * H)%type).
Proof.

HB.instance Definition _ := Magma_isSemigroup.Build (G * H)%type pair_mulgA.

End PairSemigroup.

Section PairBaseUMagma.
Variables G H : baseUMagmaType.

Definition one_pair : G * H := (1, 1).

HB.instance Definition _ := hasOne.Build (G * H)%type one_pair.

Fact fst_is_umagma_morphism : fst (1 : G * H) = 1
Proof.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build _ _ fst fst_is_umagma_morphism.

Fact snd_is_umagma_morphism : snd (1 : G * H) = 1
Proof.
HB.instance Definition _ :=
  Multiplicative_isUMagmaMorphism.Build _ _ snd snd_is_umagma_morphism.

End PairBaseUMagma.

Section PairUMagma.
Variables G H : umagmaType.

Lemma pair_mul1g : left_id (@one_pair G H) *%g.
Proof.
Lemma pair_mulg1 : right_id (@one_pair G H) *%g.
Proof.

HB.instance Definition _ :=
  BaseUMagma_isUMagma.Build (G * H)%type pair_mul1g pair_mulg1.

End PairUMagma.

HB.instance Definition _ (G H : ChoiceMagma.type) := Magma.on (G * H)%type.
HB.instance Definition _ (G H : ChoiceBaseUMagma.type) :=
  BaseUMagma.on (G * H)%type.
HB.instance Definition _ (G H : monoidType) := Semigroup.on (G * H)%type.

Section PairBaseGroup.
Variables G H : baseGroupType.

Definition inv_pair (u : G * H) := (u.1 ^-1, u.2 ^-1).

HB.instance Definition _ := hasInv.Build (G * H)%type inv_pair.

End PairBaseGroup.

Section PairGroup.
Variables G H : groupType.

Lemma pair_mulVg : left_inverse one (@inv_pair G H) mul.
Proof.
Lemma pair_mulgV : right_inverse one (@inv_pair G H) mul.
Proof.

HB.instance Definition _ :=
  Monoid_isGroup.Build (G * H)%type pair_mulVg pair_mulgV.

End PairGroup.


HB.mixin Record SetoidMagma_isSemigroup G & SetoidMagma G := {
  mulsA : associative (@mul G)
}.

#[short(type="semigroupType")]
HB.structure Definition Semigroup := {G of Magma_isSemigroup G & ChoiceMagma G}.

HB.factory Record isSemigroup G & Choice G := {
  mulsA: forall x y z,
    x * (y * z) \approx (x * y) * z;
}.

HB.builders Context G & isSemigroup G.

HB.instance Definition _ := hasMul.Build G mul.
HB.instance Definition _ := Magma_isSemigroup.Build G mulgA.

HB.end.

Bind Scope group_scope with Semigroup.sort.

Section SemigroupTheory.
Variable G : semigroupType.
Implicit Types x y : G.

#[export]
HB.instance Definition _ := SemiGroup.isLaw.Build G *%g mulgA.

Lemma commuteM x y z : commute x y -> commute x z -> commute x (y * z).
Proof.

End SemigroupTheory.


HB.mixin Record isMonoid M of hasEquiv M & hasMul M & hasOne M := {
  mulsA: forall x y z,
    x * (y * z) \approx (x * y) * z;
  mul1s: forall x,
    1 * x \approx x;
  muls1: forall x,
    x * 1 \approx x;
}.
#[short(type="monoid")]
HB.structure Definition Monoid := {
  G of isMonoid G & hasEquiv G & hasMul G & hasOne G
}.


(* If `l = [a; b; c; ...; z]`, `prod l = a @ b @ ... @ z` *)
Definition prod {M: monoid} (l: seq M) : M :=
  foldr (fun y acc => y @ acc) e l.
Arguments prod {_} / !_.

Lemma prod0 {M: monoid} : @prod M nil = e.
Proof. done. Qed.

Lemma prod1s {M: monoid} (a: M) (l: seq M) : prod (a :: l) == a @ prod l.
Proof. done. Qed.

Lemma prod_cat {M: monoid} (l1 l2: seq M): prod (l1 ++ l2) == (prod l1) @ (prod l2).
Proof.
elim: l1 => [|a l1 /= ->]; first by rewrite /= neutral_left.
by rewrite associativity.
Qed.

(** Some theory about morphisms *)

HB.mixin Record isMonoidMorphism (G H: monoid) (f: G -> H) := {
  morphism_preserve_e: f e == e;
  morphism_preserve_law: forall x y, f (x @ y) == (f x) @ (f y);
}.
#[short(type="morphism")]
HB.structure Definition Morphism (G H: monoid) :=
  { f of isSetoidMorphism G H f 
       & isMonoidMorphism G H f}.


HB.mixin Record isInjective (A B: equivType) (f: A -> B) := {
  injectivity_property: forall x y, f x == f y -> x == y;
}.

#[short(type="injectiveFunType")]
HB.structure Definition Injective (A B: equivType) :=
  { f of isInjective A B f
       & isSetoidMorphism A B f}.

#[short(type="injectiveMorphism")]
HB.structure Definition InjectiveMorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.mixin Record isSurjective (A B: equivType) (f: A -> B) := {
  surjectivity_property: forall y, exists x, f x == y;
}.

#[short(type="surjectiveFunType")]
HB.structure Definition Surjective (A B: equivType) :=
  { f of isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="surjectiveMorphism")]
HB.structure Definition SurjectiveMorphism (G H: monoid) :=
  { f of isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

#[short(type="bijectiveFunType")]
HB.structure Definition Bijective (A B: equivType) :=
  { f of isInjective A B f
       & isSurjective A B f
       & isSetoidMorphism A B f}.

#[short(type="isomorphism")]
HB.structure Definition Isomorphism (G H: monoid) :=
  { f of isInjective G H f
       & isSurjective G H f
       & isSetoidMorphism G H f
       & isMonoidMorphism G H f }.

HB.factory Record isIsomorphismInverse (S T: monoid)
  (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    morphism_inverse_left: forall x, g (f x) == x;
    morphism_inverse_right: forall x, f (g x) == x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_equiv'.

  Fact g_surjectivity_property: forall y, exists x, g x == y.
  Proof.
    move => y; exists (f y); by apply morphism_inverse_left.
  Qed.

  HB.instance Definition _ :=
    isSurjective.Build _ _ g g_surjectivity_property.
  
  Fact g_injectivity_property: forall x y, g x == g y -> x == y.
  Proof.
    move => x y Hg; have: f (g x) == f (g y).
    - by apply morphism_preserve_equiv.
    by rewrite !morphism_inverse_right.
  Qed.

  HB.instance Definition _ :=
    isInjective.Build _ _ g g_injectivity_property.

  Fact g_preserve_e: g e == e.
  Proof.
    by rewrite -(morphism_inverse_left e) morphism_preserve_e.
  Qed.

  Fact g_preserve_law: forall x y, g (x @ y) == g x @ g y.
  Proof.
    move => x y.
    move: (@surjectivity_property _ _ f x) => [x'] <-.
    move: (@surjectivity_property _ _ f y) => [y'] <-.
    by rewrite -morphism_preserve_law !morphism_inverse_left.
  Qed.

  HB.instance Definition _ :=
    isMonoidMorphism.Build _ _ g g_preserve_e g_preserve_law.
HB.end.

HB.factory Record isIsomorphismLeftInverse (S T: monoid)
  (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    morphism_inverse_left: forall x, g (f x) == x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismLeftInverse S T f g.

  HB.instance Definition _ :=
    isSetoidMorphism.Build _ _ g morphism_preserve_equiv'.

  Fact morphism_inverse_right': forall y, f (g y) == y.
  Proof.
    move => y.
    move: (@surjectivity_property _ _ f y) => [x] <-;
    by apply /morphism_preserve_equiv /morphism_inverse_left.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      morphism_preserve_equiv'
      morphism_inverse_left
      morphism_inverse_right'.
HB.end.

HB.factory Record isIsomorphismRightInverse (S T: monoid)
  (f: isomorphism S T) (g: T -> S) := {
    morphism_preserve_equiv':
      forall x y, x == y -> g x == g y;
    morphism_inverse_right: forall x, f (g x) == x;
}.

HB.builders Context 
  (S T: monoid) (f: isomorphism S T) g of 
    isIsomorphismRightInverse S T f g.

  Fact morphism_inverse_left': forall x, g (f x) == x.
  Proof.
    move => x; apply (@injectivity_property _ _ f).
    by apply morphism_inverse_right.
  Qed.
  
  HB.instance Definition _ :=
    isIsomorphismInverse.Build _ _ f g
      morphism_preserve_equiv'
      morphism_inverse_left'
      morphism_inverse_right.
HB.end.

(** Composition of morphisms *)

(* TODO(reiniscirpons): This feels like something that 
   has already been done. *)
Section MorphismComposition.

Context {S T U: monoid}.
Variable f: morphism S T.
Variable g: morphism T U.

Lemma comp_preserve_e: (g \o f) e == e.
Proof. by rewrite /comp !morphism_preserve_e. Qed.

Lemma comp_preserve_law: forall x y,
  (g \o f) (x @ y) == ((g \o f) x) @ ((g \o f) y).
Proof. move => x y; by rewrite /comp !morphism_preserve_law. Qed.

HB.instance Definition _ :=
  isMonoidMorphism.Build S U (g \o f) comp_preserve_e comp_preserve_law.
End MorphismComposition.

Section InjectionComposition.
Context {A B C: equivType}.
Variable f: injectiveFunType A B.
Variable g: injectiveFunType B C.

Lemma comp_preserve_injectivity_property: forall x y,
  (g \o f) x == (g \o f) y -> x == y.
Proof.
  move => x y; rewrite /comp;
  by move/injectivity_property/injectivity_property.
Qed.
HB.instance Definition _ :=
  isInjective.Build A C (g \o f) comp_preserve_injectivity_property.
End InjectionComposition.

Section SurjectionComposition.
Context {A B C: equivType}.
Variable f: surjectiveFunType A B.
Variable g: surjectiveFunType B C.


Lemma comp_preserve_surjectivity_property: forall y,
  exists x, (g \o f) x == y.
Proof.
  move => y.
  move: (@surjectivity_property _ _ g y) => [z] Hz.
  move: (@surjectivity_property _ _ f z) => [x] Hx.
  by exists x; rewrite /= Hx Hz.
Qed.
HB.instance Definition _ :=
  isSurjective.Build A C (g \o f) comp_preserve_surjectivity_property.
End SurjectionComposition.

Section IsomorphismComposition.
Context {S T U: monoid}.
Variable f: isomorphism S T.
Variable g: isomorphism T U.

(* TODO(reiniscirpons): Without this line isomorphism composition
  is not an isomorphism. Why? *)
HB.instance Definition _ :=
  isSetoidMorphism.Build S U
  (g \o f) morphism_preserve_equiv.
End IsomorphismComposition.


(** Theory of groups *)

HB.mixin Record isGroup G of hasEq G & isMonoid G := {
  inv : G -> G;
  inverse_law : forall x y, inv (x @ y) == (inv y) @ (inv x);
  inverse_left : forall x, x @ (inv x) == e;
  inverse_right : forall x, (inv x) @ x == e;
}.
#[short(type="group")]
HB.structure Definition Group := { G of isGroup G & hasEq G & isMonoid G }.

Lemma inv_involutive {G: group}: forall (g: G), inv (inv g) == g.
Proof.
move=> g.
have: (inv g) @ (inv (inv g)) == (inv g) @ g.
  by rewrite inverse_left inverse_right.
move=> /(congruent_left g).
by rewrite !associativity inverse_left !neutral_left.
Qed.

Lemma inverse_e: forall G: group, (@inv G e) == e.
Proof.
  move => G.
  have: (@inv G e) @ e == e => [|{2}<-]; first by rewrite inverse_right.
  by rewrite neutral_right.
Qed.


Section ProperGroup.
HB.declare Context G of hasEq G & isMonoid G & isGroup G.

Global Instance : Proper (eq ==> eq) (inv : G -> G).
Proof.
move=> a b eq_ab.
have H: (inv a) @ b == e; first by rewrite -eq_ab inverse_right.
have: (inv a) @ b @ (inv b) == (inv b); first by rewrite H neutral_left.
by rewrite -associativity inverse_left neutral_right.
Qed.

End ProperGroup.

Lemma inv_e {G: group}: inv (s:=G) e == e.
Proof. by rewrite -{1}[inv e]neutral_right inverse_right. Qed.

Lemma prod_inv {G: group} (l: seq G):
  inv (prod l) == prod (map inv (rev l)).
Proof.
elim: l => [/=|c l].
  by rewrite inv_e.
rewrite -cat1s rev_cat map_cat !prod_cat inverse_law => ->.
by rewrite /= !neutral_right.
Qed.

Lemma prod_rcons {G: group} (l: seq G) (c: G):
  prod (rcons l c) == (prod l) @ c.
Proof.
elim: l => /= [|a l ->].
  by rewrite neutral_left neutral_right.
by rewrite associativity.
Qed.

Lemma morphism_preserve_inv:
  forall (G H: group) (f: morphism G H) x,
    inv (f x) == f (inv x).
Proof.
  move => G H f x.
  have H1: (f x) @ (f (inv x)) == e.
  - rewrite -morphism_preserve_law -morphism_preserve_e;
    apply morphism_preserve_equiv; by rewrite inverse_left.
  - by rewrite -(neutral_left (f (inv x))) -(inverse_right (f x))
            -associativity H1 neutral_right.
Qed.

Definition power {G: group} (w: G) (k: int) : G :=
  match k with
  | Posz k => iter k (fun acc => w @ acc) e
  | Negz k => iter k.+1 (fun acc => (inv w) @ acc) e (* Negx 0 is -1 *)
  end.

Lemma power0 {G: group} (w: G): power w 0 = e.
Proof. done. Qed.

Lemma power1 {G: group} (w: G): power w 1 = w @ e.
Proof. done. Qed.

Lemma powerS {G: group} (w: G) (x: nat):
  power w x.+1 = w @ (power w x).
Proof. done. Qed.

Lemma powerP {G: group} (w: G) (x: nat):
  power w (- (x.+1: int)) = (inv w) @ (power w (- (x:int))).
Proof. by case: x. Qed.

(* TODO(reiniscirpons): I locked power here to avoid it being simplified
   in contexts where we dont want it to be later on.
   But now, it wont evaluate powers with a concrete, e.g.
   power w (-1) is left unexpanded. Is there some intermediate that would
   work? *)
Arguments power {_} _ _: simpl never.

Lemma power_e {G: group} (k: int) : power (e (s:=G)) k == (e (s:=G)).
Proof.
  elim: k => [//||] k.
  - by rewrite powerS => ->; rewrite neutral_left.
  - by rewrite powerP => ->; rewrite neutral_right inv_e.
Qed.

(* TODO(reiniscirpons): Should I be defining my own induction principles?*)
Definition nat_pairs_ind: forall (P: nat -> Prop),
  P 0 -> P 1 -> (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move => P H0 H1 HnSn n; enough (H: P n /\ P n.+1).
  - by case: H.
  elim: n => [//|n [Hn HSn]]; split => [//|].
  by apply HnSn.
Qed.

Lemma power_inv {G: group} (w: G) (x:int):
  power w (- x) == inv (power w x).
Proof.
case: x; elim/nat_pairs_ind => [||k].
- by rewrite /power /= inv_e.
- by rewrite /power /= inverse_law neutral_right inv_e neutral_left.
- rewrite !powerS !powerP !inverse_law => <- H.
  by rewrite H -{2}H associativity.
- by rewrite /power /= !neutral_right inv_involutive.
- by rewrite /power /= !neutral_right inverse_law inv_involutive.
- rewrite !powerS !powerP !inverse_law !inv_involutive => <- H.
  by rewrite H -{2}H !associativity.
Qed.

Lemma powerC' {G: group} (w: G) (x: int):
  (power w x) @ w == w @ (power w x).
Proof.
elim: x => [|x H|x].
- by rewrite power0 neutral_left neutral_right.
- by rewrite powerS -{2}H associativity.
- rewrite !power_inv powerS /= inverse_law => eq.
  rewrite associativity -eq.
  by rewrite -!associativity inverse_left inverse_right neutral_right.
Qed.

Lemma powerC'' {G: group} (w: G) (x: int):
  (power w x) @ (inv w) == (inv w) @ (power w x).
Proof.
  case: x.
  - case => [|k].
  -- by rewrite /power /= neutral_right neutral_left.
  -- rewrite powerS -{1}powerC'.
    by rewrite -associativity inverse_left associativity
               inverse_right neutral_left neutral_right.
  - elim => [|n H].
  -- by rewrite /power /= neutral_right.
  -- by rewrite powerP -{2}H associativity.
Qed.

Lemma powerC {G: group} (w: G) (x y: int):
  (power w x) @ (power w y) == (power w y) @ (power w x).
Proof.
  elim: x => [|n IH|n IH].
  - by rewrite power0 neutral_left neutral_right.
  - by rewrite powerS -associativity IH associativity -powerC' associativity.
  - by rewrite powerP -associativity IH associativity -powerC'' associativity.
Qed.

Lemma powerS' {G: group} (w: G) (x: int):
  power w (1 + x) == w @ (power w x).
Proof.
  case: x => n /=.
  - by rewrite /power /=.
  - case: n => [|n].
  -- by rewrite /power /= neutral_right inverse_left.
  -- rewrite /power /= !associativity inverse_left neutral_left.
     by have ->: (n.+1 - 1 = n)%N by case: n.
Qed.

Lemma powerP' {G: group} (w: G) (x: int):
  power w (-1 + x) == (inv w) @ (power w x).
Proof.
  case: x => n /=.
  - case: n => [|n].
  -- by rewrite /power /= neutral_right.
  -- rewrite /power /= associativity inverse_right neutral_left.
     by have ->: (n.+1 - 1 = n)%N by case: n.
  - by rewrite /power /=.
Qed.

Lemma power_add {G: group} (w: G) (x y: int):
  power w (x + y) == (power w x) @ (power w y).
Proof.
elim: x => [|x H|x H].
- by rewrite add0r power0 neutral_left.
- have ->: x.+1%:Z + y = 1 + (x%:Z + y) by lia.
  by rewrite powerS powerS' -associativity H.
- have ->: - x.+1%:Z + y = -1 + (- x%:Z + y) by lia.
  by rewrite powerP powerP' H associativity.
Qed.

Lemma power_switch_sign {G: group} (w: G) (x y: int):
  power (power w x) (- y) == power (power w (-x)) y.
Proof.
elim: y => [|y|y].
- by rewrite oppr0 !power0.
- rewrite powerP powerS => ->.
  by rewrite -power_inv.
- rewrite !opprK powerS powerP => ->.
  by rewrite -power_inv opprK.
Qed.

Lemma powerC'_tower {G: group} (w: G) (x y: int):
  power (power w x) y @ w == w @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity => ->.
  by rewrite associativity powerC' associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC' associativity.
Qed.

Lemma powerC''_tower {G: group} (w: G) (x y: int):
  power (power w x) y @ (inv w) == (inv w) @ power (power w x) y.
Proof.
elim: y => [|y|y].
- by rewrite power0 neutral_left neutral_right.
- rewrite powerS -associativity => ->.
  by rewrite associativity powerC'' associativity.
- rewrite powerP -associativity => ->.
  by rewrite associativity -power_inv powerC'' associativity.
Qed.

Lemma power_mul {G: group} (w: G) (x y: int):
  power w (x * y) == power (power w x) y.
Proof.
elim: x => [|x|x].
- by rewrite mul0r !power0 power_e.
- rewrite powerS.
  have ->: x.+1%:Z * y = x%:Z * y + y by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS => <-.
    by rewrite !associativity -[w @ _]powerC' -![((_ @ w) @ _)]associativity
            -powerC'_tower !associativity.
  - rewrite !power_switch_sign !powerP => <-.
    rewrite powerS inverse_law -power_inv.
    by rewrite associativity -[(_ @ _) @ inv w]associativity
            -associativity powerC''_tower !associativity.
- have ->: - x.+1%:Z * y = - x%:Z*y + (-y) by lia.
  rewrite power_add => ->.
  elim: y => [|y|y].
  - by rewrite !power0 neutral_left.
  - rewrite !powerS !powerP => <-.
    by rewrite !associativity -[inv w @ _]powerC'' -![((_ @ inv w) @ _)]associativity
            -powerC''_tower !associativity.
  - have ->: (- - y%:Z) = y%:Z by lia.
    have ->: (- - y.+1%:Z) = y.+1%:Z by lia.
    rewrite powerS ![power _ (- y.+1%:Z)]powerP => <-.
    rewrite powerP inverse_law inv_involutive.
    by rewrite !associativity -[(_ @ _) @ w]associativity
            -associativity  powerC'_tower  !associativity.
Qed.

Lemma power_proper_pos {G: group} (x y: G) (k: nat):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
elim: k => [//|k IH].
by rewrite !powerS IH Heq.
Qed.
Lemma power_proper {G: group} (x y: G) (k: int):
  x == y -> power x k == power y k.
Proof.
move=> Heq.
case: k => k.
  exact: power_proper_pos.
have ->: Negz k = - (k.+1)%:Z by done.
by rewrite !power_inv power_proper_pos.
Qed.
Arguments power_proper {_ _ _}.

Global Instance: forall G, Proper (eq ==> Logic.eq ==> eq) (@power G).
Proof.
  by move => G x y Hxy h k ->; apply power_proper.
Qed.

Lemma morphism_preserve_power_pos {G G': group} (f: morphism G G') (x: G) (k: nat):
  f (power x k) == power (f x) k.
Proof.
elim: k => [/=|k].
  by rewrite morphism_preserve_e.
by rewrite !powerS morphism_preserve_law => <-.
Qed.
Lemma morphism_preserve_power {G G': group} (f: morphism G G') (x: G) (k: int):
  f (power x k) == power (f x) k.
Proof.
case: k => k.
  exact: morphism_preserve_power_pos.
have ->: Negz k = - (k.+1)%:Z by done.
rewrite !power_inv -morphism_preserve_inv.
by rewrite morphism_preserve_power_pos.
Qed.


#[short(type="deceqGroupType")]
HB.structure Definition DecEqGroup := { G of isGroup G & hasEq G & isMonoid G & hasDecEq G }.

HB.mixin Record isSubgroup (G: group) (H: group) := {
  subgroup_inj: injectiveMorphism H G;
}.

#[short(type="subgroup")]
HB.structure Definition Subgroup (G: group) := { H of isSubgroup G (* super group *) H (* sub group *)}.

(* NOTE(reiniscirpons): I don't understand this well enough to change. Assume ok for now. *)

Elpi Accumulate coercion.db lp:{{

% See https://rocq-prover.zulipchat.com/#narrow/channel/237868-Hierarchy-Builder-devs-.26-users/topic/Missing.20instance.20in.20a.20hierarchy.20for.20subtypes/with/561428680
coercion _ T {{ Type }} ExpectedType Solution :-
  ExpectedType = {{ subgroup _ }},
  coq.elaborate-skeleton {{ ( lp:T : group) }} ExpectedType Solution Diagnostics,
  ok = Diagnostics.

}}.

(* TODO: it would be cool to "register" subgroup_inj as a coercion.
   I don't think it can be done via the vanilla Rocq coercions, and doing so via a coercion hook
   seems difficult without triggering an infinite coercion chain. *)

(* TODO(reiniscirpons): Dont do this, the issue is the parametricity,
  if we have G as a parameter for the coercion this will cause bad bad things
  to happen.
  Coercion subgroup_to_group {G} {H: subgroup G}:
    H -> G := @subgroup_inj G H.
*)

Definition in_subgroup {G: group} (K: subgroup G) (x: G) :=
  exists x': K, subgroup_inj x' == x.
Notation "x '\insubgroup' K" := (in_subgroup K x) (at level 10).

(* this definition is useful as due to non-forgetful inheritance, seeing a subgroup of a subgroup of a group as a subgroup of the group is not easy *)
Definition in_subsubgroup (G: group) (H: subgroup G) (I: subgroup H) (x: G) :=
  exists x': I, subgroup_inj (subgroup_inj x') == x.
Notation "x '\insubsubgroup[' Subgroup ']' Subsubgroup" := (@in_subsubgroup _ Subgroup Subsubgroup x) (at level 10).

Lemma in_subgroup_proper {Group: group} (Subgroup: subgroup Group) (x x': Group):
  (x == x') ->
  (x \insubgroup Subgroup) ->
  (x' \insubgroup Subgroup).
Proof.
move=> Heq [xS ?].
exists xS.
by rewrite -Heq.
Qed.

Lemma in_subgroup_e {Group: group} {Subgroup: subgroup Group}:
  e \insubgroup Subgroup.
Proof. exists e; by rewrite morphism_preserve_e. Qed.

Lemma in_subgroup_law {Group: group} {Subgroup: subgroup Group} (x y: Group):
  (x \insubgroup Subgroup) -> (y \insubgroup Subgroup) -> ((x @ y) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
case=> [y' Hy'].
exists (x' @ y').
by rewrite morphism_preserve_law -Hx' -Hy'.
Qed.

Lemma in_subgroup_inv {Group: group} {Subgroup: subgroup Group} (x: Group):
  (x \insubgroup Subgroup) -> ((inv x) \insubgroup Subgroup).
Proof.
case=> [x' Hx'].
exists (inv x').
by rewrite -Hx' morphism_preserve_inv.
Qed.

Lemma in_subsubgroup_proper {G: group} (H: subgroup G) (I: subgroup H) (x x': G) :
  x == x' ->
  (x \insubsubgroup[H] I) ->
  (x' \insubsubgroup[H] I).
Proof.
move=> Heq [xK eq].
exists xK.
by rewrite eq.
Qed.


Definition is_subgroup_stable {G: group} {H1 H2: subgroup G} (f: morphism H1 H2) (K: subgroup G) :=
  forall (x: H1), ((subgroup_inj x) \insubgroup K) -> subgroup_inj (f x) \insubgroup K.

Record local_morphism (G: group) := {
  lm_source_subgroup : subgroup G;
  lm_target_subgroup : subgroup G;
  lm_morphism :> morphism lm_source_subgroup lm_target_subgroup;
}.
Arguments lm_source_subgroup {_}.
Arguments lm_target_subgroup {_}.
Coercion morphism_to_local_morphism {G} {H1 H2: subgroup G}: morphism H1 H2 -> local_morphism G :=
  fun f => {| lm_morphism := f |}.


Section RightCoset.

Context {G: group}.
Variable H: subgroup G.

Definition right_coset_eq (x y: G): Prop := in_subgroup H (x @ inv y).

Lemma right_coset_eq': forall x y,
  right_coset_eq x y <-> (exists w: H, (subgroup_inj w) @ y == x).
Proof.
  move => x y; split.
  - rewrite /right_coset_eq /in_subgroup.
    case => w Hw; exists w;
    by rewrite Hw -associativity inverse_right neutral_right.
  - case => w Hw; exists w;
    by rewrite -Hw -associativity inverse_left neutral_right.
Qed.

Instance RightCosetEqReflexivity : Reflexive right_coset_eq.
Proof.
  move => x; rewrite right_coset_eq'; exists e;
  by rewrite morphism_preserve_e neutral_left.
Qed.
Instance RightCosetEqSymmetry : Symmetric right_coset_eq.
Proof.
  move => x y; rewrite !right_coset_eq'.
  case => w Hw; exists (inv w).
  by rewrite -morphism_preserve_inv -Hw associativity inverse_right neutral_left.
Qed.
Instance RightCosetEqTransitivity : Transitive right_coset_eq.
Proof.
  move => x y z; rewrite !right_coset_eq'.
  move => [w1 H1] [w2 H2]; exists (w1 @ w2).
  by rewrite morphism_preserve_law -associativity H2 H1.
Qed.
Instance RightCosetEqEquivalence : Equivalence right_coset_eq := {}.
End RightCoset.
Existing Instance RightCosetEqReflexivity.
Existing Instance RightCosetEqSymmetry.
Existing Instance RightCosetEqTransitivity.
Existing Instance RightCosetEqEquivalence.
Arguments right_coset_eq {_}.

HB.mixin Record isRightCosetRep
  (G: group) (H: subgroup G) (f: G -> G) := {
  right_coset_rep_correct: forall (x: G),
    right_coset_eq H x (f x);
  right_coset_rep_unique: forall (x y: G),
    right_coset_eq H x y -> f x = f y;
}.

#[short(type="rightCosetRep")]
HB.structure Definition RightCosetRep (G: group) (H: subgroup G) :=
  { f of isRightCosetRep G H f }.

Lemma right_coset_eq_spec: forall G H (f: rightCosetRep G H) (x y: G),
  (right_coset_eq H x y) <-> (f x = f y).
Proof.
  move => G H f x y; split.
  - by apply right_coset_rep_unique.
  move => Hf; transitivity (f x).
  - by apply right_coset_rep_correct.
  rewrite Hf; symmetry; by apply right_coset_rep_correct.
Qed.

HB.mixin Record isSubgroupCharacterizer (G: group) (P: G -> Type) := {
  P_law: forall x y, P x -> P y -> P (x @ y);
  P_neutral: P e;
  P_inv: forall x, P x -> P (inv x);
}.
#[short(type = "subgroup_characterizer")]
HB.structure Definition SubgroupCharacterizer (G: group) := { P of isSubgroupCharacterizer G P }.

Section SubgroupByCharacterization.
Context {G: group}.
Variable P: subgroup_characterizer G.

#[projections(primitive)]
Record subgroup_by := {
  sb_point :> G;
  sb_point_characterization: P sb_point;
}.

Definition subgroupby_inj (x: subgroup_by): G := x.

Definition subgroupby_eq (x y: subgroup_by) := (subgroupby_inj x) == (subgroupby_inj y).
Lemma subgroupby_eq_refl: forall x, subgroupby_eq x x.
Proof. by move=> x; rewrite /subgroupby_eq. Qed.
Lemma subgroupby_eq_sym: forall x y, subgroupby_eq x y -> subgroupby_eq y x.
Proof. move=> x y; rewrite /subgroupby_eq; by symmetry. Qed.
Lemma subgroupby_eq_trans: forall x y z, subgroupby_eq x y -> subgroupby_eq y z -> subgroupby_eq x z.
Proof. move=> x y z; rewrite /subgroupby_eq => ? ?; by transitivity (subgroupby_inj y). Qed.

HB.instance Definition _ := hasEq.Build subgroup_by subgroupby_eq subgroupby_eq_refl subgroupby_eq_sym subgroupby_eq_trans.

Definition subgroupby_law (x y : subgroup_by): subgroup_by.
Proof.
exists (x.(sb_point) @ y.(sb_point)).
apply /P_law; exact /sb_point_characterization.
Defined.

Definition subgroupby_neutral: subgroup_by.
Proof. exists e; exact: P_neutral. Defined.

Lemma subgroupby_associativity: forall (x y z: subgroup_by), subgroupby_law x (subgroupby_law y z) == subgroupby_law (subgroupby_law x y) z.
Proof. move=> x y z; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= associativity. Qed.

Lemma subgroupby_neutral_left: forall (x: subgroup_by), subgroupby_law subgroupby_neutral x == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_left. Qed.

Lemma subgroupby_neutral_right: forall (x: subgroup_by), subgroupby_law x subgroupby_neutral == x.
Proof. move=> x; by rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/= neutral_right. Qed.

Lemma subgroupby_congruent_left: forall (x y z: subgroup_by), y == z -> subgroupby_law x y == subgroupby_law x z.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_left.
Qed.

Lemma subgroupby_congruent_right: forall (x y z: subgroup_by), y == z -> subgroupby_law y x == subgroupby_law z x.
Proof.
move=> x y z ?.
rewrite /subgroupby_law/= /eq/= /subgroupby_eq/= /subgroupby_inj/=.
exact: congruent_right.
Qed.

HB.instance Definition _ := isMonoid.Build subgroup_by subgroupby_law subgroupby_neutral subgroupby_associativity subgroupby_neutral_left subgroupby_neutral_right subgroupby_congruent_left subgroupby_congruent_right.

Definition subgroupby_inv: subgroup_by -> subgroup_by.
Proof. move=> x; exists (inv x.(sb_point)); exact /P_inv /sb_point_characterization. Defined.

Lemma subgroupby_inverse_law: forall x y, subgroupby_inv (x @ y) == (subgroupby_inv y) @ (subgroupby_inv x).
Proof. move=> x y; by rewrite /subgroupby_inv/=/eq/=/subgroupby_eq/subgroupby_inj/= inverse_law. Qed.

Lemma subgroupby_inverse_left : forall x, x @ (subgroupby_inv x) == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_left. Qed.

Lemma subgroupby_inverse_right : forall x, (subgroupby_inv x) @ x == e.
Proof. move=> x; by rewrite /subgroupby_inv/=/law/=/subgroupby_law/=/eq/=/subgroupby_eq/=/subgroupby_inj/= inverse_right. Qed.

HB.instance Definition _ := isGroup.Build subgroup_by subgroupby_inv subgroupby_inverse_law subgroupby_inverse_left subgroupby_inverse_right.

Lemma subgroupby_inj_preserve_equiv: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isSetoidMorphism.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_preserve_equiv.

Lemma subgroupby_inj_injectivity: forall x y, x == y -> subgroupby_inj x == subgroupby_inj y.
Proof. done. Qed.

HB.instance Definition _ := 
  isInjective.Build _ _ 
    subgroupby_inj 
    subgroupby_inj_injectivity.

Lemma subgroupby_inj_preserve_e: subgroupby_inj e == e.
Proof. done. Qed.
Lemma subgroupby_inj_preserve_law: forall x y, subgroupby_inj (law x y) == law (subgroupby_inj x) (subgroupby_inj y).
Proof. done. Qed.

HB.instance Definition _ := 
  isMonoidMorphism.Build _ _
    subgroupby_inj 
    subgroupby_inj_preserve_e 
    subgroupby_inj_preserve_law.

HB.instance Definition _ :=
  isSubgroup.Build G subgroup_by subgroupby_inj.

End SubgroupByCharacterization.
Arguments subgroup_by {_}.
Arguments sb_point_characterization {_ _}.
Arguments sb_point {_ _}.

(* {e}, the subgroup! *)
Section SingletonSubgroup.
Variable K: group.

Definition singleton_subgroup_char (x: K): Type := (x == e).

Lemma ssc_neutral: singleton_subgroup_char e.
Proof. by rewrite /singleton_subgroup_char. Qed.

Lemma ssc_inv (x: K): singleton_subgroup_char x -> singleton_subgroup_char (inv x).
Proof. by rewrite /singleton_subgroup_char => ->; rewrite inv_e. Qed.

Lemma ssc_law (x y: K): singleton_subgroup_char x -> singleton_subgroup_char y -> singleton_subgroup_char (x @ y).
Proof. by rewrite /singleton_subgroup_char => -> ->; rewrite neutral_left. Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build K singleton_subgroup_char ssc_law ssc_neutral ssc_inv.

Definition singleton_subgroup := subgroup_by singleton_subgroup_char.

Definition singleton_morphism: singleton_subgroup -> singleton_subgroup := id.

Lemma sm_preserve_equiv: forall x y, x == y -> singleton_morphism x == singleton_morphism y.
Proof. done. Qed.
Lemma sm_preserve_e: singleton_morphism e == e.
Proof. done. Qed.
Lemma sm_preserve_law: forall x y, singleton_morphism (x @ y) == (singleton_morphism x) @ (singleton_morphism y).
Proof. done. Qed.

HB.instance Definition _ :=
  isSetoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_preserve_equiv.
HB.instance Definition _ :=
  isMonoidMorphism.Build singleton_subgroup singleton_subgroup
    singleton_morphism
    sm_preserve_e
    sm_preserve_law.

End SingletonSubgroup.

(* TODO(reiniscirpons): Do we need this? *)
(* Intersection of subgroups *)
Section SubgroupIntersection.
Context {G: group}.
Variable (H1 H2: subgroup G).

Record is_in_intersection (x: G) : Prop := {
  intersection_in_left: x \insubgroup H1;
  intersection_in_right: x \insubgroup H2;
}.

Definition iii_P_law : forall (x y: G), is_in_intersection x -> is_in_intersection y -> is_in_intersection (x @ y).
Proof.
move=> x y [[x1 x1_eq] [x2 x2_eq]] [[y1 y1_eq] [y2 y2_eq]]; eexists.
- by exists (x1 @ y1); rewrite morphism_preserve_law -x1_eq -y1_eq.
- by exists (x2 @ y2); rewrite morphism_preserve_law -x2_eq -y2_eq.
Qed.

Definition iii_P_neutral : is_in_intersection e.
Proof. by eexists; exists e; rewrite morphism_preserve_e. Qed.

Definition iii_P_inv : forall (x: G), is_in_intersection x -> is_in_intersection (inv x).
Proof.
move=> x [[x1 x1_eq] [x2 x2_eq]]; eexists.
- by exists (inv x1); rewrite -morphism_preserve_inv -x1_eq.
- by exists (inv x2); rewrite -morphism_preserve_inv -x2_eq.
Qed.

HB.instance Definition _ := isSubgroupCharacterizer.Build G is_in_intersection iii_P_law iii_P_neutral iii_P_inv.

(* we could also prove that H1 /\ H2 is a subgroup of H1 and H2 *)

Definition intersection := subgroup_by is_in_intersection.

End SubgroupIntersection.
