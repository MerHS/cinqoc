From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Definition all_words {T} n (alpha: seq T) :=
  let pp x wl := [seq x :: w | w <- wl] in
  let ext wl := flatten [seq pp x wl | x <- alpha] in
  iter n ext [:: [::] ].

Lemma size_all_words {T} n (alpha: seq T):
  size (all_words n alpha) = size alpha ^ n.
Proof.
  elim: n => [//|n IHn] //=.
  rewrite size_allpairs.
  rewrite IHn.
  by rewrite expnS.
Qed.



Require Import ZArith.
Section ZtoRing.

Lemma Zeq_boolP: Equality.axiom Zeq_bool.
Proof.
  rewrite /Equality.axiom.
  move=> x y.
  apply: (iffP idP); by rewrite Zeq_is_eq_bool.
Qed.
Definition Z_eqMixin := EqMixin Zeq_boolP.
Canonical Z_eqType := Eval hnf in EqType _ Z_eqMixin.

Definition Z_pickle (z: Z): nat :=
  if Z.leb 0 z
  then (Z.abs_nat z).*2
  else (Z.abs_nat (- z)).*2.+1.

Definition Z_unpickle (n: nat): option Z :=
  if odd n
  then Some (- (Z.of_nat n.-1./2))%Z
  else Some (Z.of_nat n./2).

Lemma Z_pickleK: pcancel Z_pickle Z_unpickle.
Proof.
  move=> z. rewrite /Z_pickle.
  case: ifP => z0; rewrite /Z_unpickle /=.
  rewrite odd_double (half_bit_double _ false).
  rewrite Zabs2Nat.id_abs.
  rewrite Z.abs_eq //.
  + by apply: Zle_bool_imp_le.
  + rewrite odd_double /=.
    rewrite (half_bit_double _ false).
    rewrite Zabs2Nat.id_abs.
    rewrite Z.abs_eq.
    rewrite ?Z.opp_involutive //.
    rewrite ?Z.opp_nonneg_nonpos.
    move/Z.leb_nle: z0.
    by move/Znot_le_gt /Z.gt_lt /Z.lt_le_incl.
Qed.

Definition Z_countMixin := Countable.Mixin Z_pickleK.
Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.

Definition Z_zmodMixin :=
  ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
Canonical Z_zmodType := Eval hnf in ZmodType _ Z_zmodMixin.

Open Scope ring_scope.
Goal forall x: Z, x *+ 2 = (2 * x)%Z.
Proof.
  by case=> // x; rewrite GRing.mulr2n Z.mul_comm -Zred_factor1.
Qed.

End ZtoRing.
