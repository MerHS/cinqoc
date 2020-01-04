From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat finset fingroup fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Section Lagrange.

Open Scope group_scope.

Variable gT: finGroupType.
Variable G: {group gT}.
Variable H: {group gT}.
Hypothesis HG: H \subset G.

Definition R := [rel x y | x * y^-1 \in H].

Lemma equiv_rel_R: equivalence_rel R.
Proof.
  rewrite /equivalence_rel=> x y z /=.
  split.
  - by rewrite mulgV.
  - move=> Hxy.
    apply /idP /idP => Htest.
    + apply groupVr in Hxy.
      rewrite invMg invgK in Hxy.
      move: (groupM Hxy Htest).
      by rewrite -mulgA [X in _ * X]mulgA mulVg mul1g.
    + move: (groupM Hxy Htest).
      by rewrite -mulgA [X in _ * X]mulgA mulVg mul1g.
Qed.

Lemma myCard_rcoset (A: {set gT}):
  A \in rcosets H G -> #|A| = #|H|.
Proof.
  case /rcosetsP => x xinG ->. (* -> : x=y -> P x => P y  *)
  by apply: card_rcoset.
Qed.


Lemma coset_equiv_class (x: gT) (xinG : x \in G):
  H :* x = [set y in G | R x y].
Proof.
  apply /setP => /= y. rewrite inE.
  apply /idP /idP.
  - case /rcosetP => z zinH -> {y}.
    apply /andP; split.
    + apply/ groupM; try by [].
      move/ subsetP: HG => HG'.
      by rewrite HG'.
    + rewrite invMg mulgA mulgV mul1g.
      by apply groupVr.
  - case/ andP => yinG xyvinH.
    apply/ rcosetP.
    exists (y * x^-1); last first.
    + by rewrite -mulgA mulVg mulg1.
    + move: xyvinH.
      by rewrite -groupV invMg invgK.
Qed.

Lemma rcosets_equiv_part: rcosets H G = equivalence_partition R G.
Proof.

Admitted.

End Lagrange.
