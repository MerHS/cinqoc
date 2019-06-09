From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import ssralg ssrfun div prime.

Lemma orbA b1 b2 b3: b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
  by case: b1 b2 b3.
Qed.

Lemma implybE a b : (a ==> b) = ~~ a || b.
Proof.
  by case: a b.
Qed.

Lemma negb_and (a b: bool): ~~ (a && b) = ~~ a || ~~ b.
Proof.
  by case: a b.
Qed.

Lemma expn2 n: n ^ 2 = n * n.
Proof.
  by rewrite expnS expn1.
Qed.
  
Lemma subn_sqr m n: m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
  rewrite mulnBl.
  rewrite !mulnDr.
  rewrite mulnC.
  rewrite [X in _ = _ - X]addnC.
  rewrite subnDr.
  by rewrite !expn2.
Qed.

Lemma odd_exp m n: odd (m ^ n) = (n == 0) || odd m.
Proof.
  (* elim: n => [//| n IHn] //=. *)
  (* rewrite expnSr odd_mul IHn. *)
  (* case: (n == 0) => //=. *)
  (* by rewrite Bool.andb_diag. *)
  elim: n => // n IHn.
  rewrite expnS odd_mul {}IHn.
  by rewrite orKb.
Qed.

Definition all_words n T (alpha: seq T) :=
  let pp x wl := [seq x :: w | w <- wl] in
  let ext wl := flatten [seq pp x wl | x <- alpha] in
  iter n ext [:: [::] ].

Lemma size_all_words n T (alpha: seq T):
  size (all_words n T alpha) = size alpha ^ n.
Proof.
  elim: n => [//|n IHn] //=.
  rewrite size_allpairs.
  rewrite IHn.
  by rewrite expnS.
Qed.
