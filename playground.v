From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import ssralg ssrfun div prime.

Definition predn (n: nat) :=
  match n with
  | n'.+1 => n'
  | _ => O
  end.

Compute (predn 3).

Section iterators.

Variables (T: Type) (A: Type).
Variables (f: T -> A -> A).

Implicit Type x: T.

Fixpoint iter n op x :=
  if n is p.+1 then op (iter p op x) else x.

Fixpoint foldr a s :=
  if s is y :: ys then f y (foldr a ys) else a.
  
End iterators.

Check iter. (* forall T: Type, nat -> (T -> T) -> T -> T *)
About foldr. (* forall T A: Type, (T->A->A) -> A -> list T -> A *)

Compute 0.-1.
(* Local Notation "\sum_ ( m <= i < n ) F" :=
  foldr (fun i a => F + a) 0 (iota m (n-m))) (at level 50).*)
About iter.

Lemma negbb (b: bool) : ~~ (~~ b) = b.
Proof. 
  by case: b.
Qed.  

Lemma leqn0 n: (n <= 0) = (n == 0).
Proof.
  by case: n => [| k].
Qed.  

Lemma muln_eq0 m n: (m * n) == 0 = (m == 0) || (n == 0).
Proof.
  case: m => [|m] //.
  case: n => [|n] //.
  by rewrite muln0.
Qed.

Lemma leqE m n: (m <= n) = (m - n == 0).
Proof. by []. Qed.

Lemma leq_mul21 m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
  by rewrite !leqE -mulnBr muln_eq0.
Qed.

Lemma leq_mul22 m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
  unfold leq.
  rewrite /leq.

(*
Section Chinese.

Variables m1 m2: nat.
Hypothesis co_m12: coprime m1 m2.

Lemma chinese_remainer_ x y: (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
Proof.

Admitted.
End Chinese.        

*)
Lemma leqnn n: n <= n. Proof. by []. Qed.
Hint Resolve leqnn.
Lemma example a b: a + b <= a + b.
Proof. by []. Qed.

Lemma wilson m p: prime p -> p %| m `! + 1 -> m < p.
Proof.
  move=> prime_p.
  apply: contraLR.
  rewrite -leqNgt => leq_p_m.
  (* rewrite dvdn_addr.
    by rewrite gtnNdvd // prime_gt1.  
    by rewrite dvdn_fact // prime_gt0. *)
  rewrite dvdn_addr ?dvdn_fact ?prime_gt0 //.
  by rewrite gtnNdvd // prime_gt1.
Qed.

About nat_ind.
Lemma addm0 m: m + 0 = m.
Proof.
  (* elim: m.*)
  (* elim: m => [ |m IHm]. *)
  elim: m => [ // |m IHm].
  by rewrite -addn1 -addnA.
Qed.  
About rcons.

(* 
Lemma last_ind A (P: list A -> Prop):
 P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
*)

Lemma foldl_rev T A (f: A -> T -> A) (z: A) (s: seq T) :
  foldl f z (rev s) = seq.foldr (fun x z => f z x) z s.
Proof.
  elim/last_ind: s z => [|s x IHs] z //.
  (* last_ind on s, generalize z, intros second part, intro generalized z *)
  rewrite -cats1.
  rewrite foldr_cat.
  rewrite -IHs.
  rewrite cats1.
  by rewrite rev_rcons.
Qed.  

Lemma rhsn n: n = n + 0.
Proof.
  by rewrite [in RHS] addn0.
Qed.

Theorem Syllogism: forall A B C: Prop,
    (A -> B) /\ (B -> C) -> (A -> C).
Proof.
  intros.
  destruct H.
  auto.
Qed.

Theorem Syllogism': forall A B C: Prop,
    (A -> B) /\ (B -> C) -> (A -> C).
Proof.
  move=> A B C.
  case.
  move => H1.
  move => H2.
  move => H3.
  apply H2.
  apply H1.
  by [].
Qed.







