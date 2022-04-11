From mathcomp Require Import all_ssreflect.

(*
Definition enum (T : finType) : seq T := ... (* T の全ての元の列 *)
Lemma cardE (T : finType) : #|T| = size (enum T).
*)

Check ord0 : 'I_1.

Goal #|'I_3| = 3.
Proof. Check card_ord. by rewrite card_ord. Qed.
(*
card_ord
	 : forall n : nat, #|'I_n| = n
*)

(* val が 'I_n の値を nat に戻す *)
Goal [seq val i | i <- enum 'I_3] = [:: 0; 1; 2].
Proof. by rewrite enumT /= unlock /= val_ord_enum.
    Check enumT.
(*
enumT
	 : forall T : finType, enum T = Finite.enum T
*)
    Check unlock.
(*
unlock
	 : forall (T : Type) (x : T) (C : unlockable x), unlocked C = x
*)
    Check val_ord_enum. Qed.
(*
val_ord_enum
	 : forall n : nat, [seq val i | i <- ord_enum n] = iota 0 n
*)

Section Nagoya2013.
Definition Sk k n := \sum_(1 <= i < n.+1) i^k.

Variable m : nat.
Hypothesis Hm : m > 1.

Definition Tm n := \sum_(1 <= k < m) 'C(m,k) * Sk k n. (* binomial.v 参照 *)

Lemma Sk1 k : Sk k 1 = 1.
Proof. by rewrite /Sk big_nat1 exp1n. Qed.

Lemma Tm1 : Tm 1 = 2^m - 2.
Proof.
  rewrite /Tm.
  rewrite [in 2^m](_ : 2 = 1+1) //.
  rewrite Pascal. (* 二項公式 *)
  transitivity ((\sum_(0 <= k < m.+1) 'C(m,k)) - 2).
    symmetry.
    rewrite (@big_cat_nat _ _ _ m) //=.
    rewrite (@big_cat_nat _ _ _ 1) //=; last by apply ltnW.
    rewrite addnAC !big_nat1 bin0 binn addKn.
    apply eq_bigr => i H.
    by rewrite Sk1 muln1.
  rewrite big_mkord.
  congr (_ - _).
  apply eq_bigr => i _.
  by rewrite !exp1n !muln1.
Qed.

Search (_ ^ _) "exp". (* 自然数の指数関数 expn に関する様々な補題 *)

Lemma Tm2 : Tm 2 = 3^m - 3.
Proof.
  rewrite /Tm.
  have ->: 3^m - 3 = 2^m - 2 + (3^m - 1 - 2^m).
    rewrite addnBAC.
    rewrite subnAC addnBA.
    rewrite subnKC.
    by rewrite -subnDA.
    rewrite leq_exp2r //.
    by apply ltn_trans with 1.
    rewrite subn_gt0 ltn_exp2r //.
    by apply ltn_trans with 1.
    apply ltn_trans with 2 => //.
    by rewrite -{1}(expn1 2) ltn_exp2l.
  rewrite -Tm1.
  rewrite [in 3^m](_ : 3 = 1+2) //.
  rewrite Pascal.
  transitivity (Tm 1 + (\sum_(1 <= k < m) 'C(m,k) * 2^k)).
    rewrite -big_split /=.
    apply eq_bigr => i _.
    rewrite /Sk !big_cons !big_nil.
    by rewrite !addn0 -mulnDr.
  congr (_ + _).
  transitivity ((\sum_(0 <= k < m.+1) 'C(m,k) * 2^k) - 1 - 2^m).
    symmetry.
    rewrite (@big_cat_nat _ _ _ 1) //=.
    rewrite addnC big_nat1 bin0 expn0 mul1n addnK.
    rewrite (@big_cat_nat _ _ _ m) //=; last by apply ltnW.
    by rewrite big_nat1 binn mul1n addnK.
  rewrite big_mkord.
  do 2 congr (_ - _).
  apply eq_bigr => i _.
  by rewrite exp1n mul1n.
Qed.

Theorem Tmn n : Tm n.+1 = n.+2^m - n.+2.
Proof.
  elim:n => [|n IHn] /=.
    by apply Tm1.
  have Hm': m > 0 by apply ltnW.
  have ->: n.+3 ^ m - n.+3 = n.+2 ^ m - n.+2 + (n.+3 ^ m - 1 - n.+2 ^ m).
    rewrite addnBAC.
    rewrite subnAC addnBA.
    rewrite subnKC.
    by rewrite -subnDA.
    rewrite leq_exp2r //.
    rewrite subn_gt0 ltn_exp2r //.
    by rewrite -{1}(expn1 n.+2) leq_exp2l.
  rewrite -IHn.
  rewrite [in n.+3](_ : n.+3 = 1+n.+2) //.
  rewrite Pascal.
  transitivity (Tm n.+1 + (\sum_(1 <= k < m) 'C(m,k) * n.+2^k)).
    rewrite -big_split /=.
    apply eq_bigr => i _.
    rewrite /Sk.
    rewrite (@big_cat_nat _ _ _ n.+2) //=.
    rewrite big_nat1.
    by rewrite mulnDr.
  congr (_ + _).
  transitivity ((\sum_(0 <= k < m.+1) 'C(m,k) * n.+2^k) - 1 - n.+2^m).
    symmetry.
    rewrite (@big_cat_nat _ _ _ 1) //=.
    rewrite addnC big_nat1 bin0 expn0 mul1n addnK.
    rewrite (@big_cat_nat _ _ _ m) //=.
    by rewrite big_nat1 binn mul1n addnK.
  rewrite big_mkord.
  do 2 congr (_ - _).
  apply eq_bigr => i _.
  by rewrite exp1n mul1n.
Qed.

Lemma Tmp p : p > 2 -> p  %| Tm p.-1.
Proof.
  move=>HP.
  rewrite -subn1.
  have <-: (p - 1) - 1 + 1 = p - 1.
    rewrite subnK // subn_gt0.
    apply ltn_trans with 2 => //.
  rewrite addn1 !subn1.
  rewrite Tmn -addn2 -subn2 subnK.
  apply dvdn_sub => //.
  rewrite -{1}(expn1 p).
  apply dvdn_exp2l.
  apply ltn_trans with 1 => //.
  apply ltn_trans with 2 => //.
Qed.

Theorem Skp p k : p > 2 -> prime p -> 1 <= k < p.-1 -> p %| Sk k p.-1.
Admitted.
End Nagoya2013.

(*
subn1 : n - 1 = n.-1
addKn : m + n - m = n
subnDA : n - (m + p) = n - m - p
addnBA : p <= n -> m + (n - p) = m + n - p
subnK : m <= n -> n - m + m = n
prednK : 0 < n -> n.-1.+1 = n
exp1n : 1 ^ n = 1
expn0 : m ^ 0 = 1
expn1 : m ^ 1 = m
expn_gt0 : (0 < m ^ n) = (0 < m) || (n == 0)
ltn_exp2r : 0 < e -> (m ^ e < n ^ e) = (m < n)
leq_pexp2l : 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2
*)