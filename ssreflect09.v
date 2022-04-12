(* 数学：総和・二項係数 *)
From mathcomp Require Import all_ssreflect.

(* 1 有限型：fintype *)

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

(* 2 総和：bigop *)

Print addn_monoid.
(*
addn_monoid =
Monoid.Law (idm:=0) (operator:=addn) addnA add0n addn0
	 : Monoid.law 0
*)
Print Monoid.Law.
(*
Record law (T : Type) (idm : T) : Type := Law
  { operator : T -> T -> T;
	_ : associative operator;
    _ : left_id idm operator;
    _ : right_id idm operator }.
*)
Print addn_addoid.
(*
addn_addoid =
Monoid.AddLaw (mul:=muln) (add_operator:=addn_comoid) mulnDl mulnDr
	 : Monoid.add_law 0 muln
*)
Print Monoid.ComLaw.
(*
Record com_law (T : Type) (idm : T) : Type := ComLaw
  { com_operator : Monoid.law idm;  _ : commutative com_operator }.
*)
Print Monoid.AddLaw.
(*
Record add_law (T : Type) (idm : T) (mul : T -> T -> T) : Type := AddLaw
  { add_operator : Monoid.com_law idm;
	  _ : left_distributive mul add_operator;
    _ : right_distributive mul add_operator }.
*)
(* iota m n = [:: m;m+1;...;m+n-1] *)
(* は正しいけど index_iota にするとかしないといけない *)
(*
Definition \big[op/un]_(m <= i < n | P i) F i :=
  \big[op/un]_(i <- index_iota m n | P i) F i.
*)
Check big_cat_nat.
(* Monoid.law なので結合則と単位元のみ *)
(*
big_cat_nat
	 : forall (R : Type) (idx : R) (op : Monoid.law idx)
         (n m p : nat) (P : pred nat) (F : nat -> R),
       m <= n ->
       n <= p ->
       \big[op/idx]_(m <= i < p | P i) F i =
       op (\big[op/idx]_(m <= i < n | P i) F i)
         (\big[op/idx]_(n <= i < p | P i) F i)
*)
Check big_split.
(* Monoid.com_law なので交換則のみ *)
(*
big_split
	 : forall (R : Type) (idx : R) (op : Monoid.com_law idx)
         (I : Type) (r : seq I) (P : pred I) (F1 F2 : I -> R),
       \big[op/idx]_(i <- r | P i) op (F1 i) (F2 i) =
       op (\big[op/idx]_(i <- r | P i) F1 i)
         (\big[op/idx]_(i <- r | P i) F2 i)
*)

(* 3 二項係数 *)

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
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(1) = (1 + 1)^m - 2 *)
  rewrite Pascal. (* 二項公式 *)
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(1) = sum_{i<m+1} \binom{m}{i} 1^{m-i} 1^{i} - 2 *)
  transitivity ((\sum_(0 <= k < m.+1) 'C(m,k)) - 2).
    (* \sum_{k=1}^{m-1} \binom{m}{k} * S_k(1) = \sum_{k=0}^{m} \binom{m}{k} - 2 *)
    symmetry.
    rewrite (@big_cat_nat _ _ _ m) //=.
    rewrite (@big_cat_nat _ _ _ 1) //=; last by apply ltnW.
    rewrite addnAC !big_nat1 bin0 binn addKn.
    apply eq_bigr => i H. (* 各項等しい *)
    by rewrite Sk1 muln1.
  (* \sum_{k=0}^{m} \binom{m}{k} - 2 = sum_{i<m+1} \binom{m}{i} 1^{m-i} 1^{i} - 2 *)
  rewrite big_mkord.
  (* \sum_{i<m+1} \binom{m}{i} - 2 = sum_{i<m+1} \binom{m}{i} 1^{m-i} 1^{i} - 2 *)
  congr (_ - _).
  (* \sum_{i<m+1} \binom{m}{i} = sum_{i<m+1} \binom{m}{i} 1^{m-i} 1^{i} *)
  apply eq_bigr => i _. (* 各項等しい *)
  (* \binom{m}{i} * \binom{m}{i} 1^{m-i} 1^{i} *)
  by rewrite !exp1n !muln1.
Qed.

Search (_ ^ _) "exp". (* 自然数の指数関数 expn に関する様々な補題 *)

Lemma Tm2 : Tm 2 = 3^m - 3.
Proof.
  rewrite /Tm.
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = 3^m - 3 *)
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
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = 2^m - 2 + (3^m - 1 - 2^m) *)
  rewrite -Tm1.
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = T_m(1) + (3^m - 1 - 2^m) *)
  rewrite [in 3^m](_ : 3 = 1+2) //.
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = T_m(1) + ((1+2)^m - 1 - 2^m) *)
  rewrite Pascal.
  (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = T_m(1) + (\sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i) - 1 - 2^m) *)
  transitivity (Tm 1 + (\sum_(1 <= k < m) 'C(m,k) * 2^k)).
    (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = T_m(1) + (\sum_{k=1}^{m-1} \binom{m,i}  2^k) *)
    rewrite -big_split /=.
    (* \sum_{k=1}^{m-1} \binom{m}{k} S_k(2) = \sum_{i=1}^{m-1} ( \binom{m,i} S_i(1) + \binom{m,i} 2^i) *)
    apply eq_bigr => i _. (* 各項等しい *)
    (* \binom{m}{i} S_i(2) = \binom{m,i} S_i(1) + \binom{m,i} 2^i *)
    rewrite /Sk !big_cons !big_nil.
    by rewrite !addn0 -mulnDr.
  (* T_m(1) + (\sum_{k=1}^{m-1} \binom{m,i} 2^k) = T_m(1) + (\sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i) - 1 - 2^m) *)
  congr (_ + _).
  (* \sum_{k=1}^{m-1} \binom{m,i} 2^k = \sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i - 1 - 2^m *)
  transitivity ((\sum_(0 <= k < m.+1) 'C(m,k) * 2^k) - 1 - 2^m).
    (* \sum_{k=1}^{m-1} \binom{m,i} 2^k = \sum_{k=0}^{m} \binom{m,k} 2^k - 1 - 2^m *)
    symmetry.
    rewrite (@big_cat_nat _ _ _ 1) //=.
    rewrite addnC big_nat1 bin0 expn0 mul1n addnK.
    rewrite (@big_cat_nat _ _ _ m) //=; last by apply ltnW.
    by rewrite big_nat1 binn mul1n addnK.
  (* \sum_{k=0}^{m} \binom{m,k} 2^k - 1 - 2^m = \sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i - 1 - 2^m *)
  rewrite big_mkord.
  (* \sum_{i<m+1} \binom{m,k} 2^k - 1 - 2^m = \sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i - 1 - 2^m *)
  do 2 congr (_ - _).
  (* \sum_{i<m+1} \binom{m,k} 2^k = \sum_{i<m+1} \binom{m,i}  1^{m-i} 2^i *)
  apply eq_bigr => i _. (* 各項等しい *)
  (* \binom{m,i} 2^i = \binom{m,i}  1^{m-i} 2^i *)
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

Lemma Tmp p : 2 < p -> p  %| Tm p.-1.
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

Search "dvdn".
(* dvdn_addr  forall m d n : nat, d %| m -> (d %| m + n) = (d %| n) *)
(* m = k.+1 のとき *)
(* Tm p.-1 = C'(k.+1,1) * Sk 1 (p.-1) + ... + C'(k.+1,k.-1) * Sk k.-1 p.-1 + C'(k+1,k) * Sk k p.-1 *)
(* p %| Tm p.-1 *)
(* p %| C'(k.+1,1) * Sk 1 (p.-1) + ... + C'(k.+1,k.-1) * Sk k.-1 p.-1 + C'(k+1,k) * Sk k p.-1 *)
(* 帰納法で p %| Sk 1 p.-1, ..., p %| Sk k.-1 p.-1 が言えていれば *)
Theorem Skp p k : p > 2 -> prime p -> 1 <= k < p.-1 -> p %| Sk k p.-1.
Proof.
  move=>Hp2 Hprime Hk.
  assert (m = k.+1).
  move: (Tmp p Hp2) => HTm.
  unfold Tm in HTm.
  rewrite H in HTm.
  move: Hk H HTm.
  elim: k => // k IH Hk _ .
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