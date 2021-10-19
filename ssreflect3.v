Require Import ssreflect.

Definition one : nat := 1.

(* Definition one := 1. *)

Definition one' := 1.
Print one'.

Definition double x := x + x.
Print double.

Eval compute in double 2.

Definition double' := fun x => x + x.
Print double'.

Definition quad x := let y := double x in 2 * y.
Eval compute in quad 2.

Definition quad' x := double (double x).
Eval compute in quad' 2.

Definition triple x :=
    let double x := x + x in
    double x + x.
Eval compute in triple 3.

Inductive janken : Set :=
| gu
| choki
| pa.

Definition weakness t :=
    match t with
    | gu => pa
    | choki => gu
    | pa => choki
    end.
Eval compute in weakness pa.

Print bool.
Print janken.

Definition wins t1 t2 :=
    match t1, t2 with
    | gu, choki => true
    | choki, pa => true
    | pa, gu => true
    | _, _ => false
    end.

Check wins.
Eval compute in wins gu pa.

Lemma weakness_wins t1 t2 :
    wins t1 t2 = true <-> weakness t2 = t1.
Proof.
    split.
    - by case: t1; case: t2.
    - move => <-; by case: t2.
Qed.

Module MyNat. (* nat を新しく定義 *)
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(*
Fixpoint plus (m n : nat) {struct m} : nat := (* 帰納法の対象を明示する 減らないとエラー *)
    match m with
    | O => n
    | S m' => S (plus m n)
    end.
*)

Fixpoint plus (m n : nat) {struct m} : nat := (* 同じ型の引数をまとめる *)
    match m with
    | O => n
    | S m' => S (plus m' n)
    end.

Print plus.
Check plus (S (S O)) (S O).
Eval compute in plus (S (S O)) (S O).

Fixpoint mult (m n : nat) {struct m} : nat :=
    match m with
    | O => O
    | S m' => plus n (mult m' n)
    end.
Eval compute in mult (S (S O)) (S O).
Eval compute in mult (S (S (S O))) (S (S O)).
End MyNat.

Check nat_ind.

Lemma plusnS m n : m + S n = S (m + n).
Proof.
    elim: m => /=.
    - done.
    - move => m IH.
      by rewrite IH.
Restart.
    elim: m => /=.
    - done.
    - move => m -> //.
Restart.
    elim: m => /= [|m ->] //.
Qed.

Lemma plusSn m n : S m + n = S (m + n).
Proof.
    rewrite /=. done.
    Show Proof.
Qed.

Lemma plusn0 n : n + 0 = n.
Proof.
    by rewrite /=.
Qed.
Lemma plusC m n : m + n = n + m.
Proof.
    elim n => /= [|o <-] //.
Qed.
Lemma plusA m n p : m + (n + p) = (m + n) + p.
Proof.
    elim m => /= [|q <-] //.
Qed.

Lemma multnS m n : m * S n = m + m * n.
Proof.
    elim: m => /= [|m ->] //.
    by rewrite !plusA [n + m]plusC.
Qed.

Lemma multn0 n : n * 0 = 0.
Proof.
    elim n.
    - done.
    - move => m //.
Restart.
    elim: n => [|m] //.
Qed.
Lemma multC m n : m * n = n * m.
Proof.
    elim m.
    - done.
    - move => o /= ->.
      by rewrite multnS.
Restart.
    elim: m => /= [|o ->] //.
    by rewrite multnS.
Qed.
Lemma multnDr m n p : (m + n) * p = m * p + n * p.
Proof.
    elim m.
    - done.
    - move => o /= ->.
      by rewrite plusA.
Restart.
    elim: m => /= [|o ->] //.
    by rewrite plusA.
Qed.
Lemma multA m n p : m * (n * p) = (m * n) * p.
Proof.
    elim m.
    - done.
    - move => /= q ->.
      by rewrite multnDr.
Restart.
    elim: m => /= [|q ->] //.
    by rewrite multnDr.
Qed.

Fixpoint sum n :=
    if n is S m then n + sum m else 0.
Print sum.

Lemma double_sum n : 2 * sum n = n * (n + 1).
Proof.
    elim n.
    - done.
    - move => m.
      rewrite plusSn multnS [S m * (m + 1)]multC multnS [(m + 1) * m]multC.
      move => <- //=.
      rewrite -plusnS -plusnS plusn0 plusnS.
      rewrite [m + 1 + (sum m + sum m)]plusC.
      rewrite -!plusA.
      rewrite [sum m + (m + 1)]plusA.
      by rewrite [sum m + m]plusC -plusA.
Qed.
Lemma square_eq a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
Proof.
    by rewrite /= !multnDr ![_ * (a + b)]multC !multnDr [b * a]multC [0 * b]multC multn0 plusn0 !plusA.
Qed.