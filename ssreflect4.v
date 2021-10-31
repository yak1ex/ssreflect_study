Require Import ssreflect.

Definition prod_ind (A B: Set) (P: prod A B -> Prop) :=
    fun (f: forall a b, P (pair a b)) =>
    fun p => match p as x return P x with pair a b => f a b end.
Check prod_ind.

Definition sum_ind (A B: Set) (P: sum A B -> Prop) :=
    fun (fl: forall a, P (inl _ a)) (fr: forall b, P (inr _ b))=>
    fun p => match p as x return P x
        with inl a => fl a | inr b => fr b end.
Check sum_ind.

Fixpoint nat_ind (P: nat -> Prop) (f0: P O)
    (fn: forall n, P n -> P (S n)) (n: nat) {struct n} :=
    match n as x return P x
    with O => f0 | S m => fn m (nat_ind P f0 fn m) end.
Check nat_ind.

Lemma plun0 n : n + 0 = n.
Proof.
    case: n.
    - done.
    (* forall n : nat, S n + 0 = S n*)
Restart.
    move: n.
    apply: nat_ind.
    - done.
    (* forall n : nat, n + 0 = n -> S n + 0 = S n*)
    - move => n /= -> //.
Qed.

(* 偶数の定義 *)
Inductive even : nat -> Prop :=
    | even_O : even O
    | even_SS : forall n, even n -> even (S (S n)).

(* 帰納的述語を証明する定理 *)
Theorem even_dobule n : even (n + n).
Proof.
    elim: n => /= [|n IH].
    - apply: even_O.
    - rewrite -plus_n_Sm.
      by apply: even_SS.
Qed.

(* 帰納的述語に対する帰納法もできる *)
Theorem even_plus m n : even m -> even n -> even (m + n).
Proof.
    elim: m => //=.
Restart.
    move => Hm Hn.
    elim: Hm => //= m' Hm' IH.
    by apply: even_SS.
Qed.

(* 矛盾を導き出す *)
Theorem one_not_even : ~ even 1.
Proof.
    case.
Restart.
    move H: 1 => one He. (* move H: exp => pat は H: exp = pat を作る *)
    case: He H => //.
Restart.
    move=> He.
    inversion He.
    Show Proof. (* 証明が複雑でSSReflectでは様々な理由で避ける *)
Qed.

(* 等式を導き出す *)
Theorem eq_pred m n : S m = S n -> m = n.
Proof.
    case. (* 等式を分解する *)
    done.
Qed.

Inductive and (A B : Prop) : Prop := conj : A -> B -> and A B.
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> or A B | or_intror : B -> or A B.

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex A P.

Inductive False : Prop := .

Print False_ind.

Theorem contradict (P Q : Prop) : P -> ~P -> Q.
Proof. move=> p. elim. exact: p. Qed.

(* 練習問題 3.1 *)
Module Odd.
Inductive odd : nat -> Prop :=
    | odd_1 : odd 1
    | odd_SS : forall n, odd n -> odd (S (S n)).

Theorem even_odd n : even n -> odd (S n).
Proof.
    elim: n => /= [_|n IH evSn].
    - apply: odd_1.
    - elim: evSn => [|n0 IH1 IH2].
      + apply: odd_1.
      + apply: odd_SS IH2.
Qed.

Lemma zero_not_odd : ~ odd 0.
Proof.
    move H: 0 => zero Ho.
    case: Ho H => //.
Qed.

Theorem odd_even n : odd n -> even (S n).
Proof.
    elim: n => [odO|n IH odSn].
    - elim: zero_not_odd. exact: odO.
    - elim: odSn.
      + apply: even_SS even_O.
      + move => n0 Ho He. apply: even_SS He.
Qed.