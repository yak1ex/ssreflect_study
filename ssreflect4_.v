(* settings.json "coqtop.args": ["-impredicative-set"], *)
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
Restart.
    elim.
    - apply: odd_1.
    - move => m _ IH.
      by apply: odd_SS.
Restart.
    elim.
    - apply: odd_1.
    - move => m _.
      exact: odd_SS.
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
    - elim: odSn =>[|n0 Ho He].
      + apply: even_SS even_O.
      + apply: even_SS He.
Restart.
    elim => [|n' IHn' H].
    - by apply/even_SS/even_O.
    - by apply/even_SS.
Restart.
    elim => [|n' IHn' H].
    - move: even_SS even_O. apply. (* focus においた分が apply *)
    - move: even_SS. by apply.
Restart.
    elim.
    - apply/even_SS/even_O.
    - move => n' _.
      apply/even_SS. 
Qed.

Theorem even_not_odd n : even n -> ~ odd n.
Proof.
    elim: n => [ev0|n IH evSn].
    - exact zero_not_odd.
    - elim: evSn => [|n0 He Ho].
      + exact zero_not_odd.
      + move H: (S (S n0)) => SSn0 HoSSn0.
        case: HoSSn0 H => // n1 Ho1 Heq.
        have Heq' : (n0 = n1).
        apply: eq_add_S. by apply: eq_add_S.
        apply: Ho. rewrite -> Heq'. apply: Ho1.
Restart.
    elim.
    - move H: 0 => zero Ho.
      case: Ho H => //=.
    - move => m.
      move H: (S (S m)) => ssm ev_m nodd oddSS.
      apply: nodd.
      case: oddSS H => //=.
      move => n' oddm sseq.
      case: sseq.
      by move ->.
Restart.
    elim.
    - move H: 0 => zero Ho.
      by case: Ho H.
    - move => m.
      move H: (S (S m)) => ssm ev_m nodd oddSS.
      apply: nodd.
      case: oddSS H => //.
      move => n' oddm sseq.
      case: sseq.
      by move ->.
Restart.
    elim.
    - move H: 0 => zero Ho.
      by case: Ho H.
    - move => m.
      move H: (S (S m)) => ssm ev_m nodd oddSS.
      apply: nodd.
      by case: oddSS H => // n' oddm [] ->. 
Restart.
    elim.
    - move H: 0 => zero Ho.
      by case: Ho H.
    - move => m.
      move H: (S (S m)) => ssm ev_m nodd oddSS.
      apply: nodd.
      by case: oddSS H => // n' oddm [] ->. 
Qed.
End Odd.

Section SystemF.
Definition Fand P Q := forall X : Prop, (P -> Q -> X) -> X.
Check and_ind.
Definition For P Q := forall X : Prop, (P -> X) -> (Q -> X) -> X.
Definition Ffalse := forall X : Prop, X.
Definition Ftrue := forall X : Prop, (X -> X).
Definition Feq {T} (x y : T) := forall P, Fand (P x -> P y) (P y -> P x).
Definition Fex {T} (P : T -> Prop) := forall X : Prop, (forall x, P x -> X) -> X.

Theorem Fand_ok (P Q : Prop) : Fand P Q <-> P /\ Q.
Proof.
    split => [pq | [p q] X].
    - split; by apply : pq.
    - by apply.
Qed.

Theorem For_ok (P Q : Prop) : For P Q <-> P \/ Q. 
Proof.
    split => [pq | [p|q] X px qx].
    - apply: pq => H; by [left|right].
    - apply/px/p.
    - apply/qx/q.
Restart.
    split => [pq | pq X px qx].
    - apply: pq. by left. by right.
    - move: pq. case; done.
Restart.
    split => [pq | pq X px qx].
    - apply: pq. by left. by right.
    - by case: pq.
Qed.

Theorem Ffalse_ok : Ffalse <-> False.
Proof.
    split => [ | []].
    - apply.
Restart.
    split => //. apply.
Qed.
 
Theorem Ftrue_ok : Ftrue <-> True.
Proof.
    split => [|[]] //.
Qed.
Theorem Feq_ok T (x y : T) : Feq x y <-> x = y.
Proof.
    split => [H|H].
    - apply: (H (fun x => x = y)) => _ -> //.
    - rewrite H /Feq /Fand => P X.
      apply => HP //.
Restart.
    split =>[/(_ (fun x => x = y))|-> P X].
    - apply =>_. exact. (* by apply *)
    - exact. 
Restart.
    split => [H|H].
    - apply: (H (fun x => x = y)) => _ -> //.
    - rewrite H /Feq /Fand => P X.
      exact. (* exact で通る *)
Qed.
Theorem Fex_ok T (P : T -> Prop) : Fex P <-> exists x, P x.
Proof.
    rewrite /Fex.
    split => [H|[x Hx] X HP].
    - apply: H => x Px. exists x. exact.
    - apply/(HP x)/Hx.
Restart.
    split => [|[x Px] X].
    - apply => x Px. by exists x.
    - apply. exact Px.
Restart.
    split => [|[x Px] X].
    - apply => x Px. by exists x.
    - move /(_ _ Px). done.
Restart.
    split => [|[x Px] X /(_ _ Px)] //.
    - apply => x Px. by exists x.
Qed.

Definition Nat := forall X : Set, (X -> X) -> X -> X.
Definition Zero : Nat := fun X f x => x.
Definition Succ (N: Nat) : Nat := fun X f x => f (N X f x).
Definition Plus (M N : Nat) : Nat := fun X f x => M X f (N X f x).
Definition Mult (M N : Nat) : Nat := fun X f x => M X (N X f) x.
(* こちらの定義はより直感的 *)
(*
Definition Plus' (M N : Nat) : Nat := M Nat Succ N. (* 1をM回足す *)
Definition Mult' (M N : Nat) : Nat := M Nat (Plus' N) Zero. (* NをM回足す *)
*)

Fixpoint Nat_of_nat n : Nat := (* 自然数をNatに変換 *)
    match n with 0 => Zero | S m => Succ (Nat_of_nat m) end.

(* Natの元の等価性は適用された物を比較するべき *)
Definition eq_Nat (M N : Nat) := forall X f x, M X f x = N X f x.
Definition eq_Nat_fun F f := forall n,
    eq_Nat (F (Nat_of_nat n)) (Nat_of_nat (f n)).
Definition eq_Nat_op Op op := forall m n,
    eq_Nat (Op (Nat_of_nat m) (Nat_of_nat n)) (Nat_of_nat (op m n)).
Check eq_Nat. (* Nat -> Nat -> Prop *)
Check eq_Nat_fun. (* (Nat -> Nat) -> (nat -> nat) -> Prop *)
Check eq_Nat_op. (* (Nat -> Nat -> Nat) -> (nat -> nat -> nat) -> Prop *)

Theorem Succ_ok : eq_Nat_fun Succ S.
Proof. by elim.
Restart.
    by [].
Restart.
    move=> n X f x.
    reflexivity.
Qed. (* 実は自明 *)

Theorem Plus_ok : eq_Nat_op Plus plus.
Proof.
    move=> m n X f x.
    elim: m x => //= m IH x.
    by rewrite Succ_ok /= [in RHS]/Succ -IH.
Restart.
    move=> m n X f x.
    elim: m x.
    - move => //.
    - move => //= m IH x.
      rewrite Succ_ok.
      rewrite /=.
      rewrite [in RHS]/Succ.
      rewrite -IH.
      done.
Restart.
    elim=>[|m IHm]//= n X f x. by rewrite Succ_ok /= /Succ -IHm.
Qed.

Theorem Mult_ok : eq_Nat_op Mult mult.
Proof.
    move => m n X f x.
    elim: m x => //= m IH x.
    by rewrite -Plus_ok/Plus/Mult/Succ -IH/Mult.
Restart.
    elim=>[|m IHm]//= n X f x. by rewrite -Plus_ok /= /Plus -IHm.
Restart.
    elim=>[|m IHm]//= n X f x.
    rewrite -Plus_ok /=.
    rewrite /=.
    rewrite /Plus.
    rewrite -IHm.
    done.
Qed.

(* elim: a b c => x y z は
   move: c. move: b. move: a.
   (* この時点で a -> b -> c -> _ になってる *)
   elim.
   move => x. move => y. move => z. *)

Definition Pow (M N : Nat) := fun X => N _ (M X). (* MのN乗 *)
Check Pow. 
Fixpoint pow m n := match n with 0 => 1 | S n => m * pow m n end.

Lemma Nat_of_nat_eq : forall n X f1 f2 x,
    (forall y, f1 y = f2 y) ->
    Nat_of_nat n X f1 x = Nat_of_nat n X f2 x.
Proof.
    move=>n X f1 f2 x Heq.
    elim n => //= n' Heq'.
    by rewrite /Succ Heq' Heq.
Qed.
Theorem Pow_ok : eq_Nat_op Pow pow.
Proof.
    move=> m n X f x.
    elim: n x => //= n IH x.
    rewrite -Mult_ok/Mult/Pow/Succ.
    apply: Nat_of_nat_eq => y.
    by rewrite -IH/Pow.
Restart.
    move=> m n X f x.
    elim: n x => //= n IH x.
    rewrite -Mult_ok/Mult/Pow/Succ.
    apply: Nat_of_nat_eq => y.
    apply IH.
Restart.
    move=> m n X f x.
    elim: n x => //= n IH x.
    rewrite -Mult_ok/Mult/Pow/Succ.
    apply: Nat_of_nat_eq => y.
    by rewrite -IH-/(Pow _ _ _ _ _).
Qed.

Section ProdSum. (* 値の対と直和も定義できる *)
    Variable X Y : Prop.
    Definition Prod := forall Z : Prop, (X -> Y -> Z) -> Z.
    Definition Pair (x : X) (y : Y) : Prod := fun Z f => f x y.
    Definition Fst (p : Prod) := p _ (fun x y => x).
    Definition Snd (p : Prod) := p _ (fun x y => y).
    Definition Sum := forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
    Definition InL x : Sum := fun Z f g => f x.
    Definition InR x : Sum := fun Z f g => g x.
End ProdSum.
Arguments Pair [X Y]. Arguments Fst [X Y]. Arguments Snd [X Y].
Arguments InL [X Y]. Arguments InR [X Y]. (* 型引数を省略できるようにする *)

(*
Definition Pred (N : Nat) := (* 前者関数の定義は工夫が必要 *)
    Fst (N _ (fun p : Prod Nat Nat => Pair (Snd p) (Succ (Snd p)))
        (Pair Zero Zero)).

Theorem Pred_ok : eq_Nat_fun Pred pred.
Proof. (* 自分でできなかった *)
    rewrite /eq_Nat_fun /eq_Nat.
    move => n X f x.
    elim: n.
    - done.
    - move => n IH.
      case n as [|n'].
      + done.
      + have pSSp: forall m:nat, m <> 0 -> eq_Nat (Nat_of_nat (Nat.pred (S m)))
        (Nat_of_nat (S (Nat.pred m))).
        * move => m notz.
          by case m as [|m'].
        * rewrite pSSp.
          -- done.
          -- rewrite -Succ_ok.
             rewrite /Succ.
             rewrite -IH.
             (* rewrite -[in RHS]/(Succ _ _ _ _). *)
             done.
Restart.
    case =>[|n]//= X f x.
    elim : n =>[|n IHn]//=.
    by rewrite /Succ -IHn.
Restart.
    case; first by [].
    elim.
    by [].
    move=> /= n IH X f x /=.
    rewrite [in RHS]/Succ.
    rewrite -IH.
    by [].
Qed.
*)

(* Nat が Set で定義されているときだけ証明可能 *)
Lemma Nat_of_nat_ok : forall n, Nat_of_nat n _ S O = n.
Proof.
    elim => // n IHn /=.
    by rewrite /Succ IHn.
Qed.
