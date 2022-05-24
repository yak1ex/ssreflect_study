Require Import ZArith Extraction.
From mathcomp Require Import all_ssreflect.

(* Simple Calculator *)

Module Simple.
Inductive expr : Set := (* 変数を含む整数式 *)
  | Cst of Z
  | Var of nat
  | Add of expr & expr
  | Min of expr
  | Mul of expr & expr.

Fixpoint eval (env : list Z) (e : expr) : Z := (* 評価関数 *)
  match e with
  | Cst x => x
  | Var n => nth 0 env n (* 変数の値は env で与えられる *)
  | Add e1 e2 => eval env e1 + eval env e2
  | Min e1 => 0-eval env e1
  | Mul e1 e2 => eval env e1 * eval env e2
  end%Z.

(* (x+3)*4 for x=2 *)(* not in PDF *)
Eval compute in eval [:: 2%Z] (Mul (Add (Var 0) (Cst 3)) (Cst 4)).

Inductive code : Set := (* 逆ポーランド記法による計算譜 *)
  | Cimm of Z
  | Cget of nat
  | Cadd
  | Cmin
  | Cmul.

Fixpoint eval_code (stack : list Z) (l : list code) :=
  match l with
  | nil => stack
  | c :: l' =>
    let stack' := (* 各コマンドがスタックを変える *)
        match c, stack with
        | Cimm x, _ => x :: stack
        | Cget n, _ => nth 0 stack n :: stack
        | Cadd, x :: y :: st => x+y :: st
        | Cmin, x :: st => 0-x :: st
        | Cmul, x :: y :: st => x*y :: st
        | _, _ => nil
        end%Z
    in eval_code stack' l'
  end.

(* not in PDF *)
Eval compute in eval_code [:: 2%Z] [:: Cget 0; Cimm 3; Cadd; Cimm 4; Cmul].

Fixpoint compile d (e : expr) : list code :=
  match e with
  | Cst x => [:: Cimm x]
  | Var n => [:: Cget (d+n)]
  | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
  | Min e1 => compile d e1 ++ [:: Cmin]
  | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
  end.

(* not in PDF *)
Eval compute in compile 0 (Mul (Add (Var 0) (Cst 3)) (Cst 4)).
Eval compute in
  eval_code [:: 2%Z] (compile 0 (Mul (Add (Var 0) (Cst 3)) (Cst 4))).

Lemma eval_code_cat stack l1 l2 :
  eval_code stack (l1 ++ l2) = eval_code (eval_code stack l1) l2.
Proof. by elim: l1 stack => //=. Qed.

(* drop n s == s minus its first n items ([::] if size s <= n)     *)(* this comment is not in PDF *)
Theorem compile_correct e d stack : (* コンパイラの正しさ *)
  eval_code stack (compile d e) = eval (drop d stack) e :: stack.
Proof.
  elim: e d stack => //= [n|e1 IHe1 e2 IHe2|e IHe|e1 IHe1 e2 IHe2] d stack.
  - by rewrite nth_drop. (* nht_drop は ssreflect.seq *)
  - by rewrite eval_code_cat IHe2 eval_code_cat IHe1.
  - by rewrite eval_code_cat IHe.
  - by rewrite eval_code_cat IHe2 eval_code_cat IHe1.
Qed.
End Simple.

(* Iterating calculator *)

Module Iterator.
Inductive expr : Set :=
  | Cst of Z
  | Var of nat
  | Add of expr & expr
  | Min of expr
  | Mul of expr & expr.

Fixpoint eval (env : list Z) (e : expr) : Z :=
  match e with
  | Cst x => x
  | Var n => nth 0 env n
  | Add e1 e2 => eval env e1 + eval env e2
  | Min e1 => 0-eval env e1
  | Mul e1 e2 => eval env e1 * eval env e2
  end%Z.

Inductive cmd : Set :=
  | Assign of nat & expr (* env[n] に結果を入れる *)
  | Seq of cmd & cmd (* 順番に実行 *)
  | Repeat of expr & cmd. (* n 回繰り返す *)

(* not in PDF *)
(* r <- 1; repeat (i-1) {r <- i * r; i <- i-1} *)

Definition fact :=
  Seq (Assign 1 (Cst 1))
      (Repeat (Add (Var 0) (Cst (-1)))
         (Seq (Assign 1 (Mul (Var 0) (Var 1)))
              (Assign 0 (Add (Var 0) (Cst (-1)))))).

Print Z.
Print positive.
Print iter.

Fixpoint eval_cmd (env : list Z) (c : cmd) : list Z :=
  match c with
  | Assign n e => set_nth 0%Z env n (eval env e)
  | Seq c1 c2 => eval_cmd (eval_cmd env c1) c2
  | Repeat e c =>
    if eval env e is Zpos n (* seq の iter を使う *)
    then iter (Pos.to_nat n) (fun e => eval_cmd e c) env
    else env
  end.

Eval compute in eval_cmd [:: 5%Z] fact.

Inductive code : Set :=
  | Cimm of Z
  | Cget of nat
  | Cadd
  | Cmin
  | Cmul
  | Cset of nat (* スタックの上を n 番目に書き込む *)
  | Crep of nat (* 次の n 個の命令ををスタックの上分繰り返す *)
  | Cnext. (* 終ったら Cnext の後ろに跳ぶ *)

Fixpoint eval_code (stack : list Z) (l : list code) :=
  match l with
  | nil => stack
  | c :: l' =>
    let stack' :=
        match c, stack with
        | Cimm x, _ => x :: stack
        | Cget n, _ => nth 0 stack n :: stack
        | Cadd, x :: y :: st => x+y :: st
        | Cmin, x :: st => 0-x :: st
        | Cmul, x :: y :: st => x*y :: st
        | Cset n, x :: st => set_nth 0%Z st n x
        | Crep _, Zpos n :: st =>
          iter (Pos.to_nat n) (fun st => eval_code st l') st
        | Crep _, _ :: st => st
        | Cnext, _ => stack
        | _, _ => nil
        end%Z
    in
    match c with
    | Crep n => eval_drop n stack' l' (* Crep の後はコードを飛ばす *)
    | Cnext => stack' (* Cnext は評価を止める *)
    | _ => eval_code stack' l' (* 他の場合は続ける *)
    end
  end
with eval_drop n st (l : list code) := (* 相互再帰 *)
  match l, n with
  | _ :: l', 0 => eval_code st l' (* このとき _ は Cnext のはず *)(* じゃそこまで捨てればいいのではと思ったけど多重ループが駄目そう？ *)
  | _ :: l', S n' => eval_drop n' st l'
  | [::], _ => st
  end.

Fixpoint compile d (e : expr) : list code :=
  match e with
  | Cst x => [:: Cimm x]
  | Var n => [:: Cget (d+n)]
  | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
  | Min e1 => compile d e1 ++ [:: Cmin]
  | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
  end.
(* どの expr でも stack は 1 つ伸びる *)

Fixpoint compile_cmd (c : cmd) : list code :=
  match c with
  | Assign n e => compile 0 e ++ [:: Cset n]
  | Seq c1 c2 => compile_cmd c1 ++ compile_cmd c2
  | Repeat e c =>
      let l := compile_cmd c in
      compile 0 e ++ [:: Crep (length l)] ++ l ++ [:: Cnext]
  end.
(* cmd の文脈では stack は素の状態 *)

Eval compute in compile_cmd fact.
Eval compute in eval_code [:: 5%Z] (compile_cmd fact).

Definition neutral c :=
  match c with Cnext | Crep _ => false | _ => true end.

Inductive balanced : list code -> Prop := (* Crep と Cnext の対応が取れている *)
  | Bneutral : forall c, neutral c = true -> balanced [:: c]
  | Bcat : forall l1 l2, balanced l1 -> balanced l2 -> balanced (l1 ++ l2)
  | Brep : forall l, balanced l ->
                     balanced (Crep (length l) :: l ++ [:: Cnext]).

Hint Constructors balanced.

Lemma eval_drop_cat st l1 l2 :
  eval_drop (length l1) st (l1 ++ Cnext :: l2) = eval_code st l2.
Proof.
  by elim: l1 => //.
Restart.
  by elim: l1.
Qed.

Check eq_iter. (* 証明に使える *)
Lemma eval_code_cat stack (l1 l2 : seq code) :
  balanced l1 ->
  eval_code stack (l1 ++ l2) =
  eval_code (eval_code stack l1) l2.
Proof.
  move => Hb.
  elim: Hb l2 stack => [c Hn|la lb Hba IHa Hbb IHb|l Hb IH] l2 stack.
  - case: c Hn => //.
  - by rewrite -catA !IHa IHb.
  - rewrite /= -catA !eval_drop_cat /=.
    case stack => // z l'.
    case z => // => p.
    have Heq: (eval_code^~ (l ++ Cnext :: l2)) =1 (eval_code^~ (l ++ [:: Cnext])).
      move => st. rewrite !IH //=.
    by rewrite (eq_iter Heq (Pos.to_nat p)).
Restart.
  move=>balance.
  move: stack l2.
  elim: l1 / balance.
  - by case.
  - move=> l1 l2 balance1 IH1 balance2 IH2 stack l3.
    by rewrite IH1 -catA IH1 IH2.
  - move=> l1 balance IH stack l2.
    rewrite [LHS]/=.
    rewrite -catA.
    rewrite eval_drop_cat.
    case: stack => //=.
    + by rewrite eval_drop_cat.
    + move => n l.
      rewrite eval_drop_cat.
      case: n => //= p.
      congr (eval_code _).
      apply: eq_iter => st.
      rewrite !IH //.
Qed.

Lemma compile_balanced n e : balanced (compile n e).
Proof. by elim: e n => /=; auto. Qed.

Theorem compile_correct e d stack :
  eval_code stack (compile d e) = eval (drop d stack) e :: stack.
Proof.
  elim: e d stack => //= [n|e1 IH1 e2 IH2|e IH|e1 IH1 e2 IH2] d stack.
  - by rewrite nth_drop.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH2.
    rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH1 //.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH //.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH2.
    rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH1 //.
Qed.

Lemma compile_cmd_balanced c : balanced (compile_cmd c).
Proof. by elim: c => /=; auto using compile_balanced. Qed.

Hint Resolve compile_balanced compile_cmd_balanced.

Theorem compile_cmd_correct c stack :
  eval_code stack (compile_cmd c) = eval_cmd stack c.
Proof.
  elim: c stack => //= [n e|c1 IH1 c2 IH2|e c IH] stack.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)).
    rewrite compile_correct drop0 //=.
  - by rewrite (eval_code_cat _ _ _ (compile_cmd_balanced _)) IH1 IH2.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)).
    rewrite compile_correct drop0 //=.
    rewrite eval_drop_cat /=.
    have Heq: (eval_code^~ (compile_cmd c ++ [:: Cnext])) =1 (eval_cmd^~ c).
      move => st.
      by rewrite (eval_code_cat _ _ _ (compile_cmd_balanced _)) /= IH.
    case (eval stack e) => // p.
    by rewrite (eq_iter Heq (Pos.to_nat p)).
Qed.
End Iterator.

Extraction Iterator.eval_code.

(* 練習問題の2 If of expr & cmd *)

Module Iterator'.
Inductive expr : Set :=
  | Cst of Z
  | Var of nat
  | Add of expr & expr
  | Min of expr
  | Mul of expr & expr.

Fixpoint eval (env : list Z) (e : expr) : Z :=
  match e with
  | Cst x => x
  | Var n => nth 0 env n
  | Add e1 e2 => eval env e1 + eval env e2
  | Min e1 => 0-eval env e1
  | Mul e1 e2 => eval env e1 * eval env e2
  end%Z.

Inductive cmd : Set :=
  | Assign of nat & expr (* env[n] に結果を入れる *)
  | Seq of cmd & cmd (* 順番に実行 *)
  | Repeat of expr & cmd (* n 回繰り返す *)
  | If of expr & cmd. (* n > 0 で実行 *)(* 追加 *)

(* not in PDF *)
(* r <- 1; repeat (i-1) {r <- i * r; i <- i-1} *)

Definition fact :=
  Seq (Assign 1 (Cst 1))
      (Repeat (Add (Var 0) (Cst (-1)))
         (Seq (Assign 1 (Mul (Var 0) (Var 1)))
              (Assign 0 (Add (Var 0) (Cst (-1)))))).

Print Z.
Print positive.
Print iter.

Fixpoint eval_cmd (env : list Z) (c : cmd) : list Z :=
  match c with
  | Assign n e => set_nth 0%Z env n (eval env e)
  | Seq c1 c2 => eval_cmd (eval_cmd env c1) c2
  | Repeat e c =>
    if eval env e is Zpos n (* seq の iter を使う *)
    then iter (Pos.to_nat n) (fun e => eval_cmd e c) env
    else env
  | If e c =>
    if eval env e is Zpos n then eval_cmd env c else env
  end.

Eval compute in eval_cmd [:: 5%Z] fact.

Inductive code : Set :=
  | Cimm of Z
  | Cget of nat
  | Cadd
  | Cmin
  | Cmul
  | Cset of nat (* スタックの上を n 番目に書き込む *)
  | Crep of nat (* 次の n 個の命令ををスタックの上分繰り返す *)
  | Cif of nat (* 次の n この命令をスタック先頭が正なら実行 *)(* 追加 *)
  | Cnext. (* 終ったら Cnext の後ろに跳ぶ *)

Fixpoint eval_code (stack : list Z) (l : list code) :=
  match l with
  | nil => stack
  | c :: l' =>
    let stack' :=
        match c, stack with
        | Cimm x, _ => x :: stack
        | Cget n, _ => nth 0 stack n :: stack
        | Cadd, x :: y :: st => x+y :: st
        | Cmin, x :: st => 0-x :: st
        | Cmul, x :: y :: st => x*y :: st
        | Cset n, x :: st => set_nth 0%Z st n x
        | Crep _, Zpos n :: st =>
          iter (Pos.to_nat n) (fun st => eval_code st l') st
        | Crep _, _ :: st => st
        | Cif _, Zpos n :: st => eval_code st l' (* 追加 *)
        | Cif _, _ :: st => st (* 追加 *)
        | Cnext, _ => stack
        | _, _ => nil
        end%Z
    in
    match c with
    | Crep n => eval_drop n stack' l' (* Crep の後はコードを飛ばす *)
    | Cif n => eval_drop n stack' l' (* Cif の後はコードを飛ばす *)(* 追加 *)
    | Cnext => stack' (* Cnext は評価を止める *)
    | _ => eval_code stack' l' (* 他の場合は続ける *)
    end
  end
with eval_drop n st (l : list code) := (* 相互再帰 *)
  match l, n with
  | _ :: l', 0 => eval_code st l' (* このとき _ は Cnext のはず *)(* じゃそこまで捨てればいいのではと思ったけど多重ループが駄目そう？ *)
  | _ :: l', S n' => eval_drop n' st l'
  | [::], _ => st
  end.

Fixpoint compile d (e : expr) : list code :=
  match e with
  | Cst x => [:: Cimm x]
  | Var n => [:: Cget (d+n)]
  | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
  | Min e1 => compile d e1 ++ [:: Cmin]
  | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
  end.
(* どの expr でも stack は 1 つ伸びる *)

Fixpoint compile_cmd (c : cmd) : list code :=
  match c with
  | Assign n e => compile 0 e ++ [:: Cset n]
  | Seq c1 c2 => compile_cmd c1 ++ compile_cmd c2
  | Repeat e c =>
      let l := compile_cmd c in
      compile 0 e ++ [:: Crep (length l)] ++ l ++ [:: Cnext]
  | If e c =>
    let l := compile_cmd c in
    compile 0 e ++ [:: Cif (length l)] ++ l ++ [:: Cnext] (* 追加 *)
end.
(* cmd の文脈では stack は素の状態 *)

Eval compute in compile_cmd fact.
Eval compute in eval_code [:: 5%Z] (compile_cmd fact).

Definition neutral c :=
  match c with Cnext | Crep _ | Cif _ => false | _ => true end. (* 追加 *)

Inductive balanced : list code -> Prop := (* Crep と Cnext の対応が取れている *)
  | Bneutral : forall c, neutral c = true -> balanced [:: c]
  | Bcat : forall l1 l2, balanced l1 -> balanced l2 -> balanced (l1 ++ l2)
  | Brep : forall l, balanced l ->
                     balanced (Crep (length l) :: l ++ [:: Cnext])
  | Bif : forall l, balanced l ->
                     balanced (Cif (length l) :: l ++ [:: Cnext]). (* 追加 *)

Hint Constructors balanced.

Lemma eval_drop_cat st l1 l2 :
  eval_drop (length l1) st (l1 ++ Cnext :: l2) = eval_code st l2.
Proof.
  by elim: l1 => //.
Restart.
  by elim: l1.
Qed.

Check eq_iter. (* 証明に使える *)
Lemma eval_code_cat stack (l1 l2 : seq code) :
  balanced l1 ->
  eval_code stack (l1 ++ l2) =
  eval_code (eval_code stack l1) l2.
Proof.
  move => Hb.
  elim: Hb l2 stack => [c Hn|la lb Hba IHa Hbb IHb|l Hb IH|l Hb IH] l2 stack.
  - case: c Hn => //.
  - by rewrite -catA !IHa IHb.
  - rewrite /= -catA !eval_drop_cat /=.
    case stack => // z l'.
    case z => // p.
    have Heq: (eval_code^~ (l ++ Cnext :: l2)) =1 (eval_code^~ (l ++ [:: Cnext])).
      move => st. rewrite !IH //=.
    by rewrite (eq_iter Heq (Pos.to_nat p)).
  - (* 追加 *)
    rewrite /= -catA !eval_drop_cat /=.
    case stack => // z l'.
    case z => // p.
    by rewrite !IH.
Qed.

Lemma compile_balanced n e : balanced (compile n e).
Proof. by elim: e n => /=; auto. Qed.

Theorem compile_correct e d stack :
  eval_code stack (compile d e) = eval (drop d stack) e :: stack.
Proof.
  elim: e d stack => //= [n|e1 IH1 e2 IH2|e IH|e1 IH1 e2 IH2] d stack.
  - by rewrite nth_drop.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH2.
    rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH1 //.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH //.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH2.
    rewrite (eval_code_cat _ _ _ (compile_balanced _ _)) IH1 //.
Qed.

Lemma compile_cmd_balanced c : balanced (compile_cmd c).
Proof. by elim: c => /=; auto using compile_balanced. Qed.

Hint Resolve compile_balanced compile_cmd_balanced.

Theorem compile_cmd_correct c stack :
  eval_code stack (compile_cmd c) = eval_cmd stack c.
Proof.
  elim: c stack => //= [n e|c1 IH1 c2 IH2|e c IH|e c IH] stack.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)).
    rewrite compile_correct drop0 //=.
  - by rewrite (eval_code_cat _ _ _ (compile_cmd_balanced _)) IH1 IH2.
  - rewrite (eval_code_cat _ _ _ (compile_balanced _ _)).
    rewrite compile_correct drop0 //=.
    rewrite eval_drop_cat /=.
    have Heq: (eval_code^~ (compile_cmd c ++ [:: Cnext])) =1 (eval_cmd^~ c).
      move => st.
      by rewrite (eval_code_cat _ _ _ (compile_cmd_balanced _)) /= IH.
    case (eval stack e) => // p.
    by rewrite (eq_iter Heq (Pos.to_nat p)).
  - (* 追加 *)
    rewrite (eval_code_cat _ _ _ (compile_balanced _ _)).
    rewrite compile_correct drop0 /= eval_drop_cat /=.
    case (eval stack e) => // p.
    by rewrite -IH eval_code_cat.
Qed.
(* 整数の商 *)
(* m: var 0, n: var 1, absm: var 2, sgn: var 3, q: var 4, m = qn + r, 0 <= r < |n| *)
(* n = 0 ==> undefined *)
(* m = 0 ==> q = 0 *)
(*  4 =  1 *  3 + 1 *)
(* -4 = -2 *  3 + 2 *)
(* -4 =  2 * -3 + 2 *)
(*  4 = -1 * -3 + 1 *)

(* sgn = -1; if n * m > 0 then sgn = -sgn; absm = |m|;
   loop absm { if n > 0 { if n - m + 1 > 0 { n = n - m; r = r + sgn }}; if n < 0 { n = n + m; r = r + sgn }} *)
Definition div :=
  If (Mul (Var 1) (Var 1))
    (Seq (Assign 3 (Cst (-1)%Z))
      (Seq (If (Mul (Var 0) (Var 1)) (Assign 3 (Min (Var 3))))
        (Seq (If (Min (Var 1)) (Assign 1 (Min (Var 1))))
          (Seq (Assign 2 (Var 0))
            (Seq (If (Min (Var 2)) (Assign 2 (Min (Var 2))))
            (Repeat (Var 2)
                    (Seq (If (Var 0) (If (Add (Add (Var 0) (Min (Var 1))) (Cst 1%Z))
                                        (Seq (Assign 0 (Add (Var 0) (Min (Var 1))))
                                              (Assign 4 (Add (Var 4) (Var 3))))))
                          (If (Min (Var 0)) (Seq (Assign 0 (Add (Var 0) (Var 1)))
                                                  (Assign 4 (Add (Var 4) (Var 3)))))))))))).

Eval compute in eval_cmd [:: 6%Z; 2%Z] div.
Eval compute in eval_cmd [:: 10%Z; 3%Z] div.
Eval compute in eval_cmd [:: (-6)%Z; 2%Z] div.
Eval compute in eval_cmd [:: (-6)%Z; (-2)%Z] div.
Eval compute in eval_cmd [:: 6%Z; (-2)%Z] div.
Eval compute in eval_cmd [:: 4%Z; 3%Z] div.
Eval compute in eval_cmd [:: (-4)%Z; 3%Z] div.
Eval compute in eval_cmd [:: (-4)%Z; (-3)%Z] div.
Eval compute in eval_cmd [:: 4%Z; (-3)%Z] div.
Eval compute in eval_cmd [:: 4%Z; 0%Z] div.
Eval compute in eval_cmd [:: 0%Z; 1%Z] div. (* Var 4 = 0 *)
Eval compute in eval_cmd [:: 0%Z; (-1)%Z] div.
Eval compute in eval_cmd [:: 0%Z; 0%Z] div.

End Iterator'.
