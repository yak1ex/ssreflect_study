From mathcomp Require Import all_ssreflect.

(* Lambda calculator *)

Module Lambda.

Inductive expr : Set :=
  | Var of nat (* De Bruijn 添字 *)
  | Abs of expr
  | App of expr & expr.

Fixpoint shift k (e : expr) := (* k番目以降の自由変数をずらす *)
  match e with
  | Var n => if k <= n then Var n.+1 else Var n
  | Abs e1 => Abs (shift k.+1 e1)
  | App e1 e2 => App (shift k e1) (shift k e2)
  end.

Fixpoint open_rec k u (e : expr) := (* 自由変数の代入 *)
  match e with
  | Var n => if k == n then u else if leq k n then Var n.-1 else e
  | Abs e1 => Abs (open_rec k.+1 (shift 0 u) e1)
  | App e1 e2 => App (open_rec k u e1) (open_rec k u e2)
  end.

Inductive reduces : expr -> expr -> Prop := (* 簡約の導出規則 *)
  | Rbeta : forall e1 e2, reduces (App (Abs e1) e2) (open_rec 0 e2 e1)
  | Rapp1 : forall e1 e2 e1',
            reduces e1 e1' -> reduces (App e1 e2) (App e1' e2)
  | Rapp2 : forall e1 e2 e2',
            reduces e2 e2' -> reduces (App e1 e2) (App e1 e2')
  | Rabs  : forall e1 e1',
            reduces e1 e1' -> reduces (Abs e1) (Abs e1').

(* 簡約関係は reduces の反射推移閉包 *)
Inductive RT_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | RTbase : forall a, RT_closure R a a
  | RTnext : forall a b c, R a b -> RT_closure R b c -> RT_closure R a c.
Hint Constructors reduces RT_closure : core.

Fixpoint reduce (e : expr) : option expr := (* 1 ステップ簡約 *)
  match e with
  | App (Abs e1) e2 => Some (open_rec 0 e2 e1)
  | App e1 e2 =>
    match reduce e1, reduce e2 with
    | Some e1', _ => Some (App e1' e2)
    | None, Some e2' => Some (App e1 e2')
    | None, None => None
    end
  | Abs e1 =>
    if reduce e1 is Some e1' then Some (Abs e1') else None
  | _ => None
  end.

Fixpoint eval (n : nat) e := (* n ステップ簡約 *)
  if n is k.+1 then
    if reduce e is Some e' then eval k e' else e
  else e.

Coercion Var : nat >-> expr. (* 自然数を変数として直接に使える *)

Definition church (n : nat) :=
  Abs (Abs (iter n (App 1) 0)). (* λf.λx.(fˆn x) *)
Eval compute in church 3.
(*
= Abs (Abs (App 1 (App 1 (App 1 0)))) : expr
*)

Definition chadd := Abs (Abs (Abs (Abs (App (App 3 1) (App (App 2 1) 0))))).
(* λm.λn.λf.λx.(m f (n f x)) *)
Eval compute in eval 6 (App (App chadd (church 3)) (church 2)).
(*
= Abs (Abs (App 1 (App 1 (App 1 (App 1 (App 1 0)))))) : expr
*)
Lemma reduce_ok e e' : (* 1-step 簡約の健全性 *)
  reduce e = Some e' -> reduces e e'.
Proof.
  move: e'; induction e => //= e'.
    case He: (reduce e) => [e1|] // [] <-.
    apply/Rabs/IHe/He.
  destruct e1 => //.
  - case Hn: (reduce n) => [n1|] //.
    case He: (reduce e2) => [e1|] // [] <-.
    apply/Rapp2/IHe2/He.
  - case => <-.
    by constructor.
  - case He1: (reduce (App _ _)) => [e1'|].
    + case => <-.
      apply/Rapp1/IHe1/He1.
    + case He2: (reduce e2) => [e1|] //.
      case => <-.
      apply/Rapp2/IHe2/He2.
Qed.

(* n-step 簡約の健全性 *)
Theorem eval_ok n e e' : eval n e = e' -> RT_closure reduces e e'.
Proof.
  elim: n e => /= [e ->|n IH e] //.
  case He: (reduce e) => [e1|].
  - move=> H. apply RTnext with e1.
    + apply/reduce_ok/He.
    + apply/IH/H.
  - by move=>->.
Qed.

Fixpoint closed_expr n e := (* 変数が n 個以下の項 *)
  match e with
  | Var k => k < n
  | App e1 e2 => closed_expr n e1 && closed_expr n e2
  | Abs e1 => closed_expr n.+1 e1
  end.

Lemma shift_closed n e : closed_expr n e -> shift n e = e.
Proof.
  elim: e n => [k n IH|e IH1 n IH2|e1 IH1 e2 IH2 n /andP [IH3L IH3R]] /=.
  - case: ifP =>//.
    by rewrite (ltn_geF IH).
  - rewrite IH1 //.
  - rewrite IH2 // IH1 //.
Qed.
Lemma open_rec_closed n u e : (* n + 1 個目の変数を代入しても変わらない *)
  closed_expr n e -> open_rec n u e = e.
Proof.
  move: n u.
  induction e => //= k u Hc.
  - case: ifP => Hk1.
      by rewrite (eqP Hk1) ltnn in Hc.
    by rewrite leqNgt Hc.
Admitted.

Lemma closed_iter_app n k e1 e2 :
  closed_expr k e1 -> closed_expr k e2 -> closed_expr k (iter n (App e1) e2).
Admitted.
Lemma closed_church n : closed_expr 0 (church n). Admitted.
Lemma closed_expr_S n e : closed_expr n e -> closed_expr n.+1 e. Admitted.
Hint Resolve closed_iter_app closed_church closed_expr_S.

Lemma open_iter_app k n u e1 e2 :
  open_rec k u (iter n (App e1) e2) =
    iter n (App (open_rec k u e1)) (open_rec k u e2).
Admitted.

Lemma reduces_iter n e1 e2 e2' :
  reduces e2 e2' -> reduces (iter n (App e1) e2) (iter n (App e1) e2').
Admitted.

Theorem chadd_ok' m n : (* Church 数の足し算が正しい *)
  RT_closure reduces (App (App chadd (church m)) (church n)) (church (m+n)).
Proof.
  eapply RTnext; repeat constructor.
  rewrite /= !shift_closed; auto.
Admitted.

Lemma eval_add m n e : eval (m+n) e = eval m (eval n e). Admitted.
Lemma reduce_iter_app n (k : nat) x :
  reduce (iter n (App k) x) =
    if reduce x is Some x' then Some (iter n (App k) x') else None.
Admitted.

Theorem chadd_ok m n : (* reduce でも証明 (帰結ではない) *)
  exists h, exists h',
    eval h (App (App chadd (church m)) (church n)) = eval h' (church (m+n)).
Proof.
  elim: m n => [|m IHm] n.
    rewrite add0n.
    exists 6; exists 0 => /=.
    rewrite !shift_closed; auto.
    by rewrite !open_iter_app /=.
  move: {IHm}(IHm n.+1) => [h [h' IHm]].
  exists (6+h); exists (6+h').
  rewrite (addSnnS m) -(addn1 m).
  move: (f_equal (eval 6) IHm).
  rewrite -!eval_add => <- /=.
  rewrite !shift_closed /=; auto.
  rewrite !open_iter_app /=.
  do! rewrite !reduce_iter_app /=.
  by rewrite iter_add.
Qed.
End Lambda.
