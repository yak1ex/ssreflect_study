(* 単一化 *)

From mathcomp Require Import all_ssreflect.
Require String.
Import String.StringSyntax.
Open Scope string_scope.

(* 変数 *)
Definition var := nat.

(* 定数・関数記号 *)
Notation symbol := String.string.
Definition symbol_dec := String.string_dec.

(* 項は木構造 *)
Inductive tree : Set :=
  | Var : var -> tree
  | Sym : symbol -> tree
  | Fork : tree -> tree -> tree.

(* 自動的に等価性を生成する *)
(*Scheme Equality for tree.*) (* Coq 8.9 で動かないかも *)

(* Scheme Equality が失敗するなら手で定義する *)
Definition tree_eq_dec (t1 t2 : tree) : {t1 = t2}+{t1 <> t2}.
  revert t2; induction t1; destruct t2; try by right.
  - case /boolP: (v == v0) => /eqP H. by left; rewrite H. by right; case.
  - case (symbol_dec s s0) => H. by left; rewrite H. by right; case.
  - case (IHt1_1 t2_1) => [<-|N]; last by right; case.
    case (IHt1_2 t2_2) => [<-|N']. by left. by right; case.
Defined.

(* tree を eqType として登録する *)
Lemma tree_eq_boolP : Equality.axiom tree_eq_dec.
Proof. move=> x y. case: tree_eq_dec => //= H; by constructor. Qed.
Definition tree_eq_mixin := EqMixin tree_eq_boolP.
Canonical tree_eqType := Eval hnf in EqType _ tree_eq_mixin.

(* [t/x] t' *)
Fixpoint subs (x : var) (t t' : tree) : tree :=
  match t' with
  | Var v => if v == x then t else t'
  | Sym b => Sym b
  | Fork t1 t2 => Fork (subs x t t1) (subs x t t2)
  end.

(* 代入は変数代入の繰り返し *)
Definition subs_list (s : list (var * tree)) t : tree :=
  foldl (fun t (p : var * tree) => subs p.1 p.2 t) t s.

(* 単一子の定義 *)
Definition unifies s (t1 t2 : tree) := subs_list s t1 = subs_list s t2.

(* 例 : (a, (x, y)) [x := (y, b)] [y := z] = (a, ((z,b), z)) *)
Definition atree := Fork (Sym "a") (Fork (Var 0) (Var 1)).
Definition asubs := (0, Fork (Var 1) (Sym "b")) :: (1, Var 2) :: nil.
Eval compute in subs_list asubs atree.

(* 和集合 *)
Fixpoint union (vl1 vl2 : list var) :=
  if vl1 is v :: vl then
    if v \in vl2 then union vl vl2 else union vl (v :: vl2)
  else vl2.

Lemma in_union_or v vl1 vl2 :
  v \in union vl1 vl2 = (v \in vl1) || (v \in vl2).
Proof. elim: vl1 vl2 => //= x vl IH vl2.
  case H: (x \in vl2).
  - rewrite IH. case H': (v == x).
    + by rewrite (eqP H') H !orbT.
    + congr (_ || _). by rewrite in_cons H' orFb.
  - rewrite IH. case H': (v == x).
    + by rewrite (eqP H') !in_cons eq_refl !orbT !orTb.
    + by rewrite !in_cons H' !orFb.
Restart.
  elim: vl1 vl2 => //= x vl IH vl2.
  case: ifPn => Hx; rewrite IH; case H': (v == x).
  - by rewrite (eqP H') Hx !orbT.
  - congr (_ || _). by rewrite in_cons H' orFb.
  - by rewrite (eqP H') !in_cons eq_refl !orbT !orTb.
  - by rewrite !in_cons H' !orFb.
Qed.
(* 完全性のために必要 *)
Lemma uniq_union vl1 vl2 : uniq vl2 -> uniq (union vl1 vl2).
Proof. elim: vl1 vl2 => //= a l IH vl2 Hu.
  case: ifPn => Ha; apply IH => //=.
  by rewrite Ha Hu.
Qed.

(* 出現変数 *)
Fixpoint vars (t : tree) : list var :=
  match t with
  | Var x => [:: x]
  | Sym _ => nil
  | Fork t1 t2 => union (vars t1) (vars t2)
  end.

(* 出現しない変数は代入されない *)
Lemma subs_same v t' t : v \notin (vars t) -> subs v t' t = t.
Proof.
  elim: t => //= [x | t1 IH1 t2 IH2].
  - by rewrite inE eq_sym => /negbTE ->.
  - by rewrite in_union_or negb_or => /andP[] /IH1 -> /IH2 ->.
Qed.

Definition may_cons (x : var) (t : tree) r := omap (cons (x,t)) r.
Definition subs_pair x t (p : tree * tree) := (subs x t p.1, subs x t p.2).

(* 単一化 *)
Section Unify1.

(* 代入を行ったときの再帰呼び出し *)
Variable unify2 : list (tree * tree) -> option (list (var * tree)).

(* 代入して再帰呼び出し. x は t に現れてはいけない *)
Definition unify_subs x t r :=
  if x \in vars t then None else may_cons x t (unify2 (map (subs_pair x t) r)).

(* 代入をせずに分解 *)
Fixpoint unify1 (h : nat) (l : list (tree * tree))
  : option (list (var * tree)) :=
  if h is h'.+1 then
    match l with
    | nil                   => Some nil
    | (Var x, Var x') :: r  =>
                    if x == x' then unify1 h' r else unify_subs x (Var x') r
    | (Var x, t) :: r       => unify_subs x t r
    | (t, Var x) :: r       => unify_subs x t r
    | (Sym b, Sym b') :: r  => if symbol_dec b b' then unify1 h' r else None
    | (Fork t1 t2, Fork t1' t2') :: r
                            => unify1 h' ((t1, t1') :: (t2, t2') :: r)
    | _                     => None
    end
  else None.
End Unify1.

(* 等式の大きさの計算 *)
Fixpoint size_tree (t : tree) : nat :=
  if t is Fork t1 t2 then 1 + size_tree t1 + size_tree t2 else 1.

Definition size_pairs (l : list (tree * tree)) :=
  sumn [seq size_tree p.1 + size_tree p.2 | p <- l].

(* 代入したときだけ再帰 *)
Fixpoint unify2 (h : nat) l :=
  if h is h'.+1 then unify1 (unify2 h') (size_pairs l + 1) l else None.

Fixpoint vars_pairs (l : list (tree * tree)) : list var :=
  match l with
  | nil => nil (* 集合を後部から作るようにする *)
  | (t1, t2) :: r => union (union (vars t1) (vars t2)) (vars_pairs r)
  end.

(* 変数の数だけ unify2 を繰り返す *)
Definition unify t1 t2 :=
  let l := [:: (t1,t2)] in unify2 (size (vars_pairs l) + 1) l.

(* 例 *)
Eval compute in unify (Sym "a") (Var 1).

Eval compute in
  unify (Fork (Sym "a") (Var 0)) (Fork (Var 1) (Fork (Var 1) (Var 2))).

(* 全ての等式の単一子 *)
Definition unifies_pairs s (l : list (tree * tree)) :=
  forall t1 t2, (t1,t2) \in l -> unifies s t1 t2.

(* subs_list と Fork が可換 *)
Lemma subs_list_Fork s t1 t2 :
  subs_list s (Fork t1 t2) = Fork (subs_list s t1) (subs_list s t2).
Proof. elim: s t1 t2 => //. Admitted.

(* unifies_pairs の性質 *)
Lemma unifies_pairs_same s t l :
  unifies_pairs s l -> unifies_pairs s ((t,t) :: l).
Proof. move=> H t1 t2; rewrite inE => /orP[]. Admitted.

Lemma unifies_pairs_swap s t1 t2 l :
  unifies_pairs s ((t1, t2) :: l) -> unifies_pairs s ((t2, t1) :: l).
Admitted.

Lemma unify_subs_sound h v t l s :
  (forall s l, unify2 h l = Some s -> unifies_pairs s l) ->
  unify_subs (unify2 h) v t l = Some s ->
  unifies_pairs s ((Var v, t) :: l).
Proof.
  rewrite /unify_subs.
  case Hocc: (v \in _) => // IH.
  case Hun: (unify2 _ _) => [s'|] //= [] <-.
Admitted.

(* unify2 の健全性 *)
Theorem unify2_sound h s l :
  unify2 h l = Some s -> unifies_pairs s l.
Proof.
  elim: h s l => //= h IH s l.
  move: (size_pairs l + 1) => h'.
  elim: h' l => //= h' IH' [] //.
  move=> [t1 t2] l.
  destruct t1, t2 => //.
  (* VarVar *)
- case: ifP.
  move/eqP => <- /IH'.
  by apply unifies_pairs_same.
  intros; by apply (unify_subs_sound h).
  (* VarSym *)
- intros; by apply (unify_subs_sound h).
Admitted.

(* 単一化の健全性 *)
Corollary soundness t1 t2 s :
  unify t1 t2 = Some s -> unifies s t1 t2.
Admitted.

(* 完全性 *)

(* s が s' より一般的な単一子である *)
Definition moregen s s' :=
  exists s2, forall t, subs_list s' t = subs_list s2 (subs_list s t).

(* 単一化の完全性 *)
Corollary unify_complete s t1 t2 :
  unifies s t1 t2 ->
  exists s1, unify t1 t2 = Some s1 /\ moregen s1 s.
Admitted.