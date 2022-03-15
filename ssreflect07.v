From mathcomp Require Import all_ssreflect.
Print ex.
(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
	ex_intro : forall x : A, P x -> exists y, P y
*)
(* ex (fun x:A => P(x)) は exists x:A, P(x) と同じ *)

Lemma exists_pred x : x > 0 -> exists y, x = S y.
Proof.
  case x => // n _. (* case: x と同じだが項が読みやすい *)
  by exists n.
Qed.
Print exists_pred.
(*
exists_pred = 
fun x : nat =>
match x as n return (0 < n -> exists y : nat, n = y.+1) with
| 0 =>
	fun H : 0 < 0 =>
    let H0 : False :=
      eq_ind (0 < 0) (fun e : bool => if e then False else True) I true H in
    False_ind (exists y : nat, 0 = y.+1) H0
| n.+1 =>
    fun _ : 0 < n.+1 => ex_intro (fun y : nat => n.+1 = y.+1) n (erefl n.+1)
end
     : forall x : nat, 0 < x -> exists y : nat, x = y.+1
*)
(* 実際
exists_pred = 
fun x : nat =>
match x as n return (0 < n -> exists y : nat, n = y.+1) with
| 0 =>
	(fun H : 0 < 0 =>
     let H0 : False :=
       eq_ind (0 < 0) (fun e : bool => if e then False else True) I true H in
     False_ind (exists y : nat, 0 = y.+1) H0)
      : 0 < 0 -> exists y : nat, 0 = y.+1
| n.+1 =>
    (fun n0 : nat =>
     fun=> ex_intro (fun y : nat => n0.+1 = y.+1) n0 (erefl n0.+1)) n
end
     : forall x : nat, 0 < x -> exists y : nat, x = y.+1
*)
(* fun=> は ssreflectの拡張 *)
(* Notation erefl := @Logic.eq_refl *)
Require Extraction.
Extraction exists_pred. (* 何も抽出されない *)

Print sig.
(*
Inductive sig (A : Type) (P : A -> Prop) : Type :=
	exist : forall x : A, P x -> {x : A | P x}
*)(* sig (fun x:T => Px) は {x:T | Px} と同じ *)

Definition safe_pred x : x > 0 -> {y | x = S y}.
  case x => // n _. (* exists_pred と同じ *)
  by exists n. (* こちらも exists を使う *)
Defined. (* 定義を透明にし，計算に使えるようにする *)
Print safe_pred.
(*
safe_pred = 
fun x : nat =>
match x as n return (0 < n -> {y : nat | n = y.+1}) with
| 0 =>
	(fun H : 0 < 0 =>
     let H0 : False :=
       eq_ind (0 < 0) (fun e : bool => if e then False else True) I true H in
     False_rec {y : nat | 0 = y.+1} H0)
      : 0 < 0 -> {y : nat | 0 = y.+1}
| n.+1 =>
    (fun n0 : nat =>
     fun=> exist (fun y : nat => n0.+1 = y.+1) n0 (erefl n0.+1)) n
end
     : forall x : nat, 0 < x -> {y : nat | x = y.+1}
*)
Require Extraction.
Extraction safe_pred.
(*
(** val safe_pred : nat -> nat **)

let safe_pred = function
| O -> assert false (* absurd case *)
| S n -> n
*)

Section Sort.
  Variables (A:Set) (le:A->A->bool). (* データ型 A とのその順序 le *)

  (* 既に整列されたリスト l の中に a を挿入する *)
  Fixpoint insert a (l: list A) :=
    match l with
    | nil => (a :: nil)
    | b :: l' => if le a b then a :: l else b :: insert a l'
    end.

  (* 繰り返しの挿入でリスト l を整列する *)
  Fixpoint isort (l : list A) : list A :=
    match l with
    | nil => nil
    | a :: l' => insert a (isort l')
  end.

  (* le は推移律と完全性をみたす *)
  Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_total: forall x y, ~~ le x y -> le y x.

  (* le_list x l : x はあるリスト l の全ての要素以下である *)
  Inductive le_list x : list A -> Prop :=
    | le_nil : le_list x nil
    | le_cons : forall y l,
        le x y -> le_list x l -> le_list x (y::l).

  (* sorted l : リスト l は整列されている *)
  Inductive sorted : list A -> Prop :=
    | sorted_nil : sorted nil
    | sorted_cons : forall a l,
        le_list a l -> sorted l -> sorted (a::l).

  Hint Constructors le_list sorted. (* auto の候補にする *)

  Lemma le_list_insert a b l :
    le a b -> le_list a l -> le_list a (insert b l).
  Proof.
    move=> leab; elim => {l} [|c l] /=. info_auto. (* {l}でl消して再利用 *)
    case: ifPn. info_auto. info_auto.
  Qed.

  Lemma le_list_trans a b l :
    le a b -> le_list b l -> le_list a l.
  Proof.
    move=> leab; elim. info_auto.
    info_eauto using le_trans. (* 推移律は eauto が必要 *)
  Qed.

  Hint Resolve le_list_insert le_list_trans. (* 補題も候補に加える *)

  Theorem insert_ok a l : sorted l -> sorted (insert a l).
  Proof.
    elim => [|a' l' Hlelist Hs Hs'] //=. info_auto.
    case: ifPn => Hle. info_eauto.
    info_auto.
  Qed.
  Theorem isort_ok l : sorted (isort l).
  Proof.
    elim l => [|a l' H] //=. apply: insert_ok. exact.
  Restart.
    elim l => [|a l' H] //=. exact: insert_ok.
  Qed.

  (* Permutation l1 l2 : リスト l2 は l1 の置換である *)
  Inductive Permutation : list A -> list A -> Prop :=
    | perm_nil: Permutation nil nil
    | perm_skip: forall x l l',
        Permutation l l' -> Permutation (x::l) (x::l')
    | perm_swap: forall x y l, Permutation (y::x::l) (x::y::l)
    | perm_trans: forall l l' l'',
        Permutation l l' ->
        Permutation l' l'' -> Permutation l l''.

  Hint Constructors Permutation.

  Theorem Permutation_refl l : Permutation l l.
  Proof.
    elim: l => // a l. apply: perm_skip.
  Qed.
  Theorem insert_perm l a : Permutation (a :: l) (insert a l).
  Proof.
    elim: l => /= [|a' l IH].
    - apply: Permutation_refl.
    - case: ifPn => Hle.
      + apply/perm_skip/Permutation_refl.
      + apply: perm_trans.
        apply: perm_swap.
  Restart.
    elim: l => /= [|a' l IH] in a *.
    (* elim : l a =>[ | b l IH] a. *)
    - apply: Permutation_refl.
    - case (le a a').
      + apply/Permutation_refl.
      + apply/(perm_trans _ (a' :: a :: l)).
        * exact /perm_swap.
        * exact /perm_skip.
  Qed.
  Theorem isort_perm l : Permutation l (isort l).
  Proof.
    elim: l => // a l IH /=.
    apply: perm_trans.
    apply/perm_skip/IH.
    apply: insert_perm.
  Restart.
    elim: l => // a l IH /=.
    apply/(perm_trans _ (a :: isort l)).
    - apply/perm_skip/IH.
    - apply/insert_perm.
  Qed.

  (* 証明付き整列関数 *)
  Definition safe_isort l : {l'|sorted l' /\ Permutation l l'}.
    exists (isort l).
    auto using isort_ok, isort_perm.
  Defined.
  Print safe_isort.

  (* ex 3.1 2. *)(* ↑と同じ要領で証明可能 *)
  (* Lemma: le_list_All a l : All (le a) l <-> le_list a l もあり *)
  Inductive All (P : A -> Prop) : list A -> Prop :=
  | All_nil : All P nil
  | All_cons : forall y l, P y -> All P l -> All P (y::l).

  (* sorted' l : リスト l は整列されている *)
  Inductive sorted' : list A -> Prop :=
  | sorted'_nil : sorted' nil
  | sorted'_cons : forall a l,
      All (le a) l -> sorted' l -> sorted' (a::l).

  Hint Constructors All sorted'. (* auto の候補にする *)

  Lemma le_list_insert' a b l :
      le a b -> All (le a) l -> All (le a) (insert b l).
  Proof.
    move => Hleab.
    elim => //= [|y l0 Hleay HAl HAb].
    - auto.
    - case: ifPn => Hleby ; do 2 apply: All_cons => //.
  Restart.
    move=> leab; elim => {l} [|c l] /=. info_auto. (* {l}でl消して再利用 *)
    case: ifPn. info_auto. info_auto.
  Qed.

  Lemma le_list_trans' a b l :
    le a b -> All (le b) l -> All (le a) l.
  Proof.
    move => Hleab.
    elim => //= y l0 Hleby HAbl HAal.
    apply: All_cons => //.
    apply/le_trans/Hleby/Hleab.
  Restart.
    move=> leab; elim. info_auto.
    info_eauto using le_trans. (* 推移律は eauto が必要 *)
Qed.

  Hint Resolve le_list_insert' le_list_trans'. (* 補題も候補に加える *)

  Theorem insert_ok' a l : sorted' l -> sorted' (insert a l).
  Proof.
    elim => /= [|a0 l0 IH IH' IH''].
    - by apply: sorted'_cons.
    - case: ifPn => Hle.
      + apply: sorted'_cons.
        * apply: All_cons => //.
          apply/le_list_trans'/IH/Hle.
        * by apply: sorted'_cons.
      + apply: sorted'_cons => //.
        apply: le_list_insert' => //.
        by apply: le_total.
  Restart.
    elim => [|a' l' Hlelist Hs Hs'] //=. info_auto.
    case: ifPn => Hle. info_eauto.
    info_auto.
  Qed.
  Theorem isort_ok' l : sorted' (isort l).
  Proof.
    elim l => //= a l0 IH.
    by apply: insert_ok'.
  Restart.
    elim l => [|a l' H] //=. apply: insert_ok'. exact.
  Qed.

  (* 証明付き整列関数 *)
  Definition safe_isort' l : {l'|sorted' l' /\ Permutation l l'}.
    exists (isort l).
    auto using isort_ok', isort_perm.
  Defined.
  Print safe_isort'.

End Sort.

Check safe_isort. (* le と必要な補題を与えなければならない *)
(*
safe_isort
	 : forall (A : Set) (le : A -> A -> bool),
       (forall x y z : A, le x y -> le y z -> le x z) ->
       (forall x y : A, ~~ le x y -> le y x) ->
       forall l : seq A, {l' : seq A | sorted A le l' /\ Permutation A l l'}
*)
Extraction leq. (* mathcomp の eqType の抽出が汚ない *)
(*
(** val leq : nat -> nat -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic O)
*)

Definition leq' m n := if m - n is 0 then true else false.
Extraction leq'. (* こちらはすっきりする *)
(*
(** val leq' : nat -> nat -> bool **)

let leq' m n =
  match subn m n with
  | O -> True
  | S _ -> False
*)

Lemma leq'E m n : leq' m n = (m <= n).
Proof. rewrite /leq' /leq. by case: (m-n). Qed.

Lemma leq'_trans m n p : leq' m n -> leq' n p -> leq' m p.
Proof. rewrite !leq'E; apply leq_trans. Qed.

Lemma leq'_total m n : ~~ leq' m n -> leq' n m.
Proof.
    rewrite !leq'E => H. case: (leqP m n) => HH.
    - have Hcontra: (m <= n) && ~~ (m <= n) by rewrite H HH.
      by rewrite andbN in Hcontra.
    - rewrite leq_eqVlt. apply/orP. by right.
Restart.
    rewrite !leq'E => H.
    move: (orP (leq_total m n)) => [HL|HR] //.
    case: ((negP H) HL).
Restart.
  rewrite !leq'E.
  by case: (m <= n) (leq_total m n).
Restart.
  rewrite !leq'E.
  by case /orP : (leq_total m n) => ->.
Qed.

Definition isort_leq := safe_isort nat leq' leq'_trans leq'_total.

Eval compute in proj1_sig (isort_leq (3 :: 1 :: 2 :: 0 :: nil)).
(*
= [:: 0; 1; 2; 3]
: seq nat
*)
Extraction "isort.ml" isort_leq.