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
Require Extraction.
Extraction safe_pred.
(*
(** val safe_pred : nat -> nat **)

let safe_pred = function
| O -> assert false (* absurd case *)
| S n -> n
*)