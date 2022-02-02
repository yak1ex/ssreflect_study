From mathcomp Require Import all_ssreflect.

Section sort.
Variable A : eqType.
Variable le : A -> A -> bool.
Variable le_trans: forall x y z, le x y -> le y z -> le x z.
Variable le_total: forall x y, ~~ le x y -> le y x.

Fixpoint insert a l := match l with
    | nil => (a :: nil)
    | b :: l' => if le a b then a :: l else b :: insert a l'
    end.

Fixpoint isort l :=
    if l is a :: l' then insert a (isort l') else nil.

Fixpoint sorted l := (* all を使って bool 上の述語を定義する *)
    if l is a :: l' then all (le a) l' && sorted l' else true.

Lemma le_seq_insert a b l :
    le a b -> all (le a) l -> all (le a) (insert b l).
Proof.
    elim: l => /= [-> // | c l IH].
    move=> leab /andP [leac leal].
    case: ifPn => lebc /=.
    - by rewrite leab leac.
    - by rewrite leac IH.
Qed.

Lemma le_seq_trans a b l :
    le a b -> all (le b) l -> all (le a) l.
Proof.
    move=> leab /allP lebl.
    apply/allP => x Hx.
    by apply/le_trans/lebl.
Qed.

Theorem insert_ok a l : sorted l -> sorted (insert a l).
Proof.
    elim: l => //= a0 l0 IH1 /andP[IHL IHR].
    case: ifPn => Hle /=.
    - by rewrite Hle (le_seq_trans _ _ _ Hle IHL) IHL IHR.
    - rewrite le_seq_insert => //.
        + by rewrite (IH1 IHR).
        + rewrite le_total => //.
Restart.
    elim: l => //= a0 l0 IH1 /andP[IHL IHR].
    case: ifPn => Hle /=.
    - by rewrite Hle (le_seq_trans _ _ _ Hle IHL) IHL IHR.
    - by rewrite (le_seq_insert _ _ _ (le_total _ _ Hle) IHL) (IH1 IHR).
Qed.
Theorem isort_ok l : sorted (isort l).
Proof.
    elim: l => //= a l IH.
    by apply: insert_ok.
Qed.

(* perm_eq が seq で定義されているが補題だけを使う *)
Theorem insert_perm l a : perm_eq (a :: l) (insert a l).
Proof.
    elim: l => //= b l pal.
    case: ifPn => //= leab.
    by rewrite (perm_catCA [:: a] [:: b]) perm_cons.
Qed.

(* perm_trans : forall (T : eqType), transitive (seq T) perm_eq *)
Theorem isort_perm l : perm_eq l (isort l).
Proof.
    elim: l => //= a l IH. Search "perm_".
    apply/perm_eq_trans/insert_perm.
    by rewrite perm_cons.
Qed.
End sort.

Check isort.
Definition isortn : seq nat -> seq nat := isort _ leq.
Definition sortedn := sorted _ leq.
Lemma leq_total a b : ~~ (a <= b) -> b <= a.
Proof.
    move: (leq_total a b) => /orP[HL|HR] H => //.
    case: ((negP H) HL).
Qed.

Theorem isortn_ok l : sortedn (isortn l) && perm_eq l (isortn l).
Proof.
    apply/andP. split.
    - apply: isort_ok.
        + move=>m n p. apply: leq_trans.
        + apply: leq_total.
    - apply: isort_perm.
Qed.

Require Import Extraction.
Extraction "isort.ml" isortn. (* コードが分かりにくい *)

(*
% ocaml -c isort.ml (* .mlだと思う *)
% ocaml
# #load"isort.cmo";;
# open Isort;;
# isortn (Cons (S O, Cons (O, Cons (S (S O), Nil))));;
- : Isort.nat Isort.list = Cons (O, Cons (S O, Cons (S (S O), Nil)))
*)

Section even_odd.
Notation even n := (~~ odd n). (* 単なる表記なので，展開が要らない *)

Theorem even_double n : even (n + n).
Proof. elim: n => // n. by rewrite addnS /= negbK. Qed.

(* 等式を使って n に対する通常の帰納法を可能にする *)
Theorem even_plus m n : even m -> even n = even (m + n).
Proof.
    elim: n => /= [|n IH] Hm.
    - by rewrite addn0.
    - by rewrite addnS IH.
Qed.

Theorem one_not_even : ~~ even 1.
Proof. reflexivity. Qed.

Theorem even_not_odd n : even n -> ~~ odd n.
Proof. done. Qed.

Theorem even_odd n : even n -> odd n.+1.
Proof.
    elim: n => //.
Restart.
    done.
Qed.
Theorem odd_even n : odd n -> even n.+1.
Proof.
    elim: n => //= n IH.
    rewrite negbK => //.
Restart.
    elim: n => //= _ _ -> //.
Qed.
Theorem even_or_odd n : even n || odd n.
Proof.
    by rewrite orbC orbN.
Restart.
    rewrite orbC.
    rewrite orbN.
    done.
Qed.
Theorem odd_odd_even m n : odd m -> odd n = even (m+n).
Proof.
    elim: m => //= n0 IH1 IH2.
    by rewrite -(even_plus n0 _ IH2) negbK.
Restart.
    elim: m => //= n0 IH1 IH2.
    rewrite -(even_plus n0).
    - rewrite negbK. reflexivity.
    - exact IH2.
Qed.
End even_odd.
