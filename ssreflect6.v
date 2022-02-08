From mathcomp Require Import all_ssreflect.

Fail Fixpoint gcd (m n : nat) {struct m} : nat :=
    if m is 0 then n else gcd (n %% m) m.
(* Recursive definition of gcd is ill-formed. *)
(* Recursive call to gcd has principal argument equal to 
"n %% m" instead of "n0". *)

(*
Fixpoint gcd (h m n : nat) {struct h} : nat :=
    if h is h.+1 then
        if m is 0 then n else gcd h (n %% m) m
    else 0.
*)

Require Import Wf_nat Recdef.
Check lt_wf. (* well_founded lt *)
Check lt_wf_ind. (* forall (n : nat) (P : nat -> Prop),
(forall n0 : nat, (forall m : nat, (m < n0)%coq_nat -> P m) -> P n0) ->
P n *)

Function gcd (m n : nat) {wf lt m} : nat :=
    if m is 0 then n else gcd (modn n m) m.
Proof.
    - move=> m n m0 _. apply/ltP.
      by rewrite ltn_mod.
    - exact: lt_wf.
Qed.

Check gcd_equation.
Check gcd_ind.
Print gcd_terminate.

Require Import Extraction.
Extraction gcd.
(*
let rec gcd m n =
  match m with
  | O -> n
  | S n0 -> gcd (modn n (S n0)) (S n0)
*)

Search (_ %| _) "dvdn".
Check divn_eq. (* forall m d : nat, m = m %/ d * d + m %% d *)
Check dvdn_add. (* forall d m n : nat, d %| m -> d %| n -> d %| m + n *)
Check dvdn_mull. (* forall d m n : nat, d %| n -> d %| m * n *)

Theorem gcd_divides m n : (gcd m n %| m) && (gcd m n %| n).
Proof.
    functional induction (gcd m n).
        by rewrite dvdn0 dvdnn.
        move: IHn0 => /andP [HL HR].
        apply/andP. split.
        - exact HR.
        - rewrite {2}(divn_eq n m).
          apply: dvdn_add.
          by apply: dvdn_mull.
          exact HL.
Restart.
    functional induction (gcd m n).
    by rewrite dvdn0 dvdnn.
    move: IHn0 => /andP [HL HR].
    apply/andP. split => //.
    rewrite {2}(divn_eq n m).
    apply: dvdn_add => //.
    by apply: dvdn_mull.
Restart.
    functional induction (gcd m n).
    - rewrite dvdn0. rewrite dvdnn. done.
    - apply /andP. move :IHn0. move /andP. case.
      split => //.
      rewrite {2}(divn_eq n m).
      rewrite dvdn_add => //.
      rewrite dvdn_mull => //.
Qed.

Check addKn. (* forall n : nat, cancel (addn n) (subn^~ n) *)
Theorem gcd_max g m n : g %| m -> g %| n -> g %| gcd m n.
Proof.
    functional induction (gcd m n).
        done.
        move=> Hgm Hgn.
        apply: (IHn0 _ Hgm).
        rewrite (divn_eq n m) in Hgn.
        have Hgnm: g %| n %/ m * m.
            apply/dvdn_mull/Hgm.
        rewrite <- (dvdn_addr _ Hgnm).
        exact Hgn.
Restart.
    functional induction (gcd m n) => //.
    move => Im. rewrite {1}(divn_eq n m) dvdn_addr.
    - move => In. by move: In Im.
    - by rewrite dvdn_mull.
Restart.
    functional induction (gcd m n) => //.
    move => Im. rewrite {1}(divn_eq n m) dvdn_addr.
    - move => In. by apply: IHn0.
    - by apply: dvdn_mull.
Restart.
    (* addKn 使う版 *)
    functional induction (gcd m n) => // gm gn.
    apply: IHn0 => //.
    rewrite -(addKn (n %/ m * m) (n %% m)) -divn_eq.
      by rewrite dvdn_sub // dvdn_mull.
Qed.

Check odd_mul. (* forall m n : nat, odd (m * n) = odd m && odd n *)
Check odd_double. (* forall n : nat, odd n.*2 = false *)
Check odd_double_half. (* forall n: nat, odd n + n./2.*2 = n *)
Check andbb. (* idempotent andb *)(* forall x: bool, x && x = x *)
Check negbTE. (* forall b: bool, ~~ b -> b = false *)
Check double_inj. (* injective double *)(* forall x x2: nat, x.*2 = x2.*2 -> x = x2 *)
Check divn2. (* forall m: nat, m %/ 2 = m./2 *)
Check ltn_Pdiv. (* forall m d: nat, 1 < d -> 0 < m -> m %/ d < m *)
Check muln2. (* forall m: nat, m * 2 = m.*2 *)
Check esym. (* ?x = ?y -> ?y = ?x *)(* forall (A: Type) (x y: A), x = y -> y = x *)

Lemma odd_square n : odd n = odd (n*n).
Proof. by rewrite odd_mul andbb. Qed.
Lemma even_double_half n : ~~odd n -> n./2.*2 = n.
Proof.
    move=>H.
    rewrite -{2}(odd_double_half n) -{1}(add0n (n./2).*2).
    apply/esym/eqP.
    by rewrite eqn_add2r eqb0.
Restart.
    move=>H.
    rewrite -{2}(odd_double_half n).
    by rewrite (negbTE H).
Qed.

(* 本定理 *)
Theorem main_thm (n p : nat) : n * n = (p * p).*2 -> p = 0.
Proof.
    elim/lt_wf_ind: n p => n. (* 整礎帰納法 *)
    case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
    have Hon : ~~odd n.
        apply: negbT. rewrite odd_square Hnp. apply: odd_double.
    have Hop : ~~odd p.
        apply: negbT. rewrite odd_square. rewrite -(even_double_half _ Hon) in Hnp.
        rewrite -muln2 mulnA [n./2*2*n./2]mulnC mulnA in Hnp.
        rewrite !muln2 in Hnp.
        rewrite -(double_inj Hnp).
        apply: odd_double.
    have Hp20: p./2 = 0 -> p = 0.
        move => Hp2. by rewrite -double0 -Hp2 (even_double_half _ Hop).
    apply: Hp20. apply: (IH n./2).
    - apply/ltP. rewrite -divn2. by apply: ltn_Pdiv.
    - rewrite -(even_double_half _ Hon) -(even_double_half _ Hop) in Hnp.
      rewrite -!doubleMr -!doubleMl in Hnp. by apply/double_inj/double_inj.
Restart.
  elim/lt_wf_ind: n p => n. (* 整礎帰納法 *)
  case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
  have Hon : ~~odd n.
      apply: negbT. rewrite odd_square Hnp. apply: odd_double.
  have Hop : ~~odd p.
    apply: negbT. rewrite odd_square. rewrite -(even_double_half _ Hon) in Hnp.
    rewrite -muln2 mulnA [n./2*2*n./2]mulnC mulnA in Hnp.
    rewrite !muln2 in Hnp.
    rewrite -(double_inj Hnp).
    apply: odd_double.
  rewrite -(even_double_half p Hop).
  apply/eqP. rewrite double_eq0. apply/eqP.
  apply: (IH n./2).
  - apply/ltP. rewrite -divn2. by apply: ltn_Pdiv.
  - rewrite -(even_double_half _ Hon) -(even_double_half _ Hop) in Hnp.
    rewrite -!doubleMr -!doubleMl in Hnp. by apply/double_inj/double_inj.
Qed.

(* 無理数 *)
Require Import Reals Field. (* 実数とそのための field タクティク *)

Definition irrational (x : R) : Prop :=
    forall (p q : nat), q <> 0 -> x <> (INR p / INR q)%R.

Theorem irrational_sqrt_2: irrational (sqrt (INR 2)).
Proof.
    move=> p q Hq Hrt.
    apply /Hq /(main_thm p) /INR_eq.
    rewrite -mul2n !mult_INR -(sqrt_def (INR 2)) ?{}Hrt; last by auto with real.
    have Hqr : INR q <> 0%R by auto with real.
    by field.
Qed.
