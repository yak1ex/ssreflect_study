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
Qed.

Check addKn. (* forall n : nat, cancel (addn n) (subn^~ n) *)