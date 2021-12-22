(* Coq本体のSearchに統合されている *)
Search "add". (* 名前に add を含む定理を検索する *)
Search (_ + S _). (* 結論がパターンを含む定理を検索する *)
Search _ (_ + S _). (* 前提または結論がパターンを含む定理を検索する *)
Search (_ + _) (_ * _) "mul". (* 左を全てみたすものを検索する *)

(* 1 MathComp のライブラリ *)
From mathcomp Require Import all_ssreflect.

Module Test_ssrnat.
Fixpoint sum n :=
    if n is m.+1 then n + sum m else 0.

Theorem double_sum n : 2 * sum n = n * n.+1.
Proof.
    elim: n => [|n IHn] //=.
    rewrite -[n.+2]addn2.
    Check addn2.
    rewrite !mulnDr.
    Check mulnDr.
    Print right_distributive.
    rewrite addnC.
    rewrite !(mulnC n.+1).
    by rewrite IHn.
Qed.
End Test_ssrnat.

Print reflect.
Print Bool.reflect.
Check orP.
(* reflect (?b1 \/ ?b2) (?b1 || ?b2) *)
(* reflect (is_true ?b1 \/ is_true ?b2) (?b1 || ?b2) *)
Print is_true.
(* is_true = eq^~ true *)
(* is_true = fun b : bool => eq b true *)

Module Test_ssrbool.
Variables a b c : bool.

Print andb.

Lemma andb_intro : a -> b -> a && b.
Proof.
    move=> a b.
    rewrite a.
    move=> /=.
    done.
Restart.
    by move ->.
Restart.
    move=> a b.
    rewrite /is_true in a. (* a: a = true *)
    rewrite a.
    move=> /=.
    exact b.
Qed.

Lemma andbc : a && b -> b && a.
Proof.
    case: a => /=.
        by rewrite andbT.
    done. (* discriminate *)
Restart.
    by case: a => //= ->.
Restart.
    by case: a; case: b.
Restart.
    now case a, b.
Restart.
    case: a => //=. (* b -> b && true *) by move->.
Qed.

Lemma orbC : a || b -> b || a.
Proof.
    case: a => /=.
        by rewrite orbT.
    by rewrite orbF.
Restart.
    case: a => /=.
        rewrite orbT. done.
    rewrite orbF. done.
Restart.
    move/orP => H.
    apply/orP.
    move: H => [Ha|Hb].
        by right.
    by left.
Restart.
    by case: a; case: b.
Restart.
    case: a; case: b. done. done. done. done.
Qed.

Locate "==". (* eq_op x y *)
Print eq_op. (* fun T : eqType => Equality.op (Equality.class T) *)
Lemma test_if x : if x == 3 then x*x == 9 else x != 3.
(* x : nat_eqType *)
(* x : Equality.sort nat_eqType *)
Print nat_eqType. (* EqType nat nat_eqMixin *)
Proof.
    case Hx: (x == 3).
        Print eqP.
        (* eqP : forall (T : eqType) (x y : T), reflect (x = y) (x == y) *)
        Check (eqP Hx). (* x = 3 *)
        rewrite (eqP Hx). done.
    (* ~~ は negb *)
    Locate "~~".
    done.
Restart.
    case: ifP.
        by move/eqP ->.
    by move/negbT.
Restart.
    Check ifP. Check if_spec.
    Print ifP. Print if_spec.
    case: ifP.
        move/eqP. move ->. done.
        Check negbT. (* forall b : bool, b = false -> ~~ b *)
        move/negbT. done.
Qed.
End Test_ssrbool.

(* 自然数の減算なので *)
Theorem avg_prod2 m n p : m+n = p+p -> (p - n) * (p - m) = 0.
Proof.
    move=> Hmn.
    have Hp0 q: p <= q -> p-q = 0.
        rewrite -subn_eq0. by move/eqP.
    suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
        - by rewrite (Hp0 m) //  muln0.
        - by rewrite (Hp0 n).
    case: (leqP p m) => Hpm //=.
    case: (leqP p n) => Hpn //=.
    suff: m + n < p + p.
        by rewrite Hmn ltnn.
    by rewrite -addnS leq_add // ltnW.
Restart.
    move=> Hmn.
    have Hp0 q: p <= q -> p-q = 0.
        rewrite -subn_eq0. move/eqP. done.
    suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
        - rewrite (Hp0 m). rewrite muln0. done. exact.
        - rewrite (Hp0 n). done. exact.
    case: (leqP p m) => Hpm. done.
    case: (leqP p n) => Hpn. done.
    suff: m + n < p + p.
        rewrite Hmn. rewrite ltnn. done.
    (* rewrite /leq. (* (m + n).+1 - (p + p) == 0 *) *)
    rewrite -addnS. rewrite leq_add. done. rewrite ltnW. done. exact. exact.
Qed.

Module Equalities.
    Theorem square_sum a b : (a + b)^2 = a^2 + 2 * a * b + b^2.
    Proof.
        rewrite !expnS !expn0 !muln1. 
        rewrite mulSn mul1n mulnDr !mulnDl [b * a]mulnC.
        by rewrite !addnA.
    Qed.
    Theorem diff_square m n : m >= n -> m^2 - n^2 = (m+n) * (m-n).
    Proof.
        move=>Hnm.
        rewrite !expnS !expn0 !muln1.
        rewrite mulnBr !mulnDl [n * m]mulnC.
        rewrite subnDA -addnBA.
        by rewrite subnn addn0.
        rewrite -{2}[m*n]addn0. apply leq_addr.
    Qed.
    Theorem square_diff m n : m >= n -> (m-n)^2 = m^2 + n^2 - 2 * m * n.
    Proof.
        move=>Hnm.
        rewrite !expnS !expn0 !muln1.
        rewrite mulnBr !mulnBl.
        rewrite subnBA. Abort.
End Equalities.

(* 2 単一化と自動化 *)

Lemma test x : 1 + x = x + 1.
    Check [eta addnC].
    apply addnC.
Qed.