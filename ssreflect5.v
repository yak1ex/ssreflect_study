From mathcomp Require Import all_ssreflect.

Module Test_ssrnat.
Fixpoint sum n :=
    if n is m.+1 then n + sum m else 0.

Theorem double_sum n : 2 * sum n = n * n.+1.
Proof.
    elim: n => [|n IHn] //=.
    rewrite -[n.+2]addn2.
    rewrite !mulnDr.
    rewrite addnC.
    rewrite !(mulnC n.+1).
    by rewrite IHn.
Qed.
End Test_ssrnat.

Print reflect.
Print Bool.reflect.
Check orP.

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
Qed.

Lemma andbc : a && b -> b && a.
Proof.
    case: a => /=.
        by rewrite andbT.
    done.
Restart.
    by case: a => //= ->.
Restart.
    by case: a; case: b.
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

Lemma test_if x : if x == 3 then x*x == 9 else x != 3.
Proof.
    case Hx: (x == 3).
        rewrite (eqP Hx). done.
    done.
Restart.
    case: ifP.
        by move/eqP ->.
    by move/negbT.
Restart.
    case: ifP.
        move/eqP. move ->. done.
        move/negbT. done.
Qed.
End Test_ssrbool.

Theorem avg_prod2 m n p : m+n = p+p -> (p - n) * (p - m) = 0.
Proof.
    move=> Hmn.
    have Hp0 q: p <= q -> p-q = 0.
        rewrite -subn_eq0. by move/eqP.
    suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
        - by rewrite (Hp0 m) // muln0.
        - by rewrite (Hp0 n).
    case: (leqP p m) => Hpm //=.
    case: (leqP p n) => Hpn //=.
    suff: m + n < p + p.
        by rewrite Hmn ltnn.
    by rewrite -addnS leq_add // ltnW.
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