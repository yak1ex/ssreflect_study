From mathcomp Require Import all_ssreflect all_algebra. (* 代数ライブラリ *)

Local Open Scope ring_scope. (* 環構造を使う *)
Import GRing.Theory.

Section Problem1.
Variable K : fieldType. (* 体 *)
Variable E : vectType K. (* 有限次元ベクトル空間 *)
Variable f : 'End(E). (* 線形変換 *)

Theorem equiv1 :
  (limg f + lker f)%VS = fullv <-> limg f = limg (f \o f).
Proof.
  split.
  - move/(f_equal (lfun_img f)).
    rewrite limg_comp limg_add.
    move: (subvv (lker f)).
    rewrite lkerE => /eqP ->.
    by rewrite addv0 => ->.
  - rewrite limg_comp => Hf'.
    move: (limg_ker_dim f (limg f)).
    rewrite -[RHS]add0n -Hf' => /eqP.
    rewrite eqn_add2r dimv_eq0 => /eqP /dimv_disjoint_sum.
    move: (limg_ker_dim f fullv).
    rewrite capfv addnC => -> Hdim.
    apply/eqP.
    by rewrite eqEdim Hdim subvf leqnn.
Qed.
End Problem1.

Section Problem2.
Variable K : numFieldType. (* ノルム付き体 *)
Variable E : vectType K.
Variable p q : 'End(E).

Definition projection (f : 'End(E)) := forall x, f (f x) = f x.

Lemma proj_idE f : projection f <-> {in limg f, f =1 id}.
Proof.
  split => Hf x.
  - by move/limg_lfunVK => <-.
  - by rewrite Hf // memv_img ?memvf.
Qed.

Hypothesis proj_p : projection p.
Hypothesis proj_q : projection q.

Section a.
Lemma f_g_0 f g x :
  projection f -> projection g -> projection (f+g) -> f (g x) = 0.
Proof.
  move=> Pf Pg /(_ (g x)).
  rewrite !add_lfunE !linearD /=.
  rewrite !Pf !Pg => /eqP.
  rewrite -subr_eq !addrA addrK.
  rewrite addrAC eq_sym -subr_eq eq_sym subrr => /eqP Hfg.
  move: (f_equal g Hfg).
  rewrite !linearD /= Pg linear0 => /eqP.
  rewrite -mulr2n -scaler_nat scaler_eq0 Num.Theory.pnatr_eq0 => /orP[_|/eqP HR] //.
  by rewrite -Hfg HR addr0.
Qed.

Theorem equiv2 :
  projection (p + q) <-> (forall x, p (q x) = 0 /\ q (p x) = 0).
Proof.
  split=> H x.
  - move: (f_g_0 _ _ x proj_p proj_q H) => ->.
    rewrite addrC in H.
    by move: (f_g_0 _ _ x proj_q proj_p H) => ->.
  - move: (H x) => [HL HR].
    by rewrite !add_lfunE !linearD /= HL HR addr0 addrA addr0 proj_p proj_q.
Qed.
End a.

Section b.
Hypothesis proj_pq : projection (p + q).

Lemma b1a x : x \in limg p -> x \in limg q -> x = 0.
Proof.
  move => Hpx Hqx.
  move: ((proj1 (proj_idE p)) proj_p x Hpx) => Hpxx.
  move: ((proj1 (proj_idE q)) proj_q x Hqx) => Hqxx.
  move: ((proj1 equiv2) proj_pq x) => [Hpqx _].
  by rewrite -Hpxx -Hqxx.
Qed.

Lemma b1b : directv (limg p + limg q).
Proof.
  apply/directv_addP/eqP.
  rewrite -subv0.
  apply/subvP => u /memv_capP [Hp Hq].
  rewrite memv0.
  by move: (b1a _ Hp Hq) => ->.
Qed.

Lemma limg_sub_lker f g :
  projection f -> projection g -> projection (f+g) -> (limg f <= lker g)%VS.
Proof.
  move=> Pf Pg Pfg.
  apply/subvP => u /memv_imgP [x [_ Hfv]].
  rewrite addrC in Pfg.
  by rewrite memv_ker Hfv (f_g_0 _ _ _ Pg Pf Pfg).
Qed.

Lemma b1c : (limg p <= lker q)%VS.
Proof.
  apply: (limg_sub_lker p q proj_p proj_q proj_pq).
Qed.

Lemma b1c' : (limg q <= lker p)%VS.
Proof.
  move: proj_pq => proj_qp.
  rewrite addrC in proj_qp.
  apply: (limg_sub_lker q p proj_q proj_p proj_qp).
Qed.


Lemma limg_addv (f g : 'End(E)) : (limg (f + g)%R <= limg f + limg g)%VS.
Proof.
  apply/subvP => x /memv_imgP [u _ ->].
  rewrite add_lfunE.
  apply/memv_add;apply/memv_img/memvf.
Qed.

Theorem b1 : limg (p+q) = (limg p + limg q)%VS.
Proof.
  apply/eqP; rewrite eqEsubv limg_addv /=.
  apply/subvP => x /memv_addP [u Hu] [v Hv ->].
  have -> : u + v = (p + q) (u + v).
  rewrite lfun_simp !linearD /=.
  rewrite (proj1 (proj_idE p)) // (proj1 (proj_idE q) _ v) //.
  move: (subvP b1c u Hu) (memv_ker q u) => -> /esym /eqP Hqu.
  move: (subvP b1c' v Hv) (memv_ker p v) => -> /esym /eqP Hpv.
  by rewrite Hpv Hqu addr0 add0r.
  Check memv_img.
  rewrite memv_img // memvf //.
Qed.
Theorem b2 : lker (p+q) = (lker p :&: lker q)%VS.
Proof.
  apply/vspaceP => x.
  rewrite memv_cap !memv_ker.
  rewrite add_lfunE.
  case Hpx: (p x == 0).
  - by rewrite (eqP Hpx) add0r.
  - 
Admitted.
End b.
End Problem2.

(* ベクトル空間について *)
Check lkerE.
(*
Lemma lkerE f U : (U <= lker f)%VS = (f @: U == 0)%VS.
  : forall (K : fieldType) (aT rT : vectType K) 
        (f : 'Hom(aT, rT)) (U : {vspace aT}),
      (U <= lker f)%VS = ((f @: U)%VS == 0%VS)
*)
Check subvv.
(*
Lemma subvv U : (U <= U)%VS.
  : forall (K : fieldType) (vT : vectType K) (U : {vspace vT}),
      (U <= U)%VS
*)
Check subv0.
(*
Lemma subv0 U : (U <= 0)%VS = (U == 0%VS).
  : forall (K : fieldType) (vT : vectType K) (U : {vspace vT}),
      (U <= 0)%VS = (U == 0%VS)
*)
Check addv0.
(*
Lemma addv0 : right_id 0%VS addV.
  : forall (K : fieldType) (vT : vectType K), right_id 0%VS addv
*)
Check capfv.
(*
Lemma capfv : left_id fullv capV.
  : forall (K : fieldType) (vT : vectType K), left_id fullv capv
*)
Check subvf.
(*
Lemma subvf U : (U <= fullv)%VS.
  : forall (K : fieldType) (vT : vectType K) (U : {vspace vT}),
      (U <= fullv)%VS
*)
Check memvf.
(*
Lemma memvf v : v \in fullv.
  : forall (K : fieldType) (vT : vectType K) (v : vT), v \in fullv
*)
Check memvN.
(*
Lemma memvN U v : (- v \in U) = (v \in U).
  : forall (K : fieldType) (vT : vectType K) (U : {vspace vT}) (v : vT),
    (- v \in U) = (v \in U)
*)
Check memv_add.
(*
Lemma memv_add u v U V : u \in U -> v \in V -> u + v \in (U + V)%VS.
  : forall (K : fieldType) (vT : vectType K) (u v : vT)
    (U V : {vspace vT}), u \in U -> v \in V -> u + v \in (U + V)%VS
*)
Check memv_cap.
(*
Lemma memv_cap w U V : (w \in U :&: V)%VS = (w \in U) && (w \in V).
  : forall (K : fieldType) (vT : vectType K) (w : vT) (U V : {vspace vT}),
    (w \in (U :&: V)%VS) = (w \in U) && (w \in V)
*)
Check memv_img.
(*
Lemma memv_img f v U : v \in U -> f v \in (f @: U)%VS.
  : forall (K : fieldType) (aT rT : vectType K) 
      (f : 'Hom(aT, rT)) (v : aT) (U : {vspace aT}),
    v \in U -> f v \in (f @: U)%VS
*)
Check memv_ker.
(*
Lemma memv_ker f v : (v \in lker f) = (f v == 0).
  : forall (K : fieldType) (aT rT : vectType K) 
    (f : 'Hom(aT, rT)) (v : aT), (v \in lker f) = (f v == 0)
*)
Check limg_ker_dim.
(*
Lemma limg_ker_dim f U : (\dim (U :&: lker f) + \dim (f @: U) = \dim U)%N.
  : forall (K : fieldType) (aT rT : vectType K) 
      (f : 'Hom(aT, rT)) (U : {vspace aT}),
    (\dim (U :&: lker f) + \dim (f @: U))%N = \dim U
*)
Check dimv_disjoint_sum.
(*
Lemma dimv_disjoint_sum U V :
  (U :&: V = 0)%VS -> \dim (U + V) = (\dim U + \dim V)%N.
  : forall (K : fieldType) (vT : vectType K) (U V : {vspace vT}),
  (U :&: V)%VS = 0%VS -> \dim (U + V) = (\dim U + \dim V)%N
*)
Check dimv_eq0.
(*
Lemma dimv_eq0 U : (\dim U == 0%N) = (U == 0%VS).
  : forall (K : fieldType) (vT : vectType K) (U : {vspace vT}),
    (\dim U == 0) = (U == 0%VS)
*)
Check eqEdim.
(*
Lemma eqEdim U V : (U == V) = (U <= V)%VS && (\dim V <= \dim U).
  : forall (K : fieldType) (vT : vectType K) (U V : {vspace vT}),
    (U == V) = (U <= V)%VS && (\dim V <= \dim U)%N
*)
Check eqEsubv.
(*
Lemma eqEsubv U V : (U == V) = (U <= V <= U)%VS.
  : forall (K : fieldType) (vT : vectType K) (U V : {vspace vT}),
    (U == V) = (U <= V <= U)%VS
*)
Check vspaceP.
(*
Lemma vspaceP U V : U =i V <-> U = V.
  : forall (K : fieldType) (vT : vectType K) (U V : {vspace vT}),
    U =i V <-> U = V
*)

(* 環と体について *)
Check addr0.
(*
Lemma addr0 : right_id 0 +%R.
  : forall V : zmodType, right_id 0 +%R
*)
Check addrA.
(*
Lemma addrA : associative +%R.
  : forall V : zmodType, associative +%R
*)
Check addrC.
(*
Lemma addrC : commutative +%R.
  : forall V : zmodType, commutative +%R
*)
Check subr_eq.
(*
Lemma subr_eq x y z : (x - z == y) = (x == y + z).
  : forall (V : zmodType) (x y z : V), (x - z == y) = (x == y + z)
*)
Check mulr2n.
(*
Lemma mulr2n x : x *+ 2 = x + x.
  : forall (V : zmodType) (x : V), x *+ 2 = x + x
*)
Check scaler_nat.
(*
Lemma scaler_nat n v : n%:R *: v = v *+ n.
  : forall (R : ringType) (V : lmodType R) (n : nat) (v : V),
    n%:R *: v = v *+ n
*)
Check scaler_eq0.
(*
Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
  : forall (F : fieldType) (V : lmodType F) (a : F) (v : V),
    (a *: v == 0) = (a == 0) || (v == 0)
*)
Check linear0.
(*
Lemma linear0 (f : {linear U -> V | s}) : f 0 = 0.
  : forall (R : ringType) (U : lmodType R) (V : zmodType)
      (s : R -> V -> V) (f : {linear U -> V | s}), 
    f 0 = 0
*)
Check linearD.
(*
Lemma linearD (f : {linear U -> V | s}) : {morph f : x y / x + y}.
  : forall (R : ringType) (U : lmodType R) (V : zmodType)
      (s : R -> V -> V) (f : {linear U -> V | s}),
    {morph f : x y / x + y >-> x + y}
*)
Check Num.Theory.pnatr_eq0.
(*
Lemma Num.Theory.pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
  : forall (R : numDomainType) (n : nat), (n%:R == 0) = (n == 0)
*)
