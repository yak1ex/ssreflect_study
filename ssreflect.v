Section Koushin.

Require Import ssreflect.
Require Import Unicode.Utf8.

Variables P Q : Prop.

Theorem modus_ponens : P -> (P -> Q) -> Q.
Proof.
    intros p pq.
    apply pq.
    assumption.
Qed.

Reset modus_ponens.
Theorem modus_ponens : P -> (P -> Q) -> Q.
Proof.
    move=> p. (* Intro *)
    move/(_ p). (* Apply-L2 *)
done.
Restart.
    by move => p /(_ p).
Qed.

Theorem and_comm : P /\ Q -> Q /\ P.
Proof.
    move=> [] p q. (* /\-L, Intro, Intro *)
    split. (* /\-R *)
    done. done.
Restart.
    by move=> [p q]; split.
Qed.

Theorem or_comm : P \/ Q -> Q \/ P.
Proof.
    move=> [p|q]. (* \/-L *)
        by right. (* \/-R2 *)
    by left. (* \/-R1 *)
Qed.

Theorem DeMorgan : ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
    rewrite /not.
    move=> npq.
    split=> [p|q].
        apply: npq.
        by left.
    apply: npq.
    by right.
Qed.
End Koushin.

Section Classic.
Definition Classic := forall P : Prop, ~ ~ P -> P.
Definition EM := forall P : Prop, P \/ ~ P.

Lemma Classic_is_EM : Classic <-> EM.
Proof.
    rewrite /Classic /EM.
    split => [classic | em] P.
      - apply: (classic) => nEM.
        (* move: (classic). apply => nEM. (* apply すると先頭を適用して仮定に持っていく *) *)
        have p : P.
            apply: classic => np.
            apply: nEM. by right.
        apply: nEM. by left.
      - move: em. move /(fun f => f P). move => [].
        (* move: em. move /((fun p f => f p) P). move => []. *)
        (* move: em. move /(_ P). move => []. *)
        (* move: (em P) => []. (* case *) *)
        + done.
        + move => np.
          move /(_ np). (* focus に apply する / _ は focus を指す *)
          (* move => np /(_ np). *)
          done.
Qed.

Variables P Q : Prop.

Theorem DeMorgan' : Classic ->  ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
    move /Classic_is_EM => em npq.
    (* move /Classic_is_EM. move => em npq. *)
    (* move=> /Classic_is_EM em npq. *) (* Apply-L1, Intro, Intro *)
    move: (em P). move => [p|np]. (* その場で case *)
    (* move: (em P) => [p|np]. *)
    - move: (em Q) => [q|nq].
      + elim: npq. by split.
      + by right.
    - by left.
Qed.
End Classic.
Check DeMorgan'.

Section Coq1.
    Variable P Q R : Prop.
    Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
    Proof.
        move => HPQ HQR HP. by move: (HPQ HP).
    Restart.
        move => HPQ HQR HP.
        apply: HQR.
        apply: HPQ.
        apply: HP.
    Restart.
        move=> HPQ HQR.
        by move /HPQ /HQR.
    Restart.
        by move=> HPQ HQR /HPQ.
    Restart.
        by move => HPQ HQR /HPQ.
    Restart.
        move => HPQ HQR /HPQ /HQR.
        exact.
    Restart.
        by auto.
    Qed.
    Theorem not_false: ~False.
    Proof.
        by move=> F.
    Restart.
        done.
    Qed.
    Theorem double_neg : P -> ~ ~ P.
    Proof.
        by move => HP /(_ HP) F.
    Restart.
        by move => HP /(_ HP).
    Restart.
        move => HP. exact.
    Restart.
        move => HP. by apply.
    Restart.
        move => HP.
        rewrite /not.
        by move /(_ HP).
    Restart.
        by rewrite/not.
    Qed.
    Theorem contraposition : (P -> Q) -> ~Q -> ~P.
    Proof.
        by move => HPQ HNQ /HPQ.
    Restart.
        move => pq nq p.
        apply: nq.
        apply: (pq p).
    Qed.
    Theorem and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
    Proof.
        move => [HP [HQ HR]]. by split.
    Restart.
        by move => [HP [HQ HR]].
    Restart.
        move => [HP [HQ HR]]. split. by split. done.
    Qed.
    Theorem and_distr : P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
    Proof.
        move => [HP [HQ|HR]].
        - by left.
        - by right.
    Restart.
        by move => [HP [HQ|HR]]; [left|right].
    Qed. 
    Theorem absurd : P -> ~P -> Q.
    Proof.
        move => HP /(_ HP) F. elim F.
    Restart.
        move => p np.
        by elim: np.
    Restart.
        by move => HP /(_ HP).
    Restart.
        done.
    Qed.
    Definition DM_rev := forall P Q, ~ (~P /\ ~Q) -> P \/ Q.
    Theorem DM_rev_is_EM : DM_rev <-> EM.
    Proof.
        rewrite /EM /DM_rev.
        split.
        - move => dm_rev PP. apply: dm_rev. move => [HNP HNNP].
          by move: HNP.
        - move => em PP QQ.
          move: (em PP) => [HP|HNP] HPQ.
          + by left.
          + move: (em QQ) => [HQ|HNQ].
            * by right.
            * elim: HPQ. by split.
    Restart.
        clear P Q R.
        rewrite /EM /DM_rev.
        split.
        - move => Hdm P. apply: Hdm. case => np. move /(_ np). done.
        - move => em P Q.
          move: (em P) => [HP|HNP] HPQ.
          + by left.
          + move: (em Q) => [HQ|HNQ].
            * by right.
            * move: HPQ => []. by split.
    Restart.
        clear P Q R.
        rewrite /EM /DM_rev.
        split.
        - move => Hdm P. apply: Hdm. by case.
    Restart.
        clear P Q R.
        rewrite /EM /DM_rev.
        split.
        - move => Hdm P. by apply: Hdm => [[] np /(_ np)].
          (* [ []<-case ]<-goal-case *)
    Restart.
        clear P Q R.
        rewrite /EM /DM_rev.
        split.
        - move => Hdm P. by apply: Hdm => [[]].
    Restart.
        clear P Q R.
        split => [HDM P|HEM P Q].
        - by apply: HDM => [[]].
        - case: (HEM P)=>[HP _|HnP]; [by left|].
          case: (HEM Q) => [HQ _|HnQ]; [by right|]. (* [right|]=>//. でも可 *)
          by move /(_ (conj HnP HnQ)).
    Qed.
End Coq1.