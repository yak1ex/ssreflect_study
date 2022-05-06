Require Import ssreflect.

Section Socrates.
Variable A : Set.
Variables human mortal : A -> Prop.
Variable socrates : A.

Hypothesis hm : forall x, human x -> mortal x.
Hypothesis hs : human socrates.

Theorem ms : mortal socrates.
Proof.
  apply: (hm socrates).
  assumption.
Qed.

Print ms.
End Socrates.

Section Eq.
  Variable T : Type.

  Lemma symmetry : forall x y : T, x = y -> y = x.
  Proof.
    move=> x y exy.
    rewrite exy.
    done.
  Restart.
    by move=> x y ->.
  Restart.
    by move=> x y <-. (* <- だと逆に書き換え *)
  Qed.

  Lemma transitivity : forall x y z : T, x = y -> y = z -> x = z.
  Proof.
    by move=> x y z xy <-.
  Restart.
    by move=> x y z <-.
  Qed.
End Eq.

Section Group.
  Variable G : Set.
  Variable e : G.
  Variable op : G -> G -> G.
  Notation "a * b" := (op a b).
  Variable inv : G -> G.
  Hypothesis associativity : forall a b c, (a * b) * c = a * (b * c).
  Hypothesis left_identity : forall a, e * a = a.
  Hypothesis right_identity : forall a, a * e = a.
  Hypothesis left_inverse : forall a, inv a * a = e.
  Hypothesis right_inverse : forall a, a * inv a = e.

  Lemma unit_unique : forall e', (forall a, a * e' = a) -> e' = e.
  Proof.
    move=> e' He'.
    rewrite -[RHS]He'.
    rewrite (left_identity e').
    done.
  Qed.

  Lemma inv_unique : forall a b, a * b = e -> a = inv b.
  Proof.
    move=> a b.
    Check f_equal.
    move/(f_equal (fun x => x * inv b)).
    rewrite associativity right_inverse left_identity right_identity.
    (*
    rewrite associativity.
    rewrite right_inverse.
    rewrite left_identity.
    rewrite right_identity.
    *)
    done.
  Qed.

  Lemma inv_involutive : forall a, inv (inv a) = a.
  Proof.
    move=> a.
    by rewrite <- (inv_unique a (inv a)).
  Restart.
    move=>a.
    move/inv_unique :(right_inverse a).
  Restart.
    move=> a.
    by rewrite <- (inv_unique _ _ (right_inverse _)).
  Qed.
End Group.
Check unit_unique.

Section Laws.
Variables (A:Set) (P Q : A->Prop).

Lemma DeMorgan2 : (~ exists x, P x) -> forall x, ~ P x.
Proof.
  move=> N x Px. elim: N. by exists x.
Qed.

Theorem exists_or :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
Proof.
  move=> [x [Px | Qx]]; [left|right]; by exists x.
Qed.

Hypothesis EM : forall P, P \/ ~P.

Lemma DeMorgan2' : ~ (forall x, P x) -> exists x, ~ P x.
Proof.
  move=> nap.
  (*
  move: (EM (exists x, ~ P x)).
  case; move => //.
  *)
  case: (EM (exists x, ~ P x)) => //. (* 片方の分岐を解決 *)
  move=> nnpx.
  elim: nap => x.
  (*
  case: (EM (P x)) => // => npx.
  *)
  case: (EM (P x)) => //.
  move => npx.
  elim: nnpx.
  by exists x.
Qed.

End Laws.

Section Coq3.
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Variables P Q : A -> Prop.

  Theorem exists_postpone :
    (exists x, forall y, R x y) -> (forall y, exists x, R x y).
  Proof.
    case => x H y. by exists x.
  Restart.
    move=> [x H] y. by exists x.
  Qed.

  Theorem exists_mp : (forall x, P x -> Q x) -> ex P -> ex Q.
  Proof.
    move => H [y Py]. exists y. by apply H.
  Restart.
    move => H [y /H Qy]. by exists y.
  Qed.

  Theorem or_exists :
    (exists x, P x) \/ (exists x, Q x) -> exists x, P x \/ Q x.
  Proof.
    by move => [[x Px]|[x Qx]]; exists x; [left|right].
  Restart.
    by case => [[x Px]|[x Qx]]; exists x; [left|right].
  Qed.

  Hypothesis EM : forall P, P \/ ~P.

  Variables InPub Drinker : A -> Prop.
  Theorem drinkers_paradox :
    (exists consumer, InPub consumer) ->
    exists man, InPub man /\ Drinker man ->
    forall other, InPub other -> Drinker other.
  Proof.
    case => consumer Hc.
    case : (EM (forall man, InPub man -> Drinker man))
      => [H|/(DeMorgan2' _ _ EM) [man H]]; [ by exists consumer|].
      by exists man => [[]].
  Restart.
    move=> [c Ic].
    case: (EM (exists x, ~ Drinker x)).
      move=> [nd nDnd].
      exists nd. move=> [Ind Dnd]. by elim: nDnd.
    move=> nenD. exists c.
    case: (EM (~Drinker c)).
      move=> nDc [_ Dc]. by elim nDc.
    move=> nnDc [_ Dc] o Io.
    case: (EM (Drinker o)) => //.
    move=> nDo. elim: nenD. by exists o.
  Restart.
  Abort.

  Theorem remove_c : forall a,
    (forall x y, Q x -> Q y) ->
    (forall c, ((exists x, P x) -> P c) -> Q c) -> Q a.
  Proof.
    move=> a allQ H.
    case : (EM (exists x, P x)) =>[[c pc]|np].
    - by apply : allQ (H c _).
    - by apply : H.
  Restart.
    move=> a Qxy H.
    case: (EM (exists x, P x)).
      move=> [b Pb]. move: (H b). move=> H2.
      apply: (Qxy b).
      apply: H2. by move=> //.
    move=> neP. apply : H. move=> [b Pb].
    elim: neP. by exists b.
  Restart.
  Abort.
End Coq3.