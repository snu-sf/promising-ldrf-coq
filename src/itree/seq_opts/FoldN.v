Require Import RelationClasses.

From sflib Require Import sflib.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Axioms.

Set Implicit Arguments.


Section FOLDN.

  Fixpoint fold_n {T} (f: T -> T) (n: nat) (t: T) : T :=
    match n with
    | O => t
    | S m => f (fold_n f m t)
    end.

  Lemma fold_n_2 {T} :
    forall f (t: T), f (f t) = fold_n f 2 t.
  Proof. ss. Qed.

  Lemma fold_n_one_out {T} :
    forall f (t: T) n, f (fold_n f n t) = fold_n f (1 + n) t.
  Proof.
    i. depgen t. induction n; i; ss; clarify.
  Qed.

  Lemma fold_n_one_in {T} :
    forall f (t: T) n, (fold_n f n (f t)) = fold_n f (1 + n) t.
  Proof.
    i. depgen t. induction n; i; ss; clarify. rewrite IHn. ss.
  Qed.

  Lemma fold_n_add {T} :
    forall f (t: T) n1 n2, fold_n f (n2 + n1) t = fold_n f n2 (fold_n f n1 t).
  Proof.
    i. depgen t. depgen n1. induction n2; i; ss; clarify.
    rewrite fold_n_one_out at 1.
    rewrite fold_n_one_out. rewrite <- ! fold_n_one_in.
    rewrite fold_n_one_out. rewrite <- fold_n_one_in.
    eauto.
  Qed.

  Lemma fold_n_fix {T} :
    forall f (t: T) n, (f t) = t -> fold_n f n t = t.
  Proof.
    i. depgen t. depgen n. induction n; i; ss; clarify.
    rewrite IHn; auto.
  Qed.

  Lemma fold_n_prop
        (T: Type) x
        (f: T -> T)
        (P: T -> T -> Prop)
        (REFL: forall x, P x x)
        (TRANS: forall a b c, P a b -> P b c -> P a c)
        (IND: forall x y: T, P x y -> P (f x) (f y))
        (BASE: forall x, P (f (f x)) (f x))
    :
      forall n, P (fold_n f (S n) x) (f x).
  Proof.
    induction n; ss.
    eapply TRANS. 2: eauto. eapply BASE.
  Qed.

  Lemma fold_n_mon
        (T: Type) (x y: T)
        (f: T -> T)
        (P: T -> T -> Prop)
        (IND: forall x y: T, P x y -> P (f x) (f y))
        (BASE: P x y)
    :
      forall n, P (fold_n f n x) (fold_n f n y).
  Proof.
    induction n; ss; clarify; eauto.
  Qed.

  Lemma fold_n_curry
        (T1: Type) (T2: Type)
        (d: T1 -> T2)
        (p: T1)
        f n
    :
      fold_n (fun d p => f (d p)) n d p = fold_n f n (d p).
  Proof.
    induction n; ss; clarify.
    rewrite IHn. ss.
  Qed.

  Lemma fold_n_curry2
        (T1: Type) (T2: Type)
        (d: T1 -> T2)
        (p: T1)
        f n
    :
      fold_n (fun d p => f p (d p)) n d p = fold_n (f p) n (d p).
  Proof.
    rewrite <- fold_n_curry. induction n; ss; clarify.
    rewrite IHn. ss.
  Qed.

End FOLDN.


Section FIX.

  Definition is_fix_point {T} {eq} {EQ: Equivalence eq} (f: T -> T) (t: T) :=
    eq (f t) t.

  Definition is_fix {T} {eq} {EQ: Equivalence eq} (f fp: T -> T) :=
    forall t, is_fix_point f (fp t).

  Lemma is_fix_alt {T}:
    forall (f fp: T -> T) (FIX: is_fix f fp), (forall (t: T), (f (fp t)) = (fp t)).
  Proof.
    i. unfold is_fix in FIX. unfold is_fix_point in FIX. auto.
  Qed.

  Lemma is_fix_alt_eq {T} {eq} {EQ: Equivalence eq}:
    forall (f fp: T -> T) (FIX: is_fix f fp), (forall (t: T), eq (f (fp t)) (fp t)).
  Proof.
    i. unfold is_fix in FIX. unfold is_fix_point in FIX. auto.
  Qed.

  Definition n_fix {T} {eq} {EQ: Equivalence eq} (f: T -> T) n :=
    is_fix f (fold_n f n).

  Lemma n_fix_fix {T}:
    forall (f: T -> T) n (NFIX: n_fix f n),
      (forall t, f (fold_n f n t) = fold_n f n t).
  Proof.
    i. unfold n_fix in NFIX. eapply is_fix_alt in NFIX. eapply NFIX.
  Qed.

  Lemma n_fix_fix_eq {T} {eq} {EQ: Equivalence eq}:
    forall (f: T -> T) n (NFIX: n_fix f n),
      (forall t, eq (f (fold_n f n t)) (fold_n f n t)).
  Proof.
    i. unfold n_fix in NFIX. eapply is_fix_alt_eq in NFIX. eapply NFIX.
  Qed.

  Lemma n_fix_m_fix {T}:
    forall (f: T -> T) n (NFIX: n_fix f n),
      (forall m t, (fold_n f m (fold_n f n t)) = fold_n f n t).
  Proof.
    i. depgen f. depgen n. depgen t. induction m; i; ss; clarify.
    erewrite IHm; auto. apply n_fix_fix; auto.
  Qed.

  Lemma n_fix_m_fix_eq {T} {eq} {EQ: Equivalence eq}:
    forall (f: T -> T) n (NFIX: n_fix f n),
      (forall m t, eq (fold_n f m (fold_n f n t)) (fold_n f n t)).
  Proof.
    i. depgen f. depgen n. depgen t. induction m; i; ss; clarify.
    { reflexivity. }
    etransitivity.
    2: eapply IHm; eauto.
    rewrite <- fold_n_add. rewrite PeanoNat.Nat.add_comm. rewrite fold_n_add.
    eapply n_fix_fix_eq; eauto.
  Qed.

End FIX.



Section GFIX.

  Variable K: Type.
  Variable P: Type.

  Definition GD := P -> K.

  Definition local_update := K -> K.
  Definition pointwise_update := P -> local_update.
  Definition global_update := GD -> GD.

  Definition mk_global (fs: pointwise_update) : global_update :=
    fun (d: GD) => (fun p => (fs p) (d p)).

  Lemma mk_global_fold_n_comm
        (fs: pointwise_update)
        n
    :
      mk_global (fun p => (fold_n (fs p) n)) = (fold_n (mk_global fs) n).
  Proof.
    depgen fs. induction n; i.
    { ss. }
    ss. unfold mk_global in *. ss.
    extensionality d. extensionality p. f_equal.
    specialize IHn with fs.
    assert (A: (fun (d : GD) (p : P) => fold_n (fs p) n (d p)) d p = fold_n (fs p) n (d p)).
    { ss. }
    rewrite IHn in A. rewrite <- A. ss.
  Qed.

  Lemma g_n_fix:
    forall (fs: pointwise_update) n (NFIX: forall p, @n_fix K eq eq_equivalence (fs p) n),
      @n_fix GD eq eq_equivalence (mk_global fs) n.
  Proof.
    i. unfold n_fix in *. unfold is_fix in *. i. unfold is_fix_point in *. ii.
    unfold mk_global. extensionality p. setoid_rewrite fold_n_curry2. rewrite ! NFIX. ss.
  Qed.

End GFIX.
