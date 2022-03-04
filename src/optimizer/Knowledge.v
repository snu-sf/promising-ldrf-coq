Require Import RelationClasses.

From sflib Require Import sflib.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Axioms.

Require Export Program.

Require Import FoldN.

Set Implicit Arguments.


Section THEORY.

  Variable K: Type.

  Variable eq: K -> K -> Prop.
  Hypothesis Equiv_eq: Equivalence eq.
  Hypothesis eq_leibniz : forall x y : K, eq x y -> x = y.

  Variable le: K -> K -> Prop.
  Hypothesis PreO_le: PreOrder le.
  Hypothesis PartialO_le: PartialOrder eq le.

  Variable bot: K.
  Hypothesis Bot: forall k: K, le bot k.

  Lemma bot_unique :
    forall k, le k bot -> eq k bot.
  Proof. i. eapply antisymmetry; eauto. Qed.


  Definition lt: K -> K -> Prop :=
    fun k1 k2 => (not (eq k1 k2)) /\ (le k1 k2).

  Inductive grounded: K -> nat -> Prop :=
  | grounded_O
      k
      (ZERO: forall k' (LT: lt k' k), False)
    :
      grounded k 0
  | grounded_S
      k n
      (PRED: forall k' (LT: lt k' k), grounded k' n)
    :
      grounded k (S n)
  .

  Lemma grounded_zero
        k
        (GZ: grounded k 0)
    :
      eq k bot.
  Proof.
    inv GZ. specialize ZERO with bot.
    destruct (classic (eq k bot)); auto.
    assert (A: lt bot k).
    { unfold lt. split; auto. ii. apply H. apply eq_leibniz in H0. rewrite H0. refl. }
    apply ZERO in A. clarify.
  Qed.



  Variable P: Type.
  Definition Data  := P -> K.

  Definition data_eq := fun (i1 i2: Data) => forall p: P, eq (i1 p) (i2 p).

  Global Program Instance data_Equiv: Equivalence data_eq.
  Next Obligation.
  Proof.
    unfold Reflexive, data_eq. i. refl.
  Qed.
  Next Obligation.
  Proof.
    unfold Symmetric, data_eq. i. symmetry. auto.
  Qed.
  Next Obligation.
  Proof.
    unfold Transitive, data_eq. i. etrans; eauto.
  Qed.

  Lemma data_eq_leibniz
        i1 i2
        (EQ: data_eq i1 i2)
    :
      i1 = i2.
  Proof.
    unfold data_eq in EQ. extensionality p. eapply eq_leibniz in EQ. eapply EQ.
  Qed.

  Definition data_le := fun (i1 i2: Data) => forall p, le (i1 p) (i2 p).

  Global Program Instance data_PreOrder: PreOrder data_le.
  Next Obligation.
  Proof.
    unfold Reflexive, data_le. i. refl.
  Qed.
  Next Obligation.
  Proof.
    unfold Transitive, data_le. i. etrans; eauto.
  Qed.

  Global Program Instance data_PartialOrder: PartialOrder data_eq data_le.
  Next Obligation.
  Proof.
    ii. ss. split; i; ss; clarify; eauto.
    - unfold relation_conjunction. unfold predicate_intersection. ss. splits; ss.
      + unfold data_le. i. apply data_eq_leibniz in H. rewrite H. refl.
      + unfold flip. apply data_eq_leibniz in H. rewrite H. refl.
    - unfold relation_conjunction, predicate_intersection in H. ss. des. unfold flip in H0.
      unfold data_le in H, H0. unfold data_eq. i. specialize H with p. specialize H0 with p.
      apply antisymmetry; auto.
  Qed.

  Definition data_bot : Data := fun _ => bot.

  Lemma data_bot_spec: forall i, data_le data_bot i.
  Proof. ii. ss. Qed.

  Lemma data_bot_unique :
    forall i, data_le i data_bot -> data_eq i data_bot.
  Proof. i. eapply antisymmetry; eauto. apply data_bot_spec. Qed.






  Definition knowledge_spec (f: K -> K) :=
    <<MON: forall k1 k2, le k1 k2 -> le (f k1) (f k2)>> /\
    <<KNOW: forall k, (le (f k) k) \/ (le (f k) (f bot))>>.

  Lemma knowledge_spec_strong
        f
        (KSP: knowledge_spec f)
    :
      <<KNOW: forall k, (le (f k) k) \/ (eq (f k) (f bot))>>.
  Proof.
    red. i. unfold knowledge_spec in KSP. des. specialize KNOW with k. des; auto.
    right. apply antisymmetry; auto.
  Qed.

  Lemma knowledge_fix_bot
        f
        (KSP: knowledge_spec f)
    :
      <<FBOT: eq (f (f bot)) (f bot)>>.
  Proof.
    red. dup KSP.
    unfold knowledge_spec in KSP. des. clear KNOW.
    hexploit knowledge_spec_strong; eauto. i. des.
    rename H into KNOW0. specialize KNOW0 with (f bot). des.
    - assert (A1: le bot (f bot)); auto.
      apply MON in A1. eapply antisymmetry; eauto.
    - auto.
  Qed.

  Lemma knowledge_le
        f
        (KSP: knowledge_spec f)
    :
      forall k, le (f (f k)) (f k).
  Proof.
    i. do 2 dup KSP. apply knowledge_spec_strong in KSP0. des.
    unfold knowledge_spec in KSP1. des. clear KNOW. specialize KSP0 with (f k). des; auto.
    apply eq_leibniz in KSP0. rewrite KSP0. auto.
  Qed.

  Lemma knowledge_le_n
        n f
        (KSP: knowledge_spec f)
    :
      forall k, le ((fold_n f (S n) k)) (f k).
  Proof.
    induction n; i; ss; clarify.
    { refl. }
    rewrite fold_n_one_out. rewrite <- fold_n_one_in.
    etrans. eapply IHn. apply knowledge_le; auto.
  Qed.

  Lemma _knowledge_fix
        f
        (KSP: knowledge_spec f)
        n
    :
      forall x
        (GROUND: grounded x n), eq (f (fold_n f (S n) x)) (fold_n f (S n) x).
  Proof.
    induction n.
    { i. apply grounded_zero in GROUND.
      ss. apply eq_leibniz in GROUND. rewrite ! GROUND. apply knowledge_fix_bot; auto.
    }
    i.
    do 2 dup KSP.
    unfold knowledge_spec in KSP0. des. clear KNOW.
    apply knowledge_spec_strong in KSP1. des. rename KSP1 into KNOW.
    inv GROUND. ss.
    specialize KNOW with x. des.
    - destruct (classic (eq (f x) x)).
      + apply eq_leibniz in H.
        repeat rewrite fold_n_one_out.
        hexploit (fold_n_fix f); eauto. instantiate (1:= 1 + (1 + (1 + n))). i.
        hexploit (fold_n_fix f); eauto. instantiate (1:= 1 + (1 + n)). i.
        rewrite H0. rewrite H1. refl.
      + assert (LT: lt (f x) x).
        { unfold lt; auto. }
        apply PRED in LT. apply IHn in LT.
        rewrite fold_n_one_out. rewrite <- ! fold_n_one_in. auto.
    - apply eq_leibniz in KNOW.
      assert (FIX2: eq (f (f x)) (f x)).
      { rewrite KNOW. apply knowledge_fix_bot; auto. }
      apply eq_leibniz in FIX2.
      repeat rewrite fold_n_one_out.
      rewrite <- fold_n_one_in. symmetry.
      rewrite <- fold_n_one_in. symmetry.
      hexploit (fold_n_fix f); eauto. instantiate (1:= 1 + (1 + n)). i.
      hexploit (fold_n_fix f); eauto. instantiate (1:= 1 + n). i.
      rewrite H. rewrite H0. refl.
  Qed.

  Theorem knowledge_fix
          f level
          (KSP: knowledge_spec f)
          (GROUND: forall k, grounded k level)
    :
      <<FIX: n_fix f (1 + level)>>.
  Proof.
    red. unfold n_fix. unfold is_fix. i.
    specialize GROUND with t.
    eapply _knowledge_fix; auto.
  Qed.






  Lemma knowledge_fix_or_lt_one
        f
        (KSP: knowledge_spec f)
    :
      forall k, <<FIX: eq (f (f k)) (f k)>> \/ <<LT: lt (f k) k>>.
  Proof.
    i. esplits. do 2 dup KSP.
    apply knowledge_spec_strong in KSP0. des. rename KSP0 into KNOW.
    unfold knowledge_spec in KSP1. des. clear KNOW0.
    specialize KNOW with k. des.
    - destruct (classic (eq (f k) k)).
      + left. ss. apply eq_leibniz in H. rewrite H at 1. refl.
      + right. unfold lt. auto.
    - left. ss. apply eq_leibniz in KNOW. rewrite KNOW.
      apply knowledge_fix_bot. auto.
  Qed.

  Lemma knowledge_fix_or_lt
        f n fn fn1
        (KSP: knowledge_spec f)
        (FN: fn = fold_n f n)
        (FN1: fn1 = fold_n f (1 + n))
    :
      forall k, <<FIX: eq (f (fn1 k)) (fn1 k)>> \/ <<LT: lt (fn1 k) (fn k)>>.
  Proof.
    esplits. do 2 dup KSP.
    apply knowledge_spec_strong in KSP0. des. rename KSP0 into KNOW.
    unfold knowledge_spec in KSP1. des. clear KNOW0.
    clarify. depgen n.
    induction n; i; ss; clarify.
    { hexploit knowledge_fix_or_lt_one; eauto. }
    set (g:=fold_n f n k) in *. eapply knowledge_fix_or_lt_one; eauto.
  Qed.



  Lemma kspec_app:
    forall f g
      (KSP1: knowledge_spec f)
      (KSP2: knowledge_spec g),
      knowledge_spec (fun t => f (g t)).
  Proof.
    i. unfold knowledge_spec in *. des. split; red; i; eauto.
    specialize KNOW0 with (g k). des.
    2:{ right. etrans. eapply KNOW0. apply MON0. apply Bot. }
    specialize KNOW with k. des.
    2:{ right. eauto. }
    left. etrans; eauto.
  Qed.




  Let local_update := local_update K.
  Let pointwise_update := pointwise_update K P.
  Let global_update := global_update K P.

  Definition local_spec (f: local_update) := knowledge_spec f.
  Definition pointwise_spec (fs: pointwise_update) := forall p, local_spec (fs p).
  Definition global_spec (F: global_update) :=
    exists fs, <<PSP: pointwise_spec fs>> /\ <<MKG: F = mk_global fs>>.

  Lemma global_spec_then_mon
        F
        (GSP: global_spec F)
    :
      forall d1 d2, data_le d1 d2 -> data_le (F d1) (F d2).
  Proof.
    i. unfold global_spec in GSP. des. unfold pointwise_spec in PSP. clarify.
    unfold data_le in *. unfold mk_global. i.
    unfold local_spec in PSP. unfold knowledge_spec in PSP. specialize PSP with p.
    des. apply MON. auto.
  Qed.

  Lemma pointwise_application
        (fs: pointwise_update)
        (d: Data)
        (g: global_update)
        (G: g = mk_global fs)
    :
      forall p, (g d) p = (fs p) (d p).
  Proof. clarify. Qed.

  Lemma pointwise_global_fix_point
        (fs: pointwise_update)
        (d: Data)
        (PFIX: forall p, is_fix_point (fs p) (d p))
    :
      is_fix_point (mk_global fs) d.
  Proof. ss. Qed.

  Lemma pointwise_global_fix
        (fs fps: pointwise_update)
        (PFIX: forall p, is_fix (fs p) (fps p))
    :
      is_fix (mk_global fs) (mk_global fps).
  Proof.
    unfold is_fix in *. i. eapply pointwise_global_fix_point; eauto.
  Qed.

  Theorem global_fix
          F level
          (GSP: global_spec F)
          (GROUND: forall k, grounded k level)
    :
      <<FIX: n_fix F (1 + level)>>.
  Proof.
    red.
    unfold global_spec in GSP. des. unfold pointwise_spec in PSP.
    unfold n_fix. clarify. rewrite <- mk_global_fold_n_comm. eapply pointwise_global_fix; eauto.
    unfold local_spec in PSP. i. specialize PSP with p.
    eapply knowledge_fix; eauto.
  Qed.


  Lemma global_le_n
        n f
        (GSP: global_spec f)
    :
      forall k, data_le ((fold_n f (S n) k)) (f k).
  Proof.
    ii. unfold global_spec in GSP. des. subst f. unfold mk_global.
    unfold Data. setoid_rewrite fold_n_curry2. eapply knowledge_le_n.
    unfold pointwise_spec in PSP. unfold local_spec in PSP. eauto.
  Qed.

End THEORY.






Module GLattice.

  (* Grounded Lattice Definition *)
  Record t (level: nat) :=
    mk_glattice
      {
        K: Type;

        eq: K -> K -> Prop;
        eq_Equiv :> Equivalence eq;
        eq_leibniz: forall x y: K, eq x y -> x = y;

        le: K -> K -> Prop;
        le_PreOrder :> PreOrder le;
        le_PartialOrder :> PartialOrder eq le;

        bot: K;
        bot_spec: forall k: K, le bot k;

        level_grounded: forall k: K, grounded eq le k level;
      }
  .

  (* Knowledge property definitions *)
  Definition knowledge_spec {n: nat} {T: t n} (f: local_update (K T)) :=
    knowledge_spec (le T) (bot T) f.

  Definition global_spec {n: nat} {T: t n} {P: Type} (F: global_update (K T) P) :=
    global_spec (le T) (bot T) F.


  (* Properties *)
  Definition bot_unique {n: nat} {T: t n} :=
    bot_unique (le_PartialOrder T) (bot T) (bot_spec T).


  (* Global Data structure *)
  Definition data_eq {n: nat} {T: t n} {P: Type} : (Data (K T) P -> Data (K T) P -> Prop) :=
    @data_eq (K T) (eq T) P.

  Definition data_Equiv {n} {T: t n} {P: Type} :=
    @data_Equiv (K T) (eq T) (eq_Equiv T) P.

  Definition data_eq_leibniz {n} {T: t n} {P: Type} :=
    @data_eq_leibniz (K T) (eq T) (eq_leibniz T) P.


  Definition data_le {n: nat} {T: t n} {P: Type} : (Data (K T) P -> Data (K T) P -> Prop) :=
    @data_le (K T) (le T) P.

  Definition data_PreOrder {n} {T: t n} {P: Type} :=
    @data_PreOrder (K T) (le T) (le_PreOrder T) P.

  Definition data_PartialOrder {n} {T: t n} {P: Type} :=
    data_PartialOrder (eq_leibniz T) (le_PartialOrder T) (P:=P).


  Definition data_bot {n: nat} {T: t n} {P: Type} :=
    data_bot (bot T) (P:=P).

  Definition data_bot_spec {n: nat} {T: t n} {P: Type} :=
    data_bot_spec (le T) (bot T) (bot_spec T) (P:=P).

  Definition data_bot_unique {n: nat} {T: t n} {P: Type} :=
    data_bot_unique (eq_leibniz T) (le_PartialOrder T) (bot_spec T) (P:=P).


  Lemma global_spec_then_mon
        (n: nat) (T: t n) (P: Type)
        (F: global_update (K T) P)
        (GSP: global_spec F)
    :
      forall d1 d2, data_le d1 d2 -> data_le (F d1) (F d2).
  Proof.
    i. hexploit (global_spec_then_mon GSP); eauto.
  Qed.


  (* Main theorems *)
  Theorem kspec_app
          (n: nat) (T: t n)
          (f g: local_update (K T))
          (KSP1: knowledge_spec f)
          (KSP2: knowledge_spec g)
    :
      knowledge_spec (fun x => (f (g x))).
  Proof.
    hexploit (kspec_app
                T.(le_PreOrder)
                T.(bot_spec)
                KSP1
                KSP2).
    i. apply H.
  Qed.

  Lemma knowledge_le_n
        (n: nat) (T: t n)
        (f: local_update (K T))
        (KSP: knowledge_spec f)
    :
      forall k, (le T) ((fold_n f (S n) k)) (f k).
  Proof.
    i.
    hexploit (knowledge_le_n
                T.(eq_leibniz)
                T.(le_PartialOrder)
                T.(bot_spec)
                n
                KSP).
    i. eapply H.
  Qed.

  Theorem knowledge_fix
          (n: nat) (T: t n)
          (f: local_update (K T))
          (KSP: knowledge_spec f)
    :
      @n_fix (K T) (eq T) (eq_Equiv T) f (1 + n).
  Proof.
    hexploit (knowledge_fix
                T.(eq_leibniz)
                T.(le_PartialOrder)
                T.(bot_spec)
                KSP
                T.(level_grounded)).
    i. des. apply H.
  Qed.

  Theorem global_fix
          (n: nat) (T: t n) (P: Type)
          (F: global_update (K T) P)
          (GSP: global_spec F)
    :
      @n_fix (Data (K T) P) data_eq data_Equiv F (1 + n).
  Proof.
    hexploit (global_fix
                T.(eq_leibniz)
                T.(le_PartialOrder)
                T.(bot_spec)
                GSP
                T.(level_grounded)).
    i. des. apply H.
  Qed.

  Lemma global_le_n
        level (T: t level) (P: Type)
        n
        (F: global_update (K T) P)
        (GSP: global_spec F)
    :
      forall k, data_le ((fold_n F (S n) k)) (F k).
  Proof.
    i.
    hexploit (global_le_n
                T.(eq_leibniz)
                T.(le_PartialOrder)
                T.(bot_spec)
                n
                GSP).
    i. eapply H.
  Qed.

End GLattice.



Module MLattice.

  (* Meet SemiLattice Definition *)
  Record t :=
    mk_mlattice
      {
        K: Type;

        eq: K -> K -> Prop;
        eq_Equiv :> Equivalence eq;
        eq_leibniz: forall x y: K, eq x y -> x = y;

        meet: K -> K -> K;
        meet_comm_eq: forall k1 k2, eq (meet k1 k2) (meet k2 k1);
        meet_assoc_eq: forall k1 k2 k3, eq (meet k1 (meet k2 k3)) (meet (meet k1 k2) k3);
        meet_idem_eq: forall k, eq (meet k k) k;

        le: K -> K -> Prop;
        le_spec_eq: forall k1 k2, (le k1 k2) <-> (eq k1 (meet k1 k2));
      }
  .

  Global Program Instance eq_Equiv_inst {T: t}: Equivalence (eq T).
  Next Obligation.
  Proof.
    eapply Equivalence_Reflexive. Unshelve. apply (eq_Equiv T).
  Qed.
  Next Obligation.
  Proof.
    eapply Equivalence_Symmetric. Unshelve. apply (eq_Equiv T).
  Qed.
  Next Obligation.
  Proof.
    eapply Equivalence_Transitive. Unshelve. apply (eq_Equiv T).
  Qed.


  Lemma meet_comm {T: t}: forall k1 k2, (meet T k1 k2) = (meet T k2 k1).
  Proof. i. apply (eq_leibniz T). apply (meet_comm_eq T). Qed.

  Lemma meet_assoc {T: t}: forall k1 k2 k3, (meet T k1 (meet T k2 k3)) = (meet T (meet T k1 k2) k3).
  Proof. i. apply (eq_leibniz T). apply (meet_assoc_eq T). Qed.
    
  Lemma meet_idem {T: t}: forall k, (meet T k k) = k.
  Proof. i. apply (eq_leibniz T). apply (meet_idem_eq T). Qed.

  Lemma le_spec {T: t}: forall k1 k2, (le T k1 k2) <-> (k1 = (meet T k1 k2)).
  Proof.
    i. etrans. eapply (le_spec_eq T). split; i; eauto.
    - apply (eq_leibniz T) in H; auto.
    - rewrite H at 1. refl.
  Qed.


  Global Program Instance le_PreOrder {T: t}: PreOrder (le T).
  Next Obligation.
  Proof.
    ii. apply le_spec. rewrite meet_idem. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. apply le_spec. apply le_spec in H. apply le_spec in H0.
    rewrite H. rewrite <- meet_assoc. rewrite <- H0. auto.
  Qed.

  Global Program Instance le_PartialOrder {T: t}: @PartialOrder _ (eq T) (eq_Equiv T) (le T) le_PreOrder.
  Next Obligation.
  Proof.
    unfold relation_equivalence, relation_conjunction.
    unfold predicate_equivalence, predicate_intersection.
    unfold pointwise_lifting, pointwise_extension.
    i. split; i.
    - split.
      + apply (eq_leibniz T) in H. rewrite H. refl.
      + apply (eq_leibniz T) in H. rewrite H. refl.
    - des. unfold flip in H0. apply (le_spec) in H. apply (le_spec) in H0. rewrite H; rewrite H0.
      rewrite meet_comm. rewrite <- meet_assoc. rewrite meet_idem. refl.
  Qed.


  Lemma meet_is_min_l {T: t}: forall k1 k2, (le T) ((meet T) k1 k2) k1.
  Proof.
    i. rewrite (le_spec). rewrite (meet_comm k1 k2). rewrite <- (meet_assoc k2 k1 k1). rewrite meet_idem. auto.
  Qed.

  Lemma meet_is_min_r {T: t}: forall k1 k2, (le T) ((meet T) k1 k2) k2.
  Proof.
    i. rewrite (le_spec). rewrite <- (meet_assoc k1 k2 k2). rewrite meet_idem. auto.
  Qed.


  Lemma meet_bot_bot_l_eq {T: t}:
    forall bot (SPEC: forall k, (le T) bot k) m, (eq T) ((meet T) bot m) bot.
  Proof. i. symmetry. apply (le_spec_eq T). apply SPEC. Qed.

  Lemma meet_bot_bot_l {T: t}:
    forall bot (SPEC: forall k, (le T) bot k) m, ((meet T) bot m) = bot.
  Proof. i. symmetry. apply (le_spec). apply SPEC. Qed.

  Lemma meet_bot_bot_r_eq {T: t}:
    forall bot (SPEC: forall k, (le T) bot k) m, (eq T) ((meet T) m bot) bot.
  Proof.
    i. symmetry. pose (meet_comm_eq T). specialize e with m bot. apply (eq_leibniz T) in e. rewrite e.
    apply (le_spec_eq T). apply SPEC.
  Qed.

  Lemma meet_bot_bot_r {T: t}:
    forall bot (SPEC: forall k, (le T) bot k) m, ((meet T) m bot) = bot.
  Proof. i. symmetry. rewrite meet_comm. apply le_spec. apply SPEC. Qed.


  Lemma meet_is_top {T: t}:
    forall k1 k2 k
      (LE1: (le T) k k1)
      (LE2: (le T) k k2),
      (le T) k (meet T k1 k2).
  Proof.
    i. rewrite (le_spec) in LE1. rewrite (le_spec) in LE2.
    rewrite (le_spec). rewrite LE2 at 1. rewrite LE1 at 1.
    rewrite meet_assoc. auto.
  Qed.

  Lemma meet_mon {T: t}:
    forall m1 m2 n1 n2 (LE1: le T m1 m2) (LE2: le T n1 n2),
      le T (meet T m1 n1) (meet T m2 n2).
  Proof.
    i.
    assert (ML1: le T (meet T m1 n1) m2).
    { etrans. eapply meet_is_min_l. auto. }
    assert (ML2: le T (meet T m1 n1) n2).
    { etrans. eapply meet_is_min_r. auto. }
    apply meet_is_top; auto.
  Qed.

End MLattice.
