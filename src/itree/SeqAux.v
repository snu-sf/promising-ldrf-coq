Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export Program.

Require Import Simple.
Require Import FlagAux.





Ltac contra := match goal with [H: forall _: is_true true, is_true false |- _] => exploit H; ss end.
Ltac clearb := repeat match goal with
                      | [H: forall _: is_true false, is_true false |- _] => clear H
                      | [H: forall _: is_true true, is_true true |- _] => clear H end.



Section REDAT.

  Lemma perm_meet_high:
    forall p1 p2 (MEET: Perm.meet p1 p2 = Perm.high), (p1 = Perm.high) /\ (p2 = Perm.high).
  Proof.
    i. split.
    - hexploit Perm.meet_le_l. i. erewrite MEET in H. destruct p1; ss.
    - hexploit Perm.meet_le_r. i. erewrite MEET in H. destruct p2; ss.
  Qed.

  Lemma input_transl_access0:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (ACC: Oracle.in_access i0 = None),
      SeqEvent.in_access i = None.
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACQUIRE RELEASE.
    destruct i0, i; ss. destruct in_access, in_access0; ss.
  Qed.

  Lemma input_transl_access1:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      l v f (ACC: Oracle.in_access i0 = Some (l, v, f)),
      exists v1 f1 v2, SeqEvent.in_access i = Some (l, v1, f1, v2).
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACQUIRE RELEASE.
    destruct i0, i; ss. destruct in_access, in_access0; ss. clarify.
    destruct p0; ss. des_ifs. des; clarify. eauto.
  Qed.

  Lemma input_transl_acquire0:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (ACC: Oracle.in_acquire i0 = None),
      SeqEvent.in_acquire i = None.
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACCESS RELEASE.
    destruct i0, i; ss. destruct in_acquire, in_acquire0; ss.
  Qed.

  Lemma input_transl_acquire1:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (ACC: Oracle.in_acquire i0 = Some ()),
      exists f, SeqEvent.in_acquire i = Some f.
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACCESS RELEASE.
    destruct i0, i; ss. destruct in_acquire, in_acquire0; ss. eauto.
  Qed.

  Lemma input_transl_release0:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (ACC: Oracle.in_release i0 = None),
      SeqEvent.in_release i = None.
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACCESS ACQUIRE.
    destruct i0, i; ss. destruct in_release, in_release0; ss.
  Qed.

  Lemma input_transl_release1:
    forall i0 i (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (ACC: Oracle.in_release i0 = Some ()),
      exists v f, SeqEvent.in_release i = Some (v, f).
  Proof.
    i. unfold Oracle.input_le in INPUTLE. des. ss. clear ACCESS ACQUIRE.
    destruct i0, i; ss. destruct in_release, in_release0; ss. destruct p, u; ss. eauto.
  Qed.


  Lemma red_rlx_full:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists p_new v_new,
      (<<EVACC: is_accessing ev = Some (l, v_new)>>) /\
      (<<OO: o = Oracle.mk_output (Some p_new) None None>>) /\
      (<<IN: i = SeqEvent.mk_input (Some (l, (SeqMemory.value_map m l), (SeqMemory.flags m l), v_new)) None None>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) = ValueMap.write l v_new m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.update l false m.(SeqMemory.flags)>>) /\
      (<<PERM: p1 = Perms.update l p_new p>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP.
    inv REL.
    2:{ hexploit RELEASE. rewrite <- H0. ss. i; clarify. }
    clear RELEASE RELEASE0.
    inv ACQ.
    2:{ hexploit ACQUIRE. rewrite <- H2; ss. i. clarify. }
    clear ACQUIRE ACQUIRE0.
    inv UPD.
    { hexploit UPDATE; clear UPDATE. i; des. clear H1. hexploit H6; clear H6. rewrite ACC. eauto.
      i. des. rewrite H1 in H4. ss. }
    hexploit UPDATE; clear UPDATE. i; des. clear H6. hexploit H1; clear H1. erewrite <- H4. eauto. i; des; clarify.
    inv MEM. ss. esplits; ss; eauto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_rlx:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
      loc (NEQ: l <> loc)
    ,
      (<<MEMV: SeqMemory.read loc m = SeqMemory.read loc m1>>) /\
      (<<MEMF: SeqMemory.flags m loc = SeqMemory.flags m1 loc>>) /\
      (<<PERM: p loc = p1 loc>>).
  Proof.
    i. hexploit red_rlx_full; eauto. i; des. destruct m, m1; ss.
    rewrite MEMV, MEMF, PERM. unfold ValueMap.write , Flags.update, Perms.update.
    rewrite ! Loc.eq_dec_neq; auto.
  Qed.


  Lemma red_acq_full:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists p_new v_new (p_acq : Perms.t) (v_acq : ValueMap.t),
      (<<EVACC: is_accessing ev = Some (l, v_new)>>) /\
      (<<OO: o = Oracle.mk_output (Some p_new) (Some (p_acq, v_acq)) None>>) /\
      (<<IN: i = SeqEvent.mk_input (Some (l, (SeqMemory.value_map m l), (SeqMemory.flags m l), v_new))
                                   (Some (Flags.update l false m.(SeqMemory.flags))) None>>) /\
      (<<PERM: p1 = Perms.join (Perms.update l p_new p) p_acq>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired (Perms.update l p_new p) p_acq)
                                v_acq (ValueMap.write l v_new m.(SeqMemory.value_map))>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.update l false m.(SeqMemory.flags)>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP.
    inv REL.
    2:{ hexploit RELEASE. rewrite <- H0. ss. i; clarify. }
    clear RELEASE RELEASE0.
    inv UPD.
    { hexploit UPDATE; clear UPDATE. i; des. clear H1. hexploit H4; clear H4. rewrite ACC. eauto.
      i. des. rewrite H1 in H2. ss. }
    hexploit UPDATE; clear UPDATE. i; des. clear H4. hexploit H1; clear H1. erewrite <- H2. eauto. i; des; clarify.
    inv ACQ.
    { hexploit ACQUIRE0; auto. i. rewrite <- H5 in H4. ss. }
    clear ACQUIRE ACQUIRE0.
    inv MEM. inv MEM0. ss. esplits; eauto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_acq:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq : Perms.t) (v_acq : ValueMap.t) (f_acq : Flags.t),
    forall loc (NEQ: l <> loc),
      (<<ACQFLAG: Flag.le (f_acq loc) (SeqMemory.flags m loc)>>) /\
      (<<ACQPERM: p1 loc = Perm.join (p loc) (p_acq loc)>>) /\
      (<<ACQMEMV: SeqMemory.read loc m1 =
                  ValueMap.read loc (ValueMap.acquire (Perms.acquired p p_acq) v_acq (SeqMemory.value_map m))>>) /\
      (<<ACQMEMF: SeqMemory.flags m1 loc = SeqMemory.flags m loc>>).
  Proof.
    i. hexploit red_acq_full; eauto. i; des. destruct m, m1; ss.
    rewrite MEMV, MEMF, PERM. esplits. i.
    unfold ValueMap.write , Flags.update, Perms.update. splits.
    - refl.
    - unfold Perms.join, Perms.update. rewrite Loc.eq_dec_neq; auto.
    - unfold ValueMap.acquire, ValueMap.read, Perms.acquired, Perms.update, ValueMap.write.
      rewrite ! Loc.eq_dec_neq; auto. eapply NEQ.
    - unfold Flags.update. rewrite Loc.eq_dec_neq; auto.
      Unshelve. all: ss.
  Qed.


  Lemma red_rel_full:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists p_new v_new (p_rel : Perms.t),
      (<<EVACC: is_accessing ev = Some (l, v_new)>>) /\
      (<<OO: o = Oracle.mk_output (Some p_new) None (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input (Some (l, (SeqMemory.value_map m l), (SeqMemory.flags m l), v_new)) None
                                   (Some (ValueMap.write l v_new (SeqMemory.value_map m),
                                          Flags.update l false (SeqMemory.flags m)))>>) /\
      (<<PERM: p1 = Perms.meet (Perms.update l p_new p) p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) = (ValueMap.write l v_new m.(SeqMemory.value_map))>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP. clarify.
    inv ACQ.
    2:{ hexploit ACQUIRE. rewrite <- H0. ss. i; clarify. }
    clear ACQUIRE ACQUIRE0.
    inv UPD.
    { hexploit UPDATE; clear UPDATE. i; des. clear H1. hexploit H4; clear H4. rewrite ACC. eauto.
      i. des. rewrite H1 in H2. ss. }
    hexploit UPDATE; clear UPDATE. i; des. clear H4. hexploit H1; clear H1. erewrite <- H2. eauto. i; des; clarify.
    inv REL.
    { hexploit RELEASE0; auto. i. rewrite <- H5 in H4. ss. }
    clear RELEASE RELEASE0.
    inv MEM. inv MEM0. ss. esplits; eauto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_rel:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_rel : Perms.t),
    forall loc (NEQ: l <> loc),
      (<<RELPERM: p1 loc = Perm.meet (p loc) (p_rel loc)>>) /\
      (<<RELMEMV: SeqMemory.read loc m1 = SeqMemory.read loc m>>) /\
      (<<RELMEMF: SeqMemory.flags m1 loc = false>>).
  Proof.
    i. hexploit red_rel_full; eauto. i; des. destruct m, m1; ss.
    rewrite MEMV, MEMF, PERM. esplits. i. splits.
    - unfold Perms.meet, Perms.update. rewrite Loc.eq_dec_neq; auto.
    - unfold ValueMap.write. rewrite Loc.eq_dec_neq; auto.
    - ss.
  Qed.


  Lemma red_acq_rel_full:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists p_new v_new (p_acq p_rel : Perms.t) (v_acq : ValueMap.t),
      (<<EVACC: is_accessing ev = Some (l, v_new)>>) /\
      (<<OO: o = Oracle.mk_output (Some p_new) (Some (p_acq, v_acq)) (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input (Some (l, (SeqMemory.value_map m l), (SeqMemory.flags m l), v_new))
                                   (Some (Flags.update l false m.(SeqMemory.flags)))
                                   (Some (ValueMap.acquire (Perms.acquired (Perms.update l p_new p) p_acq) v_acq
                                                           (ValueMap.write l v_new (SeqMemory.value_map m)),
                                          Flags.update l false (SeqMemory.flags m)))>>) /\
      (<<PERM: p1 = Perms.meet (Perms.join (Perms.update l p_new p) p_acq) p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired (Perms.update l p_new p) p_acq)
                                v_acq (ValueMap.write l v_new m.(SeqMemory.value_map))>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP. clarify.
    inv ACQ.
    { hexploit ACQUIRE0; auto. i. rewrite <- H0 in H1. ss. }
    clear ACQUIRE ACQUIRE0.
    inv REL.
    { hexploit RELEASE0; auto. i. rewrite <- H2 in H1. ss. }
    clear RELEASE RELEASE0.
    inv UPD.
    { hexploit UPDATE; clear UPDATE. i; des. clear H1. hexploit H6; clear H6. rewrite ACC. eauto.
      i. des. rewrite H1 in H4. ss. }
    hexploit UPDATE; clear UPDATE. i; des. hexploit H1; clear H1. erewrite <- H4. eauto. i; des; clarify.
    inv MEM. inv MEM0. inv MEM1. ss. esplits; eauto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_acq_rel:
    forall p m l v ev i o p1 m1
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq p_rel : Perms.t) (v_acq : ValueMap.t) (f_acq : Flags.t),
    forall loc (NEQ: l <> loc),
      (<<ACQFLAG: Flag.le (f_acq loc) (SeqMemory.flags m loc)>>) /\
      (<<PERM1: p1 loc = Perm.meet (Perm.join (p loc) (p_acq loc)) (p_rel loc)>>) /\
      (<<MEMV1: SeqMemory.read loc m1 =
                  ValueMap.read loc (ValueMap.acquire (Perms.acquired p p_acq) v_acq (SeqMemory.value_map m))>>) /\
      (<<MEMF1: SeqMemory.flags m1 loc = false>>).
  Proof.
    i. hexploit red_acq_rel_full; eauto. i; des. destruct m, m1; ss.
    rewrite MEMV, MEMF, PERM. esplits. i. splits.
    - refl.
    - unfold Perms.join, Perms.meet, Perms.update. rewrite Loc.eq_dec_neq; auto.
    - unfold ValueMap.acquire, ValueMap.read, Perms.acquired, Perms.update, ValueMap.write.
      rewrite ! Loc.eq_dec_neq; auto. eapply NEQ.
    - ss.
      Unshelve. all: ss.
  Qed.

  Lemma red_rlx2_oracle:
    forall p m ev0 i0 i o p1 m1
      (ACC: Oracle.in_access i0 = None)
      (NOACQ: Oracle.in_acquire i0 = None)
      (NOREL: Oracle.in_release i0 = None)
      (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (EVENT: Oracle.wf_input ev0 i0)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      (<<OO: o = Oracle.mk_output None None None>>) /\
      (<<IN: i = SeqEvent.mk_input None None None>>) /\
      (<<MEM: m = m1>>) /\ (<<PERM: p = p1>>).
  Proof.
    i. unfold Oracle.wf_input in EVENT. des. inv STEP.
    hexploit input_transl_release0; eauto. intro IREL; des.
    hexploit input_transl_acquire0; eauto. intro IACQ; des.
    hexploit input_transl_access0; eauto. intro IACC; des.
    inv REL.
    2:{ rewrite IREL in H0; ss. }
    clear RELEASE RELEASE0.
    inv ACQ.
    2:{ rewrite IACQ in H2; ss. }
    clear ACQUIRE ACQUIRE0.
    inv UPD.
    2:{ rewrite IACC in H4; ss. }
    splits; auto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_rlx2_full:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      (<<OO: o = Oracle.mk_output None None None>>) /\
      (<<IN: i = SeqEvent.mk_input None None None>>) /\
      (<<MEM: m = m1>>) /\ (<<PERM: p = p1>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP.
    inv REL.
    2:{ hexploit RELEASE. rewrite <- H0. ss. i; clarify. }
    clear RELEASE RELEASE0.
    inv ACQ.
    2:{ hexploit ACQUIRE. rewrite <- H2; ss. i. clarify. }
    clear ACQUIRE ACQUIRE0.
    inv UPD.
    2:{ hexploit UPDATE. rewrite <- H4; ss. i. rewrite ACC in H1. des. hexploit H1. do 2 eexists. refl. i; des; ss. }
    splits; auto.
    destruct o; ss. rewrite <- H; rewrite <- H3; rewrite <- H5. ss.
    destruct i; ss. rewrite <- H0; rewrite <- H2; rewrite <- H4. ss.
  Qed.

  Lemma red_rlx2:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      (<<MEM: m = m1>>) /\ (<<PERM: p = p1>>).
  Proof.
    i. hexploit red_rlx2_full; eauto. i; des. destruct m, m1; ss.
  Qed.

  Lemma red_acq2_oracle:
    forall p m ev0 i0 i o p1 m1
      (ACC: Oracle.in_access i0 = None)
      (ISACQ: Oracle.in_acquire i0 = Some ())
      (NOREL: Oracle.in_release i0 = None)
      (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (EVENT: Oracle.wf_input ev0 i0)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq : Perms.t) (v_acq : ValueMap.t),
      (<<OO: o = Oracle.mk_output None (Some (p_acq, v_acq)) None>>) /\
      (<<IN: i = SeqEvent.mk_input None (Some m.(SeqMemory.flags)) None>>) /\
      (<<PERM: p1 = Perms.join p p_acq>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired p p_acq)
                                v_acq m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = m.(SeqMemory.flags)>>).
  Proof.
    i. unfold Oracle.wf_input in EVENT. des. inv STEP.
    hexploit input_transl_release0; eauto. intro IREL; des.
    hexploit input_transl_acquire1; eauto. intro IACQ; des.
    hexploit input_transl_access0; eauto. intro IACC; des.
    inv REL.
    2:{ rewrite IREL in H0; ss. }
    clear RELEASE RELEASE0.
    inv UPD.
    2:{ rewrite IACC in H2; ss. }
    inv ACQ.
    { rewrite IACQ in H4; ss. }
    clear ACQUIRE ACQUIRE0.
    inv MEM. ss. esplits; auto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_acq2_full:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq : Perms.t) (v_acq : ValueMap.t),
      (<<OO: o = Oracle.mk_output None (Some (p_acq, v_acq)) None>>) /\
      (<<IN: i = SeqEvent.mk_input None (Some m.(SeqMemory.flags)) None>>) /\
      (<<PERM: p1 = Perms.join p p_acq>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired p p_acq)
                                v_acq m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = m.(SeqMemory.flags)>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP.
    inv REL.
    2:{ hexploit RELEASE. rewrite <- H0. ss. i; clarify. }
    clear RELEASE RELEASE0.
    inv UPD.
    2:{ hexploit UPDATE. rewrite <- H2; ss. i. rewrite ACC in H1. des. hexploit H1. do 2 eexists. refl. i; des; ss. }
    inv ACQ.
    { clarify. hexploit ACQUIRE0; auto. i. rewrite <- H4 in H1. ss. }
    clear ACQUIRE ACQUIRE0.
    inv MEM. ss.
    esplits; auto.
    destruct o; ss. rewrite <- H; rewrite <- H3; rewrite <- H5. ss.
    destruct i; ss. rewrite <- H0; rewrite <- H2; rewrite <- H4. ss.
  Qed.

  Lemma red_acq2:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq : Perms.t) (v_acq : ValueMap.t) (f_acq : Flags.t),
      (<<ACQFLAG: Flags.le (f_acq) (SeqMemory.flags m)>>) /\
      (<<ACQPERM: p1 = Perms.join (p) (p_acq)>>) /\
      (<<ACQMEMV: SeqMemory.value_map m1 = (ValueMap.acquire (Perms.acquired p p_acq) v_acq (SeqMemory.value_map m))>>) /\
      (<<ACQMEMF: SeqMemory.flags m1 = SeqMemory.flags m>>).
  Proof.
    i. hexploit red_acq2_full; eauto. i; des. destruct m, m1; ss.
    do 3 eexists. splits; eauto.
    refl.
  Qed.

  Lemma red_rel2_oracle:
    forall p m ev0 i0 i o p1 m1
      (ACC: Oracle.in_access i0 = None)
      (NOACQ: Oracle.in_acquire i0 = None)
      (ISREL: Oracle.in_release i0 = Some ())
      (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (EVENT: Oracle.wf_input ev0 i0)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_rel : Perms.t),
      (<<OO: o = Oracle.mk_output None None (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input None None
                                   (Some (SeqMemory.value_map m, SeqMemory.flags m))>>) /\
      (<<PERM: p1 = Perms.meet p p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) = m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold Oracle.wf_input in EVENT. des. inv STEP.
    hexploit input_transl_release1; eauto. intro IREL; des.
    hexploit input_transl_acquire0; eauto. intro IACQ; des.
    hexploit input_transl_access0; eauto. intro IACC; des.
    inv REL.
    { rewrite IREL in H0; ss. }
    clear RELEASE RELEASE0.
    inv UPD.
    2:{ rewrite IACC in H2; ss. }
    inv ACQ.
    2:{ rewrite IACQ in H4; ss. }
    clear ACQUIRE ACQUIRE0.
    inv MEM. ss. esplits; auto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_rel2_full:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_rel : Perms.t),
      (<<OO: o = Oracle.mk_output None None (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input None None
                                   (Some (SeqMemory.value_map m, SeqMemory.flags m))>>) /\
      (<<PERM: p1 = Perms.meet p p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) = m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP. clarify.
    inv ACQ.
    2:{ hexploit ACQUIRE. rewrite <- H0. ss. i; clarify. }
    clear ACQUIRE ACQUIRE0.
    inv UPD.
    2:{ hexploit UPDATE. rewrite <- H2; ss. i. rewrite ACC in H1. des. hexploit H1. do 2 eexists. refl. i; des; ss. }
    inv REL.
    { hexploit RELEASE0; auto. i. rewrite <- H4 in H1. ss. }
    clear RELEASE RELEASE0.
    inv MEM. ss.
    do 1 eexists. splits; auto.
    destruct o; ss. rewrite <- H; rewrite <- H3; rewrite <- H5. ss.
    destruct i; ss. rewrite <- H0; rewrite <- H2; rewrite <- H4. ss.
  Qed.

  Lemma red_rel2:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_rel : Perms.t),
      (<<RELPERM: p1 = Perms.meet (p) (p_rel)>>) /\
      (<<RELMEMV: SeqMemory.value_map m1 = SeqMemory.value_map m>>) /\
      (<<RELMEMF: SeqMemory.flags m1 = Flags.bot>>).
  Proof.
    i. hexploit red_rel2_full; eauto. i; des. destruct m, m1; ss.
    do 1 eexists. splits; eauto.
  Qed.

  Lemma red_acq_rel2_oracle:
    forall p m ev0 i0 i o p1 m1
      (ACC: Oracle.in_access i0 = None)
      (ISACQ: Oracle.in_acquire i0 = Some ())
      (ISREL: Oracle.in_release i0 = Some ())
      (INPUTLE: Oracle.input_le i0 (SeqEvent.get_oracle_input i))
      (EVENT: Oracle.wf_input ev0 i0)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq p_rel : Perms.t) (v_acq : ValueMap.t),
      (<<OO: o = Oracle.mk_output None (Some (p_acq, v_acq)) (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input None
                                   (Some m.(SeqMemory.flags))
                                   (Some (ValueMap.acquire (Perms.acquired p p_acq) v_acq
                                                           (SeqMemory.value_map m), (SeqMemory.flags m)))>>) /\
      (<<PERM: p1 = Perms.meet (Perms.join p p_acq) p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired p p_acq)
                                v_acq m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold Oracle.wf_input in EVENT. des. inv STEP.
    hexploit input_transl_release1; eauto. intro IREL; des.
    hexploit input_transl_acquire1; eauto. intro IACQ; des.
    hexploit input_transl_access0; eauto. intro IACC; des.
    inv REL.
    { rewrite IREL in H0; ss. }
    clear RELEASE RELEASE0.
    inv UPD.
    2:{ rewrite IACC in H2; ss. }
    inv ACQ.
    { rewrite IACQ in H4; ss. }
    clear ACQUIRE ACQUIRE0.
    inv MEM. inv MEM0. ss. esplits; auto.
    destruct o; ss; clarify. destruct i; ss; clarify.
  Qed.

  Lemma red_acq_rel2_full:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq p_rel : Perms.t) (v_acq : ValueMap.t),
      (<<OO: o = Oracle.mk_output None (Some (p_acq, v_acq)) (Some p_rel)>>) /\
      (<<IN: i = SeqEvent.mk_input None
                                   (Some m.(SeqMemory.flags))
                                   (Some (ValueMap.acquire (Perms.acquired p p_acq) v_acq
                                                           (SeqMemory.value_map m), (SeqMemory.flags m)))>>) /\
      (<<PERM: p1 = Perms.meet (Perms.join p p_acq) p_rel>>) /\
      (<<MEMV: m1.(SeqMemory.value_map) =
               ValueMap.acquire (Perms.acquired p p_acq)
                                v_acq m.(SeqMemory.value_map)>>) /\
      (<<MEMF: m1.(SeqMemory.flags) = Flags.bot>>).
  Proof.
    i. unfold SeqEvent.wf_input in EVENT. des. inv STEP. clarify.
    inv ACQ.
    { hexploit ACQUIRE0; auto. i. rewrite <- H0 in H1. ss. }
    clear ACQUIRE ACQUIRE0.
    inv REL.
    { hexploit RELEASE0; auto. i. rewrite <- H2 in H1. ss. }
    clear RELEASE RELEASE0.
    inv UPD.
    2:{ hexploit UPDATE. rewrite <- H4; ss. i. rewrite ACC in H1. des. hexploit H1. do 2 eexists. refl. i; des; ss. }
    inv MEM. inv MEM0. ss. do 3 eexists. splits; auto.
    destruct o; ss. rewrite <- H; rewrite <- H3; rewrite <- H5. ss.
    destruct i; ss. rewrite <- H0; rewrite <- H2; rewrite <- H4. ss.
  Qed.

  Lemma red_acq_rel2:
    forall p m ev i o p1 m1
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
    exists (p_acq p_rel : Perms.t) (v_acq : ValueMap.t) (f_acq : Flags.t),
      (<<ACQFLAG: Flags.le (f_acq) (SeqMemory.flags m)>>) /\
      (<<PERM1: p1 = Perms.meet (Perms.join (p) (p_acq)) (p_rel)>>) /\
      (<<MEMV1: SeqMemory.value_map m1 = (ValueMap.acquire (Perms.acquired p p_acq) v_acq (SeqMemory.value_map m))>>) /\
      (<<MEMF1: SeqMemory.flags m1 = Flags.bot>>).
  Proof.
    i. hexploit red_acq_rel2_full; eauto. i; des. destruct m, m1; ss.
    do 3 eexists. esplits; eauto. refl.
  Qed.

End REDAT.



Section REDSTEP.

  Lemma step_rlx:
    forall ev l v i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_rlx_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des.
    hexploit H. i; des. clear H0. hexploit H1; clear H1. rewrite ACC. eauto. i; des; clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
  Qed.

  Lemma step_acq:
    forall ev l v i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_acq_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des.
    hexploit H. i; des. clear H0. hexploit H1; clear H1. rewrite ACC. eauto. i; des; clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
  Qed.

  Lemma step_rel:
    forall ev l v i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_rel_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des.
    hexploit H. i; des. clear H0. hexploit H1; clear H1. rewrite ACC. eauto. i; des; clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
  Qed.

  Lemma step_acq_rel:
    forall ev l v i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = Some (l, v))
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_acq_rel_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des.
    hexploit H. i; des. clear H0. hexploit H1; clear H1. rewrite ACC. eauto. i; des; clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
  Qed.

  Lemma step_rlx2:
    forall ev i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (NOREL: is_release ev = false)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_rlx2_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des. clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
    Unshelve. all: ss. all: try exact 0. exact false.
  Qed.

  Lemma step_acq2:
    forall ev i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (NOREL: is_release ev = false)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_acq2_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des. clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
    Unshelve. all: ss. all: try exact 0. exact false.
  Qed.

  Lemma step_rel2:
    forall ev i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (NOACQ: is_acquire ev = false)
      (ISREL: is_release ev = true)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_rel2_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des. clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
    Unshelve. all: ss. all: try exact 0. exact false.
  Qed.

  Lemma step_acq_rel2:
    forall ev i_tgt o p src_m tgt_m p1 mem_tgt
      (ACC: is_accessing ev = None)
      (ATOMIC: is_atomic_event ev)
      (ISACQ: is_acquire ev = true)
      (ISREL: is_release ev = true)
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      (<<IN_SRC: SeqEvent.wf_input ev i_src>>) /\
      (<<STEP_SRC: SeqEvent.step i_src o p src_m p1 mem_src>>).
  Proof.
    i. hexploit red_acq_rel2_full; eauto. i; des.
    subst o i_tgt. ss. inv INPUT. ss. des. clarify.
    eexists (SeqEvent.mk_input _ _ _). esplits.
    2:{ repeat econs; eauto. }
    repeat econs; i; ss; des; clarify; eauto.
    Unshelve. all: ss. all: try exact 0. exact false.
  Qed.

  Lemma exists_input_no_acq:
    forall pe (NOACQ: is_acquire pe = false) m0 p0,
      (exists i,
          (forall o (WFO: Oracle.wf_output pe o), exists m1 p1, (SeqEvent.step i o p0 m0 p1 m1)) /\
          (Oracle.wf_input pe (SeqEvent.get_oracle_input i)) /\
          (SeqEvent.wf_input pe i)).
  Proof.
    i. destruct (is_accessing pe) eqn:ACC, (is_release pe) eqn:REL.
    - destruct p. eexists (SeqEvent.mk_input (Some (t, _, _, _)) None (Some _)). splits.
      2:{ econs; ss; eauto. ii. rewrite ACC. split; i; des; clarify; eauto. clarify. }
      2:{ econs; ss; eauto. ii. rewrite ACC. split; i; des; clarify; eauto. clarify. }
      i. unfold Oracle.wf_output in WFO. des. clarify.
      destruct o; ss. destruct out_access, out_acquire, out_release; ss; clearb; try by contra.
      2:{ hexploit UPDATE0. rewrite ACC; ss. i; clarify. }
      do 2 eexists. econs; ss. econs; eauto. econs; eauto. econs; eauto. econs; eauto. econs.
    - destruct p. eexists (SeqEvent.mk_input (Some (t, _, _, _)) None None). splits.
      2:{ econs; ss; eauto. ii. rewrite ACC. split; i; des; clarify; eauto. clarify. }
      2:{ econs; ss; eauto. ii. rewrite ACC. split; i; des; clarify; eauto. clarify. }
      i. unfold Oracle.wf_output in WFO. des. clarify.
      destruct o; ss. destruct out_access, out_acquire, out_release; ss; clearb; try by contra.
      2:{ hexploit UPDATE0. rewrite ACC; ss. i; clarify. }
      do 2 eexists. econs; ss. econs; eauto. econs; eauto. econs; eauto. econs; eauto.
    - eexists (SeqEvent.mk_input None None (Some _)). splits.
      2:{ econs; ss; eauto. ii. split; i; des; clarify; eauto. clarify. }
      2:{ econs; ss; eauto. ii. split; i; des; clarify; eauto. clarify. }
      i. unfold Oracle.wf_output in WFO. des. clarify.
      destruct o; ss. destruct out_access, out_acquire, out_release; ss; clearb; try by contra.
      { hexploit UPDATE; auto. rewrite ACC; ss. }
      do 2 eexists. econs; ss. econs; eauto. econs; eauto. econs; eauto. econs; eauto.
    - eexists (SeqEvent.mk_input None None None). splits.
      2:{ econs; ss; eauto. ii. split; i; des; clarify; eauto. clarify. }
      2:{ econs; ss; eauto. ii. split; i; des; clarify; eauto. clarify. }
      i. unfold Oracle.wf_output in WFO. des. clarify.
      destruct o; ss. destruct out_access, out_acquire, out_release; ss; clearb; try by contra.
      { hexploit UPDATE; auto. rewrite ACC; ss. }
      do 2 eexists. econs; ss. econs; eauto. econs; eauto. econs; eauto.
  Qed.

End REDSTEP.



Section ORACLE.

  Lemma oracle_no_acquire:
    forall e0 e i0
      (ACQUIRE : ~ is_acquire e)
      (EVENT : ProgramEvent.le e0 e)
      (INPUT0 : Oracle.wf_input e0 i0)
    ,
      Oracle.in_acquire i0 = None.
  Proof.
    i. unfold Oracle.wf_input in INPUT0. des. unfold ProgramEvent.le in EVENT.
    clear UPDATE RELEASE RELEASE0.
    des_ifs; destruct (Oracle.in_acquire i0); ss; try by contra.
    - hexploit ACQUIRE0; auto; i. destruct ord; ss.
    - des; clarify. hexploit ACQUIRE0; auto; i. destruct ordr0; ss.
    - hexploit ACQUIRE0; auto; i. destruct ordw; destruct ordr; ss.
  Qed.

  Lemma oracle_access_none:
    forall e0 e i0
      (ORACLE: Oracle.in_access i0 = None)
      (EVENT: ProgramEvent.le e0 e)
      (INPUT0 : Oracle.wf_input e0 i0)
    ,
      is_accessing e = None.
  Proof.
    i. unfold Oracle.wf_input in INPUT0. des. unfold ProgramEvent.le in EVENT.
    clear ACQUIRE ACQUIRE0 RELEASE RELEASE0.
    des_ifs; destruct (Oracle.in_access i0); ss; clarify; try by contra.
    all: hexploit UPDATE; i; des; hexploit H0; i; des; ss; eauto.
  Qed.

  Lemma oracle_access_same:
    forall e0 e i0 t0 t1 t2
      (ORACLE: Oracle.in_access i0 = Some (t0, t1, t2))
      (EVENT: ProgramEvent.le e0 e)
      (INPUT0 : Oracle.wf_input e0 i0)
    ,
      exists val, is_accessing e = Some (t0, val).
  Proof.
    i. unfold Oracle.wf_input in INPUT0. des. unfold ProgramEvent.le in EVENT.
    clear ACQUIRE ACQUIRE0 RELEASE RELEASE0.
    des_ifs; destruct (Oracle.in_access i0); ss; clarify; try by contra.
    1,5,6,7: hexploit UPDATE; i; des; hexploit H; eauto.
    - hexploit UPDATE. i; des. hexploit H0; eauto. i; des. clarify; eauto.
    - des; clarify. hexploit UPDATE. i; des. hexploit H0; eauto. i; des. clarify; eauto.
    - des; clarify. hexploit UPDATE. i; des. hexploit H0; eauto. i; des. clarify; eauto.
  Qed.

End ORACLE.



Section UPTO.
Section LANG.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Lemma event_step_flags
        i o p0 p1 m0 m1
        (STEP: SeqEvent.step i o p0 m0 p1 m1)
    :
      Flags.le (SeqMemory.flags m0)
               (Flags.join (SeqMemory.flags m1) (SeqEvent.written i)).
  Proof.
    inv STEP.
    inv ACQ.
    { clear H. inv UPD.
      { clear H. inv REL.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          rewrite flags_join_bot_l. rewrite flags_join_bot_r. refl.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          rewrite flags_join_bot_l.
          inv MEM. ss. rewrite flags_join_bot_l. refl.
      }
      { clear H. inv REL.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. inv MEM0. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
      }
    }
    { clear H. inv MEM. ss. inv UPD; ss.
      { clear H. inv REL; ss.
        - clear H. apply Flags.join_ge_l.
        - clear H. inv MEM; ss. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          do 2 rewrite flags_join_bot_l. refl.
      }
      { clear H. inv REL; ss.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. inv MEM0. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
      }
    }
  Qed.

  Lemma at_step_flags
        e i o (th0 th1: SeqThread.t (lang_src))
        (STEP: SeqThread.at_step e i o th0 th1)
    :
      Flags.le (SeqMemory.flags (SeqState.memory (SeqThread.state th0)))
               (Flags.join (SeqMemory.flags (SeqState.memory (SeqThread.state th1))) (SeqEvent.written i)).
  Proof.
    inv STEP. ss. eapply event_step_flags; eauto.
  Qed.


  Lemma one_na_step_flags
        (st1 st2: SeqState.t (lang_src)) p
        (STEP: SeqState.na_step p MachineEvent.silent st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    inv STEP. inv LOCAL; try refl. des_ifs.
    destruct m0; ss. ii. unfold Flags.update. condtac.
    - destruct (flags loc0); ss.
    - refl.
  Qed.

  Lemma na_step_flags
        (th0 th1: SeqThread.t (lang_src))
        (STEP: SeqThread.na_step (@SeqState.na_step lang_src) MachineEvent.silent th0 th1)
    :
      Flags.le (SeqMemory.flags (SeqState.memory (SeqThread.state th0)))
               (SeqMemory.flags (SeqState.memory (SeqThread.state th1))).
  Proof.
    inv STEP. eapply one_na_step_flags; eauto.
  Qed.

  Lemma na_steps_flags
        (st1 st2: SeqState.t (lang_src)) p
        (STEPS: rtc (SeqState.na_step p MachineEvent.silent) st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    induction STEPS.
    { refl. }
    hexploit one_na_step_flags; eauto.
    i. etrans; eauto.
  Qed.

  Lemma one_na_step_flags_events
        (st1 st2: SeqState.t (lang_src)) p e
        (STEP: SeqState.na_step p e st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    destruct e.
    { eapply one_na_step_flags; eauto. }
    - inv STEP. inv LOCAL. des_ifs.
    - inv STEP. inv LOCAL; ss; try refl.
      des_ifs. ii. unfold Flags.update. clear Heq. des_ifs. destruct (SeqMemory.flags m0 loc); ss. refl.
  Qed.

  Lemma opt_na_step_flags_events
        (st1 st2: SeqState.t (lang_src)) p e
        (STEP: SeqState.na_opt_step p e st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    inv STEP. eapply one_na_step_flags_events; eauto. refl.
  Qed.


  Lemma partial_step_flags tr w th0 th1
        (STEPS: SeqThread.steps (@SeqState.na_step lang_src) tr th0 th1)
        (WF: Oracle.wf th0.(SeqThread.oracle))
        (TRACE: SeqThread.writing_trace tr w)
    :
      (Flags.le (th0.(SeqThread.state).(SeqState.memory).(SeqMemory.flags))
                (Flags.join th1.(SeqThread.state).(SeqState.memory).(SeqMemory.flags) w)).
  Proof.
    depgen w. induction STEPS; i; ss.
    { inv TRACE. rewrite flags_join_bot_r. refl. }
    { hexploit IHSTEPS; clear IHSTEPS; eauto.
      { inv STEP. ss. }
      { i. hexploit na_step_flags; eauto. i. etrans. 2:eauto. auto. }
    }
    inv TRACE.
    hexploit IHSTEPS; clear IHSTEPS; eauto.
    { inv STEP. ss. unfold Oracle.wf in WF. punfold WF. 2: eapply Oracle.wf_mon.
      inv WF. hexploit WF0; clear WF0; eauto. i; des. pclearbot. auto. }
    i. rename H into IH.
    hexploit at_step_flags; eauto. i. etrans. eauto. clear H.
    match goal with | [|-_ _ (_ ?a (_ ?b ?c))] =>
                      replace (Flags.join a (Flags.join b c)) with (Flags.join (Flags.join a c) b) end.
    2:{ rewrite flags_join_comm. rewrite flags_join_assoc. symmetry.
        rewrite flags_join_assoc. f_equal. rewrite flags_join_comm. auto. }
    apply Flags.join_mon_l. auto.
  Qed.
End LANG.


  Variant deferred_le_sf_ctx
          (sim_seq:
             forall
               (lang_src: language) (lang_tgt: language)
               (sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop)
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (lang_src: language) (lang_tgt: language)
          (sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | deferred_le_sf_ctx_intro
      d1
      (LESF: Flags.le d0 (Flags.join d1 (st_src0.(SeqState.memory).(SeqMemory.flags))))
      (SIM: @sim_seq _ _ sim_terminal p0 d1 st_src0 st_tgt0).

  Lemma deferred_le_sf_ctx_mon: monotone7 deferred_le_sf_ctx.
  Proof. ii. inv IN. econs 1; eauto. Qed.

  Hint Resolve deferred_le_sf_ctx_mon: paco.

  Lemma deferred_le_sf_ctx_wrespectful: wrespectful7 _sim_seq deferred_le_sf_ctx.
  Proof.
    econs; eauto with paco.
    ii. inv PR. dup SIM. apply GF in SIM. inv SIM.
    2:{ econs 2. unfold sim_seq_failure_case in *. i. hexploit FAILURE; clear FAILURE; eauto. }
    econs 1.
    4:{ unfold sim_seq_partial_case in PARTIAL.
        ii. hexploit PARTIAL; clear PARTIAL; eauto. i; des.
        - esplits; eauto.
          hexploit partial_step_flags; eauto. i. ss.
          left. etrans. eapply Flags.join_mon_l. eapply LESF.
          etrans. rewrite <- flags_join_assoc.
          match goal with | [|- _ (_ _ (Flags.join ?a ?b)) _] => replace (Flags.join a b) with (Flags.join b a) end.
          2:{ apply flags_join_comm. }
          rewrite flags_join_assoc. eapply Flags.join_mon_l. eapply FLAGS.
          rewrite flags_join_comm.
          apply Flags.join_spec; auto. rewrite flags_join_comm. auto. refl.
        - esplits; eauto.
    }
    { clear NASTEP ATSTEP PARTIAL. unfold sim_seq_terminal_case in *. i.
      hexploit TERMINAL; clear TERMINAL; eauto. i; des.
      eexists. splits; eauto.
      etrans. eapply Flags.join_mon_l. eapply LESF. rewrite <- flags_join_assoc.
      match goal with | [|- _ (_ _ (Flags.join ?a ?b)) _] => replace (Flags.join a b) with (Flags.join b a) end.
      2:{ apply flags_join_comm. }
      rewrite flags_join_assoc. etrans. eapply Flags.join_mon_l. eapply FLAG.
      hexploit na_steps_flags; eauto. i. rewrite flags_join_comm.
      hexploit Flags.join_spec. eapply H. refl. i; auto.
    }
    { clear TERMINAL ATSTEP PARTIAL. unfold sim_seq_na_step_case in *. i.
      hexploit NASTEP; clear NASTEP; eauto. i; des.
      do 2 eexists. splits; eauto. eapply rclo7_clo_base. econs; eauto.
      hexploit opt_na_step_flags_events; eauto. i.
      hexploit na_steps_flags; eauto. i. etrans. eapply LESF. apply Flags.join_mon_r.
      etrans. eapply H0. auto.
    }
    { clear TERMINAL NASTEP PARTIAL. unfold sim_seq_at_step_case in *. i.
      hexploit ATSTEP; clear ATSTEP; eauto. i; des.
      do 3 eexists. splits; eauto. i. hexploit SIM; clear SIM; eauto. i; des.
      do 2 eexists. eexists. esplits; eauto.
      2:{ eapply rclo7_clo_base. econs. refl. eauto. }
      ss. eapply SeqEvent.input_match_mon.
      3: refl.
      { eapply SeqEvent.step_input_match. eapply STEP_SRC. eapply MATCH. }
      etrans. eapply LESF. apply Flags.join_mon_r. eapply na_steps_flags; eauto.
    }
  Qed.

  Lemma deferred_le_sf_ctx_spec: deferred_le_sf_ctx <8=
                                 gupaco7 _sim_seq
                                         (cpn7 _sim_seq).
  Proof. i. eapply wrespect7_uclo; eauto with paco. eapply deferred_le_sf_ctx_wrespectful. Qed.


  Lemma sim_seq_upto_deferred
        g p d0 d1 lang_src lang_tgt src tgt sim_terminal
        (LE: Flags.le d0 d1)
        (SIM: gupaco7 _sim_seq (cpn7 _sim_seq) g
                      lang_src lang_tgt sim_terminal
                      p d1 src tgt)
    :
      gupaco7 _sim_seq (cpn7 _sim_seq) g lang_src lang_tgt sim_terminal p d0 src tgt.
  Proof.
    guclo deferred_le_sf_ctx_spec. econs; eauto. etrans; eauto. apply Flags.join_ge_l.
  Qed.



  Variant seqevent_in_access_le (i0 i1: SeqEvent.input) : Prop :=
  | in_access_none
      (IN0: i0.(SeqEvent.in_access) = None)
      (IN1: i1.(SeqEvent.in_access) = None)
  | in_access_some
      l v0 f0 v1 f1 vn
      (VAL: Const.le v0 v1)
      (FLAG: Flag.le f0 f1)
      (IN0: i0.(SeqEvent.in_access) = Some (l, v0, f0, vn))
      (IN1: i1.(SeqEvent.in_access) = Some (l, v1, f1, vn))
  .

  Variant seqevent_in_acquire_le (i0 i1: SeqEvent.input) : Prop :=
  | in_acquire_none
      (IN0: i0.(SeqEvent.in_acquire) = None)
      (IN1: i1.(SeqEvent.in_acquire) = None)
  | in_acquire_some
      f0 f1
      (FLAG: Flags.le f0 f1)
      (IN0: i0.(SeqEvent.in_acquire) = Some f0)
      (IN1: i1.(SeqEvent.in_acquire) = Some f1)
  .

  Variant seqevent_in_release_le (i0 i1: SeqEvent.input) : Prop :=
  | in_release_none
      (IN0: i0.(SeqEvent.in_release) = None)
      (IN1: i1.(SeqEvent.in_release) = None)
  | in_release_some
      v0 f0 v1 f1
      (VAL: ValueMap.le v0 v1)
      (FLAG: Flags.le f0 f1)
      (IN0: i0.(SeqEvent.in_release) = Some (v0, f0))
      (IN1: i1.(SeqEvent.in_release) = Some (v1, f1))
  .

  Definition seqevent_input_le (i0 i1: SeqEvent.input) :=
    (<<LEINACC: seqevent_in_access_le i0 i1>>) /\ (<<LEINACQ: seqevent_in_acquire_le i0 i1>>) /\
    (<<LEINREL: seqevent_in_release_le i0 i1>>).

  Lemma input_le_same_oracle_input
        i0 i1 i2
        (LE: seqevent_input_le i1 i2)
        (INPUT: Oracle.input_le i0 (SeqEvent.get_oracle_input i1))
    :
      Oracle.input_le i0 (SeqEvent.get_oracle_input i2).
  Proof.
    destruct i0, i1, i2. unfold seqevent_input_le in LE. unfold Oracle.input_le in *. des. ss. splits.
    2:{ destruct in_acquire0, in_acquire1, in_acquire; ss. inv LEINACQ; ss. inv LEINACQ; ss. }
    2:{ destruct in_release0, in_release1, in_release; ss. inv LEINREL; ss. inv LEINREL; ss. }
    clear ACQUIRE RELEASE LEINACQ LEINREL. inv LEINACC; ss; subst; ss.
    destruct in_access; ss. unfold Oracle.in_access_le in *. des_ifs. des; clarify. splits; auto.
    - etrans; eauto.
    - etrans; eauto.
  Qed.

  Lemma input_le_wf
        ev i1 i2
        (LE: seqevent_input_le i1 i2)
        (INPUT: SeqEvent.wf_input ev i1)
    :
      SeqEvent.wf_input ev i2.
  Proof.
    destruct i1, i2. unfold seqevent_input_le in LE. unfold SeqEvent.wf_input in *. des. ss. splits.
    2:{ destruct in_acquire0, in_acquire, (is_acquire ev); ss. inv LEINACQ; ss. inv LEINACQ; ss. }
    2:{ destruct in_release0, in_release, (is_release ev); ss. inv LEINREL; ss. inv LEINREL; ss. }
    clear ACQUIRE ACQUIRE0 RELEASE RELEASE0 LEINACQ LEINREL. inv LEINACC; ss; subst; ss.
    i. split; i.
    - des. clarify. eapply UPDATE; eauto.
    - hexploit UPDATE; clear UPDATE. i; des. clear H0. hexploit H1; clear H1; eauto. i; des. inv H0. eauto.
  Qed.

  Lemma input_le_written_le
        i1 i2
        (LEIN : seqevent_input_le i1 i2)
    :
      Flags.le (SeqEvent.written i1) (SeqEvent.written i2).
  Proof.
    destruct i1, i2. unfold seqevent_input_le in LEIN. des; ss. unfold SeqEvent.written. ss.
    clear LEINACQ. inv LEINACC; ss; subst; ss.
    - rewrite ! flags_join_bot_l. inv LEINREL; ss; subst ;ss.
    - inv LEINREL; ss; subst ;ss.
      + des_ifs. refl.
      + des_ifs.
        * apply Flags.join_mon_r. auto.
        * rewrite ! flags_join_bot_l. etrans. eauto. apply Flags.join_ge_r.
  Qed.

  Lemma input_le_match
        x1 d1 i1 i2 i_tgt
        (MATCH : SeqEvent.input_match x1 d1 i1 i_tgt)
        (INLE : seqevent_input_le i1 i2)
    :
      SeqEvent.input_match x1 d1 i2 i_tgt.
  Proof.
    destruct i1, i2. unfold seqevent_input_le in INLE. des; ss. inv MATCH. ss.
    inv LEINACC; ss.
    { inv LEINACQ; ss.
      { inv LEINREL; ss; clarify.
        - econs; ss; eauto.
        - econs; ss; eauto. inv RELEASE. econs; eauto.
          + i. etrans; eauto.
          + etrans; eauto. apply Flags.join_mon_l; auto.
      }
      { inv LEINREL; ss; clarify.
        - econs; ss; eauto. inv ACQUIRE; ss. econs; eauto. etrans; eauto.
        - inv RELEASE; inv ACQUIRE. ss. econs; ss; eauto.
          + rewrite <- H3. econs; eauto. etrans; eauto.
          + rewrite <- H4. econs; eauto.
            * i. etrans; eauto.
            * etrans; eauto. apply Flags.join_mon_l; auto.
      }
    }
    { inv LEINACQ; ss.
      { inv ACCESS; ss. inv LEINREL; ss; subst.
        - econs; ss; eauto. rewrite <- H6. econs; eauto. etrans; eauto. etrans; eauto.
        - inv RELEASE; ss. econs; ss; eauto.
          + rewrite <- H6. econs; eauto. etrans; eauto. etrans; eauto.
          + rewrite <- H4. econs; eauto.
            * i. etrans; eauto.
            * etrans; eauto. apply Flags.join_mon_l; auto.
      }
      { inv ACCESS; ss. inv ACQUIRE; ss. inv LEINREL; ss; subst.
        - econs; ss; eauto.
          + rewrite <- H6. econs; eauto. etrans; eauto. etrans; eauto.
          + rewrite <- H3. econs; eauto. etrans; eauto.
        - inv RELEASE; ss. econs; ss; eauto.
          + rewrite <- H6. econs; eauto. etrans; eauto. etrans; eauto.
          + rewrite <- H3. econs; eauto. etrans; eauto.
          + rewrite <- H5. econs; eauto.
            * i. etrans; eauto.
            * etrans; eauto. apply Flags.join_mon_l; auto.
      }
    }
  Qed.

  Definition trace_le0 (t0 t1: (ProgramEvent.t * SeqEvent.input * Oracle.output)) : Prop :=
    let '(pe0, i0, o0) := t0 in
    let '(pe1, i1, o1) := t1 in
    (<<LEPE: pe0 = pe1>>) /\ (<<LEIN: seqevent_input_le i0 i1>>) /\ (o0 = o1).

  Definition trace_le (tr0 tr1: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) :=
    List.Forall2 trace_le0 tr0 tr1.

  Lemma writing_trace_mon_on_trace
        tr0 tr w
        (TRACE: SeqThread.writing_trace tr w)
        (LE: trace_le tr tr0)
    :
      exists w0, (SeqThread.writing_trace tr0 w0) /\ (Flags.le w w0).
  Proof.
    depgen tr0. induction TRACE; i; ss.
    { inv LE. exists Flags.bot. split. econs. refl. }
    inv LE. rename l' into tr2. destruct y as [y o2]. destruct y as [e2 i2]. eapply IHTRACE in H3. des. clear IHTRACE.
    unfold trace_le0 in *. des. clarify. eexists. split. econs; eauto.
    etrans. eapply Flags.join_mon_r. eauto. apply Flags.join_mon_l. apply input_le_written_le; auto.
  Qed.


  Definition mem_le (m0 m1: SeqMemory.t) : Prop :=
    (<<LEF: Flags.le m0.(SeqMemory.flags) m1.(SeqMemory.flags)>>) /\
    (<<LEV: ValueMap.le m0.(SeqMemory.value_map) m1.(SeqMemory.value_map)>>).


  Ltac unfold_many2 := unfold SeqMemory.write in *; unfold_many; ss.

  Lemma thread_na_step_le
        lang_src
        memory1 memory0 state o p th1
        (LE: mem_le memory1 memory0)
        (STEPS: SeqThread.na_step (SeqState.na_step (lang:=lang_src)) MachineEvent.silent
                                  {|
                                    SeqThread.state := {| SeqState.state := state; SeqState.memory := memory1 |};
                                    SeqThread.perm := p;
                                    SeqThread.oracle := o
                                  |} th1)
    :
      exists th0,
        (<<STEPS: SeqThread.na_step (SeqState.na_step (lang:=lang_src)) MachineEvent.silent
                                   {| SeqThread.state := {| SeqState.state := state; SeqState.memory := memory0 |};
                                      SeqThread.perm := p;
                                      SeqThread.oracle := o |}
                                   th0>>) /\
        (<<STATE: (th1.(SeqThread.state).(SeqState.state)) = (th0.(SeqThread.state).(SeqState.state))>>) /\
        (<<PERM: (th1.(SeqThread.perm)) = (th0.(SeqThread.perm))>>) /\
        (<<ORACLE: (th1.(SeqThread.oracle)) = (th0.(SeqThread.oracle))>>) /\
        (<<MEMLE: mem_le (th1.(SeqThread.state).(SeqState.memory)) (th0.(SeqThread.state).(SeqState.memory))>>).
  Proof.
    unfold mem_le in LE. des. inv STEPS. inv STEP. inv LOCAL; ss.
    - esplits. econs. econs. eauto. econs. all: ss.
    - esplits. econs. econs. eauto. econs; auto. i. destruct (p loc); ss. etrans. eapply VAL; eauto. eapply LEV. all: ss.
    - esplits. econs. econs. eauto. econs; auto. all: ss. econs; eauto.
      + ii. unfold_many2. des_ifs.
      + ii. unfold_many2. des_ifs. refl.
  Qed.

  Lemma state_na_step_le
        lang_src
        st_src1 x2 x0 ev
        (MEMLE: mem_le (SeqState.memory st_src1) (SeqState.memory x2))
        (STATE: SeqState.state st_src1 = SeqState.state x2)
        (st_src0: SeqState.t lang_src)
        (STEP : SeqState.na_step x0 ev st_src1 st_src0)
    :
      exists st_src2 : SeqState.t lang_src,
        (<<STEPS: SeqState.na_step x0 ev x2 st_src2>>) /\
        (<<STATE: SeqState.state st_src2 = SeqState.state st_src0>>) /\
        (<<MEMLE: mem_le (SeqState.memory st_src0) (SeqState.memory st_src2)>>).
  Proof.
    destruct st_src1, x2; ss.
    inv STEP. inv LOCAL; ss; subst.
    - esplits.
      { econs; eauto. econs. }
      all: ss.
    - esplits.
      { econs; eauto. econs; eauto. i. destruct (x0 loc); ss. etrans. eapply VAL; eauto. unfold mem_le in MEMLE; des. apply LEV. }
      all: ss.
    - destruct (x0 loc) eqn:PERMCASE; ss.
      + esplits.
        { econs; eauto. econs; eauto. rewrite PERMCASE. ss. }
        all: ss. unfold mem_le in *. des. unfold_many2. split; ii.
        * des_ifs.
        * des_ifs. refl.
      + esplits.
        { econs; eauto. econs; eauto. rewrite PERMCASE. ss. }
        all: ss. unfold mem_le in *. des. unfold_many2. split; ii.
        * des_ifs.
        * des_ifs. refl.
    - esplits.
      { econs; eauto. econs. }
      all: ss.
    - esplits.
      { econs; eauto. econs. auto. }
      all: ss.
  Qed.

  Lemma state_na_steps_le
        lang_src
        st_src1 x2 x0
        (MEMLE: mem_le (SeqState.memory st_src1) (SeqState.memory x2))
        (STATE: SeqState.state st_src1 = SeqState.state x2)
        (st_src0: SeqState.t lang_src)
        (STEPS : rtc (SeqState.na_step x0 MachineEvent.silent) st_src1 st_src0)
    :
      exists st_src2 : SeqState.t lang_src,
        (<<STEPS: rtc (SeqState.na_step x0 MachineEvent.silent) x2 st_src2>>) /\
        (<<STATE: SeqState.state st_src2 = SeqState.state st_src0>>) /\
        (<<MEMLE: mem_le (SeqState.memory st_src0) (SeqState.memory st_src2)>>).
  Proof.
    depgen x2. induction STEPS; i; ss.
    { esplits. refl. all: auto. }
    destruct x, x2; ss.
    inv H. inv LOCAL; ss; subst.
    - specialize IHSTEPS with {| SeqState.state := st1; SeqState.memory := memory0 |}.
      hexploit IHSTEPS; clear IHSTEPS; ss. i; des.
      esplits.
      { econs 2. econs. eauto. econs. eapply STEPS0. }
      all: auto.
    - specialize IHSTEPS with {| SeqState.state := st1; SeqState.memory := memory0 |}.
      hexploit IHSTEPS; clear IHSTEPS; ss. i; des.
      esplits.
      { econs 2. econs. eauto. econs; auto. i. destruct (x0 loc); ss.
        { unfold mem_le in MEMLE. des. etrans. eapply VAL; auto. apply LEV. }
          eapply STEPS0. }
      all: auto.
    - destruct (x0 loc) eqn:PERMCASE; ss.
      specialize IHSTEPS with {| SeqState.state := st1; SeqState.memory := SeqMemory.write loc val memory0 |}.
      hexploit IHSTEPS; clear IHSTEPS; ss.
      { unfold mem_le in *. des. unfold_many2. split; ss.
        - ii. des_ifs.
        - ii. des_ifs. refl.
      }
      i; des. esplits.
      { econs 2. econs. eauto. econs; auto. rewrite PERMCASE. ss. eapply STEPS0. }
      all: auto.
  Qed.

  Lemma seqevent_step_le
        memory1 memory0 p i1 oo p1 m1
        (LE: mem_le memory1 memory0)
        (STEP: SeqEvent.step i1 oo p memory1 p1 m1)
    :
      exists i0 m0,
        (<<STEPS: SeqEvent.step i0 oo p memory0 p1 m0>>) /\
        (<<INLE: seqevent_input_le i1 i0>>) /\
        (<<MEMLE: mem_le m1 m0>>).
  Proof.
    unfold mem_le in LE. des.
    destruct (SeqEvent.in_access i1) eqn:IACC, (SeqEvent.in_acquire i1) eqn:IACQ, (SeqEvent.in_release i1) eqn:IREL.
    { destruct p0 as [p0 vn]. destruct p0 as [p0 f]. destruct p0 as [l v]. destruct p2 as [vm fs].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. inv MEM0. inv MEM1. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 2. 3,4: ss. 1,2: eauto.
        + econs 2. 2,3: ss. ii. unfold_flags. des_ifs.
        + econs 2. 3,4: ss.
          * ii. unfold_many2. des_ifs. refl. refl.
          * ii. unfold_flags. des_ifs.
      - ss. econs; ss. ii. unfold_many2. des_ifs. refl. refl.
    }
    { destruct p0 as [p0 vn]. destruct p0 as [p0 f]. destruct p0 as [l v].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. inv MEM0. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto.
        + econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 2. 3,4: ss. 1,2: eauto.
        + econs 2. 2,3: ss. ii. unfold_flags. des_ifs.
        + econs 1. all: ss.
      - ss. econs; ss.
        + ii. unfold_flags. des_ifs.
        + ii. unfold_many2. des_ifs. refl. refl.
    }
    { destruct p0 as [p0 vn]. destruct p0 as [p0 f]. destruct p0 as [l v]. destruct p2 as [vm fs].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. inv MEM0. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto. econs; eauto.
        + econs; eauto.
        + econs; eauto. econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 2. 3,4: ss. 1,2: eauto.
        + econs 1. all: ss.
        + econs 2. 3,4: ss.
          * ii. unfold_many2. des_ifs. refl.
          * ii. unfold_flags. des_ifs.
      - ss. econs; ss. ii. unfold_many2. des_ifs. refl.
    }
    { destruct p0 as [p0 vn]. destruct p0 as [p0 f]. destruct p0 as [l v].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto. econs; eauto.
        + econs; eauto.
        + econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 2. 3,4: ss. 1,2: eauto.
        + econs 1. all: ss.
        + econs 1. all: ss.
      - ss. econs; ss.
        + ii. unfold_flags. des_ifs.
        + ii. unfold_many2. des_ifs. refl.
    }
    { destruct p0 as [vm fs].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. inv MEM0. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto.
        + econs; eauto. econs; eauto.
        + econs; eauto. econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 1. all: ss.
        + econs 2. 2,3: ss. ii. unfold_flags. des_ifs.
        + econs 2. 3,4: ss.
          * ii. unfold_many2. des_ifs. refl.
          * ii. unfold_flags. des_ifs.
      - ss. econs; ss. ii. unfold_many2. des_ifs. refl.
    }
    { inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto.
        + econs; eauto. econs; eauto.
        + econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 1. all: ss.
        + econs 2. 2,3: ss. ii. unfold_flags. des_ifs.
        + econs 1. all: ss.
      - ss. econs; ss. ii. unfold_many2. des_ifs. refl.
    }
    { destruct p0 as [vm fs].
      inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. inv MEM. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto.
        + econs; eauto.
        + econs; eauto. econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 1. all: ss.
        + econs 1. all: ss.
        + econs 2. 3,4: ss. all: auto.
      - ss.
    }
    { inv STEP. rewrite IACC in UPD. rewrite IACQ in ACQ. rewrite IREL in REL. inv UPD. inv REL. inv ACQ.
      destruct oo; ss; clarify. ss. destruct i1; ss; clarify.
      eexists (SeqEvent.mk_input _ _ _). esplits.
      - econs; ss.
        + econs; eauto.
        + econs; eauto.
        + econs; eauto.
      - ss. unfold seqevent_input_le. splits; ss.
        + econs 1. all: ss.
        + econs 1. all: ss.
        + econs 1. all: ss.
      - ss.
    }
  Qed.

  Lemma thread_at_step_le
        lang_src
        memory1 memory0 state p o ev i1 oo th1
        (* (WF: Oracle.wf o) *)
        (LE: mem_le memory1 memory0)
        (STEPS: SeqThread.at_step (lang:=lang_src) ev i1 oo
                                  {|
                                    SeqThread.state := {| SeqState.state := state; SeqState.memory := memory1 |};
                                    SeqThread.perm := p;
                                    SeqThread.oracle := o
                                  |} th1)
    :
      exists i0 th0,
        (<<STEPS: SeqThread.at_step (lang:=lang_src) ev i0 oo
                                    {| SeqThread.state := {| SeqState.state := state; SeqState.memory := memory0 |};
                                       SeqThread.perm := p;
                                       SeqThread.oracle := o |}
                                    th0>>) /\
        (<<INLE: seqevent_input_le i1 i0>>) /\
        (<<STATE: (th1.(SeqThread.state).(SeqState.state)) = (th0.(SeqThread.state).(SeqState.state))>>) /\
        (<<PERM: (th1.(SeqThread.perm)) = (th0.(SeqThread.perm))>>) /\
        (<<ORACLE: (th1.(SeqThread.oracle)) = (th0.(SeqThread.oracle))>>) /\
        (<<MEMLE: mem_le (th1.(SeqThread.state).(SeqState.memory)) (th0.(SeqThread.state).(SeqState.memory))>>).
  Proof.
    dup LE. rename LE0 into MEMLE. unfold mem_le in LE. des. inv STEPS.
    destruct (is_accessing ev) eqn:ACC, (is_acquire ev) eqn:ACQ, (is_release ev) eqn:REL.
    { destruct p0 as [l v]. hexploit red_acq_rel_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { destruct p0 as [l v]. hexploit red_acq_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { destruct p0 as [l v]. hexploit red_rel_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { destruct p0 as [l v]. hexploit red_rlx_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { hexploit red_acq_rel2_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { hexploit red_acq2_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { hexploit red_rel2_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
    { hexploit red_rlx2_full; eauto. i; des. ss.
      hexploit seqevent_step_le; eauto. i; des. esplits; eauto.
      { econs; eauto. eapply input_le_same_oracle_input; eauto. eapply input_le_wf; eauto. }
      all: ss.
    }
  Qed.


  Lemma thread_steps_le
        lang_src
        tr1 th1 th2 th0
        (WF: Oracle.wf th1.(SeqThread.oracle))
        (STATE: th1.(SeqThread.state).(SeqState.state) = th0.(SeqThread.state).(SeqState.state))
        (MEMLE: mem_le th1.(SeqThread.state).(SeqState.memory) th0.(SeqThread.state).(SeqState.memory))
        (PERM: th1.(SeqThread.perm) = th0.(SeqThread.perm))
        (ORACLE: th1.(SeqThread.oracle) = th0.(SeqThread.oracle))
        (STEPS: SeqThread.steps (SeqState.na_step (lang:=lang_src)) tr1 th1 th2)
    :
      exists tr0 th3,
        (<<STEPS: SeqThread.steps (SeqState.na_step (lang:=lang_src)) tr0 th0 th3>>) /\
        (<<STATE: (th3.(SeqThread.state).(SeqState.state)) = (th2.(SeqThread.state).(SeqState.state))>>) /\
        (<<PERM: (th3.(SeqThread.perm)) = (th2.(SeqThread.perm))>>) /\
        (<<ORACLE: (th3.(SeqThread.oracle)) = (th2.(SeqThread.oracle))>>) /\
        (<<TRACE: trace_le tr1 tr0>>) /\
        (<<MEMLE: mem_le th2.(SeqThread.state).(SeqState.memory) th3.(SeqThread.state).(SeqState.memory)>>).
  Proof.
    depgen th0. depgen WF. induction STEPS; i.
    - esplits. econs 1. all: ss.
    - destruct th0, th3; ss; clarify. destruct state, state0; ss; clarify.
      hexploit thread_na_step_le; eauto. i; des.
      hexploit IHSTEPS.
      { inv STEP; ss. }
      eapply STATE. all: auto. i; des.
      esplits; eauto. econs 2. eapply STEPS0. eauto.
    - destruct th0, th3; ss; clarify. destruct state, state0; ss; clarify.
      hexploit thread_at_step_le; eauto. i; des.
      hexploit IHSTEPS.
      { inv STEP; ss. clarify. punfold WF. 2:eapply Oracle.wf_mon. inv WF. hexploit WF0; eauto. i; des. pclearbot. auto. }
      eapply STATE. all: auto. i; des.
      esplits; eauto. econs 3. eapply STEPS0. eauto.
      econs 2; eauto. ss.
  Qed.

  Lemma seqthread_failure_diff_mem
        lang_src
        th th3
        (FAILURE : SeqThread.failure (SeqState.na_step (lang:=lang_src)) th)
        (STATE : SeqState.state (SeqThread.state th3) = SeqState.state (SeqThread.state th))
        (PERM : SeqThread.perm th3 = SeqThread.perm th)
        (* (ORACLE : SeqThread.oracle th3 = SeqThread.oracle th) *)
        (* (MEMLE : mem_le (SeqState.memory (SeqThread.state th)) (SeqState.memory (SeqThread.state th3))) *)
    :
      SeqThread.failure (SeqState.na_step (lang:=lang_src)) th3.
  Proof.
    inv FAILURE. inv H. inv STEP. ss. destruct th3. ss. destruct state. ss. clarify. inv LOCAL.
    - econs. econs. econs; eauto. econs; eauto.
    - econs. econs. econs; eauto. econs; eauto.
    - econs. econs. econs; eauto. econs; eauto.
  Qed.


  Variant mem_le_ctx
          (sim_seq:
             forall
               (lang_src: language) (lang_tgt: language)
               (sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop)
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (lang_src: language) (lang_tgt: language)
          (sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | flags_le_ctx_intro
      st_src1
      (MEMLE: mem_le st_src1.(SeqState.memory) st_src0.(SeqState.memory))
      (STATE: st_src1.(SeqState.state) = st_src0.(SeqState.state))
      (SIM: sim_seq _ _ sim_terminal p0 d0 st_src1 st_tgt0).

  Lemma mem_le_ctx_mon: monotone7 mem_le_ctx.
  Proof. ii. inv IN. econs 1; eauto. Qed.

  Hint Resolve mem_le_ctx_mon: paco.

  Lemma mem_le_ctx_wrespectful: wrespectful7 _sim_seq mem_le_ctx.
  Proof.
    econs; eauto with paco.
    ii. inv PR. dup SIM. apply GF in SIM. inv SIM.
    2:{ econs 2. unfold sim_seq_failure_case in *. i. hexploit FAILURE; clear FAILURE; eauto. i; des.
        hexploit thread_steps_le. 6: eauto. all: ss.
        instantiate (1:= {| SeqThread.state := x5; SeqThread.perm := x3; SeqThread.oracle := o |}).
        all: ss. i; des. hexploit writing_trace_mon_on_trace. eauto. eauto. i; des.
        esplits. eapply STEPS0. eauto. eapply seqthread_failure_diff_mem; eauto.
    }
    econs 1.
    4:{ unfold sim_seq_partial_case in PARTIAL.
        ii. hexploit PARTIAL; clear PARTIAL; eauto. i; des.
        - hexploit thread_steps_le. 6: eauto. all: ss.
          instantiate (1:= {| SeqThread.state := x5; SeqThread.perm := x3; SeqThread.oracle := o |}).
          all: ss. i; des.
          hexploit writing_trace_mon_on_trace. eauto. eauto. i; des.
          esplits; eauto.
          left. depgen FLAGS. depgen MEMLE0. depgen H0. clear; i. etrans; eauto.
          etrans. eapply Flags.join_mon_l. eauto. apply Flags.join_mon_r.
          unfold mem_le in MEMLE0. des. auto.
        - hexploit thread_steps_le. 6: eauto. all: ss.
          instantiate (1:= {| SeqThread.state := x5; SeqThread.perm := x3; SeqThread.oracle := o |}).
          all: ss. i; des.
          hexploit writing_trace_mon_on_trace. eauto. eauto. i; des.
          esplits; eauto.
          right. eapply seqthread_failure_diff_mem; eauto.
    }
    { clear NASTEP ATSTEP PARTIAL. unfold sim_seq_terminal_case in *. i.
      hexploit TERMINAL; clear TERMINAL; eauto. i; des.
      hexploit state_na_steps_le; eauto. i; des. unfold mem_le in *; des.
      exists st_src2. splits; auto. rewrite STATE0; auto. rewrite STATE0; auto.
      etrans; eauto. etrans; eauto.
    }
    { clear TERMINAL ATSTEP PARTIAL. unfold sim_seq_na_step_case in *. i.
      hexploit NASTEP; clear NASTEP; eauto. i; des.
      hexploit state_na_steps_le; eauto. i; des. unfold mem_le in *; des.
      inv STEP.
      - hexploit state_na_step_le. 3: eapply STEP0. instantiate (1:=st_src3). all: ss. i; des.
        exists st_src3, st_src4. splits; auto. econs 1; auto.
        eapply rclo7_clo_base. econs; eauto.
      - esplits. eapply STEPS0. econs 2.
        eapply rclo7_clo_base. econs. 3: eauto. all: auto. econs; eauto.
    }
    { clear TERMINAL NASTEP PARTIAL. unfold sim_seq_at_step_case in *. i.
      hexploit ATSTEP; clear ATSTEP; eauto. i; des.
      hexploit state_na_steps_le; eauto. i; des. esplits; eauto. rewrite STATE0; eauto. i.
      hexploit SIM; clear SIM; eauto. i; des.
      hexploit seqevent_step_le. 2: eapply STEP_SRC. eapply MEMLE0. i; des.
      hexploit input_le_match; eauto. i; des.
      esplits. eapply STEPS1.
      { eauto. }
      { eapply input_le_wf; eauto. }
      apply rclo7_clo_base. econs. 3: eauto. all: ss.
    }
  Qed.

  Lemma mem_le_ctx_spec: mem_le_ctx <8=
                         gupaco7 _sim_seq
                                 (cpn7 _sim_seq).
  Proof. i. eapply wrespect7_uclo; eauto with paco. eapply mem_le_ctx_wrespectful. Qed.


  Lemma sim_seq_upto_mem
        lang_src lang_tgt sim_terminal
        g p d st_src0 st_src1 tgt
        (MEMLE: mem_le st_src1.(SeqState.memory) st_src0.(SeqState.memory))
        (STATE: st_src1.(SeqState.state) = st_src0.(SeqState.state))
        (SIM: gupaco7 _sim_seq
                      (cpn7 _sim_seq) g
                      lang_src lang_tgt sim_terminal
                      p d st_src1 tgt)
    :
      gupaco7 _sim_seq
              (cpn7 _sim_seq) g
              lang_src lang_tgt sim_terminal
              p d st_src0 tgt.
  Proof.
    guclo mem_le_ctx_spec. econs; eauto.
  Qed.

End UPTO.
Hint Resolve cpn7_wcompat: paco.
