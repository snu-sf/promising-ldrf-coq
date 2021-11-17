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
Require Import ITreeLang.



Section LANG.

  Definition is_na_inst (i: Inst.t) :=
    match i with
    | Inst.skip
    | Inst.assign _ _
    | Inst.abort
    | Inst.choose _ =>
      True
    | Inst.load _ _ ord
    | Inst.store _ _ ord =>
      Ordering.le ord Ordering.na
    | Inst.update _ _ _ ordr ordw =>
      (Ordering.le ordr Ordering.na) \/ (Ordering.le ordw Ordering.na)
    | _ => False
    end.

  Definition update_mem_na (v: Const.t) (i: Inst.t) (m: SeqMemory.t) :=
    match i with
    | Inst.store lhs _ _ =>
      SeqMemory.write lhs v m
    | _ =>
      m
    end.

  Variant match_inst_pe: Inst.t -> ProgramEvent.t -> Prop :=
  | match_inst_pe_load
      lhs rhs ord val
    :
      match_inst_pe (Inst.load lhs rhs ord) (ProgramEvent.read rhs val ord)
  | match_inst_pe_store
      lhs rhs ord val
    :
      match_inst_pe (Inst.store lhs rhs ord) (ProgramEvent.write lhs val ord)
  | match_inst_pe_update_failure
      lhs loc rmw ordr ordw val
    :
      match_inst_pe (Inst.update lhs loc rmw ordr ordw) (ProgramEvent.read loc val ordr)
  | match_inst_pe_update_success
      lhs loc rmw ordr ordw valr valw
    :
      match_inst_pe (Inst.update lhs loc rmw ordr ordw) (ProgramEvent.update loc valr valw ordr ordw)
  | match_inst_pe_fence
      ordr ordw
    :
      match_inst_pe (Inst.fence ordr ordw) (ProgramEvent.fence ordr ordw)
  | match_inst_pe_syscall
      lhs rhses sev
    :
      match_inst_pe (Inst.syscall lhs rhses) (ProgramEvent.syscall sev).

End LANG.



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
