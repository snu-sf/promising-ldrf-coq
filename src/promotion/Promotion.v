Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import PromotionDef.
Require Import SimCommon.
Require Import SimThreadPromotion.
Require Import SimThreadOther.
Require Import PSimulation.

Set Implicit Arguments.


Module Promotion.
  Lemma inj_option_pair
        A B
        (a1 a2: A)
        (b1 b2: B)
        (EQ: Some (a1, b1) = Some (a2, b2)):
    a1 = a2 /\ b1 = b2.
  Proof.
    inv EQ. ss.
  Qed.

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some (_, _) = Some (_, _) |- _] =>
             apply inj_option_pair in H; des
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             exploit eq_sigT_fst; try exact H; i; subst
           end;
       ss; subst).

  Inductive sim_conf (p: Ident.t) (l: Loc.t) (r: Reg.t) (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (TIDS: Threads.tids c_src.(Configuration.threads) = Threads.tids c_tgt.(Configuration.threads))
      (FIND_SRC: forall tid lang_src st_src lc_src
                   (FIND: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)),
          lang_src = lang)
      (FIND_TGT: forall tid lang_tgt st_tgt lc_tgt
                   (FIND: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang)
      (PROMOTION: exists st_src lc_src st_tgt lc_tgt,
          <<FIND_SRC: IdentMap.find p c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src)>> /\
          <<FIND_TGT: IdentMap.find p c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)>> /\
          <<SIM_THREAD: SimThreadPromotion.sim_thread_reserve
                          l r
                          (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                          (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>)
      (OTHER: forall tid st_src lc_src st_tgt lc_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
                (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadOther.sim_thread
                          l
                          (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                          (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>)
  .
  Hint Constructors sim_conf.


  (* TODO: move to Configuration.v *)
  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: Threads.tids ths_src = Threads.tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (Threads.tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (Threads.tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.

  Lemma sim_conf_find
        p l r c_src c_tgt tid
        (SIM: sim_conf p l r c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread_other
        p l r c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf p l r c_src c_tgt)
        (TID: tid <> p)
        (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)):
    SimThreadOther.sim_thread
      l
      (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
      (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory)).
  Proof.
    inv SIM. exploit OTHER; eauto.
  Qed.

  Theorem sim_conf_sim
          p l r c_src c_tgt
          (SIM: sim_conf p l r c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      dup SIM. inv SIM0. des. ss.
      dup WF_SRC. inv WF_SRC0. inv WF.
      exploit THREADS; eauto. i. clear DISJOINT THREADS.
      exploit SimThreadPromotion.step_reserve_sim_thread; try exact SIM_THREAD; eauto. i. des.
      destruct e2_src.
      esplits.
      - econs 2; eauto. econs.
        replace MachineEvent.silent with
            (ThreadEvent.get_machine_event (ThreadEvent.promise l from to Message.reserve Memory.op_kind_cancel)) by ss.
        econs; eauto; ss.
        ii. right. esplits; eauto. s.
        exploit TERMINAL_TGT; eauto. i. des. inv THREAD.
        exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
      - s. ii. destruct (Ident.eq_dec tid p).
        + subst. simplify.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadPromotion.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
        + simplify.
          clear st_src lc_src st_tgt lc_tgt x from to state local sc memory
                FIND_SRC0 FIND_TGT0 SIM_THREAD SC MEM STEP SIM2.
          exploit sim_conf_find; eauto. i. des.
          exploit x0; eauto. i. des.
          exploit FIND_SRC; eauto. i. subst.
          exploit FIND_TGT; eauto. i. subst.
          clear x0 x1 FIND_SRC FIND_TGT.
          exploit sim_conf_sim_thread_other; eauto. intro SIM_THREAD.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadOther.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadOther.sim_thread_promises_bot; eauto.
    }

    destruct (Ident.eq_dec tid p); subst; inv STEP_TGT.
    { (* promotion: failure *)
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. des. ss.
      clear FIND_SRC FIND_TGT OTHER.
      rewrite TID in FIND_TGT0. simplify.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadPromotion.sim_thread_reserve_plus_step; eauto. s. i. des.
      destruct e_src; ss. inv STEP_SRC. destruct e3_src. ss.
      assert (CSTEP: Configuration.step
                       MachineEvent.failure p
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add p (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { econs 1; eauto. }
      esplits; [econs 2; eauto|].
      exploit Configuration.step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None.
      { eapply rtc_n1.
        - eapply rtc_implies; try exact STEPS_SRC. apply tau_union.
        - econs. econs. eapply STEP0. }
      i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        exploit sim_conf_sim_thread_other; eauto. s. i.
        eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* promotion: normal *)
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. des. ss.
      clear FIND_SRC FIND_TGT OTHER.
      rewrite TID in FIND_TGT0. simplify.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadPromotion.sim_thread_reserve_plus_step; eauto. s. i. des.
      destruct e3_src. ss.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e_src) p
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add p (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - destruct (rtc_tail STEPS_SRC).
          + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
            econs 2. econs 2; eauto.
            * ii. subst. ss.
            * exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
              eapply SimThreadPromotion.sim_thread_consistent; eauto.
          + inv H.
            replace (IdentMap.add p (existT (fun lang : language => Language.state lang) lang state, local) ths1_src)
              with ths1_src; auto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; eauto.
          + ii. subst. ss. destruct e0; ss.
          + exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            eapply SimThreadPromotion.sim_thread_consistent; eauto.
      }
      rewrite <- EVENT0. esplits; eauto.
      exploit Configuration.opt_step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None; try eapply Thread.tau_opt_all; eauto. s. i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        exploit sim_conf_sim_thread_other; eauto. s. i.
        eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* other: failure *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT PROMOTION OTHER.
      exploit sim_conf_sim_thread_other; eauto. s. intro SIM_TH.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadOther.sim_thread_plus_step; eauto. s. i. des.
      destruct e_src; ss. inv STEP_SRC. destruct e3_src. ss.
      assert (CSTEP: Configuration.step
                       MachineEvent.failure tid
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { econs 1; eauto. }
      esplits; [econs 2; eauto|].
      exploit Configuration.step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None.
      { eapply rtc_n1.
        - eapply rtc_implies; try exact STEPS_SRC. apply tau_union.
        - econs. econs. eapply STEP0. }
      i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite x. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; try congr.
        inv SIM. des. ss. esplits; eauto.
        eapply SimThreadPromotion.sim_thread_reserve_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i. simplify.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* other: normal *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT PROMOTION OTHER.
      exploit sim_conf_sim_thread_other; eauto. s. intro SIM_TH.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadOther.sim_thread_plus_step; eauto. s. i. des.
      destruct e3_src. ss.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e_src) tid
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - destruct (rtc_tail STEPS_SRC).
          + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
            econs 2. econs 2; eauto.
            * ii. subst. ss.
            * exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
              eapply SimThreadOther.sim_thread_consistent; eauto.
          + inv H.
            replace (IdentMap.add tid (existT (fun lang : language => Language.state lang) lang state, local) ths1_src)
              with ths1_src; auto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; eauto.
          + ii. subst. ss. destruct e0; ss.
          + exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            eapply SimThreadOther.sim_thread_consistent; eauto.
      }
      rewrite <- EVENT0. esplits; eauto.
      exploit Configuration.opt_step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None; try eapply Thread.tau_opt_all; eauto. s. i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite x. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; try congr.
        inv SIM. des. ss. esplits; eauto.
        eapply SimThreadPromotion.sim_thread_reserve_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i. simplify.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }
  Qed.
End Promotion.