From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import ITreeLang.

Require Import PromiseConsistent.
Require Import SimpleSimulation.

Require Import iPromotionDef.
Require Import SimCommon.
Require Import iSimThreadPromotion.
Require Import iSimThreadOther.

Set Implicit Arguments.


Module Promotion.
  Section LANG.
  Variable R_tid: Ident.t -> Type.

  Inductive sim_conf (p: Ident.t) (l: Loc.t) (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (TIDS: Threads.tids (Configuration.threads c_src) = Threads.tids (Configuration.threads c_tgt))
      (FIND_SRC: forall tid lang_src st_src lc_src
                   (FIND: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)),
          lang_src = lang (R_tid tid))
      (FIND_TGT: forall tid lang_tgt st_tgt lc_tgt
                   (TID: tid <> p)
                   (FIND: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang (R_tid tid))
      (FIND_TGT_PROMOTE: forall lang_tgt st_tgt lc_tgt
                   (FIND: IdentMap.find p (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang (Const.t * R_tid p))
      (PROMOTION: exists st_src lc_src st_tgt lc_tgt,
          <<FIND_SRC: IdentMap.find p (Configuration.threads c_src) = Some (existT _ (lang (R_tid p)) st_src, lc_src)>> /\
          <<FIND_TGT: IdentMap.find p (Configuration.threads c_tgt) = Some (existT _ (lang (Const.t * R_tid p)) st_tgt, lc_tgt)>> /\
          <<SIM_THREAD: SimThreadPromotion.sim_thread_all
                          l
                          (Thread.mk (lang _) st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk (lang _) st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
      (OTHER: forall tid st_src lc_src st_tgt lc_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ (lang (R_tid tid)) st_src, lc_src))
                (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ (lang (R_tid tid)) st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadOther.sim_thread
                          l
                          (Thread.mk (lang _) st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk (lang _) st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
  .
  Hint Constructors sim_conf: core.

  Lemma sim_conf_find
        p l c_src c_tgt tid
        (SIM: sim_conf p l c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply Threads.tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread_other
        p l c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf p l c_src c_tgt)
        (TID: tid <> p)
        (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ (lang (R_tid tid)) st_src, lc_src))
        (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ (lang _) st_tgt, lc_tgt)):
    SimThreadOther.sim_thread
      l
      (Thread.mk (lang _) st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
      (Thread.mk (lang _) st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt)).
  Proof.
    inv SIM. exploit OTHER; eauto.
  Qed.

  Lemma sim_conf_sim
        p l c_src c_tgt
        (SIM: sim_conf p l c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      dup SIM. inv SIM0. des. ss.
      dup WF_SRC. inv WF_SRC0. inv WF.
      exploit THREADS; eauto. i. clear DISJOINT THREADS.
      inv SIM_THREAD.
      { esplits; eauto. ii. destruct (Ident.eq_dec tid p).
        + subst. rewrite FIND in FIND_SRC0. Configuration.simplify2.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadPromotion.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
        + clear st_src lc_src st_tgt lc_tgt x FIND_SRC0 FIND_TGT0 H SC MEM.
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
      exploit SimThreadPromotion.step_reserve_sim_thread; try exact H; eauto. i. des.
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
        + subst. Configuration.simplify2.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadPromotion.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
        + Configuration.simplify2.
          clear st_src lc_src st_tgt lc_tgt x from to local sc memory
                FIND_SRC0 FIND_TGT0 H SC MEM STEP SIM2.
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

    inv STEP_TGT.
    destruct (Ident.eq_dec tid p); subst.
    { destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.silent)) eqn:SILENT.
      { (* promotion: silent *)
        destruct c_src as [ths1_src sc1_src mem1_src].
        destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
        dup SIM. inv SIM0. des. ss.
        clear FIND_SRC OTHER.
        rewrite TID in FIND_TGT0. Configuration.simplify2.
        dup WF_SRC. inv WF_SRC0. inv WF. ss.
        exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
        dup WF_TGT. inv WF_TGT0. inv WF. ss.
        exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
        exploit SimThreadPromotion.sim_thread_all_plus_step_silent; eauto. i. des.
        destruct e3_src. ss.
        assert (CSTEP: Configuration.opt_step
                         (ThreadEvent.get_machine_event e_src) p
                         (Configuration.mk ths1_src sc1_src mem1_src)
                         (Configuration.mk
                            (IdentMap.add p (existT (fun (lang: language) => (Language.state lang)) (lang _) state0, local) ths1_src)
                            sc memory)).
        { inv STEP_SRC.
          - destruct (rtc_tail STEPS_SRC).
            + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
              econs 2. econs; eauto. i.
              exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
              eapply SimThreadPromotion.sim_thread_reserve_consistent; eauto.
              apply EVENT. ii. congr.
            + inv H.
              replace (IdentMap.add p (existT (fun lang : language => Language.state lang) (lang _) state0, local) ths1_src)
                with ths1_src; auto.
              apply IdentMap.eq_leibniz. ii.
              rewrite -> IdentMap.gsident; auto.
          - econs 2. econs; eauto.
            exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            eapply SimThreadPromotion.sim_thread_reserve_consistent; eauto.
            apply EVENT. ii. congr.
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
        - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i. eapply FIND_TGT; eauto.
        - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          inv FIND. auto.
        - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto. right. auto.
        - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
          revert FIND_TGT0. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      }

      { (* promotion: failure, syscall *)
        destruct c_src as [ths1_src sc1_src mem1_src].
        destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
        dup SIM. inv SIM0. des. ss.
        clear FIND_SRC OTHER.
        rewrite TID in FIND_TGT0. Configuration.simplify2.
        dup WF_SRC. inv WF_SRC0. inv WF. ss.
        exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
        dup WF_TGT. inv WF_TGT0. inv WF. ss.
        exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
        exploit SimThreadPromotion.sim_thread_all_plus_step; eauto; ss. i. des.
        destruct e3_src. ss.
        assert (CSTEP: Configuration.step
                         (ThreadEvent.get_machine_event e0) p
                         (Configuration.mk ths1_src sc1_src mem1_src)
                         (Configuration.mk
                            (IdentMap.add p (existT (fun (lang: language) => (Language.state lang)) (lang _) state0, local) ths1_src)
                            sc memory)).
        { rewrite <- EVENT0. econs; eauto. i.
          destruct e_src; ss; try congr.
          inv STEP_SRC; [inv STEP0|].
          inv STEP0. inv LOCAL. inv LOCAL0. ss.
          ii. right. esplits; eauto.
        }
        esplits; [econs 2; eauto|].
        exploit Configuration.step_future; try exact CSTEP; eauto. s. i. des.
        hexploit Thread.rtc_all_step_prev_None.
        { eapply rtc_n1.
          - eapply rtc_implies; try exact STEPS_SRC. apply tau_union.
          - econs. econs. eapply STEP_SRC.
        }
        i. des.
        right. apply CIH. econs; ss.
        - repeat rewrite Threads.tids_add.
          repeat rewrite IdentSet.add_mem; ss.
          + rewrite Threads.tids_o. rewrite TID. ss.
          + rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
        - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          + inv FIND. ss.
          + inv SIM. eapply FIND_SRC; eauto.
        - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i. eapply FIND_TGT; eauto.
        - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          inv FIND. auto.
        - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto. left. auto.
        - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
          revert FIND_TGT0. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      }
    }

    { (* other *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC PROMOTION OTHER.
      exploit sim_conf_sim_thread_other; eauto. s. intro SIM_TH.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadOther.sim_thread_plus_step; eauto.
      { econs 2; eauto. }
      s. i. des.
      destruct e3_src. ss.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e_src) tid
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) (lang _) state0, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - destruct (rtc_tail STEPS_SRC).
          + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
            econs 2. econs; eauto.
            exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            eapply SimThreadOther.sim_thread_consistent; eauto.
            apply EVENT. congr.
          + inv H.
            replace (IdentMap.add tid (existT (fun lang : language => Language.state lang) (lang _) state0, local) ths1_src)
              with ths1_src; auto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs; eauto.
          exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP; eauto. s. i. des.
          exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
          eapply SimThreadOther.sim_thread_consistent; eauto.
          apply EVENT. congr.
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
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; try congr.
        i. eapply FIND_TGT_PROMOTE; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; try congr.
        inv SIM. des. ss. esplits; eauto.
        eapply SimThreadPromotion.sim_thread_all_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT0. rewrite IdentMap.gsspec. condtac; ss; i. Configuration.simplify2.
        + revert FIND_TGT0. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }
  Qed.


  (* promotion *)

  Definition syntax_tids (pgm: Threads.syntax): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements pgm).

  Lemma syntax_tids_o tid pgm:
    IdentSet.mem tid (syntax_tids pgm) = IdentMap.find tid pgm.
  Proof.
    unfold syntax_tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements pgm); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Inductive promote_program (p: Ident.t) (l: Loc.t) (program_src program_tgt: Threads.syntax): Prop :=
  | promote_program_intro
      (TIDS: syntax_tids program_src = syntax_tids program_tgt)
      (FIND_SRC: forall tid lang_src syn_src
                   (FIND: IdentMap.find tid program_src = Some (existT _ lang_src syn_src)),
          lang_src = lang (R_tid tid))
      (FIND_TGT: forall tid lang_tgt syn_tgt
                   (TID: tid <> p)
                   (FIND: IdentMap.find tid program_tgt = Some (existT _ lang_tgt syn_tgt)),
          lang_tgt = lang (R_tid tid))
      (PROMOTION: exists syn_src syn_tgt,
          <<FIND_SRC: IdentMap.find p program_src = Some (existT _ (lang (R_tid p)) syn_src)>> /\
          <<FIND_TGT: IdentMap.find p program_tgt = Some (existT _ (lang _) syn_tgt)>> /\
          <<PROMOTE: syn_tgt = promote_itree l Const.undef syn_src>>)
      (OTHER: forall tid syn_src syn_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid program_src = Some (existT _ (lang (R_tid tid)) syn_src))
                (FIND_TGT: IdentMap.find tid program_tgt = Some (existT _ (lang _) syn_tgt)),
          <<LOCFREE: loc_free_itree l syn_src>> /\
          <<SYNTAX: syn_src = syn_tgt>>)
  .

  Lemma init_sim_conf
        p l program_src program_tgt
        (PROMOTE: promote_program p l program_src program_tgt):
    <<SIM: sim_conf p l (Configuration.init program_src) (Configuration.init program_tgt)>>.
  Proof.
    inv PROMOTE. econs; ss; i.
    - apply IdentSet.ext. i.
      repeat rewrite Threads.tids_o.
      unfold Threads.init.
      repeat rewrite IdentMap.Facts.map_o.
      specialize (@syntax_tids_o i program_src). i.
      specialize (@syntax_tids_o i program_tgt). i.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt) eqn:TGT; ss.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src = IdentMap.find i program_src) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src = IdentMap.find i program_src) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_src) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_SRC; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_TGT; eauto.
    - hexploit PROMOTION. i. unfold Threads.init in *.
      repeat rewrite IdentMap.Facts.map_o in *. des.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) p program_tgt) eqn:TGT; ss.
      setoid_rewrite TGT in FIND_TGT0. clarify.
    - unfold Threads.init in *.
      repeat rewrite IdentMap.Facts.map_o in *. des.
      replace (@UsualFMapPositive.UsualPositiveMap'.find
                 (@sigT _ (@Language.syntax ProgramEvent.t)) p program_src) with
          (IdentMap.find p program_src) by ss.
      replace (@UsualFMapPositive.UsualPositiveMap'.find
                 (@sigT _ (@Language.syntax ProgramEvent.t)) p program_tgt) with
          (IdentMap.find p program_tgt) by ss.
      rewrite FIND_SRC0. rewrite FIND_TGT0. ss.
      esplits; eauto.
      left. econs; ss; try refl.
      + instantiate (1 := Const.undef). econs; eauto.
      + ii. rewrite Memory.bot_get in *. ss.
      + replace (Memory.max_ts l Memory.init) with Time.bot by ss.
        unfold Memory.get, Memory.init, Cell.get, Cell.init, Cell.Raw.init. ss.
        rewrite DOMap.singleton_eq. unfold Message.elt. eauto.
      + i. rewrite Memory.bot_get. ss.
      + ii. unfold Memory.get, Memory.init, Cell.get, Cell.init in GET.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_src) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:TGT; ss.
      destruct s, s0; ss.  Configuration.simplify2.
      exploit OTHER; eauto. i. des. subst.
      econs; ss; try refl.
      + i. rewrite Memory.bot_get. ss.
      + ii. rewrite Memory.bot_get in *. ss.
  Qed.

  Theorem promote_behavior
          p l program_src program_tgt
          (PROMOTE: promote_program p l program_src program_tgt):
    behaviors Configuration.step (Configuration.init program_tgt) <2=
    behaviors Configuration.step (Configuration.init program_src).
  Proof.
    exploit init_sim_conf; eauto. i. des.
    specialize (Configuration.init_wf program_src). intro WF_SRC.
    specialize (Configuration.init_wf program_tgt). intro WF_TGT.
    hexploit sim_conf_sim; eauto. i.
    exploit sim_adequacy; try exact H; eauto.
  Qed.
  End LANG.
End Promotion.
