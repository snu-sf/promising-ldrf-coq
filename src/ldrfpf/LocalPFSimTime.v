Require Import RelationClasses.
Require Import List.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import PromiseConsistent.
Require Import Pred.
Require Import Trace.
Require Import JoinedView.

Require Import MemoryProps.
Require Import OrderedTimes.
Require SimMemory.

Require Import LocalPF.
Require Import LocalPFThread.
Require Import TimeTraced.
Require Import PFConsistentStrong.
Require Import Mapping.
Require Import GoodFuture.
Require Import CapMap.
Require Import CapFlex.
Require Import Pred.

Require Import LocalPFSim.

Set Implicit Arguments.

Section SIMTIME.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).
  Hypothesis INCR: forall nat loc, times loc (incr_time_seq nat).

  Lemma Forall2_tail A B (P: A -> B -> Prop) la lb a b
        (FORALL: List.Forall2 P (la ++ [a]) (lb ++ [b]))
    :
      List.Forall2 P la lb /\ P a b.
  Proof.
    eapply Forall2_app_inv_l in FORALL. des.
    inv FORALL0. inv H3. eapply app_inj_tail in FORALL1.
    des; clarify.
  Qed.

  Lemma promise_read_race views0 prom0 extra0 proml0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step_strong times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration L times (fun _ => True) views0 prom0 extra0 proml0 c_src0 c_mid0 c_tgt0)
        (READ: ~ List.Forall
                 (fun the => no_read_msgs
                               (all_promises (fun tid' => tid <> tid') prom0)
                               (snd the)) (tr_tgt ++ tr_cert))
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (RACEFREE: ~ pf_multi_race L c_src0)
    :
      (<<UB: forall beh, behaviors (pf_multi_step L) c_src0 beh>>).
  Proof.
    exploit times_configuration_step_future; eauto.
    { eapply times_configuration_step_strong_step; eauto. } i. des.
    exploit (@Memory.max_concrete_timemap_exists (Configuration.memory c_tgt1)); eauto.
    { eapply WF2. } intros [max MAX].
    eapply configuration_step_certify in STEPTGT; eauto. des.
    hexploit (@trace_times_list_exists (tr_tgt ++ tr_cert')). i. des.
    assert (exists (maxmap: TimeMap.t),
               (<<TIMES: forall loc' ts (IN: List.In ts (times0 loc')), Time.lt ts (maxmap loc')>>) /\
               (<<MAX: forall loc', Time.lt (Memory.max_ts loc' c_tgt0.(Configuration.memory)) (maxmap loc')>>)).
    { hexploit (@choice
                  Loc.t
                  Time.t
                  (fun loc' max =>
                     (<<TIMES: forall ts (IN: List.In ts (times0 loc')), Time.lt ts (max)>>) /\
                     (<<MAX: Time.lt (Memory.max_ts loc' c_tgt0.(Configuration.memory)) (max)>>))).
      { i. hexploit (finite_greatest (fun _ => True) (times0 x)). i. des.
        { exists (Time.incr (Time.join
                               (Memory.max_ts x (Configuration.memory c_tgt0))
                               to)).
          splits.
          { i. eapply GREATEST in IN0; auto. eapply TimeFacts.le_lt_lt; eauto.
            eapply TimeFacts.le_lt_lt.
            { eapply Time.join_r. }
            { eapply  Time.incr_spec. }
          }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. }
            { eapply  Time.incr_spec. }
          }
        }
        { exists (Time.incr (Memory.max_ts x (Configuration.memory c_tgt0))). splits.
          { i. eapply EMPTY in IN. ss. }
          { eapply Time.incr_spec. }
        }
      }
      i. des. exists f0. split.
      { ii. specialize (H loc'). des. auto. }
      { ii. specialize (H loc'). des. auto. }
    } i. des.

    assert (exists tid0 ploc pts rlc re pl0 pl1 tr0 tr1,
               (<<READING: reading_event ploc pts re>>) /\
               (<<PROMISED: prom0 tid0 ploc pts>>) /\
               (<<NEQ: tid0 <> tid>>) /\
               (<<PROML: proml0 tid0 = pl0 ++ (ploc, pts) :: pl1>>) /\
               (<<TRACE: tr0 ++ (rlc, re) :: tr1 = tr_tgt ++ tr_cert'>>) /\
               (<<NOREAD: List.Forall (fun the => no_read_msgs
                                                    (all_promises (fun tid' => tid <> tid') prom0)
                                                    (snd the)) tr0>>)).
    { assert (FORALL: ~ Forall
                        (fun the => no_read_msgs (all_promises (fun tid' => tid <> tid') prom0) (snd the))
                        (tr_tgt ++ tr_cert')).
      { erewrite list_Forall_app in READ. erewrite list_Forall_app. ii.
        des. eapply READ. split; auto.
        eapply List.Forall_forall. ii. destruct STEPTGT0.
        - eapply list_Forall2_in2 in H0; eauto. des.
          erewrite List.Forall_forall in FORALL1. exploit (FORALL1 b); auto.
          i. destruct b, x. ss. unfold no_read_msgs in x1. inv SAT; ss.
          + ii. inv H0. eapply MAPIDENT in TO.
            { subst. eauto. }
            2: { refl. }
            eapply memory_future_concrete_promised.
            { eapply Memory.future_future_weak; eauto. }
            eapply sim_configuration_forget_tgt_concrete; eauto; ss.
          + ii. inv H0. eapply MAPIDENT in FROM.
            { subst. eauto. }
            2: { refl. }
            eapply memory_future_concrete_promised.
            { eapply Memory.future_future_weak; eauto. }
            eapply sim_configuration_forget_tgt_concrete; eauto; ss.
        - des. eapply list_Forall2_in2 in H0.
          2: { eapply List.in_or_app. left. eauto. } des.
          erewrite List.Forall_forall in FORALL1. exploit (FORALL1 b); auto.
          i. destruct b, x. ss. unfold no_read_msgs in x1. inv SAT; ss.
          + ii. inv H0. eapply MAPIDENT in TO.
            { subst. eauto. }
            2: { refl. }
            eapply memory_future_concrete_promised.
            { eapply Memory.future_future_weak; eauto. }
            eapply sim_configuration_forget_tgt_concrete; eauto; ss.
          + ii. inv H0. eapply MAPIDENT in FROM.
            { subst. eauto. }
            2: { refl. }
            eapply memory_future_concrete_promised.
            { eapply Memory.future_future_weak; eauto. }
            eapply sim_configuration_forget_tgt_concrete; eauto; ss.
      }
      exploit list_first_occurence. i. des.
      { exfalso. eapply FORALL; eauto. }
      destruct a as (rlc, re). ss.
      assert (exists ploc pts tid0, (<<PROMISED: prom0 tid0 ploc pts>>) /\ (<<READING: reading_event ploc pts re>>) /\ (<<NEQ: tid <> tid0>>)).
      { eapply NNPP. ii. eapply FAIL. unfold no_read_msgs. ss. des_ifs.
        - ii. inv H0. eapply H; eauto. esplits; eauto. econs.
        - ii. inv H0. eapply H; eauto. esplits; eauto. econs. } des.
      assert (LIN: List.In (ploc, pts) (proml0 tid0)).
      { destruct (IdentMap.find tid0 c_tgt0.(Configuration.threads)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT.
        { inv SIM. eapply CONSISTENT in TIDTGT; eauto.
          eapply TIDTGT.(pi_consistent_promises) in PROMISED. auto. }
        { inv SIM. ss. specialize (THSJOIN tid0). specialize (THSPF tid0).
          unfold option_rel in THSJOIN.
          unfold option_rel in THSPF. des_ifs.
          eapply BOT in Heq1. des. exfalso. eapply PROM; eauto. }
      }
      eapply List.in_split in LIN. des. esplits; eauto.
    }
    des.

    exploit (@sim_configuration_certify_partial
               L times WO INCR
               (fun _ => True) tid0 ploc pts pl0 pl1); eauto.
    i. des. destruct x0; des.
    { ii. inv STEPSRC; ss. econs 3; eauto. econs; eauto. } exfalso.
    inv STEPSRC.
    2: { inv FINAL. } rename STEP0 into STEPSRC.

    hexploit times_configuration_opt_step_future; try apply STEPTGT; eauto. i. des.
    hexploit JConfiguration.opt_step_future; try apply STEPMID; eauto. i. des.
    hexploit pf_step_trace_future; try apply STEPSRC; eauto. i. des.

    assert (IDENT: map_ident_in_memory (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))
                                       (Configuration.memory c_tgt0)).
    { ii. splits; auto. eapply TimeFacts.le_lt_lt; eauto. }
    assert (MAPLT0: mapping_map_lt (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))).
    { ii. des. subst. auto. }

    dup STEP. dep_inv STEP.
    exploit good_future_configuration_step_aux.
    { eauto. }
    { eapply STEP0. }
    { eauto. }
    { eapply WF0. }
    { inv SIM0. auto. }
    { eauto. }
    { erewrite <- TID.
      inv STEPTGT; auto. inv STEP; auto.
      ss. erewrite IdentMap.gso; eauto.
    }
    { eapply map_ident_in_memory_local; eauto.
      { eapply WF_TGT; eauto. }
      { eapply WF_TGT; eauto. }
    }
    { eapply max_good_future_map; eauto. eapply WF_TGT. }
    { eauto. }
    { eapply map_ident_in_memory_closed_timemap; eauto. eapply WF_TGT. }
    { erewrite SC. refl. }
    { erewrite app_nil_r.
      eapply List.Forall_impl; try apply WFTIME; eauto. i. ss.
      eapply wf_time_evt_mon; eauto. i. ss. eauto. }
    i. des. ss.

    inv STEP. guardH CERTBOT0.
    hexploit sim_configuration_sim_thread; eauto. i. des.
    generalize (sim_configuration_forget_exclusive SIM0 WF3 TIDSRC).
    intros EXCLUSIVE.
    generalize (sim_configuration_extra_exclusive SIM0 WF3 TIDSRC).
    intros EXCLUSIVEEXTRA.

    eapply Forall_app_inv in TIMES1. des.
    exploit Trace.steps_future.
    { eapply STEPS0. }
    { eapply WF0; eauto. }
    { eapply WF0; eauto. }
    { eapply WF0; eauto. } i. ss. des.
    exploit Thread.step_future; eauto. i. des. ss. ss.

    assert (exists tr_read rlc' re' th,
               (<<STEPS: Trace.steps (tr_read ++ [(rlc', re')]) (Thread.mk _ st0 lc0 c_tgt2.(Configuration.sc) c_tgt2.(Configuration.memory)) th>>) /\
               (<<REST: exists tr_rest,
                   Trace.steps tr_rest th (Thread.mk _ st2 lc2 sc0 memory0)>>) /\
               (<<READING: reading_event ploc pts re'>>) /\
               (<<SILENT: Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) (tr_read ++ [(rlc', re')])>>) /\
               (<<WFTIME: Forall (fun the => wf_time_evt times (snd the)) (tr_read ++ [(rlc', re')])>>) /\
               (<<NOREAD: Forall (fun the => no_read_msgs (all_promises (fun tid' => tid <> tid') (fun tid' => if Ident.eq_dec tid' tid0 then prom_self else prom0 tid')) (snd the)) (tr_read ++ [(rlc', re')])>>)).
    { assert (NOREAD0: Forall (fun the => no_read_msgs (all_promises (fun tid' => tid <> tid') (fun tid' => if Ident.eq_dec tid' tid0 then prom_self else prom0 tid')) (snd the)) tr0).
      { eapply Forall_impl; try apply NOREAD; eauto. i. ss.
        eapply no_read_msgs_mon; [eauto|]. i. inv PR.
        econs; eauto. des_ifs. eapply DECR; eauto. }
      assert (NOREAD1: no_read_msgs (all_promises (fun tid' => tid <> tid') (fun tid' => if Ident.eq_dec tid' tid0 then prom_self else prom0 tid')) re).
      { assert (NPROM: ~ (all_promises (fun tid' => tid <> tid') (fun tid' => if Ident.eq_dec tid' tid0 then prom_self else prom0 tid')) ploc pts).
        { ii. inv H. des_ifs.
          { eapply (WRITTEN ploc pts); eauto.
            eapply List.in_or_app. right. ss. auto. }
          { clear - n WF_SRC SIM PROMS PROMISED.
            dup SIM. inv SIM. specialize (THSPF tid0).
            unfold option_rel in *. des_ifs.
            { inv THSPF. inv LOCAL. destruct st as [lang st].
              exploit sim_configuration_forget_exclusive; try eassumption.
              { econs; eauto. }
              i. des. ss. inv UNCH.
              set (PROM := PROMS0.(sim_promise_contents) ploc pts).
              rewrite NPROM in *. inv PROM; try by (eapply NPROM0; eauto).
            }
            { eapply BOT in Heq. des. eapply PROM; eauto. }
          }
        }
        { inv READING; eauto. }
      }

      erewrite <- TRACE in *.
      hexploit (list_match_rev tr1). i. des; clarify.
      { eapply Forall2_tail in TRACE1. des. ss.
        exists tr'0, e3.(Thread.local), e1, (Thread.mk _ st2 lc2 sc0 memory0). splits.
        { eapply Trace.steps_trans; eauto. }
        { eauto. }
        { inv READING; inv EVT; econs; eauto. }
        { eapply Forall_app; eauto. econs; eauto. ss.
          inv READING; inv EVT; eauto. }
        { eapply Forall_app; eauto. }
        { eapply Forall_app.
          { eapply Forall_forall. i.
            eapply list_Forall2_in in TRACE1; eauto. des.
            eapply Forall_forall in IN; try apply NOREAD0. ss.
            destruct a, x. ss. inv EVT0; ss. }
          { econs; eauto. ss. clear - NOREAD1 EVT. inv EVT; ss. }
        }
      }
      { rewrite app_comm_cons in *. rewrite app_assoc in TRACE1.
        eapply Forall2_tail in TRACE1. des. ss.
        replace (tr0 ++ (rlc, re) :: tl_rev) with ((tr0 ++ [(rlc, re)]) ++ tl_rev) in *.
        2: { erewrite <- app_assoc. auto. }
        eapply Forall2_app_inv_l in TRACE1. des. clarify.
        eapply Forall2_app_inv_l in TRACE1. des. clarify.
        inv TRACE3. inv H4. destruct y. des. ss.
        eapply Trace.steps_separate in STEPS0. des.
        exists l1'0, t, t0, th1. splits.
        { eauto. }
        { esplits. eapply Trace.steps_trans; eauto. }
        { inv READING; inv EVT0; econs; eauto. }
        { eapply Forall_app_inv in SILENT0. des. auto. }
        { eapply Forall_app_inv in FORALL1. des. auto. }
        { eapply Forall_app.
          { eapply Forall_forall. i.
            eapply list_Forall2_in in TRACE1; eauto. des.
            eapply Forall_forall in IN; try apply NOREAD0. ss.
            destruct a, x. ss. clear - IN EVT1. inv EVT1; ss. }
          { econs; eauto. ss. clear - NOREAD1 EVT0. inv EVT0; ss. }
        }
      }
    } des.

    exploit Trace.steps_future; try apply STEPS1; ss.
    { eapply WF0; eauto. }
    { eapply WF0; eauto. }
    { eapply WF0; eauto. } i. des.

    assert (CONSISTENT1: Local.promise_consistent th.(Thread.local)).
    { exploit Trace.steps_future; try apply REST; eauto. i. des. ss.
      eapply Trace.steps_promise_consistent; eauto. ss.
      destruct (classic (e1 = ThreadEvent.failure)) as [EQ0|NEQ0].
      { subst. inv STEP2; inv STEP. ss. inv LOCAL. inv LOCAL0. auto. }
      specialize (CONSISTENT0 NEQ0).
      eapply pf_consistent_super_strong_consistent in CONSISTENT0; eauto.
      eapply consistent_promise_consistent in CONSISTENT0; eauto.
    }

    hexploit sim_configuration_sim_thread; eauto. i. des.
    hexploit sim_thread_steps_silent; try apply STEPS1; eauto.
    { eapply Forall_forall. i. splits.
      - eapply Forall_forall in WFTIME0; eauto.
      - eapply Forall_forall in NOREAD0; eauto.
      - eapply Forall_forall in SILENT1; eauto. }
    { eapply WF3. }
    { eapply WF1. }
    { eapply WF0. }
    { eapply WF3. }
    { eapply WF1. }
    { eapply WF0. }
    { eapply WF3; eauto. }
    { eapply WF1; eauto. }
    { eapply WF0; eauto. }
    { inv SIM0. ss. }
    { inv SIM0. ss. }

    { eapply sim_configuration_forget_exclusive; eauto. }
    { eapply sim_configuration_extra_exclusive; eauto. }
    { inv SIM0. ss. }
    { eapply WF1; eauto. }
    { eapply WF1; eauto. }
    { eapply WF1; eauto. } i. des.

    exploit sim_traces_sim_event_exists.
    { eauto. }
    { eauto. }
    { eapply List.in_or_app. right. ss. eauto. }
    { ii. subst. inv READING0. }
    { inv READING0; ss. } i. des.
    eapply in_split in IN. des. subst.
    eapply Trace.steps_separate in STEPSRC0. des.
    inv STEPS3; clarify.

    exploit Trace.steps_future; try apply STEPS2; eauto.
    { eapply WF3; eauto. }
    { eapply WF3; eauto. }
    { eapply WF3; eauto. } i. des. ss.
    exploit Thread.step_future; eauto. i. des.

    eapply RACEFREE. econs.
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply sim_traces_pf in TRACE2; eauto.
      eapply Forall_app_inv in TRACE2. des. auto. }
    { eapply step_promise_consistent in STEP; eauto.
      eapply Trace.steps_promise_consistent in STEPS4; eauto.
      dep_inv THREAD.
      eapply sim_local_strong_sim_local in LOCALPF.
      eapply JSim.sim_local_promise_consistent in LOCALJOIN; eauto.
      eapply sim_promise_consistent; eauto.
    }
    { eauto. }
    { clear - EVENT READING0. inv READING0; inv EVENT; econs. }
    { exploit sim_configuration_forget_tgt_concrete; try apply SIM; eauto; ss.
      i. des; auto. }
  Qed.
End SIMTIME.
