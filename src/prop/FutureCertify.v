Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import Cover.
Require Import Mapping.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.
Require Import PFConsistent.
Require Import CapFlex.
Require Import PFConsistentStrong.

Set Implicit Arguments.

Module FutureCertify.
  Section FutureCertify.
    Variable (lang: language).

    Lemma future_memory_map
          mem mem_cap mem_future times
          (CAP: Memory.cap mem mem_cap)
          (FUTURE: Memory.future_weak mem mem_future)
          (CLOSED: Memory.closed mem):
      exists (f: Loc.t -> Time.t -> Time.t -> Prop),
        (<<IDENT: map_ident_in_memory f mem>>) /\
        (<<MAPLT: mapping_map_lt_iff f>>) /\
        (<<MEMORY: memory_map f mem_cap mem_future>>) /\
        (<<COMPLETE: forall loc to (IN: List.In to (times loc)),
            exists fto, (<<MAPPED: f loc to fto>>)>>).
    Proof.
      exploit (choice (fun loc f =>
                         (<<COMPLETE: forall to (IN: List.In to (Time.incr (Memory.max_ts loc mem)::(times loc))), exists fto, (<<MAPPED: f to fto>>)>>) /\
                         (<<SAME: forall ts (TS: Time.le ts (Memory.max_ts loc mem)), f ts ts>>) /\
                         (<<BOUND: forall to fto (MAPPED: f to fto) (TS: Time.lt (Memory.max_ts loc mem) to),
                             (Time.lt (Time.join (Memory.max_ts loc mem_future) (Memory.max_ts loc mem)) fto)>>) /\
                         (<<MAPLT: mapping_map_lt_iff_loc f>>))).
      { intros loc. hexploit shift_map_exists.
        - eapply Time.join_r.
        - eapply Time.incr_spec.
        - i. des. exists f. esplits; eauto.
          i. exploit BOUND; eauto. i. des. eapply x. }
      intros [f FSPEC]. exists f.
      assert (IDENT: map_ident_in_memory f mem).
      { ii. specialize (FSPEC loc). des. eauto. }
      splits; eauto.
      - ii. specialize (FSPEC loc). des.
        red in MAPLT. eapply MAPLT; eauto.
      - econs.
        + i. eapply Memory.cap_inv in GET; eauto. des; eauto.
          dup GET. destruct (classic (msg = Message.reserve)); auto.
          eapply Memory.future_weak_get1 in GET; eauto; ss. des.
          right. esplits; eauto.
          * specialize (FSPEC loc). des. eapply SAME.
            eapply Memory.max_ts_spec in GET0. des. auto.
          * eapply map_ident_in_memory_closed_message; eauto.
            inv CLOSED. eapply CLOSED0 in GET0. des. eauto.
        + i. specialize (FSPEC loc). des.
          exploit COMPLETE.
          { ss. left. auto. } i. des.
          exploit BOUND; eauto.
          { eapply Time.incr_spec. } i.
          left. esplits.
          * eapply MAPPED.
          * eapply Time.bot_spec.
          * eapply Memory.max_ts_spec in GET. des.
            etrans; eauto. etrans.
            { eapply Time.join_l. }
            { left. eapply x. }
          * eapply map_ident_in_memory_bot; eauto.
          * i. inv CLOSED. eapply memory_cap_covered; eauto.
      - ii. specialize (FSPEC loc). des. eapply COMPLETE; ss; eauto.
    Qed.

    Lemma cap_steps_current_steps
          th0 th1 mem1 sc1
          (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
          (MEMORY: Memory.closed (Thread.memory th0))
          (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
          (CAP: Memory.cap (Thread.memory th0) mem1)
          (SC_MAX: Memory.max_concrete_timemap mem1 sc1)
          (STEPS: rtc (@Thread.tau_step lang)
                      (Thread.mk lang (Thread.state th0) (Thread.local th0) sc1 mem1)
                      th1)
          (CONSISTENT: Local.promise_consistent (Thread.local th1))
      :
        exists lc' sc' mem',
          (<<STEPS: rtc (@Thread.tau_step lang)
                        th0
                        (Thread.mk lang (Thread.state th1) lc' sc' mem')>>) /\
          (<<CONSISTENT: Local.promise_consistent lc'>>)
    .
    Proof.
      eapply pred_steps_thread_steps in STEPS.
      destruct th0, th1. ss.
      hexploit steps_map.
      { eapply ident_map_le. }
      { eapply ident_map_bot. }
      { eapply ident_map_eq. }
      { eapply ident_map_lt. }
      { i. eapply ident_map_mappable_evt. }
      { eapply STEPS. }
      { ss. }
      { ss. }
      { ss. }
      { eapply Local.cap_wf; eauto. }
      { eapply LOCAL. }
      { eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eauto. }
      { eapply Memory.max_concrete_timemap_closed; eauto. }
      { eapply map_ident_in_memory_local; eauto; ss.
        eapply ident_map_lt_iff.
      }
      { econs.
        { i. destruct (classic (msg = Message.reserve)); auto. right.
          exists to, from, msg.
          eapply Memory.cap_inv in GET; eauto. des; ss. esplits; eauto.
          { refl. }
          { eapply ident_map_message. }
          { refl. }
        }
        { i. eapply CAP in GET. left. exists fto, ffrom, fto, ffrom. splits; ss.
          { refl. }
          { refl. }
          { i. econs; eauto. }
        }
      }
      { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
      { eapply ident_map_timemap. }
      { eapply Memory.max_concrete_timemap_spec; eauto.
        eapply Memory.cap_closed_timemap; eauto. }
      { instantiate (1:=fun _ => True). ss. }
      i. des. esplits.
      { eapply rtc_implies; try apply STEP. i. inv H. inv TSTEP. econs; eauto. }
      { inv LOCAL0. eapply promise_consistent_mon; cycle 1; eauto.
        { refl. }
        eapply promise_consistent_map; eauto.
        { eapply ident_map_le; eauto. }
        { eapply ident_map_eq; eauto. }
      }
    Qed.

    Definition future_certify lang (e:Thread.t lang): Prop :=
      forall sc1 mem1
        (FUTURE: Memory.future_weak (Thread.memory e) mem1)
        (FUTURE: TimeMap.le (Thread.sc e) sc1)
        (WF: Local.wf (Thread.local e) mem1)
        (SC: Memory.closed_timemap sc1 mem1)
        (MEM: Memory.closed mem1),
        (<<FAILURE: Thread.steps_failure (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1)>>) \/
        exists e2,
          (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1) e2>>) /\
          (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>).

    Lemma future_certify_exists
          e
          (LOCAL: Local.wf (Thread.local e) (Thread.memory e))
          (MEMORY: Memory.closed (Thread.memory e))
          (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
          (CONSISTENT: @Thread.consistent lang e):
      future_certify e.
    Proof.
      eapply consistent_no_sc_trace_consistent in CONSISTENT; eauto.
      ii. hexploit Memory.cap_exists.
      { eapply MEMORY. } i. des.
      exploit CONSISTENT; eauto. i. des.

      hexploit trace_times_list_exists. i. des.
      hexploit (future_memory_map times CAP FUTURE); eauto. i. des.

      destruct e2.
      hexploit trace_steps_map.
      { eapply mapping_map_lt_iff_map_le; eauto. }
      { eapply map_ident_in_memory_bot; eauto. }
      { eapply mapping_map_lt_iff_map_eq; eauto. }
      { eapply mapping_map_lt_iff_map_lt; eauto. }
      { eapply wf_time_mapped_mappable; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eapply Local.cap_wf; eauto. }
      { eapply WF. }
      { eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.closed_timemap_bot. inv MEM. auto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply map_ident_in_memory_local; eauto. }
      { eauto. }
      { eapply mapping_map_lt_iff_collapsable_unwritable. eauto. }
      { eapply map_ident_concrete_closed_timemap; eauto.
        ii. eapply IDENT; eauto. inv CONCRETE.
        eapply Memory.max_ts_spec in GET. des; eauto.
      }
      { ii. eapply Time.bot_spec. }
      i. des.
      hexploit no_sc_any_sc_traced.
      { eapply STEPS0. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eapply List.Forall_forall. ii.
        eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in NOSC; eauto.
        destruct a, x. ss. inv EVENT; ss.
      }
      i. des.
      eapply List.Forall2_app_inv_l in TRACE0. des. subst.
      eapply Trace.steps_separate in STEPS1. des.
      eapply Trace.silent_steps_tau_steps in STEPS2; cycle 1.
      { eapply List.Forall_forall. i.
        eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in IN; eauto.
        destruct a, x. ss. inv EVENT; ss.
      }
      red in TRACE. des; clarify.
      { right. esplits.
        { eauto. }
        { inv TRACE1. inv STEPS3; ss. inv LOCAL0.
          rewrite PROMISES in PROMISES0.
          eapply bot_promises_map in PROMISES0; eauto.
        }
      }
      { left. repeat red.
        inv TRACE1. inv H3. des.
        inv STEPS3. inv TR. inv STEPS1; ss.
        esplits.
        { eauto. }
        { replace pf with true in STEP; [eauto|].
          inv STEP; inv STEP0; ss. inv EVENT; ss.
        }
        { inv EVENT; ss. }
      }
    Qed.

    Lemma future_consistent
          e sc' mem'
          (LOCAL: Local.wf (Thread.local e) (Thread.memory e))
          (MEMORY: Memory.closed (Thread.memory e))
          (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
          (CONSISTENT: @Thread.consistent lang e)
          (SC_FUTURE: TimeMap.le (Thread.sc e) sc')
          (MEM_FUTURE: Memory.future_weak (Thread.memory e) mem')
          (LOCAL': Local.wf (Thread.local e) mem')
          (MEMORY': Memory.closed mem')
          (SC': Memory.closed_timemap sc' mem'):
      Thread.consistent (Thread.mk lang (Thread.state e) (Thread.local e) sc' mem').
    Proof.
      ii. ss.
      eapply future_certify_exists; try exact CONSISTENT; eauto.
      - etrans; eauto. eapply Memory.cap_future_weak; eauto.
      - eapply Local.cap_wf; eauto.
      - eapply Memory.cap_closed_timemap; eauto.
      - eapply Memory.cap_closed; eauto.
    Qed.
  End FutureCertify.

  Lemma undef_added_step lang pf e th0 th1
        loc to0 to1 from1
        (STEP: @Thread.step lang pf e th0 th1)
        (PROMISED: concrete_promised th0.(Thread.local).(Local.promises) loc to0)
        (TS: Time.lt to0 to1)
        (UNCH: unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) loc to1 from1 Message.undef)
        (CONSISTENT: Local.promise_consistent th0.(Thread.local))
        (LOCALWF: Local.wf th0.(Thread.local) th0.(Thread.memory))
    :
    (<<FAILURE: Thread.steps_failure th0>>) \/
    (<<PROMISED: concrete_promised th1.(Thread.local).(Local.promises) loc to0>>).
  Proof.
    dup STEP. inv STEP.
    { right. red.
      inv STEP1; ss. inv LOCAL. inv PROMISED. inv PROMISE; ss.
      { eapply Memory.add_get1 in GET; eauto. econs; eauto. }
      { eapply Memory.split_get1 in GET; eauto. des. econs; eauto. }
      { eapply Memory.lower_get1 in GET; eauto. des. econs; eauto. inv MSG_LE; ss. }
      { dup GET. eapply Memory.remove_get1 in GET; eauto. des; clarify.
        { eapply Memory.remove_get0 in PROMISES. des. clarify. }
        { econs; eauto. }
      }
    }
    { inv STEP1; ss. inv LOCAL; ss.
      { right. eauto. }
      { inv LOCAL0. eauto. }
      { destruct (Loc.eq_dec loc0 loc).
        { subst. left. repeat red. esplits; [refl|..].
          { econs 2. instantiate (2:=ThreadEvent.racy_write loc to1 val ord).
            econs; eauto. econs. econs; eauto.
            inv PROMISED. inv UNCH. econs; eauto; ss.
            eapply CONSISTENT in GET; eauto. red.
            etrans; [|eauto]. eapply TimeFacts.le_lt_lt; [|eapply GET]; eauto.
            eapply LOCALWF.
          }
          { ss. }
        }
        { inv PROMISED. right. inv LOCAL0. ss. econs.
          { erewrite Memory.write_get_diff_promise; eauto. }
          { eauto. }
        }
      }
      { destruct (Loc.eq_dec loc0 loc).
        { subst. left. repeat red. esplits; [refl|..].
          { econs 2. instantiate (2:=ThreadEvent.racy_update loc to1 valr valw ordr ordw).
            econs; eauto. econs. econs; eauto.
            inv PROMISED. inv UNCH. econs; eauto; ss.
            eapply CONSISTENT in GET; eauto. red.
            etrans; [|eauto]. eapply TimeFacts.le_lt_lt; [|eapply GET]; eauto.
            eapply LOCALWF.
          }
          { ss. }
        }
        { inv PROMISED. right. inv LOCAL1. inv LOCAL2. ss. econs.
          { erewrite Memory.write_get_diff_promise; eauto. }
          { eauto. }
        }
      }
      { inv LOCAL0. eauto. }
      { inv LOCAL0. eauto. }
      { inv LOCAL0. eauto. }
      { destruct (Loc.eq_dec loc0 loc).
        { subst. left. repeat red. esplits; [refl|..].
          { econs 2. instantiate (2:=ThreadEvent.racy_write loc to1 val ord).
            econs; eauto. econs. econs; eauto.
            inv PROMISED. inv UNCH. econs; eauto; ss.
            eapply CONSISTENT in GET; eauto. red.
            etrans; [|eauto]. eapply TimeFacts.le_lt_lt; [|eapply GET]; eauto.
            eapply LOCALWF.
          }
          { ss. }
        }
        { inv PROMISED. right. inv LOCAL0. ss. econs.
          { erewrite Memory.write_na_get_diff_promise; eauto. }
          { eauto. }
        }
      }
      { inv LOCAL0. eauto. }
      { inv LOCAL0. eauto. }
      { left. repeat red. esplits; eauto. }
    }
  Qed.

  Lemma undef_added_steps lang th0 th1
        loc to0 to1 from1
        (STEPS: rtc (@Thread.tau_step lang) th0 th1)
        (PROMISED: concrete_promised th0.(Thread.local).(Local.promises) loc to0)
        (TS: Time.lt to0 to1)
        (UNCH: unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) loc to1 from1 Message.undef)
        (CONSISTENT: Local.promise_consistent th1.(Thread.local))
        (LOCALWF: Local.wf th0.(Thread.local) th0.(Thread.memory))
        (MEMWF: Memory.closed th0.(Thread.memory))
        (SCWF: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
    :
    (<<FAILURE: Thread.steps_failure th0>>) \/
    (<<PROMISED: concrete_promised th1.(Thread.local).(Local.promises) loc to0>>).
  Proof.
    revert PROMISED UNCH CONSISTENT LOCALWF MEMWF SCWF. induction STEPS; i.
    { right. eauto. }
    { inv H. inv TSTEP. hexploit Thread.step_future; eauto. i. des.
      hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto. i.
      hexploit PromiseConsistent.step_promise_consistent; eauto. i.
      hexploit undef_added_step; eauto. i. des; eauto.
      eapply unchangable_increase in UNCH; eauto.
      hexploit IHSTEPS; eauto. i. des.
      { left. red in FAILURE. des. repeat red. esplits; [|eauto|eauto].
        econs 2; [|eauto]. econs; eauto. econs; eauto.
      }
      { eauto. }
    }
  Qed.

  Lemma undef_added_failure lang st lc sc0 mem0 sc1 mem1
        (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 mem0))
        (MEMLE: Memory.future_weak mem0 mem1)
        (SCLE: TimeMap.le sc0 sc1)
        (LOCAL: Local.wf lc mem0)
        (MEM0: Memory.closed mem0)
        (SC0: Memory.closed_timemap sc0 mem0)
        (MEM1: Memory.closed mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (LOCAL1: Local.wf lc mem1)
        loc from0 to0 msg from1 to1
        (GET0: Memory.get loc to0 lc.(Local.promises) = Some (from0, msg))
        (MSG: msg <> Message.reserve)

        (GET1: Memory.get loc to1 mem1 = Some (from1, Message.undef))
        (TS: Time.lt to0 to1)
        (NONE: Memory.get loc to1 mem0 = None)
    :
      Thread.steps_failure (Thread.mk _ st lc sc1 mem1).
  Proof.
    eapply future_certify_exists in CONSISTENT; eauto.
    exploit CONSISTENT; eauto. i. des; ss; auto.
    eapply undef_added_steps in STEPS; eauto; ss.
    { des; eauto. exfalso. rewrite PROMISES in PROMISED.
      inv PROMISED. erewrite Memory.bot_get in GET. ss.
    }
    { econs; eauto. }
    { econs; eauto.
      destruct (Memory.get loc to1 lc.(Local.promises)) as [[]|] eqn:EQ; auto.
      eapply LOCAL in EQ. clarify.
    }
    { eapply Local.bot_promise_consistent; eauto. }
  Qed.
End FutureCertify.
