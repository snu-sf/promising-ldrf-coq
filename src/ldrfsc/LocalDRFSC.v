Require Import Omega.
Require Import Bool.
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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.
Require Import Single.

Require Import OrdStep.
Require Import RARace.
Require Import SCStep.
Require Import Stable.

Require Import MemoryProps.
Require Import Mapping.
Require Import SplitCertification.

Require Import LocalDRFRA.

Section SIM.

  Variable L: Loc.t -> bool.

  Lemma ra_program_step_sc_program_step_or_race lang
        (th0 th1: Thread.t lang) e
        (STEP: OrdThread.program_step L Ordering.acqrel Ordering.acqrel e th0 th1)
    :
      (<<STEP: SCThread.program_step L e th0 th1>>) \/
      (<<RACE: SCRace.race L th0>>).
  Proof.
    destruct (classic (SCRace.race L th0)) as [RACE|RACE]; auto.
    left. inv STEP. econs; eauto. inv LOCAL; ss.
    - econs; eauto.
    - inv LOCAL0. econs; eauto. econs; eauto.
      i. destruct (Time.le_lt_dec to' ts); auto. exfalso. eapply RACE.
      unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
      inv STEP. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
      eapply RLX. des_ifs. etrans; [|eapply Ordering.join_r]. auto.
    - inv LOCAL0. econs; eauto. econs; eauto.
      i. destruct (Time.le_lt_dec to to'); auto. exfalso. eapply RACE.
      unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
      inv STEP. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
    - inv LOCAL1. inv LOCAL2. econs; eauto.
      + econs; eauto.
        i. destruct (Time.le_lt_dec to' tsr); auto. exfalso. eapply RACE.
        unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
        inv STEP. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
        eapply RLX. des_ifs. etrans; [|eapply Ordering.join_r]. auto.
      + econs; eauto.
        i. destruct (Time.le_lt_dec tsw to'); auto. exfalso. eapply RACE.
        unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
        inv STEP0. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
        eapply TimeFacts.le_lt_lt; eauto. inv STEP. ss.
        etrans; [|eapply Time.join_l]. eapply Time.join_l.
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
    - inv LOCAL0.
      { des_ifs.
        { exfalso. inv STEP. destruct ord; ss. }
        econs. econs 1; eauto.
      }
      { econs. econs 2; eauto.
        replace Ordering.acqrel with (Ordering.join ord Ordering.acqrel); eauto.
        destruct ord; ss.
      }
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma ra_thread_step_sc_thread_step_or_race lang
        (th0 th1: Thread.t lang) pf e
        (STEP: OrdThread.step L Ordering.acqrel Ordering.acqrel pf e th0 th1)
    :
      (<<STEP: SCThread.step L pf e th0 th1>>) \/
      (<<RACE: SCRace.race L th0>>).
  Proof.
    inv STEP.
    - left. econs; eauto.
    - eapply ra_program_step_sc_program_step_or_race in STEP0.
      des; auto. left. econs 2; eauto.
  Qed.

  Lemma ra_thread_opt_step_sc_thread_opt_step_or_race lang
        (th0 th1: Thread.t lang) e
        (STEP: OrdThread.opt_step L Ordering.acqrel Ordering.acqrel e th0 th1)
    :
      (<<STEP: SCThread.opt_step L e th0 th1>>) \/
      (<<RACE: SCRace.race L th0>>).
  Proof.
    inv STEP.
    - left. econs; eauto.
    - eapply ra_thread_step_sc_thread_step_or_race in STEP0.
      des; auto. left. econs 2; eauto.
  Qed.

  Lemma ra_thread_tau_steps_sc_thread_tau_steps_or_race lang
        (th0 th1: Thread.t lang)
        (STEPS: rtc (OrdThread.tau_step L Ordering.acqrel Ordering.acqrel) th0 th1)
    :
      (<<STEPS: rtc (SCThread.tau_step L) th0 th1>>) \/
      (exists th',
          (<<STEPS0: rtc (SCThread.tau_step L) th0 th'>>) /\
          (<<STEPS1: rtc (OrdThread.tau_step L Ordering.acqrel Ordering.acqrel) th' th1>>) /\
          (<<RACE: SCRace.race L th'>>)).
  Proof.
    induction STEPS; eauto. dup H. inv H. inv TSTEP.
    eapply ra_thread_step_sc_thread_step_or_race in STEP; eauto. des.
    - left. econs; eauto. econs; eauto. econs; eauto.
    - right. exists th'. esplits; eauto. econs; eauto. econs; eauto. econs; eauto.
    - right. exists x. esplits; eauto.
    - right. exists x. esplits; eauto.
  Qed.

  Lemma ra_thread_all_steps_sc_thread_all_steps_or_race lang
        (th0 th1: Thread.t lang)
        (STEPS: rtc (OrdThread.all_step L Ordering.acqrel Ordering.acqrel) th0 th1)
    :
      (<<STEPS: rtc (SCThread.all_step L) th0 th1>>) \/
      (exists th',
          (<<STEPS0: rtc (SCThread.all_step L) th0 th'>>) /\
          (<<STEPS1: rtc (OrdThread.all_step L Ordering.acqrel Ordering.acqrel) th' th1>>) /\
          (<<RACE: SCRace.race L th'>>)).
  Proof.
    induction STEPS; eauto. dup H. inv H. inv USTEP.
    eapply ra_thread_step_sc_thread_step_or_race in STEP; eauto. des.
    - left. econs; eauto. econs; eauto. econs; eauto.
    - right. exists th'. esplits; eauto. econs; eauto. econs; eauto. econs; eauto.
    - right. exists x. esplits; eauto.
    - right. exists x. esplits; eauto.
  Qed.

  Lemma cap_step_current_step
        pf e lang (e0 e1: Thread.t lang) fe0
        (THREAD: thread_map ident_map e0 fe0)
        (STEP: SCThread.step L pf e e0 e1)
        (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
        (FLOCAL: Local.wf (Thread.local fe0) (Thread.memory fe0))
        (MEMORY: Memory.closed (Thread.memory e0))
        (FMEMORY: Memory.closed (Thread.memory fe0))
        (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
        (FSC: Memory.closed_timemap (Thread.sc fe0) (Thread.memory fe0))
    :
      (exists fe fe1,
          (<<THREAD: thread_map ident_map e1 fe1>>) /\
          (<<STEP: SCThread.step L pf fe fe0 fe1>>) /\
          (<<EVENT: tevent_map ident_map fe e>>)) \/
      (<<RACE: SCRace.race L fe0>>)
  .
  Proof.
    destruct (classic (SCRace.race L fe0)) as [RACE|RACE]; auto. left.
    assert (MAPLT: mapping_map_lt_iff ident_map).
    { eapply ident_map_lt_iff. }
    assert (MAPLE: mapping_map_le ident_map).
    { eapply ident_map_le. }
    assert (MAPEQ: mapping_map_eq ident_map).
    { eapply ident_map_eq. }

    inv THREAD. ss. inv STEP.
    { inv STEP0. inv LOCAL1.
      exploit promise_map; try apply PROMISE; eauto; ss.
      { eapply FLOCAL. }
      { eapply LOCAL0. }
      { eapply mapping_map_lt_iff_non_collapsable; eauto. }
      { eapply ident_map_message. }
      i. des. inv LOCAL0.
      eexists _, (Thread.mk _ st (Local.mk (Local.tview flc) fprom1) fsc fmem1).
      esplits; eauto.
      { econs; eauto.
        { econs; eauto. }
        { eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
      }
      { econs 1. econs.
        { econs; eauto. eapply closed_message_map; eauto.
          eapply ident_map_message. }
        { inv KIND; ss. }
        { ii. clarify. exploit PF; eauto. }
      }
      { econs; eauto; ss. eapply ident_map_message. }
    }
    { inv STEP0. inv LOCAL1.
      { esplits; eauto.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs 1; eauto. }
        { econs; eauto. }
      }
      { inv LOCAL2. exploit read_step_map; eauto.
        { eapply ident_map_bot. }
        { eapply FLOCAL. } i. des.
        exists (ThreadEvent.read loc fto val freleased ord). esplits.
        { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
        { econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
          ii. destruct (Time.le_lt_dec to' fto); auto. exfalso. eapply RACE.
          unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
          inv READ. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
          eapply RLX; eauto. destruct (L loc); ss.
          etrans; [|eapply Ordering.join_r]. auto.
        }
        { econs; eauto. }
      }
      { inv LOCAL2. hexploit write_step_map; try eassumption; eauto.
        { eapply ident_map_bot. }
        { eapply FLOCAL. }
        { eapply FLOCAL. }
        { econs 2. }
        { refl. }
        { refl. }
        { eapply mapping_map_lt_iff_non_collapsable; eauto. }
        i. des.
        exists (ThreadEvent.write loc from to val freleasedw ord). esplits.
        { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
        { econs 2; eauto. econs; eauto. econs 3; eauto. econs; eauto.
          ii. destruct (Time.le_lt_dec to to'); auto. exfalso. eapply RACE.
          unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
          inv WRITE. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
        }
        { econs; eauto; ss. }
      }
      { inv LOCAL2. inv LOCAL3. exploit read_step_map; eauto.
        { eapply ident_map_bot. }
        { eapply FLOCAL. } i. des.
        hexploit Local.read_step_future; try apply STEP; eauto. i. des.
        hexploit Local.read_step_future; try apply READ; eauto. i. des.
        hexploit write_step_map; try eapply STEP0; try eassumption; eauto.
        { eapply ident_map_bot. }
        { eapply WF0. }
        { eapply WF0. }
        { eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
        { refl. }
        { eapply mapping_map_lt_iff_non_collapsable; eauto. }
        i. des.
        exists (ThreadEvent.update loc fto tsw valr valw freleased freleasedw ordr ordw). esplits.
        { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
        { econs 2; eauto. econs; eauto. econs 4; eauto.
          { econs; eauto.
            ii. destruct (Time.le_lt_dec to' fto); auto. exfalso. eapply RACE.
            unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
            inv READ. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
            eapply RLX; eauto. destruct (L loc); ss. etrans; [|eapply Ordering.join_r]. auto.
          }
          { econs; eauto.
            ii. destruct (Time.le_lt_dec tsw to'); auto. exfalso. eapply RACE.
            unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
            inv WRITE. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
            eapply TimeFacts.le_lt_lt; eauto. eapply TVIEW_FUTURE0.
          }
        }
        { econs; eauto; ss. }
      }
      { inv LOCAL2. exploit fence_step_map; try apply FENCE; eauto.
        { eapply ident_map_bot. }
        { eapply FLOCAL. } i. des.
        exists (ThreadEvent.fence ordr ordw). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs 5; eauto. }
        { econs; eauto; ss. }
      }
      { inv LOCAL2. exploit fence_step_map; eauto.
        { eapply ident_map_bot. }
        { eapply FLOCAL. } i. des.
        exists (ThreadEvent.syscall e0). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs 6; eauto. }
        { econs; eauto; ss. }
      }
      { inv LOCAL2. exploit failure_step_map; eauto. i.
        exists (ThreadEvent.failure). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs 7; eauto. }
        { econs; eauto; ss. }
      }
      { inv LOCAL2.
        { hexploit write_na_step_map; try eassumption; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. }
          { eapply FLOCAL. }
          { refl. }
          { refl. }
          { eapply mapping_map_lt_iff_non_collapsable; eauto. }
          { instantiate (1:=List.map (fun '(from, to, msg) => (from, to)) msgs).
            clear. induction msgs; ss. econs; eauto. destruct a as [[from to] msg]. ss.
          }
          { eapply List.Forall_forall.
            i. eapply mapping_map_lt_iff_non_collapsable; eauto.
          }
          i. des.
          eexists (ThreadEvent.write_na _ fmsgs _ _ _ _). esplits.
          { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { econs 2; eauto. econs; eauto. econs; eauto. econs 1; eauto. }
          { econs; eauto; ss. }
        }
        { hexploit write_step_map; try eassumption; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. }
          { eapply FLOCAL. }
          { econs 2. }
          { refl. }
          { refl. }
          { eapply mapping_map_lt_iff_non_collapsable; eauto. }
          i. des.
          eexists (ThreadEvent.write_na _ [] _ _ _ _). esplits.
          { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { econs 2; eauto. econs; eauto. econs; eauto. econs 2; eauto. }
          { econs; eauto; ss. }
        }
      }
      { inv LOCAL2. hexploit racy_read_step_map; try eassumption; eauto.
        { eapply ident_map_lt. }
        i. des. eexists (ThreadEvent.racy_read _ fto _ _). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. }
        { econs; eauto; ss. }
      }
      { inv LOCAL2. hexploit racy_write_step_map; try eassumption; eauto.
        { eapply ident_map_lt. }
        i. des. eexists (ThreadEvent.racy_write _ fto _ _). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. }
        { econs; eauto; ss. }
      }
      { hexploit racy_update_step_map; try eassumption; eauto.
        { eapply ident_map_bot. }
        { eapply ident_map_lt. }
        i. des. eexists (ThreadEvent.racy_update _ fto _ _ _ _). esplits.
        { econs; eauto. }
        { econs 2; eauto. econs; eauto. econs; eauto. }
        { econs; eauto; ss. }
      }
    }
  Qed.

  Lemma sc_race_map f lang (th0 fth0: Thread.t lang)
        (RACE: SCRace.race L th0)
        (THREAD: thread_map f th0 fth0)
        (MAPLT: mapping_map_lt_iff f)
    :
      SCRace.race L fth0.
  Proof.
    unfold SCRace.race, SCLocal.non_maximal in *. des. inv THREAD. ss.
    eapply MEM in GET. des; ss.
    esplits; eauto.
    { inv MSG; inv MSGLE; ss. }
    inv LOCAL. inv TVIEWLE. inv CUR. specialize (RLX loc).
    eapply TimeFacts.le_lt_lt; eauto.
    eapply (@MAPLT loc (View.rlx (TView.cur (Local.tview lc)) loc) to (View.rlx (TView.cur ftv') loc) fto); eauto.
    eapply TVIEW.
  Qed.

  Lemma cap_tau_steps_current_tau_steps
        lang (e0 e1: Thread.t lang) fe0
        (THREAD: thread_map ident_map e0 fe0)
        (STEPS: rtc (SCThread.tau_step L) e0 e1)
        (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
        (FLOCAL: Local.wf (Thread.local fe0) (Thread.memory fe0))
        (MEMORY: Memory.closed (Thread.memory e0))
        (FMEMORY: Memory.closed (Thread.memory fe0))
        (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
        (FSC: Memory.closed_timemap (Thread.sc fe0) (Thread.memory fe0))
    :
      (exists fe1,
          (<<THREAD: thread_map ident_map e1 fe1>>) /\
          (<<STEP: rtc (SCThread.tau_step L) fe0 fe1>>)) \/
      (exists e' fe',
          (<<FSTEPS: rtc (SCThread.tau_step L) fe0 fe'>>) /\
          (<<STEPS0: rtc (SCThread.tau_step L) e0 e'>>) /\
          (<<STEPS1: rtc (SCThread.tau_step L) e' e1>>) /\
          (<<THREAD: thread_map ident_map e' fe'>>) /\
          (<<RACE: SCRace.race L fe'>>)).
  Proof.
    ginduction STEPS; i.
    { left. esplits; eauto. }
    dup H. inv H. inv TSTEP. exploit cap_step_current_step; eauto.
    i. des.
    - exploit SCThread.step_future; try apply STEP; eauto. i. des.
      exploit SCThread.step_future; try apply STEP0; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      + left. esplits; eauto. econs; eauto. econs.
        * econs; eauto.
        * erewrite <- EVENT. inv EVENT0; eauto.
      + right. exists e', fe'. esplits; eauto. econs; eauto. econs.
        * econs; eauto.
        * erewrite <- EVENT. inv EVENT0; eauto.
    - right. esplits; eauto.
  Qed.

  Lemma cap_race_current_race
        lang (e0 e1: Thread.t lang) cap
        (CAP: Memory.cap (Thread.memory e0) cap)
        (STEPS: rtc (SCThread.tau_step L) (Thread.mk _ (Thread.state e0) (Thread.local e0) (Thread.sc e0) cap) e1)
        (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
        (MEMORY: Memory.closed (Thread.memory e0))
        (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
        (CONSISTENT: Local.promise_consistent (Thread.local e1))
        (RACE: SCRace.race L e1)
    :
      exists e2,
        (<<STEPS: rtc (SCThread.tau_step L) e0 e2>>) /\
        (<<CONSISTENT: Local.promise_consistent (Thread.local e2)>>) /\
        (<<RACE: SCRace.race L e2>>).
  Proof.
    exploit cap_tau_steps_current_tau_steps.
    { econs.
      { eapply ident_map_local. }
      { instantiate (1:=(Thread.memory e0)). instantiate (1:=cap). econs.
        - i. eapply Memory.cap_inv in GET; eauto. des; clarify; auto.
          right. exists to, from, msg, msg.
          esplits; eauto; try refl. eapply ident_map_message.
        - i. left.
          exists fto, ffrom, fto, ffrom. esplits; eauto; try refl.
          i. econs; eauto. eapply Memory.cap_le; eauto. refl.
      }
      { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
      { eapply ident_map_timemap. }
      { refl. }
    }
    { eauto. }
    { eapply Local.cap_wf; eauto. }
    { eauto. }
    { eapply Memory.cap_closed; eauto. }
    { eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eauto. }
    i. des.
    - exists fe1. esplits.
      + destruct e0. ss.
      + destruct e1, fe1. destruct local, local0. ss. inv THREAD.
        inv LOCAL0. ss.
        eapply promise_consistent_mon.
        { eapply promise_consistent_map; eauto.
          { eapply ident_map_le. }
          { eapply ident_map_eq. }
        }
        { eauto. }
        { refl. }
      + eapply sc_race_map; eauto. eapply ident_map_lt_iff.
    - assert (CONSISTENT0: Local.promise_consistent (Thread.local e')).
      { exploit SCThread.rtc_tau_step_future; try apply STEPS0; eauto.
        { eapply Local.cap_wf; eauto. }
        { eapply Memory.cap_closed_timemap; eauto. }
        { eapply Memory.cap_closed; eauto. }
        i. des. ss. eapply SCThread.rtc_tau_step_promise_consistent; eauto.
      }
      exists fe'. esplits.
      + destruct e0. ss.
      + destruct e', fe'. destruct local, local0. ss. inv THREAD.
        inv LOCAL0. ss.
        eapply promise_consistent_mon.
        { eapply promise_consistent_map; eauto.
          { eapply ident_map_le. }
          { eapply ident_map_eq. }
        }
        { eauto. }
        { refl. }
      + auto.
  Qed.

  Lemma ord_thread_consistent_promise_consistent lang
        (th0: Thread.t lang)
        (CONSISTENT: OrdThread.consistent L Ordering.acqrel Ordering.acqrel th0)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (MEMORY: Memory.closed (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
    :
      Local.promise_consistent (Thread.local th0).
  Proof.
    hexploit (@Memory.cap_exists (Thread.memory th0)); eauto. intros [cap CAP].
    exploit CONSISTENT; eauto. i. des.
    { unfold OrdThread.steps_failure in FAILURE. des.
      eapply OrdThread.rtc_tau_step_promise_consistent in STEPS; eauto.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { inv STEP_FAILURE; inv STEP; ss.
        inv LOCAL0; ss; inv LOCAL1; ss. inv STEP; ss.
      }
    }
    { eapply OrdThread.rtc_tau_step_promise_consistent in STEPS; eauto.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Local.bot_promise_consistent; eauto. }
    }
  Qed.

  Lemma ra_thread_consistent_sc_thread_consistent_or_race lang
        (th0: Thread.t lang)
        (CONSISTENT: OrdThread.consistent L Ordering.acqrel Ordering.acqrel th0)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (MEMORY: Memory.closed (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
    :
      (<<CONSISTENT: SCThread.consistent L th0>>) \/
      (exists th1,
          (<<STEPS: rtc (SCThread.tau_step L) th0 th1>>) /\
          (<<CONSISTENT: Local.promise_consistent (Thread.local th1)>>) /\
          (<<RACE: SCRace.race L th1>>)).
  Proof.
    destruct (classic (exists th1,
                          (<<STEPS: rtc (SCThread.tau_step L) th0 th1>>) /\
                          (<<CONSISTENT: Local.promise_consistent (Thread.local th1)>>) /\
                          (<<RACE: SCRace.race L th1>>))) as [RACE|RACE]; auto.
    left. ii. exploit CONSISTENT; eauto. i. des.
    - unfold OrdThread.steps_failure in *. des.
      left. unfold SCThread.steps_failure.
      eapply ra_thread_tau_steps_sc_thread_tau_steps_or_race in STEPS. des.
      + hexploit ra_thread_step_sc_thread_step_or_race; eauto. i. des.
        { red. esplits; eauto. }
        { exfalso. eapply RACE.
          eapply cap_race_current_race; eauto.
          inv STEP_FAILURE; inv STEP; ss. inv LOCAL0; ss; inv LOCAL1; ss. inv STEP; ss.
        }
      + exfalso. eapply RACE.
        eapply cap_race_current_race; eauto.
        exploit SCThread.rtc_tau_step_future; try apply STEPS0; eauto.
        { eapply Local.cap_wf; eauto. }
        { eapply Memory.cap_closed_timemap; eauto. }
        { eapply Memory.cap_closed; eauto. }
        i. des. ss. eapply OrdThread.rtc_tau_step_promise_consistent; eauto.
        inv STEP_FAILURE; inv STEP; ss. inv LOCAL0; ss; inv LOCAL1; ss. inv STEP; ss.
    - right. eapply ra_thread_tau_steps_sc_thread_tau_steps_or_race in STEPS. des.
      + esplits; eauto.
      + exfalso. eapply RACE.
        eapply cap_race_current_race; eauto.
        exploit SCThread.rtc_tau_step_future; try apply STEPS0; eauto.
        { eapply Local.cap_wf; eauto. }
        { eapply Memory.cap_closed_timemap; eauto. }
        { eapply Memory.cap_closed; eauto. }
        i. des. ss. eapply OrdThread.rtc_tau_step_promise_consistent; eauto.
        eapply Local.bot_promise_consistent; eauto.
  Qed.

  Lemma ra_configuration_step_sc_configuration_step_or_race e tid c0 c1
        (STEP: OrdConfiguration.step L Ordering.acqrel Ordering.acqrel e tid c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<STEP: SCConfiguration.step L e tid c0 c1>>) \/
      (<<RACE: SCRace.race_steps L c0 tid>>).
  Proof.
    destruct (classic (SCRace.race_steps L c0 tid)) as [RACE|RACE]; auto. left.
    inv STEP.
    exploit Thread.rtc_cancel_step_future; eauto; try eapply WF; eauto. i. des. ss.
    assert ((<<LOCAL: Local.wf lc4 memory4>>) /\
            (<<MEMORY: Memory.closed memory4>>) /\
            (<<CLOSED: Memory.closed_timemap sc4 memory4>>)).
    { inv STEP0.
      - exploit Thread.rtc_reserve_step_future; eauto. i. des. ss.
      - exploit OrdThread.step_future; eauto. i. des. ss.
        exploit Thread.rtc_reserve_step_future; eauto. i. des. ss.
    } des.

    assert ((<<CONSISTENT: Local.promise_consistent (Thread.local e2)>>) /\
            (<<CONSISTENT: Local.promise_consistent lc4>>)).
    { destruct (classic (ThreadEvent.get_machine_event e = MachineEvent.failure)).
      - cut (Local.promise_consistent (Thread.local e2) /\ Local.promise_consistent (Thread.local e3)).
        { i. des. eapply PromiseConsistent.rtc_reserve_step_promise_consistent2 in RESERVES; eauto. }
        inv STEP0; ss. inv STEP; inv STEP0; ss. inv LOCAL0; ss; inv LOCAL1; ss. inv STEP; ss.
      - hexploit ord_thread_consistent_promise_consistent; eauto. i. ss. splits; eauto.
        eapply PromiseConsistent.rtc_reserve_step_promise_consistent in RESERVES; eauto.
        inv STEP0; auto. eapply OrdThread.step_promise_consistent in STEP; eauto.
    }

    exploit ra_thread_opt_step_sc_thread_opt_step_or_race; try apply STEP0.
    i. des; cycle 1.
    { exfalso. eapply RACE. unfold SCRace.race_steps. esplits.
      + eauto.
      + eapply rtc_implies; try apply CANCELS. i.
        inv H. inv STEP; [|inv STEP1; inv LOCAL0]. econs; eauto.
        * econs; eauto. econs 1; eauto. ii. clarify.
        (* * ss. *)
      + eauto.
      + eauto.
    }

    econs; eauto. i.
    hexploit ra_thread_consistent_sc_thread_consistent_or_race; eauto; ss. i. des; ss.
    destruct (ThreadEvent.get_machine_event e) eqn:EVENT.
    { exfalso. eapply RACE. unfold SCRace.race_steps. esplits.
      + eauto.
      + etrans.
        { eapply rtc_implies; try apply CANCELS. i.
          inv H0. inv STEP1; [|inv STEP2; inv LOCAL0]. econs.
          * econs; eauto. econs 1; eauto. ii. clarify.
          (* * ss. *)
        } etrans.
        { instantiate (1:=e3). inv STEP; eauto. econs; eauto.
          econs; eauto. econs; eauto. } etrans.
        { eapply rtc_implies; try apply RESERVES. i.
          inv H0. inv STEP1; [|inv STEP2; inv LOCAL0]. econs.
          * econs; eauto. econs 1; eauto. ii. clarify.
          (* * ss. *)
        }
        { eapply rtc_implies; try apply STEPS. i. inv H0. econs; eauto. }
      + eauto.
      + eauto.
    }
    { destruct e; clarify. inv STEP. inv STEP1; inv STEP.
      inv LOCAL0. inv LOCAL1. hexploit PROMISES; eauto. ii. right. ss.
      hexploit reserve_steps_le_cancel_steps.
      { eapply RESERVES. }
      { eapply Memory.cap_le; eauto. refl. }
      i. des. esplits.
      { eapply rtc_implies; try apply STEPS0; eauto. i.
        inv H1. inv STEP; [|inv STEP1; inv LOCAL1]. econs.
        * econs; eauto. econs 1; eauto. ii. clarify.
        * ss.
      }
      erewrite LOCAL0. eauto.
    }
    { destruct e; ss. }
  Qed.

  Lemma ra_configuration_steps_sc_configuration_steps_or_race c0 c1
        (STEPS: rtc (OrdConfiguration.all_step L Ordering.acqrel Ordering.acqrel) c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<STEPS: rtc (SCConfiguration.all_step L) c0 c1>>) \/
      (exists c' tid,
          (<<STEPS: rtc (SCConfiguration.all_step L) c0 c'>>) /\
          (<<RACE: SCRace.race_steps L c' tid>>)).
  Proof.
    ginduction STEPS; eauto. i. inv H.
    eapply ra_configuration_step_sc_configuration_step_or_race in STEP; eauto. des.
    { exploit SCConfiguration.step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      { left. econs; eauto. econs; eauto. }
      { right. esplits; [|eapply RACE]. econs; eauto. econs; eauto. }
    }
    { right. esplits; eauto. }
  Qed.

  Lemma ra_behavior_sc_behavior_or_race c
        (RACEFREE: SCRace.racefree L c)
        (WF: Configuration.wf c)
    :
      behaviors (@OrdConfiguration.machine_step L Ordering.acqrel Ordering.acqrel) c <2=
      behaviors (@SCConfiguration.machine_step L) c.
  Proof.
    i. ginduction PR; eauto; i.
    - econs 1; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 2; eauto.
        * rewrite <- H0. econs; eauto.
        * eapply IHPR; eauto.
          { eapply SCRace.step_racefree; eauto. }
          { eapply SCConfiguration.step_future; eauto. }
      + exfalso. eapply RACEFREE; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 3; eauto.
        * rewrite <- H0. econs; eauto.
      + exfalso. eapply RACEFREE; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 4; eauto.
        * rewrite <- H0. econs; eauto.
        * eapply IHPR; eauto.
          { eapply SCRace.step_racefree; eauto. }
          { eapply SCConfiguration.step_future; eauto. }
      + exfalso. eapply RACEFREE; eauto.
    - econs 5.
  Qed.

  Lemma sc_racefree_ra_racefree c
        (RACEFREE: SCRace.racefree L c)
        (WF: Configuration.wf c)
    :
      RARace.racefree L c.
  Proof.
    ii. unfold RARace.race in *. des. guardH ORDERING.
    exploit ra_configuration_steps_sc_configuration_steps_or_race.
    { etrans.
      { eapply STEPS1. } econs 2.
      { econs; eauto. }
      { eapply STEPS2. }
    }
    { eauto. }
    i. des.
    { exploit ra_thread_all_steps_sc_thread_all_steps_or_race; eauto. i. des.
      { eapply RACEFREE; eauto. econs. esplits; eauto.
        unfold ThreadEvent.is_reading in *. des_ifs.
        - inv READ_STEP; inv STEP. econs; eauto. esplits; eauto; ss.
          inv LOCAL. inv LOCAL0. inv STEP.
          unfold SCLocal.non_maximal. esplits; eauto; ss.
        - inv READ_STEP; inv STEP. econs; eauto. esplits; eauto; ss.
          inv LOCAL. inv LOCAL1. inv LOCAL2. inv STEP.
          unfold SCLocal.non_maximal. esplits; eauto; ss.
      }
      { eapply RACEFREE; eauto. econs. esplits; eauto.
        exploit SCConfiguration.all_steps_future; eauto. i. des.
        exploit SCThread.rtc_all_step_future; eauto; try eapply WF2; eauto.
        i. des. ss.
        eapply OrdThread.rtc_all_step_promise_consistent in STEPS3; eauto.
      }
    }
    { eapply RACEFREE; eauto. }
  Qed.

End SIM.


(* LDRF-SC theorem *)
Theorem local_drf_sc L
        s
        (RACEFREE: SCRace.racefree_syn L s):
  behaviors SConfiguration.machine_step (Configuration.init s) <2=
  behaviors (@SCConfiguration.machine_step L) (Configuration.init s).
Proof.
  i. eapply local_drf_ra in PR; eauto.
  - eapply ra_behavior_sc_behavior_or_race; eauto.
    eapply Configuration.init_wf; eauto.
  - eapply sc_racefree_ra_racefree; eauto.
    eapply Configuration.init_wf; eauto.
Qed.
