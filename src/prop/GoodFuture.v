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
Require Import Pred.

Require Import MemoryMerge.
Require Import PromiseConsistent.
Require Import PFConsistent.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import Mapping.

Set Implicit Arguments.

Section GOODFUTURE.

  Record good_future (mem0 mem1: Memory.t) (tm: TimeMap.t): Prop :=
    {
      good_future_tm_wf:
        forall loc, Time.lt (Memory.max_ts loc mem0) (tm loc);
      good_future_future: Memory.future_weak mem0 mem1;
      good_future_cover:
        forall loc ts (COVERED: covered loc ts mem1),
          (<<COVERED: covered loc ts mem0>>) \/
          (<<TS: Time.lt (tm loc) ts>>);
    }.

  Lemma good_future_refl
        mem tm
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
    :
      good_future mem mem tm.
  Proof.
    econs; ss.
    { refl. }
    { i. left. auto. }
  Qed.

  Lemma good_future_trans
        mem0 mem1 mem2 tm0 tm1
        (FUTURE01: good_future mem0 mem1 tm0)
        (FUTURE12: good_future mem1 mem2 tm1)
        (TM: TimeMap.le tm0 tm1)
    :
      good_future mem0 mem2 tm0.
  Proof.
    econs; ss.
    { eapply FUTURE01.(good_future_tm_wf); eauto. }
    { etrans.
      { eapply FUTURE01.(good_future_future); eauto. }
      { eapply FUTURE12.(good_future_future); eauto. }
    }
    { i. exploit FUTURE12.(good_future_cover); eauto. i. des.
      { eapply FUTURE01.(good_future_cover); eauto. }
      { right. eapply TimeFacts.le_lt_lt; eauto. }
    }
  Qed.

  Record good_future_map (max tm: TimeMap.t)
         (times: Loc.t -> list Time.t)
         (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
    {
      good_future_map_map_lt:
        mapping_map_lt f;
      good_future_map_map_bot:
        mapping_map_bot f;
      good_future_map_ident:
        forall loc ts (TS: Time.le ts (max loc)),
          f loc ts ts;
      good_future_map_bound:
        forall loc ts fts
               (MAP: f loc ts fts),
          Time.lt fts (tm loc);
      good_future_map_complete:
        forall loc ts (IN: List.In ts (times loc)),
          mappable_time f loc ts;
    }.

  Lemma good_future_map_exists max tm times
        (TM: forall loc, Time.lt (max loc) (tm loc))
    :
      exists f,
        (<<MAP: good_future_map max tm times f>>).
  Proof.
    hexploit (@choice
                Loc.t (Time.t -> Time.t -> Prop)
                (fun loc f =>
                   (<<MAPLT: mapping_map_lt_loc f>>) /\
                   (<<IDENT: forall ts (TS: Time.le ts (max loc)),
                       f ts ts>>) /\
                   (<<MAX: forall ts fts
                                  (MAP: f ts fts),
                       Time.lt fts (tm loc)>>) /\
                   (<<COMPLETE: forall ts (IN: List.In ts (times loc)),
                       exists fts, (<<MAP: f ts fts>>)>>))).
    { intros loc.
      hexploit (@shift_map_exists
                  (max loc) (max loc) (tm loc)
                  (times loc)); ss.
      { refl. } intros [f SPEC]. exists f. des. splits; auto.
      { i. destruct (Time.le_lt_dec ts (max loc)).
        { exploit mapping_map_lt_loc_map_eq.
          { eapply MAPLT. }
          { eapply MAP. }
          { eapply SAME; eauto. }
          i. subst. eapply TimeFacts.le_lt_lt; eauto.
        }
        { eapply BOUND in MAP; auto. des. auto. }
      }
    }
    intros [f SPEC]. exists f. econs.
    { eapply mapping_map_lt_locwise.
      i. specialize (SPEC loc). des. auto. }
    { ii. specialize (SPEC loc). des.
      eapply IDENT. eapply Time.bot_spec. }
    { i. specialize (SPEC loc). des. auto. }
    { i. specialize (SPEC loc). des. eauto. }
    { i. specialize (SPEC loc). des.
      exploit COMPLETE; eauto. }
  Qed.

  Lemma good_future_memory_map mem0 mem1 tm times f
        (FUTURE: good_future mem0 mem1 tm)
        (MEM: Memory.closed mem0)
        (MAP: good_future_map (Memory.max_timemap mem0) tm times f)
    :
      memory_map f mem0 mem1.
  Proof.
    econs.
    { i. destruct msg as [val released|]; auto. right.
      exploit Memory.future_weak_get1.
      { eapply FUTURE. }
      { eapply GET. }
      i. des.
      exists to, from', (Message.concrete val released), msg'. splits; auto.
      { eapply good_future_map_ident; eauto.
        eapply Memory.max_ts_spec in GET. des. eauto. }
      { eapply map_ident_in_memory_closed_message.
        { ii. eapply MAP.(good_future_map_ident). eapply TS. }
        { eapply MEM in GET. des. auto. }
      }
    }
    { i. destruct (Time.le_lt_dec fto (Memory.max_ts loc mem0)).
      { left. exists fto, ffrom, fto, ffrom. splits; auto.
        { eapply MAP.(good_future_map_ident); eauto. }
        { refl. }
        { refl. }
        { eapply MAP.(good_future_map_ident); eauto.
          eapply memory_get_ts_le in GET. etrans; eauto.
        }
        { i. exploit FUTURE.(good_future_cover).
          { econs; eauto. }
          i. des; auto.
          exfalso. inv ITV. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS. } etrans.
          { eapply TO. } etrans.
          { eapply l. }
          { left. eapply FUTURE.(good_future_tm_wf). }
        }
      }
      { right. destruct (Time.le_lt_dec (tm loc) ffrom).
        { ii. eapply MAP.(good_future_map_bound) in MAP0.
          eapply TimeFacts.lt_le_lt; eauto. }
        { exfalso. exploit FUTURE.(good_future_cover).
          { econs; try apply GET.
            instantiate (1:=Time.meet (tm loc) fto). econs; ss.
            { unfold Time.meet. des_ifs.
              apply memory_get_ts_strong in GET. des; auto.
              subst. inv l. }
            { eapply Time.meet_r. }
          }
          { i. des.
            { inv COVERED. inv ITV; ss.
              apply Memory.max_ts_spec in GET0. des.
              eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
              { eapply TO. } eapply TimeFacts.le_lt_lt.
              { eapply MAX. }
              unfold Time.meet. des_ifs.
              eapply FUTURE.(good_future_tm_wf).
            }
            { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TS. }
              { eapply Time.meet_l. }
            }
          }
        }
      }
    }
  Qed.

  Lemma promise_write_not_in_covered prom0 prom1 mem0 mem1 MSGS
        loc from to msg kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (NOTIN: kind = Memory.op_kind_add ->
                forall ts (ITV: Interval.mem (from, to) ts), ~ MSGS loc ts)
        l t
        (COVERED: covered l t mem1)
    :
      covered l t mem0 \/ ~ MSGS l t.
  Proof.
    inv PROMISE.
    { erewrite add_covered in COVERED; eauto. des; auto.
      subst. right. eapply NOTIN; eauto. }
    { erewrite split_covered in COVERED; eauto. }
    { erewrite lower_covered in COVERED; eauto. }
    { erewrite remove_covered in COVERED; eauto. des; auto. }
  Qed.

  Lemma step_write_not_in_covered P MSGS lang (th0 th1: Thread.t lang) e
        (STEP: pred_step P e th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in MSGS)
        loc ts
        (COVERED: covered loc ts th1.(Thread.memory))
    :
      covered loc ts th0.(Thread.memory) \/ ~ MSGS loc ts.
  Proof.
    inv STEP. eapply NOTIN in SAT. inv STEP0. inv STEP.
    { inv STEP0; ss. inv LOCAL0. eapply promise_write_not_in_covered; eauto.
      i. subst. ss. auto. }
    { inv STEP0; ss. inv LOCAL0; auto.
      - inv LOCAL1. inv WRITE. ss. eapply promise_write_not_in_covered; eauto.
      - inv LOCAL2. inv WRITE. ss. eapply promise_write_not_in_covered; eauto.
    }
  Qed.

  Lemma steps_write_not_in_covered P MSGS lang (th0 th1: Thread.t lang)
        (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in MSGS)
        loc ts
        (COVERED: covered loc ts th1.(Thread.memory))
    :
      covered loc ts th0.(Thread.memory) \/ ~ MSGS loc ts.
  Proof.
    ginduction STEPS; auto. i.
    inv H. dup TSTEP. inv TSTEP. inv STEP.
    exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des; auto.
    exploit step_write_not_in_covered; eauto.
  Qed.

  Lemma step_write_not_in_good_future P lang (th0 th1: Thread.t lang) tm e
        (TM: forall loc, Time.lt (Memory.max_ts loc th0.(Thread.memory)) (tm loc))
        (STEPS: pred_step P e th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in (fun loc ts =>
                                      (<<TS: Time.le ts (tm loc)>>) /\
                                      (<<PROM: ~ covered loc ts th0.(Thread.memory)>>)))
    :
      good_future th0.(Thread.memory) th1.(Thread.memory) tm.
  Proof.
    econs; auto.
    { eapply Memory.future_future_weak.
      inv STEPS. inv STEP.
      exploit Thread.step_future; eauto. i. des. auto. }
    { i. eapply step_write_not_in_covered in COVERED; eauto. des; auto.
      apply not_and_or in COVERED. des.
      { right. destruct (Time.le_lt_dec ts (tm loc)); ss. }
      { left. apply NNPP; eauto. }
    }
  Qed.

  Lemma steps_write_not_in_good_future P lang (th0 th1: Thread.t lang) tm
        (TM: forall loc, Time.lt (Memory.max_ts loc th0.(Thread.memory)) (tm loc))
        (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in (fun loc ts =>
                                      (<<TS: Time.le ts (tm loc)>>) /\
                                      (<<PROM: ~ covered loc ts th0.(Thread.memory)>>)))
    :
      good_future th0.(Thread.memory) th1.(Thread.memory) tm.
  Proof.
    econs; auto.
    { eapply Memory.future_future_weak.
      eapply thread_steps_pred_steps in STEPS.
      exploit Thread.rtc_tau_step_future; eauto. i. des. auto. }
    { i. eapply steps_write_not_in_covered in COVERED; eauto. des; auto.
      apply not_and_or in COVERED. des.
      { right. destruct (Time.le_lt_dec ts (tm loc)); ss. }
      { left. apply NNPP; eauto. }
    }
  Qed.

End GOODFUTURE.