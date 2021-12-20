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
Require Import Trace.

Require Import MemoryProps.
Require Import Mapping.

Set Implicit Arguments.

Section GOODFUTURE.

  Record good_future (tm: TimeMap.t) (mem0 mem1: Memory.t): Prop :=
    {
      good_future_future: Memory.future_weak mem0 mem1;
      good_future_cover:
        forall loc ts (COVERED: covered loc ts mem1),
          (<<COVERED: covered loc ts mem0>>) \/
          (<<TS: Time.lt (tm loc) ts>>);
    }.

  Lemma good_future_mon tm0 tm1
        (TM: TimeMap.le tm0 tm1)
    :
      good_future tm1 <2= good_future tm0.
  Proof.
    ii. econs.
    { eapply PR. }
    { i. eapply PR in COVERED. des; auto.
      right. eapply TimeFacts.le_lt_lt; eauto.
    }
  Qed.

  Global Program Instance good_future_PreOrder tm: PreOrder (good_future tm).
  Next Obligation.
    ii. econs; eauto. refl.
  Qed.
  Next Obligation.
    ii. econs.
    { etrans.
      { eapply H. }
      { eapply H0. }
    }
    { i. eapply H0 in COVERED. des; auto.
      eapply H in COVERED0. auto. }
  Qed.

  Record good_future_map (max tm: TimeMap.t)
         (times: Loc.t -> list Time.t)
         (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
    {
      good_future_map_map_lt:
        mapping_map_lt_iff f;
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
                   (<<MAPLT: mapping_map_lt_iff_loc f>>) /\
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
        { exploit mapping_map_lt_iff_loc_map_eq.
          { eapply MAPLT. }
          { eapply MAP. }
          { eapply SAME; eauto. }
          i. subst. eapply TimeFacts.le_lt_lt; eauto.
        }
        { eapply BOUND in MAP; auto. des. auto. }
      }
    }
    intros [f SPEC]. exists f. econs.
    { eapply mapping_map_lt_iff_locwise.
      i. specialize (SPEC loc). des. auto. }
    { ii. specialize (SPEC loc). des.
      eapply IDENT. eapply Time.bot_spec. }
    { i. specialize (SPEC loc). des. auto. }
    { i. specialize (SPEC loc). des. eauto. }
    { i. specialize (SPEC loc). des.
      exploit COMPLETE; eauto. }
  Qed.

  Lemma good_future_memory_map mem0 mem1 tm times f
        (FUTURE: good_future tm mem0 mem1)
        (MEM: Memory.closed mem0)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem0) (tm loc))
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
        { ii. eapply (good_future_map_ident MAP). eapply TS. }
        { eapply MEM in GET. des. auto. }
      }
    }
    { i. destruct (Time.le_lt_dec fto (Memory.max_ts loc mem0)).
      { left. exists fto, ffrom, fto, ffrom. splits; auto.
        { eapply (good_future_map_ident MAP); eauto. }
        { refl. }
        { refl. }
        { eapply (good_future_map_ident MAP); eauto.
          eapply memory_get_ts_le in GET. etrans; eauto.
        }
        { i. exploit (good_future_cover FUTURE).
          { econs; eauto. }
          i. des; auto.
          exfalso. inv ITV. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS. } etrans.
          { eapply TO. } etrans.
          { eapply l. }
          { left. auto. }
        }
      }
      { right. destruct (Time.le_lt_dec (tm loc) ffrom).
        { ii. eapply (good_future_map_bound MAP) in MAP0.
          eapply TimeFacts.lt_le_lt; eauto. }
        { exfalso. exploit (good_future_cover FUTURE).
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

  Lemma step_write_not_in_good_future P lang (th0 th1: Thread.t lang) tm e
        (TM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory th0)) (tm loc))
        (STEPS: pred_step P e th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in (fun loc ts =>
                                      (<<TS: Time.le ts (tm loc)>>) /\
                                      (<<PROM: ~ covered loc ts (Thread.memory th0)>>)))
    :
      good_future tm (Thread.memory th0) (Thread.memory th1).
  Proof.
    econs; auto.
    { eapply Memory.future_future_weak.
      inv STEPS. inv STEP.
      exploit Thread.step_future; eauto. i. des. auto. }
    { i. inv STEPS. inv STEP.
      eapply step_write_not_in_covered in COVERED; eauto. des; auto.
      apply not_and_or in COVERED. des.
      { right. destruct (Time.le_lt_dec ts (tm loc)); ss. }
      { left. apply NNPP; eauto. }
    }
  Qed.

  Lemma steps_write_not_in_good_future P lang (th0 th1: Thread.t lang) tm
        (TM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory th0)) (tm loc))
        (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: P <1= write_not_in (fun loc ts =>
                                      (<<TS: Time.le ts (tm loc)>>) /\
                                      (<<PROM: ~ covered loc ts (Thread.memory th0)>>)))
    :
      good_future tm (Thread.memory th0) (Thread.memory th1).
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

  Lemma write_not_in_good_future_traced lang (th0 th1: Thread.t lang) tr tm
        (TM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory th0)) (tm loc))
        (STEPS: Trace.steps tr th0 th1)
        (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (CLOSED: Memory.closed (Thread.memory th0))
        (NOTIN: List.Forall (fun em =>
                               write_not_in (fun loc ts =>
                                               (<<TS: Time.le ts (tm loc)>>) /\
                                               (<<PROM: ~ covered loc ts (Thread.memory th0)>>)) (snd em)) tr)
    :
      good_future tm (Thread.memory th0) (Thread.memory th1).
  Proof.
    econs; auto.
    { eapply Memory.future_future_weak.
      eapply Trace.steps_future; eauto. }
    { i. eapply write_not_in_covered_traced in COVERED; eauto. des; auto.
      apply not_and_or in COVERED. des.
      { right. destruct (Time.le_lt_dec ts (tm loc)); ss. }
      { left. apply NNPP; eauto. }
    }
  Qed.

  Lemma max_good_future_map (mem mem_good: Memory.t) (tm: TimeMap.t)
        (FUTURE: good_future tm mem mem_good)
        (CLOSED: Memory.closed mem)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
    :
      memory_map
        (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
        mem
        mem_good.
  Proof.
    assert (IDENT: map_ident_in_memory (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc)) mem).
    { ii. split; auto. eapply TimeFacts.le_lt_lt; eauto. }
    econs.
    { i. destruct msg as [val released|]; auto.
      exploit Memory.max_ts_spec; try apply GET. i. des. dup GET.
      eapply (good_future_future FUTURE) in GET.
      destruct GET as [from' [released' [GET [FROM RELEASED]]]]. guardH RELEASED.
      right. esplits.
      { ss. }
      { eapply TimeFacts.le_lt_lt; eauto. }
      { eapply map_ident_in_memory_closed_message; eauto.
        eapply CLOSED; eauto. }
      { econs 1. instantiate (1:=released'). unguard. des; auto. subst. refl. }
      { eauto. }
    }
    { i. destruct (Time.le_lt_dec (tm loc) ffrom).
      { right. ii. des. subst. eapply TimeFacts.lt_le_lt; eauto.  }
      { assert (TS: Time.lt fto (tm loc)).
        { destruct (Time.le_lt_dec (tm loc) fto); auto. exfalso.
          exploit (good_future_cover FUTURE).
          { instantiate (1:=Time.middle (Time.join (Memory.max_ts loc mem) ffrom) (tm loc)).
            instantiate (1:=loc).
            econs; eauto. econs; ss.
            { eapply TimeFacts.le_lt_lt.
              { eapply Time.join_r. }
              { eapply Time.middle_spec. unfold Time.join. des_ifs. }
            }
            { transitivity (tm loc); auto. left. eapply Time.middle_spec.
              unfold Time.join. des_ifs. }
          }
          { i. des.
            { inv COVERED. inv ITV. ss.
              eapply Memory.max_ts_spec in GET0. des.
              exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
              { eapply TO. } eapply TimeFacts.le_lt_lt.
              { eapply MAX. } eapply TimeFacts.le_lt_lt.
              { eapply Time.join_l. }
              { eapply Time.middle_spec. unfold Time.join. des_ifs. }
            }
            { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TS. } left.
              { eapply Time.middle_spec. unfold Time.join. des_ifs. }
            }
          }
        }
        left. exists fto, ffrom, fto, ffrom. splits; auto; try refl.
        i. exploit (good_future_cover FUTURE).
        { econs; eauto. }
        i. des; auto. inv ITV. ss.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. } etrans.
        { left. eapply TS0. }
        auto.
      }
    }
  Qed.


End GOODFUTURE.