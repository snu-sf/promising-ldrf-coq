Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
From PromisingLib Require Import Event.
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

Require Import Single.
Require Import PFStep.
Require Import LocalDRFPF.

Set Implicit Arguments.

Section NOTRELEASED.

  Variable loc: Loc.t.
  Variable ts: Time.t.
  Hypothesis NONBOT: ts <> Time.bot.

  Definition not_released_timemap (tm: TimeMap.t) := tm loc <> ts.

  Record not_released_view (vw: View.t): Prop :=
    {
      not_released_pln: not_released_timemap (View.pln vw);
      not_released_rlx: not_released_timemap (View.rlx vw);
    }.
  Hint Constructors not_released_view: core.

  Inductive not_released_opt_view: option View.t -> Prop :=
  | not_released_opt_view_some
      vw
      (RELEASED: not_released_view vw)
    :
      not_released_opt_view (Some vw)
  | not_released_opt_view_none
    :
      not_released_opt_view None
  .
  Hint Constructors not_released_opt_view: core.

  Inductive not_released_message: Message.t -> Prop :=
  | not_released_message_concrete
      val released
      (RELEASED: not_released_opt_view released)
    :
      not_released_message (Message.concrete val released)
  | not_released_message_reserve
    :
      not_released_message Message.reserve
  | not_released_message_undef
    :
      not_released_message Message.undef
  .
  Hint Constructors not_released_message: core.

  Record not_released_tview (vw: TView.t): Prop :=
    {
      not_released_rel: forall loc0, not_released_view ((TView.rel vw) loc0);
      not_released_cur: not_released_view (TView.cur vw);
      not_released_acq: not_released_view (TView.acq vw);
    }.
  Hint Constructors not_released_tview: core.

  Lemma not_released_timemap_bot
    :
      not_released_timemap TimeMap.bot.
  Proof.
    ii. eapply NONBOT. eauto.
  Qed.

  Lemma not_released_timemap_join tm0 tm1
      (TM0: not_released_timemap tm0)
      (TM1: not_released_timemap tm1)
    :
      not_released_timemap (TimeMap.join tm0 tm1).
  Proof.
    ii. unfold TimeMap.join, Time.join in *. des_ifs.
  Qed.

  Lemma not_released_timemap_singleton_join loc0 ts0
        (NEQ: (loc0, ts0) <> (loc, ts))
    :
      not_released_timemap (TimeMap.singleton loc0 ts0).
  Proof.
    ii. unfold TimeMap.singleton in *.
    setoid_rewrite LocFun.add_spec in H. des_ifs.
  Qed.

  Lemma not_released_view_bot
    :
      not_released_view View.bot.
  Proof.
    econs; eapply not_released_timemap_bot.
  Qed.

  Lemma not_released_unwrap vw
        (RELEASED: not_released_opt_view vw)
    :
      not_released_view (View.unwrap vw).
  Proof.
    inv RELEASED; ss. eapply not_released_view_bot.
  Qed.

  Lemma not_released_view_join vw0 vw1
        (VW0: not_released_view vw0)
        (VW1: not_released_view vw1)
    :
      not_released_view (View.join vw0 vw1).
  Proof.
    inv VW0. inv VW1.
    econs; eapply not_released_timemap_join; eauto.
  Qed.

  Lemma not_released_view_singleton_ur loc0 ts0
        (NEQ: (loc0, ts0) <> (loc, ts))
    :
      not_released_view (View.singleton_ur loc0 ts0).
  Proof.
    econs; ss; eapply not_released_timemap_singleton_join; eauto.
  Qed.

  Lemma not_released_view_singleton_rw loc0 ts0
        (NEQ: (loc0, ts0) <> (loc, ts))
    :
      not_released_view (View.singleton_rw loc0 ts0).
  Proof.
    econs; ss.
    - eapply not_released_timemap_bot; eauto.
    - eapply not_released_timemap_singleton_join; eauto.
  Qed.

  Lemma not_released_view_singleton_ur_if cond loc0 ts0
        (NEQ: (loc0, ts0) <> (loc, ts))
    :
      not_released_view (View.singleton_ur_if cond loc0 ts0).
  Proof.
    unfold View.singleton_ur_if. des_ifs.
    - eapply not_released_view_singleton_ur; eauto.
    - eapply not_released_view_singleton_rw; eauto.
  Qed.

  Inductive not_released_memory (prom mem: Memory.t): Prop :=
  | not_released_memory_intro
      (MESSAGES: forall loc0 ts0 from msg
                        (GET: Memory.get loc0 ts0 mem = Some (from, msg))
                        (LOCTS: (loc0, ts0) <> (loc, ts)),
          (<<RELEASED: not_released_message msg>>) \/ (<<GET: Memory.get loc0 ts0 prom = Some (from, msg)>>))
      (EXIST: exists from msg, (<<GET: Memory.get loc ts mem = Some (from, msg)>>) /\ (<<NRESERVE: msg <> Message.reserve>>))
      (NONE: Memory.get loc ts prom = None)
  .

  Inductive not_released_thread lang (th: Thread.t lang): Prop :=
  | not_released_thread_intro
      (TVIEW: not_released_tview (Local.tview (Thread.local th)))
      (MEM: not_released_memory (Local.promises (Thread.local th)) (Thread.memory th))
      (SC: not_released_timemap (Thread.sc th))
  .

  Lemma not_released_promise_neq prom0 mem0 loc0 from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc0 from to msg prom1 mem1 kind)
        (RELEASED: not_released_memory prom0 mem0)
    :
      (loc0, to) <> (loc, ts).
  Proof.
    ii. clarify. inv RELEASED. des. inv PROMISE.
    - eapply Memory.add_get0 in MEM. eapply Memory.add_get0 in PROMISES.
      des. clarify.
    - eapply Memory.split_get0 in MEM. eapply Memory.split_get0 in PROMISES.
      des. clarify.
    - eapply Memory.lower_get0 in MEM. eapply Memory.lower_get0 in PROMISES.
      des. clarify.
    - eapply Memory.remove_get0 in MEM. eapply Memory.remove_get0 in PROMISES.
      des. clarify.
  Qed.

  Lemma not_released_write_neq prom0 mem0 loc0 from to msg prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc0 from to msg prom1 mem1 kind)
        (RELEASED: not_released_memory prom0 mem0)
    :
      (loc0, to) <> (loc, ts).
  Proof.
    inv WRITE. eapply not_released_promise_neq; eauto.
  Qed.

  Lemma not_released_promise prom0 mem0 loc0 from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc0 from to msg prom1 mem1 kind)
        (RELEASED: not_released_memory prom0 mem0)
    :
      not_released_memory prom1 mem1.
  Proof.
    hexploit not_released_promise_neq; eauto. intros NEQ.
    inv RELEASED. inv PROMISE.
    - econs.
      + ii. erewrite Memory.add_o in GET; eauto.
        erewrite (@Memory.add_o prom1 prom0); eauto. des_ifs; auto.
      + des. eapply Memory.add_get1 in GET; eauto.
      + erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify.
    - econs.
      + ii. erewrite Memory.split_o in GET; eauto.
        erewrite (@Memory.split_o prom1 prom0); eauto. des_ifs; auto.
      + des. eapply Memory.split_get1 in GET; eauto. des. eauto.
      + erewrite Memory.split_o; eauto. des_ifs.
        * ss. des; clarify.
        * ss. des; clarify.
          eapply Memory.split_get0 in PROMISES. des. clarify.
    - econs.
      + ii. erewrite Memory.lower_o in GET; eauto.
        erewrite (@Memory.lower_o prom1 prom0); eauto. des_ifs; auto.
      + des. eapply Memory.lower_get1 in GET; eauto. des.
        clarify. esplits; eauto. inv MSG_LE; ss.
      + erewrite Memory.lower_o; eauto. des_ifs. ss. des; clarify.
    - econs.
      + ii. erewrite Memory.remove_o in GET; eauto.
        erewrite (@Memory.remove_o prom1 prom0); eauto. des_ifs; auto.
      + des. eapply Memory.remove_get1 in GET; eauto. des; eauto. clarify.
      + erewrite Memory.remove_o; eauto. des_ifs.
  Qed.

  Lemma not_released_fulfill prom0 loc0 from to msg prom1 mem
        (FULFILL: Memory.remove prom0 loc0 from to msg prom1)
        (RELEASED: not_released_memory prom0 mem)
        (RELEASEDM: not_released_message msg)
        (GET: Memory.get loc0 to mem = Some (from, msg))
    :
      not_released_memory prom1 mem.
  Proof.
    econs.
    - ii. dup GET0. eapply RELEASED in GET0.
      { erewrite Memory.remove_o; eauto.
        des; auto. des_ifs; auto. ss. des; clarify. left. auto. }
      { ii. clarify. }
    - eapply RELEASED.
    - inv RELEASED. erewrite Memory.remove_o; eauto. des_ifs.
  Qed.

  Lemma not_released_write prom0 mem0 loc0 from to msg prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc0 from to msg prom1 mem1 kind)
        (RELEASED: not_released_memory prom0 mem0)
        (RELEASEDM: not_released_message msg)
    :
      not_released_memory prom1 mem1.
  Proof.
    inv WRITE. hexploit not_released_promise; eauto. i.
    eapply not_released_fulfill; eauto.
    eapply Memory.write_get2; eauto.
  Qed.

  Lemma not_released_write_na prom0 mem0 loc0 ts0 from to val prom1 mem1 kind msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc0 from to val prom1 mem1 msgs kinds kind)
        (RELEASED: not_released_memory prom0 mem0)
    :
      not_released_memory prom1 mem1.
  Proof.
    revert RELEASED. induction WRITE; i.
    { eapply not_released_write; eauto. }
    { eapply IHWRITE. eapply not_released_write; eauto.
      unguard. des; clarify. econs; eauto.
    }
  Qed.

  Lemma not_released_write_na_neq ts0 prom0 mem0 loc0 from to val prom1 mem1 msgs kinds kind
        (WRITE: Memory.write_na ts0 prom0 mem0 loc0 from to val prom1 mem1 msgs kinds kind)
        (RELEASED: not_released_memory prom0 mem0)
    :
      (loc0, to) <> (loc, ts).
  Proof.
    revert RELEASED. induction WRITE; i.
    { eapply not_released_write_neq; eauto. }
    { eapply IHWRITE. eapply not_released_write; eauto.
      unguard. des; clarify. econs; eauto.
    }
  Qed.

  Lemma not_released_read lc0 mem0 loc0 ts0 val released ord lc1
        (READ: Local.read_step lc0 mem0 loc0 ts0 val released ord lc1)
        (TVIEW: not_released_tview (Local.tview lc0))
        (MEM: not_released_memory (Local.promises lc0) mem0)
        (CONSISTENT: Local.promise_consistent lc1)
        (NOTREAD: (loc0, ts0) <> (loc, ts))
    :
      (<<TVIEW: not_released_tview (Local.tview lc1)>>) /\
      (<<MEM: not_released_memory (Local.promises lc1) mem0>>) /\
      (<<RELEASEDM: not_released_opt_view released>>).
  Proof.
    inv READ. inv MEM. exploit MESSAGES; eauto. i. des.
    { inv RELEASED. splits; ss.
      { econs; ss.
        { eapply TVIEW; eauto. }
        { eapply not_released_view_join.
          { eapply not_released_view_join.
            { eapply TVIEW; eauto. }
            { eapply not_released_view_singleton_ur_if; eauto. }
          }
          { des_ifs.
            { eapply not_released_unwrap; eauto. }
            { eapply not_released_view_bot; eauto. }
          }
        }
        { eapply not_released_view_join.
          { eapply not_released_view_join.
            { eapply TVIEW; eauto. }
            { eapply not_released_view_singleton_ur_if; eauto. }
          }
          { des_ifs.
            { eapply not_released_unwrap; eauto. }
            { eapply not_released_view_bot; eauto. }
          }
        }
      }
      { econs; eauto. }
    }
    { exfalso. exploit CONSISTENT; eauto; ss. i.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      etrans; [|try apply TimeMap.join_l].
      etrans; [|try apply TimeMap.join_r]. clear GET0.
      unfold View.singleton_ur_if. des_ifs; ss.
      { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq. refl. }
      { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq. refl. }
      { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq. refl. }
      { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq. refl. }
    }
  Qed.

  Lemma not_released_read_racy lc0 mem0 val released ord lc1
        (READ: Local.read_step lc0 mem0 loc ts val released ord lc1)
        (TVIEW: not_released_tview (Local.tview lc0))
        (MEM: not_released_memory (Local.promises lc0) mem0)
        (CONSISTENT: Local.promise_consistent lc1)
    :
      Time.lt (if Ordering.le Ordering.relaxed ord
               then ((TView.cur (Local.tview lc0)).(View.rlx) loc)
               else ((TView.cur (Local.tview lc0)).(View.pln) loc)) ts.
  Proof.
    inv READ. inv READABLE. des_ifs.
    { exploit RLX; eauto. intros H. inv H; eauto. inv H0. exfalso.
      eapply (not_released_rlx (not_released_cur TVIEW)); auto. }
    { inv PLN; eauto. inv H. exfalso.
      eapply (not_released_pln (not_released_cur TVIEW)); auto. }
  Qed.

  Lemma not_released_write_tview tvw0 sc0 loc0 to ord
        (TVIEW: not_released_tview tvw0)
        (NEQ: (loc0, to) <> (loc, ts))
    :
      not_released_tview (TView.write_tview tvw0 sc0 loc0 to ord).
  Proof.
    econs; ss.
    { i. setoid_rewrite LocFun.add_spec. des_ifs.
      { eapply not_released_view_join; eauto.
        { eapply TVIEW. }
        { eapply not_released_view_singleton_ur; eauto. }
      }
      { eapply not_released_view_join; eauto.
        { eapply TVIEW. }
        { eapply not_released_view_singleton_ur; eauto. }
      }
      { eapply TVIEW. }
    }
    { eapply not_released_view_join; eauto.
      { eapply TVIEW. }
      { eapply not_released_view_singleton_ur; eauto. }
    }
    { eapply not_released_view_join; eauto.
      { eapply TVIEW. }
      { eapply not_released_view_singleton_ur; eauto. }
    }
  Qed.

  Lemma not_released_write_releaed tvw0 sc0 loc0 to releasedr ord
        (TVIEW: not_released_tview tvw0)
        (RELEASEDR: not_released_opt_view releasedr)
        (NEQ: (loc0, to) <> (loc, ts))
    :
      not_released_opt_view (TView.write_released tvw0 sc0 loc0 to releasedr ord).
  Proof.
    unfold TView.write_released. des_ifs. econs. eapply not_released_view_join.
    { eapply not_released_unwrap; eauto. }
    { eapply not_released_write_tview; eauto. }
  Qed.

  Lemma not_released_write_step lc0 sc0 mem0 loc0 from to val releasedr releasedm ord lc1 sc1 mem1 kind
        (WRITE: Local.write_step lc0 sc0 mem0 loc0 from to val releasedr releasedm ord lc1 sc1 mem1 kind)
        (TVIEW: not_released_tview (Local.tview lc0))
        (MEM: not_released_memory (Local.promises lc0) mem0)
        (SC: not_released_timemap sc0)
        (RELEASEDR: not_released_opt_view releasedr)
    :
      (<<TVIEW: not_released_tview (Local.tview lc1)>>) /\
      (<<MEM: not_released_memory (Local.promises lc1) mem1>>) /\
      (<<SC: not_released_timemap sc1>>).
  Proof.
    inv WRITE. ss.
    hexploit not_released_write_neq; eauto. i.
    hexploit not_released_write; eauto.
    { econs. eapply not_released_write_releaed; eauto. }
    i. esplits; eauto.
    eapply not_released_write_tview; eauto.
  Qed.

  Lemma not_released_write_na_step lc0 sc0 mem0 loc0 from to val ord lc1 sc1 mem1 msgs kinds kind
        (WRITE: Local.write_na_step lc0 sc0 mem0 loc0 from to val ord lc1 sc1 mem1 msgs kinds kind)
        (TVIEW: not_released_tview (Local.tview lc0))
        (MEM: not_released_memory (Local.promises lc0) mem0)
        (SC: not_released_timemap sc0)
    :
      (<<TVIEW: not_released_tview (Local.tview lc1)>>) /\
      (<<MEM: not_released_memory (Local.promises lc1) mem1>>) /\
      (<<SC: not_released_timemap sc1>>).
  Proof.
    inv WRITE. ss.
    hexploit not_released_write_na_neq; eauto. i.
    hexploit not_released_write_na; eauto.
    i. esplits; eauto.
    eapply not_released_write_tview; eauto.
  Qed.

  Lemma not_released_read_fence_tview tvw ord
        (TVIEW: not_released_tview tvw)
    :
      not_released_tview (TView.read_fence_tview tvw ord).
  Proof.
    econs; ss.
    { eapply TVIEW. }
    { des_ifs; eapply TVIEW. }
    { eapply TVIEW. }
  Qed.

  Lemma not_released_write_fence_sc tvw sc ord
        (TVIEW: not_released_tview tvw)
        (SC: not_released_timemap sc)
    :
      not_released_timemap (TView.write_fence_sc tvw sc ord).
  Proof.
    unfold TView.write_fence_sc. des_ifs.
    eapply not_released_timemap_join; eauto. eapply TVIEW.
  Qed.

  Lemma not_released_write_fence_tview tvw sc ord
        (TVIEW: not_released_tview tvw)
        (SC: not_released_timemap sc)
    :
      not_released_tview (TView.write_fence_tview tvw sc ord).
  Proof.
    econs; ss.
    { i. des_ifs.
      { econs; eapply not_released_write_fence_sc; eauto. }
      { eapply TVIEW. }
      { eapply TVIEW. }
    }
    { des_ifs.
      { econs; eapply not_released_write_fence_sc; eauto. }
      { eapply TVIEW. }
    }
    { eapply not_released_view_join.
      { eapply TVIEW. }
      des_ifs.
      { econs; eapply not_released_write_fence_sc; eauto. }
      { eapply not_released_view_bot. }
    }
  Qed.

  Lemma not_released_fence lc0 sc0 ordr ordw lc1 sc1 mem
        (FENCE: Local.fence_step lc0 sc0 ordr ordw lc1 sc1)
        (TVIEW: not_released_tview (Local.tview lc0))
        (MEM: not_released_memory (Local.promises lc0) mem)
        (SC: not_released_timemap sc0)
    :
      (<<TVIEW: not_released_tview (Local.tview lc1)>>) /\
      (<<MEM: not_released_memory (Local.promises lc1) mem>>) /\
      (<<SC: not_released_timemap sc1>>).
  Proof.
    inv FENCE. splits; ss.
    { eapply not_released_write_fence_tview; eauto.
      eapply not_released_read_fence_tview; eauto.
    }
    { eapply not_released_write_fence_sc; eauto.
      eapply not_released_read_fence_tview; eauto.
    }
  Qed.

  Lemma not_released_thread_step lang (th0 th1: Thread.t lang) pf e
        (STEP: Thread.step pf e th0 th1)
        (CONSISTENT: Local.promise_consistent (Thread.local th1))
        (THREAD: not_released_thread th0)
    :
      (<<THREAD: not_released_thread th1>> /\ <<RACY: ~ PFRace.reading_event loc ts e>>) \/
      (<<RACY: PFRace.racy_read loc ts (Thread.local th0) e>>).
  Proof.
    inv THREAD. inv STEP.
    { inv STEP0. inv LOCAL. ss. exploit not_released_promise; eauto.
      i. left. splits; ss; eauto. ii. inv H. }
    { inv STEP0. inv LOCAL; ss.
      { left. splits; [|intros H; inv H]. econs; eauto. }
      { destruct (loc_ts_eq_dec (loc0, ts0) (loc, ts)).
        { ss. des; clarify. right.
          exploit not_released_read_racy; eauto. i. econs; eauto.
        }
        { exploit not_released_read; eauto.
          { ii. ss. des; clarify. }
          guardH o. i. des. left. splits.
          { econs; eauto. }
          { ii. inv H. ss. unguard. des; clarify. }
        }
      }
      { exploit not_released_write_step; eauto. i. des.
        left. splits; [|intros H; inv H]. econs; eauto. }
      { eapply write_step_promise_consistent in CONSISTENT; eauto.
        destruct (loc_ts_eq_dec (loc0, tsr) (loc, ts)).
        { ss. des; clarify. right.
          exploit not_released_read_racy; eauto. i. econs; eauto.
        }
        { exploit not_released_read; eauto.
          { ii. ss. des; clarify. }
          guardH o. i. des. left.
          exploit not_released_write_step; eauto. i. des. splits.
          { econs; eauto. }
          { ii. inv H. ss. unguard. des; clarify. }
        }
      }
      { exploit not_released_fence; eauto.
        i. des. left. splits; [|intros H; inv H]. econs; eauto. }
      { exploit not_released_fence; eauto.
        i. des. left. splits; [|intros H; inv H]. econs; eauto. }
      { inv LOCAL0. left. splits; [|intros H; inv H]. econs; eauto. }
      { exploit not_released_write_na_step; eauto. i. des.
        left. splits; [|intros H; inv H]. econs; eauto. }
      { inv LOCAL0.
        destruct (loc_ts_eq_dec (loc0, to) (loc, ts)).
        { ss. des; clarify. right. inv RACE. econs; eauto. }
        { left. splits.
          { econs; eauto. }
          { ii. inv H; des; ss. }
        }
      }
      { inv LOCAL0. left. splits; [|intros H; inv H]. econs; eauto. }
      { inv LOCAL0.
        { left. splits; [|intros H; inv H]. econs; eauto. }
        { left. splits; [|intros H; inv H]. econs; eauto. }
        { left. splits; [|intros H; inv H]. econs; eauto. }
      }
    }
  Qed.

  Lemma not_released_thread_opt_step lang (th0 th1: Thread.t lang) e
        (STEP: Thread.opt_step e th0 th1)
        (CONSISTENT: Local.promise_consistent (Thread.local th1))
        (THREAD: not_released_thread th0)
    :
      (<<THREAD: not_released_thread th1>> /\ <<RACY: ~ PFRace.reading_event loc ts e>>) \/
      (<<RACY: PFRace.racy_read loc ts (Thread.local th0) e>>).
  Proof.
    inv STEP; eauto.
    { left. splits; auto. ii. inv H. }
    { eapply not_released_thread_step; eauto. }
  Qed.

  Lemma not_released_rtc_reserve_step lang (th0 th1: Thread.t lang)
        (STEPS: rtc (@Thread.reserve_step _) th0 th1)
        (CONSISTENT: Local.promise_consistent (Thread.local th1))
        (THREAD: not_released_thread th0)
    :
      not_released_thread th1.
  Proof.
    ginduction STEPS; eauto. i. eapply IHSTEPS; eauto.
    inv H. eapply not_released_thread_step in STEP; eauto.
    { des; auto. inv RACY. }
    { eapply rtc_reserve_step_promise_consistent; eauto. }
  Qed.

  Lemma not_released_rtc_cancel_step lang (th0 th1: Thread.t lang)
        (STEPS: rtc (@Thread.cancel_step _) th0 th1)
        (CONSISTENT: Local.promise_consistent (Thread.local th1))
        (THREAD: not_released_thread th0)
    :
      not_released_thread th1.
  Proof.
    ginduction STEPS; eauto. i. eapply IHSTEPS; eauto.
    inv H. eapply not_released_thread_step in STEP; eauto.
    { des; auto. inv RACY. }
    { eapply rtc_cancel_step_promise_consistent; eauto. }
  Qed.

  Definition not_released_configuration tid (c: Configuration.t): Prop :=
    forall lang st lc
           (TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
      not_released_thread (Thread.mk _ st lc (Configuration.sc c) (Configuration.memory c)).

  Lemma not_released_configuration_step L tid e c0 c1
        (STEP: PFConfiguration.step L e tid c0 c1)
        (CONFIGURATION: not_released_configuration tid c0)
        (WF: Configuration.wf c0)
    :
      (<<RELEASED: not_released_configuration tid c1>> /\ <<RACY: ~ PFRace.reading_event loc ts e>>) \/
      (<<RACY: PFRace.racy_read_step L loc ts e tid c0 c1>>).
  Proof.
    inv STEP.
    exploit Thread.rtc_cancel_step_future; eauto; try eapply WF; eauto. i. des. ss.
    exploit Thread.opt_step_future; eauto. i. des. ss.
    exploit Thread.rtc_reserve_step_future; eauto. i. des. ss.
    assert (CONSISTENT4: Local.promise_consistent lc4).
    { destruct (classic (ThreadEvent.get_machine_event e = MachineEvent.failure)).
      { subst. eapply rtc_reserve_step_promise_consistent2 in RESERVES; eauto.
        inv STEP0; ss. inv STEP; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; auto.
      }
      { specialize (CONSISTENT H).
        eapply PF.pf_consistent_consistent in CONSISTENT.
        eapply consistent_promise_consistent in CONSISTENT; eauto. }
    }
    assert (CONSISTENT3: Local.promise_consistent (Thread.local e3)).
    { eapply rtc_reserve_step_promise_consistent; eauto. }
    assert (CONSISTENT2: Local.promise_consistent (Thread.local e2)).
    { inv STEP0; eauto. eapply step_promise_consistent; eauto. }
    assert (CONSISTENT1: Local.promise_consistent lc1).
    { eapply rtc_cancel_step_promise_consistent in CANCELS; eauto. }
    exploit not_released_rtc_cancel_step; eauto. intros RELEASED2.
    exploit not_released_thread_opt_step; eauto. i. des.
    { exploit not_released_rtc_reserve_step; eauto. intros RELEASED4.
      inv RELEASED4. ss. left. splits; auto. ii. ss.
      erewrite IdentMap.gss in TID0. dep_clarify. }
    { right. econs; eauto. }
  Qed.

  Lemma not_released_configuration_steps L tid c0 c1
        (STEPS: rtc (PFConfiguration.machine_step L MachineEvent.silent tid) c0 c1)
        (CONFIGURATION: not_released_configuration tid c0)
        (WF: Configuration.wf c0)
    :
      (<<RELEASED: not_released_configuration tid c1>>) \/
      (exists c1' c2' e,
          (<<STEPS: rtc (PFConfiguration.machine_step L MachineEvent.silent tid) c0 c1'>>) /\
          (<<RACY: PFRace.racy_read_step L loc ts e tid c1' c2'>>)).
  Proof.
    ginduction STEPS; eauto. i. inv H.
    exploit not_released_configuration_step; eauto. i. des.
    { erewrite H1. exploit IHSTEPS; eauto.
      { eapply PFConfiguration.step_event_configuration_step in STEP; eauto.
        des. eapply SConfiguration.step_future; eauto. }
      i. des; auto. right. exists c1', c2'. esplits; eauto.
      econs 2; eauto. erewrite <- H1. econs; eauto.
    }
    { right. esplits; eauto. }
  Qed.

  Lemma promise_not_released_timemap prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        tm
        (TM: Memory.closed_timemap tm mem0)
    :
      not_released_timemap tm.
  Proof.
    inv PROMISE. ii.
    specialize (TM loc). des. eapply Memory.add_get0 in MEM.
    des. rewrite H in *. clarify.
  Qed.

  Lemma promise_not_released_view prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: Memory.closed_view vw mem0)
    :
      not_released_view vw.
  Proof.
    inv VW. econs; eapply promise_not_released_timemap; eauto.
  Qed.

  Lemma promise_not_released_tview prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: TView.closed vw mem0)
    :
      not_released_tview vw.
  Proof.
    inv VW. econs; i; eapply promise_not_released_view; eauto.
  Qed.

  Lemma promise_not_released_opt_view prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: Memory.closed_opt_view vw mem0)
    :
      not_released_opt_view vw.
  Proof.
    inv VW; econs. eapply promise_not_released_view; eauto.
  Qed.

  Lemma promise_not_released_message prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        msg0
        (MSG: Memory.closed_message msg0 mem0)
    :
      not_released_message msg0.
  Proof.
    inv MSG; econs. eapply promise_not_released_opt_view; eauto.
  Qed.

  Lemma promise_not_released_memory prom0 mem0 from msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        (MEM: Memory.closed mem0)
        (NRESERVE: msg <> Message.reserve)
        prom
        (MLE: Memory.le prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    inversion PROMISE. econs.
    { i. erewrite Memory.add_o in GET; eauto. des_ifs.
      { ss. des; clarify. }
      { left. eapply promise_not_released_message; eauto. eapply MEM; eauto. }
    }
    { eapply Memory.add_get0 in MEM0. des. esplits; eauto. }
    { destruct (Memory.get loc ts prom) as [[from0 msg0]|] eqn:GET; auto.
      eapply MLE in GET. eapply Memory.add_get0 in MEM0. des. clarify. }
  Qed.

  Lemma write_not_released_timemap prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        tm
        (TM: Memory.closed_timemap tm mem0)
    :
      not_released_timemap tm.
  Proof.
    inv WRITE. eapply promise_not_released_timemap; eauto.
  Qed.

  Lemma write_not_released_view prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: Memory.closed_view vw mem0)
    :
      not_released_view vw.
  Proof.
    inv WRITE. eapply promise_not_released_view; eauto.
  Qed.

  Lemma write_not_released_tview prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: TView.closed vw mem0)
    :
      not_released_tview vw.
  Proof.
    inv WRITE. eapply promise_not_released_tview; eauto.
  Qed.

  Lemma write_not_released_opt_view prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        vw
        (VW: Memory.closed_opt_view vw mem0)
    :
      not_released_opt_view vw.
  Proof.
    inv WRITE. eapply promise_not_released_opt_view; eauto.
  Qed.

  Lemma write_not_released_message prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        msg0
        (MSG: Memory.closed_message msg0 mem0)
    :
      not_released_message msg0.
  Proof.
    inv WRITE. eapply promise_not_released_message; eauto.
  Qed.

  Lemma write_not_released_memory prom0 mem0 from msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 Memory.op_kind_add)
        (MEM: Memory.closed mem0)
        (NRESERVE: msg <> Message.reserve)
        prom
        (MLE: Memory.le prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    inv WRITE. eapply promise_not_released_memory; eauto.
  Qed.

  Lemma write_na_not_released_timemap prom0 mem0 ts0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        tm
        (TM: Memory.closed_timemap tm mem0)
    :
      not_released_timemap tm.
  Proof.
    revert tm TM. remember Memory.op_kind_add. revert Heqo.
    remember loc. revert Heqt KINDS. guardH TS. revert TS.
    induction WRITE; i; subst.
    { inv WRITE. inv PROMISE. ii.
      specialize (TM loc). des. eapply Memory.add_get0 in MEM.
      des. rewrite H in *. unguard. des; clarify.
    }
    { inv KINDS; subst.
      cut (to' = ts \/ __guard__(to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))).
      2:{ unguard. ss. des; clarify; eauto. }
      i. des.
      { subst. eapply write_not_released_timemap; eauto. }
      { eapply IHWRITE; eauto.
        eapply Memory.future_closed_timemap; eauto.
        econs; [|refl]. econs.
        { eapply Memory.write_op; eauto. }
        { red in MSG_EX. des; clarify. econs; eauto. }
        { red in MSG_EX. des; clarify. econs; eauto. eapply Time.bot_spec. }
      }
    }
  Qed.

  Lemma write_na_not_released_view ts0 prom0 mem0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        vw
        (VW: Memory.closed_view vw mem0)
    :
      not_released_view vw.
  Proof.
    inv VW. econs; eapply write_na_not_released_timemap; eauto.
  Qed.

  Lemma write_na_not_released_tview ts0 prom0 mem0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        vw
        (VW: TView.closed vw mem0)
    :
      not_released_tview vw.
  Proof.
    inv VW. econs; i; eapply write_na_not_released_view; eauto.
  Qed.

  Lemma write_na_not_released_opt_view ts0 prom0 mem0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        vw
        (VW: Memory.closed_opt_view vw mem0)
    :
      not_released_opt_view vw.
  Proof.
    inv VW; econs. eapply write_na_not_released_view; eauto.
  Qed.

  Lemma write_na_not_released_message ts0 prom0 mem0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        msg0
        (MSG: Memory.closed_message msg0 mem0)
    :
      not_released_message msg0.
  Proof.
    inv MSG; econs. eapply write_na_not_released_opt_view; eauto.
  Qed.

  Lemma promise_other_not_released_memory prom0 mem0 loc0 from to msg prom1 mem1
        (PROMISE: Memory.promise prom0 mem0 loc0 from to msg prom1 mem1 Memory.op_kind_add)
        (RELEASEDM: not_released_message msg)
        prom
        (MLE: Memory.le prom mem0)
        (RELEASED: not_released_memory prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    inv PROMISE. inv RELEASED. econs; eauto.
    { i. erewrite Memory.add_o in GET; eauto. des_ifs.
      { eauto. }
      { eapply MESSAGES; eauto. }
    }
    { des. esplits; eauto. eapply Memory.add_get1; eauto. }
  Qed.

  Lemma write_other_not_released_memory prom0 mem0 loc0 from to msg prom1 mem1
        (WRITE: Memory.write prom0 mem0 loc0 from to msg prom1 mem1 Memory.op_kind_add)
        (RELEASEDM: not_released_message msg)
        prom
        (MLE: Memory.le prom mem0)
        (RELEASED: not_released_memory prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    inv WRITE. eapply promise_other_not_released_memory; eauto.
  Qed.

  Lemma write_na_other_not_released_memory prom0 mem0 loc0 ts0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc0 from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        prom
        (MLE: Memory.le prom mem0)
        (RELEASED: not_released_memory prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    revert KINDS RELEASED. remember Memory.op_kind_add.
    revert Heqo. induction WRITE; eauto; i; subst.
    { eapply write_other_not_released_memory; eauto. }
    inv KINDS. eapply IHWRITE; eauto.
    { inv WRITE_EX. inv PROMISE. ii.
      eapply MLE in LHS. eapply Memory.add_get1; eauto.
    }
    { eapply write_other_not_released_memory; eauto.
      unguard. des; clarify. econs; eauto.
    }
  Qed.

  Lemma write_na_not_released_memory ts0 prom0 mem0 from to msg prom1 mem1 msgs kinds
        (WRITE: Memory.write_na ts0 prom0 mem0 loc from to msg prom1 mem1 msgs kinds Memory.op_kind_add)
        (TS: to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))
        (KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds)
        (MEM: Memory.closed mem0)
        prom
        (MLE: Memory.le prom mem0)
    :
      not_released_memory prom mem1.
  Proof.
    remember Memory.op_kind_add. revert Heqo.
    remember loc. revert Heqt KINDS prom MLE. guardH TS. revert TS.
    induction WRITE; i.
    { unguard. des; ss; clarify.
      eapply write_not_released_memory; eauto; ss.
    }
    { inv KINDS; subst.
      cut (to' = ts \/ __guard__(to = ts \/ exists from0 msg0, (<<IN: List.In (from0, ts, msg0) msgs>>))).
      2:{ unguard. ss. des; clarify; eauto. }
      intros TS0. des.
      { subst. hexploit write_not_released_memory; eauto.
        { red in MSG_EX. des; clarify. }
        i. eapply write_na_other_not_released_memory; eauto.
        inv WRITE_EX. inv PROMISE. ii.
        eapply MLE in LHS. eapply Memory.add_get1; eauto.
      }
      { eapply IHWRITE; eauto.
        { eapply Memory.write_closed; eauto.
          { red in MSG_EX. des; clarify. econs. econs. }
          { red in MSG_EX. des; clarify. econs. eapply Time.bot_spec. }
        }
        { inv WRITE_EX. inv PROMISE. ii.
          eapply MLE in LHS. eapply Memory.add_get1; eauto.
        }
      }
    }
  Qed.
End NOTRELEASED.


Lemma promise_not_released_add L loc ts prom0 mem0 from msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from ts msg prom1 mem1 kind)
      (PF: PF.pf_promises L prom0)
      (LOC: L loc)
      (NRESERVE: msg <> Message.reserve)
  :
    (<<KIND: kind = Memory.op_kind_add>>) /\ (<<NONBOT: ts <> Time.bot>>).
Proof.
  inv PROMISE.
  { splits; auto.
    ii. subst. eapply add_succeed_wf in MEM. des.
    eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec.
  }
  { eapply Memory.split_get0 in PROMISES. des. subst.
    eapply PF in GET0; eauto. ss. }
  { eapply Memory.lower_get0 in PROMISES. des. subst.
    eapply PF in GET; eauto. clarify. inv MSG_LE; ss. }
  { ss. }
Qed.

Lemma write_not_released_add L loc ts prom0 mem0 from msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from ts msg prom1 mem1 kind)
      (PF: PF.pf_promises L prom0)
      (LOC: L loc)
      (NRESERVE: msg <> Message.reserve)
  :
    (<<KIND: kind = Memory.op_kind_add>>) /\ (<<NONBOT: ts <> Time.bot>>).
Proof.
  inv WRITE. eapply promise_not_released_add; eauto.
Qed.

Lemma write_na_not_released_add L loc ts ts0 prom0 mem0 from msg prom1 mem1 kind msgs kinds
      (WRITE: Memory.write_na ts0 prom0 mem0 loc from ts msg prom1 mem1 msgs kinds kind)
      (PF: PF.pf_promises L prom0)
      (LOC: L loc)
  :
    (<<KIND: kind = Memory.op_kind_add>>) /\ (<<KINDS: List.Forall (fun k => k = Memory.op_kind_add) kinds>>) /\ (<<NONBOT: ts <> Time.bot>>) /\ (<<NONBOTS: List.Forall (fun '(from, to, msg) => to <> Time.bot) msgs>>).
Proof.
  revert PF. induction WRITE; i.
  { hexploit write_not_released_add; eauto; ss. i. des. splits; auto. }
  { hexploit write_not_released_add; eauto; ss.
    { unguard. des; clarify. }
    i. des. hexploit IHWRITE; eauto.
    { eapply PF.pf_promises_write; eauto. }
    i. des. splits; eauto.
  }
Qed.

Lemma thread_step_write_not_released L loc ts lang (th0 th1: Thread.t lang) pf e
      lc_other
      (STEP: Thread.step pf e th0 th1)
      (WRITE: PFRace.writing_event loc ts e)
      (PF: PF.pf_promises L (Local.promises (Thread.local th0)))
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (MEM: Memory.closed (Thread.memory th0))
      (LOC: L loc)
      (LOCALOTHER: Local.wf lc_other (Thread.memory th0))
  :
    (<<NONBOT: ts <> Time.bot>>) /\
    (<<TVIEW: not_released_tview loc ts (Local.tview lc_other)>>) /\
    (<<MEM: not_released_memory loc ts (Local.promises lc_other) (Thread.memory th1)>>) /\
    (<<SC: not_released_timemap loc ts (Thread.sc th1)>>).
Proof.
  inv STEP; inv STEP0; ss.
  { inv WRITE. }
  inv WRITE; inv LOCAL0.
  { inv LOCAL1. inv WRITE.
    exploit promise_not_released_add; eauto; ss. i. des; subst. splits; auto.
    { eapply promise_not_released_tview; eauto. eapply LOCALOTHER. }
    { eapply promise_not_released_memory; eauto; ss. eapply LOCALOTHER. }
    { eapply promise_not_released_timemap; eauto. }
  }
  { inv LOCAL1. inv LOCAL2. inv WRITE. ss.
    exploit promise_not_released_add; eauto; ss. i. des. des; subst. splits; auto.
    { eapply promise_not_released_tview; eauto. eapply LOCALOTHER. }
    { eapply promise_not_released_memory; eauto; ss. eapply LOCALOTHER. }
    { eapply promise_not_released_timemap; eauto. }
  }
  { inv LOCAL1. guardH IN.
    exploit write_na_not_released_add; eauto; ss. i. des; subst.
    assert (TSNBOT: ts <> Time.bot).
    { red in IN. des; subst; ss.
      eapply List.Forall_forall in NONBOTS; eauto. ss. }
    splits; auto.
    { eapply write_na_not_released_tview; eauto; ss. eapply LOCALOTHER. }
    { eapply write_na_not_released_memory; eauto. eapply LOCALOTHER. }
    { eapply write_na_not_released_timemap; eauto. }
  }
Qed.

Lemma rtc_reserve_step_write_not_released loc ts lang (th0 th1: Thread.t lang)
      lc_other
      (STEPS: rtc (@Thread.reserve_step _) th0 th1)
      (TVIEW: not_released_tview loc ts (Local.tview lc_other))
      (MEM: not_released_memory loc ts (Local.promises lc_other) (Thread.memory th0))
      (SC: not_released_timemap loc ts (Thread.sc th0))
  :
    (<<TVIEW: not_released_tview loc ts (Local.tview lc_other)>>) /\
    (<<MEM: not_released_memory loc ts (Local.promises lc_other) (Thread.memory th1)>>) /\
    (<<SC: not_released_timemap loc ts (Thread.sc th1)>>).
Proof.
  ginduction STEPS; eauto.
  i. inv H. inv STEP; inv STEP0; inv LOCAL. ss. inv PROMISE.
  eapply IHSTEPS; eauto. inv MEM. des. econs; eauto.
  { i. erewrite Memory.add_o in GET0; eauto. des_ifs.
    { ss. des; clarify. left. econs. }
    { eapply MESSAGES; eauto. }
  }
  { eapply Memory.add_get1 in GET; eauto. }
Qed.

Lemma configuration_write_not_released L c0 c1 e loc ts tid0 tid1
      (WRITE: PFRace.writing_event loc ts e)
      (STEP: PFConfiguration.step L e tid0 c0 c1)
      (WF: Configuration.wf c0)
      (PF: PF.pf_configuration L c0)
      (TID: tid0 <> tid1)
      (LOC: L loc)
  :
    (<<NONBOT: ts <> Time.bot>>) /\ (<<RELEASED: not_released_configuration loc ts tid1 c1>>).
Proof.
  inv STEP. hexploit (PF tid0); eauto. intros PROMISES.
  exploit Thread.rtc_cancel_step_future; eauto; try eapply WF; eauto.
  i. des. ss.
  inv STEP0.
  { inv WRITE. }
  hexploit PF.pf_promises_cancel_steps; eauto. intros PROMISES2. splits.
  { inv WRITE.
    { inv STEP; inv STEP0; inv LOCAL. ss.
      inv LOCAL0. inv WRITE.
      eapply promise_not_released_add in PROMISE; eauto; ss. des; auto. }
    { inv STEP; inv STEP0; inv LOCAL. ss.
      inv LOCAL1. inv LOCAL2. inv WRITE.
      eapply promise_not_released_add in PROMISE; eauto; ss. des; auto. }
    { inv STEP; inv STEP0; inv LOCAL. ss.
      inv LOCAL0. eapply write_na_not_released_add in WRITE; eauto; ss.
      des; subst; ss. eapply List.Forall_forall in NONBOTS; eauto; ss.
    }
  }
  { ii. ss. erewrite IdentMap.gso in TID1; eauto.
    hexploit Thread.rtc_all_step_disjoint.
    { eapply rtc_implies; try apply CANCELS.
      clear. i. inv H. econs. econs; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    i. des.
    hexploit thread_step_write_not_released; eauto. i. des.
    hexploit rtc_reserve_step_write_not_released; eauto. i. des. ss.
  }
Qed.

Lemma pf_racefree_view_pf_race_free_imm L c
      (WF: Configuration.wf c)
      (PF: PF.pf_configuration L c)
      (RACEFREE: PFRace.racefree_view L c)
  :
    PFRace.racefree L c.
Proof.
  ii. exploit PFConfiguration.rtc_all_step_future; eauto. i. des.
  exploit configuration_write_not_released; eauto. i. des.
  exploit PFConfiguration.step_future; try apply CSTEP0; eauto. i. des.
  exploit not_released_configuration_steps; eauto. i. des.
  { exploit not_released_configuration_step; try apply CSTEP1; eauto.
    { eapply PFConfiguration.rtc_all_step_future; try apply WF0; eauto.
      eapply rtc_implies; try apply STEPS.
      i. inv H. econs; eauto. }
    i. des; ss.
    eapply RACEFREE.
    { eauto. }
    { eapply CSTEPS. }
    { econs; eauto. }
    { eapply rtc_implies; try apply STEPS.
      i. inv H. econs; eauto. }
    { eauto. }
  }
  { eapply RACEFREE.
    { eauto. }
    { eapply CSTEPS. }
    { econs; eauto. }
    { eapply rtc_implies; try apply STEPS0.
      i. inv H. econs; eauto. }
    { eauto. }
  }
Qed.


Lemma local_drf_pf_view_after L c
        (WF: Configuration.wf c)
        (PF: PF.pf_configuration L c)
        (RACEFRFEE: PFRace.racefree_view L c)
  :
    behaviors SConfiguration.machine_step c <2=
    behaviors (PFConfiguration.machine_step L) c.
Proof.
  ii. eapply local_drf_pf_after; eauto.
  eapply pf_racefree_view_pf_race_free_imm; eauto.
Qed.


(* Happens-before based LDRF-PF theorem *)
Theorem local_drf_pf_view L
        s
        (RACEFRFEE: PFRace.racefree_view_syn L s):
  behaviors SConfiguration.machine_step (Configuration.init s) <2=
  behaviors (PFConfiguration.machine_step L) (Configuration.init s).
Proof.
  eapply local_drf_pf_view_after; eauto.
  - eapply Configuration.init_wf.
  - eapply PF.configuration_init_pf.
Qed.
