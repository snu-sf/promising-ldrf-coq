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
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import MemoryProps.
Require Import JoinedView.
Require Import JoinedViewExist.

Set Implicit Arguments.


Lemma read_tview_plain_cur
      tview loc to released ord
      (WF: TView.wf tview)
      (ORD: Ordering.le ord Ordering.plain)
      (CUR: Time.le to ((View.rlx (TView.cur tview)) loc)):
  TView.read_tview tview loc to released ord = tview.
Proof.
  unfold TView.read_tview. destruct tview. ss. f_equal.
  { condtac; try by destruct ord; ss.
    rewrite View.join_bot_r.
    apply View.antisym; try apply View.join_l.
    apply View.join_spec; try refl.
    unfold View.singleton_ur_if.
    condtac; try by destruct ord; ss.
    unfold View.singleton_rw.
    econs; try apply TimeMap.bot_spec. ss.
    ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
    condtac; try apply Time.bot_spec.
    subst. ss.
  }
  { condtac; try by destruct ord; ss.
    rewrite View.join_bot_r.
    apply View.antisym; try apply View.join_l.
    apply View.join_spec; try refl.
    unfold View.singleton_ur_if.
    unfold View.singleton_rw.
    econs; try apply TimeMap.bot_spec. ss.
    ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
    condtac; try apply Time.bot_spec.
    subst. etrans; eauto. apply WF.
  }
Qed.

Lemma read_step_plain_cur
      lc1 mem1 loc to val released ord lc2
      (WF: TView.wf (Local.tview lc1))
      (ORD: Ordering.le ord Ordering.plain)
      (CUR: Time.le to ((View.rlx (TView.cur (Local.tview lc1))) loc))
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
  lc2 = lc1.
Proof.
  destruct lc1. inv STEP; ss. f_equal.
  eapply read_tview_plain_cur; eauto.
Qed.

Lemma sim_local_read_na_aux
      views
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: JSim.sim_local views lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (ORD: Ordering.le ord_src ord_tgt)
      (NA: Ordering.le ord_src Ordering.na)
      (CONS: Local.promise_consistent lc2_tgt)
  :
    (exists released_src lc2_src,
        (<<REL: View.opt_le released_src released_tgt>>) /\
        (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
        (<<CUR: Time.le ts ((View.rlx (TView.cur (Local.tview lc1_src))) loc)>>)) \/
    (<<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc ts val ord_src>>).
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; eauto. i. des. inv MSG. ss.
  destruct (TimeFacts.le_lt_dec ts ((View.rlx (TView.cur vw_src)) loc)).
  { left. esplits.
    - eauto.
    - econs; eauto.
      { etrans; eauto. }
      eapply TViewFacts.readable_mon; try exact READABLE; eauto. apply TVIEW.
    - ss.
  }
  { right. econs. econs; try exact GET0; ss.
    - destruct (Memory.get loc ts prom_src) as [[]|] eqn:GETP; ss.
      inv WF1_SRC. ss.
      exploit PROMISES0; eauto. i.
      rewrite x in *. inv GET0.
      specialize (PROMISES loc ts).
      rewrite GETP in *. inv PROMISES. clear NIL.
      exploit CONS; eauto; ss. i.
      exfalso.
      eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt; try eapply x0.
      etrans; [|eapply Time.join_l].
      etrans; [|eapply Time.join_r].
      unfold View.singleton_ur_if. condtac; ss.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
    - unfold TView.racy_view.
      eapply TimeFacts.le_lt_lt; eauto. apply WF1_SRC.
    - destruct ord_src; ss.
  }
Qed.

Lemma sim_local_read_na
      views
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: JSim.sim_local views lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (ORD: Ordering.le ord_src ord_tgt)
      (NA: Ordering.le ord_src Ordering.na)
      (CONS: Local.promise_consistent lc2_tgt)
  :
    (<<LOCAL2: JSim.sim_local views lc1_src lc2_tgt>>) /\
    ((exists released_src lc2_src,
         (<<REL: View.opt_le released_src released_tgt>>) /\
         (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
         (<<LC: lc2_src = lc1_src>>)) \/
     (<<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc ts val ord_src>>)).
Proof.
  splits.
  { inv LOCAL1. inv STEP_TGT. econs; eauto. ss.
    etrans; eauto. eapply TViewFacts.read_tview_incr; eauto.
  }
  exploit sim_local_read_na_aux; eauto. i. des; eauto.
  exploit read_step_plain_cur;
    try exact STEP_SRC; try apply WF1_SRC; eauto. i. subst.
  left. esplits; eauto.
Qed.

Require Import DelayedStep.
Require Import NoMix.
Require Import gSimAux.

Section POINTABLE.
  Variable loc_na: Loc.t -> Prop.
  Section MESSAGES.

  Variable msgs: Messages.t.
  Hypothesis MSGSBOT: forall loc, msgs loc Time.bot Time.bot Message.elt.

  Definition pointable_timemap (tm: TimeMap.t): Prop :=
    forall loc (NA: loc_na loc),
    exists from val released, msgs loc (tm loc) from (Message.concrete val released).

  Lemma pointable_timemap_join tm0 tm1
        (TM0: pointable_timemap tm0)
        (TM1: pointable_timemap tm1)
    :
      pointable_timemap (TimeMap.join tm0 tm1).
  Proof.
    ii. unfold TimeMap.join, Time.join.  des_ifs.
    { eapply TM1; eauto. }
    { eapply TM0; eauto. }
  Qed.

  Lemma pointable_timemap_bot
    :
      pointable_timemap TimeMap.bot.
  Proof.
    ii. esplits. eapply MSGSBOT.
  Qed.

  Lemma pointable_timemap_singleton loc ts
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
    :
      pointable_timemap (TimeMap.singleton loc ts).
  Proof.
    ii. unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec. des_ifs.
    { eapply POINTED; eauto. }
    { esplits. rewrite LocFun.init_spec. eapply MSGSBOT. }
  Qed.

  Record pointable_view (vw: View.t): Prop :=
    { pointable_pln: pointable_timemap vw.(View.pln);
      pointable_rlx: pointable_timemap vw.(View.rlx);
    }.

  Lemma pointable_view_join vw0 vw1
        (VW0: pointable_view vw0)
        (VW1: pointable_view vw1)
    :
      pointable_view (View.join vw0 vw1).
  Proof.
    econs; ss.
    { eapply pointable_timemap_join; eauto.
      { eapply VW0. }
      { eapply VW1. }
    }
    { eapply pointable_timemap_join; eauto.
      { eapply VW0. }
      { eapply VW1. }
    }
  Qed.

  Lemma pointable_view_bot
    :
      pointable_view View.bot.
  Proof.
    econs.
    { eapply pointable_timemap_bot; eauto. }
    { eapply pointable_timemap_bot; eauto. }
  Qed.

  Lemma pointable_view_singleton_ur loc ts
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
    :
      pointable_view (View.singleton_ur loc ts).
  Proof.
    econs; ss.
    { eapply pointable_timemap_singleton; eauto. }
    { eapply pointable_timemap_singleton; eauto. }
  Qed.

  Lemma pointable_view_singleton_rw loc ts
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
    :
      pointable_view (View.singleton_rw loc ts).
  Proof.
    econs; ss.
    { eapply pointable_timemap_bot; eauto. }
    { eapply pointable_timemap_singleton; eauto. }
  Qed.

  Lemma pointable_view_singleton_ur_if loc ts cond
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
    :
      pointable_view (View.singleton_ur_if cond loc ts).
  Proof.
    destruct cond; ss.
    { eapply pointable_view_singleton_ur; eauto. }
    { eapply pointable_view_singleton_rw; eauto. }
  Qed.

  Variant pointable_opt_view: forall (vw: option View.t), Prop :=
  | pointable_opt_view_some
      vw
      (VW: pointable_view vw)
    :
      pointable_opt_view (Some vw)
  | pointable_opt_view_nond
    :
      pointable_opt_view None
  .

  Lemma pointable_unwrap vw
        (VW: pointable_opt_view vw)
    :
      pointable_view (View.unwrap vw).
  Proof.
    inv VW; auto. eapply pointable_view_bot; eauto.
  Qed.

  Record pointable_tview (tvw: TView.t): Prop :=
    { pointable_rel: forall loc, pointable_view (tvw.(TView.rel) loc);
      pointable_cur: pointable_view tvw.(TView.cur);
      pointable_acq: pointable_view tvw.(TView.acq);
    }.

  Lemma pointable_read_tview tvw loc ts released ord
        (TVW: pointable_tview tvw)
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
        (RELEASED: pointable_opt_view released)
    :
      pointable_tview (TView.read_tview tvw loc ts released ord).
  Proof.
    econs; ss.
    { i. eapply TVW. }
    { des_ifs.
      { eapply pointable_view_join; eauto.
        { eapply pointable_view_join.
          { eapply TVW. }
          { eapply pointable_view_singleton_ur_if; eauto. }
        }
        { eapply pointable_unwrap; eauto. }
      }
      { eapply pointable_view_join; eauto.
        { eapply pointable_view_join.
          { eapply TVW. }
          { eapply pointable_view_singleton_ur_if; eauto. }
        }
        { eapply pointable_view_bot; eauto. }
      }
    }
    { des_ifs.
      { eapply pointable_view_join; eauto.
        { eapply pointable_view_join.
          { eapply TVW. }
          { eapply pointable_view_singleton_ur_if; eauto. }
        }
        { eapply pointable_unwrap; eauto. }
      }
      { eapply pointable_view_join; eauto.
        { eapply pointable_view_join.
          { eapply TVW. }
          { eapply pointable_view_singleton_ur_if; eauto. }
        }
        { eapply pointable_view_bot; eauto. }
      }
    }
  Qed.

  Lemma pointable_write_tview tvw sc loc ts ord
        (TVW: pointable_tview tvw)
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
    :
      pointable_tview (TView.write_tview tvw sc loc ts ord).
  Proof.
    econs; ss.
    { i. setoid_rewrite LocFun.add_spec. des_ifs.
      { eapply pointable_view_join; eauto.
        { eapply TVW. }
        { eapply pointable_view_singleton_ur; eauto. }
      }
      { eapply pointable_view_join; eauto.
        { eapply TVW. }
        { eapply pointable_view_singleton_ur; eauto. }
      }
      { eapply TVW. }
    }
    { eapply pointable_view_join; eauto.
      { eapply TVW. }
      { eapply pointable_view_singleton_ur; eauto. }
    }
    { eapply pointable_view_join; eauto.
      { eapply TVW. }
      { eapply pointable_view_singleton_ur; eauto. }
    }
  Qed.

  Lemma pointable_read_fence_tview tvw ord
        (TVW: pointable_tview tvw)
    :
      pointable_tview (TView.read_fence_tview tvw ord).
  Proof.
    econs; ss.
    { i. eapply TVW. }
    { des_ifs.
      { eapply TVW. }
      { eapply TVW. }
    }
    { eapply TVW. }
  Qed.

  Lemma pointable_write_fence_sc tvw sc ord
        (TVW: pointable_tview tvw)
        (SC: pointable_timemap sc)
    :
      pointable_timemap (TView.write_fence_sc tvw sc ord).
  Proof.
    unfold TView.write_fence_sc. des_ifs.
    eapply pointable_timemap_join; eauto. eapply TVW.
  Qed.

  Lemma pointable_write_fence_tview tvw sc ord
        (TVW: pointable_tview tvw)
        (SC: pointable_timemap sc)
    :
      pointable_tview (TView.write_fence_tview tvw sc ord).
  Proof.
    econs; ss.
    { i. des_ifs; ss.
      { econs; eapply pointable_write_fence_sc; eauto. }
      { eapply TVW. }
      { eapply TVW. }
    }
    { des_ifs; ss.
      { econs; eapply pointable_write_fence_sc; eauto. }
      { eapply TVW. }
    }
    { des_ifs; ss.
      { eapply pointable_view_join.
        { eapply TVW. }
        { econs; eapply pointable_write_fence_sc; eauto. }
      }
      { eapply pointable_view_join.
        { eapply TVW. }
        { eapply pointable_view_bot. }
      }
    }
  Qed.

  Lemma pointable_write_released tvw sc loc ts releasedm ord
        (TVW: pointable_tview tvw)
        (POINTED: forall (NA: loc_na loc), exists from val released, msgs loc ts from (Message.concrete val released))
        (RELEASED: pointable_opt_view releasedm)
    :
      pointable_opt_view (TView.write_released tvw sc loc ts releasedm ord).
  Proof.
    unfold TView.write_released. des_if; econs.
    eapply pointable_view_join.
    { eapply pointable_unwrap; eauto. }
    { eapply pointable_write_tview; eauto. }
  Qed.

  Variant pointable_message: forall (msg: Message.t), Prop :=
  | pointable_concrete
      val released
      (RELEASED: pointable_opt_view released)
    :
      pointable_message (Message.concrete val released)
  | pointable_undef
    :
      pointable_message Message.undef
  | pointable_reserve
    :
      pointable_message Message.reserve
  .

  Definition pointable_memory (mem: Memory.t): Prop :=
    forall loc (AT: ~ loc_na loc) from to val released
           (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
      pointable_opt_view released.

  Lemma pointable_write prom0 mem0 loc from to msg prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
        (MEM: pointable_memory mem0)
        (MSG: forall (AT: ~ loc_na loc), pointable_message msg)
    :
      pointable_memory mem1.
  Proof.
    inv WRITE. inv PROMISE.
    { ii. erewrite Memory.add_o in GET; eauto. des_ifs.
      { ss. des; clarify. specialize (MSG AT). inv MSG. eauto. }
      { eapply MEM; eauto. }
    }
    { ii. erewrite Memory.split_o in GET; eauto. des_ifs.
      { ss. des; clarify. specialize (MSG AT). inv MSG. eauto. }
      { ss. des; clarify. eapply Memory.split_get0 in MEM0. des.
        eapply MEM; eauto.
      }
      { eapply MEM; eauto. }
    }
    { ii. erewrite Memory.lower_o in GET; eauto. des_ifs.
      { ss. des; clarify. specialize (MSG AT). inv MSG. eauto. }
      { eapply MEM; eauto. }
    }
    { ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
      eapply MEM; eauto.
    }
  Qed.

  Lemma pointable_write_na ts prom0 mem0 loc from to val prom1 mem1 msgs0 kinds kind
        (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs0 kinds kind)
        (MEM: pointable_memory mem0)
    :
      pointable_memory mem1.
  Proof.
    revert MEM. induction WRITE; i.
    { eapply pointable_write; eauto. econs; eauto. econs. }
    { eapply IHWRITE. eapply pointable_write; eauto.
      red in MSG_EX. des; clarify; econs; eauto. econs.
    }
  Qed.

  Definition pointable_views (views: Loc.t -> Time.t -> list View.t): Prop :=
    forall loc (AT: ~ loc_na loc) ts,
      List.Forall pointable_view (views loc ts).

  Lemma pointable_joined_view views released
        (JOINED: joined_view views released)
        (VIEWS: List.Forall pointable_view views)
    :
      pointable_view released.
  Proof.
    revert VIEWS. induction JOINED; i.
    { eapply pointable_view_bot; eauto. }
    { eapply pointable_view_join; eauto.
      eapply List.Forall_forall in VIEW; eauto.
    }
  Qed.

  Lemma pointable_joined_opt_view views released
        (JOINED: joined_opt_view views released)
        (VIEWS: List.Forall pointable_view views)
    :
      pointable_opt_view released.
  Proof.
    inv JOINED; econs. eapply pointable_joined_view; eauto.
  Qed.

  Lemma pointable_joined_memory views mem
        (JOINED: joined_memory views mem)
        (VIEWS: pointable_views views)
    :
    pointable_memory mem.
  Proof.
    ii. destruct released; econs. inv JOINED.
    exploit COMPLETE; eauto. i. des.
    eapply pointable_joined_view; eauto.
  Qed.

  Lemma pointable_views_incr tvw (views1 views2: Loc.t -> Time.t -> list View.t)
        (VIEWS: pointable_views views1)
        (TVIEW: pointable_tview tvw)
        (VIEWSLE: forall loc ts (NEQ: views2 loc ts <> views1 loc ts),
            (<<NIL: views1 loc ts = []>>) /\
            exists from,
              (<<VIEW: views2 loc ts = (View.join (tvw.(TView.rel) loc) (View.singleton_ur loc ts))
                                         ::(all_join_views (View.singleton_ur loc ts) (views1 loc from))>>))
    :
      pointable_views views2.
  Proof.
    ii. destruct (classic (views2 loc ts = views1 loc ts)).
    { rewrite H. eapply VIEWS; eauto. }
    { hexploit VIEWSLE; eauto. i. des. rewrite VIEW. econs.
      { eapply pointable_view_join.
        { eapply TVIEW. }
        { eapply pointable_view_singleton_ur; eauto. i. ss. }
      }
      { unfold all_join_views. eapply list_map_forall.
        { eapply VIEWS; eauto. }
        { i. eapply pointable_view_join; auto.
          eapply pointable_view_singleton_ur; eauto. i. ss.
        }
      }
    }
  Qed.
  End MESSAGES.

  Variable msgs0: Messages.t.
  Variable msgs1: Messages.t.
  Hypothesis MSGSMON: msgs0 <4= msgs1.

  Lemma pointable_timemap_mon tm
        (TM: pointable_timemap msgs0 tm)
    :
    pointable_timemap msgs1 tm.
  Proof.
    ii. exploit TM; eauto. i. des. esplits; eauto.
  Qed.

  Lemma pointable_view_mon vw
        (VW: pointable_view msgs0 vw)
    :
    pointable_view msgs1 vw.
  Proof.
    econs.
    { eapply pointable_timemap_mon; eapply VW. }
    { eapply pointable_timemap_mon; eapply VW. }
  Qed.

  Lemma pointable_opt_view_mon vw
        (VW: pointable_opt_view msgs0 vw)
    :
    pointable_opt_view msgs1 vw.
  Proof.
    inv VW; econs. eapply pointable_view_mon; eauto.
  Qed.

  Lemma pointable_tview_mon tvw
        (TVW: pointable_tview msgs0 tvw)
    :
    pointable_tview msgs1 tvw.
  Proof.
    inv TVW; econs; i; eapply pointable_view_mon; eauto.
  Qed.

  Lemma pointable_message_mon msg
        (MSG: pointable_message msgs0 msg)
    :
    pointable_message msgs1 msg.
  Proof.
    inv MSG; econs; eauto. eapply pointable_opt_view_mon; eauto.
  Qed.

  Lemma pointable_memory_mon mem
        (MEM: pointable_memory msgs0 mem)
    :
    pointable_memory msgs1 mem.
  Proof.
    ii. exploit MEM; eauto. i. eapply pointable_opt_view_mon; eauto.
  Qed.
End POINTABLE.

Require Import Pred.
Require Import Delayed.
Require Import Simple.

Section NA.
  Variable loc_na: Loc.t -> Prop.

  Lemma sim_thread_promise_step views0 lang_src lang_tgt fin
        th0_src th0_tgt th1_tgt pf_tgt e_tgt
        (STEP: Thread.step pf_tgt e_tgt th0_tgt th1_tgt)
        (ISPROMISE: is_promise e_tgt)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th0_src.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th0_src.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
    :
      exists e_src pf_src th1_src views1,
        (<<JSTEP: JThread.step pf_src e_src th0_src th1_src views0 views1>>) /\
        (<<ISPROMISE: is_promise e_src>>) /\
        (<<SIM: JSim.sim_thread views1 th1_src th1_tgt>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th1_src.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na fin th1_src.(Thread.local).(Local.tview)>>)
  .
  Proof.
    dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP; inv STEP0; [|inv LOCAL; inv LOCAL0; ss].
    hexploit JSim.sim_local_promise; eauto. i. des. esplits.
    { econs. econs 1; eauto.
      { econs; eauto. }
      { i. instantiate (1:=views2). clarify. eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { ss. }
    { econs; eauto. }
    { ss. }
    { auto. }
    { inv STEP_SRC; auto. }
  Qed.

  Lemma sim_thread_release_step views0 lang_src lang_tgt fin
        th0_src th0_tgt th1_tgt pf_tgt e_tgt
        (STEP: Thread.step pf_tgt e_tgt th0_tgt th1_tgt)
        (ISRELEASE: release_event e_tgt)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th0_src.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th0_src.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (AT: forall l c
                    (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e_tgt) = true)
                    (ACCESS: is_accessing (ThreadEvent.get_program_event e_tgt) = Some (l, c)),
            ~ loc_na l)
    :
      (<<FAILURE: Thread.steps_failure th0_src>>) \/
      exists e_src pf_src th1_src views1,
        (<<JSTEP: JThread.step pf_src e_src th0_src th1_src views0 views1>>) /\
        (<<ISRELEASE: release_event e_src>>) /\
        (<<SIM: JSim.sim_thread views1 th1_src th1_tgt>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th1_src.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na fin th1_src.(Thread.local).(Local.tview)>>)
  .
  Proof.
    destruct (classic (Thread.steps_failure th0_src)) as [FAILURE|NFAILURE]; auto.
    right. dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    hexploit PromiseConsistent.step_promise_consistent; eauto. intros CONSISTENT0.
    hexploit pointable_joined_memory; eauto. intros POINTMEM.
    inv STEP; inv STEP0; ss. inv LOCAL0; ss.
    (* write *)
    { revert ISRELEASE. hexploit JSim.sim_local_write; eauto.
      { econs. }
      { refl. } i. des.
      exists (ThreadEvent.write loc from to val released_src ord). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { eapply VIEWSLE. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { econs; eauto; refl. }
      { ss. }
      { ss. inv STEP_SRC. ss. }
      { ss. inv STEP_SRC. ss.
        hexploit AT.
        { destruct ord; ss. }
        { eauto. }
        i. eapply pointable_write_tview; eauto. i. ss.
      }
    }
    (* update *)
    { hexploit JSim.sim_local_read; eauto.
      { refl. } i. des.
      hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
      hexploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
      revert ISRELEASE. hexploit JSim.sim_local_write; eauto.
      { refl. } i. des.
      exists (ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { eapply VIEWSLE. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { eauto. }
      { ss. }
      { ss. inv STEP_SRC. inv STEP_SRC0. ss. }
      { ss. inv STEP_SRC. inv STEP_SRC0. ss.
        hexploit AT.
        { destruct (Ordering.le Ordering.plain ordr) eqn:ORDR; ss.
          { destruct ordw; ss. }
          exfalso. eapply NFAILURE. repeat red. esplits.
          { refl. }
          { econs 2. econs.
            { instantiate (2:=ThreadEvent.racy_update _ _ _ _ _ _). eauto. }
            econs. econs 1.
            { destruct ordr; ss. }
            { eapply JSim.sim_local_promise_consistent; eauto. }
          }
          { ss. }
        }
        { eauto. }
        i. eapply pointable_write_tview; eauto; ss.
        eapply pointable_read_tview; eauto; ss.
      }
    }
    (* fence *)
    { revert ISRELEASE.
      hexploit JSim.sim_local_fence; try eassumption.
      { refl. }
      { refl. }
      i. des.
      exists (ThreadEvent.fence ordr ordw). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { ss. }
      { ss. }
      { ss. inv STEP_SRC. ss.
        eapply pointable_write_fence_sc; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
      { ss. inv STEP_SRC. ss.
        eapply pointable_write_fence_tview; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
    }
    (* syscall *)
    { revert ISRELEASE.
      hexploit JSim.sim_local_fence; try eassumption.
      { refl. }
      { refl. }
      i. des.
      exists (ThreadEvent.syscall e). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { ss. }
      { ss. }
      { ss. inv STEP_SRC. ss.
        eapply pointable_write_fence_sc; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
      { ss. inv STEP_SRC. ss.
        eapply pointable_write_fence_tview; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
    }
    (* failure *)
    { hexploit JSim.sim_local_failure; eauto. i. des.
      exists (ThreadEvent.failure). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
    }
    (* racy write *)
    { hexploit JSim.sim_local_racy_write; eauto.
      { refl. }
      i. eexists (ThreadEvent.racy_write _ _ _ _). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
    }
    (* racy update *)
    { hexploit JSim.sim_local_racy_update; eauto.
      { refl. }
      { refl. }
      i. eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
      { ss. }
    }
  Qed.

  Lemma sim_thread_lower_step views0 lang_src lang_tgt fin
        th0_src th0_tgt th1_tgt e_tgt
        (STEP: lower_step e_tgt th0_tgt th1_tgt)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th0_src.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th0_src.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (AT: forall l c
                    (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e_tgt) = true)
                    (ACCESS: is_accessing (ThreadEvent.get_program_event e_tgt) = Some (l, c)),
            ~ loc_na l)
    :
      exists e_src pf_src th1_src views1,
        (<<JSTEP: JThread.step pf_src e_src th0_src th1_src views0 views1>>) /\
        (<<STEP: lower_step e_src th0_src th1_src>>) /\
        (<<SIM: JSim.sim_thread views1 th1_src th1_tgt>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th1_src.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na fin th1_src.(Thread.local).(Local.tview)>>)
  .
  Proof.
    TODO`

    dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP. inv STEP0. inv LOCAL0; ss.
    - inv STEP0.
      hexploit sim_local_promise; eauto. i. des. esplits.
      + econs.
        * econs. econs 1; eauto.
        * i. instantiate (1:=views2). clarify. eauto.
        * eauto.
        * eauto.
        * eauto.
        * ss.
      + ss.
      + eauto.
    - inv STEP0. inv LOCAL0.
      + esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_read; eauto.
        { refl. } i. des.
        exists (ThreadEvent.read loc ts val released_src ord). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * eauto.

      + hexploit sim_local_write; eauto.
        { econs. }
        { refl. } i. des.
        exists (ThreadEvent.write loc from to val released_src ord). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { eapply VIEWSLE. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * econs; eauto; refl.

      + hexploit sim_local_read; eauto.
        { refl. } i. des.
        hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
        hexploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
        hexploit sim_local_write; eauto.
        { refl. } i. des.
        exists (ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { eapply VIEWSLE. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * eauto.

      + hexploit sim_local_fence; eauto.
        { refl. }
        { refl. } i. des.
        exists (ThreadEvent.fence ordr ordw). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_fence; eauto.
        { refl. }
        { refl. } i. des.
        exists (ThreadEvent.syscall e). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_failure; eauto.  i. des.
        exists (ThreadEvent.failure). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_write_na_step; eauto.
        { refl. }
        i. des.
        eexists (ThreadEvent.write_na _ _ _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * econs.

      + hexploit sim_local_racy_read; eauto.
        { refl. }
        i. eexists (ThreadEvent.racy_read _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_racy_write; eauto.
        { refl. }
        i. eexists (ThreadEvent.racy_write _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_racy_update; eauto.
        { refl. }
        { refl. }
        i. eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

  Qed.
End NA.
