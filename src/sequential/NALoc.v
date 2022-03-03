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

  Lemma pointable_views_mon views
        (VW: pointable_views msgs0 views)
    :
    pointable_views msgs1 views.
  Proof.
    ii. eapply List.Forall_impl; [|eapply VW]; eauto.
    eapply pointable_view_mon; eauto.
  Qed.
End POINTABLE.

Require Import Pred.
Require Import Delayed.
Require Import Simple.

Section NA.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Lemma sim_thread_promise_step views0 lang_src lang_tgt fin
        th_src0 th_tgt0 th_tgt1 pf_tgt e_tgt
        (STEP: Thread.step pf_tgt e_tgt th_tgt0 th_tgt1)
        (ISPROMISE: is_promise e_tgt)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
    :
      exists e_src pf_src th_src1 views1,
        (<<JSTEP: JThread.step pf_src e_src th_src0 th_src1 views0 views1>>) /\
        (<<ISPROMISE: is_promise e_src>>) /\
        (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th_src1.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na fin th_src1.(Thread.local).(Local.tview)>>)
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
        th_src0 th_tgt0 th_tgt1 pf_tgt e_tgt
        (STEP: Thread.step pf_tgt e_tgt th_tgt0 th_tgt1)
        (ISRELEASE: release_event e_tgt)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (AT: forall l c
                    (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e_tgt) = true)
                    (ACCESS: is_accessing (ThreadEvent.get_program_event e_tgt) = Some (l, c)),
            ~ loc_na l)
    :
      (exists e_src th_src1,
          (<<FAILURE: Thread.step true e_src th_src0 th_src1>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)) \/
      exists e_src pf_src th_src1 views1,
        (<<JSTEP: JThread.step pf_src e_src th_src0 th_src1 views0 views1>>) /\
        (<<ISRELEASE: release_event e_src>>) /\
        (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th_src1.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na fin th_src1.(Thread.local).(Local.tview)>>)
  .
  Proof.
    destruct (classic (exists e_src th_src1,
                          (<<FAILURE: Thread.step true e_src th_src0 th_src1>>) /\
                          (<<EVENT: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>))) as [FAILURE|NFAILURE]; auto.
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
    { destruct (classic (loc_na loc)) as [LOC|LOC].
      { exfalso.
        destruct (Ordering.le Ordering.plain ordr && Ordering.le Ordering.plain ordw) eqn:ORDNA.
        { eapply AT; auto. }
        eapply NFAILURE. esplits.
        { econs 2. econs.
          { instantiate (2:=ThreadEvent.racy_update _ Time.bot _ _ _ _). eauto. }
          econs.
          { eapply andb_false_elim in ORDNA. inv ORDNA.
            { destruct ordr; ss. econs 1; eauto.
              eapply JSim.sim_local_promise_consistent; eauto. }
            { destruct ordw; ss. }
          }
        }
        { ss. }
      }
      hexploit JSim.sim_local_read; eauto.
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
        eapply pointable_write_tview; eauto; ss.
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

  Lemma write_committed prom0 mem0 loc from to msg prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
    :
    committed mem0 prom0 mem1 prom1 loc to from msg.
  Proof.
    hexploit Memory.write_get2; eauto. i. des.
    econs.
    { econs; eauto. }
    { ii. inv H. inv WRITE. inv PROMISE.
      { eapply Memory.add_get0 in MEM. des; clarify. }
      { eapply Memory.split_get0 in MEM. des; clarify. }
      { eapply Memory.lower_get0 in MEM. eapply Memory.lower_get0 in PROMISES.
        des; clarify.
      }
      { eapply Memory.remove_get0 in MEM. des; clarify. }
    }
  Qed.

  Lemma write_na_committed ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind
        (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
    :
    committed mem0 prom0 mem1 prom1 loc to from (Message.concrete val None).
  Proof.
    induction WRITE.
    { eapply write_committed; eauto. }
    { inv IHWRITE. econs; eauto.
      ii. eapply NUNCHANGABLE. eapply unchangable_write in WRITE_EX; eauto.
    }
  Qed.

  Lemma list_Forall2_impl_strong A B (P Q: A -> B -> Prop) (la: list A) (lb: list B)
        (FORALL: List.Forall2 P la lb)
        (IMPL: forall a b (INA: List.In a la) (INB: List.In b lb) (SAT: P a b),
            Q a b)
    :
    List.Forall2 Q la lb.
  Proof.
    revert IMPL. induction FORALL; ss; i. econs; eauto.
  Qed.

  Lemma write_na_messages_wf ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind
        (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
    :
    List.Forall (fun '(_, _, msg) => msg = Message.undef \/ exists val, msg = Message.concrete val None) msgs.
  Proof.
    induction WRITE; i; econs; eauto.
  Qed.

  Lemma sim_thread_lower_step views0 lang_src lang_tgt fin
        th_src0 th_tgt0 th_tgt1 e_tgt
        (STEP: lower_step e_tgt th_tgt0 th_tgt1)
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (AT: forall l c
                    (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e_tgt) = true)
                    (ACCESS: is_accessing (ThreadEvent.get_program_event e_tgt) = Some (l, c)),
            ~ loc_na l)
    :
      (exists e_src th_src1,
          (<<FAILURE: Thread.step true e_src th_src0 th_src1>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)) \/
      exists e_src pf_src th_src1 views1,
        (<<JSTEP: JThread.step pf_src e_src th_src0 th_src1 views0 views1>>) /\
        (<<STEP: lower_step e_src th_src0 th_src1>>) /\
        (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<POINTSC: pointable_timemap loc_na fin th_src1.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>)
  .
  Proof.
    destruct (classic (exists e_src th_src1,
                          (<<FAILURE: Thread.step true e_src th_src0 th_src1>>) /\
                          (<<EVENT: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>))) as [FAILURE|NFAILURE]; auto.
    right. dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP; ss.
    hexploit PromiseConsistent.step_promise_consistent; eauto. intros CONSISTENT0.
    hexploit pointable_joined_memory; eauto. intros POINTMEM.
    inv STEP0; ss. inv LOCAL0; ss.
    (* silent *)
    { eexists (ThreadEvent.silent). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { econs; eauto. ss. refl. }
      { ss. }
      { ss. }
      { ss. }
      { rewrite committed_same. auto. }
    }
    (* read *)
    { destruct (classic (loc_na loc)) as [LOC|LOC].
      { hexploit sim_local_read_na; eauto.
        { refl. }
        { apply NNPP. ii. eapply AT.
          { destruct ord; ss. }
          { eauto. }
          { auto. }
        }
        i. des; subst.
        { exists (ThreadEvent.read loc ts val released_src ord). esplits.
          { econs.
            { econs 2; eauto. }
            { ss. }
            { ss. }
            { ss. }
            { ss. }
            { ss. }
          }
          { econs; eauto. ss. refl. }
          { ss. }
          { ss. }
          { ss. }
          { rewrite committed_same. auto. }
        }
        { exists (ThreadEvent.racy_read loc ts val ord). esplits.
          { econs.
            { econs 2; eauto. }
            { ss. }
            { ss. }
            { ss. }
            { ss. }
            { ss. }
          }
          { econs; eauto. ss. refl. }
          { ss. }
          { ss. }
          { ss. }
          { rewrite committed_same. auto. }
        }
      }
      hexploit JSim.sim_local_read; eauto.
      { refl. } i. des.
      exists (ThreadEvent.read loc ts val released_src ord). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { econs; eauto. ss. refl. }
      { ss. }
      { ss. }
      { ss. }
      { inv STEP_SRC. ss. rewrite committed_same; eauto.
        eapply pointable_read_tview; eauto. i. ss.
      }
    }
    (* write *)
    { hexploit JSim.sim_local_write; eauto.
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
      { econs; eauto; ss.
        { inv LOCAL1. inv STEP_SRC. ss.
          eapply write_lower_memory_lower in WRITE; eauto.
          eapply write_lower_lower_memory; eauto.
          inv KIND; ss.
        }
        { inv LOCAL1. inv STEP_SRC. ss.
          i. hexploit SAME; auto. i. subst.
          eapply write_same_memory_same in WRITE; eauto.
          eapply write_lower_lower_memory_same in WRITE0; eauto.
          inv KIND; ss. subst.
          assert ((<<SRC: TView.write_released (Local.tview lc_src) sc_src loc to None ord = None>>) /\ (<<TGT: TView.write_released (Local.tview lc_tgt) sc_tgt loc to None ord = None>>)).
          { destruct ord; ss. }
          des. rewrite SRC. rewrite TGT in OPT0.
          symmetry. eapply OPT0; auto.
        }
      }
      { ss. }
      { ss. }
      { inv STEP_SRC; ss. }
      { inv STEP_SRC. ss.
        eapply pointable_write_tview.
        { left. eauto. }
        { eapply pointable_tview_mon; [|eauto]. i. auto. }
        { i. esplits. right. eapply write_committed; eauto. }
      }
    }
    (* update *)
    { destruct (classic (loc_na loc)) as [LOC|LOC].
      { exfalso.
        destruct (Ordering.le Ordering.plain ordr && Ordering.le Ordering.plain ordw) eqn:ORDNA.
        { eapply AT; auto. }
        eapply NFAILURE. esplits.
        { econs 2. econs.
          { instantiate (2:=ThreadEvent.racy_update _ Time.bot _ _ _ _). eauto. }
          econs.
          { eapply andb_false_elim in ORDNA. inv ORDNA.
            { destruct ordr; ss. econs 1; eauto.
              eapply JSim.sim_local_promise_consistent; eauto. }
            { destruct ordw; ss. econs 2; eauto.
              eapply JSim.sim_local_promise_consistent; eauto. }
          }
        }
        { ss. }
      }
      hexploit JSim.sim_local_read; eauto.
      { refl. } i. des.
      hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
      hexploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
      hexploit JSim.sim_local_write; eauto.
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
      { econs; eauto; ss.
        { inv LOCAL2. inv STEP_SRC0. ss.
          eapply write_lower_memory_lower in WRITE; eauto.
          eapply write_lower_lower_memory; eauto.
          inv KIND; ss.
        }
      }
      { ss. }
      { ss. }
      { ss. inv STEP_SRC. inv STEP_SRC0. ss. }
      { ss. inv STEP_SRC. inv STEP_SRC0. ss.
        eapply pointable_tview_mon.
        { i. left. eapply PR. }
        eapply pointable_write_tview; eauto; ss.
        eapply pointable_read_tview; eauto; ss.
      }
    }
    (* fence *)
    { hexploit JSim.sim_local_fence; try eassumption.
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
      { econs; eauto. ss. refl. }
      { ss. }
      { ss. }
      { ss. inv STEP_SRC. ss.
        eapply pointable_write_fence_sc; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
      { ss. inv STEP_SRC. ss. rewrite committed_same.
        eapply pointable_write_fence_tview; eauto.
        eapply pointable_read_fence_tview; eauto.
      }
    }
    (* write na *)
    { hexploit JSim.sim_local_write_na_step; eauto.
      { refl. } i. des.
      exists (ThreadEvent.write_na loc msgs from to val ord). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { dup STEP_SRC. inv STEP_SRC. inv LOCAL1.
        hexploit SAME; auto. i. subst.
        hexploit write_na_lower_memory_lower; eauto. i. des.
        hexploit write_na_lower_lower_memory.
        { eapply WRITE. }
        { eapply list_Forall2_compose.
          { eauto. }
          { instantiate (1:=fun kind '(_, _, msg) => is_lower_kind kind msg /\
                                                       __guard__(msg = Message.undef \/
                                                                   (exists val0, msg = Message.concrete val0 None))).
            eapply list_Forall2_impl_strong; eauto.
            i. ss. eapply write_na_messages_wf in WRITE0.
            eapply List.Forall_forall in INB; eauto.
            destruct b as [[from0 to0] msg0]. auto.
          }
          i. destruct c as [[from0 to0] msg0]. des.
          inv SAT0; ss. subst. des.
          red in SAT2. des; subst.
          { inv MSG. auto. }
          { symmetry. eapply OPT; eauto. }
        }
        { inv KIND; ss. symmetry. eapply OPT; ss. }
        i. subst. econs; eauto.
        { refl. }
      }
      { ss. }
      { ss. }
      { inv STEP_SRC; ss. }
      { inv STEP_SRC. ss.
        eapply pointable_write_tview.
        { left. eauto. }
        { eapply pointable_tview_mon; [|eauto]. i. auto. }
        { i. esplits. right. eapply write_na_committed; eauto. }
      }
    }
    (* racy read *)
    { hexploit JSim.sim_local_racy_read; eauto.
      { refl. } i. des.
      exists (ThreadEvent.racy_read loc to val ord). esplits.
      { econs.
        { econs 2; eauto. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
        { ss. }
      }
      { econs; eauto. ss. refl. }
      { ss. }
      { ss. }
      { ss. }
      { rewrite committed_same; eauto. }
    }
  Qed.

  Lemma sim_thread_promise_steps lang_src lang_tgt
        th_tgt0 th_tgt1
        (STEPS: rtc (tau (@pred_step is_promise _)) th_tgt0 th_tgt1)
    :
      forall
        fin th_src0 views0
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt0.(Thread.state)),
      exists th_src1 views1,
        (<<STEPS_SRC: rtc (tau (@pred_step is_promise _)) th_src0 th_src1>>) /\
        (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
        (<<POINTSC: pointable_timemap loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.sc)>>) /\
        (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>) /\
        (<<POINTVIEWS: pointable_views loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) views1>>) /\
        (<<JOINED: joined_memory views1 (Thread.memory th_src1)>>) /\
        (<<RELEASED: joined_released views1 th_src1.(Thread.local).(Local.promises) th_src1.(Thread.local).(Local.tview).(TView.rel)>>) /\
        (<<VIEWS: wf_views views1>>) /\
        (<<VIEWSLE: views_le views0 views1>>) /\
        (<<NOMIX: nomix loc_na loc_at _ th_tgt1.(Thread.state)>>)
  .
  Proof.
    induction STEPS; i.
    { esplits; eauto.
      { eapply pointable_timemap_mon; [|eauto]. auto. }
      { eapply pointable_tview_mon; [|eauto]. auto. }
      { eapply pointable_views_mon; [|eauto]. auto. }
      { refl. }
    }
    inv H. inv TSTEP. inv STEP.
    hexploit Thread.step_future; eauto. i. des.
    hexploit PromiseConsistent.rtc_all_step_promise_consistent.
    { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP. econs; eauto. }
    all: eauto. intros CONSISTENT1.
    hexploit sim_thread_promise_step; eauto. i. des.
    hexploit JThread.step_future; eauto. i. des.
    inv JSTEP. hexploit (IHSTEPS (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises)))); eauto.
    { eapply pointable_timemap_mon; [|eauto]. auto. }
    { eapply pointable_tview_mon; [|eauto]. auto. }
    { eapply pointable_views_mon.
      { i. left. eapply PR. }
      eapply pointable_views_incr; eauto.
      i. hexploit VIEWSLE; eauto. i.  des. esplits; eauto. }
    { inv STEP0; inv STEP1; ss. inv LOCAL; ss. }
    i. des.
    hexploit committed_trans.
    { econs 2; [|refl]. econs. econs. eapply STEP. }
    { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP. econs; eauto. }
    intros COMMITTED. esplits.
    { econs 2; [|eauto]. econs.
      { econs; eauto. econs; eauto. }
      { rewrite EVENT0. auto. }
    }
    { eauto. }
    { rewrite COMMITTED. eapply pointable_timemap_mon; [|eauto]. i. ss. des; auto. }
    { rewrite COMMITTED. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
    { rewrite COMMITTED. eapply pointable_views_mon; [|eauto]. i. ss. des; auto. }
    { auto. }
    { auto. }
    { auto. }
    { etrans; eauto. }
    { auto. }
  Qed.

  Lemma sim_thread_lower_steps lang_src lang_tgt
        th_tgt0 th_tgt1
        (STEPS: rtc (tau (@lower_step _)) th_tgt0 th_tgt1)
    :
      forall
        fin th_src0 views0
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt0.(Thread.state)),
        (exists e_src th_src1 th_src2,
            (<<STEPS: rtc (tau lower_step) th_src0 th_src1>>) /\
            (<<FAILURE: Thread.step true e_src th_src1 th_src2>>) /\
            (<<EVENT: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)) \/
        (exists th_src1 views1,
            (<<STEPS_SRC: rtc (tau (@lower_step _)) th_src0 th_src1>>) /\
            (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
            (<<POINTSC: pointable_timemap loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.sc)>>) /\
            (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>) /\
            (<<POINTVIEWS: pointable_views loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) views1>>) /\
            (<<JOINED: joined_memory views1 (Thread.memory th_src1)>>) /\
            (<<RELEASED: joined_released views1 th_src1.(Thread.local).(Local.promises) th_src1.(Thread.local).(Local.tview).(TView.rel)>>) /\
            (<<VIEWS: wf_views views1>>) /\
            (<<VIEWSLE: views_le views0 views1>>) /\
            (<<NOMIX: nomix loc_na loc_at _ th_tgt1.(Thread.state)>>))
  .
  Proof.
    induction STEPS; i.
    { right. esplits; eauto.
      { eapply pointable_timemap_mon; [|eauto]. auto. }
      { eapply pointable_tview_mon; [|eauto]. auto. }
      { eapply pointable_views_mon; [|eauto]. auto. }
      { refl. }
    }
    inv H. hexploit Thread.step_future.
    { inv TSTEP. econs 2; eauto. }
    all: eauto. i. des.
    hexploit PromiseConsistent.rtc_all_step_promise_consistent.
    { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP0. econs; eauto. econs; eauto. }
    all: eauto. intros CONSISTENT1.
    punfold NOMIX. exploit NOMIX.
    { instantiate (2:=ThreadEvent.get_program_event e). instantiate (1:=y.(Thread.state)). inv TSTEP. inv STEP. eauto. }
    i. des. inv CONT; ss.
    hexploit sim_thread_lower_step; eauto. i. des.
    { left. esplits.
      { refl. }
      { eauto. }
      { eauto. }
    }
    hexploit JThread.step_future; eauto. i. des.
    inv JSTEP. hexploit (IHSTEPS (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises)))); eauto.
    { eapply pointable_timemap_mon; [|eauto]. auto. }
    { eapply pointable_views_incr.
      { eauto. }
      { eapply pointable_views_mon.
        { i. left. eapply PR. }
        { eauto. }
      }
      { eauto. }
      i. hexploit VIEWSLE; eauto. i. des. esplits; eauto.
    }
    i. des.
    { left. esplits.
      { econs 2; [|eauto]. econs; eauto. inv STEP. destruct e_src; ss. }
      { eauto. }
      { eauto. }
    }
    right.
    hexploit committed_trans.
    { inv STEP. econs 2; [|refl]. econs. econs. econs 2; eauto. }
    { eapply rtc_implies; [|eauto]. i. inv H0. inv TSTEP0. econs; eauto. econs; eauto. }
    intros COMMITTED. esplits.
    { econs 2; [|eauto]. econs.
      { eauto. }
      { rewrite EVENT0. auto. }
    }
    { eauto. }
    { rewrite COMMITTED. eapply pointable_timemap_mon; [|eauto]. i. ss. des; auto. }
    { rewrite COMMITTED. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
    { rewrite COMMITTED. eapply pointable_views_mon; [|eauto]. i. ss. des; auto. }
    { auto. }
    { auto. }
    { auto. }
    { etrans; eauto. }
    { auto. }
  Qed.

  Lemma sim_thread_dstep lang_src lang_tgt
        th_tgt0 th_tgt1 e_tgt
        (STEPS: dstep e_tgt th_tgt0 th_tgt1)
        fin th_src0 views0
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt0.(Thread.state))
    :
      (exists th_src1 e_src,
          (<<STEPS_SRC: dstep e_src th_src0 th_src1>>) /\
          (<<FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)) \/
      (exists th_src1 views1 e_src,
          (<<STEPS_SRC: dstep e_src th_src0 th_src1>>) /\
          (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
          (<<POINTSC: pointable_timemap loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.sc)>>) /\
          (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>) /\
          (<<POINTVIEWS: pointable_views loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) views1>>) /\
          (<<JOINED: joined_memory views1 (Thread.memory th_src1)>>) /\
          (<<RELEASED: joined_released views1 th_src1.(Thread.local).(Local.promises) th_src1.(Thread.local).(Local.tview).(TView.rel)>>) /\
          (<<VIEWS: wf_views views1>>) /\
          (<<VIEWSLE: views_le views0 views1>>) /\
          (<<NOMIX: nomix loc_na loc_at _ th_tgt1.(Thread.state)>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>))
  .
  Proof.
    inv STEPS.
    hexploit rtc_implies; [|eapply PROMISES|..].
    { instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. }
    intros PROMISES_TGT.
    hexploit rtc_implies; [|eapply LOWERS|..].
    { instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. econs; eauto. }
    intros LOWERS_TGT.
    hexploit Thread.rtc_tau_step_future; [eapply PROMISES_TGT|..]; eauto. i. des.
    hexploit Thread.rtc_tau_step_future; [eapply LOWERS_TGT|..]; eauto. i. des.
    hexploit PromiseConsistent.step_promise_consistent; [eapply STEP_RELEASE|..]; eauto.
    intros CONSISTENT2.
    hexploit PromiseConsistent.rtc_tau_step_promise_consistent; [eapply LOWERS_TGT|..]; eauto.
    intros CONSISTENT1.
    hexploit sim_thread_promise_steps; eauto. i. des.
    hexploit rtc_implies; [|eapply STEPS_SRC|..].
    { instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. }
    intros PROMISES_SRC.
    hexploit Thread.rtc_tau_step_future; [eapply PROMISES_SRC|..]; eauto. i. des.
    hexploit sim_thread_lower_steps; eauto.
    { i. left. auto. }
    i. des.
    { left. esplits.
      { econs; eauto. destruct e_src; ss. }
      { auto. }
    }
    hexploit rtc_implies; [|eapply STEPS_SRC0|..].
    { instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. econs; eauto. }
    intros LOWERS_SRC.
    hexploit Thread.rtc_tau_step_future; [eapply LOWERS_SRC|..]; eauto. i. des.
    punfold NOMIX1. exploit NOMIX1.
    { instantiate (2:=ThreadEvent.get_program_event e_tgt). instantiate (1:=th_tgt1.(Thread.state)).
      inv STEP_RELEASE; inv STEP; ss.
    }
    i. des. inv CONT; ss.
    hexploit sim_thread_release_step; eauto.
    { i. left. auto. }
    i. des.
    { left. esplits.
      { econs; eauto. destruct e_src; ss. }
      { auto. }
    }
    hexploit JThread.step_future; eauto. i. des.
    inv JSTEP.
    hexploit committed_trans.
    { eapply rtc_implies; [|eapply PROMISES_SRC]. i. inv H0. econs; eauto. }
    { eapply rtc_implies; [|eapply LOWERS_SRC]. i. inv H0. econs; eauto. }
    intros SAME0.
    hexploit committed_trans.
    { etrans.
      { eapply rtc_implies; [|eapply PROMISES_SRC]. i. inv H0. econs; eauto. }
      { eapply rtc_implies; [|eapply LOWERS_SRC]. i. inv H0. econs; eauto. }
    }
    { econs 2; [|refl]. econs. econs. eapply STEP. }
    intros SAME1. right. esplits.
    { econs; eauto. }
    { eauto. }
    { rewrite SAME1. rewrite SAME0. eapply pointable_timemap_mon; [|eauto].
      i. ss. des; auto.
    }
    { rewrite SAME1. rewrite SAME0. eapply pointable_tview_mon; [|eauto].
      i. ss. des; auto.
    }
    { eapply pointable_views_incr.
      { eauto. }
      { instantiate (1:=views2). rewrite SAME1. rewrite SAME0.
        eapply pointable_views_mon; [|eauto]. i. ss. des; auto.
      }
      { rewrite SAME1. rewrite SAME0. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
      { i. hexploit VIEWSLE1; eauto. i. des; eauto. }
    }
    { eauto. }
    { eauto. }
    { eauto. }
    { etrans; eauto. etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_rtc_tau_dstep lang_src lang_tgt
        th_tgt0 th_tgt1
        (STEPS: rtc (tau (@dstep _)) th_tgt0 th_tgt1)
    :
      forall
        fin th_src0 views0
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt0.(Thread.state)),
        (exists th_src1,
            (<<STEPS_SRC: dsteps MachineEvent.failure th_src0 th_src1>>)) \/
        (exists th_src1 views1,
            (<<STEPS_SRC: rtc (tau (@dstep _)) th_src0 th_src1>>) /\
            (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
            (<<POINTSC: pointable_timemap loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.sc)>>) /\
            (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>) /\
            (<<POINTVIEWS: pointable_views loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) views1>>) /\
            (<<JOINED: joined_memory views1 (Thread.memory th_src1)>>) /\
            (<<RELEASED: joined_released views1 th_src1.(Thread.local).(Local.promises) th_src1.(Thread.local).(Local.tview).(TView.rel)>>) /\
            (<<VIEWS: wf_views views1>>) /\
            (<<VIEWSLE: views_le views0 views1>>) /\
            (<<NOMIX: nomix loc_na loc_at _ th_tgt1.(Thread.state)>>))
  .
  Proof.
    induction STEPS; i.
    { right. esplits.
      { refl. }
      { eauto. }
      { rewrite committed_same. auto. }
      { rewrite committed_same. auto. }
      { rewrite committed_same. auto. }
      { auto. }
      { auto. }
      { auto. }
      { refl. }
      { auto. }
    }
    inv H. pose proof (dstep_rtc_all_step TSTEP) as STEPS_TGT0.
    pose proof (rtc_dstep_rtc_tau_step STEPS) as STEPS_TGT1.
    hexploit Thread.rtc_all_step_future; [eapply STEPS_TGT0|..]; eauto. i. des.
    hexploit PromiseConsistent.rtc_tau_step_promise_consistent; [eapply STEPS_TGT1|..]; eauto. intros CONSISTENT1.
    hexploit sim_thread_dstep; eauto. i. des.
    { left. esplits. econs 2.
      { refl. }
      { eauto. }
      { auto. }
    }
    pose proof (dstep_rtc_all_step STEPS_SRC) as STEPS_SRC0.
    hexploit Thread.rtc_all_step_future; [eapply STEPS_SRC0|..]; eauto. i. des.
    hexploit IHSTEPS; eauto.
    { ss. i. left. auto. }
    i. des.
    { left. clear - STEPS_SRC1 STEPS_SRC EVENT EVENT0. inv STEPS_SRC1.
      esplits. econs.
      { econs 2; [|eapply DSTEPS]. econs; eauto. rewrite EVENT0. auto. }
      { eauto. }
      { eauto. }
    }
    hexploit committed_trans.
    { eapply STEPS_SRC0. }
    { eapply rtc_implies.
      { instantiate (1:=@Thread.tau_step _). i. inv H. econs; eauto. }
      eapply rtc_dstep_rtc_tau_step. eapply STEPS_SRC1. }
    intros SAME. right. esplits.
    { econs 2; [|eauto]. econs; eauto. rewrite EVENT0. auto. }
    { eauto. }
    { rewrite SAME. eapply pointable_timemap_mon; [|eauto]. i. ss. des; auto. }
    { rewrite SAME. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
    { rewrite SAME. eapply pointable_views_mon; [|eauto]. i. ss. des; auto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { etrans; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_dsteps lang_src lang_tgt
        th_tgt0 th_tgt1 e
        (STEPS: dsteps e th_tgt0 th_tgt1)
        fin th_src0 views0
        (SIM: @JSim.sim_thread views0 lang_src lang_tgt th_src0 th_tgt0)

        (WF_SRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (WF_TGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEM_SRC: Memory.closed (Thread.memory th_src0))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt0))
        (CONS_TGT: Local.promise_consistent (Thread.local th_tgt1))

        (REL: joined_released views0 (Local.promises (Thread.local th_src0)) (Local.tview (Thread.local th_src0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th_src0))
        (VIEWS: wf_views views0)

        (POINTSC: pointable_timemap loc_na fin th_src0.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src0.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views0)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt0.(Thread.state))
    :
      (exists th_src1,
          (<<STEPS_SRC: dsteps MachineEvent.failure th_src0 th_src1>>)) \/
      (exists th_src1 views1,
          (<<STEPS_SRC: dsteps e th_src0 th_src1>>) /\
          (<<SIM: JSim.sim_thread views1 th_src1 th_tgt1>>) /\
          (<<POINTSC: pointable_timemap loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.sc)>>) /\
          (<<POINTLOCAL: pointable_tview loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) th_src1.(Thread.local).(Local.tview)>>) /\
          (<<POINTVIEWS: pointable_views loc_na (fin \4/ (committed th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) th_src1.(Thread.memory) th_src1.(Thread.local).(Local.promises))) views1>>) /\
          (<<JOINED: joined_memory views1 (Thread.memory th_src1)>>) /\
          (<<RELEASED: joined_released views1 th_src1.(Thread.local).(Local.promises) th_src1.(Thread.local).(Local.tview).(TView.rel)>>) /\
          (<<VIEWS: wf_views views1>>) /\
          (<<VIEWSLE: views_le views0 views1>>) /\
          (<<NOMIX: nomix loc_na loc_at _ th_tgt1.(Thread.state)>>))
  .
  Proof.
    inv STEPS.
    { pose proof (rtc_dstep_rtc_tau_step DSTEPS) as STEPS_TGT0.
      hexploit rtc_implies; [|eapply PROMISES|..].
      { instantiate (1:=@Thread.all_step _). i. inv H. inv TSTEP. econs; eauto. }
      intros STEPS_TGT1.
      hexploit Thread.rtc_tau_step_future; [eapply STEPS_TGT0|..]; eauto. i. des.
      hexploit PromiseConsistent.rtc_all_step_promise_consistent; [eapply STEPS_TGT1|..]; eauto. intros CONSISTENT1.
      hexploit sim_thread_rtc_tau_dstep; eauto. i. des.
      { left. eauto. }
      pose proof (rtc_dstep_rtc_tau_step STEPS_SRC) as STEPS_SRC0.
      hexploit Thread.rtc_tau_step_future; [eapply STEPS_SRC0|..]; eauto. i. des.
      hexploit sim_thread_promise_steps; eauto.
      { i. ss. left. auto. }
      i. des. right.
      hexploit committed_trans.
      { eapply rtc_implies.
        { instantiate (2:=@Thread.tau_step lang_src). i. inv H. econs; eauto. }
        eapply STEPS_SRC0. }
      { eapply rtc_implies; [|eapply STEPS_SRC1|..].
        i. inv H. inv TSTEP. econs; eauto.
      }
      intros SAME. esplits.
      { econs 1; eauto. }
      { eauto. }
      { rewrite SAME. eapply pointable_timemap_mon; [|eauto]. i. ss. des; auto. }
      { rewrite SAME. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
      { rewrite SAME. eapply pointable_views_mon; [|eauto]. i. ss. des; auto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { etrans; eauto. }
      { eauto. }
    }
    { pose proof (rtc_dstep_rtc_tau_step DSTEPS) as STEPS_TGT0.
      hexploit Thread.rtc_tau_step_future; [eapply STEPS_TGT0|..]; eauto. i. des.
      pose proof (dstep_rtc_all_step DSTEP) as STEPS_TGT1.
      hexploit PromiseConsistent.rtc_all_step_promise_consistent; [eapply STEPS_TGT1|..]; eauto. intros CONSISTENT1.
      hexploit sim_thread_rtc_tau_dstep; eauto. i. des.
      { left. eauto. }
      pose proof (rtc_dstep_rtc_tau_step STEPS_SRC) as STEPS_SRC0.
      hexploit Thread.rtc_tau_step_future; [eapply STEPS_SRC0|..]; eauto. i. des.
      hexploit sim_thread_dstep; eauto.
      { i. ss. left. auto. }
      i. des.
      { left. esplits. econs; eauto. }
      right. hexploit committed_trans.
      { eapply rtc_implies.
        { instantiate (2:=@Thread.tau_step lang_src). i. inv H. econs; eauto. }
        eapply STEPS_SRC0. }
      { eapply dstep_rtc_all_step. eapply STEPS_SRC1. }
      intros SAME. esplits.
      { econs 2; eauto. }
      { eauto. }
      { rewrite SAME. eapply pointable_timemap_mon; [|eauto]. i. ss. des; auto. }
      { rewrite SAME. eapply pointable_tview_mon; [|eauto]. i. ss. des; auto. }
      { rewrite SAME. eapply pointable_views_mon; [|eauto]. i. ss. des; auto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { etrans; eauto. }
      { eauto. }
    }
  Qed.

  Lemma sim_thread_delayed_consistent lang_src lang_tgt
        th_tgt
        (CONSISTENT: delayed_consistent th_tgt)
        fin th_src views
        (SIM: @JSim.sim_thread views lang_src lang_tgt th_src th_tgt)

        (WF_SRC: Local.wf (Thread.local th_src) (Thread.memory th_src))
        (WF_TGT: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src) (Thread.memory th_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th_src))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt))

        (REL: joined_released views (Local.promises (Thread.local th_src)) (Local.tview (Thread.local th_src)).(TView.rel))
        (JOINED: joined_memory views (Thread.memory th_src))
        (VIEWS: wf_views views)

        (POINTSC: pointable_timemap loc_na fin th_src.(Thread.sc))
        (POINTLOCAL: pointable_tview loc_na fin th_src.(Thread.local).(Local.tview))
        (POINTVIEWS: pointable_views loc_na fin views)
        (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
        (NOMIX: nomix loc_na loc_at _ th_tgt.(Thread.state))
    :
      delayed_consistent th_src.
  Proof.
    hexploit delayed_consistent_promise_consistent; eauto. intros CONSISTENT0.
    ii. red in CONSISTENT.
    hexploit (@Memory.cap_exists th_tgt.(Thread.memory)); eauto. i. des.
    hexploit CONSISTENT; eauto. intros [e [th_tgt1 [STEPS ?]]].
    guardH H. des.
    assert (SIMCAP: JSim.sim_thread
                      views
                      (Thread.mk _ th_src.(Thread.state) th_src.(Thread.local) th_src.(Thread.sc) mem1)
                      (Thread.mk _ th_tgt.(Thread.state) th_tgt.(Thread.local) th_tgt.(Thread.sc) mem2)).
    { dup SIM. inv SIM.
      apply inj_pair2 in H3. apply inj_pair2 in H5. subst. ss.
      assert (st0 = st).
      { inv SIM0.
        apply inj_pair2 in H3. apply inj_pair2 in H8. subst. auto. }
      subst. econs; eauto. eapply sim_memory_cap; eauto.
    }
    pose proof (dsteps_rtc_all_step STEPS) as STEPS_TGT0.
    hexploit Thread.rtc_all_step_future; [eapply STEPS_TGT0|..]; eauto.
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des; ss.
    hexploit sim_thread_dsteps; eauto; ss.
    { eapply Local.cap_wf; eauto. }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed; eauto. }
    { eapply Memory.cap_closed; eauto. }
    { red in H. des; subst.
      { inv STEPS; ss. inv DSTEP. inv STEP_RELEASE; inv STEP; ss.
        inv LOCAL; ss; inv LOCAL0; ss.
      }
      { eapply rtc_implies in STEPS0.
        2:{ instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. econs; eauto. }
        eapply PromiseConsistent.rtc_tau_step_promise_consistent in STEPS0; eauto.
        eapply Local.bot_promise_consistent; eauto.
      }
    }
    { eapply JSim.joined_memory_cap; eauto. }
    i. des.
    { esplits; eauto. }
    red in H. des.
    { esplits; eauto. }
    dup SIM0. inv SIM0.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM1. apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst.
    pose proof (dsteps_rtc_all_step STEPS_SRC) as STEPS_SRC0.
    hexploit Thread.rtc_all_step_future; [eapply STEPS_SRC0|..]; eauto.
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des; ss.
    hexploit sim_thread_lower_steps; [eapply STEPS0|..]; eauto; ss.
    { eapply Local.bot_promise_consistent; eauto. }
    { auto. }
    i. des.
    { esplits; [|left; eauto]. instantiate (1:=th_src2). inv STEPS_SRC.
      { econs 2.
        { eauto. }
        { econs.
          { eauto. }
          { etrans; eauto. }
          { eauto. }
          { destruct e_src; ss. }
        }
        { auto. }
      }
      { econs 2.
        { etrans; [eauto|]. econs 2; [|refl]. econs; eauto. }
        { econs.
          { refl. }
          { eauto. }
          { eauto. }
          { destruct e_src; ss. }
        }
        { auto. }
      }
    }
    esplits; eauto. right. esplits; eauto.
    inv SIM0. eapply inj_pair2 in H2. eapply inj_pair2 in H4. subst.
    eapply JSim.sim_local_memory_bot; eauto.
  Qed.

  Definition dstep_finalized e tid c0 c1
             (STEP: DConfiguration.step e tid c0 c1)
             (WF: Configuration.wf c0)
    :
      finalized c0 <4= finalized c1.
  Proof.
    ii. inv STEP.
    hexploit finalized_unchangable; eauto. i.
    eapply dsteps_rtc_all_step in DSTEPS.
    hexploit unchangable_rtc_all_step_increase; eauto. i.
    inv H0. econs; eauto. i. ss.
    rewrite IdentMap.gsspec in TID0. des_ifs.
    inv PR. eapply NPROM0; eauto.
  Qed.

  Definition dstep_committed_finalized e tid c0 c1 st0 st1 lc0 lc1
             (STEP: DConfiguration.step e tid c0 c1)
             (FIND0: IdentMap.find tid c0.(Configuration.threads) = Some (st0, lc0))
             (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (st1, lc1))
             (WF: Configuration.wf c0)
    :
      committed c0.(Configuration.memory) lc0.(Local.promises) c1.(Configuration.memory) lc1.(Local.promises) <4= finalized c1.
  Proof.
    hexploit DConfiguration.step_future; eauto. i. des.
    ii. inv PR. dup UNCHANGABLE. inv UNCHANGABLE. econs; eauto.
    i. inv STEP. ss.
    rewrite IdentMap.gss in FIND1. clarify.
    dup TID. rewrite IdentMap.gsspec in TID. des_ifs.
    destruct (Memory.get x0 x1 lc.(Local.promises)) as [[from msg]|] eqn:EQ; auto.
    exfalso. eapply NUNCHANGABLE.
    destruct c0, lc, lc0. ss.
    eapply other_promise_unchangable with (tid1:=tid) (tid2:=tid0); eauto.
    econs; eauto. inv WF2. ss.
    inv WF0. destruct st. exploit THREADS; eauto.
    i. inv x4. ss. rewrite EQ. eapply PROMISES in EQ. clarify.
  Qed.

  Variant d_na_step e tid c1 c2 :=
  | d_na_step_intro
      (STEP: DConfiguration.step e tid c1 c2)
      (CLOSEDFUTURE: forall (NFAILURE: e <> MachineEvent.failure)
                            tid0 (TID: tid0 <> tid)
                            lang st lc
                            (TID: IdentMap.find tid0 (Configuration.threads c1) = Some (existT _ lang st, lc)),
          closed_future_tview loc_na lc.(Local.tview) c1.(Configuration.memory) c2.(Configuration.memory))
  .

  Variant sim_configuration
          (views: Loc.t -> Time.t -> list View.t):
    forall (c_src c_tgt: Configuration.t), Prop :=
  | sim_configuration_intro
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (THS: forall tid,
          option_rel
            (JSim.sim_statelocal views)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt))
      (MEM: sim_memory mem_src mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_configuration
        views
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration.

  Variant pointable_configuration
          (views: Loc.t -> Time.t -> list View.t)
          (fin: Messages.t) (c: Configuration.t): Prop :=
  | pointable_configuration_intro
      (SC: pointable_timemap loc_na fin c.(Configuration.sc))
      (MEM: pointable_memory loc_na fin c.(Configuration.memory))
      (THS: forall tid lang st lc
                   (TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
          pointable_tview loc_na fin lc.(Local.tview))
      (VIEWS: pointable_views loc_na fin views)
      (FIN: fin <4= finalized c)
      (FINBOT: forall loc, fin loc Time.bot Time.bot Message.elt)
  .

  Variant nomix_configuration (c: Configuration.t): Prop :=
  | nomix_configuration_intro
      (THS: forall tid lang st lc
                   (TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
          nomix loc_na loc_at _ st)
  .

  Lemma pointable_closed_future_timemap fin tm mem0 mem1
        (TM: pointable_timemap loc_na fin tm)
        (FIN0: fin <4= Messages.of_memory mem0)
        (FIN1: fin <4= Messages.of_memory mem1)
    :
      closed_future_timemap loc_na tm mem0 mem1.
  Proof.
    ii. hexploit (TM loc); auto. i. des.
    hexploit FIN0; eauto. hexploit FIN1; eauto. i.
    inv H0. inv H1. rewrite GET. rewrite GET0. ss.
  Qed.

  Lemma pointable_closed_future_view fin vw mem0 mem1
        (VW: pointable_view loc_na fin vw)
        (FIN0: fin <4= Messages.of_memory mem0)
        (FIN1: fin <4= Messages.of_memory mem1)
    :
      closed_future_view loc_na vw mem0 mem1.
  Proof.
    econs.
    { eapply pointable_closed_future_timemap; eauto. eapply VW. }
    { eapply pointable_closed_future_timemap; eauto. eapply VW. }
  Qed.

  Lemma pointable_closed_future_tview fin tvw mem0 mem1
        (TVW: pointable_tview loc_na fin tvw)
        (FIN0: fin <4= Messages.of_memory mem0)
        (FIN1: fin <4= Messages.of_memory mem1)
    :
      closed_future_tview loc_na tvw mem0 mem1.
  Proof.
    econs.
    { i. eapply pointable_closed_future_view; eauto. eapply TVW. }
    { eapply pointable_closed_future_view; eauto. eapply TVW. }
    { eapply pointable_closed_future_view; eauto. eapply TVW. }
  Qed.

  Lemma sim_configuration_step views0 fin0 c_tgt0 c_tgt1 c_src0 e tid
        (STEP: DConfiguration.step e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration views0 c_src0 c_tgt0)
        (NOMIX: nomix_configuration c_tgt0)
        (POINTABLE: pointable_configuration views0 fin0 c_src0)
        (WFSRC: JConfiguration.wf views0 c_src0)
        (WFTGT: Configuration.wf c_tgt0)
    :
      (exists c_src1,
        (<<STEP: d_na_step MachineEvent.failure tid c_src0 c_src1>>)) \/
      (exists c_src1 e views1 fin1,
        (<<STEP: d_na_step e tid c_src0 c_src1>>) /\
        (<<SIM: sim_configuration views0 c_src0 c_tgt0>>) /\
        (<<NOMIX: nomix_configuration c_tgt1>>) /\
        (<<POINTABLE: pointable_configuration views1 fin1 c_src1>>) /\
        (<<WFSRC: JConfiguration.wf views1 c_src1>>) /\
        (<<WFTGT: Configuration.wf c_tgt1>>))
  .
  Proof.
    dup WFSRC. dup WFTGT. dup STEP.
    hexploit DConfiguration.step_future; eauto. i. des.
    inv SIM. inv STEP. inv NOMIX. inv POINTABLE. ss.
    inv WFTGT. inv WFSRC. dup WF0. inv WF0. ss.
    hexploit THS0; eauto. intros NOMIX.
    hexploit (THS tid). i. rewrite TID in H.
    destruct (IdentMap.find tid ths_src) as [|] eqn:TIDSRC; ss.
    ss. dup H. inv H. eapply inj_pair2 in H4.
    assert (st1 = st).
    { inv H0. apply inj_pair2 in H2. apply inj_pair2 in H. subst. auto. }
    subst. hexploit REL; eauto. intros RELEASED.
    hexploit THS1; eauto. intros POINTVIEW.
    inv WF3. inv WF.
    hexploit THREADS; eauto. intros LOCALTGT.
    hexploit THREADS0; eauto. intros LOCALSRC.
    hexploit Thread.rtc_all_step_future.
    { eapply dsteps_rtc_all_step. eapply DSTEPS. }
    all: eauto. i. des. ss.
    hexploit sim_thread_dsteps.
    { eauto. }
    { econs; eauto. }
    all: eauto.
    { destruct (classic (e = MachineEvent.failure)); eauto.
      { subst. inv DSTEPS. inv DSTEP; ss. inv STEP_RELEASE; inv STEP; ss.
        inv LOCAL0; ss; inv LOCAL1; ss.
      }
      { hexploit CONSISTENT; eauto. i.
        eapply delayed_consistent_promise_consistent in H1; eauto; ss.
      }
    }
    i. ss. des.
    { destruct th_src1. left. esplits. econs.
      { econs; eauto. ss. }
      { ss. }
    }
    destruct th_src1.
    assert (DSTEP: DConfiguration.step
                     e
                     tid
                     (Configuration.mk
                        ths_src sc_src mem_src)
                     (Configuration.mk
                        (IdentMap.add tid (existT (Language.state (E:=ProgramEvent.t)) lang state, local) ths_src)
                        sc memory)).
    { econs; eauto. i.
      hexploit CONSISTENT; eauto. i.
      hexploit Thread.rtc_all_step_future.
      { eapply dsteps_rtc_all_step. eapply STEPS_SRC. }
      all: eauto. i. des; ss.
      eapply sim_thread_delayed_consistent; eauto.
      i. ss. left. auto.
    }
    right. esplits; auto.
    { econs.
      { eauto. }
      { i. ss. eapply pointable_closed_future_tview.
        { eapply THS1 in TID1; eauto. }
        { i. hexploit FIN; eauto. i. inv H. econs; eauto. }
        { i. hexploit FIN; eauto. i.
          hexploit dstep_finalized; eauto. i. inv H1. econs; eauto. }
      }
    }
    { econs. i. ss. rewrite IdentMap.gsspec in TID0. des_ifs.
      { eapply inj_pair2 in H1. subst. auto. }
      { eauto. }
    }
    { econs; ss; eauto.
      { eapply pointable_joined_memory; eauto. }
      { i. rewrite IdentMap.gsspec in TID0. des_ifs.
        eapply pointable_tview_mon.
        { i. left. eapply PR. }
        { eauto. }
      }
      { i. ss. des.
        { eapply dstep_finalized; eauto. }
        { eapply dstep_committed_finalized; eauto.
          ss. erewrite IdentMap.gss. eauto.
        }
      }
      { i. ss. left. auto. }
    }
    { hexploit DConfiguration.step_future; eauto. i. des; ss. econs; eauto.
      i. ss. erewrite IdentMap.gsspec in TH. des_ifs.
      eapply joined_released_le; eauto.
    }
  Qed.
End NA.
