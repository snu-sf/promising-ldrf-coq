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

  Lemma pointable_joined_opt_view views released
        (JOINED: joined_opt_view views released)
        (VIEWS: List.Forall pointable_view views)
    :
      pointable_opt_view released.
  Proof.
    inv JOINED; econs.
    revert VIEWS. induction JOINED0; i.
    { eapply pointable_view_bot; eauto. }
    { eapply pointable_view_join; eauto.
      eapply List.Forall_forall in VIEW; eauto.
    }
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
End POINTABLE.
