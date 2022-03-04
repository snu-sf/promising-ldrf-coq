Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
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

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Require Import Lia.

Require Import JoinedView.
Require Import SeqLift.
Require Import Sequential.

Require Import Pred.

Require Import SeqLiftStep.


Variant sim_thread_sol
        (c: bool)
        (vs: Loc.t -> Const.t)
        (P: Loc.t -> bool)
        (D: Loc.t -> bool)
        mem lc: Prop :=
  | sim_thread_intro
      (CONS: Local.promise_consistent lc)
      (DEBT: forall loc to from msg
                    (GET: Memory.get loc to lc.(Local.promises) = Some (from, msg)),
          (<<MSG: msg <> Message.reserve>>) /\ (<<DEBT: c = true -> D loc>>))
      (NSYNC: forall loc, Memory.nonsynch_loc loc lc.(Local.promises))
      (VALS: forall loc,
        exists from released,
          (<<GET: Memory.get loc (lc.(Local.tview).(TView.cur).(View.rlx) loc) mem = Some (from, Message.concrete (vs loc) released)>>))
      (PERM: forall loc val released (MAX: max_readable mem lc.(Local.promises) loc (lc.(Local.tview).(TView.cur).(View.pln) loc) val released),
          P loc)
.

Definition lowered_content (b: bool) (cnt0 cnt1: option (Time.t * Message.t)): Prop :=
  (cnt0 = cnt1 /\ b = false) \/
    cnt1 = match cnt0 with
           | Some (_, Message.reserve) | None => None
           | Some (from, Message.undef) => Some (from, Message.undef)
           | Some (from, Message.concrete val released) => Some (from, Message.concrete val None)
           end.

Lemma lowered_content_trans b0 b1 b2 cnt0 cnt1 cnt2
      (LOWER0: lowered_content b0 cnt0 cnt1)
      (LOWER1: lowered_content b1 cnt1 cnt2)
      (BOOL: b0 = false -> b1 = false -> b2 =false)
  :
  lowered_content b2 cnt0 cnt2.
Proof.
  unfold lowered_content in *. des; subst; auto.
  right. des_ifs.
Qed.

Definition lowered_memory mem0 mem1: Prop :=
  forall loc to, lowered_content false (Memory.get loc to mem0) (Memory.get loc to mem1).

Program Instance lowered_memory_PreOrder: PreOrder lowered_memory.
Next Obligation.
Proof.
  ii. left. auto.
Qed.
Next Obligation.
Proof.
  ii. specialize (H loc to). specialize (H0 loc to).
  eapply lowered_content_trans; eauto.
Qed.

Lemma lower_none_lowered_memory mem0 loc from to val released mem1
      (LOWER: Memory.lower mem0 loc from to (Message.concrete val released) (Message.concrete val None) mem1)
  :
  lowered_memory mem0 mem1.
Proof.
  ii. erewrite (@Memory.lower_o mem1); eauto. des_ifs.
  { ss. des; clarify. right.
    eapply Memory.lower_get0 in LOWER. des. rewrite GET. ss.
  }
  { left. auto. }
Qed.

Lemma cancel_lowered_memory mem0 loc from to  mem1
      (CANCEL: Memory.remove mem0 loc from to Message.reserve mem1)
  :
  lowered_memory mem0 mem1.
Proof.
  ii. erewrite (@Memory.remove_o mem1); eauto. des_ifs.
  { ss. des; clarify. right.
    eapply Memory.remove_get0 in CANCEL. des. rewrite GET. ss.
  }
  { left. auto. }
Qed.

Lemma nonsynch_all
      lang st
      tvw prom0 mem0 sc
      (LOCAL: Local.wf (Local.mk tvw prom0) mem0)
  :
  exists prom1 mem1,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st (Local.mk tvw prom0) sc mem0) (Thread.mk _ st (Local.mk tvw prom1) sc mem1)>>) /\
      (<<NONE: forall loc to,
          Memory.get loc to prom1 = match Memory.get loc to prom0 with
                                    | Some (_, Message.reserve) | None => None
                                    | Some (from, Message.undef) => Some (from, Message.undef)
                                    | Some (from, Message.concrete val released) => Some (from, Message.concrete val None)
                                    end>>) /\
      (<<MAX: forall loc val released,
          max_readable mem0 prom0 loc (tvw.(TView.cur).(View.pln) loc) val released
          <->
            max_readable mem1 prom1 loc (tvw.(TView.cur).(View.pln) loc) val released>>) /\
      (<<PRESERVE: forall loc to val released from
                          (GET: Memory.get loc to mem0 = Some (from, Message.concrete val released)),
        exists released', (<<GET: Memory.get loc to mem1 = Some (from, Message.concrete val released')>>)>>)
.
Proof.
  inv LOCAL. clear TVIEW_WF TVIEW_CLOSED. rename PROMISES into MLE.
  red in FINITE. des.
  cut (exists prom1 mem1,
             (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st (Local.mk tvw prom0) sc mem0) (Thread.mk _ st (Local.mk tvw prom1) sc mem1)>>) /\
               (<<NONE: forall loc to (IN: List.In (loc, to) dom),
                   lowered_content true (Memory.get loc to prom0) (Memory.get loc to prom1)>>) /\
               (<<MAX: forall loc val released,
                   max_readable mem0 prom0 loc (tvw.(TView.cur).(View.pln) loc) val released
                   <->
                     max_readable mem1 prom1 loc (tvw.(TView.cur).(View.pln) loc) val released>>) /\
               (<<LOWERPROM: lowered_memory prom0 prom1>>) /\
               (<<LOWERMEM: lowered_memory mem0 mem1>>)).
  { i. des. esplits; eauto.
    { i. specialize (NONE loc to). unfold lowered_content in *.
      destruct (Memory.get loc to prom0) as [[from msg]|] eqn:PROM.
      { hexploit NONE; eauto. i; des; ss. }
      { specialize (LOWERPROM loc to). rewrite PROM in LOWERPROM.
        red in LOWERPROM. des; auto.
      }
    }
    { i. specialize (LOWERMEM loc to). rewrite GET in LOWERMEM. des; eauto.
      red in LOWERMEM. des; eauto.
    }
  }
  clear FINITE. revert prom0 mem0 MLE BOT. induction dom.
  { i. esplits.
    { refl. }
    { i. ss. }
    { auto. }
    { refl. }
    { refl. }
  }
  i. destruct a as [loc to].
  destruct (Memory.get loc to prom0) as [[from msg]|] eqn:GET.
  { destruct msg.
    { hexploit Memory.lower_exists.
      { eapply GET. }
      { hexploit memory_get_ts_strong; eauto. i. des; clarify.
        rewrite BOT in GET. ss.
      }
      { instantiate (1:=Message.concrete val None). econs; ss. }
      { econs; ss. refl. }
      i. des.
      hexploit Memory.lower_exists_le; eauto. i. des.
      assert (PROMISE: Memory.promise prom0 mem0 loc from to (Message.concrete val None) mem2 mem1 (Memory.op_kind_lower (Message.concrete val released))).
      { econs; eauto; ss. econs. eapply Time.bot_spec. }
      hexploit (IHdom mem2 mem1); eauto.
      { eapply promise_memory_le; eauto. }
      { eapply Memory.promise_bot_none; eauto. }
      i. des. esplits.
      { econs 2.
        { econs.
          { econs. econs 1. econs; eauto. }
          { ss. }
        }
        { eauto. }
      }
      { i. ss. des; clarify.
        { eapply lowered_content_trans.
          2:{ eapply LOWERPROM. }
          2:{ instantiate (1:=true). ss. }
          des; clarify.
          { rewrite GET. erewrite (@Memory.lower_o mem2); eauto.
            des_ifs; ss; des; clarify. right. auto.
          }
        }
        { eapply lowered_content_trans.
          2:{ eapply NONE; eauto. }
          2:{ instantiate (1:=false). ss. }
          eapply lower_none_lowered_memory; eauto.
        }
      }
      { i. etrans; [|eapply MAX]. destruct (Loc.eq_dec loc0 loc); subst.
        { eapply promise_max_readable; eauto. }
        { eapply promise_unchanged_loc in PROMISE; eauto. des.
          eapply unchanged_loc_max_readable; eauto.
        }
      }
      { etrans; eauto. eapply lower_none_lowered_memory; eauto. }
      { etrans; eauto. eapply lower_none_lowered_memory; eauto. }
    }
    { hexploit (IHdom prom0 mem0); eauto. i. des. esplits; eauto.
      i. ss. des; clarify.
      { eapply lowered_content_trans.
        2:{ eapply LOWERPROM. }
        2:{ instantiate (1:=true). ss. }
        rewrite GET. right. auto.
      }
      { eapply NONE; auto. }
    }
    { hexploit Memory.remove_exists.
      { eapply GET. }
      i. des.
      hexploit Memory.remove_exists_le; eauto. i. des.
      assert (PROMISE: Memory.promise prom0 mem0 loc from to Message.reserve mem2 mem1 (Memory.op_kind_cancel)).
      { econs; eauto; ss. }
      hexploit (IHdom mem2 mem1); eauto.
      { eapply promise_memory_le; eauto. }
      { eapply Memory.promise_bot_none; eauto. }
      i. des. esplits.
      { econs 2.
        { econs.
          { econs. econs 1. econs; eauto. }
          { ss. }
        }
        { eauto. }
      }
      { i. ss. des; clarify.
        { eapply lowered_content_trans.
          2:{ eapply LOWERPROM. }
          2:{ instantiate (1:=true). ss. }
          des; clarify.
          { rewrite GET. erewrite (@Memory.remove_o mem2); eauto.
            des_ifs; ss; des; clarify. right. auto.
          }
        }
        { eapply lowered_content_trans.
          2:{ eapply NONE; eauto. }
          2:{ instantiate (1:=false). ss. }
          eapply cancel_lowered_memory; eauto.
        }
      }
      { i. etrans; [|eapply MAX]. destruct (Loc.eq_dec loc0 loc); subst.
        { eapply promise_max_readable; eauto. }
        { eapply promise_unchanged_loc in PROMISE; eauto. des.
          eapply unchanged_loc_max_readable; eauto.
        }
      }
      { etrans; eauto. eapply cancel_lowered_memory; eauto. }
      { etrans; eauto. eapply cancel_lowered_memory; eauto. }
    }
  }
  { hexploit (IHdom prom0 mem0); eauto. i. des. esplits; eauto.
    i. ss. des; clarify.
    { eapply lowered_content_trans.
      2:{ eapply LOWERPROM. }
      2:{ instantiate (1:=true). ss. }
      rewrite GET. right. auto.
    }
    { eapply NONE; auto. }
  }
Qed.

Lemma sim_thread_sim_thread_sol
      c D f vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (BOT: c = true -> lc_tgt.(Local.promises) = Memory.bot)
      (CONSTGT: Local.promise_consistent lc_tgt)
      (DEBT: forall loc (TGT: flag_src loc = false) (DEBT: D loc = false), flag_tgt loc = false)
      (WF: Mapping.wfs f)
      (LOCAL: Local.wf lc_src0 mem_src0)
      lang st
  :
  exists mem_src1 lc_src1 vs,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st lc_src0 sc_src mem_src0) (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread_sol c vs (fun loc => vs_src loc) D mem_src1 lc_src1>>) /\
      (<<VALS: forall loc val (VAL: vs_src loc = Some val), vs loc = val>>)
.
Proof.
  hexploit (choice (fun loc val =>
                      exists from released,
                        (<<GET: Memory.get loc (lc_src0.(Local.tview).(TView.cur).(View.rlx) loc) mem_src0 = Some (from, Message.concrete val released)>>))).
  { inv LOCAL. inv TVIEW_CLOSED. inv CUR.
    intros loc. hexploit (RLX loc). i. des. eauto.
  }
  intros [vs VALS]. inv SIM.
  assert (CONSSRC: Local.promise_consistent lc_src0).
  { eapply sim_local_consistent; eauto. }
  destruct lc_src0 as [tvw_src prom_src0].
  hexploit nonsynch_all; eauto. i. des.
  exists mem1, (Local.mk tvw_src prom1), vs. splits.
  { eauto. }
  { econs; eauto.
    { ii. ss. rewrite NONE in PROMISE. des_ifs.
      { eapply CONSSRC; eauto; ss. }
      { eapply CONSSRC; eauto; ss. }
    }
    { inv LOCAL0. i. ss.
      assert (exists msg', Memory.get loc to prom_src0 = Some (from, msg') /\ msg <> Message.reserve).
      { rewrite NONE in GET. des_ifs.
        { esplits; eauto; ss. }
        { esplits; eauto; ss. }
      }
      des. splits; auto. i. subst.
      hexploit sim_promises_get_if; eauto. i. des.
      { rewrite BOT in GET0; auto. rewrite Memory.bot_get in GET0. ss. }
      { destruct (flag_src loc) eqn:EQ.
        { erewrite sim_promises_none in H; eauto. ss. }
        { destruct (D loc) eqn:DEBT0; eauto. hexploit DEBT; eauto. i. des; clarify. }
      }
    }
    { ii. ss. rewrite NONE in GET. des_ifs. }
    { i. ss. specialize (VALS loc). des. hexploit PRESERVE; eauto. }
    { i. ss. ss. hexploit (MAXSRC loc). i. inv H.
      destruct (vs_src loc) eqn:VAL; ss.
      exfalso. eapply NONMAX; eauto. eapply MAX; eauto.
    }
  }
  { i. hexploit (MAXSRC loc). i. inv H.
    hexploit (VALS loc). i.
    hexploit MAX0; eauto. i. des. ss. inv MAX1.
    assert (TS: View.pln (TView.cur tvw_src) loc = View.rlx (TView.cur tvw_src) loc).
    { eapply TimeFacts.antisym.
      { eapply LOCAL. }
      destruct (Time.le_lt_dec (View.rlx (TView.cur tvw_src) loc) (View.pln (TView.cur tvw_src) loc)); auto.
      exfalso. eapply MAX2 in l; eauto; ss.
      exploit CONSSRC; eauto; ss. i. timetac.
    }
    rewrite TS in *. clarify.
  }
Qed.

Lemma sim_thread_none
      vs P D mem lc
      (SIM: sim_thread_sol true vs P D mem lc)
      (DEBT: forall loc, D loc = false)
  :
  lc.(Local.promises) = Memory.bot.
Proof.
  eapply Memory.ext. i. rewrite Memory.bot_get.
  inv SIM. destruct (Memory.get loc ts lc.(Local.promises)) eqn:GET; auto.
  destruct p. exploit DEBT0; eauto. i. des.
  exfalso. hexploit DEBT1; eauto. rewrite DEBT. ss.
Qed.

Lemma sim_thread_sol_failure
      c vs P D mem lc
      (SIM: sim_thread_sol c vs P D mem lc)
  :
  Local.failure_step lc.
Proof.
  inv SIM. econs. eauto.
Qed.

Lemma sim_thread_sol_fence
      c vs P D mem lc0 sc ordr ordw
      (SIM: sim_thread_sol c vs P D mem lc0)
      (ORDR: ~ Ordering.le Ordering.acqrel ordr)
      (ORDW: ~ Ordering.le Ordering.seqcst ordw)
  :
  exists lc1,
    (<<FENCE: Local.fence_step lc0 sc ordr ordw lc1 sc>>) /\
    (<<SIM: sim_thread_sol c vs P D mem lc1>>)
.
Proof.
  inv SIM. esplits.
  { econs; eauto.
    { destruct ordw; ss. }
    { i. destruct ordw; ss. }
  }
  econs; eauto; ss.
  { ii. ss. des_ifs. eapply CONS; eauto. }
  { ii. des_ifs. }
  { ii. des_ifs. eapply PERM; eauto. }
Qed.

Lemma sim_thread_sol_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  exists to, Local.is_racy lc mem loc to Ordering.na.
Proof.
  inv SIM. destruct lc.
  hexploit non_max_readable_race; eauto.
Qed.

Lemma sim_thread_sol_read_na_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
      val
  :
  exists to, Local.racy_read_step lc mem loc to val Ordering.na.
Proof.
  exploit sim_thread_sol_racy; eauto. i. des.
  esplits. eauto.
Qed.

Lemma sim_thread_sol_write_na_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  exists to, Local.racy_write_step lc mem loc to Ordering.na.
Proof.
  exploit sim_thread_sol_racy; eauto. i. des.
  esplits. econs; eauto.
  inv SIM. auto.
Qed.

Lemma sim_thread_sol_read_na
      c vs P D mem lc loc val
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (VAL: Const.le val (vs loc))
  :
  exists ts released,
    (<<READ: Local.read_step lc mem loc ts val released Ordering.na lc>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss. eapply LOCAL. }
  destruct lc. f_equal. ss. unfold TView.read_tview. des_ifs.
  ss. rewrite ! View.join_bot_r. rewrite ! View.le_join_l.
  { destruct tview; auto. }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { eapply LOCAL. }
  }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { refl. }
  }
Qed.

Lemma sim_thread_sol_read
      c vs P D mem lc0 loc ord val
      (SIM: sim_thread_sol c vs P D mem lc0)
      (LOCAL: Local.wf lc0 mem)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (VAL: Const.le val (vs loc))
  :
  exists ts released lc1,
    (<<READ: Local.read_step lc0 mem loc ts val released ord lc1>>) /\
    (<<SIM: sim_thread_sol c vs (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) D mem lc1>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss.
    { eapply LOCAL. }
    { i. refl. }
  }
  destruct lc0 as [tvw0 prom]. ss.
  set (tvw1 := (TView.read_tview
                  tvw0 loc
                  (View.rlx (TView.cur tvw0) loc) released ord)).
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
    { eapply Time.bot_spec. }
  }
  assert (RLX: forall loc0, tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { eapply TimeMap.singleton_spec. refl. }
    { eapply TimeMap.singleton_spec. refl. }
  }
  remember tvw1. clear tvw1 Heqt.
  econs; eauto; ss.
  { ii. ss. rewrite RLX. eapply CONS; eauto. }
  { i. rewrite RLX. eauto. }
  { i. destruct (Loc.eq_dec loc0 loc); auto.
    rewrite OTHERPLN in MAX; eauto.
  }
Qed.

Lemma sim_thread_sol_write_na
      c vs P D mem0 lc0 sc loc val
      (SIM: sim_thread_sol c vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
      lang st
  :
  (exists to, Local.racy_write_step lc0 mem0 loc to Ordering.na)
  \/
  exists lc1 mem1 lc2 mem2 from to msgs kinds kind,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc0 sc mem0)
                  (Thread.mk _ st lc1 sc mem1)>>) /\
    (<<WRITE: Local.write_na_step lc1 sc mem1 loc from to val Ordering.na lc2 sc mem2 msgs kinds kind>>) /\
    (<<SIM: sim_thread_sol c (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then false else D loc0) mem2 lc2>>)
.
Proof.
  destruct lc0 as [tvw0 prom0].
  destruct (classic (exists val released, <<MAX: max_readable mem0 prom0 loc (tvw0.(TView.cur).(View.pln) loc) val released>>)).
  2:{ left. inv SIM.
      exploit non_max_readable_race; eauto. i. des. eauto. }
  right. des.
  inv SIM. hexploit max_readable_na_write_step; eauto.
  { i. exploit NSYNC; eauto. }
  { refl. }
  { eapply Time.incr_spec. }
  { eapply Time.incr_spec. }
  i. des. esplits.
  { eapply reserve_future_steps. eapply cancel_future_reserve_future; eauto. }
  { eauto. }
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (SAMERLX: tvw1.(TView.cur).(View.rlx) loc = tvw1.(TView.cur).(View.pln) loc).
  { rewrite VIEW. inv WRITE. clarify. ss.
    unfold TimeMap.join. rewrite timemap_singleton_eq.
    eapply TimeFacts.le_join_r.
    hexploit (VALS loc). i. des.
    eapply Memory.max_ts_spec in GET. des. etrans; eauto.
    left. etrans; eapply Time.incr_spec.
  }
  econs.
  { ii. ss. rewrite PROMISES in PROMISE. des_ifs.
    rewrite OTHERRLX; eauto.
  }
  { ii. ss. rewrite PROMISES in GET. des_ifs. eauto. }
  { ii. ss. rewrite PROMISES in GET. des_ifs. eapply NSYNC in GET; eauto. }
  { ii. ss. des_ifs.
    { rewrite SAMERLX. rewrite VIEW. inv MAX0. eauto. }
    { erewrite Memory.add_o; eauto.
      erewrite Memory.add_o; eauto. des_ifs.
      { ss. des; clarify. }
      { ss. des; clarify. }
      clear o. rewrite OTHERRLX; auto.
      inv LOWER. rewrite OTHER; auto.
    }
  }
  { i. ss. des_ifs.
    inv WRITE. clarify. eapply na_write_unchanged_loc in WRITE0; eauto.
    eapply cancel_future_unchanged_loc in RESERVE; eauto. des.
    rewrite OTHERPLN in MAX1; auto.
    des. eapply PERM. eapply unchanged_loc_max_readable; [..|eauto].
    { etrans; eauto. }
    { etrans; eauto. }
  }
Qed.

Lemma write_tview_other_rlx
      tvw sc loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.rlx) loc0 = tvw.(TView.cur).(View.rlx) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_other_pln
      tvw sc loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.pln) loc0 = tvw.(TView.cur).(View.pln) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_same_pln
      tvw sc loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) sc loc ts ord)
      (TVIEW: TView.wf tvw)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.pln) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  transitivity (View.rlx (TView.cur tvw) loc).
  { eapply TVIEW. }
  { left. eapply WRITABLE. }
Qed.

Lemma write_tview_same_rlx
      tvw sc loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) sc loc ts ord)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.rlx) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  left. eapply WRITABLE.
Qed.

Lemma sim_thread_sol_write
      c vs P D mem0 lc0 sc loc ord val
      (SIM: sim_thread_sol c vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
  :
  exists lc1 mem1 from to released kind,
    (<<WRITE: Local.write_step lc0 sc mem0 loc from to val None released ord lc1 sc mem1 kind>>) /\
    (<<SIM: sim_thread_sol c (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) D mem1 lc1>>)
.
Proof.
  Local Opaque TView.write_tview.
  destruct lc0 as [tvw0 prom0].
  assert (exists lc1 mem1 from to released kind,
             (<<WRITE: Local.write_step (Local.mk tvw0 prom0) sc mem0 loc from to val None released ord lc1 sc mem1 kind>>) /\
             (<<CONS: Local.promise_consistent lc1>>) /\
             (<<NSYNC: forall loc, Memory.nonsynch_loc loc lc1.(Local.promises)>>) /\
             (<<GET: forall from0 to0 msg0 (GET: Memory.get loc to0 lc1.(Local.promises) = Some (from0, msg0)),
               exists from1, Memory.get loc to0 prom0 = Some (from1, msg0)>>)).
  { set (msg := fun ts => Message.concrete val (TView.write_released tvw0 sc loc ts None ord)).
    assert (MSGWF: forall ts, Message.wf (msg ts)).
    { i. unfold msg. econs.
      eapply TViewFacts.write_future0; eauto. eapply LOCAL.
    }
    assert (MSGTO: forall ts (WRITABLE: TView.writable tvw0.(TView.cur) sc loc ts ord), Memory.message_to (msg ts) loc ts).
    { i. econs. eapply writable_message_to; eauto.
      { eapply LOCAL. }
      { eapply WRITABLE. }
      { eapply Time.bot_spec. }
    }
    hexploit (cell_elements_least (prom0 loc) (fun _ => True)).
    i. des.
    { assert (TS: Time.lt from to).
      { hexploit memory_get_ts_strong; eauto. i. des; clarify.
        inv LOCAL. ss. specialize (BOT loc). setoid_rewrite GET in BOT. ss.
      }
      set (ts := Time.middle from to).
      hexploit (Time.middle_spec TS). i. des.
      assert (WRITABLE: TView.writable tvw0.(TView.cur) sc loc ts ord).
      { econs. eapply TimeFacts.le_lt_lt; [|eauto].
        inv SIM. hexploit (VALS loc). i. des.
        eapply memory_get_from_mon; eauto.
        { eapply LOCAL. eauto. }
        exploit CONS; eauto. eapply DEBT; eauto.
      }
      hexploit (@Memory.split_exists prom0 loc from ts to (msg ts) msg0); eauto.
      i. des.
      hexploit Memory.split_exists_le.
      { eapply LOCAL. }
      { eauto. }
      i. des.
      hexploit Memory.remove_exists.
      { eapply Memory.split_get0 in H1. des. eapply GET2. }
      i. des.
      assert (WRITE: Memory.write prom0 mem0 loc from ts (msg ts) mem3 mem1 (Memory.op_kind_split to msg0)).
      { econs; eauto.
        { econs 2; eauto.
          { ss. }
          { inv SIM. eapply DEBT; eauto. }
        }
      }
      esplits.
      { econs; eauto. inv SIM. eauto. }
      { ii. ss. destruct (Loc.eq_dec loc0 loc).
        { subst. rewrite write_tview_same_rlx; auto.
          erewrite Memory.remove_o in PROMISE; eauto.
          erewrite Memory.split_o in PROMISE; eauto. des_ifs.
          { ss. des; clarify. }
          { ss. des; clarify. eapply LEAST in PROMISE; eauto.
            eapply TimeFacts.lt_le_lt; eauto.
          }
        }
        { rewrite write_tview_other_rlx; auto. inv SIM. eapply CONS; eauto.
          ss. erewrite <- Memory.write_get_diff_promise; eauto.
        }
      }
      { ii. ss. inv SIM. erewrite Memory.remove_o in GET0; eauto.
        erewrite Memory.split_o in GET0; eauto. des_ifs.
        { ss. des; clarify. eapply NSYNC in GET; eauto. }
        { eapply NSYNC in GET0; eauto. }
      }
      { i. ss. erewrite Memory.remove_o in GET0; eauto.
        erewrite Memory.split_o in GET0; eauto. des_ifs.
        { ss. des; clarify. esplits. eauto. }
        { eauto. }
      }
    }
    { assert (WRITABLE: TView.writable tvw0.(TView.cur) sc loc (Time.incr (Memory.max_ts loc mem0)) ord).
      { econs. inv SIM. hexploit (VALS loc). i. des.
        eapply Memory.max_ts_spec in GET. des.
        eapply TimeFacts.le_lt_lt.
        { eapply MAX. }
        { eapply Time.incr_spec. }
      }
      hexploit (@Memory.add_exists mem0 loc (Memory.max_ts loc mem0) (Time.incr (Memory.max_ts loc mem0))); eauto.
      { i. eapply Memory.max_ts_spec in GET2. des.
        symmetry. eapply interval_le_disjoint. auto.
      }
      { eapply Time.incr_spec. }
      i. des.
      hexploit Memory.add_exists_le.
      { eapply LOCAL. }
      { eauto. }
      i. des. esplits.
      { econs; eauto.
        { econs; eauto.
          { econs; eauto. i. ss.
            hexploit Memory.max_ts_spec; eauto. i. des.
            eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply Time.incr_spec. }
            etrans.
            { eapply memory_get_ts_le. eauto. }
            { eauto. }
          }
          { hexploit Memory.remove_exists.
            { eapply Memory.add_get0. eapply H0. }
            i. des. eapply MemoryMerge.add_remove in H0; eauto.
            subst. eauto.
          }
        }
        { inv SIM. eauto. }
      }
      { ii. ss. destruct (Loc.eq_dec loc0 loc).
        { subst. eapply EMPTY in PROMISE. ss. }
        { rewrite write_tview_other_rlx; auto. inv SIM. eapply CONS; eauto. }
      }
      { inv SIM. eauto. }
      { eauto. }
    }
  }
  des. esplits; eauto. inv SIM. inv WRITE. ss. econs; eauto; ss.
  { i. destruct (Loc.eq_dec loc0 loc).
    { subst. eapply GET in GET0. des. eauto. }
    { erewrite Memory.write_get_diff_promise in GET0; eauto. }
  }
  { i. des_ifs.
    { rewrite write_tview_same_rlx; auto.
      esplits. eapply Memory.write_get2; eauto.
    }
    { rewrite write_tview_other_rlx; auto.
      erewrite Memory.write_get_diff; eauto.
    }
  }
  { i. des_ifs.
    rewrite write_tview_other_pln in MAX; auto.
    eapply write_unchanged_loc in WRITE0; eauto. des.
    eapply PERM; eauto. eapply unchanged_loc_max_readable; eauto.
  }
Qed.
