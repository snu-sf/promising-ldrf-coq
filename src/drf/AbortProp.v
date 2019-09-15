Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Set Implicit Arguments.



Inductive added_memory_imm (tm: TimeMap.t): Memory.t -> Memory.t -> Prop :=
| added_memory_imm_intro
    m0 loc to from val m1
    (TLE: Time.le (tm loc) to)
    (ADD: Memory.add m0 loc to from (Message.full val None) m1)
  :
    added_memory_imm tm m0 m1
.

Definition added_memory (tm: TimeMap.t) := rtc (added_memory_imm tm).

Lemma added_memory_future tm m0 m1
      (ADDED: added_memory tm m0 m1)
  :
    Memory.future m0 m1.
Proof.
  ginduction ADDED; auto. etrans; [| apply IHADDED].
  inv H. econs; eauto. econs; eauto.
  econs. ss. eapply Time.bot_spec.
Qed.

Definition is_cancel (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise _ _ _ _ Memory.op_kind_cancel => True
  | _ => False
  end.

Inductive only_reserves (proms: Memory.t): Prop :=
| only_reserves_intro
    (RESERVES: forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
        msg = Message.reserve)
    (FINITE: Memory.finite proms)
.

Lemma reserves_cancelable lang st vw proms sc mem0
      (RESERVES: only_reserves proms)
      (MLE: Memory.le proms mem0)
  :
    exists mem1,
      rtc (tau (@pred_step is_cancel lang))
          (Thread.mk lang st (Local.mk vw proms) sc mem0)
          (Thread.mk lang st (Local.mk vw Memory.bot) sc mem1).
Proof.
  inv RESERVES. unfold Memory.finite in *. des.
  ginduction dom; ss; i.
  - exists mem0. replace proms with Memory.bot; auto.
    eapply Memory.ext. i. rewrite Memory.bot_get.
    destruct (Memory.get loc ts proms) as [[from msg]|] eqn:GET; auto.
    exfalso. eauto.
  - destruct a as [loc' to'].
    destruct (Memory.get loc' to' proms) as [[from' msg']|] eqn:GET.
    + exploit RESERVES0; eauto. i. clarify.
      exploit Memory.remove_exists.
      { eapply GET. }
      intros [prom1 REMOVE0].
      exploit Memory.remove_exists.
      { eapply MLE. eapply GET. }
      intros [mem1 REMOVE1]. hexploit IHdom.
      * instantiate (1:=mem1). instantiate (1:=prom1).
        ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
        eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
      * i. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        eapply RESERVES0; eauto.
      * i. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        exploit FINITE; eauto. i. ss.
        des; ss; clarify.
      * i. des. exists mem2. econs 2.
        { econs.
          - instantiate (2:=ThreadEvent.promise loc' from' to' Message.reserve Memory.op_kind_cancel).
            econs; ss. econs. econs 1. econs; ss.
            econs; ss. econs; eauto.
          - ss. }
        eapply H.
    + eapply IHdom; eauto.
      i. exploit FINITE; eauto. i. des; clarify.
Qed.

Inductive lower_memory (mem_src mem_tgt: Memory.t): Prop :=
| lower_memory_intro
    (COVER: forall loc to (COV: covered loc to mem_src),
        covered loc to mem_tgt)
    (MLE: forall loc to from_tgt vw_tgt val
                 (GETTGT: Memory.get loc to mem_tgt = Some (from_tgt, Message.full val vw_tgt)),
        exists from_src vw_src,
          (<<GETSRC: Memory.get loc to mem_src = Some (from_src, Message.full val vw_src)>>) /\
          (<<VWLE: View.opt_le vw_src vw_tgt>>)).


Inductive lower_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| lower_event_silent:
    lower_event ThreadEvent.silent ThreadEvent.silent
| lower_event_syscall e:
    lower_event (ThreadEvent.syscall e) (ThreadEvent.syscall e)
| lower_event_failure:
    lower_event ThreadEvent.failure ThreadEvent.failure
| lower_event_fence ordr ordw:
    lower_event (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
| lower_event_read
    loc to val vw_src vw_tgt ordr
    (VWLE: View.opt_le vw_src vw_tgt)
  :
    lower_event
      (ThreadEvent.read loc to val vw_src ordr)
      (ThreadEvent.read loc to val vw_tgt ordr)
| lower_event_write
    loc from to val vw_src vw_tgt ordw
    (VWLE: View.opt_le vw_src vw_tgt)
  :
    lower_event
      (ThreadEvent.write loc from to val vw_src ordw)
      (ThreadEvent.write loc from to val vw_tgt ordw)
| lower_event_update
    loc from to valr valw vwr_src vwr_tgt vww_src vww_tgt ordr ordw
    (VWRLE: View.opt_le vwr_src vwr_tgt)
    (VWWLE: View.opt_le vww_src vww_tgt)
  :
    lower_event
      (ThreadEvent.update loc from to valr valw vwr_src vww_src ordr ordw)
      (ThreadEvent.update loc from to valr valw vwr_tgt vww_tgt ordr ordw)
| lower_event_promise
    loc from to msg kind
  :
    lower_event
      (ThreadEvent.promise loc from to msg kind)
      (ThreadEvent.promise loc from to msg kind)
.
Hint Constructors lower_event.

Lemma lower_memory_closed_message msg mem_src mem_tgt
      (LOWMEM: lower_memory mem_src mem_tgt)
      (CLOSED: Memory.closed_message msg mem_tgt)
  :
    Memory.closed_message msg mem_src.
Proof.
  inv CLOSED; eauto. inv CLOSED0; eauto. econs. econs.
  inv CLOSED. inv LOWMEM. econs.
  - ii. specialize (PLN loc). des.
    eapply MLE in PLN. des. esplits; eauto.
  - ii. specialize (RLX loc). des.
    eapply MLE in RLX. des. esplits; eauto.
Qed.

Lemma promise_consistent_mon v_src v_tgt prom
      (CONSISTENT: Local.promise_consistent (Local.mk v_tgt prom))
      (VWLE: TView.le v_src v_tgt)
  :
    Local.promise_consistent (Local.mk v_src prom).
Proof.
  ii. ss. exploit CONSISTENT; eauto. i. ss.
  eapply TimeFacts.le_lt_lt; eauto. eapply VWLE.
Qed.

Lemma lower_memory_promise mem_src0 mem_tgt0 prom0
      loc from to msg prom1 mem_tgt1 kind
      (LOWMEM: lower_memory mem_src0 mem_tgt0)
      (MLESRC: Memory.le prom0 mem_src0)
      (MLETGT: Memory.le prom0 mem_tgt0)
      (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
  :
    exists mem_src1,
      (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<LOWMEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
Admitted.

Lemma lower_memory_write mem_src0 mem_tgt0 prom0
      loc from to val vw_src vw_tgt prom1 mem_tgt1 kind
      (LOWMEM: lower_memory mem_src0 mem_tgt0)
      (MLESRC: Memory.le prom0 mem_src0)
      (MLETGT: Memory.le prom0 mem_tgt0)
      (VWLE: View.opt_le vw_src vw_tgt)
      (VWWF: View.opt_wf vw_src)
      (PROMISE: Memory.write prom0 mem_tgt0 loc from to val vw_tgt prom1 mem_tgt1 kind)
  :
    exists mem_src1,
      (<<PROMISE: Memory.write prom0 mem_src0 loc from to val vw_src prom1 mem_src1 kind>>) /\
      (<<LOWMEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
Admitted.

Lemma tview_read_fence_wf
      ord tview
      (WF_TVIEW: TView.wf tview)
  :
    TView.wf (TView.read_fence_tview tview ord).
Proof.
  econs; ss; eauto.
  - i. eapply WF_TVIEW.
  - des_ifs; eapply WF_TVIEW.
  - eapply WF_TVIEW.
  - i. des_ifs; try eapply WF_TVIEW.
    etrans; eapply WF_TVIEW.
  - des_ifs; try eapply WF_TVIEW. refl.
Qed.

Lemma lower_memory_step
      lang prom th_src th_tgt th_tgt' st st' v_src v_tgt v_tgt' prom' sc_src sc_tgt sc_tgt'
      mem_src mem_tgt mem_tgt' tf e_tgt
      (VWFSRC: TView.wf v_src)
      (VWFTGT: TView.wf v_tgt)
      (VIEW: TView.le v_src v_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v_src prom) sc_src mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v_tgt prom) sc_tgt mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v_tgt' prom') sc_tgt' mem_tgt')
      (LOWMEM: lower_memory mem_src mem_tgt)
      (MLESRC: Memory.le prom mem_src)
      (MLETGT: Memory.le prom mem_tgt)
      (STEP: Thread.step tf e_tgt th_tgt th_tgt')
  :
    exists e_src v_src' mem_src' sc_src',
      (<<STEP: Thread.step
                 tf e_src th_src
                 (Thread.mk lang st' (Local.mk v_src' prom') sc_src' mem_src')>>) /\
      (<<VIEW: TView.le v_src' v_tgt'>>) /\
      (<<LOWMEM: lower_memory mem_src' mem_tgt'>>) /\
      (<<EVT: lower_event e_src e_tgt>>) /\
      (<<SC: TimeMap.le sc_src' sc_tgt'>>)
.
Proof.
  clarify. inv STEP.
  - inv STEP0. inv LOCAL. clarify. ss.
    exploit lower_memory_promise; eauto. i. des. esplits; eauto.
    econs; eauto. econs 1; eauto. econs; eauto.
    eapply lower_memory_closed_message; eauto.
  - inv STEP0. inv LOCAL.
    + exists ThreadEvent.silent. esplits; eauto.
      econs 2; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify. dup LOWMEM. inv LOWMEM.
      exploit MLE; eauto. i. des.
      exists (ThreadEvent.read loc ts val vw_src ord). esplits; eauto.
      * econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        eapply TViewFacts.readable_mon; eauto.
        { inv VIEW. eauto. }
        { refl. }
      * ss. eapply TViewFacts.read_tview_mon; eauto.
        { eapply Cell.get_opt_wf in GET. inv GET. eauto. }
        { refl. }
    + inv LOCAL0. ss. clarify.
      assert (RELEASEDLE:
                View.opt_le
                  (TView.write_released v_src sc_src loc to None ord)
                  (TView.write_released v_tgt sc_tgt loc to None ord)).
      { eapply TViewFacts.write_released_mon; eauto. refl. }
      exploit lower_memory_write; eauto.
      { eapply TViewFacts.write_future0; eauto. } i. des.
      dup LOWMEM. inv LOWMEM.
      exists (ThreadEvent.write loc from to val (TView.write_released v_src sc_src loc to None ord) ord).
      esplits; eauto.
      * econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        eapply TViewFacts.writable_mon; eauto.
        { inv VIEW. eauto. }
        { refl. }
      * ss. eapply TViewFacts.write_tview_mon; eauto. refl.
    + inv LOCAL1. inv LOCAL2. ss. clarify.
      dup LOWMEM. inv LOWMEM.
      exploit MLE; eauto. i. des.
      exists (ThreadEvent.update
                loc tsr tsw valr valw vw_src
                (TView.write_released (TView.read_tview v_src loc tsr vw_src ordr) sc_src loc tsw
                                      vw_src ordw) ordr ordw).
      assert (RELEASEDLE: View.opt_le
                            (TView.write_released (TView.read_tview v_src loc tsr vw_src ordr) sc_src loc tsw vw_src ordw)
                            (TView.write_released (TView.read_tview v_tgt loc tsr releasedr ordr) sc_tgt loc tsw
                                                  releasedr ordw)).
      { dup GET. eapply Cell.get_opt_wf in GET. inv GET.
        eapply TViewFacts.write_released_mon; try eassumption.
        - eapply TViewFacts.read_tview_mon; eauto. refl.
        - eapply TViewFacts.read_future1; eauto.
        - refl. }
      exploit lower_memory_write; try apply WRITE; try eassumption.
      { dup GETSRC. eapply Cell.get_opt_wf in GETSRC. inv GETSRC.
        ss. eapply TViewFacts.write_future0; eauto.
        eapply TViewFacts.read_future1; eauto. }
      i. des.
      esplits; eauto.
      * econs 2; eauto. econs; eauto. econs; eauto.
        { econs; eauto. ss.
          eapply TViewFacts.readable_mon; eauto.
          - eapply VIEW; eauto.
          - refl. }
        { econs; eauto. ss.
          eapply TViewFacts.writable_mon; eauto.
          - eapply View.join_le.
            + eapply View.join_le; eauto.
              * eapply VIEW.
              * refl.
            + des_ifs.
              * eapply View.unwrap_opt_le; eauto.
              * refl.
          - refl. }
      * ss. eapply TViewFacts.write_tview_mon; eauto.
        { eapply TViewFacts.read_tview_mon; eauto.
          - dup GET. eapply Cell.get_opt_wf in GET. inv GET. eauto.
          - refl. }
        { eapply TViewFacts.read_future1; eauto.
          dup GET. eapply Cell.get_opt_wf in GET. inv GET. eauto. }
        { refl. }
    + inv LOCAL0. ss. clarify. esplits; eauto.
      * econs 2; eauto. econs; eauto.
      * ss. eapply TViewFacts.write_fence_tview_mon; eauto.
        { eapply TViewFacts.read_fence_tview_mon; eauto. refl. }
        { refl. }
        { eapply tview_read_fence_wf; eauto. }
      * ss. eapply TViewFacts.write_fence_sc_mon; eauto.
        { eapply TViewFacts.read_fence_tview_mon; eauto. refl. }
        { refl. }
    + inv LOCAL0. ss. clarify. esplits; eauto.
      * econs 2; eauto. econs; eauto.
      * ss. eapply TViewFacts.write_fence_tview_mon; eauto.
        { eapply TViewFacts.read_fence_tview_mon; eauto. }
        { eapply tview_read_fence_wf; eauto. }
      * ss. eapply TViewFacts.write_fence_sc_mon; eauto.
        { eapply TViewFacts.read_fence_tview_mon; eauto. }
    + inv LOCAL0. ss. clarify. esplits; eauto.
      * econs 2; eauto. econs; eauto. econs; eauto.
        econs; eauto. eapply promise_consistent_mon; eauto.
Qed.

Lemma progressable_in_added_rtc
      lang st lc sc0 sc1 m0 m1 tm
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 m0))
      (FUTURE: Memory.future m0 m1)
  :
    exists m2 e2,
      (<<ADDED: rtc (added_memory tm) m1 m2>>) /\
      (<<STEPS: rtc (Thread.tau_step (lang:=lang))
                    (Thread.mk _ st lc sc1 m1) e2>>) /\
      (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>).
Proof.
Admitted.

Definition same_locs_memory (L: Loc.t -> Prop) (mem_src mem_tgt: Memory.t): Prop :=
  forall loc (SAT: L loc) to,
    Memory.get loc to mem_src = Memory.get loc to mem_tgt.

Definition locs_in (L: Loc.t -> Prop) (e : ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc _ _ _ _ => L loc
  | ThreadEvent.read loc _ _ _ _ => L loc
  | ThreadEvent.write loc _ _ _ _ _ => L loc
  | ThreadEvent.update loc _ _ _ _ _ _ _ _=> L loc
  | _ => True
  end.

Lemma same_locs_memory_remove L mem_src0 mem_tgt0
      loc from to msg mem_tgt1
      (SAMELOCS: same_locs_memory L mem_src0 mem_tgt0)
      (REMOVE: Memory.remove mem_tgt0 loc from to msg mem_tgt1)
      (SAT: L loc)
  :
    exists mem_src1,
      (<<REMOVE: Memory.remove mem_src0 loc from to msg mem_src1>>) /\
      (<<SAMELOCS: same_locs_memory L mem_src1 mem_tgt1>>).
Proof.
  exploit Memory.remove_get0; eauto. i. des.
  exploit Memory.remove_exists.
  - erewrite SAMELOCS; eauto.
  - i. des. esplits; eauto.
    ii. erewrite (@Memory.remove_o mem2); eauto.
    erewrite (@Memory.remove_o mem_tgt1); cycle 1; eauto.
    des_ifs. eapply SAMELOCS; eauto.
Qed.

Lemma same_locs_memory_promise L mem_src0 mem_tgt0 prom0
      loc from to msg prom1 mem_tgt1 kind
      (SAMELOCS: same_locs_memory L mem_src0 mem_tgt0)
      (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
      (SAT: L loc)
  :
    exists mem_src1,
      (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<SAMELOCS: same_locs_memory L mem_src1 mem_tgt1>>).
Proof.
  inv PROMISE.
  - dup MEM. inv MEM0. inv ADD.
    exploit Memory.add_exists.
    + instantiate (1:=to). instantiate (1:=from).
      instantiate (1:=mem_src0). instantiate (1:=loc).
      ii. exploit SAMELOCS; eauto.
      unfold Memory.get, Cell.get. i.
      eapply DISJOINT; eauto. erewrite <- x0. eauto.
    + eauto.
    + eauto.
    + i. des. exists mem2. esplits; eauto.
      * econs 1; eauto. i.
Admitted.

Lemma same_locs_memory_write L mem_src0 mem_tgt0 prom0
      loc from to val vw prom1 mem_tgt1 kind
      (SAMELOCS: same_locs_memory L mem_src0 mem_tgt0)
      (PROMISE: Memory.write prom0 mem_tgt0 loc from to val vw prom1 mem_tgt1 kind)
      (SAT: L loc)
  :
    exists mem_src1,
      (<<PROMISE: Memory.write prom0 mem_src0 loc from to val vw prom1 mem_src1 kind>>) /\
      (<<SAMELOCS: same_locs_memory L mem_src1 mem_tgt1>>).
Proof.
  inv PROMISE. exploit same_locs_memory_promise; eauto. i. des.
  esplits; eauto.
Qed.

Lemma same_locs_memory_step
      L lang prom th_src th_tgt th_tgt' st st' v v' prom' sc sc'
      mem_src mem_tgt mem_tgt' tf e
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (SAMELOCS: same_locs_memory L mem_src mem_tgt)
      (STEP: pred_step (locs_in L) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: Thread.step
                 tf e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<SAMELOCS: same_locs_memory L mem_src' mem_tgt' >>)
.
Proof.
  clarify. inv STEP. inv STEP0. inv STEP.
  - inv STEP0. inv LOCAL. ss. clarify.
    exploit same_locs_memory_promise; eauto. i. des.
    exists mem_src1. esplits; eauto.
    econs 1; eauto. econs; eauto.
    + econs; eauto. eauto.
Admitted.
