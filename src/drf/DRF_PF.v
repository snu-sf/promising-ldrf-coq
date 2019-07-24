Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import PF.
Require Import Race.
Require Import SimWhole.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Set Implicit Arguments.

Inductive unchanged_on (P: Loc.t -> Time.t -> Prop) m0 m1 : Prop :=
| unchanged_on_intro
    (NCOV: forall l t (IN: P l t), ~ covered l t m1)
    (FUTURE : Memory.le m0 m1)
.

(* Definition to_thread (st: StateLocal.t) sc m := *)
(*   Thread.mk st.(StateLocal.lang) st.(StateLocal.state) st.(StateLocal.local) sc m. *)


Inductive promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
| promised_intro
    msg
    (GET: Memory.get loc to mem = Some msg)
  :
    promised mem loc to
.

Inductive promised_loc (mem: Memory.t) (loc: Loc.t) : Prop :=
| promised_loc_intro
    to
    (PROMISED: promised mem loc to)
  :
    promised_loc mem loc
.

Inductive all_promises (c: Configuration.t) (P: IdentMap.key -> Prop)
          (l: Loc.t) (t: Time.t) : Prop :=
| all_promises_intro
    tid st lc
    (TID1: IdentMap.find tid c.(Configuration.threads) = Some (st, lc))
    (PROISED: promised lc.(Local.promises) l t)
    (SAT: P tid)
.

Module Forget.

  Inductive forget_statelocal:
    sigT Language.state * Local.t -> sigT Language.state * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc1 lc2
      (TVIEW : lc1.(Local.tview) = lc2.(Local.tview))
      (PROMS : lc1.(Local.promises) = Memory.bot)
    :
      forget_statelocal (st, lc1) (st, lc2)
  .
  
  Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (* (FUTURE: Memory.le msrc mtgt) *)
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .
  
  Inductive forget_config csrc ctgt : Prop :=
  | forget_configuration_intro
      (THS : forall tid, option_rel
                           forget_statelocal 
                           (IdentMap.find tid csrc.(Configuration.threads))
                           (IdentMap.find tid ctgt.(Configuration.threads)))
      (SC : csrc.(Configuration.sc) = ctgt.(Configuration.sc))
      (MEM : forget_memory
               (all_promises ctgt (fun _ => True))
               csrc.(Configuration.memory) ctgt.(Configuration.memory))
  .
  
End Forget.

Lemma forget_memory_le P msrc mtgt
      (FORGET: Forget.forget_memory P msrc mtgt)
  :
    Memory.le msrc mtgt.
Proof.
  inv FORGET. ii.
  destruct (classic (P loc to)).
  - exploit FORGET0; eauto.
    i. clarify.
  - exploit COMPLETE; eauto.
    i. rewrite LHS in *. auto.
Qed.

Lemma memory_le_get_none msrc mtgt loc to
      (MLE: Memory.le msrc mtgt)
      (NONE: Memory.get loc to mtgt = None)
  :
    Memory.get loc to msrc = None.
Proof.
  destruct (Memory.get loc to msrc) eqn:GET; auto.
  destruct p. eapply MLE in GET. clarify.
Qed.

Lemma memory_le_covered msrc mtgt loc to
      (MLE: Memory.le msrc mtgt)
      (COVERED: covered loc to msrc)
  :
    covered loc to mtgt.
Proof.
  inv COVERED. econs; eauto.
Qed.

Module Inv.
  
  Inductive t lang (st: Language.state lang) lc
            (proms: Memory.t) (updates : Loc.t -> Prop) (mlast: Memory.t): Prop :=
  | inv_intro
      (PROMS: forall
          l m sc (PROM : promised_loc proms l)
          (FUTURE: unchanged_on
                     ((fun loc to => covered loc to proms) \2/ (fun loc _ => updates loc))
                     mlast m),          
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@Thread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<WRITING : is_writing _ st' l Ordering.relaxed>>))
      (UPDATE : forall
          l m sc (UPD : updates l)
          (FUTURE: unchanged_on
                     ((fun loc to => covered loc to proms) \2/ (fun loc _ => updates loc))
                     mlast m),          
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@Thread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_reading _ st' l Ordering.relaxed>>)
      (* /\ (<<WRITING : is_reading _ st' l Ordering.acqrel>>) *)
      )
  .

End Inv.




Inductive opt_pred_step P (lang : Language.t)
  : ThreadEvent.t -> Thread.t lang -> Thread.t lang -> Prop :=
| step_none t: opt_pred_step P ThreadEvent.silent t t
| step_some
    e t0 t1
    (STEP: pred_step P e t0 t1)
  :
    opt_pred_step P e t0 t1.
Hint Constructors opt_pred_step.

Definition promise_view_consistent (lc: Local.t): Prop :=
  forall
    loc to msg
    (GET: Memory.get loc to lc.(Local.promises) = Some msg),
    Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) to.    

Lemma promise_view_consistent_le tv0 tv1 prm
      (VLE: TView.le tv0 tv1)
      (CONS: promise_view_consistent (Local.mk tv1 prm))
  :
    promise_view_consistent (Local.mk tv0 prm).
Proof.
  ii. exploit CONS; eauto. i. ss.
  inv VLE. inv CUR. specialize (RLX loc).
  clear - RLX x. inv RLX.
  - etrans; eauto.
  - rewrite H in *. auto.
Qed.

Lemma promise_view_consistent_write lang (st0 st1: Language.state lang) lc0 lc1
      sc0 sc1 m0 m1 loc tsr tsw valw releasedr releasedw ordw kind
      (STEP: Local.write_step
               lc0 sc0 m0 loc
               tsr tsw valw releasedr releasedw ordw lc1 sc1 m1 kind)
      (WF1: Local.wf lc0 m0)
      (SC1: Memory.closed_timemap sc0 m0)
      (RVwF: View.opt_wf releasedr)
      (RVCLOSED: Memory.closed_opt_view releasedr m0)
      (CLOSED1: Memory.closed m0)
      (CONSISTENT: promise_view_consistent lc1)
  :
    promise_view_consistent lc0.    
Proof.
  exploit Local.write_step_future; eauto. i. des.
  inv STEP. inv WRITE. inv PROMISE; ss.
  - exploit MemoryFacts.MemoryFacts.add_remove_eq.
    { eapply PROMISES. }
    { eapply REMOVE. }
    i. clarify. eapply promise_view_consistent_le; eauto.
  - ii. destruct (loc_ts_eq_dec (loc0, to) (loc, tsw)).
    + des. ss. clarify. inv WRITABLE. eauto.
    + destruct (TimeSet.Facts.eq_dec to tsw).
      * exploit CONSISTENT; ss; eauto.
        { instantiate (1:=msg). instantiate (1:=to). instantiate (1:=loc0).
          erewrite Memory.remove_o; eauto.
          erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify. }
        { i. eapply TimeFacts.le_lt_lt; eauto. eapply TimeMap.join_l. }
      * destruct (loc_ts_eq_dec (loc0, to) (loc, ts3)).
        { exploit CONSISTENT; ss; eauto.
          - instantiate (2:=to). instantiate (2:=loc0).
            erewrite Memory.remove_o; eauto.
            erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify.
          - i. eapply TimeFacts.le_lt_lt; eauto. eapply TimeMap.join_l. }
        { exploit CONSISTENT; ss; eauto.
          - instantiate (2:=to). instantiate (2:=loc0).
            erewrite Memory.remove_o; eauto.
            erewrite Memory.split_o; eauto. des_if.
            + ss. des; clarify.
            + simpl in *. des_if; cycle 1.
              * eauto.
              * des; ss; clarify.
          - i. eapply TimeFacts.le_lt_lt; eauto. eapply TimeMap.join_l. }
  - ii. destruct (loc_ts_eq_dec (loc0, to) (loc, tsw)).
    + des. ss. clarify. inv WRITABLE. eauto.
    + exploit CONSISTENT; ss; eauto.
      * instantiate (1:=msg). instantiate (1:=to). instantiate (1:=loc0).
        erewrite Memory.remove_o; eauto.
        erewrite Memory.lower_o; eauto. des_ifs; ss; des; clarify.
      * i. eapply TimeFacts.le_lt_lt; eauto. eapply TimeMap.join_l.
Qed.

Lemma promise_view_consistent_step lang (st0 st1: Language.state lang) lc0 lc1
      sc0 sc1 m0 m1 pf e
      (WF1: Local.wf lc0 m0)
      (SC1: Memory.closed_timemap sc0 m0)
      (CLOSED1: Memory.closed m0)
      (CONSISTENT: promise_view_consistent lc1)
      (STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 m0) (Thread.mk _ st1 lc1 sc1 m1))
  :
    promise_view_consistent lc0.    
Proof.
  exploit Thread.step_future; eauto; ss. i. des.
  inv STEP; ss.
  - inv STEP0. inv LOCAL. ii. destruct msg0.
    exploit Memory.promise_get1_promise; eauto. i. des.
    exploit CONSISTENT; ss; eauto.
  - inv STEP0. destruct lc0, lc1. inv LOCAL; ss; eauto.
    + inv LOCAL0; ss. clarify.
      eapply promise_view_consistent_le; eauto.
    + eapply promise_view_consistent_write; eauto.
    + exploit Local.read_step_future; eauto. i. des.
      hexploit promise_view_consistent_write; eauto.
      inv LOCAL1. ss. i.
      eapply promise_view_consistent_le; eauto.
    + inv LOCAL0; ss. clarify.
      eapply promise_view_consistent_le; eauto.
    + inv LOCAL0; ss. clarify.
      eapply promise_view_consistent_le; eauto.
Qed.

Lemma inhabited_future mem1 mem2
      (FUTURE: Memory.future mem1 mem2)
      (INHABITED: Memory.inhabited mem1)
  :
    Memory.inhabited mem2.
Proof.
  induction FUTURE; auto. apply IHFUTURE.
  inv H. hexploit Memory.op_inhabited; eauto.
Qed.

Lemma thread_consistent_view_consistent lang st lc sc mem
      (CLOSED1: Memory.closed mem)
      (INHABITED: Memory.inhabited mem)
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem))
  :
    promise_view_consistent lc.    
Proof.
  exploit Memory.cap_exists; eauto. instantiate (1:=lc.(Local.promises)). i. des.
  hexploit inhabited_future; eauto. i. 
  exploit Memory.max_full_timemap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des. ss.
  assert (CONSISTENT1: promise_view_consistent (Thread.local e2)).
  { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. clarify. }
Admitted.  

Lemma self_promise_remove_promise
      prom prom' mem_src mem_tgt mem_tgt' loc from to msg kind
      (MEM: Forget.forget_memory (promised prom) mem_src mem_tgt)
      (PROMISE: Memory.promise prom mem_tgt loc from to msg prom' mem_tgt' kind)
  :
    Forget.forget_memory (promised prom') mem_src mem_tgt'.
Proof.
  dup MEM. eapply forget_memory_le in MEM0. inv MEM. inv PROMISE.
  - econs; eauto.
    * i. rewrite COMPLETE.
      { symmetry. erewrite Memory.add_o; eauto. des_ifs.
        - ss. des. clarify. exfalso. apply NPROMS.
          apply Memory.add_get0 in PROMISES. des.
          econs; eauto. }
      { ii. inv H. eapply NPROMS.
        exploit Memory.add_o; try apply PROMISES; eauto. i.
        erewrite GET in *. des_ifs.
        - econs; eauto.
        - econs; eauto. }            
    * i. inv PROMS. destruct msg0.
      erewrite Memory.add_o in GET; eauto. des_ifs.
      { ss. des. clarify.
        eapply memory_le_get_none; eauto.
        apply Memory.add_get0 in MEM. des. eauto. }
      { eapply FORGET. econs; eauto. }
  - econs; eauto.
    * i. rewrite COMPLETE.
      { symmetry. erewrite Memory.split_o; eauto. des_ifs.
        - ss. des. clarify. exfalso. apply NPROMS.
          apply Memory.split_get0 in PROMISES. des.
          econs; eauto.
        - ss. destruct a. clarify. exfalso. apply NPROMS.
          apply Memory.split_get0 in PROMISES.
          econs; des; eauto. }
      { ii. inv H. eapply NPROMS.
        exploit Memory.split_o; try apply PROMISES; eauto. i.
        erewrite GET in *. des_ifs.
        - econs; eauto.
        - econs; eauto.
        - econs; eauto. }            
    * i. inv PROMS. destruct msg0.
      erewrite Memory.split_o in GET; eauto. des_ifs.
      { ss. des. clarify.
        eapply memory_le_get_none; eauto.
        apply Memory.split_get0 in MEM. des. eauto. }
      { ss. destruct a. clarify.
        eapply FORGET. apply Memory.split_get0 in PROMISES.
        econs. des; eauto. }
      { eapply FORGET. econs; eauto. }
  - econs; eauto.
    * i. rewrite COMPLETE.
      { symmetry. erewrite Memory.lower_o; eauto. des_ifs.
        - ss. des. clarify. exfalso. apply NPROMS.
          apply Memory.lower_get0 in PROMISES. des.
          econs; eauto. }
      { ii. inv H. eapply NPROMS.
        exploit Memory.lower_o; try apply PROMISES; eauto. i.
        erewrite GET in *. des_ifs.
        - econs; eauto.
        - econs; eauto. }
    * i. inv PROMS. destruct msg1.
      erewrite Memory.lower_o in GET; eauto. des_ifs.
      { ss. des. clarify. eapply FORGET.
        apply Memory.lower_get0 in PROMISES. des. econs. eauto. }
      { eapply FORGET. apply Memory.lower_get0 in PROMISES.
        econs. des; eauto. }
Qed.

Lemma consistent_read_no_self_promise_read
      v v' prom prom'
      mem_tgt loc ts val released ord
      (STEP: Local.read_step (Local.mk v prom) mem_tgt loc
             ts val released ord (Local.mk v' prom'))
      (CONSISTENT: promise_view_consistent (Local.mk v' prom'))
  :
    ~ prom.(promised) loc ts.
Proof.
  ii. inv H. inv STEP. ss. clarify.
  exploit CONSISTENT; ss; eauto. ss.
  unfold TimeMap.join. i.
  apply TimeFacts.join_lt_des in x. des.
  apply TimeFacts.join_lt_des in AC. des.
  unfold View.singleton_ur_if, View.singleton_ur in *. clear - BC0. des_ifs; ss.
  * unfold TimeMap.singleton in *.
    setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
  * unfold TimeMap.singleton in *.
    setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
Qed.

Lemma consistent_read_no_self_promise
      lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_tgt mem_tgt' e_tgt
      (LOCALWF: Local.wf (Local.mk v prom) mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (SC: Memory.closed_timemap sc mem_tgt)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (CONSISTENT: promise_view_consistent (Local.mk v' prom'))
      (STEP: Thread.step_allpf e_tgt th_tgt th_tgt')
  :
    no_read_msgs prom.(promised) e_tgt.
Proof.
  inv STEP. inv STEP0; ss.
  - inv STEP. ss.
  - inv STEP. inv LOCAL; ss.
    + ii. exploit consistent_read_no_self_promise_read; eauto.
    + ii. destruct lc2. hexploit consistent_read_no_self_promise_read; eauto.
      exploit Local.read_step_future; eauto. i. des.
      eapply promise_view_consistent_write; eauto.
Qed.

Lemma write_succeed mem1 loc from1 to1 val released
      (NCOVER: forall t (COVER: covered loc t mem1),
          ~ Interval.mem (from1, to1) t)
      (TO: Time.le (View.rlx (View.unwrap released) loc) to1)
      (FROMTO: Time.lt from1 to1)
      (MSGWF: Message.wf (Message.full val released))
  :
    exists mem2,
      (<<WRITE: Memory.write Memory.bot mem1 loc from1 to1 val released Memory.bot mem2 Memory.op_kind_add>>).
Proof.
  exploit Memory.add_exists; eauto.
  { instantiate (1:=mem1). instantiate (1:=loc).
    ii. eapply NCOVER; eauto. econs; eauto. }
  i. des. exists mem2.
  exploit Memory.add_exists; eauto.
  { instantiate (1:=Memory.bot). instantiate (1:=loc).
    ii. rewrite Memory.bot_get in *. clarify. } i. des.
  econs.
  - econs; eauto; ss.
  - exploit Memory.remove_exists; eauto.
    { eapply Memory.add_get0 in x1. des. eauto. } i. des.
    exploit MemoryFacts.MemoryFacts.add_remove_eq; eauto.
    i. clarify.
Qed.

Lemma self_promise_remove_write


  Local.write_step {| Local.tview := v; Local.promises := prom |} sc mem_tgt
             loc from to val None released ord
             {| Local.tview := v'; Local.promises := prom' |} sc' mem_tgt' kind

Lemma self_promise_remove
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: Forget.forget_memory (promised prom) mem_src mem_tgt)
      (STEP: (@pred_step (P /1\ no_read_msgs prom.(promised)) lang) e_tgt th_tgt th_tgt')
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (P /1\ no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\ 
      (<<MEM: Forget.forget_memory (promised prom') mem_src' mem_tgt'>>).
Proof.
  dup MEM. eapply forget_memory_le in MEM0.  
  clarify. inv STEP. des. inv STEP0. inv STEP.
  - inv STEP0. ss. inv LOCAL. clarify. ss.
    exists mem_src, ThreadEvent.silent. esplits; eauto.
    eapply self_promise_remove_promise; eauto.
  - inv STEP0. ss. inv LOCAL; clarify; ss.
    + exists mem_src, ThreadEvent.silent.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + exists mem_src, (ThreadEvent.read loc ts val released ord).
      inv LOCAL0. ss. clarify.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      inv MEM. rewrite COMPLETE; eauto.
    + admit.


      (* exploit Local.write_step_future; eauto. *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } i. des. *)

      inv LOCAL0. ss. clarify.
      exploit write_succeed; eauto.
      { instantiate (1:=to). instantiate (1:=from). instantiate (1:=mem_src).
        instantiate (1:=loc).
        admit. }
      {


        admit. }
      { admit. }
      { admit. }

      i. des.
      exists mem2. exists (ThreadEvent.write
                             loc from to val
                             (TView.write_released v sc loc to None ord) ord).
      esplits; eauto.
      * econs. econs; ss. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; ss; eauto. ii.
        erewrite Memory.bot_get in GET. clarify.
      * econs; eauto.
        { admit. }
      
      
      Memory.write admit.
    + admit.
    + inv LOCAL0. ss. clarify.
      exists mem_src, (ThreadEvent.fence ordr ordw).
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
      ii. rewrite Memory.bot_get in *. clarify.
    + inv LOCAL0. ss. clarify.
      exists mem_src, (ThreadEvent.syscall e).
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
      ii. rewrite Memory.bot_get in *. clarify.
Admitted.
      inv MEM. 

      

Local.write_step {| Local.tview := tview; Local.promises := promises |} sc
             mem_tgt loc tsr tsw valw releasedr releasedw ordw
             {| Local.tview := v'; Local.promises := prom' |} sc' mem_tgt' kind
      

      ii. inv H. inv LOCAL0. ss. clarify.
      exploit CONSISTENT; eauto. ss.
      unfold TimeMap.join. i.
      apply TimeFacts.join_lt_des in x. des.
      apply TimeFacts.join_lt_des in AC. des.
      unfold View.singleton_ur_if, View.singleton_ur in *. clear - BC0. des_ifs; ss.
      * unfold TimeMap.singleton in *.
        setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
      * unfold TimeMap.singleton in *.
        setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
    + ii. inv H.
      exploit Local.read_step_future; eauto. i. des.
      exploit Local.write_step_future; eauto. i. des. ss.
      inv LOCAL1. ss.
      exploit CONSISTENT; ss; eauto. ss.
      unfold TimeMap.join. i.
      apply TimeFacts.join_lt_des in x. des.
      apply TimeFacts.join_lt_des in AC. des.
      unfold View.singleton_ur_if, View.singleton_ur in *. clear - BC0. des_ifs; ss.
      * unfold TimeMap.singleton in *.
        setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
      * unfold TimeMap.singleton in *.
        setoid_rewrite LocFun.add_spec_eq in BC0. timetac.
    +



      inv LOCAL1.


      ii.
        
      des_ifs.
      * appl

      
      TimeMap.join
      
      unfold Time

      des_ifs.


      inv 
    
    no_read_msgs
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (P /1\ no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\ 
      (<<MEM: Forget.forget_memory (promised prom') mem_src' mem_tgt'>>).
Proof.
  dup MEM. eapply forget_memory_le in MEM0.  
  clarify. inv STEP. inv STEP0. inv STEP.
  - inv STEP0. ss. inv LOCAL. clarify. ss.
    exists mem_src, ThreadEvent.silent. esplits; eauto.
    eapply self_promise_remove_promise; eauto.
  - inv STEP0. ss. inv LOCAL; clarify; ss.
    + exists mem_src, ThreadEvent.silent.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + exists mem_src, (ThreadEvent.read loc ts val released ord).
      inv LOCAL0. ss. clarify.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      inv MEM. 

Thread.step_allpf e e2' e3>>) /\
                              (<<BREAKP : P e>>) /\ (<<BREAKQ : ~ Q e
      

Lemma self_promise_remove
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (CONSISTENT: Thread.consistent th_tgt')
      (MEM: Forget.forget_memory (promised prom) mem_src mem_tgt)
      (STEP: (@pred_step (P /1\ no_read_msgs prom.(promised)) lang) e_tgt th_tgt th_tgt')
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (P /1\ no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\ 
      (<<MEM: Forget.forget_memory (promised prom') mem_src' mem_tgt'>>).
Proof.
  dup MEM. eapply forget_memory_le in MEM0.  
  clarify. inv STEP. inv STEP0. inv STEP.
  - inv STEP0. ss. inv LOCAL. clarify. ss.
    exists mem_src, ThreadEvent.silent. esplits; eauto.
    eapply self_promise_remove_promise; eauto.
  - inv STEP0. ss. inv LOCAL; clarify; ss.
    + exists mem_src, ThreadEvent.silent.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + exists mem_src, (ThreadEvent.read loc ts val released ord).
      inv LOCAL0. ss. clarify.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      inv MEM. 


Lemma self_promise_remove
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (CONSISTENT: Thread.consistent th_tgt')
      (MEM: Forget.forget_memory (promised prom) mem_src mem_tgt)
      (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (P /1\ no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\ 
      (<<MEM: Forget.forget_memory (promised prom') mem_src' mem_tgt'>>).
Proof.
  dup MEM. eapply forget_memory_le in MEM0.  
  clarify. inv STEP. inv STEP0. inv STEP.
  - inv STEP0. ss. inv LOCAL. clarify. ss.
    exists mem_src, ThreadEvent.silent. esplits; eauto.
    eapply self_promise_remove_promise; eauto.
  - inv STEP0. ss. inv LOCAL; clarify; ss.
    + exists mem_src, ThreadEvent.silent.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + exists mem_src, (ThreadEvent.read loc ts val released ord).
      inv LOCAL0. ss. clarify.
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      inv MEM. 

      econs 2; eauto.
    + 
    

    inv MEM. inv PROMISE.
    + econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.add_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.add_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.add_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }            
      * i. inv PROMS. destruct msg0.
        erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.add_get0 in MEM. des. eauto. }
        { eapply FORGET. econs; eauto. }
    + econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.split_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES. des.
            econs; eauto.
          - ss. destruct a. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES.
            econs; des; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.split_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto.
          - econs; eauto. }            
      * i. inv PROMS. destruct msg0.
        erewrite Memory.split_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.split_get0 in MEM. des. eauto. }
        { ss. destruct a. clarify.
          eapply FORGET. apply Memory.split_get0 in PROMISES.
          econs. des; eauto. }
        { eapply FORGET. econs; eauto. }
    + econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.lower_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.lower_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.lower_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg1.
        erewrite Memory.lower_o in GET; eauto. des_ifs.
        { ss. des. clarify. eapply FORGET.
          apply Memory.lower_get0 in PROMISES. des. econs. eauto. }
        { eapply FORGET. apply Memory.lower_get0 in PROMISES.
          econs. des; eauto. }
  - inv STEP0. inv LOCAL; ss.
    + exists mem_src, ThreadEvent.silent. ss. esplits; eauto.
      econs. econs; ss; eauto. econs; eauto. econs 2; eauto.
    


    Mem.write


    
          eapply forget_memory_le

          admit. }
        { eapply FORGET; eauto. econs; eauto. }

          
          admit. 
        
        des_ifs.
          
          econs; eauto.
          erewrite Memory.add_o; eauto. des_ifs.
          ss. de
          \
                                                           

          apply Memory.add_get0 in PROMISES. des.
          econs; eauto. 

          econs

            rewrite GET0


          des
        
  
Admitted.
    
Lemma other_promise_remove
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc' mem_src mem_tgt proms mem_tgt' e
      (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
      (NOPRM: lc.(Local.promises) = Memory.bot)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
      (MEM: Forget.forget_memory proms mem_src mem_tgt)
      (STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms)
                         e th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory proms mem_src' mem_tgt'>>).
Proof.
  inv STEP. des. inv STEP0. inv STEP; inv STEP0; ss. inv LOCAL; ss.
  - exists mem_src. esplits; eauto.
    econs; eauto. econs. econs 2; eauto. econs; eauto.
  - exists mem_src. esplits; eauto.
    econs; eauto. econs. econs 2; eauto. econs; eauto. econs; eauto.
    inv LOCAL0. inv MEM. econs; eauto. erewrite COMPLETE; eauto.
  - inv LOCAL0. inv WRITE. inv PROMISE.
    + admit.
    + exfalso. rewrite NOPRM in *. clear - PROMISES. inv PROMISES. inv SPLIT.
      ss. unfold Cell.Raw.bot in *. rewrite IdentMap.Properties.F.empty_o in *. clarify.
    + exfalso. rewrite NOPRM in *. clear - PROMISES. inv PROMISES. inv LOWER.
      ss. unfold Cell.Raw.bot in *. rewrite IdentMap.Properties.F.empty_o in *. clarify.
  - admit.
  - exists mem_src. esplits; eauto.
    econs; eauto. econs. econs 2; eauto. econs; eauto.
  - exists mem_src. esplits; eauto.
    econs; eauto. econs. econs 2; eauto. econs; eauto.
Admitted.

Lemma self_promise_remove
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (CONSISTENT: Thread.consistent th_tgt')
      (MEM: Forget.forget_memory (fun loc to => covered loc to prom) mem_src mem_tgt)
      (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (P /1\ no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory (fun loc to => covered loc to prom') mem_src' mem_tgt'>>).
Proof.
Admitted.


opt_pred_step
  
  
      
Thread.consistent

Lemma consistent_no_read_self_promise
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc' mem_src mem_tgt proms mem_tgt' e
      (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
      (MEM: Forget.forget_memory proms mem_src mem_tgt)
      (STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms)
                         e th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory proms mem_src' mem_tgt'>>).
Proof.


Lemma other_promise_remove
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc' mem_src mem_tgt proms mem_tgt' e
      (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
      (MEM: Forget.forget_memory proms mem_src mem_tgt)
      (STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms)
                         e th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory proms mem_src' mem_tgt'>>).
Proof.

Lemma other_promise_remove
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc' mem_src mem_tgt proms mem_tgt' e
      (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
      (MEM: Forget.forget_memory proms mem_src mem_tgt)
      (STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms)
                         e th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory proms mem_src' mem_tgt'>>).
Proof.


Lemma local_step_view_incr lc1 lc2 e sc1 sc2 mem1 mem2
      (TVIEW: TView.wf (Local.tview lc1))
      (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2)
  :
    (<<INCR: TView.le (Local.tview lc1) (Local.tview lc2)>>) /\
    (<<TVIEW: TView.wf (Local.tview lc2)>>).
Proof.
  inv STEP.
  - split; auto. red. refl.
  - inv LOCAL; ss. split.
    + apply TViewFacts.read_tview_incr.
    + 
  - inv LOCAL; ss. apply TViewFacts.write_tview_incr.
Local.wf   
    
    
  
  :
    ~ promise_view_consistent lc1.    
Proof.




Lemma promise_view_inconsistent_step lang (st0 st1: Language.state lang) lc0 lc1
      sc0 sc1 m0 m1 pf e
      (INCONSISTENT: ~ promise_view_consistent lc0)
      (STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 m0) (Thread.mk _ st1 lc1 sc1 m1))
  :
    ~ promise_view_consistent lc1.    
Proof.
  inv STEP; ss.
  - inv STEP0. inv LOCAL. ii. eapply INCONSISTENT. ii. destruct msg0.
    exploit Memory.promise_get1_promise; eauto. i. des.
    exploit H; ss; eauto.
  - ii. inv STEP0. inv LOCAL; ss; eauto.
    + inv LOCAL0; ss.
TView.le      


  Admitt

      (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2)
      TViewl.le (Local.tview lc1) (Local.tview lc2)
      

    Thread.step

    + exploit Memory.promise_get1_promise; eauto.
      i.
    
  
  forall
    loc to msg
    (GET: Memory.get loc to lc.(Local.promises) = Some msg),
    Time.lt (lc.(Local.tview).(TView.cur).(View.pln) loc) to.    


Lemma self_promise_remove
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc' mem_src mem_tgt mem_tgt'
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: Forget.forget_memory (fun loc to => covered loc to prom) mem_src mem_tgt)
      (STEP: tau (@pred_step P lang) th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: rc (tau (@pred_step (P /1\ no_promise) lang)) th_src
                  (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory (fun loc to => covered loc to prom') mem_src' mem_tgt'>>).
Proof.
  clarify. inv STEP. inv TSTEP. inv STEP. inv STEP0.
  - inv STEP. inv LOCAL. ss. clarify.
    exists mem_src. splits.
    + right.
    + econs.
Admitted.



Lemma other_promise_remove
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc' mem_src mem_tgt proms mem_tgt' e
      (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
      (MEM: Forget.forget_memory proms mem_src mem_tgt)
      (STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms) e th_tgt th_tgt')
  :
    exists mem_src',
      (<<STEP: pred_step (P /1\ no_promise /1\ no_read_msgs proms)
                         e th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
      (<<MEM: Forget.forget_memory proms mem_src' mem_tgt'>>).
Proof.
  clarify. inv STEP. inv STEP0. inv STEP; des.
  - exfalso. inv STEP0. inv SAT1.
  - inv STEP0. inv LOCAL; (esplits; [econs; eauto; econs; right; econs; eauto|]); eauto.
    + econs 2; eauto.
      inv LOCAL0. econs; eauto.
      instantiate (1:= from).
      inv MEM.
Admitted.
  
Inductive sim_pf
          (mlast: Ident.t -> Memory.t) (updates: Ident.t -> (Loc.t -> Prop))
          (c_src c_tgt: Configuration.t) : Prop :=
| sim_pf_intro
    (FORGET: Forget.forget_config c_src c_tgt)
    (RACEFREE: pf_racefree c_src)
    (INV:
       forall
         tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
         (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                  Some (existT _ lang_src st_src, lc_src))
         (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
                  Some (existT _ lang_tgt st_tgt, lc_tgt)),
         Inv.t _ st_src lc_src lc_tgt.(Local.promises) (updates tid) (mlast tid))
    (FUTURE:
       forall tid lang_src st_src lc_src
              (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                       Some (existT _ lang_src st_src, lc_src)),
         unchanged_on
           (fun loc _ => (updates tid) loc)
           (mlast tid) c_src.(Configuration.memory))
    (WFSRC: Configuration.wf c_tgt)
    (WFTGT: Configuration.wf c_tgt)
.

Inductive sim_pf_all c_src c_tgt: Prop :=
| sim_pf_all_intro mlast updates (SIM : sim_pf mlast updates c_src c_tgt)
.

Lemma init_pf s tid st lc
      (TID: IdentMap.find tid (Threads.init s) = Some (st, lc))
  :
    Local.promises lc = Memory.bot.
Proof.
  unfold Threads.init in *. erewrite UsualFMapPositive.UsualPositiveMap.Facts.map_o in *.
  unfold option_map in *. des_ifs.
Qed.  
  
Lemma sim_pf_init
      s
      (RACEFREE: pf_racefree (Configuration.init s))
  :
    sim_pf_all (Configuration.init s) (Configuration.init s)
.
Proof.
  econs. instantiate (1:=fun _ _ => False). instantiate (1:=fun _ => Memory.init).
  econs; eauto; ss; i.
  - econs; i; ss.
    + unfold Threads.init in *. erewrite UsualFMapPositive.UsualPositiveMap.Facts.map_o in *.
      unfold option_map in *. des_ifs.      
    + econs; ss; eauto. ii. inv H.
      unfold Memory.get, Memory.init in *.
      rewrite Cell.init_get in *. des_ifs. inv ITV. ss. timetac.
  - unfold Threads.init in *. erewrite UsualFMapPositive.UsualPositiveMap.Facts.map_o in *.
    unfold option_map in *. des_ifs. econs; ss. i. exfalso.
    replace lc_src with Local.init in *; ss.
    + inv PROM. rewrite Memory.bot_get in GET. clarify.
    + inv TIDTGT. auto.
  - econs; ss.
  - apply Configuration.init_wf.
  - apply Configuration.init_wf.
Qed.

(* (* TODO *) *)
(* Lemma pf_step_hold_other *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid mlast skylast tf *)
(*       (SIM: sim_pf mlast skylast c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists th2_src th3_src, *)
(*       (<<STEPS_SRC: rtc (tau (@Thread.program_step _)) *)
(*                        (to_thread *)
(*                           (Threads.find tid c1_src.(Configuration.threads)) *)
(*                           c1_src.(Configuration.sc) *)
(*                           c1_src.(Configuration.memory)) *)
(*                        th2_src>>) /\ *)
(*       (<<STEP_SRC: opt_pftstep e th2_src th3_src>>) /\ *)
(*       (<<SC: th3_src.(Thread.sc) = c3_tgt.(Configuration.sc)>> /\ *)
(*             <<MEM: Forget.forget_memory *)
(*                      (all_promises c3_tgt) *)
(*                      th3_src.(Thread.memory) c3_tgt.(Configuration.memory)>>) /\ *)
(*       (<<ST: Forget.forget_state *)
(*               (StateLocal.mk _ th3_src.(Thread.state) th3_src.(Thread.local)) *)
(*               (Threads.find tid c3_tgt.(Configuration.threads))>>) /\ *)
(*       (<<HOLD: forall tid2 (NEQ : tid <> tid2), *)
(*                 Inv.hold *)
(*                   (Threads.find tid2 c1_src.(Configuration.threads)) *)
(*                   (Locked.t (c1_tgt.(Configuration.mpreds) tid2)) *)
(*                   ((Threads.find tid2 c3_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*                   (skylast tid2) *)
(*                   (mlast tid2) th3_src.(Thread.memory)>>). *)
(* Proof. *)
(* Admitted. *)

(* Lemma inv_monotone st proms sky updates mlast v0 v1 *)
(*       (LE: TimeMap.le v0 v1) *)
(*       (INV: Inv.t st proms sky updates mlast v1) *)
(*   : *)
(*     Inv.t st proms sky updates mlast v0. *)
(* Proof. *)
(*   inv INV. econs; i. *)
(*   - eapply PROMS; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(*   - eapply UPDATE; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(* Qed. *)

(* Lemma inv_hold_self *)
(*       st locked proms sky mem *)
(*       (SKY: TimeMap.le (Memory.max_timemap mem) sky) *)
(*       (PROM: forall l t, covered proms l t -> covered mem l t -> False) *)
(*   : *)
(*     Inv.hold st locked proms sky mem mem *)
(* . *)
(* Proof. *)
(*   ii. econs; i; ss; eauto. *)
(*   revert INV. induction FUTURE; ss; i.     *)
(*   clarify. unfold TimeMap.add in *. ss. *)
(*   des_ifs. *)
(*   - left. eapply TimeFacts.le_lt_lt; cycle 1; eauto. *)
(*     eapply IHFUTURE; ss. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(*   - eapply IHFUTURE; eauto. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(* Qed. *)

(* (* TODO *) *)
(* Lemma consistent_inhabited *)
(*       mlast skylast c_src c_tgt tid *)
(*       (FORGET: Forget.forget_config c_src c_tgt) *)
(*       (RACEFREE: pf_racefree c_src) *)
(*       (INHABITED: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.inhabited *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid')) *)
(*       (HOLD: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.hold *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid') c_src.(Configuration.memory)) *)
(*       (CONSISTENT: Thread.consistent *)
(*                      (c_tgt.(Configuration.mpreds) tid) *)
(*                      bot2 *)
(*                      (to_thread *)
(*                         (Threads.find tid c_tgt.(Configuration.threads)) *)
(*                         (c_tgt.(Configuration.sc)) *)
(*                         (c_tgt.(Configuration.memory)))) *)
(*   : *)
(*     Inv.inhabited *)
(*       (Threads.find tid c_src.(Configuration.threads)) *)
(*       (Locked.t (c_tgt.(Configuration.mpreds) tid)) *)
(*       ((Threads.find tid c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*       (Memory.max_timemap c_tgt.(Configuration.memory)) c_src.(Configuration.memory). *)
(* Admitted. *)


(* Definition not_stuck lang (st: Language.state lang) := *)
(*   exists st' e, Language.step _ e st st'. *)

(* Lemma same_add_same ths tid st *)
(*       (FIND: Threads.find tid ths = st) *)
(*       (STEP: not_stuck _ st.(StateLocal.state)) *)
(*   : *)
(*     Threads.add tid st ths = ths. *)
(* Proof. *)
(*   eapply IdentMap.eq_leibniz. ii. *)
(*   unfold Threads.find, Threads.add in *. *)
(*   rewrite IdentMap.Facts.add_o. des_ifs. *)
(*   exfalso. inv STEP. des. inv H. *)
(* Qed. *)

(* Ltac etatac := match goal with *)
(*                  [|- ?x = ?y] => *)
(*                  (try (destruct x; ss; clarify; eauto; fail));              *)
(*                  (try (destruct y; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction x; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction y; ss; clarify; eauto; fail)) *)
(*                end. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)

(*   assert (SIMPF: sim_pf_all *)
(*                    (Configuration.mk *)
(*                       (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                       (th3_src.(Thread.local)))  *)
(*                                    (Configuration.threads c1_src)) *)
(*                       (Configuration.sc c3_tgt) *)
(*                       th3_src.(Thread.memory) MPreds.init) *)
(*                    c3_tgt). *)

(*   { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         admit. *)
(*         (* inv STEPS_SRC0. *) *)
(*         (* econs; [|left]. econs. econs. econs; ss; eauto. *) *)
(*         (* etatac. *) *)
(*       } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
  
(*   eapply rtc_tail in STEPS_SRC. des. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)







(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf mlast skylast *)
(*       (SIM: sim_pf c1_src c1_tgt mlast skylast) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf *)
(*                 c3_src c3_tgt *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then c3_src.(Configuration.memory) else skylast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)

                
(* (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
                         
(*                          >>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)






(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = to_thread Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: Forget.forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: Forget.forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)

(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: Forget.forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: Forget.forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)
      
      
(*       Thread.step Thread.t st lc sc mem1  *)

(*       Thread.t *)
(*       Thread.step *)
(* Configuration.step *)

(* opt (Thread.step *)


(* Lemma sim_pf_sim_whole: *)
(*   sim_pf_all <2= (sim_whole (fun _ => pftstep) Configuration.step). *)
(* Proof. *)
(*   pcofix CIH. ii. *)
(*   pfold. econs. *)
(*   - esplits; eauto. *)
(*     inv PR. inv SIM. inv FORGET. *)
(*     ii. specialize (THS tid). inv THS. *)
(*     rewrite FIND in *. ss. econs; eauto. *)
(*     specialize (TERMINAL_TGT tid). *)
(*     destruct (Threads.find tid (Configuration.threads x1)). ss. *)
(*     dependent destruction STATE. eapply TERMINAL_TGT; eauto. *)
(*   - i. exploit sim_pf_step; eauto. i. des. esplits; eauto. *)
(* Qed. *)

(* Theorem drf_pf *)
(*       s *)
(*       (RACEFREE: pf_racefree (Configuration.init s)) *)
(*   : *)
(*     behaviors Configuration.step (Configuration.init s) <1= *)
(*     behaviors (fun _ => pftstep) (Configuration.init s) *)
(* . *)
(* Proof. *)
(*   apply sim_whole_adequacy, sim_pf_sim_whole, sim_pf_init. ss. *)
(* Qed. *)

(* Lemma self_promise_remove_lifting *)
(*       lang st1 st2 lc1_src lc1_tgt lc2_tgt mem1_tgt mem2_tgt mem1_src sc1 sc2 P  *)
(*       (STATE1 : Forget.forget_local lc1_src lc1_tgt) *)
(*       (MEM1 : Forget.forget_memory (Local.is_promised_loc lc1_src) *)
(*                                   mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step P _)  *)
(*                       (Thread.mk lang st1 lc1_tgt sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2_tgt sc2 mem2_tgt)) *)
(*       (CONSISTENT : promise_view_consistent lc2_tgt) *)
(*   : *)
(*     exists lc2_src mem2_src, *)
(*       <<SRC_STEP : (rc (tau (@pred_step P _))) *)
(*                        (Thread.mk _ st1 lc1_src sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2_src sc2 mem2_src)>> /\ *)
(*       <<STATE1 : Forget.forget_local lc2_src lc2_tgt>> /\ *)
(*       <<MEM1 : Forget.forget_memory (Local.is_promised_loc lc2_src) *)
(*                                     mem2_src mem2_tgt>> *)
(* . *)
(* Proof. *)
(*   destruct TGT_STEP, TSTEP, STEP. *)
(*   dependent destruction STEP. dependent destruction STEP. *)
(*   - exists lc1_src, mem1_src. destruct LOCAL. subst. *)
(*     econs; eauto; [| econs]. *)
(*     + apply Relation_Operators.r_refl. *)
(*     + destruct STATE1; econs; eauto. *)
(*     + destruct MEM1. econs; eauto. admit. *)
(*   - admit. *)
(* Admitted. *)

(* Lemma other_promise_remove_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P proms *)
(*       (MEM1 : Forget.forget_memory proms mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                      no_read_msgs proms) _)  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                       no_read_msgs proms) _)   *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> /\ *)
(*       <<MEM1 : Forget.forget_memory proms mem2_src mem2_tgt>> *)
(* . *)
(* Admitted. *)

(* Lemma future_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P v1 v2 *)
(*       (TGT_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _))  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*       (INTERVAL_EMPTY : empty_interval v1 v2 (fun _ => True) mem1_src) *)
(*       (FUTURE : Memory.le mem1_src mem1_tgt) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _)) *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> *)
(* . *)
(* Admitted. *)

