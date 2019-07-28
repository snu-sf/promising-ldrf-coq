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

Require Import DRF_PF.

Set Implicit Arguments.

Lemma forget_compose P0 P1 Q m0 m1 m2
      (FORGET0: forget_memory P0 m0 m1)
      (FORGET1: forget_memory P1 m1 m2)
      (COMPOSE: forall loc to, Q loc to <-> P0 loc to \/ P1 loc to)
  :
    forget_memory Q m0 m2.
Proof.
  inv FORGET0. inv FORGET1. econs; eauto.
  - ii. erewrite COMPOSE in NPROMS. apply not_or_and in NPROMS. des.
    erewrite COMPLETE; eauto.
  - i. apply COMPOSE in PROMS. destruct (classic (P0 l t)); auto.
    des; clarify. erewrite COMPLETE; eauto.
Qed.

(* Lemma forget_compose P0 P1 Q m0 m1 m2 *)
(*       (FORGET0: forget_memory P0 m0 m1) *)
(*       (FORGET1: forget_memory P1 m1 m2) *)
(*       (COMPOSE: forall loc to, Q loc to <-> P0 loc to \/ P1 loc to) *)
(*   : *)
(*     forget_memory Q m0 m2. *)
(* Proof. *)
(*   inv FORGET0. inv FORGET1. econs; eauto. *)
(*   - ii. erewrite COMPOSE in NPROMS. apply not_or_and in NPROMS. des. *)
(*     erewrite COMPLETE; eauto. *)
(*   - i. apply COMPOSE in PROMS. destruct (classic (P0 l t)); auto. *)
(*     des; clarify. erewrite COMPLETE; eauto. *)
(* Qed. *)

Lemma forget_compose_middle P0 P1 Q m0 m1 m2
      (FORGET: forget_memory Q m0 m2)
      (FORGET1: forget_memory P1 m1 m2)
      (COMPOSE: forall loc to, Q loc to <-> P0 loc to \/ P1 loc to)
  :
    forget_memory P0 m0 m1.
Proof.
  inv FORGET. inv FORGET1. econs; eauto.
  - ii. destruct (classic (P1 l t)).
    + erewrite FORGET; eauto. eapply FORGET0; eauto.
      eapply COMPOSE; eauto.
    + erewrite COMPLETE; eauto.
      * erewrite COMPLETE0; eauto.
      * ii. eapply COMPOSE in H0. des; clarify.
  - i. eapply FORGET0. eapply COMPOSE; eauto.
Qed.

Lemma step_lifting
      lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt others updates otherspace

      (STEP: (@pred_step
                ((fun _ => True)
                   /1\ (write_not_in otherspace)
                   /1\ (no_update_on updates)
                   /1\ (no_read_msgs others)
                   /1\ (write_not_in others)
                   /1\ (no_read_msgs prom.(promised))) lang) e_tgt th_tgt th_tgt')

      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')      
      (MEM: pf_sim_memory (promised prom \2/ others) mem_src mem_tgt)
      (NOATTATCH: not_attatched updates mem_src) 
      
      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)      
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\
      (<<MEM: pf_sim_memory (promised prom' \2/ others) mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates mem_src'>>) /\
      (<<UNCHANGED: unchanged_on otherspace mem_src mem_src'>>).
Proof.
  hexploit (forget_exists prom mem_tgt); eauto. i. des.

  exploit self_promise_remove; try apply FORGET; eauto.
  i. des.

  inv MEM.
  assert (FORGET1: forget_memory others mem_inter mem_src0).
  { eapply forget_compose_middle; eauto.
    i. split; i; des; auto. }
  
  inv STEP0.
  { exists mem_src, ThreadEvent.silent. esplits; eauto.
    - econs; eauto.
      eapply forget_compose.
      + eapply FORGET1.
      + eapply MEM0.
      + i. split; i; des; auto.
    - refl. }

  exploit other_promise_remove; try eapply STEP1; eauto.
  i. des.
  
  exploit shorter_memory_step; try apply STEP0; eauto.
  i. des.

  exploit no_update_on_step; try apply STEP2; eauto.
  { refl. }
  i. des.

  exists mem_src'2, e_src0. esplits.
  - econs 2. eapply pred_step_mon; cycle 1; eauto.
    ss. i. des. eauto.
  - etrans; eauto.
  - econs.
    + instantiate (1:=mem_src'0).
      eapply forget_compose; eauto.
      i. split; i; des; auto.
    + etrans; eauto.
  - eauto.
  - exploit write_not_in_unchanged_on; try apply STEP3; eauto.
Qed.

    
    0
    eapply pred_step_mon; cycle 1; eauto.
    ss. i. des. eauto.
  - eauto.
  - econs; eauto.
    admit.
  -  
    
  
  { eapply STEP1. apply STEP1. }
  { ss. }
  { ss. }
  { ss. }
  

  ; try apply STEP1; try apply FORGET0; eauto.
  ss.
  eauto.
  eauto.
  { eapply STEP1. }
  {
  {
  i. des.

  
  exploit other_promise_remove; try apply STEP1; try apply FORGET0; eauto.
  ss.
  eauto.
  eauto.
  { eapply STEP1. }
  {
  {
  i. des.
  
  exploit other_promise_remove; try apply FORGET0; eauto.
  i. des.

  
         Inv.t _ st_src lc_src lc_tgt.(Local.promises) (updates tid) (mlast tid))
    (FUTURE:
       forall tid lang_src st_src lc_src
              (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                       Some (existT _ lang_src st_src, lc_src)),
         unchanged_on
           (fun loc to => covered loc to lc_src.(Local.promises))
           (mlast tid) c_src.(Configuration.memory))
    (NOATTATCH:
       forall tid,
         not_attatched (updates tid) c_src.(Configuration.memory))

  
Thread.step
  
not_in_others 
  
Local.wf lc mem
Memory.closed_timemap (Configuration.sc conf) (Configuration.memory conf) ->
Memory.closed (Configuration.memory conf) -> Configuration.wf conf
                                                              
                                                              noreadself
                                                                             

                                                                             
         
Inductive wf (conf : Configuration.t) : Prop :=
    wf_intro : Threads.wf (Configuration.threads conf) (Configuration.memory conf) ->
               

                                                                             
  
  Configuration.wf


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
    + exploit self_promise_remove_write; eauto. i. des.
      exists mem_src', (ThreadEvent.write loc from to val released ord).
      esplits; eauto. econs. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + exploit Local.read_step_future; eauto. i. des.
      inv LOCAL1. ss. exploit self_promise_remove_write; eauto. i. des. 
      exists mem_src',
      (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw).
      esplits; eauto. econs. econs; ss; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
      inv MEM. rewrite COMPLETE; eauto.
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
Qed.


no_write_others attatch no_read_self no_read_other








Lemma step_lifting

      




WIP

Lemma not_attatch L prom mem_src mem_tgt loc from1 to1 val released mem_tgt' from'
      (SHORTER: shorter_memory mem_src mem_tgt)
      (NOATTATCH: not_attatched L mem_src) 
      (ADD: Memory.write Memory.bot mem_tgt loc from1 to1 val released prom mem_tgt' Memory.op_kind_add)
  :
    exists mem_src' to',
      (<<ADD: Memory.write Memory.bot mem_src loc from' to' val released prom mem_src' Memory.op_kind_add>>) /\  
      (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched L mem_src'>>).
Proof.

  
  dup SHORTER. inv SHORTER. inv ADD. inv PROMISE.
  exploit MemoryFacts.MemoryFacts.add_remove_eq; try apply REMOVE; eauto. i. clarify.
  exploit write_succeed; eauto.
  - instantiate (1:=mem_src). instantiate (1:=loc).
    ii. eapply COVER in COVER0. inv COVER0.
    dup MEM. eapply Memory.add_get0 in MEM. des. 
    dup GET. eapply Memory.add_get1 in GET; eauto.
    exploit Memory.get_disjoint.
    + eapply GET.
    + eapply GET1.
    + i. des; clarify.
      eapply x0; eauto. inv H. econs; ss; eauto.
      eapply TimeFacts.le_lt_lt; eauto.
  - inv MEM. inv ADD. inv MSG_WF. inv TS. eauto.
  - inv MEM. inv ADD. eauto.
  - i. des. inv WRITE. inv PROMISE. esplits; eauto. econs.
    + i. erewrite Memory.add_o in GET; eauto.      
      erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
    + i. inv COV. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss; des; clarify. eapply Memory.add_get0 in MEM. des.
        econs; eauto. inv ITV. econs; eauto.
        ss. eapply TimeFacts.le_lt_lt; eauto.
      * exploit COVER.
        { econs; eauto. }
        intros COV. inv COV. eapply Memory.add_get1 in GET0; eauto.
        econs; eauto.
Qed.


Lemma no_update_on_step
      L lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
      mem_tgt mem_tgt' mem_src e
      (STEP: (@pred_step (no_promise /1\ no_update_on L) lang) e th_tgt th_tgt')
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (SHORTER: shorter_memory mem_src mem_tgt)
      (NOATTATCH: not_attatched L mem_src) 
  :
    exists e_src mem_src',
      (<<STEP: (@pred_step (no_promise) lang)
                 e_src th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched L mem_src'>>).
Proof.
  dup SHORTER. inv SHORTER. inv STEP. inv STEP0. des. inv STEP.
  - inv STEP0. ss.
  - inv STEP0. inv LOCAL.
    + exists mem_src; eauto. econs; eauto. econs; eauto.
      econs; eauto. econs 2; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify. exploit COMPLETE; eauto. i. des.
      exists mem_src; eauto. econs; eauto. econs; eauto.
      econs; eauto. econs 2; eauto. econs; eauto.
    + exploit write_msg_wf; eauto. i. des.
      inv LOCAL0. ss. clarify.
      exploit memory_write_bot_add; eauto. i. clarify.
      dup WRITE. exploit shorter_memory_write; eauto.
      { refl. }
      i. des. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + inv LOCAL1. ss. exploit write_msg_wf; eauto. i. des.
      exploit COMPLETE; eauto. i. des.
      inv LOCAL2. ss. clarify.
      exploit memory_write_bot_add; eauto. i. clarify.
      dup WRITE. exploit shorter_memory_write; eauto.
      { refl. }
      i. des. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
      econs; eauto. econs 2; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
      econs; eauto. econs 2; eauto. econs; eauto.
Qed.


Lemma shorter_memory_write mem_src mem_tgt loc from1 to1 val released mem_tgt' from'
      (SHORTER: shorter_memory mem_src mem_tgt)
      (ADD: Memory.write Memory.bot mem_tgt loc from1 to1 val released Memory.bot mem_tgt' Memory.op_kind_add)
      (TO: Time.le from1 from')
      (FROM: Time.lt from' to1)
  :
    exists mem_src',
      (<<ADD: Memory.write Memory.bot mem_src loc from' to1 val released Memory.bot mem_src' Memory.op_kind_add>>) /\  
      (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).  
Proof.
  dup SHORTER. inv SHORTER. inv ADD. inv PROMISE.
  exploit write_succeed; eauto.
  - instantiate (1:=mem_src). instantiate (1:=loc).
    ii. eapply COVER in COVER0. inv COVER0.
    dup MEM. eapply Memory.add_get0 in MEM. des. 
    dup GET. eapply Memory.add_get1 in GET; eauto.
    exploit Memory.get_disjoint.
    + eapply GET.
    + eapply GET1.
    + i. des; clarify.
      eapply x0; eauto. inv H. econs; ss; eauto.
      eapply TimeFacts.le_lt_lt; eauto.
  - inv MEM. inv ADD. inv MSG_WF. inv TS. eauto.
  - inv MEM. inv ADD. eauto.
  - i. des. inv WRITE. inv PROMISE. esplits; eauto. econs.
    + i. erewrite Memory.add_o in GET; eauto.      
      erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
    + i. inv COV. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss; des; clarify. eapply Memory.add_get0 in MEM. des.
        econs; eauto. inv ITV. econs; eauto.
        ss. eapply TimeFacts.le_lt_lt; eauto.
      * exploit COVER.
        { econs; eauto. }
        intros COV. inv COV. eapply Memory.add_get1 in GET0; eauto.
        econs; eauto.
Qed

.

ThreadEvent.t  
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


Lemma shorter_memory_write mem_src mem_tgt loc from to msg mem_tgt' from'
      (SHORTER: shorter_memory mem_src mem_tgt)
      (ADD: Memory.write mem_tgt loc from to msg mem_tgt')
      (TO: Time.le from' from)
      (FROM: Time.lt from' to)
  :
    exists mem_src',
      (<<ADD: Memory.add mem_src loc from to msg mem_src'>>) /\  
      (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).  
Proof.

  


  
  
  
  
Lemma shorter_memory_step
      P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_tgt mem_tgt' mem_src e
      (STEP: (@pred_step (P /1\ no_promise) lang) e th_tgt th_tgt')
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (SHORTER: shorter_memory mem_src mem_tgt)
  :
    exists mem_src',
      (<<STEP: (@pred_step (P /1\ no_promise) lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
Proof.
  dup SHORTER. inv SHORTER. inv STEP. inv STEP0. des. inv STEP.
  - inv STEP0. ss.
  - inv STEP0. inv LOCAL.
    + exists mem_src; eauto. econs; eauto. econs; eauto.
      


    
    inv LOCAL. ss. clarify.
    esplits. econs; eauto. econs; eauto. econs 1; eauto. econs; eauto.
  - inv STEP0. inv LOCAL; ss.
    + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify. exists sc_src. 
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. ss.
      inv WRITABLE. econs; eauto.
    + inv LOCAL1. ss. inv LOCAL2. ss. clarify. exists sc_src. 
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. ss.
      inv WRITABLE. econs; eauto.
    + inv LOCAL0. ss. clarify.
      esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. ss. f_equal.
      unfold TView.write_fence_tview. ss. des_ifs.
Qed.


Lemma not_attatched_write
      L lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_tgt mem_tgt' e_tgt
      (SCMAX: ~ promise_view_consistent prom sc)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memort.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (STEP: (@pred_step (no_update_on L) lang) e_tgt th_tgt th_tgt')
  :
    no_sc e_tgt.
Proof.


Lemma not_attatched_write
      L lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_tgt mem_tgt' e_tgt
      (SCMAX: ~ promise_view_consistent prom sc)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memort.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (STEP: (@pred_step (no_update_on L) lang) e_tgt th_tgt th_tgt')
  :
    no_sc e_tgt.
Proof.
      
                         
    Memory.
    
    (<<GET: exists msg, <<MSG: Memory.get l t = Some msg>> >>) /\
    (<<NOATTATCH: exists msg,

        

                  Memory.adjacent
  covered






Lemma consistent_read_no_self_promise
      lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_tgt mem_tgt' e_tgt
      (LOCALWF: Local.wf (Local.mk v prom) mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (SC: Memory.closed_timemap sc mem_tgt)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (CONSISTENT: local_consistent (Local.mk v' prom'))
      (STEP: Thread.step_allpf e_tgt th_tgt th_tgt')
  :
    no_read_msgs prom.(promised) e_tgt.
Proof.

Lemma forget_exists prom mem_tgt:
  exists mem_src, <<FORGET: forget_memory prom.(promised) mem_src mem_tgt>>.
Proof.
  hexploit (Memory.finite_sound_exists prom); eauto. i. des.
  hexploit (forget_exists_list dom mem_tgt). i. des. exists mem_src.
  inv FORGET. econs; i.
  - eapply COMPLETE; eauto. ii. eapply NPROMS.
    exploit H0; eauto. i. des. econs; eauto.
  - eapply FORGET0; eauto. inv PROMS. destruct msg. eauto.
Qed.


Memory.get
                                  
  ex

  
  revert prom mem_tgt H. induction dom; ss.
  - i. exists mem_tgt. econs; ss.
    i. inv PROMS. destruct msg. exfalso. eauto.
  - i. destruct a as [loc to].
    exploit IHdom.

    destruct (Memory.get loc to mem_src). 
    
    
  
  
  
      
  
  Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (* (FUTURE: Memory.le msrc mtgt) *)
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .

    


        Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (* (FUTURE: Memory.le msrc mtgt) *)
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .


Memory.finite
Lemma forget_step
Configuration.step
      

Lemma unchanged_on_step
      (
      


  
Inductive unchanged_on (P: Loc.t -> Time.t -> Prop) m0 m1 : Prop :=
| unchanged_on_intro
    (NCOV: forall l t (IN: P l t) (COV: covered l t m1), covered l t m0)
    (FUTURE : Memory.le m0 m1)
.


Lemma pf_step_hold_other
      c1_src c1_tgt
      c3_tgt e tid mlast updates tf
      (SIM: sim_pf mlast updates c1_src c1_tgt)
      (STEP_TGT: Configuration.step e tid c1_tgt c3_tgt)
  :
    exists th2_src th3_src,
      (<<STEPS_SRC: rtc (tau (@Thread.program_step _))
                       (to_thread
                          (Threads.find tid c1_src.(Configuration.threads))
                          c1_src.(Configuration.sc)
                          c1_src.(Configuration.memory))
                       th2_src>>) /\
      (<<STEP_SRC: opt_pftstep e th2_src th3_src>>) /\
      (<<SC: th3_src.(Thread.sc) = c3_tgt.(Configuration.sc)>> /\
            <<MEM: forget_memory
                     (all_promises c3_tgt)
                     th3_src.(Thread.memory) c3_tgt.(Configuration.memory)>>) /\
      (<<ST: forget_state
              (StateLocal.mk _ th3_src.(Thread.state) th3_src.(Thread.local))
              (Threads.find tid c3_tgt.(Configuration.threads))>>) /\
      (<<HOLD: forall tid2 (NEQ : tid <> tid2),
                Inv.hold
                  (Threads.find tid2 c1_src.(Configuration.threads))
                  (Locked.t (c1_tgt.(Configuration.mpreds) tid2))
                  ((Threads.find tid2 c3_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises))
                  (skylast tid2)
                  (mlast tid2) th3_src.(Thread.memory)>>).
Proof.
Admitted.

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
(*       (FORGET: forget_config c_src c_tgt) *)
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
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)

(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
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
(*       (STATE1 : forget_local lc1_src lc1_tgt) *)
(*       (MEM1 : forget_memory (Local.is_promised_loc lc1_src) *)
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
(*       <<STATE1 : forget_local lc2_src lc2_tgt>> /\ *)
(*       <<MEM1 : forget_memory (Local.is_promised_loc lc2_src) *)
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
(*       (MEM1 : forget_memory proms mem1_src mem1_tgt) *)
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
(*       <<MEM1 : forget_memory proms mem2_src mem2_tgt>> *)
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

