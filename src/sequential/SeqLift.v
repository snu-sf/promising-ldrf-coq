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

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Set Implicit Arguments.

Variant max_readable (mem prom: Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
| max_readable_intro
    from val released
    (GET: Memory.get loc ts mem = Some (from, Message.concrete val released))
    (NONE: Memory.get loc ts prom = None)
    (MAX: forall ts' from' msg
                 (TS: Time.lt ts ts')
                 (GET: Memory.get loc ts' mem = Some (from', msg))
                 (MSG: __guard__(msg = Message.undef \/ exists val' released', msg = Message.concrete val' released')),
        Memory.get loc ts' prom = Some (from', msg))
.

Lemma max_readable_inj mem prom loc ts0 ts1
      (MAX0: max_readable mem prom loc ts0)
      (MAX1: max_readable mem prom loc ts1)
  :
    ts0 = ts1.
Proof.
  inv MAX0. inv MAX1. apply TimeFacts.antisym.
  { destruct (Time.le_lt_dec ts0 ts1); auto.
    hexploit MAX0; eauto.
    { right. eauto. }
    i. clarify.
  }
  { destruct (Time.le_lt_dec ts1 ts0); auto.
    hexploit MAX; eauto.
    { right. eauto. }
    i. clarify.
  }
Qed.

Lemma max_readable_read mem prom loc ts
      (MAX: max_readable




    { i. eauto.



    inv MAX0.



  Time.le


Definition world: Type. Admitted.
Variable world_messages_le: Messages.t -> world -> world -> Prop.
Definition flags := Loc.t -> bool.
Definition flags_bot: flags := fun _ => false.

Definition update_flgas (f: flags) (l: Loc.t) (b: bool): flags :=
  fun l' => if (Loc.eq_dec l' l) then b else f l'.

Definition sim_local (f_src: flags) (f_tgt: flags) (b: bool) (w: world) (views: Loc.t -> Time.t -> list View.t) (lc_src: Local.t) (lc_tgt: Local.t): Prop. Admitted.

Definition sim_memory (f_src: flags) (b: bool) (w: world) (views: Loc.t -> Time.t -> list View.t) (mem_src: Memory.t) (mem_tgt: Memory.t): Prop. Admitted.

Definition sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop. Admitted.

Lemma sim_local_future f_tgt w0 w1 views0 views1 lc_src lc_tgt
      (SIM: sim_local flags_bot f_tgt false w0 views0 lc_src lc_tgt)
      (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1)
      (VIEWS: views_le views0 views1)
  :
    sim_local flags_bot f_tgt true w1 views1 lc_src lc_tgt.
Admitted.

Lemma sim_cap f_tgt w0 views0 lc_src lc_tgt mem_src0 mem_tgt0 mem_tgt1
      (LOCAL: sim_local flags_bot f_tgt false w0 views0 lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w0 views0 mem_src0 mem_tgt0)
      (CAP: Memory.cap mem_tgt0 mem_tgt1)
  :
    exists tm_src mem_src1 w1,
      (<<TM: forall loc, Time.lt (Memory.max_ts loc mem_src0) (tm_src loc)>>) /\
      (<<CAP: CapFlex.cap_flex mem_src0 mem_src1 tm_src>>) /\
      (<<MEM: sim_memory flags_bot true w1 views0 mem_src1 mem_tgt1>>) /\
      (<<LOCAL: sim_local flags_bot f_tgt false w1 views0 lc_src lc_tgt>>) /\
      (<<WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_local_lower flags_bot f_tgt w lc_src lc_tgt0 lc_tgt1 views
      (SIM: sim_local flags_bot f_tgt false w views lc_src lc_tgt0)
      (LOCAL: lower_local lc_tgt0 lc_tgt1)
  :
    sim_local flags_bot f_tgt false w views lc_src lc_tgt1.
Admitted.

Lemma sim_memory_lower f_src b w views mem_src mem_tgt0 mem_tgt1
      (SIM: sim_memory f_src b w views mem_src mem_tgt0)
      (LOCAL: lower_memory mem_tgt0 mem_tgt1)
  :
    sim_memory f_src b w views mem_src mem_tgt1.
Admitted.

Lemma sim_update_latest lang_src
      (st_src: lang_src.(Language.state))
      f_tgt w views lc_src lc_tgt mem_src mem_tgt sc_src
      (LOCAL: sim_local flags_bot f_tgt true w views lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w views mem_src mem_tgt)
  :
    exists mem_src' lc_src',
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local flags_bot f_tgt false w views lc_src' lc_tgt>>) /\
      (<<MEM: sim_memory flags_bot false w views mem_src' mem_tgt>>).
Admitted.

Memo

Lemma sim_promise_step lang_src lang_tgt
      (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      f_tgt w views lc_src lc_tgt mem_src mem_tgt sc_src
      (LOCAL: sim_local flags_bot f_tgt true w views lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w views mem_src mem_tgt)
  :
    exists mem_src' lc_src',
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local flags_bot f_tgt false w views lc_src' lc_tgt>>) /\
      (<<MEM: sim_memory flags_bot false w views mem_src' mem_tgt>>).
Admitted.



Lemma sim_memory_lower f_src b w views mem_src mem_tgt0 mem_tgt1
      (SIM: sim_memory f_src b w views mem_src mem_tgt0)
      (LOCAL: lower_memory mem_tgt0 mem_tgt1)
  :
    sim_memory f_src b w views mem_src mem_tgt1.
Admitted.


Lemma sim_promise_step

Lemma sim_

Lemma sim_update_latest lang_src
      (st_src: lang_src.(Language.state))
      f_tgt



Lemma sim_promise_step



  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
             (b0: bool) (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t)
             '(views0, fin0): Prop :=
    (<<FUTURE: forall w1 sc1_src mem1_src
                      sc1_tgt mem1_tgt views1 fin1
                      (SC: sim_timemap w1 sc1_src sc1_tgt)
                      (MEMORY: sim_memory b0 w1 views1 mem1_src mem1_tgt)
                      (WF_SRC: Local.wf lc1_src mem1_src)
                      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
                      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
                      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
                      (MEM_SRC: Memory.closed mem1_src)
                      (MEM_TGT: Memory.closed mem1_tgt)
                      (CONS_TGT: Local.promise_consistent lc1_tgt)
                      (REL: joined_released views1 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
                      (JOINED: joined_memory views1 mem1_tgt)
                      (FINMEMORY: fin1 <4= unchangable mem1_tgt lc1_tgt.(Local.promises))
                      (VIEWS: wf_views views1)
                      (VIEWSLE: views_le views0 views1)
                      (FUTURE: sim_memory_future
                                 b0
                                 (lc1_src.(Local.promises)) (lc1_tgt.(Local.promises))
                                 mem0_src mem1_src mem0_tgt mem1_tgt
                                 sc0_src sc1_src sc0_tgt sc1_tgt
                                 w0 w1
                                 views0 views1
                                 fin0 fin1)
                      (UNCHANGED: UndefCertify.unchanged lc1_src.(Local.promises) mem0_src mem1_src),
        (<<TERMINAL:
           forall
             (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
             (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
             exists st2_src lc2_src sc2_src mem2_src w2,
               (<<STEPS: rtc (@Thread.tau_step _)
                             (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
               (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
               (<<MEMORY: sim_memory b0 w2 views1 mem2_src mem1_tgt>>) /\
               (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
               (<<LOCAL: sim_local w2 views1 lc2_src lc1_tgt>>) /\
               (<<TERMINAL: sim_terminal st2_src st1_tgt>>) /\
               (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w2>>)>>) /\
        (<<PROMISES:
           forall (BOOL: b0 = true)
                  (PROMISES_TGT: (Local.promises lc1_tgt) = Memory.bot),
             (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc0_src mem0_src)>>) \/
             exists st2_src lc2_src sc2_src mem2_src,
               (<<STEPS: rtc (@Thread.tau_step _)
                             (Thread.mk _ st1_src lc1_src sc0_src mem0_src)
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
               (<<PROMISES_SRC: (Local.promises lc2_src) = Memory.bot>>)>>) /\
        (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt sim_terminal)
                                  b0 w1
                                  st1_src lc1_src sc1_src mem1_src
                                  st1_tgt lc1_tgt sc1_tgt mem1_tgt
                                  (views1, fin1)>>)>>) /\
    (<<CAP: forall (BOOL: b0 = false)
                   (MEMORY: sim_memory b0 w0 views0 mem0_src mem0_tgt)
                   (WF_SRC: Local.wf lc1_src mem0_src)
                   (WF_TGT: Local.wf lc1_tgt mem0_tgt)
                   (SC_SRC: Memory.closed_timemap sc0_src mem0_src)
                   (SC_TGT: Memory.closed_timemap sc0_tgt mem0_tgt)
                   (MEM_SRC: Memory.closed mem0_src)
                   (MEM_TGT: Memory.closed mem0_tgt)
                   (CONS_TGT: Local.promise_consistent lc1_tgt)
                   (REL: joined_released views0 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
                   (JOINED: joined_memory views0 mem0_tgt)
                   (VIEWS: wf_views views0),
        exists tm_src,
          (<<TM: forall loc, Time.lt (Memory.max_ts loc mem0_src) (tm_src loc)>>) /\
          (<<CAP: forall cap_src cap_tgt
                         (CAPSRC: CapFlex.cap_flex mem0_src cap_src tm_src)
                         (CAPTGT: Memory.cap mem0_tgt cap_tgt),
              exists w3,
                (<<SC3: sim_timemap w3 sc0_src sc0_tgt>>) /\
                (<<MEMORY3: sim_memory true w3 views0 cap_src cap_tgt>>) /\
                (<<SIM: sim_thread _ _ sim_terminal true w3 st1_src lc1_src sc0_src cap_src st1_tgt lc1_tgt sc0_tgt cap_tgt (views0, fin0)>>)>>)>>)
  .


Lemma sim_update

      reserve_future_memory


Lemma sim_local




               Variant promises_map_latest (vers: versions) (prom_src prom_tgt: Memory.t)
            (f_src: flags) (f_tgt: flags): Prop :=
