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
Require Import Behavior.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.
Require Import JoinedView.

Require Import gSimAux.
Require Import gSimulation.
Require Import Program.


Set Implicit Arguments.

Definition world: Type. Admitted.
Definition world_messages_le: Messages.t -> world -> world -> Prop. Admitted.

Instance world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs). Admitted.

Lemma world_messages_le_mon:
  forall msgs0 msgs1 w0 w1
         (LE: world_messages_le msgs1 w0 w1)
         (MSGS: msgs0 <4= msgs1),
    world_messages_le msgs0 w0 w1.
Admitted.

Definition sim_memory: forall (b: bool) (w: world) (views: Loc.t -> Time.t -> list View.t) (mem_src mem_tgt:Memory.t), Prop. Admitted.
Definition sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop. Admitted.
Definition sim_local: forall (w: world) (views: Loc.t -> Time.t -> list View.t) (lc_src lc_tgt:Local.t), Prop. Admitted.

Definition sim_local_mon:
  forall lc_src lc_tgt
         (w0 w1: world)
         (views0 views1: Loc.t -> Time.t -> list View.t)
         (SIM: sim_local w0 views0 lc_src lc_tgt)
         (WORLD: world_messages_le (Messages.of_memory (Local.promises lc_src)) w0 w1)
         (VIEWS: views_le views0 views1),
    sim_local w1 views1 lc_src lc_tgt.
Admitted.

Definition sim_memory_mon:
  forall mem_src mem_tgt
         b (w0: world)
         (views0 views1: Loc.t -> Time.t -> list View.t)
         (SIM: sim_memory b w0 views0 mem_src mem_tgt)
         (VIEWS: views_le views0 views1),
    sim_memory b w0 views1 mem_src mem_tgt.
Admitted.

Definition sim_timemap_mon: forall msgs (w0 w1: world) (WORLD: world_messages_le msgs w0 w1),
    sim_timemap w0 <2= sim_timemap w1.
Admitted.

Lemma sim_local_memory_bot:
  forall w views lc_src lc_tgt
         (SIM: sim_local w views lc_src lc_tgt)
         (BOT: (Local.promises lc_tgt) = Memory.bot),
    (Local.promises lc_src) = Memory.bot.
Admitted.

Lemma sim_cap mem0_src mem0_tgt sc0_src sc0_tgt lc1_src lc1_tgt w0 views0
      (MEMORY: sim_memory false w0 views0 mem0_src mem0_tgt)
      (LOCAL: sim_local w0 views0 lc1_src lc1_tgt)
      (WF_SRC: Local.wf lc1_src mem0_src)
      (WF_TGT: Local.wf lc1_tgt mem0_tgt)
      (SC_SRC: Memory.closed_timemap sc0_src mem0_src)
      (SC_TGT: Memory.closed_timemap sc0_tgt mem0_tgt)
      (MEM_SRC: Memory.closed mem0_src)
      (MEM_TGT: Memory.closed mem0_tgt)
      (CONS_TGT: Local.promise_consistent lc1_tgt)
      (REL: joined_released views0 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
      (JOINED: joined_memory views0 mem0_tgt)
      (VIEWS: wf_views views0)
  :
    exists tm_src,
      (<<TMSRC: forall loc, Time.lt (Memory.max_ts loc mem0_src) (tm_src loc)>>) /\
      (<<CAP: forall cap_src cap_tgt
                     (CAPSRC: CapFlex.cap_flex mem0_src cap_src tm_src)
                     (CAPTGT: Memory.cap mem0_tgt cap_tgt),
          exists w3,
            (<<SC3: sim_timemap w3 sc0_src sc0_tgt>>) /\
            (<<MEMORY3: sim_memory true w3 views0 cap_src cap_tgt>>) /\
            (<<LOCAL: sim_local w3 views0 lc1_src lc1_tgt>>) /\
            (<<WORLD: world_messages_le (unchangable mem0_src lc1_src.(Local.promises)) w0 w3>>)>>).
Admitted.

Lemma sim_local_promise
      b w0 views0 views1
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg_tgt kind_tgt
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt)
      (LOCAL1: sim_local w0 views0 lc1_src lc1_tgt)
      (MEM1: sim_memory b w0 views0 mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc2_tgt)
      (REL0: joined_released views0 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
      (JOINED0: joined_memory views0 mem1_tgt)
      (VIEWS0: wf_views views0)

      (REL1: joined_released views1 lc2_tgt.(Local.promises) lc2_tgt.(Local.tview).(TView.rel))
      (JOINED1: joined_memory views1 mem2_tgt)
      (VIEWS1: wf_views views1)
      (PROMISE: forall val released
                       (MSG: msg_tgt = Message.concrete val released),
          (<<JOINED: joined_opt_view (views1 loc to) released>>))
      (VIEWSLE: forall loc ts (NEQ: views1 loc ts <> views0 loc ts),
          (<<NIL: views0 loc ts = []>>) /\
          exists from val released,
            (<<GET: Memory.get loc ts mem2_tgt = Some (from, Message.concrete val released)>>) /\
            (<<VIEW: views1 loc ts = (View.join ((Local.tview lc2_tgt).(TView.rel) loc) (View.singleton_ur loc ts))
                                       ::(all_join_views (View.singleton_ur loc ts) (views0 loc from))>>))
  :
    exists lc2_src mem2_src msg_src kind_src w1,
      (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
      (<<LOCAL2: sim_local w1 views1 lc2_src lc2_tgt>>) /\
      (<<MEM2: sim_memory b w1 views1 mem2_src mem2_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w0 w1>>).
Admitted.
