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

Require Import MaxView.

Set Implicit Arguments.


Definition world: Type. Admitted.
Variable world_messages_le: Messages.t -> world -> world -> Prop.


Definition flags := Loc.t -> bool.
Definition flags_bot: flags := fun _ => false.

Definition flags_le (f_tgt f_src: flags): Prop :=
  forall loc, (f_tgt loc) -> (f_src loc).

Definition update_flags (f: flags) (l: Loc.t) (b: bool): flags :=
  fun l' => if (Loc.eq_dec l' l) then b else f l'.


Definition sim_timemap (f_src: flags) (b: bool) (w: world) (sc_src sc_tgt: TimeMap.t): Prop. Admitted.

Definition sim_memory (f_src: flags) (b: bool) (w: world) (mem_src: Memory.t) (mem_tgt: Memory.t): Prop. Admitted.


Definition value_map := Loc.t -> option (Const.t * Const.t).

Definition value_map_le (vm0 vm1: value_map): Prop :=
  forall loc,
    match (vm0 loc), (vm1 loc) with
    | _, None => True
    | Some vs0, Some vs1 => vs0 = vs1
    | _, _ => False
    end.


Definition sim_local (vm: value_map) (f_src: flags) (f_tgt: flags)
           (b: bool) (w: world)
           (lc_src: Local.t) (lc_tgt: Local.t)
           (mem_src: Memory.t) (mem_tgt: Memory.t)
           (sc_src: TimeMap.t) (sc_tgt: TimeMap.t): Prop. Admitted.


Lemma sim_local_lower vm flags_bot f_tgt w lc_src lc_tgt0 lc_tgt1 mem_src
      mem_tgt0 mem_tgt1 sc_src sc_tgt0 sc_tgt1
      (SIM: sim_local vm flags_bot f_tgt false w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0)
      (LOCAL: lower_local lc_tgt0 lc_tgt1)
      (MEM: lower_memory mem_tgt0 mem_tgt1)
      (SC: TimeMap.le sc_tgt0 sc_tgt1)
  :
    sim_local vm flags_bot f_tgt false w lc_src lc_tgt1 mem_src mem_tgt1 sc_src sc_tgt1.
Admitted.

Lemma sim_update_latest lang_src
      (st_src: lang_src.(Language.state))
      vm f_tgt w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      (LOCAL: sim_local vm flags_bot f_tgt true w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src mem_tgt)
      (SC: sim_timemap flags_bot false w0 sc_src sc_tgt)
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm flags_bot f_tgt false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory flags_bot false w1 mem_src' mem_tgt>>) /\
      (<<SC: sim_timemap flags_bot false w1 sc_src sc_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_memory_lower f_src w mem_src mem_tgt0 mem_tgt1
      (SIM: sim_memory f_src false w mem_src mem_tgt0)
      (MEM: lower_memory mem_tgt0 mem_tgt1)
  :
    sim_memory f_src false w mem_src mem_tgt1.
Admitted.

Lemma sim_timemap_lower f_src w sc_src sc_tgt0 sc_tgt1
      (SIM: sim_timemap f_src false w sc_src sc_tgt0)
      (SC: TimeMap.le sc_tgt0 sc_tgt1)
  :
    sim_timemap f_src false w sc_src sc_tgt1.
Admitted.






Lemma sim_promise_consistent
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
  :
    Local.promise_consistent lc_src.
Admitted.

Lemma sim_cap vm f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 mem_tgt1 sc_src sc_tgt
      (LOCAL: sim_local vm flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src sc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src0 mem_tgt0)
      (SC: sim_timemap flags_bot false w0 sc_src sc_tgt)
      (CAP: Memory.cap mem_tgt0 mem_tgt1)
  :
    exists tm_src mem_src1 w1,
      (<<TM: forall loc, Time.lt (Memory.max_ts loc mem_src0) (tm_src loc)>>) /\
      (<<CAP: CapFlex.cap_flex mem_src0 mem_src1 tm_src>>) /\
      (<<MEM: sim_memory flags_bot true w1 mem_src1 mem_tgt1>>) /\
      (<<SC: sim_timemap flags_bot true w1 sc_src sc_tgt>>) /\
      (<<LOCAL: sim_local vm flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src sc_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_future vm0 f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0
      (SIM: sim_local vm0 flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0)
      (MEM0: sim_memory flags_bot false w0 mem_src0 mem_tgt0)
      (SC0: sim_timemap flags_bot false w0 sc_src0 sc_tgt0)

      w1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1)
      (MEMSRC: Memory.future mem_src0 mem_src1)
      (MEMTGT: Memory.future mem_tgt0 mem_tgt1)
      (SCSRC: TimeMap.le sc_src0 sc_src1)
      (SCTGT: TimeMap.le sc_tgt0 sc_tgt1)
      (MEM1: sim_memory flags_bot false w1 mem_src1 mem_tgt1)
      (SC1: sim_timemap flags_bot false w1 sc_src1 sc_tgt1)
  :
    exists vm1,
      (<<SIM: sim_local vm1 flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src1 sc_tgt1>>) /\
      (<<VALUES: value_map_le vm0 vm1>>)
.
Admitted.

Lemma sim_make_promise_match lang_src
      (st_src: lang_src.(Language.state))
      vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc v
      (FLAG: f_src loc = true)
      (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w0 mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w0 sc_src sc_tgt)
      (VAL: vm loc = Some (v, v))
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc false) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory f_src b w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_make_promise_not_match lang_src
      (st_src: lang_src.(Language.state))
      vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc v_src v_tgt
      (FLAG: f_src loc = true)
      (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w0 mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w0 sc_src sc_tgt)
      (VAL: vm loc = Some (v_src, v_tgt))
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc true) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory f_src b w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_na_racy_read_tgt
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc val ord
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (READ: Local.racy_read_step lc_tgt mem_tgt loc val ord)
  :
    (<<VALUE: vm loc = None>>) /\
    (<<ORD: ord = Ordering.na>>).
Admitted.

Lemma sim_na_read_tgt
      vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt
      lc_tgt1 loc ts val released
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (READ: Local.read_step lc_tgt0 mem_tgt loc ts val released Ordering.na lc_tgt1)
  :
    forall v_src v_tgt (VALUE: vm loc = Some (v_src, v_tgt)), v_tgt = val.
Admitted.

Lemma sim_na_racy_write_tgt
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc ord
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (READ: Local.racy_write_step lc_tgt mem_tgt loc ord)
  :
    (<<VALUE: vm loc = None>>) /\
    (<<ORD: ord = Ordering.na>>).
Admitted.

Lemma sim_na_write_tgt
      vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0
      loc ord mem_tgt1 lc_tgt1 sc_tgt1 from to val ord
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (READ: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (LOWER: lower_memory th1.(Thread.memory) th0.(Thread.memory)
  :
    (<<VALUE: vm loc = None>>) /\
    (<<ORD: ord = Ordering.na>>).
Admitted.
