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

Definition world: Type. Admitted.
Variable world_messages_le: Messages.t -> world -> world -> Prop.
Definition flags := Loc.t -> bool.
Definition flags_bot: flags := fun _ => false.

Definition update_flgas (f: flags) (l: Loc.t) (b: bool): flags :=
  fun l' => if (Loc.eq_dec l' l) then b else f l'.


Definition sim_local (f_src: flags) (f_tgt: flags) (b: bool) (w: world) (lc_src: Local.t) (lc_tgt: Local.t): Prop. Admitted.

Definition sim_memory (f_src: flags) (b: bool) (w: world) (mem_src: Memory.t) (mem_tgt: Memory.t): Prop. Admitted.

Definition sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop. Admitted.

Lemma sim_local_future f_tgt w0 w1 lc_src lc_tgt
      (SIM: sim_local flags_bot f_tgt false w0 lc_src lc_tgt)
      (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1)
  :
    sim_local flags_bot f_tgt true w1 lc_src lc_tgt.
Admitted.

Lemma sim_update_latest lang_src
      (st_src: lang_src.(Language.state))
      f_tgt w lc_src lc_tgt mem_src mem_tgt sc_src
      (LOCAL: sim_local flags_bot f_tgt true w lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w mem_src mem_tgt)
  :
    exists mem_src' lc_src',
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local flags_bot f_tgt false w lc_src' lc_tgt>>) /\
      (<<MEM: sim_memory flags_bot false w mem_src' mem_tgt>>).
Admitted.

Lemma sim_cap f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 mem_tgt1
      (LOCAL: sim_local flags_bot f_tgt false w0 lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src0 mem_tgt0)
      (CAP: Memory.cap mem_tgt0 mem_tgt1)
  :
    exists tm_src mem_src1 w1,
      (<<TM: forall loc, Time.lt (Memory.max_ts loc mem_src0) (tm_src loc)>>) /\
      (<<CAP: CapFlex.cap_flex mem_src0 mem_src1 tm_src>>) /\
      (<<MEM: sim_memory flags_bot true w1 mem_src1 mem_tgt1>>) /\
      (<<LOCAL: sim_local flags_bot f_tgt false w1 lc_src lc_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_local_lower flags_bot f_tgt w lc_src lc_tgt0 lc_tgt1
      (SIM: sim_local flags_bot f_tgt false w lc_src lc_tgt0)
      (LOCAL: lower_local lc_tgt0 lc_tgt1)
  :
    sim_local flags_bot f_tgt false w lc_src lc_tgt1.
Admitted.

Lemma sim_memory_lower f_src b w mem_src mem_tgt0 mem_tgt1
      (SIM: sim_memory f_src b w mem_src mem_tgt0)
      (LOCAL: lower_memory mem_tgt0 mem_tgt1)
  :
    sim_memory f_src b w mem_src mem_tgt1.
Admitted.

Lemma sim_make_promise lang_src
      (st_src: lang_src.(Language.state))
      f_src f_tgt w0 lc_src lc_tgt mem_src mem_tgt sc_src
      loc b
      (LOCAL: sim_local f_src f_tgt false w0 lc_src lc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src mem_tgt)
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local f_src f_tgt false w1 lc_src' lc_tgt>>) /\
      (<<MEM: sim_memory f_src false w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.




Definition update_flgas (f: flags) (l: Loc.t) (b: bool): flags :=
  fun l' => if (Loc.eq_dec l' l) then b else f l'.
