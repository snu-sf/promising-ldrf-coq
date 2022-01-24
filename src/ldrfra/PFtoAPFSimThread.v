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

Require Import MemoryMerge.

Require Import PFStep.
Require Import OrdStep.
Require Import RelWrites.
Require Import RelStep.

Set Implicit Arguments.


Module PFtoAPFSimThread.
  Section PFtoAPFSimThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Variant sim_memory (rels: RelWrites.t) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (SOUND: Memory.le mem_src mem_tgt)
        (COMPLETE1: forall loc (LOC: L loc), Cell.le (mem_tgt loc) (mem_src loc))
        (COMPLETE2: forall loc ts from to msg
                      (LOC: ~ L loc) (LE: Time.le ts to)
                      (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>) \/
            exists from' to' val released,
              (<<LT: Time.lt ts to'>>) /\
              (<<GET_SRC: Memory.get loc to' mem_src = Some (from', Message.concrete val released)>>))
        (RESERVE: forall loc from to
                    (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.reserve)),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, Message.reserve)>>))
    .
    Hint Constructors sim_memory.

    Inductive sim_statelocal (rels: RelWrites.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: lc_src = lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal.

    Inductive sim_thread (rels: RelWrites.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: (Thread.state e_src) = (Thread.state e_tgt))
        (LOCAL: (Thread.local e_src) = (Thread.local e_tgt))
        (PROMISES: OrdLocal.reserve_only L (Local.promises (Thread.local e_src)))
        (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
        (MEMORY: sim_memory rels (Thread.memory e_src) (Thread.memory e_tgt))
    .
    Hint Constructors sim_thread.
  End PFtoAPFSimThread.
End PFtoAPFSimThread.
