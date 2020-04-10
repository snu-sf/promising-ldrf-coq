Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.
Require Import Mapping.

Require Import LocalDRFDef.
Require Import LocalDRF_PF.

Set Implicit Arguments.

Section CONCRETEIDENT.

  Definition map_ident_concrete (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.

  Definition map_ident_concrete_bot
             f mem
             (MAP: map_ident_concrete f mem)
             (CLOSED: Memory.closed mem)
    :
      mapping_map_bot f.
  Proof.
    ii. eapply MAP. inv CLOSED. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_timemap
        f mem tm
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      timemap_map f tm tm.
  Proof.
    ii. eapply MAP; eauto.
    exploit CLOSED; eauto. i. des. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_view vw mem)
    :
      view_map f vw vw.
  Proof.
    inv CLOSED. econs.
    - eapply map_ident_concrete_closed_timemap; eauto.
    - eapply map_ident_concrete_closed_timemap; eauto.
  Qed.

  Lemma map_ident_concrete_closed_tview
        f mem tvw
        (MAP: map_ident_concrete f mem)
        (CLOSED: TView.closed tvw mem)
    :
      tview_map f tvw tvw.
  Proof.
    inv CLOSED. econs.
    - i. eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_opt_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      opt_view_map f vw vw.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_message
        f mem msg
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_message msg mem)
    :
      msg_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_opt_view; eauto.
  Qed.

  Inductive compose_map (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
    : Loc.t -> Time.t -> Time.t -> Prop :=
  | compose_map_intro
      loc ts0 ts1 ts2
      (MAP0: f0 loc ts0 ts1)
      (MAP1: f1 loc ts1 ts2)
    :
      compose_map f0 f1 loc ts0 ts2
  .
  Hint Constructors compose_map.

  Lemma compose_map_eq f0 f1
        (MAPEQ0: mapping_map_eq f0)
        (MAPEQ1: mapping_map_eq f1)
    :
      mapping_map_eq (compose_map f0 f1).
  Proof.
    unfold mapping_map_eq in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPEQ0 _ _ _ _ MAP2 MAP0); eauto. i. clarify.
    eauto.
  Qed.

  Lemma compose_map_lt f0 f1
        (MAPLT0: mapping_map_lt f0)
        (MAPLT1: mapping_map_lt f1)
    :
      mapping_map_lt (compose_map f0 f1).
  Proof.
    unfold mapping_map_lt in *. i. inv MAP0. inv MAP1.
    transitivity (Time.lt ts1 ts2); eauto.
  Qed.

  Lemma compose_map_timemap f0 f1 tm0 tm1 tm2
        (MAP0: timemap_map f0 tm0 tm1)
        (MAP1: timemap_map f1 tm1 tm2)
    :
      timemap_map (compose_map f0 f1) tm0 tm2.
  Proof.
    ii. eauto.
  Qed.

  Lemma compose_map_view f0 f1 vw0 vw1 vw2
        (MAP0: view_map f0 vw0 vw1)
        (MAP1: view_map f1 vw1 vw2)
    :
      view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - eapply compose_map_timemap; eauto.
    - eapply compose_map_timemap; eauto.
  Qed.

  Lemma compose_map_opt_view f0 f1 vw0 vw1 vw2
        (MAP0: opt_view_map f0 vw0 vw1)
        (MAP1: opt_view_map f1 vw1 vw2)
    :
      opt_view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_tview f0 f1 tvw0 tvw1 tvw2
        (MAP0: tview_map f0 tvw0 tvw1)
        (MAP1: tview_map f1 tvw1 tvw2)
    :
      tview_map (compose_map f0 f1) tvw0 tvw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - i. eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_msg f0 f1 msg0 msg1 msg2
        (MAP0: msg_map f0 msg0 msg1)
        (MAP1: msg_map f1 msg1 msg2)
    :
      msg_map (compose_map f0 f1) msg0 msg2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_opt_view; eauto.
  Qed.

  Lemma compose_map_mappable f0 f1 mem0 mem1
        (MAP: memory_map f0 mem0 mem1)
        (MAPPABLE: mappable_memory f1 mem1)
    :
      mappable_memory (compose_map f0 f1) mem0.
  Proof.
    ii. inv MAP. exploit MAPPED; eauto. i. des; clarify.
    inv MSG. inv MSGLE. exploit MAPPABLE; eauto. i. inv x.
    eexists. eauto.
  Qed.

  Lemma compose_map_memory f0 f1 m0 m1 m2
        (MEM0: memory_map f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: memory_map f1 m1 m2)
    :
      memory_map (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto.
      + subst. inv MSGLE. inv MSG. auto.
      + right. inv CLOSED0. exploit CLOSED; eauto. i. des.
        exploit msg_map_exists; try apply MSG_CLOSED; eauto. i. des.
        exploit msg_map_exists; try apply CLOSED0; eauto. i. des.
        esplits; [..|eauto].
        * eauto.
        * eapply compose_map_msg; eauto.
        *


          { eauto. }
          {

          ; eauto.

mappable_memory_closed_msg_exists

mappable_memory_closed_msg_exists


        esplits; eauto.
        eapply compose_map_msg; eauto.

        * econs; eauto.


  Definition mapping_map_le:=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.

  Definition mapping_map_bot :=
    forall loc,
      f loc Time.bot Time.bot.

  Definition mapping_map_eq :=
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.


  Definition mapping_map_lt (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.lt t0 t1 <-> Time.lt ft0 ft1.


  Definition map_ident_concrete (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.



  Definition map_ident_concrete_compose_memory
             (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.




  Lemma map_ident_concrete_promises
        f mem0 mem
        (MAP: map_ident_concrete f mem)
        (MAPLT: mapping_map_lt f)
        (CLOSED: Memory.closed mem)
        (MLE: Memory.le mem0 mem)
    :
      promises_map f mem0 mem0.
  Proof.
    inv CLOSED. econs.
    - i. esplits; eauto.
      + eapply mapping_map_lt_non_collapsable; auto.
      + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
        eapply MAP; eauto.
      + eapply MLE in GET. eapply CLOSED0 in GET. des.
        eapply map_ident_concrete_closed_message; eauto.
    - i. esplits; eauto.
      + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
        eapply MAP; eauto.
      + eapply MLE in GET. eapply MAP. etrans.
        * eapply memory_get_ts_le; eauto.
        * eapply Memory.max_ts_spec in GET. des. auto.
  Qed.

  Lemma map_ident_concrete_memory
        f mem
        (MAP: map_ident_concrete f mem)
        (MAPLT: mapping_map_lt f)
        (CLOSED: Memory.closed mem)
    :
      memory_map f mem mem.
  Proof.
    eapply promises_map_memory_map.
    eapply map_ident_concrete_promises; eauto. refl.
  Qed.

  Lemma map_ident_concrete_local
        f mem lc
        (MAP: map_ident_concrete f mem)
        (MAPLT: mapping_map_lt f)
        (LOCAL: Local.wf lc mem)
        (CLOSED: Memory.closed mem)
    :
      local_map f lc lc.
  Proof.
    inv LOCAL. econs.
    - refl.
    - eapply map_ident_concrete_closed_tview; eauto.
    - eapply map_ident_concrete_promises; eauto.
  Qed.


End CONCRETEIDENT.
