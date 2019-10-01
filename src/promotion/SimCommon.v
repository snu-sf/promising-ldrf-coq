Require Import Omega.
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
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import Promotion.

Set Implicit Arguments.


Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  forall loc (LOC: loc <> l), tm_src loc = tm_tgt loc.

Inductive sim_view (l: Loc.t) (view_src view_tgt: View.t): Prop :=
| sim_view_intro
    (PLN: sim_timemap l view_src.(View.pln) view_tgt.(View.pln))
    (RLX: sim_timemap l view_src.(View.rlx) view_tgt.(View.rlx))
.
Hint Constructors sim_view.

Inductive sim_opt_view (l: Loc.t): forall (view_src view_tgt: option View.t), Prop :=
| sim_opt_view_some
    view_src view_tgt
    (SIM: sim_view l view_src view_tgt):
    sim_opt_view l (Some view_src) (Some view_tgt)
| sim_opt_view_none:
    sim_opt_view l None None
.
Hint Constructors sim_opt_view.

Inductive sim_tview (l: Loc.t) (tview_src tview_tgt: TView.t): Prop :=
| sim_tview_intro
    (REL: forall loc, sim_view l (tview_src.(TView.rel) loc) (tview_tgt.(TView.rel) loc))
    (CUR: sim_view l tview_src.(TView.cur) tview_tgt.(TView.cur))
    (ACQ: sim_view l tview_src.(TView.acq) tview_tgt.(TView.acq))
.
Hint Constructors sim_tview.


Inductive sim_message (l: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_full
    val released_src released_tgt
    (RELEASED: sim_opt_view l released_src released_tgt):
    sim_message l (Message.full val released_src) (Message.full val released_tgt)
| sim_message_reserve:
    sim_message l Message.reserve Message.reserve
.
Hint Constructors sim_message.

Inductive sim_memory (l: Loc.t) (mem_src mem_tgt: Memory.t): Prop :=
| sim_memory_intro
    (SOUND: forall loc from to msg_src
              (LOC: loc <> l)
              (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
        exists msg_tgt,
          <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
    (COMPLETE: forall loc from to msg_tgt
                 (LOC: loc <> l)
                 (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
        exists msg_src,
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
.
Hint Constructors sim_memory.

Definition released_eq_tview_loc (l loc: Loc.t) (released: View.t) (tview: TView.t): Prop :=
  <<PLN: released.(View.pln) l = (tview.(TView.rel) loc).(View.pln) l>> /\
  <<RLX: released.(View.rlx) l = (tview.(TView.rel) loc).(View.rlx) l>>.

Definition promises_released (l: Loc.t) (promises: Memory.t) (tview:TView.t): Prop :=
  forall loc from to val released
    (GETP: Memory.get loc to promises =
           Some (from, Message.full val (Some released))),
    released_eq_tview_loc l loc released tview.

Inductive sim_local (l: Loc.t) (lc_src lc_tgt: Local.t): Prop :=
| sim_local_intro
    (TVIEW: sim_tview l lc_src.(Local.tview) lc_tgt.(Local.tview))
    (PROMISES1: sim_memory l lc_src.(Local.promises) lc_tgt.(Local.promises))
    (RELEASED: promises_released l lc_src.(Local.promises) lc_src.(Local.tview))
.
Hint Constructors sim_local.

Definition get_released_src (l loc: Loc.t) (released_tgt: View.t) (tview_src: TView.t): View.t :=
  View.mk
    (LocFun.add l ((tview_src.(TView.rel) loc).(View.pln) l) released_tgt.(View.pln))
    (LocFun.add l ((tview_src.(TView.rel) loc).(View.rlx) l) released_tgt.(View.rlx)).

Definition get_message_src (l loc: Loc.t) (msg_tgt: Message.t) (tview_src: TView.t): Message.t :=
  match msg_tgt with
  | Message.full val (Some released_tgt) =>
    Message.full val (Some (get_released_src l loc released_tgt tview_src))
  | _ => msg_tgt
  end.


Lemma get_released_src_released_eq_tview_loc
      l loc released_tgt tview_src:
  <<RELEASED: released_eq_tview_loc l loc (get_released_src l loc released_tgt tview_src) tview_src>>.
Proof.
  unfold get_released_src. econs; ss.
  - unfold LocFun.add. condtac; ss.
  - unfold LocFun.add. condtac; ss.
Qed.

Lemma get_released_src_sim_view
      l loc released_tgt tview_src:
  <<SIM: sim_view l (get_released_src l loc released_tgt tview_src) released_tgt>>.
Proof.
  unfold get_released_src. econs; ss.
  - unfold sim_timemap, LocFun.add. i. condtac; ss.
  - unfold sim_timemap, LocFun.add. i. condtac; ss.
Qed.

Lemma get_released_src_wf
      l loc released_tgt tview_src
      (RELEASED_TGT: View.wf released_tgt)
      (TVIEW_SRC: TView.wf tview_src):
  View.wf (get_released_src l loc released_tgt tview_src).
Proof.
  econs. ii.
  unfold get_released_src, LocFun.add. ss. condtac.
  - subst. inv TVIEW_SRC.
    destruct (REL loc). apply PLN_RLX.
  - inv RELEASED_TGT. apply PLN_RLX.
Qed.

Lemma get_released_src_closed
      l loc released_tgt tview_src
      mem_src mem_tgt
      (SIM: sim_memory l mem_src mem_tgt)
      (CLOSED_SRC: TView.closed tview_src mem_src)
      (CLOSED_TGT: Memory.closed_view released_tgt mem_tgt):
  Memory.closed_view (get_released_src l loc released_tgt tview_src) mem_src.
Proof.
  inv CLOSED_SRC. inv CLOSED_TGT.
  unfold get_released_src. econs; ss.
  - ii. unfold LocFun.add. condtac; ss.
    + subst. destruct (REL loc). eauto.
    + specialize (PLN loc0). des. inv SIM.
      exploit COMPLETE; eauto. i. des.
      inv MSG. inv RELEASED; eauto.
  - ii. unfold LocFun.add. condtac; ss.
    + subst. destruct (REL loc). eauto.
    + specialize (RLX loc0). des. inv SIM.
      exploit COMPLETE; eauto. i. des.
      inv MSG. inv RELEASED; eauto.
Qed.

Lemma get_released_src_le
      l loc released2_src released1_tgt released2_tgt tview_src
      (LE: View.le released1_tgt released2_tgt)
      (SIM: sim_view l released2_src released2_tgt)
      (RELEASED_SRC: released_eq_tview_loc l loc released2_src tview_src):
  <<LE: View.le (get_released_src l loc released1_tgt tview_src) released2_src>>.
Proof.
  inv LE. inv SIM. inv RELEASED_SRC. des.
  unfold get_released_src. econs; ss.
  - ii. unfold LocFun.add. condtac; ss.
    + subst. rewrite H. refl.
    + rewrite PLN0; ss. eauto.
  - ii. unfold LocFun.add. condtac; ss.
    + subst. rewrite H0. refl.
    + rewrite RLX0; ss. eauto.
Qed.

Lemma get_message_src_sim_message
      l loc msg_tgt tview_src:
  <<SIM: sim_message l (get_message_src l loc msg_tgt tview_src) msg_tgt>>.
Proof.
  unfold get_message_src.
  destruct msg_tgt; ss. destruct released; ss.
  - econs. econs. eapply get_released_src_sim_view.
  - econs. econs.
Qed.

Lemma get_message_src_wf
      l loc msg_tgt tview_src
      (MSG_TGT: Message.wf msg_tgt)
      (TVIEW_SRC: TView.wf tview_src):
  Message.wf (get_message_src l loc msg_tgt tview_src).
Proof.
  unfold get_message_src.
  destruct msg_tgt; ss. destruct released; ss.
  inv MSG_TGT. inv WF. econs. econs.
  apply get_released_src_wf; eauto.
Qed.

Lemma get_message_src_message_to
      l loc to msg_tgt tview_src
      (MSG_TGT: Memory.message_to msg_tgt loc to)
      (LOC: loc <> l):
  Memory.message_to (get_message_src l loc msg_tgt tview_src) loc to.
Proof.
  unfold get_message_src.
  destruct msg_tgt; ss. destruct released; ss.
  inv MSG_TGT. econs. ss.
  unfold LocFun.add. condtac; ss.
Qed.

Lemma get_message_src_closed
      l loc msg_tgt tview_src
      mem_src mem_tgt
      (SIM: sim_memory l mem_src mem_tgt)
      (CLOSED_SRC: TView.closed tview_src mem_src)
      (CLOSED_TGT: Memory.closed_message msg_tgt mem_tgt):
  Memory.closed_message (get_message_src l loc msg_tgt tview_src) mem_src.
Proof.
  inv CLOSED_TGT; ss.
  destruct released; eauto.
  inv CLOSED. econs. econs.
  eapply get_released_src_closed; eauto.
Qed.


Lemma sim_memory_promise
      l tview_src
      promises1_src mem1_src
      promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
      (PROMISES1: sim_memory l promises1_src promises1_tgt)
      (MEM1: sim_memory l mem1_src mem1_tgt)
      (RELEASED1: promises_released l promises1_src tview_src)
      (TVIEW_SRC: TView.wf tview_src)
      (LE1_SRC: Memory.le promises1_src mem1_src)
      (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
      (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
      (LOC: loc <> l):
  exists promises2_src mem2_src kind_src,
    <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to
                                  (get_message_src l loc msg_tgt tview_src) promises2_src mem2_src kind_src>> /\
    <<PROMISES2: sim_memory l promises2_src promises2_tgt>> /\
    <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
    <<RELEASED2: promises_released l promises2_src tview_src>>.
Proof.
  inv PROMISES1. inv MEM1. inv PROMISE_TGT.
  { (* add *)
    exploit (@Memory.add_exists mem1_src loc from to (get_message_src l loc msg_tgt tview_src)).
    { ii. exploit SOUND0; eauto. i. des.
      exploit Memory.add_get1; try exact GET_TGT; eauto. i.
      exploit Memory.add_get0; try exact MEM. i. des.
      exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des.
      { subst. congr. }
      apply (x2 x); eauto. }
    { inv MEM. inv ADD. ss. }
    { eapply get_message_src_wf; eauto.
      inv MEM. inv ADD. ss. }
    i. des.
    exploit Memory.add_exists_le; try exact x0; eauto. i. des.
    esplits.
    - econs; eauto.
      + eapply get_message_src_message_to; eauto.
      + unfold get_message_src.
        destruct msg_tgt; try destruct released; ss. i.
        exploit RESERVE; eauto. i. des.
        exploit COMPLETE0; try exact x; eauto. i. des.
        inv MSG. eauto.
      + i. exploit SOUND0; try exact GET; eauto. i. des.
        destruct msg_tgt; ss. eauto.
    - econs; i.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC.
          exploit Memory.add_get0; try exact PROMISES. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o.
          exploit SOUND; eauto. i. des.
          exploit Memory.add_get1; try exact GET_TGT; eauto.
      + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.add_get0; try exact x1. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o.
          exploit COMPLETE; eauto. i. des.
          exploit Memory.add_get1; try exact GET_SRC; eauto.
    - econs; i.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC.
          exploit Memory.add_get0; try exact MEM. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o.
          exploit SOUND0; eauto. i. des.
          exploit Memory.add_get1; try exact GET_TGT; eauto.
      + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.add_get0; try exact x0. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o.
          exploit COMPLETE0; eauto. i. des.
          exploit Memory.add_get1; try exact GET_SRC; eauto.
    - ii. revert GETP. erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst.
      unfold get_message_src.
      destruct msg_tgt; try destruct released0; ss. i. inv GETP.
      eapply get_released_src_released_eq_tview_loc; eauto.
  }
  { (* split *)
    guardH RESERVE.
    exploit Memory.split_get0; try exact PROMISES. i. des.
    clear GET GET1 GET2.
    exploit COMPLETE; eauto. i. des.
    exploit (@Memory.split_exists promises1_src loc from to ts3
                                  (get_message_src l loc msg_tgt tview_src) msg_src); eauto.
    { inv MEM. inv SPLIT. ss. }
    { inv MEM. inv SPLIT. ss. }
    { eapply get_message_src_wf; eauto.
      inv MEM. inv SPLIT. ss. }
    i. des.
    exploit Memory.split_exists_le; try exact x0; eauto. i. des.
    esplits.
    - econs 2; eauto.
      + eapply get_message_src_message_to; eauto.
      + unguard. des. subst.
        unfold get_message_src. destruct released'; eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET_SRC0.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o. des. subst. inv GET_SRC0.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          esplits; eauto.
        * guardH o. guardH o0.
          exploit SOUND; eauto. i. des.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto.
      + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.split_get0; try exact x0. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o. des. subst. inv GET_TGT.
          exploit Memory.split_get0; try exact x0. i. des.
          esplits; eauto.
        * guardH o. guardH o0.
          exploit COMPLETE; eauto. i. des.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET_SRC0.
          exploit Memory.split_get0; try exact MEM. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o. des. subst. inv GET_SRC0.
          exploit Memory.split_get0; try exact MEM. i. des.
          esplits; eauto.
        * guardH o. guardH o0.
          exploit SOUND0; eauto. i. des.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto.
      + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.split_get0; try exact x1. i. des.
          esplits; eauto.
          eapply get_message_src_sim_message; eauto.
        * guardH o. des. subst. inv GET_TGT.
          exploit Memory.split_get0; try exact x1. i. des.
          esplits; eauto.
        * guardH o. guardH o0.
          exploit COMPLETE0; eauto. i. des.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto.
    - ii. revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      + des. subst.
        unfold get_message_src.
        destruct msg_tgt; try destruct released0; ss. i. inv GETP.
        eapply get_released_src_released_eq_tview_loc; eauto.
      + guardH o. des. subst. i. inv GETP. eauto.
  }
  { (* lower *)
    exploit Memory.lower_get0; try exact PROMISES. i. des. subst.
    inv MSG_LE. clear GET0.
    exploit COMPLETE; eauto. i. des.
    exploit (@Memory.lower_exists promises1_src loc from to msg_src
                                  (get_message_src l loc (Message.full val released0) tview_src)); eauto.
    { inv MEM. inv LOWER. ss. }
    { eapply get_message_src_wf; eauto.
      inv MEM. inv LOWER. ss. }
    { ss. destruct released0.
      - inv RELEASED. inv MSG. inv RELEASED. econs. econs.
        eapply get_released_src_le; eauto.
      - inv MSG. eauto. }
    i. des.
    exploit Memory.lower_exists_le; try exact x0; eauto. i. des.
    esplits.
    - econs 3; eauto.
      + eapply get_message_src_message_to; eauto.
      + inv MSG. eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC0.
          exploit Memory.lower_get0; try exact PROMISES. i. des.
          esplits; eauto.
          destruct released0; eauto. econs. econs.
          eapply get_released_src_sim_view; eauto.
        * guardH o.
          exploit SOUND; eauto. i. des.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto.
      + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.lower_get0; try exact x0. i. des.
          esplits; eauto.
          destruct released0; eauto. econs. econs.
          eapply get_released_src_sim_view; eauto.
        * guardH o.
          exploit COMPLETE; eauto. i. des.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC0.
          exploit Memory.lower_get0; try exact MEM. i. des.
          esplits; eauto.
          destruct released0; eauto. econs. econs.
          eapply get_released_src_sim_view; eauto.
        * guardH o.
          exploit SOUND0; eauto. i. des.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto.
      + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET_TGT.
          exploit Memory.lower_get0; try exact x1. i. des.
          esplits; eauto.
          destruct released0; eauto. econs. econs.
          eapply get_released_src_sim_view; eauto.
        * guardH o.
          exploit COMPLETE0; eauto. i. des.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto.
    - ii. revert GETP. erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. destruct released0; ss. i. inv GETP.
        eapply get_released_src_released_eq_tview_loc; eauto.
      + i. eapply RELEASED1; eauto.
  }
  { (* cancel *)
    exploit Memory.remove_get0; try exact PROMISES. i. des.
    exploit COMPLETE; eauto. i. des. inv MSG.
    exploit Memory.remove_exists; try exact GET_SRC. i. des.
    exploit Memory.remove_exists_le; try exact x0; eauto. i. des.
    esplits.
    - econs 4; eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
        guardH o.
        exploit SOUND; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss.
        esplits; eauto.
      + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
        guardH o.
        exploit COMPLETE; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss.
        esplits; eauto.
    - econs; i.
      + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
        guardH o.
        exploit SOUND0; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss.
        esplits; eauto.
      + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
        guardH o.
        exploit COMPLETE0; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss.
        esplits; eauto.
    - ii. revert GETP. erewrite Memory.remove_o; eauto. condtac; ss. i.
      eapply RELEASED1; eauto.
  }
Qed.

Lemma sim_memory_promise_loc
      l
      promises1_src mem1_src
      promises1_tgt mem1_tgt from to msg_tgt promises2_tgt mem2_tgt kind_tgt
      (PROMISES1: sim_memory l promises1_src promises1_tgt)
      (MEM1: sim_memory l mem1_src mem1_tgt)
      (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt l from to msg_tgt promises2_tgt mem2_tgt kind_tgt):
    <<PROMISES2: sim_memory l promises1_src promises2_tgt>> /\
    <<MEM2: sim_memory l mem1_src mem2_tgt>>.
Proof.
  inv PROMISES1. inv MEM1. inv PROMISE_TGT.
  { (* add *)
    splits.
    - econs; i.
      + erewrite Memory.add_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; [des|]; ss; i; eauto.
    - econs; i.
      + erewrite Memory.add_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; [des|]; ss; i; eauto.
  }
  { (* split *)
    splits.
    - econs; i.
      + erewrite Memory.split_o; eauto.
        repeat condtac; [des|des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.split_o; eauto.
        repeat condtac; [des|des|]; ss; i; eauto.
    - econs; i.
      + erewrite Memory.split_o; eauto.
        repeat condtac; [des|des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.split_o; eauto.
        repeat condtac; [des|des|]; ss; i; eauto.
  }
  { (* lower *)
    splits.
    - econs; i.
      + erewrite Memory.lower_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.lower_o; eauto.
        condtac; [des|]; ss; i; eauto.
    - econs; i.
      + erewrite Memory.lower_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.lower_o; eauto.
        condtac; [des|]; ss; i; eauto.
  }
  { (* cancel *)
    splits.
    - econs; i.
      + erewrite Memory.remove_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.remove_o; eauto.
        condtac; [des|]; ss; i; eauto.
    - econs; i.
      + erewrite Memory.remove_o; eauto.
        condtac; [des|]; ss; i; eauto.
      + revert GET_TGT. erewrite Memory.remove_o; eauto.
        condtac; [des|]; ss; i; eauto.
  }
Qed.
