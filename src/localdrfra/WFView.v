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
Require Import Configuration.

Require Import SimMemory.
Require Import MemoryProps.

Set Implicit Arguments.

(* TODO: move *)

Lemma time_join_idempotent
      ts
  :
    Time.join ts ts = ts.
Proof.
  unfold Time.join. condtac; auto.
Qed.

Lemma timemap_join_idempotent
      tm
  :
    TimeMap.join tm tm = tm.
Proof.
  extensionality ts. apply time_join_idempotent; auto.
Qed.

Lemma view_join_idempotent
      vw
  :
    View.join vw vw = vw.
Proof.
  destruct vw. unfold View.join. ss. f_equal.
  - apply timemap_join_idempotent.
  - apply timemap_join_idempotent.
Qed.

Section JOINED.

  Definition wf_views (views: Loc.t -> Time.t -> list View.t): Prop :=
    forall loc ts, List.Forall View.wf (views loc ts).

  Inductive joined_view
            (views: list View.t): View.t -> Prop :=
  | joined_view_bot
    :
      joined_view views View.bot
  | joined_view_one
      vw0 vw1
      (VIEW: List.In vw0 views)
      (JOINED: joined_view views vw1)
    :
      joined_view views (View.join vw0 vw1)
  .
  Hint Constructors joined_view.

  Lemma joined_view_nil
        view
        (JOINED: joined_view [] view)
    :
      view = View.bot.
  Proof.
    ginduction JOINED; ss.
  Qed.

  Lemma joined_view_cons viewhd viewstl view
        (JOINED: joined_view (viewhd :: viewstl) view)
    :
      (<<JOINEDTL: joined_view viewstl view>>) \/
      (<<VIEW: exists view',
          (<<JOIN: view = View.join viewhd view'>>) /\
          (<<JOINEDTL: joined_view viewstl view'>>)>>).
  Proof.
    ginduction JOINED; eauto. ss. des; subst.
    - right. esplits; eauto.
    - left. econs; eauto.
    - erewrite <- View.join_assoc. erewrite view_join_idempotent.
      right. eauto.
    - right. erewrite View.join_comm. erewrite View.join_assoc. esplits; eauto.
      erewrite View.join_comm. econs; eauto.
  Qed.

  Lemma joined_view_exact
        views view
        (IN: List.In view views)
    :
      joined_view views view.
  Proof.
    erewrite <- View.join_bot_r. econs 2; eauto.
  Qed.

  Lemma joined_view_incl
        views0 views1 view
        (JOINED: joined_view views0 view)
        (INCL: forall vw (IN: List.In vw views0),
            List.In vw views1)
    :
      joined_view views1 view.
  Proof.
    ginduction JOINED; auto.
  Qed.

  Lemma joined_view_join
        views view0 view1
        (JOINED0: joined_view views view0)
        (JOINED1: joined_view views view1)
    :
      joined_view views (View.join view0 view1).
  Proof.
    ginduction JOINED0; eauto.
    - i. erewrite View.join_bot_l. auto.
    - i. erewrite View.join_assoc. econs; eauto.
  Qed.

  Inductive joined_opt_view
            (views: list View.t): option View.t -> Prop :=
  | joined_opt_view_some
      view
      (JOINED: joined_view views view)
    :
      joined_opt_view views (Some view)
  | joined_opt_view_none
    :
      joined_opt_view views None
  .
  Hint Constructors joined_view.

  Inductive joined_memory
            (views: Loc.t -> Time.t -> list View.t)
            (mem: Memory.t): Prop :=
  | joined_memory_intro
      (COMPLETE: forall loc ts from val released
                        (GET: Memory.get loc ts mem = Some (from, Message.concrete val released)),

          (<<SINGLETON: joined_view (views loc ts) (View.singleton_ur loc ts)>>) /\
          (<<JOINED: joined_opt_view (views loc ts) released>>) /\

          (* (<<JOINED: joined_view ((View.singleton_ur loc ts)::(views loc ts)) released>>) /\ *)

          (<<INCL: forall view (IN: List.In view (views loc from)),
              List.In view (views loc ts)>>)
      )
      (ONLY: forall loc ts (SOME: views loc ts <> []),
          exists from val released,
            (<<GET: Memory.get loc ts mem = Some (from, Message.concrete val released)>>))
      (CLOSED: forall loc ts, List.Forall (fun vw => Memory.closed_view vw mem) (views loc ts))
  .

  Lemma joined_view_closed
        views view mem loc ts
        (MEM: joined_memory views mem)
        (JOINED: joined_view (views loc ts) view)
        (INHABITED: Memory.inhabited mem)
    :
      Memory.closed_view view mem.
  Proof.
    ginduction JOINED; eauto.
    - i. eapply Memory.closed_view_bot; auto.
    - i. eapply Memory.join_closed_view; eauto.
      inv MEM. eapply List.Forall_forall in VIEW; [|eauto]. ss.
  Qed.

  Lemma joined_opt_view_closed
        views view mem loc ts
        (MEM: joined_memory views mem)
        (JOINED: joined_opt_view (views loc ts) view)
        (INHABITED: Memory.inhabited mem)
    :
      Memory.closed_opt_view view mem.
  Proof.
    inv JOINED; econs. eapply joined_view_closed; eauto.
  Qed.

  Definition views_le
             (views0 views1: Loc.t -> Time.t -> list View.t): Prop :=
    forall loc ts (VIEW0: views0 loc ts <> []), views1 loc ts = views0 loc ts.

  Global Program Instance views_le_PreOrder: PreOrder views_le.
  Next Obligation.
  Proof. ii. auto. Qed.
  Next Obligation.
  Proof. ii. erewrite <- H in *; auto. Qed.

  Record max_le_joined_view
         (views: list View.t)
         (view: View.t)
         (max: View.t): Prop :=
    {
      max_le_joined_view_joined: joined_view views max;
      max_le_joined_view_le: View.le max view;
      max_le_joined_view_max: forall vw
                                     (JOINED: joined_view views vw)
                                     (VIEWLE: View.le vw view),
          View.le vw max;
    }.
  Hint Constructors max_le_joined_view.

  Lemma max_le_joined_view_exists
        views view
        (VIEWSWF: List.Forall View.wf (views))
    :
      exists max,
        (<<MAX: max_le_joined_view views view max>>) /\
        (<<VIEWWF: View.wf max>>)
  .
  Proof.
    ginduction views.
    - exists View.bot. esplits; [econs|]; eauto.
      + eapply View.bot_spec.
      + i. eapply joined_view_nil in JOINED. subst. refl.
      + eapply View.bot_wf.
    - i. inv VIEWSWF. specialize (IHviews view H2). des. inv MAX.
      destruct (classic (View.le a view)).
      + exists (View.join a max). esplits; [econs|].
        * econs; ss; auto.
          eapply joined_view_incl; eauto. i. ss. auto.
        * eapply View.join_spec; eauto.
        * i. apply joined_view_cons in JOINED. des.
          { etrans.
            - eapply max_le_joined_view_max0; auto.
            - apply View.join_r. }
          { subst. eapply View.join_le.
            - refl.
            - eapply max_le_joined_view_max0; eauto.
              etrans; eauto. eapply View.join_r. }
        * eapply View.join_wf; eauto.
      + exists max. esplits; [econs|]; auto.
        * eapply joined_view_incl; eauto. i. ss. auto.
        * i. apply joined_view_cons in JOINED. des.
          { apply max_le_joined_view_max0; auto. }
          { subst. exfalso. eapply H.
            etrans; eauto. eapply View.join_l. }
  Qed.

  Inductive max_le_joined_opt_view
            (views: list View.t):
    forall (view max: option View.t), Prop :=
  | max_le_joined_opt_view_some
      view max
      (MAXLE: max_le_joined_view views view max)
    :
      max_le_joined_opt_view views (Some view) (Some max)
  | max_le_joined_opt_view_none
    :
      max_le_joined_opt_view views None None
  .
  Hint Constructors max_le_joined_opt_view.

  Lemma max_le_joined_opt_view_exists
        views view
        (VIEWSWF: List.Forall View.wf (views))
    :
      exists max,
        (<<MAX: max_le_joined_opt_view views view max>>) /\
        (<<VIEWWF: View.opt_wf max>>)
  .
  Proof.
    destruct view.
    - hexploit (@max_le_joined_view_exists views t); auto. i. des.
      inv MAX. exists (Some max). econs; ss; eauto.
    - exists None. econs; eauto.
  Qed.

  Inductive max_le_joined_message
            (views: list View.t):
    forall (msg max: Message.t), Prop :=
  | max_le_joined_message_concrete
      val view max
      (MAXLE: max_le_joined_opt_view views view max)
    :
      max_le_joined_message views (Message.concrete val view) (Message.concrete val max)
  | max_le_joined_message_reserve
    :
      max_le_joined_message views Message.reserve Message.reserve
  .

  Lemma max_le_joined_message_exists
        views msg
        (VIEWSWF: List.Forall View.wf (views))
    :
      exists max,
        (<<MAX: max_le_joined_message views msg max>>) /\
        (<<MAGWF: Message.wf max>>)
  .
  Proof.
    destruct msg.
    - hexploit (@max_le_joined_opt_view_exists views released); auto. i. des.
      exists (Message.concrete val max). esplits; econs; ss.
    - exists Message.reserve. esplits; econs; eauto.
  Qed.

  Lemma max_le_joined_message_le
        views msg max
        (MAX: max_le_joined_message views msg max)
    :
      sim_message max msg.
  Proof.
    inv MAX; eauto. inv MAXLE; eauto. inv MAXLE0; eauto.
  Qed.

  Inductive joined_released
            (views: Loc.t -> Time.t -> list View.t)
            (prom: Memory.t)
            (rel: Loc.t -> View.t): Prop :=
  | joined_released_intro
      (COMPLETE: forall loc ts from val released
                        (GET: Memory.get loc ts prom = Some (from, Message.concrete val (Some released))),
          joined_view (views loc ts) (rel loc))
  .

End JOINED.


Section STEP.

  Inductive step lang: forall (pf:bool) (e:ThreadEvent.t)
                              (e1 e2:Thread.t lang)
                              (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | step_intro
      pf e e1 e2 views1 views2
      (STEP: Thread.step pf e e1 e2)

      (PROMISE:
         forall loc from to val released kind
                (EVENT: e = ThreadEvent.promise loc from to (Message.concrete val released) kind),
           ((<<NADD: kind <> Memory.op_kind_add>>) /\
            (<<JOINED: joined_opt_view (views1 loc to) released>>))
           \/
           ((<<ADD: kind = Memory.op_kind_add>>) /\
            (<<JOINED: joined_opt_view
                         ((View.singleton_ur loc to)
                            ::(e1.(Thread.local).(Local.tview).(TView.rel) loc)
                            ::(views1 loc from)) released>>)))

      (VIEWSLE:
         (<<VIEWSEQ: views1 = views2>>) \/
         (<<VIEWSLE: forall loc ts (NEQ: views2 loc ts <> views1 loc ts),
             (<<NIL: views1 loc ts = []>>) /\
             exists from,
               (<<CONS: views2 loc ts = (e2.(Thread.local).(Local.tview).(TView.rel) loc)::(views2 loc from)>>)>>))
      (VIEWSWF: wf_views views2)

      (MEMORY: joined_memory views2 e2.(Thread.memory))
      (RELEASED: joined_released views2 e2.(Thread.local).(Local.promises) e2.(Thread.local).(Local.tview).(TView.rel))
    :
      step pf e e1 e2 views1 views2
  .
  Hint Constructors step.

  Lemma step_thread_step lang pf e (e1 e2: Thread.t lang) views1 views2
        (STEP: step pf e e1 e2 views1 views2)
    :
      Thread.step pf e e1 e2.
  Proof.
    inv STEP. auto.
  Qed.

  Lemma step_views_le lang pf e (e1 e2: Thread.t lang) views1 views2
        (STEP: step pf e e1 e2 views1 views2)
    :
      views_le views1 views2.
  Proof.
    inv STEP. des.
    - subst. refl.
    - ii. apply NNPP. ii. exploit VIEWSLE0; eauto. i. des. ss.
  Qed.

  Inductive rtc_tau lang: forall (e1 e2: Thread.t lang)
                                 (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | rtc_tau_base
      e1 views1
    :
      rtc_tau e1 e1 views1 views1
  | rtc_tau_step
      pf e e1 e2 e3 views1 views2 views3
      (STEP: step pf e e1 e2 views1 views2)
      (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
      (STEPS: rtc_tau e2 e3 views2 views3)
    :
      rtc_tau e1 e3 views1 views3
  .
  Hint Constructors rtc_tau.

  Lemma tau_steps_thread_tau_steps lang (e1 e2: Thread.t lang) views1 views2
        (STEPS: rtc_tau e1 e2 views1 views2)
    :
      rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    ginduction STEPS.
    - refl.
    - econs; eauto. econs; eauto. econs. eapply step_thread_step; eauto.
  Qed.

  Definition consistent lang (e: Thread.t lang)
             (views1: Loc.t -> Time.t -> list View.t): Prop :=
    forall (mem1 : Memory.t) (sc1 : TimeMap.t)
           (CAP: Memory.cap e.(Thread.memory) mem1)
           (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
    exists e2 views2,
      (<<STEPS: rtc_tau (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2
                        views1 views2>>) /\
      ((<<FAILURE: exists e3, <<FAILURE: Thread.step true ThreadEvent.failure e2 e3>> >>) \/
       (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>)).

  Lemma consistent_thread_consistent lang (e: Thread.t lang) views
        (CONSISTENT: consistent e views)
    :
      Thread.consistent e.
  Proof.
    ii. exploit CONSISTENT; eauto. i. des.
    - left. unfold Thread.steps_failure. esplits.
      + eapply tau_steps_thread_tau_steps; eauto.
      + eauto.
    - right. esplits.
      + eapply tau_steps_thread_tau_steps; eauto.
      + eauto.
  Qed.

  Inductive configuration_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t)
                                       (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | configuration_step_intro
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      views1 views2 views3
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc_tau (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2 views1 views2)
      (STEP: step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3) views2 views3)
      (CONSISTENT: forall (NORMAL: e <> ThreadEvent.failure),
          consistent (Thread.mk _ st3 lc3 sc3 memory3) views3)
    :
      configuration_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3) views1 views3
  .

  Lemma step_configuration_step e tid c1 c2 views1 views2
        (STEP: configuration_step e tid c1 c2 views1 views2)
    :
      Configuration.step e tid c1 c2.
  Proof.
    inv STEP. destruct (classic (e0 = ThreadEvent.failure)).
    - subst. ss. econs; try eassumption.
      + eapply tau_steps_thread_tau_steps; eauto.
      + eapply step_thread_step; eauto.
    - econs; try eassumption.
      + eapply tau_steps_thread_tau_steps; eauto.
      + eapply step_thread_step; eauto.
      + eapply consistent_thread_consistent; eauto.
  Qed.

End STEP.

Section SIMULATION.

  Inductive joined_promise_content
            (views: list View.t)
  : forall (msg_src msg_tgt: option (Time.t * Message.t)), Prop :=
  | joined_promise_content_concrete
      from val released_src released_tgt
      (RELEASED: max_le_joined_opt_view views released_src released_tgt)
      (NIL: views <> [])
    :
      joined_promise_content
        views
        (Some (from, Message.concrete val released_src))
        (Some (from, Message.concrete val released_tgt))
  | joined_promise_content_reserve
      from
    :
      joined_promise_content
        views
        (Some (from, Message.reserve))
        (Some (from, Message.reserve))
  | joined_promise_content_none
    :
      joined_promise_content
        views
        None
        None
  .
  Hint Constructors joined_promise_content.

  Definition sim_joined_promises (views: Loc.t -> Time.t -> list View.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      joined_promise_content (views loc ts) (Memory.get loc ts prom_src) (Memory.get loc ts prom_tgt).

  Lemma sim_joined_promises_le
        prom_src prom_tgt views0 views1
        (PROM: sim_joined_promises views0 prom_src prom_tgt)
        (VIEWSLE: views_le views0 views1)
    :
      sim_joined_promises views1 prom_src prom_tgt.
  Proof.
    ii. specialize (PROM loc ts). inv PROM; eauto.
    exploit VIEWSLE; eauto. i. rewrite x. auto.
  Qed.

  Lemma joined_released_le
        prom rel views0 views1
        (REL: joined_released views0 prom rel)
        (VIEWSLE: views_le views0 views1)
    :
      joined_released views1 prom rel.
  Proof.
    inv REL. econs. i. exploit COMPLETE; eauto. i.
    destruct (views0 loc ts) eqn:VIEW.
    - eapply joined_view_incl; eauto. i. ss.
    - exploit VIEWSLE; eauto.
      { erewrite VIEW. ss. }
      i. rewrite x0. rewrite VIEW. auto.
  Qed.

  Require Import SimLocal.

  Inductive sim_local (views: Loc.t -> Time.t -> list View.t):
    forall (lc_src lc_tgt: Local.t), Prop :=
  | sim_local_intro
      vw_src vw_tgt prom_src prom_tgt
      (TVIEW: TView.le vw_src vw_tgt)
      (PROMISES: sim_joined_promises views prom_src prom_tgt)
      (REL: joined_released views prom_src vw_src.(TView.rel))
    :
      sim_local
        views
        (Local.mk vw_src prom_src)
        (Local.mk vw_tgt prom_tgt)
  .
  Hint Constructors sim_local.

  Lemma sim_local_le
        lc_src lc_tgt views0 views1
        (SIM: sim_local views0 lc_src lc_tgt)
        (VIEWSLE: views_le views0 views1)
    :
      sim_local views1 lc_src lc_tgt.
  Proof.
    inv SIM. econs; eauto.
    - eapply sim_joined_promises_le; eauto.
    - eapply joined_released_le; eauto.
  Qed.

  Inductive sim_statelocal (views: Loc.t -> Time.t -> list View.t):
    forall (stlc_src stlc_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
  | sim_statelocal_intro
      lang st lc_src lc_tgt
      (LOCAL: sim_local views lc_src lc_tgt)
    :
      sim_statelocal
        views
        (existT _ lang st, lc_src)
        (existT _ lang st, lc_tgt)
  .
  Hint Constructors sim_statelocal.

  Lemma sim_statelocal_le
        stlc_src stlc_tgt views0 views1
        (SIM: sim_statelocal views0 stlc_src stlc_tgt)
        (VIEWSLE: views_le views0 views1)
    :
      sim_statelocal views1 stlc_src stlc_tgt.
  Proof.
    inv SIM. econs; eauto.
    eapply sim_local_le; eauto.
  Qed.

  Inductive sim_configuration (views: Loc.t -> Time.t -> list View.t):
    forall (c_src c_tgt: Configuration.t), Prop :=
  | sim_configuration_intro
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (THS: forall tid,
          option_rel
            (sim_statelocal views)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt))
      (MEM: sim_memory mem_src mem_tgt)
      (MEMORY: joined_memory views mem_src)
      (SC: TimeMap.le sc_src sc_tgt)
      (WFSRC: Configuration.wf (Configuration.mk ths_src sc_src mem_src))
      (WFTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (VIEWSWF: wf_views views)
    :
      sim_configuration
        views
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration.

  Inductive sim_thread (views: Loc.t -> Time.t -> list View.t):
    forall lang0 lang1 (th0: Thread.t lang0) (th1: Thread.t lang1), Prop :=
  | sim_thread_intro
      lang st vw_src vw_tgt prom_src prom_tgt
      mem_src mem_tgt sc_src sc_tgt
      (TVIEW: TView.le vw_src vw_tgt)
      (PROM: sim_joined_promises views prom_src prom_tgt)
      (REL: joined_released views prom_src vw_src.(TView.rel))
      (MEM: sim_memory mem_src mem_tgt)
      (MEMORY: joined_memory views mem_src)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_thread
        views
        (Thread.mk lang st (Local.mk vw_src prom_src) sc_src mem_src)
        (Thread.mk lang st (Local.mk vw_tgt prom_tgt) sc_tgt mem_tgt)
  .
  Hint Constructors sim_thread.

  Lemma sim_local_read
        views
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        lc2_tgt
        loc ts val released_tgt ord_src ord_tgt
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (ORD: Ordering.le ord_src ord_tgt):
    exists released_src lc2_src,
      (<<REL: View.opt_le released_src released_tgt>>) /\
      (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
      (<<LOCAL2: sim_local views lc2_src lc2_tgt>>).
  Proof.
    inv LOCAL1. inv STEP_TGT.
    exploit sim_memory_get; try apply GET; eauto. i. des.
    inv MSG. esplits; eauto.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto. apply TVIEW.
    - econs; eauto. s. apply TViewFacts.read_tview_mon; auto.
      + apply WF1_TGT.
      + inv MEM1_TGT. exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
  Qed.

  Lemma sim_local_nonsynch_loc
        views loc lc_src lc_tgt
        (SIM: sim_local views lc_src lc_tgt)
        (NONSYNCH: Memory.nonsynch_loc loc lc_tgt.(Local.promises)):
    Memory.nonsynch_loc loc lc_src.(Local.promises).
  Proof.
    inv SIM. ii. destruct msg; ss.
    specialize (PROMISES loc t). rewrite GET in *. inv PROMISES.
    exploit NONSYNCH; eauto. ss. i. subst. inv RELEASED. ss.
  Qed.

  Lemma sim_local_nonsynch
        views lc_src lc_tgt
        (SIM: sim_local views lc_src lc_tgt)
        (NONSYNCH: Memory.nonsynch lc_tgt.(Local.promises)):
    Memory.nonsynch lc_src.(Local.promises).
  Proof.
    ii. eapply sim_local_nonsynch_loc; eauto.
  Qed.

  Lemma sim_local_fence
        views
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt
        ordr_src ordw_src
        ordr_tgt ordw_tgt
        (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (ORDR: Ordering.le ordr_src ordr_tgt)
        (ORDW: Ordering.le ordw_src ordw_tgt):
    exists lc2_src sc2_src,
      (<<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>>) /\
      (<<LOCAL2: sim_local views lc2_src lc2_tgt>>) /\
      (<<SC2: TimeMap.le sc2_src sc2_tgt>>).
  Proof.
    inv STEP_TGT. esplits; eauto.
    - econs; eauto. i. eapply sim_local_nonsynch; eauto.
    - inv LOCAL1. inv WF1_SRC. inv WF1_TGT. econs.
      + eapply TViewFacts.write_fence_tview_mon; eauto.
        * eapply TViewFacts.read_fence_tview_mon; eauto.
        * eapply TViewFacts.read_fence_future; eauto.
      + ss.
      + ss. econs. ii.
        inv REL. exploit COMPLETE; eauto. i.
        specialize (PROMISES loc ts).
        rewrite GET in *. inv PROMISES. inv RELEASED.
        condtac; auto. condtac; auto.
        * exploit RELEASE; eauto; ss. destruct ordw_src, ordw_tgt; ss.
        * exploit RELEASE; eauto; ss. destruct ordw_src, ordw_tgt; ss.
    - inv LOCAL1. inv WF1_SRC. inv WF1_TGT.
      apply TViewFacts.write_fence_sc_mon; auto; try refl.
      apply TViewFacts.read_fence_tview_mon; auto; try refl.
  Qed.

  Lemma sim_local_promise_consistent
        views
        lc_src lc_tgt
        (LOCAL: sim_local views lc_src lc_tgt)
        (CONS_TGT: Local.promise_consistent lc_tgt):
    (<<CONS_SRC: Local.promise_consistent lc_src>>).
  Proof.
    inv LOCAL. ii. ss.
    specialize (PROMISES loc ts). rewrite PROMISE in *. inv PROMISES.
    exploit CONS_TGT; eauto. i. ss.
    eapply TimeFacts.le_lt_lt; eauto.
    inv TVIEW. inv CUR. eauto.
  Qed.

  Lemma sim_local_failure
        views
        lc1_src lc1_tgt
        (STEP_TGT: Local.failure_step lc1_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt):
    (<<STEP_SRC: Local.failure_step lc1_src>>).
  Proof.
    inv STEP_TGT.
    hexploit sim_local_promise_consistent; eauto.
  Qed.

  Lemma sim_message_to msg_src msg_tgt loc to
        (MSGTO: Memory.message_to msg_tgt loc to)
        (MSG: sim_message msg_src msg_tgt)
    :
      Memory.message_to msg_src loc to.
  Proof.
    inv MSGTO; inv MSG; econs. etrans; eauto.
    eapply View.unwrap_opt_le in RELEASED. inv RELEASED. auto.
  Qed.

  Lemma sim_local_promise
        views1
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        lc2_tgt mem2_tgt
        loc from to msg_tgt kind_tgt
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt)
        (LOCAL1: sim_local views1 lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (JOINMEM1: joined_memory views1 mem1_src)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (WFVIEWS1: wf_views views1)
    (* (CONS_TGT: Local.promise_consistent lc1_tgt) *)
    :
      exists msg_src kind_src lc2_src mem2_src views2,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
        (<<LOCAL2: sim_local views2 lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views2 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views1>>)
  .
  Proof.
    inv STEP_TGT. inv PROMISE.
    - assert (NOATTACH: forall ts msg
                               (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
      { admit. }

      destruct msg_tgt as [val released_tgt|].
      {
        set (views :=((View.singleton_ur loc to)
                        ::(lc1_src.(Local.tview).(TView.rel) loc)
                        ::(views1 loc from))).
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs.
          { eapply View.singleton_ur_wf; eauto. }
          econs.
          { inv WF1_SRC. inv TVIEW_WF. ss. }
          eauto.
        }
        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then views
                                  else views1 l t).
        hexploit (@max_le_joined_opt_view_exists views released_tgt); auto. i. des.
        (* hexploit max_le_joined_opt_view_le; eauto. intros SIMMSG. *)

        hexploit add_succeed_wf; try apply MEM; eauto. i. des.
        hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val max)); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        { econs; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC]. exists (Message.concrete val max).

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { dup JOINMEM1. inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits.
              * eapply joined_view_exact. ss. auto.
              * inv MAX; econs. inv MAXLE. auto.
              * i. des; auto.
            + ss. des; clarify. exfalso. eauto.
            + eapply COMPLETE; eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
            + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
          - unfold views2. ii. des_ifs.
            + ss. des; clarify. unfold views. econs.
              { eapply Memory.singleton_ur_closed_view.
                - eapply Memory.add_get0; eauto.
                - inv MEM1_SRC. eapply Memory.add_inhabited; eauto. }
              econs.
              { inv WF1_SRC. inv TVIEW_CLOSED.
                eapply Memory.add_closed_view; eauto. }
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto. }

        esplits.
        { econs; eauto.
          - econs; eauto.
            eapply sim_message_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - econs. eapply joined_opt_view_closed; eauto.
            + instantiate (1:=to). instantiate (1:=loc).


            +


            eapply joined_view_closed.

            econs.


            + i.
              admit.
          - inv MAX; eauto. inv MAXLE; eauto. inv MAXLE0.
            econs. econs.




            unfold views in *.
            admit.
          +

            ss. des; clarify.


          des_ifs.
          + ss. des; clarify. unfold views2. des_ifs; ss; des; clarify.
            { exfalso. eapply Time.lt_strorder; eauto. } splits.
            * eapply joined_view_exact. ss. auto.
            * inv MAX. inv MAXLE; econs. inv MAXLE0. ss.
            * i. des; auto.
          + guardH o. unfold views2. des_ifs; ss; des; clarify.


          unfold views2. des_ifs.
          + ss. des; clarify. splits.
            * eapply joined_view_exact. ss. auto.
            * inv MAX. inv MAXLE; econs. inv MAXLE0. ss.
            * i. des; auto.
          + ss. des; clarify. splits.
            * eapply joined_view_exact. ss. auto.
            * inv MAX. inv MAXLE; econs. inv MAXLE0. ss.
            * i. des; auto.
          + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
            i.
            admit.
          + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
            i.
            admit.
          +

            splits.
            * eapply eapply joined_view_exact. ss. auto.
            * inv MAX. inv MAXLE; econs. inv MAXLE0. ss.
            * i. des; auto.
          + ss. des; clarify. splits.
            * eapply joined_view_exact. ss. auto.
            * inv MAX. inv MAXLE; econs. inv MAXLE0. ss.
            * i. des; auto.
          +

              eapply joined_view_exact. ss. auto.
            *


            admit.
          + admit.
          +


            exfalso. ss. des; clarify.

            nfold ss. des; clarify.



      hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to max); eauto.
      { inv WF1_SRC. auto. }
      intros [prom2_src PROMISES_SRC]. exists max. esplits.
      { econs; eauto.
        - econs; eauto.
          + eapply sim_message_to; eauto.
          + i.
            admit.
        - inv MAX; eauto. inv MAXLE; eauto. inv MAXLE0.
          econs. econs.


            admit.
        -

Memory.promise

      i. des.

        admit. }
      { auto.

        specialize (MEM1 loc to2).
        eapply DISJOINT.



    Local.


    (<<REL: joined_released lc2_src.(Local.promise prom_src vw_src.(TView.rel)

      (MEMORY: joined_memory views mem_src)



  Lemma sim_local_write
        pview
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt mem2_tgt
        loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
        (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
        (RELM_SRC_WF: View.opt_wf releasedm_src)
        (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
        (RELM_TGT_WF: View.opt_wf releasedm_tgt)
        (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
        (ORD: Ordering.le ord_src ord_tgt)
        (PVIEW: SimPromises.mem loc to pview = false \/
                Ordering.le ord_tgt Ordering.plain \/
                Ordering.le Ordering.strong_relaxed ord_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
        (LOCAL1: sim_local pview lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists released_src lc2_src sc2_src mem2_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src
                                   released_src
                                   ord_src lc2_src sc2_src mem2_src
                                   (SimPromises.kind_transf loc to pview kind)>> /\
                  <<REL2: View.opt_le released_src released_tgt>> /\
                          <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src lc2_tgt>> /\
                                    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
                                           <<MEM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    guardH PVIEW.
    exploit write_promise_fulfill; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_fulfill; try apply STEP2;
      try apply LOCAL2; try apply MEM2; eauto.
    { eapply Memory.future_closed_opt_view; eauto. }
    { unguardH PVIEW. des; intuition.
      exploit Local.write_step_strong_relaxed; eauto. i.
      left. eapply sim_local_promise_not_lower; try exact STEP1; eauto.
    }
    i. des.
    exploit promise_fulfill_write_sim_memory; try exact STEP_SRC; try exact STEP_SRC0; eauto.
    { i. hexploit ORD0; eauto.
      eapply sim_local_nonsynch_loc; eauto.
    }
    i. des. subst. esplits; eauto.
    - apply TViewFacts.write_released_mon; ss;
        try apply LOCAL1; try apply WF1_TGT.
    - etrans; eauto.
  Qed.



  Lemma sim_read
    :

        forall (pview : SimPromises.SimPromises.t) (lc1_src : Local.t) (mem1_src : Memory.t)
    (lc1_tgt : Local.t) (mem1_tgt : Memory.t) (lc2_tgt : Local.t) (loc : Loc.t)
    (ts : Time.t) (val : Const.t) (released_tgt : option View.t) (ord_src ord_tgt : Ordering.t),
  Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt ->
  sim_local pview lc1_src lc1_tgt ->
  sim_memory mem1_src mem1_tgt ->
  Local.wf lc1_src mem1_src ->
  Local.wf lc1_tgt mem1_tgt ->
  Memory.closed mem1_src ->
  Memory.closed mem1_tgt ->
  Ordering.le ord_src ord_tgt ->
  exists (released_src : option View.t) (lc2_src : Local.t),
    << View.opt_le released_src released_tgt >> /\
    << Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src >> /\
    << sim_local pview lc2_src lc2_tgt >>




  sim_memory

  Lemma sim_

  L



           Thread.t

    (views: Loc.t -> Time.t -> list View.t):
    forall (c_src c_tgt: Configuration.t), Prop :=
  | sim_configuration_intro
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (THS: forall tid,
          option_rel
            (sim_statelocal views)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt))
      (MEM: sim_memory mem_src mem_tgt)
      (MEMORY: joined_memory views mem_src)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_configuration
        views
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .


  Configuration.step
