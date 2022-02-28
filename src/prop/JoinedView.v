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
Require Import Single.

Require Import SimMemory.
Require Import MemoryProps.

Require Import Behavior.
Require Import Program.

Set Implicit Arguments.


Section JOINED.

  Definition views_le
             (views0 views1: Loc.t -> Time.t -> list View.t): Prop :=
    forall loc ts (VIEW0: views0 loc ts <> []), views1 loc ts = views0 loc ts.

  Global Program Instance views_le_PreOrder: PreOrder views_le.
  Next Obligation.
  Proof. ii. auto. Qed.
  Next Obligation.
  Proof. ii. erewrite <- H in *; auto. Qed.

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
    - erewrite <- View.join_assoc.
      erewrite (@View.le_join_l vw0 vw0); try refl. eauto.
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
                        (GET: Memory.get loc ts mem = Some (from, Message.concrete val (Some released))),

          (<<JOINED: joined_view (views loc ts) released>>) /\

          (<<INCL: forall view (IN: List.In view (views loc from)),
              List.In (View.join view (View.singleton_ur loc ts)) (views loc ts)>>)
      )
      (ONLY: forall loc ts (SOME: views loc ts <> []),
          exists from val released,
            (<<GET: Memory.get loc ts mem = Some (from, Message.concrete val released)>>))
      (CLOSED: forall loc ts, List.Forall (fun vw => Memory.closed_view vw mem) (views loc ts))
  .

  Lemma joined_view_closed
        views view mem
        (MEM: List.Forall (fun vw => Memory.closed_view vw mem) views)
        (JOINED: joined_view views view)
        (INHABITED: Memory.inhabited mem)
    :
      Memory.closed_view view mem.
  Proof.
    ginduction JOINED; eauto.
    - i. eapply Memory.closed_view_bot; auto.
    - i. eapply Memory.join_closed_view; eauto.
      eapply List.Forall_forall in VIEW; [|eauto]. ss.
  Qed.

  Lemma joined_memory_get_closed
        views mem loc to from msg
        (MEM: joined_memory views mem)
        (GET: Memory.get loc to mem = Some (from, msg))
        (INHABITED: Memory.inhabited mem)
    :
      Memory.closed_message msg mem.
  Proof.
    inv MEM. destruct msg as [val [released|]| |]; eauto. econs. econs.
    exploit COMPLETE; eauto. i. des.
    eapply joined_view_closed; eauto.
  Qed.

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

  Lemma max_le_joined_view_le_le
        views view0 view1 max0 max1
        (MAXLE0: max_le_joined_view views view0 max0)
        (MAXLE1: max_le_joined_view views view1 max1)
        (VIEWLE: View.le view0 view1)
    :
      View.le max0 max1.
  Proof.
    eapply max_le_joined_view_max; eauto.
    - eapply max_le_joined_view_joined; eauto.
    - etrans; eauto. eapply max_le_joined_view_le; eauto.
  Qed.

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

  Lemma max_le_joined_opt_view_le_le
        views view0 view1 max0 max1
        (MAXLE0: max_le_joined_opt_view views view0 max0)
        (MAXLE1: max_le_joined_opt_view views view1 max1)
        (VIEWLE: View.opt_le view0 view1)
    :
      View.opt_le max0 max1.
  Proof.
    inv MAXLE0; inv MAXLE1; inv VIEWLE; eauto.
    econs. eapply max_le_joined_view_le_le; eauto.
  Qed.

  Lemma max_le_joined_opt_view_joined
        views view max
        (MAXLE: max_le_joined_opt_view views view max)
    :
      joined_opt_view views max.
  Proof.
    inv MAXLE; econs. eapply max_le_joined_view_joined; eauto.
  Qed.

  Lemma max_le_joined_opt_view_le
        views view max
        (MAXLE: max_le_joined_opt_view views view max)
    :
      View.opt_le max view.
  Proof.
    inv MAXLE; econs. eapply max_le_joined_view_le; eauto.
  Qed.

  Lemma max_le_joined_opt_view_max
        views view max
        (MAXLE: max_le_joined_opt_view views view max)
        vw
        (JOINED: joined_opt_view views vw)
        (VIEWLE: View.opt_le vw view)
    :
      View.opt_le vw max.
  Proof.
    inv MAXLE; auto. inv JOINED; econs. inv VIEWLE.
    eapply max_le_joined_view_max; eauto.
  Qed.

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
  | max_le_joined_message_undef
    :
      max_le_joined_message views Message.undef Message.undef
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
    - exists Message.undef. esplits; econs; eauto.
    - exists Message.reserve. esplits; econs; eauto.
  Qed.

  Lemma max_le_joined_message_le
        views msg max
        (MAX: max_le_joined_message views msg max)
    :
      Message.le max msg.
  Proof.
    inv MAX; eauto. inv MAXLE; eauto.
    { econs; ss.
      { refl. }
      { inv MAXLE0; eauto. }
    }
    { econs; ss. refl. }
  Qed.

  Definition joined_released
             (views: Loc.t -> Time.t -> list View.t)
             (prom: Memory.t)
             (rel: Loc.t -> View.t): Prop :=
    forall loc ts from val released
           (GET: Memory.get loc ts prom = Some (from, Message.concrete val (Some released))),
      List.In (View.join (rel loc) (View.singleton_ur loc ts)) (views loc ts)
  .

  Lemma joined_released_le
        prom rel views0 views1
        (REL: joined_released views0 prom rel)
        (VIEWSLE: views_le views0 views1)
    :
      joined_released views1 prom rel.
  Proof.
    ii. exploit REL; eauto. i. des.
    destruct (views0 loc ts) eqn:VIEW; ss.
    exploit VIEWSLE; eauto.
    { erewrite VIEW. ss. }
    i. rewrite x0. rewrite VIEW. eauto.
  Qed.

  Definition all_join_views (view: View.t) (views: list View.t) :=
    List.map (fun vw => View.join vw view) views.

  Lemma all_join_views_in view views
        vw
        (IN: List.In vw views)
    :
      List.In (View.join vw view) (all_join_views view views).
  Proof.
    eapply List.in_map with (f:= fun vw => View.join vw view) in IN. ss.
  Qed.

  Lemma all_join_views_in_iff view views
        vw
        (IN: List.In vw (all_join_views view views))
    :
      exists vw',
        (<<IN: List.In vw' views>>) /\
        (<<VIEW: vw = View.join vw' view>>)
  .
  Proof.
    eapply List.in_map_iff in IN; eauto. des. subst. eauto.
  Qed.

  Lemma all_join_views_wf view views
        (VIEWWF: View.wf view)
        (VIEWSWF: List.Forall View.wf views)
    :
      List.Forall View.wf (all_join_views view views).
  Proof.
    ginduction views; eauto. i. ss. inv VIEWSWF. econs; eauto.
    eapply View.join_wf; eauto.
  Qed.

  Lemma all_join_views_closed view views mem
        (VIEWCLOSED: Memory.closed_view view mem)
        (VIEWSCLOSED: List.Forall (fun vw => Memory.closed_view vw mem) views)
    :
      List.Forall (fun vw => Memory.closed_view vw mem) (all_join_views view views).
  Proof.
    ginduction views; eauto. i. ss. inv VIEWSCLOSED. econs; eauto.
    eapply Memory.join_closed_view; eauto.
  Qed.

  Lemma all_join_views_joined view views vw
        (JOINED: joined_view views vw)
    :
      (<<BOT: vw = View.bot>>) \/
      (<<JOINED: joined_view (all_join_views view views) (View.join view vw)>>).
  Proof.
    ginduction JOINED; i; auto. hexploit IHJOINED; eauto. i. des.
    - subst. erewrite View.join_bot_r. right. erewrite View.join_comm.
      eapply joined_view_exact. eapply all_join_views_in; eauto.
    - right. erewrite view_join_dist. eapply joined_view_join; eauto.
      eapply joined_view_exact. erewrite View.join_comm. eapply all_join_views_in; eauto.
  Qed.

End JOINED.


Module JThread.

  Inductive step lang: forall (pf:bool) (e:ThreadEvent.t)
                              (e1 e2:Thread.t lang)
                              (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | step_intro
      pf e e1 e2 views1 views2
      (STEP: Thread.step pf e e1 e2)

      (PROMISE:
         forall loc from to val released kind
                (EVENT: e = ThreadEvent.promise loc from to (Message.concrete val released) kind),
           (<<JOINED: joined_opt_view (views2 loc to) released>>))

      (VIEWSLE: forall loc ts (NEQ: views2 loc ts <> views1 loc ts),
          (<<NIL: views1 loc ts = []>>) /\
          exists from val released,
            (<<GET: Memory.get loc ts (Thread.memory e2) = Some (from, Message.concrete val (Some released))>>) /\
            (<<NONE: Memory.get loc ts (Thread.memory e1) = None>>) /\
            (<<VIEW: views2 loc ts = (View.join ((Local.tview (Thread.local e2)).(TView.rel) loc) (View.singleton_ur loc ts))
                                       ::(all_join_views (View.singleton_ur loc ts) (views1 loc from))>>))

      (VIEWSWF: wf_views views2)
      (MEMORY: joined_memory views2 (Thread.memory e2))
      (RELEASED: joined_released views2 (Local.promises (Thread.local e2)) (Local.tview (Thread.local e2)).(TView.rel))
    :
      step pf e e1 e2 views1 views2
  .
  Hint Constructors step.

  Inductive opt_step lang: forall (e:ThreadEvent.t)
                                  (e1 e2:Thread.t lang)
                                  (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | opt_step_none
      e views:
      opt_step ThreadEvent.silent e e views views
  | opt_step_some
      pf e e1 e2 views1 views2
      (STEP: step pf e e1 e2 views1 views2):
      opt_step e e1 e2 views1 views2
  .
  Hint Constructors opt_step.

  Lemma step_thread_step lang pf e (e1 e2: Thread.t lang) views1 views2
        (STEP: step pf e e1 e2 views1 views2)
    :
      Thread.step pf e e1 e2.
  Proof.
    inv STEP. auto.
  Qed.

  Lemma opt_step_thread_opt_step lang e (e1 e2: Thread.t lang) views1 views2
        (STEP: opt_step e e1 e2 views1 views2)
    :
      Thread.opt_step e e1 e2.
  Proof.
    inv STEP.
    - econs.
    - econs 2. eapply step_thread_step; eauto.
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
    forall (mem1 : Memory.t)
           (CAP: Memory.cap (Thread.memory e) mem1),
    exists e2 views2,
      (<<STEPS: rtc_tau (Thread.mk _ (Thread.state e) (Thread.local e) (Thread.sc e) mem1) e2
                        views1 views2>>) /\
      ((exists e e3, (<<STEP_FAILURE: Thread.step true e e2 e3 >>) /\
                     (<<EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure>>))
       \/
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
      + eauto.
    - right. esplits.
      + eapply tau_steps_thread_tau_steps; eauto.
      + eauto.
  Qed.

  Lemma step_future lang pf e th0 th1 views0 views1
        (STEP: @step lang pf e th0 th1 views0 views1)
        (WF: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (MEM: Memory.closed (Thread.memory th0))
        (REL: joined_released views0 (Local.promises (Thread.local th0)) (Local.tview (Thread.local th0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0))
        (VIEWS: wf_views views0)
    :
      (<<WF: Local.wf (Thread.local th1) (Thread.memory th1)>>) /\
      (<<SC: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1)>>) /\
      (<<MEM: Memory.closed (Thread.memory th1)>>)/\
      (<<REL: joined_released views1 (Local.promises (Thread.local th1)) (Local.tview (Thread.local th1)).(TView.rel)>>)/\
      (<<JOINED: joined_memory views1 (Thread.memory th1)>>) /\
      (<<VIEWS: wf_views views1>>) /\
      (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th0)) (Local.tview (Thread.local th1))>>) /\
      (<<SC_FUTURE: TimeMap.le (Thread.sc th0) (Thread.sc th1)>>) /\
      (<<MEM_FUTURE: Memory.future (Thread.memory th0) (Thread.memory th1)>>) /\
      (<<VIEWS_FUTURE: views_le views0 views1>>)
  .
  Proof.
    inv STEP. exploit Thread.step_future; eauto. i. des. splits; auto.
    ii. apply NNPP. ii. exploit VIEWSLE; eauto. i. des. ss.
  Qed.

  Lemma opt_step_future lang e th0 th1 views0 views1
        (STEP: @opt_step lang e th0 th1 views0 views1)
        (WF: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (MEM: Memory.closed (Thread.memory th0))
        (REL: joined_released views0 (Local.promises (Thread.local th0)) (Local.tview (Thread.local th0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0))
        (VIEWS: wf_views views0)
    :
      (<<WF: Local.wf (Thread.local th1) (Thread.memory th1)>>) /\
      (<<SC: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1)>>) /\
      (<<MEM: Memory.closed (Thread.memory th1)>>)/\
      (<<REL: joined_released views1 (Local.promises (Thread.local th1)) (Local.tview (Thread.local th1)).(TView.rel)>>)/\
      (<<JOINED: joined_memory views1 (Thread.memory th1)>>) /\
      (<<VIEWS: wf_views views1>>) /\
      (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th0)) (Local.tview (Thread.local th1))>>) /\
      (<<SC_FUTURE: TimeMap.le (Thread.sc th0) (Thread.sc th1)>>) /\
      (<<MEM_FUTURE: Memory.future (Thread.memory th0) (Thread.memory th1)>>) /\
      (<<VIEWS_FUTURE: views_le views0 views1>>)
  .
  Proof.
    inv STEP.
    - esplits; eauto; try by refl.
    - eapply step_future; eauto.
  Qed.

  Lemma tau_steps_future lang th0 th1 views0 views1
        (STEPS: @rtc_tau lang th0 th1 views0 views1)
        (WF: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (MEM: Memory.closed (Thread.memory th0))
        (REL: joined_released views0 (Local.promises (Thread.local th0)) (Local.tview (Thread.local th0)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0))
        (VIEWS: wf_views views0)
    :
      (<<WF: Local.wf (Thread.local th1) (Thread.memory th1)>>) /\
      (<<SC: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1)>>) /\
      (<<MEM: Memory.closed (Thread.memory th1)>>)/\
      (<<REL: joined_released views1 (Local.promises (Thread.local th1)) (Local.tview (Thread.local th1)).(TView.rel)>>)/\
      (<<JOINED: joined_memory views1 (Thread.memory th1)>>) /\
      (<<VIEWS: wf_views views1>>) /\
      (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th0)) (Local.tview (Thread.local th1))>>) /\
      (<<SC_FUTURE: TimeMap.le (Thread.sc th0) (Thread.sc th1)>>) /\
      (<<MEM_FUTURE: Memory.future (Thread.memory th0) (Thread.memory th1)>>) /\
      (<<VIEWS_FUTURE: views_le views0 views1>>)
  .
  Proof.
    ginduction STEPS; i.
    - splits; eauto; try by refl.
    - exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto; try by (etrans; eauto).
  Qed.

  Inductive reserve_step (views: Loc.t -> Time.t -> list View.t)
            lang (e1 e2:Thread.t lang): Prop :=
  | reserve_step_intro
      pf loc from to
      (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) e1 e2 views views)
    :
      reserve_step views e1 e2
  .
  Hint Constructors reserve_step.

  Inductive cancel_step (views: Loc.t -> Time.t -> list View.t)
            lang (e1 e2:Thread.t lang): Prop :=
  | cancel_step_intro
      pf loc from to
      (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) e1 e2 views views)
    :
      cancel_step views e1 e2
  .
  Hint Constructors cancel_step.

  Lemma rtc_reserve_step_rtc_tau lang th0 th1 views
        (STEPS: rtc (@reserve_step views lang) th0 th1)
    :
      rtc_tau th0 th1 views views.
  Proof.
    ginduction STEPS; eauto. inv H. econs 2; eauto.
  Qed.

  Lemma rtc_cancel_step_rtc_tau lang th0 th1 views
        (STEPS: rtc (@cancel_step views lang) th0 th1)
    :
      rtc_tau th0 th1 views views.
  Proof.
    ginduction STEPS; eauto. inv H. econs 2; eauto.
  Qed.

  Lemma rtc_reserve_step_future lang th0 th1 views
        (STEPS: rtc (@reserve_step views lang) th0 th1)
        (WF: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (MEM: Memory.closed (Thread.memory th0))
        (REL: joined_released views (Local.promises (Thread.local th0)) (Local.tview (Thread.local th0)).(TView.rel))
        (JOINED: joined_memory views (Thread.memory th0))
        (VIEWS: wf_views views)
    :
      (<<WF: Local.wf (Thread.local th1) (Thread.memory th1)>>) /\
      (<<SC: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1)>>) /\
      (<<MEM: Memory.closed (Thread.memory th1)>>)/\
      (<<REL: joined_released views (Local.promises (Thread.local th1)) (Local.tview (Thread.local th1)).(TView.rel)>>)/\
      (<<JOINED: joined_memory views (Thread.memory th1)>>) /\
      (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th0)) (Local.tview (Thread.local th1))>>) /\
      (<<SC_FUTURE: TimeMap.le (Thread.sc th0) (Thread.sc th1)>>) /\
      (<<MEM_FUTURE: Memory.future (Thread.memory th0) (Thread.memory th1)>>)
  .
  Proof.
    ginduction STEPS; i.
    - splits; eauto; try by refl.
    - inv H. exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto; try by (etrans; eauto).
  Qed.

  Lemma rtc_cancel_step_future lang th0 th1 views
        (STEPS: rtc (@cancel_step views lang) th0 th1)
        (WF: Local.wf (Thread.local th0) (Thread.memory th0))
        (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        (MEM: Memory.closed (Thread.memory th0))
        (REL: joined_released views (Local.promises (Thread.local th0)) (Local.tview (Thread.local th0)).(TView.rel))
        (JOINED: joined_memory views (Thread.memory th0))
        (VIEWS: wf_views views)
    :
      (<<WF: Local.wf (Thread.local th1) (Thread.memory th1)>>) /\
      (<<SC: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1)>>) /\
      (<<MEM: Memory.closed (Thread.memory th1)>>)/\
      (<<REL: joined_released views (Local.promises (Thread.local th1)) (Local.tview (Thread.local th1)).(TView.rel)>>)/\
      (<<JOINED: joined_memory views (Thread.memory th1)>>) /\
      (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th0)) (Local.tview (Thread.local th1))>>) /\
      (<<SC_FUTURE: TimeMap.le (Thread.sc th0) (Thread.sc th1)>>) /\
      (<<MEM_FUTURE: Memory.future (Thread.memory th0) (Thread.memory th1)>>)
  .
  Proof.
    ginduction STEPS; i.
    - splits; eauto; try by refl.
    - inv H. exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto; try by (etrans; eauto).
  Qed.

End JThread.

Module JConfiguration.

  Inductive step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t)
                         (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | step_intro
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      views1 views2 views3
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: JThread.rtc_tau (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2 views1 views2)
      (STEP: JThread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3) views2 views3)
      (CONSISTENT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          JThread.consistent (Thread.mk _ st3 lc3 sc3 memory3) views3)
    :
      step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3) views1 views3
  .
  Hint Constructors step.

  Inductive opt_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t)
                             (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | opt_step_some
      e tid c1 c2 views1 views2
      (STEP: step e tid c1 c2 views1 views2)
    :
      opt_step e tid c1 c2 views1 views2
  | opt_step_none
      tid c views:
      opt_step MachineEvent.silent tid c c views views
  .
  Hint Constructors opt_step.

  Inductive steps: forall (c1 c2: Configuration.t) (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | steps_refl
      c views:
      steps c c views views
  | steps_step
      e tid c1 c2 c3 views1 views2 views3
      (STEP: step e tid c1 c2 views1 views2)
      (STEPS: steps c2 c3 views2 views3):
      steps c1 c3 views1 views3
  .
  Hint Constructors steps.

  Lemma step_configuration_step e tid c1 c2 views1 views2
        (STEP: step e tid c1 c2 views1 views2)
    :
      Configuration.step e tid c1 c2.
  Proof.
    inv STEP. destruct (classic (e0 = ThreadEvent.failure)).
    - subst. econs; try eassumption.
      + eapply JThread.tau_steps_thread_tau_steps; eauto.
      + eapply JThread.step_thread_step; eauto.
      + ss.
    - econs; try eassumption.
      + eapply JThread.tau_steps_thread_tau_steps; eauto.
      + eapply JThread.step_thread_step; eauto.
      + i. eapply JThread.consistent_thread_consistent; eauto.
  Qed.

  Inductive wf (views: Loc.t -> Time.t -> list View.t)
            (conf:Configuration.t): Prop :=
  | wf_intro
      (WF: Configuration.wf conf)
      (REL: forall tid lang st lc
                   (TH: IdentMap.find tid (Configuration.threads conf) = Some (existT _ lang st, lc)),
          joined_released views (Local.promises lc) (TView.rel (Local.tview lc)))
      (JOINMEM: joined_memory views (Configuration.memory conf))
      (VIEWS: wf_views views)
  .

  Definition init_views: Loc.t -> Time.t -> list View.t :=
    fun _ ts => if (Time.eq_dec Time.bot ts) then [View.bot] else [].

  Lemma init_wf syn: wf init_views (Configuration.init syn).
  Proof.
    econs.
    - eapply Configuration.init_wf.
    - i. ss. unfold Threads.init in TH.
      erewrite IdentMap.Facts.map_o in TH.
      unfold option_map in TH. des_ifs. ss.
      ii. erewrite Memory.bot_get in GET. clarify.
    - ss. econs.
      + ii. splits; auto.
        * unfold Memory.init in *. setoid_rewrite Cell.init_get in GET. des_ifs.
        * i. unfold init_views in *. des_ifs. ss. des; auto.
          subst. unfold Memory.init in *. setoid_rewrite Cell.init_get in GET. des_ifs.
      + i. unfold init_views in *. des_ifs.
        hexploit Memory.init_closed. intros []. eauto.
      + ii. unfold init_views. des_ifs. econs; eauto.
        hexploit TView.bot_closed. intros []. auto.
    - ii. unfold init_views. des_ifs. econs; eauto. eapply View.bot_wf.
  Qed.

  Lemma step_future
        e tid c1 c2 views1 views2
        (STEP: step e tid c1 c2 views1 views2)
        (WF1: wf views1 c1)
    :
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>)
  .
  Proof.
    inv WF1.
    dup STEP. exploit Configuration.step_future; eauto.
    { eapply step_configuration_step; eauto. }
    i. des.
    inv STEP0. inv WF. ss.
    hexploit JThread.tau_steps_future; try apply STEPS; ss; eauto.
    { inv WF0. eapply THREADS in TID. ss. }
    i. des.
    hexploit JThread.step_future; eauto. ss. i. des. splits; auto.
    - econs; eauto. i. ss. erewrite IdentMap.gsspec in TH. des_ifs.
      hexploit REL; eauto. i.
      eapply joined_released_le; eauto. etrans; eauto.
    - etrans; eauto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2 views1 views2
        (STEP: opt_step e tid c1 c2 views1 views2)
        (WF1: wf views1 c1)
    :
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>)
  .
  Proof.
    inv STEP.
    { eapply step_future; eauto. }
    { esplits; eauto; try refl. }
  Qed.

  Lemma steps_future
        c1 c2 views1 views2
        (STEPS: steps c1 c2 views1 views2)
        (WF1: wf views1 c1):
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>).
  Proof.
    revert WF1. induction STEPS; i.
    - splits; ss; refl.
    - exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; ss; etrans; eauto.
  Qed.

  Inductive single_step:
    forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t)
           (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | single_step_intro
      e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4 views1 views2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@JThread.cancel_step views1 lang) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: JThread.opt_step e e2 e3 views1 views2)
      (RESERVES: rtc (@JThread.reserve_step views2 _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          JThread.consistent (Thread.mk _ st4 lc4 sc4 memory4) views2):
      single_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4) views1 views2
  .
  Hint Constructors single_step.

  Inductive machine_single_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t)
                                 (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | machine_single_step_intro
      e tid c1 c2 views1 views2
      (STEP: single_step e tid c1 c2 views1 views2)
    :
      machine_single_step (ThreadEvent.get_machine_event e) tid c1 c2 views1 views2
  .
  Hint Constructors machine_single_step.

  Lemma single_step_configuration_step e tid c1 c2 views1 views2
        (STEP: single_step e tid c1 c2 views1 views2)
    :
      SConfiguration.step e tid c1 c2.
  Proof.
    inv STEP. econs.
    - eauto.
    - eapply rtc_implies; try apply CANCELS.
      clear. i. inv H. econs. eapply JThread.step_thread_step; eauto.
    - eapply JThread.opt_step_thread_opt_step; eauto.
    - eapply rtc_implies; try apply RESERVES.
      clear. i. inv H. econs. eapply JThread.step_thread_step; eauto.
    - i. eapply JThread.consistent_thread_consistent; eauto.
  Qed.

  Lemma single_step_future
        e tid c1 c2 views1 views2
        (STEP: single_step e tid c1 c2 views1 views2)
        (WF1: wf views1 c1)
    :
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>)
  .
  Proof.
    inv WF1.
    dup STEP. exploit SConfiguration.step_future; eauto.
    { eapply single_step_configuration_step; eauto. }
    i. des.
    inv STEP0. inv WF. ss.
    hexploit JThread.rtc_cancel_step_future; try apply CANCELS; ss; eauto.
    { inv WF0. eapply THREADS in TID. ss. }
    i. des.
    hexploit JThread.opt_step_future; eauto. i. des.
    hexploit JThread.rtc_reserve_step_future; try apply RESERVES; ss; eauto. i. des.
    splits; auto.
    econs; eauto. i. ss. erewrite IdentMap.gsspec in TH. des_ifs.
    hexploit REL; eauto. i.
    eapply joined_released_le; eauto.
  Qed.

  Lemma machine_single_step_future
        e tid c1 c2 views1 views2
        (STEP: machine_single_step e tid c1 c2 views1 views2)
        (WF1: wf views1 c1)
    :
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>)
  .
  Proof.
    inv STEP. eapply single_step_future; eauto.
  Qed.

  Inductive single_steps: forall (c1 c2: Configuration.t) (views1 views2: Loc.t -> Time.t -> list View.t), Prop :=
  | single_steps_refl
      c views:
      single_steps c c views views
  | single_steps_step
      e tid c1 c2 c3 views1 views2 views3
      (STEP: single_step e tid c1 c2 views1 views2)
      (STEPS: single_steps c2 c3 views2 views3):
      single_steps c1 c3 views1 views3
  .
  Hint Constructors single_steps.

  Lemma single_steps_future
        c1 c2 views1 views2
        (STEPS: single_steps c1 c2 views1 views2)
        (WF1: wf views1 c1):
      (<<WF2: wf views2 c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
      (<<VIEWS_FUTURE: views_le views1 views2>>).
  Proof.
    revert WF1. induction STEPS; i.
    - splits; ss; refl.
    - exploit single_step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; ss; etrans; eauto.
  Qed.
End JConfiguration.



Module JSim.

  Inductive sim_op_kind: forall (kind_src kind_tgt: Memory.op_kind), Prop :=
  | sim_op_kind_add
    :
      sim_op_kind Memory.op_kind_add Memory.op_kind_add
  | sim_op_kind_split
      ts msg_src msg_tgt
      (MSG: Message.le msg_src msg_tgt)
    :
      sim_op_kind (Memory.op_kind_split ts msg_src) (Memory.op_kind_split ts msg_tgt)
  | sim_op_kind_lower
      msg_src msg_tgt
      (MSG: Message.le msg_src msg_tgt)
      (OPT: forall val, msg_src = Message.concrete val None <-> msg_tgt = Message.concrete val None)
    :
      sim_op_kind (Memory.op_kind_lower msg_src) (Memory.op_kind_lower msg_tgt)
  | sim_op_kind_cancel
    :
      sim_op_kind Memory.op_kind_cancel Memory.op_kind_cancel
  .
  Hint Constructors sim_op_kind.

  Global Program Instance sim_op_kind_PreOrder: PreOrder sim_op_kind.
  Next Obligation. ii. destruct x; econs; eauto; refl. Qed.
  Next Obligation. ii. inv H; inv H0; econs; eauto; etrans; eauto. Qed.

  Inductive sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
  | sim_event_promise
      loc from to msg_src msg_tgt kind_src kind_tgt
      (MSG: Message.le msg_src msg_tgt)
      (KIND: sim_op_kind kind_src kind_tgt)
    :
      sim_event
        (ThreadEvent.promise loc from to msg_src kind_src)
        (ThreadEvent.promise loc from to msg_tgt kind_tgt)
  | sim_event_silent
    :
      sim_event
        ThreadEvent.silent
        ThreadEvent.silent
  | sim_event_read
      loc ts val released_src released_tgt ord
      (RELEASED: View.opt_le released_src released_tgt)
    :
      sim_event
        (ThreadEvent.read loc ts val released_src ord)
        (ThreadEvent.read loc ts val released_tgt ord)
  | sim_event_write
      loc from to val released_src released_tgt ord
      (RELEASED: View.opt_le released_src released_tgt)
      (OPT: released_src = None <-> released_tgt = None)
    :
      sim_event
        (ThreadEvent.write loc from to val released_src ord)
        (ThreadEvent.write loc from to val released_tgt ord)
  | sim_event_write_na
      loc msgs from to val ord
    :
      sim_event
        (ThreadEvent.write_na loc msgs from to val ord)
        (ThreadEvent.write_na loc msgs from to val ord)
  | sim_event_update
      loc tsr tsw valr valw releasedr_src releasedr_tgt releasedw_src releasedw_tgt ordr ordw
      (RELEASEDR: View.opt_le releasedr_src releasedr_tgt)
      (RELEASEDW: View.opt_le releasedw_src releasedw_tgt)
      (OPT: releasedw_src = None <-> releasedw_tgt = None)
    :
      sim_event
        (ThreadEvent.update loc tsr tsw valr valw releasedr_src releasedw_src ordr ordw)
        (ThreadEvent.update loc tsr tsw valr valw releasedr_tgt releasedw_tgt ordr ordw)
  | sim_event_fence
      ordr ordw
    :
      sim_event
        (ThreadEvent.fence ordr ordw)
        (ThreadEvent.fence ordr ordw)
  | sim_event_syscall
      e
    :
      sim_event
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | sim_event_failure
    :
      sim_event
        ThreadEvent.failure
        ThreadEvent.failure
  | sim_event_racy_read
      loc to val ord
    :
      sim_event
        (ThreadEvent.racy_read loc to val ord)
        (ThreadEvent.racy_read loc to val ord)
  | sim_event_racy_write
      loc to val ord
    :
      sim_event
        (ThreadEvent.racy_write loc to val ord)
        (ThreadEvent.racy_write loc to val ord)
  | sim_event_racy_update
      loc to valr valw ordr ordw
    :
      sim_event
        (ThreadEvent.racy_update loc to valr valw ordr ordw)
        (ThreadEvent.racy_update loc to valr valw ordr ordw)
  .
  Hint Constructors sim_event.

  Global Program Instance sim_event_PreOrder: PreOrder sim_event.
  Next Obligation. ii. destruct x; try (econs; eauto); refl. Qed.
  Next Obligation. ii. inv H; inv H0; econs; eauto; etrans; eauto. Qed.

  Lemma sim_event_program_event e_src e_tgt
        (EVENT: sim_event e_src e_tgt)
    :
      ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
  Proof.
    inv EVENT; ss.
  Qed.

  Lemma sim_event_machine_event e_src e_tgt
        (EVENT: sim_event e_src e_tgt)
    :
      ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.
  Proof.
    inv EVENT; ss.
  Qed.

  Inductive joined_promise_content
            (views: list View.t)
            (loc: Loc.t) (ts: Time.t)
  : forall (msg_src msg_tgt: option (Time.t * Message.t)), Prop :=
  | joined_promise_content_concrete
      from val released_src released_tgt
      (RELEASED: max_le_joined_opt_view views released_tgt released_src)
      (NIL: (released_src = None /\ released_tgt = None) \/ views <> [])
    :
      joined_promise_content
        views loc ts
        (Some (from, Message.concrete val released_src))
        (Some (from, Message.concrete val released_tgt))
  | joined_promise_content_reserve
      from
    :
      joined_promise_content
        views loc ts
        (Some (from, Message.reserve))
        (Some (from, Message.reserve))
  | joined_promise_content_undef
      from
    :
      joined_promise_content
        views loc ts
        (Some (from, Message.undef))
        (Some (from, Message.undef))
  | joined_promise_content_none
    :
      joined_promise_content
        views loc ts
        None
        None
  .
  Hint Constructors joined_promise_content.

  Definition sim_joined_promises (views: Loc.t -> Time.t -> list View.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      joined_promise_content (views loc ts) loc ts (Memory.get loc ts prom_src) (Memory.get loc ts prom_tgt).

  Lemma sim_joined_promises_le
        prom_src prom_tgt views0 views1
        (PROM: sim_joined_promises views0 prom_src prom_tgt)
        (VIEWSLE: views_le views0 views1)
    :
      sim_joined_promises views1 prom_src prom_tgt.
  Proof.
    ii. specialize (PROM loc ts). inv PROM; eauto. des.
    { clarify. econs; eauto. econs. }
    { exploit VIEWSLE; eauto. i. rewrite x. auto. }
  Qed.

  Inductive sim_local (views: Loc.t -> Time.t -> list View.t):
    forall (lc_src lc_tgt: Local.t), Prop :=
  | sim_local_intro
      vw_src vw_tgt prom_src prom_tgt
      (TVIEW: TView.le vw_src vw_tgt)
      (PROMISES: sim_joined_promises views prom_src prom_tgt)
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
    eapply sim_joined_promises_le; eauto.
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

  Inductive sim_thread (views: Loc.t -> Time.t -> list View.t):
    forall lang0 lang1 (th0: Thread.t lang0) (th1: Thread.t lang1), Prop :=
  | sim_thread_intro
      lang st lc_src lc_tgt
      mem_src mem_tgt sc_src sc_tgt
      (LOCAL: sim_local views lc_src lc_tgt)
      (MEM: sim_memory mem_src mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_thread
        views
        (Thread.mk lang st lc_src sc_src mem_src)
        (Thread.mk lang st lc_tgt sc_tgt mem_tgt)
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
        (JOINMEM: joined_memory views mem1_src)
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (ORD: Ordering.le ord_src ord_tgt)
    :
      exists released_src lc2_src,
        (<<REL: View.opt_le released_src released_tgt>>) /\
        (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
        (<<LOCAL2: sim_local views lc2_src lc2_tgt>>) /\
        (<<REL: joined_released views (Local.promises lc2_src) (TView.rel (Local.tview lc2_src))>>) /\
        (<<JOINED: joined_opt_view (views loc ts) released_src>>)
  .
  Proof.
    inv LOCAL1. inv STEP_TGT.
    exploit sim_memory_get; try apply GET; eauto. i. des.
    inv MSG. esplits.
    - eauto.
    - econs; eauto.
      { etrans; eauto. }
      eapply TViewFacts.readable_mon; eauto. apply TVIEW.
    - econs; eauto. s. apply TViewFacts.read_tview_mon; auto.
      + apply WF1_TGT.
      + inv MEM1_TGT. exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
    - eauto.
    - destruct released; econs. inv JOINMEM.
      exploit COMPLETE; eauto. i. des. auto.
  Qed.

  Lemma sim_local_is_racy
        views
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        loc to ord_src ord_tgt
        (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc to ord_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (JOINMEM: joined_memory views mem1_src)
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (ORD: Ordering.le ord_src ord_tgt)
    :
      Local.is_racy lc1_src mem1_src loc to ord_src
  .
  Proof.
    inv LOCAL1. inv STEP_TGT.
    exploit sim_memory_get; try apply GET; eauto. i. des. econs; eauto.
    { specialize (PROMISES loc to). ss. rewrite GETP in *. inv PROMISES; auto. }
    { eapply TViewFacts.racy_view_mon; eauto.
      ss. eapply TVIEW. }
    { inv MSG; ss. }
    { i. hexploit MSG2; eauto. i. subst. inv MSG; ss. }
  Qed.

  Lemma sim_local_racy_read
        views
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        loc to val ord_src ord_tgt
        (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc to val ord_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (JOINMEM: joined_memory views mem1_src)
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (ORD: Ordering.le ord_src ord_tgt)
    :
      Local.racy_read_step lc1_src mem1_src loc to val ord_src
  .
  Proof.
    inv LOCAL1. inv STEP_TGT. econs; eauto. eapply sim_local_is_racy; eauto.
  Qed.

  Lemma sim_local_nonsynch_loc
        views loc lc_src lc_tgt
        (SIM: sim_local views lc_src lc_tgt)
        (NONSYNCH: Memory.nonsynch_loc loc (Local.promises lc_tgt)):
    Memory.nonsynch_loc loc (Local.promises lc_src).
  Proof.
    inv SIM. ii. destruct msg; ss.
    specialize (PROMISES loc t). rewrite GET in *. inv PROMISES.
    exploit NONSYNCH; eauto. ss. i. subst. inv RELEASED. ss.
  Qed.

  Lemma sim_local_nonsynch
        views lc_src lc_tgt
        (SIM: sim_local views lc_src lc_tgt)
        (NONSYNCH: Memory.nonsynch (Local.promises lc_tgt)):
    Memory.nonsynch (Local.promises lc_src).
  Proof.
    ii. eapply sim_local_nonsynch_loc; eauto.
  Qed.

  Lemma sim_local_memory_bot views lc_src lc_tgt
        (SIM: sim_local views lc_src lc_tgt)
        (BOT: Local.promises lc_tgt = Memory.bot)
    :
      Local.promises lc_src = Memory.bot.
  Proof.
    inv SIM. ss. eapply Memory.ext. i.
    specialize (PROMISES loc ts). inv PROMISES; eauto.
    erewrite Memory.bot_get in H. clarify.
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
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (ORDR: Ordering.le ordr_src ordr_tgt)
        (ORDW: Ordering.le ordw_src ordw_tgt):
    exists lc2_src sc2_src,
      (<<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>>) /\
      (<<LOCAL2: sim_local views lc2_src lc2_tgt>>) /\
      (<<SC2: TimeMap.le sc2_src sc2_tgt>>) /\
      (<<REL: joined_released views (Local.promises lc2_src) (TView.rel (Local.tview lc2_src))>>).
  Proof.
    inv STEP_TGT. esplits.
    - econs; eauto.
      + i. eapply sim_local_nonsynch; eauto.
      + i. subst. destruct ordw_tgt; ss.
        specialize (PROMISES eq_refl).
        eapply sim_local_memory_bot; eauto.
    - inv LOCAL1. inv WF1_SRC. inv WF1_TGT. econs.
      + eapply TViewFacts.write_fence_tview_mon; eauto.
        * eapply TViewFacts.read_fence_tview_mon; eauto.
        * eapply TViewFacts.read_fence_future; eauto.
      + ss.
    - inv LOCAL1. inv WF1_SRC. inv WF1_TGT.
      apply TViewFacts.write_fence_sc_mon; auto; try refl.
      apply TViewFacts.read_fence_tview_mon; auto; try refl.
    - ss. ii. exploit REL; eauto. i.
      inv LOCAL1. specialize (PROMISES0 loc ts). ss.
      rewrite GET in *. inv PROMISES0. inv RELEASED.
      condtac; auto. condtac; auto.
      * exploit RELEASE; eauto; ss. destruct ordw_src, ordw_tgt; ss.
      * exploit RELEASE; eauto; ss. destruct ordw_src, ordw_tgt; ss.
  Qed.

  Lemma sim_local_promise_consistent
        views
        lc_src lc_tgt
        (LOCAL: sim_local views lc_src lc_tgt)
        (CONS_TGT: Local.promise_consistent lc_tgt):
    (<<CONS_SRC: Local.promise_consistent lc_src>>).
  Proof.
    inv LOCAL. ii. ss.
    specialize (PROMISES loc ts). rewrite PROMISE in *. inv PROMISES; ss.
    { exploit CONS_TGT; eauto; ss.
      eapply TimeFacts.le_lt_lt; eauto.
      inv TVIEW. inv CUR. eauto. }
    { exploit CONS_TGT; eauto; ss.
      eapply TimeFacts.le_lt_lt; eauto.
      inv TVIEW. inv CUR. eauto. }
  Qed.

  Lemma sim_local_racy_write
        views
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        loc to ord_src ord_tgt
        (STEP_TGT: Local.racy_write_step lc1_tgt mem1_tgt loc to ord_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (JOINMEM: joined_memory views mem1_src)
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (ORD: Ordering.le ord_src ord_tgt)
    :
      Local.racy_write_step lc1_src mem1_src loc to ord_src
  .
  Proof.
    inv LOCAL1. inv STEP_TGT. econs; eauto.
    { eapply sim_local_is_racy; eauto. }
    { eapply sim_local_promise_consistent; eauto. }
  Qed.

  Lemma sim_local_racy_update
        views
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        loc to ordr_src ordw_src ordr_tgt ordw_tgt
        (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc to ordr_tgt ordw_tgt)
        (LOCAL1: sim_local views lc1_src lc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (JOINMEM: joined_memory views mem1_src)
        (REL: joined_released views (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (ORDR: Ordering.le ordr_src ordr_tgt)
        (ORDW: Ordering.le ordw_src ordw_tgt)
    :
      Local.racy_update_step lc1_src mem1_src loc to ordr_src ordw_src
  .
  Proof.
    inv LOCAL1. inv STEP_TGT.
    { econs 1; auto.
      { etrans; eauto. }
      { eapply sim_local_promise_consistent; eauto. }
    }
    { econs 2; auto.
      { etrans; eauto. }
      { eapply sim_local_promise_consistent; eauto. }
    }
    { econs 3; eauto.
      { eapply sim_local_is_racy; eauto. }
      { eapply sim_local_promise_consistent; eauto. }
    }
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

  Lemma message_le_to msg_src msg_tgt loc to
        (MSGTO: Memory.message_to msg_tgt loc to)
        (MSG: Message.le msg_src msg_tgt)
    :
      Memory.message_to msg_src loc to.
  Proof.
    inv MSGTO; inv MSG; econs. etrans; eauto.
    eapply View.unwrap_opt_le in RELEASED. inv RELEASED. auto.
  Qed.

  Let unwrap_views (vw: option View.t) (views: list View.t): list View.t :=
    match vw with
    | Some _ => views
    | _ => []
    end.

  Lemma max_le_joined_opt_view_joined2
        views view max
        (MAXLE: max_le_joined_opt_view views view max)
    :
      joined_opt_view (unwrap_views view views) max.
  Proof.
    inv MAXLE; econs. eapply max_le_joined_view_joined; eauto.
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
        (CONS_TGT: Local.promise_consistent lc2_tgt)

        (REL1: joined_released views1 (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))

    :
      exists msg_src views2 kind_src lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
        (<<LOCAL2: sim_local views2 lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views2 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views2>>) /\
        (<<REL2: joined_released views2 (Local.promises lc2_src) (TView.rel (Local.tview lc2_src))>>) /\

        (<<PROMISE:
           forall val released
                  (CONCRETE: msg_src = Message.concrete val released),
             (<<JOINED: joined_opt_view (views2 loc to) released>>)>>) /\
        (<<VIEWSLE: forall loc ts (NEQ: views2 loc ts <> views1 loc ts),
            (<<NIL: views1 loc ts = []>>) /\
            exists from val released,
              (<<GET: Memory.get loc ts mem2_src = Some (from, Message.concrete val (Some released))>>) /\
              (<<NONE: Memory.get loc ts mem1_src = None>>) /\
              (<<VIEW: views2 loc ts = (View.join ((TView.rel (Local.tview lc2_src)) loc) (View.singleton_ur loc ts))
                                         ::(all_join_views (View.singleton_ur loc ts) (views1 loc from))>>)>>) /\
        (<<MSG: Message.le msg_src msg_tgt>>) /\
        (<<KIND: sim_op_kind kind_src kind_tgt>>) /\
        (<<RESERVE: msg_tgt = Message.reserve -> msg_src = Message.reserve /\ views1 = views2>>) /\
        (<<UNDEF: msg_tgt = Message.undef -> msg_src = Message.undef /\ views1 = views2>>)
  .
  Proof.
    inv STEP_TGT. inv PROMISE.
    { hexploit add_succeed_wf; try apply MEM; eauto. i. des.

      assert (NOATTACH: forall (NORESERVE: msg_tgt <> Message.reserve) ts msg
                               (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
      { i. exploit sim_memory_get_inv; try exact GET; eauto.
        { apply MEM1_SRC. }
        { apply MEM1_TGT. }
        i. des. inv FROM; cycle 1.
        { inv H. eapply ATTACH; eauto. }
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.get_ts; try exact GET1. i. des.
        { subst. inv H. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. inv TO; inv H0.
          exploit Memory.get_ts; try exact GET. i. des; timetac. inv x2. }
        exploit Memory.get_disjoint; [exact GET1|exact x0|..]. i. des.
        { subst. congr. }
        apply (x3 to); econs; ss; try refl.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. eauto. }
        { etrans; eauto. econs. ss. }
      }

      destruct msg_tgt as [val released_tgt| |].

      (* add concrete message *)
      {
        set (views := (View.join ((TView.rel (Local.tview lc1_src)) loc) (View.singleton_ur loc to))
                        ::(all_join_views (View.singleton_ur loc to) (views1 loc from))).
        assert (VIEWWF: View.wf (View.join (TView.rel (Local.tview lc1_src) loc) (View.singleton_ur loc to))).
        { inv WF1_SRC. inv TVIEW_WF.
          eapply View.join_wf; eauto. eapply View.singleton_ur_wf. }
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs; eauto.
          eapply all_join_views_wf; eauto. eapply View.singleton_ur_wf. }
        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then unwrap_views released_tgt views
                                  else views1 l t).
        hexploit (@max_le_joined_opt_view_exists views released_tgt); auto. i. des.

        hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val max)); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le (Local.promises lc1_src) mem1_src loc from to (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists (Message.concrete val max), views2.

        assert (SINGLETONCLOSED: Memory.closed_view (View.singleton_ur loc to) mem2_src).
        { eapply Memory.singleton_ur_closed_view.
          - eapply Memory.add_get0; eauto.
          - inv MEM1_SRC. eapply Memory.add_inhabited; eauto. }

        assert (MSGCLOSED: Memory.closed_view (View.join (TView.rel (Local.tview lc1_src) loc) (View.singleton_ur loc to))
                                              mem2_src).
        { inv WF1_SRC. inv TVIEW_CLOSED.
          eapply Memory.join_closed_view; eauto.
          eapply Memory.add_closed_view; eauto. }

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits; auto.
              * inv MAX. eapply max_le_joined_view_joined; eauto.
              * i. inv MAX. ss. right. eapply all_join_views_in; eauto.
            + ss. des; clarify. exfalso. eapply NOATTACH; eauto. ss.
            + eapply COMPLETE; eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
            + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
          - unfold views2. ii. des_ifs.
            + ss. des; clarify. destruct released_tgt; ss.
              unfold views. econs; auto.
              eapply all_join_views_closed; eauto.
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
        }

        esplits.
        { econs.
          - econs; eauto.
            { eapply message_le_to; eauto.
              eapply max_le_joined_message_le. econs; eauto. }
            { i. eapply NOATTACH; eauto. ss. }
          - eapply joined_memory_get_closed; eauto.
            + eapply Memory.add_get0; eauto.
            + inv MEM1_SRC. eapply Memory.add_inhabited; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. unfold views2.
            erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto.
            { inv MAX; econs. eauto. }
            { inv MAX; eauto. right. ss. }
        }
        { eapply sim_memory_add; cycle 1; eauto. econs; [refl|].
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. destruct released_tgt; ss. }
        { ss. ii. unfold views2.
          erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
          ss. des; clarify. inv MAX; ss; auto. }
        { i. unfold views2. des_ifs; ss; des; clarify.
          eapply max_le_joined_opt_view_joined2; eauto. }
        { unfold views2. i. des_ifs. ss. des; subst.
          assert (NIL: [] = views1 loc to).
          { inv JOINMEM1. apply NNPP. ii. exploit ONLY; eauto. i. des.
            eapply Memory.add_get0 in MEM_SRC. des. clarify. }
          split; auto.
          inv MAX; ss.
          unfold views. esplits; eauto.
          { eapply Memory.add_get0; eauto. }
          { eapply Memory.add_get0; eauto. }
        }
        { econs; eauto; [refl|]. eapply max_le_joined_opt_view_le; eauto. }
        { eauto. }
        { ss. }
        { ss. }
      }

      (* add undef *)
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.undef); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le (Local.promises lc1_src) mem1_src loc from to Message.undef); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.undef, views1.

        esplits.
        { econs.
          - econs; eauto.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
        }
        { eapply sim_memory_add; cycle 1; eauto. }
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. des_ifs.
            ss. guardH o. exploit COMPLETE; eauto.
          - ii. exploit ONLY; eauto. i. des.
            eapply Memory.add_get1 in GET; eauto.
          - i. eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.add_closed_view; eauto. }
        { auto. }
        { ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto. }
        { i. clarify. }
        { i. clarify. }
        { eauto. }
        { eauto. }
        { i. splits; auto. }
        { auto. }
      }

      (* add reserve *)
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.reserve); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le (Local.promises lc1_src) mem1_src loc from to Message.reserve); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.reserve, views1.

        esplits.
        { econs.
          - econs; eauto.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
        }
        { eapply sim_memory_add; cycle 1; eauto. }
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. des_ifs.
            ss. guardH o. exploit COMPLETE; eauto.
          - ii. exploit ONLY; eauto. i. des.
            eapply Memory.add_get1 in GET; eauto.
          - i. eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.add_closed_view; eauto. }
        { auto. }
        { ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto. }
        { i. clarify. }
        { i. clarify. }
        { eauto. }
        { eauto. }
        { i. splits; auto. }
        { ss. }
      }
    }

    (* split *)
    { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des. subst.
      assert (exists msg_src',
                 (<<GETSRC: Memory.get loc ts3 (Local.promises lc1_src) = Some (from, msg_src')>>) /\
                 (<<GETMEMSRC: Memory.get loc ts3 mem1_src = Some (from, msg_src')>>) /\
                 (<<SIMMSG: Message.le msg_src' msg3>>)).
      { inv LOCAL1. inv WF1_SRC. dup PROMISES0. ss.
        specialize (PROMISES2 loc ts3). erewrite GET2 in *. inv PROMISES2; ss.
        - esplits; eauto. inv WF1_TGT. exploit sim_memory_get; eauto.
          { i. clear NIL. des.
            symmetry in H0. apply PROMISES1 in H0. clarify. }
        - esplits; eauto.
      } des.

      destruct msg_tgt as [val'0 released'0| |]; ss.
      {
        set (views :=(View.join ((TView.rel (Local.tview lc1_src)) loc)
                                (View.singleton_ur loc to))
                       ::(all_join_views (View.singleton_ur loc to) (views1 loc from))).
        assert (VIEWWF: View.wf (View.join (TView.rel (Local.tview lc1_src) loc) (View.singleton_ur loc to))).
        { inv WF1_SRC. inv TVIEW_WF.
          eapply View.join_wf; eauto. eapply View.singleton_ur_wf. }
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs; eauto.
          eapply all_join_views_wf; eauto. eapply View.singleton_ur_wf. }

        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then unwrap_views released'0 views
                                  else views1 l t).
        hexploit (@max_le_joined_opt_view_exists views released'0); auto. i. des.

        hexploit (@Memory.split_exists (Local.promises lc1_src) loc from to ts3 (Message.concrete val'0 max) msg_src'); auto.
        intros [prom2_src PROMISES_SRC].
        hexploit (@Memory.split_exists_le (Local.promises lc1_src) mem1_src loc from to ts3 (Message.concrete val'0 max) msg_src'); eauto.
        { inv WF1_SRC. auto. }
        intros [mem2_src MEM_SRC].

        assert (SINGLETONCLOSED: Memory.closed_view (View.singleton_ur loc to) mem2_src).
        { eapply Memory.singleton_ur_closed_view.
          - eapply Memory.split_get0 in MEM_SRC. des. eauto.
          - inv MEM1_SRC. eapply Memory.split_inhabited; eauto. }

        assert (MSGCLOSED: Memory.closed_view (View.join (TView.rel (Local.tview lc1_src) loc) (View.singleton_ur loc to))
                                              mem2_src).
        { inv WF1_SRC. inv TVIEW_CLOSED.
          eapply Memory.join_closed_view; eauto.
          eapply Memory.split_closed_view; eauto. }

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.split_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits; auto.
              * inv MAX. eapply max_le_joined_view_joined; eauto.
              * i. inv MAX. ss. right. eapply all_join_views_in; eauto.
            + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
              ii; ss. destruct released'0; ss. des; auto.
              * subst. erewrite View.join_assoc. erewrite singleton_ur_join.
                unfold Time.join. des_ifs.
                { inv LOCAL1. ss. exploit REL1; eauto. }
                { exfalso. eapply Time.lt_strorder. etrans; eauto. }
              * eapply all_join_views_in_iff in IN. des. subst.
                erewrite View.join_assoc. erewrite singleton_ur_join.
                unfold Time.join. des_ifs; eauto.
                exfalso. eapply Time.lt_strorder. etrans; eauto.
            + ss. des; clarify. exfalso.
              hexploit Memory.get_disjoint.
              { eapply GETMEMSRC. }
              { eapply GET. } i. des; clarify. eapply H.
              * instantiate (1:=Time.meet ts ts3).
                unfold Time.meet. des_ifs; econs; ss.
                { eapply TimeFacts.lt_le_lt; eauto.
                  eapply memory_get_ts_le; eauto. }
                { transitivity to; eauto. }
                { refl. }
              * unfold Time.meet. des_ifs; econs; ss.
                { apply memory_get_ts_strong in GET. des; clarify. }
                { refl. }
                { left. auto. }
            + ss. des; clarify.
            + ss. eauto.
          - unfold views2. i. erewrite (@Memory.split_o mem2_src); eauto.
            des_ifs; eauto. guardH o. ss. des; clarify.
            hexploit (ONLY loc ts3); eauto. i. des; clarify.
            eapply Memory.split_get0 in MEM_SRC. des; clarify. eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. destruct released'0; ss.
              unfold views. econs; auto.
              eapply all_join_views_closed; eauto.
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.split_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.split_closed_view; eauto.
        }

        exists (Message.concrete val'0 max), views2. esplits.
        { econs.
          - econs 2; eauto; ss.
            { eapply message_le_to; eauto.
              eapply max_le_joined_message_le. econs; eauto. }
            { inv SIMMSG; ss. }
          - eapply joined_memory_get_closed; eauto.
            + eapply Memory.split_get0 in MEM_SRC. des. eauto.
            + inv MEM1_SRC. eapply Memory.split_inhabited; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.split_o prom2_src); eauto.
            erewrite (@Memory.split_o promises2); eauto. unfold views2. des_ifs.
            + ss. des; clarify. inv MAX; ss.
              { econs; eauto.
                { econs; eauto. }
                { right. ii. clarify. }
              }
              { econs; eauto. econs; eauto. }
            + ss. des; clarify.
              specialize (PROMISES0 loc ts3).
              rewrite GETSRC in *. erewrite GET2 in *.
              inv PROMISES0; eauto.
        }
        { eapply sim_memory_split; cycle 1; eauto. econs; [refl|].
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. destruct released'0; ss. }
        { ss. ii. erewrite (@Memory.split_o prom2_src) in *; eauto. unfold views2.
          des_ifs; eauto.
          - ss. des; clarify. unfold views. inv MAX. ss.
            econs; ss; auto.
          - ss. des; clarify. eapply REL1; eauto. }
        { i. clarify. unfold views2. des_ifs; ss; des; ss.
          eapply max_le_joined_opt_view_joined2; eauto. }
        { unfold views2. i. des_ifs. ss. des; subst.
          assert (NIL: [] = views1 loc to).
          { inv JOINMEM1. apply NNPP. ii. exploit ONLY; eauto. i. des.
            eapply Memory.split_get0 in MEM_SRC. des. clarify. }
          split; auto.
          inv MAX; ss.
          unfold views. esplits; eauto.
          { eapply Memory.split_get0 in MEM_SRC. des. eauto. }
          { eapply Memory.split_get0; eauto. }
        }
        { econs; eauto; [refl|]. eapply max_le_joined_opt_view_le; eauto. }
        { eauto. }
        { ss. }
        { ss. }
      }
      { hexploit (@Memory.split_exists (Local.promises lc1_src) loc from to ts3 Message.undef msg_src'); auto.
        intros [prom2_src PROMISES_SRC].
        hexploit (@Memory.split_exists_le (Local.promises lc1_src) mem1_src loc from to ts3 Message.undef msg_src'); eauto.
        { inv WF1_SRC. auto. }
        intros [mem2_src MEM_SRC].
        exists Message.undef, views1. esplits; ss.
        { econs; ss. econs 2; eauto. inv SIMMSG; ss. }
        { inv LOCAL1. econs; eauto. ii.
          erewrite (@Memory.split_o prom2_src); eauto.
          erewrite (@Memory.split_o promises2); eauto. des_ifs.
          guardH o. ss. des; clarify.
          specialize (PROMISES0 loc ts3). rewrite GETSRC in *. rewrite GET2 in *.
          inv PROMISES0; eauto.
        }
        { eapply sim_memory_split; cycle 1; eauto. }
        { inv JOINMEM1. econs.
          { i. erewrite Memory.split_o in GET; eauto. des_ifs; eauto.
            ss. des; clarify. hexploit (COMPLETE loc ts3); eauto.
            i. des. splits; auto. i. hexploit (ONLY loc from0); eauto.
            { destruct (views1 loc from0); ss. }
            i. des. eapply Memory.split_get0 in MEM_SRC. des; clarify.
          }
          { i. hexploit ONLY; eauto. i. des.
            eapply Memory.split_get1 in GET; eauto. des. eauto. }
          { i. eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.split_closed_view; eauto. }
        }
        { ii. ss. erewrite Memory.split_o in GET; eauto. des_ifs.
          { ss. des; clarify. eapply REL1; eauto. }
          { eapply REL1; eauto. }
        }
        { econs; eauto. }
      }
    }

    (* lower *)
    { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
      subst. inv MSG_LE; ss.
      { inv LOCAL1. dup PROMISES0. ss.
        specialize (PROMISES1 loc to). erewrite GET in *. inv PROMISES1.

        hexploit (@max_le_joined_opt_view_exists ((views1 loc to)) released); auto. i.
        guardH NIL. des.

        assert (RELEASEDLE: View.opt_le max released_src).
        { eapply max_le_joined_opt_view_le_le; eauto. }
        hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val' released_src) (Message.concrete val max)); auto.
        intros [prom2_src PROMISES_SRC].
        hexploit (@Memory.lower_exists_le prom_src mem1_src loc from to (Message.concrete val' released_src) (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [mem2_src MEM_SRC].

        assert (JOINMEM2: joined_memory views1 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.lower_o in GET0; eauto. des_ifs.
            + ss. des; clarify. splits; auto.
              * inv MAX. eapply max_le_joined_view_joined; eauto.
              * inv RELEASEDLE. exploit COMPLETE; eauto.
                { inv WF1_SRC. ss. eauto. }
                i. des. auto.
            + exploit COMPLETE; eauto.
          - i. erewrite (@Memory.lower_o mem2_src); eauto. des_ifs; eauto.
          - i. eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.lower_closed_view; eauto. }

        exists (Message.concrete val max), views1. esplits.
        { econs.
          - econs 3; eauto; ss.
            eapply message_le_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - eapply joined_memory_get_closed; eauto.
            + eapply Memory.lower_get0; eauto.
            + inv MEM1_SRC. eapply Memory.lower_inhabited; eauto.
          - ss.
        }
        { econs; eauto.
          - ii. erewrite (@Memory.lower_o prom2_src); eauto.
            erewrite (@Memory.lower_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto.
            unguard. des; auto. clarify. inv RELEASEDLE. inv MAX. auto.
        }
        { eapply sim_memory_lower; cycle 1; eauto. econs; [refl|].
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { auto. }
        { ss. ii. erewrite (@Memory.lower_o prom2_src) in *; eauto. des_ifs; eauto.
          ss. des; clarify. inv RELEASEDLE. eapply REL1; eauto. }
        { i. clarify. eapply max_le_joined_opt_view_joined; eauto. }
        { i. clarify. }
        { econs; eauto; [refl|]. eapply max_le_joined_opt_view_le; eauto. }
        { econs; eauto.
          { econs; eauto; [refl|]. eapply max_le_joined_opt_view_le; eauto. }
          { i. inv RELEASED0; ss. }
        }
        { ss. }
        { ss. }
      }
      { hexploit (@lower_same_same promises2); eauto. i. subst.
        hexploit (@lower_same_same mem2_tgt); eauto. i. subst.
        dup LOCAL1. inv LOCAL0. specialize (PROMISES0 loc to).
        ss. rewrite GET in PROMISES0. inv PROMISES0.
        exists Message.undef, views1. esplits; eauto; ss.
        { econs; ss.
          { econs; ss.
            { eapply Memory.lower_exists_same; eauto. }
            { eapply Memory.lower_exists_same; eauto. eapply WF1_SRC; eauto. }
          }
        }
      }
    }

    { hexploit Memory.remove_get0; try apply PROMISES; eauto. i. des.
      inv LOCAL1. dup PROMISES0. ss.
      specialize (PROMISES1 loc to). erewrite GET in *. inv PROMISES1.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); auto.
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.remove_exists_le prom_src mem1_src loc from to Message.reserve); eauto.
      { inv WF1_SRC. auto. }
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views1 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
          + exploit COMPLETE; eauto.
        - i. erewrite (@Memory.remove_o mem2_src); eauto. des_ifs; eauto.
          ss. des; clarify. exploit ONLY; eauto. i. des.
          inv WF1_SRC. ss. symmetry in H0. apply PROMISES1 in H0. clarify.
        - i. eapply List.Forall_impl; try apply CLOSED0. ss.
          i. eapply Memory.cancel_closed_view; eauto. }

      exists Message.reserve, views1. esplits.
      { econs; eauto. }
      { econs; eauto.
        - ii. erewrite (@Memory.remove_o prom2_src); eauto.
          erewrite (@Memory.remove_o promises2); eauto. des_ifs.
      }
      { eapply sim_memory_remove; cycle 1; eauto. }
      { assumption. }
      { auto. }
      { ss. ii. erewrite (@Memory.remove_o prom2_src) in *; eauto. des_ifs; eauto. }
      { i. clarify. }
      { i. clarify. }
      { eauto. }
      { eauto. }
      { i. splits; auto. }
      { auto. }
    }
  Qed.

  Lemma sim_local_write
        views1
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt mem2_tgt
        (loc: Loc.t)
        from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
        (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
        (RELM_SRC_WF: View.opt_wf releasedm_src)
        (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
        (RELM_TGT_WF: View.opt_wf releasedm_tgt)
        (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
        (RELM_JOINED: joined_opt_view (views1 loc from) releasedm_src)
        (ORD: Ordering.le ord_src ord_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
        (LOCAL1: sim_local views1 lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (WFVIEWS1: wf_views views1)
        (JOINMEM1: joined_memory views1 mem1_src)
        (REL1: joined_released views1 (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (CONS_TGT: Local.promise_consistent lc2_tgt)
    :
      exists released_src views2 kind_src lc2_src sc2_src mem2_src,
        (<<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src
                                      released_src
                                      ord_src lc2_src sc2_src mem2_src kind_src>>) /\
        (<<LOCAL2: sim_local views2 lc2_src lc2_tgt>>) /\
        (<<SC2: TimeMap.le sc2_src sc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views2 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views2>>) /\

        (<<REL2: joined_released views2 (Local.promises lc2_src) (TView.rel (Local.tview lc2_src))>>) /\

        (<<VIEWSLE: forall loc ts (NEQ: views2 loc ts <> views1 loc ts),
            (<<NIL: views1 loc ts = []>>) /\
            exists from val released,
              (<<GET: Memory.get loc ts mem2_src = Some (from, Message.concrete val (Some released))>>) /\
              (<<NONE: Memory.get loc ts mem1_src = None>>) /\
              (<<VIEW: views2 loc ts = (View.join ((TView.rel (Local.tview lc2_src)) loc) (View.singleton_ur loc ts))
                                         ::(all_join_views (View.singleton_ur loc ts) (views1 loc from))>>)>>) /\
        (<<RELEASED: View.opt_le released_src released_tgt>>) /\
        (<<OPT: ord_src = ord_tgt -> released_src = None <-> released_tgt = None>>) /\
        (<<KIND: sim_op_kind kind_src kind>>)
  .
  Proof.
    inv WF1_SRC.
    exploit (@TViewFacts.write_future0 loc to releasedm_src ord_src (Local.tview lc1_src) sc1_src); eauto. i. des.

    set (released_src := (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
    assert (OPT: ord_src = ord_tgt -> released_src = None <-> TView.write_released (Local.tview lc1_tgt) sc1_tgt loc to releasedm_tgt ord_tgt = None).
    { i. subst. subst released_src.
      unfold TView.write_released. destruct (Ordering.le Ordering.relaxed ord_tgt); ss.
    }
    
    exists released_src.
    set (write_tview := TView.write_tview (Local.tview lc1_src) sc1_src loc to ord_src).

    assert (CONS_SRC: forall loc0 ts0 from val released
                             (GET: Memory.get loc0 ts0 (Local.promises lc1_src) = Some (from, Message.concrete val released)),
               (<<EQ: loc0 = loc /\ ts0 = to>>) \/
               ((<<TS: Time.lt (View.rlx (TView.cur write_tview) loc0) ts0>>) /\
                (<<NEQ: __guard__(loc0 <> loc \/ loc0 = loc /\ Time.lt to ts0)>>))).
    { i. inv LOCAL1. ss. specialize (PROMISES0 loc0 ts0).
      erewrite GET in *. inv PROMISES0. symmetry in H. clear NIL.
      assert (((<<NEQ: __guard__(loc0 <> loc \/ ts0 <> to)>>) /\
               exists from0' val0' released_tgt0',
                 (<<GET_TGT: Memory.get loc0 ts0 (Local.promises lc2_tgt) =
                             Some (from0', Message.concrete val0' released_tgt0')>>))
              \/
              (loc0 = loc /\ ts0 = to)).
      { destruct (loc_ts_eq_dec (loc0, ts0) (loc, to)); auto. guardH o.
        left. split; auto.
        inv STEP_TGT. ss. inv WRITE. inv PROMISE.
        - eapply Memory.add_get1 in H; cycle 1; eauto.
          eapply Memory.remove_get1 in H; eauto. des; eauto.
          unguard. subst. des; ss.
        - eapply Memory.split_get1 in H; cycle 1; eauto. des.
          eapply Memory.remove_get1 in GET2; eauto. des; eauto.
          subst. unguard. exfalso. des; auto.
        - eapply Memory.lower_get1 in H; cycle 1; eauto. des. inv MSG_LE.
          eapply Memory.remove_get1 in GET2; eauto. des; eauto.
          subst. unguard. exfalso. des; auto.
        - ss. }
      des; auto. right. apply or_strengthen in NEQ.
      exploit CONS_TGT; eauto; ss. i. inv STEP_TGT. ss. splits.
      - eapply TimeFacts.le_lt_lt; eauto. eapply timemap_join_mon; [|refl].
        inv TVIEW. inv CUR. ss.
      - unguard. des; auto. apply NNPP in NOT. subst. right. split; auto.
        eapply TimeFacts.le_lt_lt; eauto. unfold TimeMap.join.
        unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
        eapply Time.join_r.
    }

    assert (RELEASE_SRC:
              forall (ORD: Ordering.le Ordering.acqrel ord_src = true)
                     ts from val released
                     (GET: Memory.get loc ts (Local.promises lc1_src) = Some (from, Message.concrete val (Some released))),
                False).
    { i. inv STEP_TGT. inv WRITE. ss.
      hexploit RELEASE.
      { destruct ord_tgt; ss; destruct ord_src; ss. }
      intros NONSYNCH. eapply sim_local_nonsynch_loc in NONSYNCH; eauto.
      inv LOCAL1. ss. specialize (PROMISES0 loc ts).
      erewrite GET in *. inv PROMISES0. symmetry in H. inv RELEASED.
      clear NIL. inv PROMISE; ss.
      - eapply Memory.add_get1 in H; cycle 1; eauto.
        eapply Memory.remove_get1 in H; eauto. des; subst.
        + exploit NONSYNCH; eauto. ss.
        + exploit NONSYNCH; eauto. ss.
      - eapply Memory.split_get1 in H; cycle 1; eauto. des.
        eapply Memory.remove_get1 in GET2; eauto. des; subst.
        + exploit NONSYNCH; eauto. ss.
        + exploit NONSYNCH; eauto. ss.
      - eapply Memory.lower_get1 in H; cycle 1; eauto. des. inv MSG_LE.
        eapply Memory.remove_get1 in GET2; eauto. des; subst.
        + exploit NONSYNCH; eauto. ss.
        + exploit NONSYNCH; eauto. ss.
    }

    assert (SIMMSG: Message.le (Message.concrete val released_src) (Message.concrete val released_tgt)).
    { econs; eauto; [refl|]. inv STEP_TGT. inv LOCAL1. inv WF1_TGT.
      eapply TViewFacts.write_released_mon; eauto. }

    inv STEP_TGT. inv WRITE. inv PROMISE.
    { hexploit add_succeed_wf; try apply MEM; eauto. i. des.
      set (views :=((TView.rel (write_tview)) loc)
                     ::(all_join_views (View.singleton_ur loc to) (views1 loc from))).
      set (views2 := fun (l: Loc.t) (t: Time.t) => if (loc_ts_eq_dec (l, t) (loc, to))
                                                   then unwrap_views released_src views
                                                   else views1 l t).

      assert (NOATTACH: forall ts msg
                               (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
      { i. exploit sim_memory_get_inv; try exact GET; eauto.
        { apply MEM1_SRC. }
        { apply MEM1_TGT. }
        i. des. inv FROM; cycle 1.
        { inv H. eapply ATTACH; eauto; ss. }
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.get_ts; try exact GET1. i. des.
        { subst. inv H. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. inv TO; inv H0.
          exploit Memory.get_ts; try exact GET. i. des; timetac. inv x2. }
        exploit Memory.get_disjoint; [exact GET1|exact x0|..]. i. des.
        { subst. congr. }
        apply (x3 to); econs; ss; try refl.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. eauto. }
        { etrans; eauto. econs. ss. }
      }

      hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val released_src)); auto.
      { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
        - econs; eauto.
        - i. inv H. eapply DISJOINT; eauto. }
      intros [mem2_src MEM_SRC].
      hexploit (@Memory.add_exists_le (Local.promises lc1_src) mem1_src loc from to (Message.concrete val released_src)); eauto.
      intros [prom2_src' PROMISES_SRC'].
      hexploit (@Memory.remove_exists prom2_src' loc from to (Message.concrete val released_src)).
      { eapply Memory.add_get0. eauto. }
      intros [prom2_src PROMISES_SRC].

      hexploit MemoryMerge.MemoryMerge.add_remove; try apply PROMISES_SRC; eauto.
      hexploit MemoryMerge.MemoryMerge.add_remove; try apply REMOVE; eauto.
      i. subst.

      hexploit TViewFacts.op_closed_tview; try apply SC1_SRC; eauto.
      instantiate (1:=ord_src). intros RELEASED_CLOSED.

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.add_o in GET; eauto. unfold views2.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          { ss. des; subst. inv GET.
            destruct (loc_ts_eq_dec (loc, from0) (loc, to)).
            { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
            ss. des; ss. splits.
            - unfold TView.write_released in released_src.
              unfold released_src in H2.
              destruct (Ordering.le Ordering.relaxed ord_src) eqn:ORDSRC; inv H2.
              inv RELM_JOINED.
              + eapply all_join_views_joined in JOINED. des.
                { subst. ss.
                  erewrite View.join_bot_l. eapply joined_view_exact; ss; auto. }
                ss. erewrite <- View.le_join_r with (l:=View.singleton_ur loc to); cycle 1.
                { setoid_rewrite LocFun.add_spec_eq. condtac.
                  - etrans; [|eapply View.join_r]. eapply View.join_r.
                  - etrans; [|eapply View.join_r]. eapply View.join_r. }
                erewrite <- View.join_assoc. eapply joined_view_join.
                { eapply joined_view_incl; eauto. i. ss. auto. }
                { eapply joined_view_exact; ss; auto. }
              + erewrite View.join_bot_l. eapply joined_view_exact; ss; auto.
            - i. rewrite H2. ss. right. eapply all_join_views_in; eauto.
          }
          destruct (loc_ts_eq_dec (loc0, from0) (loc, to)).
          { guardH o. ss. des; subst. exfalso. eauto. }
          { eauto. }
        - unfold views2. i. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + ss. des; subst. esplits. eapply Memory.add_get0; eauto.
          + guardH o. exploit ONLY; eauto. i. des.
            eapply Memory.add_get1 in GET; eauto.
        - i. unfold views2. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + unfold views. ss. des; subst.
            destruct released_src; ss. unfold views. econs.
            * inv RELEASED_CLOSED. ss.
            * eapply all_join_views_closed.
              { eapply Memory.singleton_ur_closed_view.
                - eapply Memory.add_get0; eauto.
                - inv MEM1_SRC. eapply Memory.add_inhabited; eauto. }
              { eapply List.Forall_impl; try apply CLOSED. ss.
                i. eapply Memory.add_closed_view; eauto. }
          + eapply List.Forall_impl; try apply CLOSED. ss.
            i. eapply Memory.add_closed_view; eauto.
      }

      exists views2. esplits.
      - econs; eauto.
        + inv LOCAL1. inv TVIEW. eapply TViewFacts.writable_mon; eauto.
        + econs; eauto. econs; eauto.
          eapply message_le_to; eauto.
        + i. eapply sim_local_nonsynch_loc; eauto.
      - inv LOCAL1. econs.
        + inv WF1_TGT. eapply TViewFacts.write_tview_mon; eauto.
        + ii. unfold views2.
          condtac; auto. ss. des. subst.
          eapply Memory.remove_get0 in PROMISES_SRC.
          eapply Memory.remove_get0 in REMOVE. des.
          rewrite GET0. rewrite GET2. econs.
      - eauto.
      - eapply sim_memory_add; cycle 1; eauto.
      - eauto.
      - unfold views2. ii. condtac; auto. destruct released_src; ss.
        ss. des; subst.
        inv WF_TVIEW. ss. econs; auto.
        eapply all_join_views_wf; eauto. eapply View.singleton_ur_wf.
      - unfold views2. ii. ss.
        exploit CONS_SRC; eauto. i. des.
        + subst. eapply Memory.add_get0 in PROMISES_SRC'. des.
          erewrite GET in *. inv GET0.
        + destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          { exfalso. ss. unguard. des; subst; ss.
            eapply Time.lt_strorder; eauto. }
          ss. unguard. guardH o. des; subst.
          { setoid_rewrite LocFun.add_spec_neq; eauto. }
          { setoid_rewrite LocFun.add_spec_eq. condtac.
            { exfalso. eapply RELEASE_SRC in GET; auto. }
            exploit REL1; eauto. i.
            erewrite View.join_assoc.
            erewrite singleton_ur_join. unfold Time.join. condtac; auto.
            exfalso. eapply Time.lt_strorder. etrans; eauto.
          }
      - unfold views2. i.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss. des. subst.
        assert (NIL: [] = views1 loc to).
        { inv JOINMEM1. apply NNPP. ii.
          hexploit ONLY; eauto. i. des.
          eapply Memory.add_get0 in MEM_SRC. des. rewrite GET in *. ss. }
        splits; ss. destruct released_src; ss.
        unfold views. esplits; eauto.
        * eapply Memory.add_get0 in MEM_SRC. des. eauto.
        * eapply Memory.add_get0; eauto.
        * f_equal. symmetry. eapply View.le_join_l.
          setoid_rewrite LocFun.add_spec_eq. condtac.
          { eapply View.join_r. }
          { eapply View.join_r. }
      - inv SIMMSG. eauto.
      - auto.
      - econs.
    }

    {
      hexploit split_succeed_wf; try apply PROMISES0; eauto. i. des.
      set (views :=((TView.rel (write_tview)) loc)
                     ::(all_join_views (View.singleton_ur loc to) (views1 loc from))).
      set (views2 := fun (l: Loc.t) (t: Time.t) => if (loc_ts_eq_dec (l, t) (loc, to))
                                                   then unwrap_views released_src views
                                                   else views1 l t).

      assert (exists msg3_src,
                 (<<GETSRC: Memory.get loc ts3 (Local.promises lc1_src) = Some (from, msg3_src)>>) /\
                 (<<GETMEMSRC: Memory.get loc ts3 mem1_src = Some (from, msg3_src)>>) /\
                 (<<SIMMSG: Message.le msg3_src msg3>>)).
      { inv LOCAL1. dup PROMISES0. ss.
        specialize (PROMISES1 loc ts3). erewrite GET2 in *. inv PROMISES1; ss.
        - esplits; eauto. inv WF1_TGT. exploit sim_memory_get; eauto.
          { i. clear NIL. des. symmetry in H0. apply PROMISES in H0. erewrite H0 in *.
            inv GET. auto. }
        - esplits; eauto.
      } des.

      hexploit (@Memory.split_exists (Local.promises lc1_src) loc from to ts3 (Message.concrete val released_src) msg3_src); auto.
      intros [prom2_src' PROMISES_SRC'].
      hexploit (@Memory.split_exists_le (Local.promises lc1_src) mem1_src loc from to ts3 (Message.concrete val released_src) msg3_src); eauto.
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.split_o in GET; eauto. unfold views2.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          { ss. des; subst. inv GET.
            destruct (loc_ts_eq_dec (loc, from0) (loc, to)).
            { exfalso. ss. des; subst. eapply Time.lt_strorder; eauto. }
            ss. des; ss. splits; ss.
            - unfold TView.write_released in released_src.
              unfold released_src in H2.
              destruct (Ordering.le Ordering.relaxed ord_src) eqn:ORDSRC; inv H2.
              inv RELM_JOINED.
              + eapply all_join_views_joined in JOINED. des.
                { subst. ss.
                  erewrite View.join_bot_l. eapply joined_view_exact; ss; auto. }
                ss. erewrite <- View.le_join_r with (l:=View.singleton_ur loc to); cycle 1.
                { setoid_rewrite LocFun.add_spec_eq. condtac.
                  - etrans; [|eapply View.join_r]. eapply View.join_r.
                  - etrans; [|eapply View.join_r]. eapply View.join_r. }
                erewrite <- View.join_assoc. eapply joined_view_join.
                { eapply joined_view_incl; eauto. i. ss. auto. }
                { eapply joined_view_exact; ss; auto. }
              + erewrite View.join_bot_l. eapply joined_view_exact; ss; auto.
            - i. rewrite H2. ss. right. eapply all_join_views_in; eauto.
          }
          destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)).
          { ss. des; subst; ss. inv GET.
            destruct (loc_ts_eq_dec (loc, from0) (loc, from0)); cycle 1.
            { ss. des; ss. }
            hexploit (COMPLETE loc ts3); eauto. i. des. splits; auto.
            unfold views. i. destruct released_src; ss. des; subst.
            - inv LOCAL1. ss. exploit REL1; eauto. i.
              setoid_rewrite LocFun.add_spec_eq. condtac.
              + exploit RELEASE_SRC; eauto. i. subst. ss.
              + erewrite View.join_assoc.
                erewrite singleton_ur_join. unfold Time.join. condtac; auto.
                exfalso. eapply Time.lt_strorder. etrans; eauto.
            - eapply all_join_views_in_iff in IN. des. subst.
              erewrite View.join_assoc.
              erewrite singleton_ur_join. unfold Time.join. condtac; auto.
              exfalso. eapply Time.lt_strorder. etrans; eauto.
          }
          destruct (loc_ts_eq_dec (loc0, from0) (loc, to)); eauto.
          { ss. des; subst; ss. exfalso.
            exploit Memory.get_disjoint.
            { eapply GET. }
            { eapply GETMEMSRC. } i. des; subst; ss.
            exploit memory_get_to_mon.
            { eapply GETMEMSRC. }
            { eapply GET. }
            { auto. } i.
            eapply x0.
            - instantiate (1:=ts3). econs; ss. left. auto.
            - econs; ss; [|refl]. etrans; eauto.
          }

        - unfold views2. i. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + ss. des; subst. eapply Memory.split_get0 in MEM_SRC. des. eauto.
          + guardH o. exploit ONLY; eauto. i. des.
            eapply Memory.split_get1 in GET; eauto. des. eauto.
        - i. unfold views2. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + unfold views. ss. destruct released_src; ss. des; subst. econs.
            * inv TVIEW_CLOSED. setoid_rewrite LocFun.add_spec_eq. condtac.
              { eapply Memory.join_closed_view.
                - eapply Memory.split_closed_view; eauto.
                - eapply Memory.singleton_ur_closed_view.
                  + eapply Memory.split_get0 in MEM_SRC. des. eauto.
                  + inv MEM1_SRC. eapply Memory.split_inhabited; eauto. }
              { eapply Memory.join_closed_view.
                - eapply Memory.split_closed_view; eauto.
                - eapply Memory.singleton_ur_closed_view.
                  + eapply Memory.split_get0 in MEM_SRC. des. eauto.
                  + inv MEM1_SRC. eapply Memory.split_inhabited; eauto. }
            * eapply all_join_views_closed.
              { eapply Memory.singleton_ur_closed_view.
                - eapply Memory.split_get0 in MEM_SRC. des. eauto.
                - inv MEM1_SRC. eapply Memory.split_inhabited; eauto. }
              { eapply List.Forall_impl; try apply CLOSED. ss.
                i. eapply Memory.split_closed_view; eauto. }
          + eapply List.Forall_impl; try apply CLOSED. ss.
            i. eapply Memory.split_closed_view; eauto.
      }

      hexploit (@Memory.remove_exists prom2_src' loc from to (Message.concrete val released_src)); auto.
      { eapply Memory.split_get0 in PROMISES_SRC'. des. eauto. }
      intros [prom2_src PROMISES_SRC].

      exists views2. esplits.
      - econs; eauto.
        + inv LOCAL1. inv TVIEW. eapply TViewFacts.writable_mon; eauto.
        + econs; eauto. econs 2; eauto; ss.
          { eapply message_le_to; eauto. }
          { subst. inv SIMMSG0; eauto; ss. }
        + i. eapply sim_local_nonsynch_loc; eauto.
      - inv LOCAL1. econs.
        + inv WF1_TGT. eapply TViewFacts.write_tview_mon; eauto.
        + ii. unfold views2.
          erewrite (@Memory.remove_o prom2_src); eauto.
          erewrite (@Memory.remove_o promises2); eauto.
          erewrite (@Memory.split_o prom2_src'); eauto.
          erewrite (@Memory.split_o promises0); eauto. ss.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); auto.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)); auto.
          ss. des; subst; ss.
          hexploit (PROMISES1 loc ts3). i.
          rewrite GET2 in *. rewrite GETSRC in *. inv H; auto.
      - auto.
      - eapply sim_memory_split; cycle 1; eauto.
      - eauto.
      - unfold views2. ii. condtac; auto. destruct released_src; ss.
        ss. des; subst.
        inv WF_TVIEW. ss. econs; auto.
        eapply all_join_views_wf; eauto. eapply View.singleton_ur_wf.
      - unfold views2. ii. ss.
        erewrite (@Memory.remove_o prom2_src) in GET; eauto.
        erewrite (@Memory.split_o prom2_src') in GET; eauto.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)).
        { ss. des; subst; ss. inv GET.
          exploit CONS_SRC; eauto. i. des; subst; ss.
          exploit (REL1 loc); eauto. i. condtac.
          - exfalso. exploit RELEASE_SRC; eauto.
          - unguard. des; ss. setoid_rewrite LocFun.add_spec_eq.
            erewrite View.join_assoc. erewrite singleton_ur_join.
            unfold Time.join. condtac; auto.
            exfalso. eapply Time.lt_strorder. etrans; eauto.
        }
        { guardH o. guardH o0.
          exploit (REL1 loc0); eauto. i.
          exploit CONS_SRC; eauto. i. des; subst; ss.
          { unguard. des; ss. } destruct NEQ.
          { setoid_rewrite LocFun.add_spec_neq; auto. }
          des; subst. setoid_rewrite LocFun.add_spec_eq. condtac.
          - exfalso. exploit RELEASE_SRC; eauto.
          - erewrite View.join_assoc. erewrite singleton_ur_join.
            unfold Time.join. condtac; auto.
            exfalso. eapply Time.lt_strorder. etrans; eauto.
        }

      - unfold views2. i.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss. des. subst.
        assert (NIL: [] = views1 loc to).
        { inv JOINMEM1. apply NNPP. ii.
          hexploit ONLY; eauto. i. des.
          eapply Memory.split_get0 in MEM_SRC. des. rewrite GET in *. ss. }
        splits; auto. destruct released_src; ss.
        + unfold views. esplits; eauto.
          * eapply Memory.split_get0 in MEM_SRC. des. eauto.
          * eapply Memory.split_get0; eauto.
          * f_equal. symmetry. eapply View.le_join_l.
            setoid_rewrite LocFun.add_spec_eq. condtac.
            { eapply View.join_r. }
            { eapply View.join_r. }
      - inv SIMMSG. eauto.
      - auto.
      - econs; eauto.
    }

    {
      des. subst. hexploit lower_succeed_wf; try apply PROMISES0; eauto. i. des.
      inv LOCAL1. ss. hexploit (PROMISES1 loc to).
      i. rewrite GET in H. inv H; [|inv MSG_LE|inv MSG_LE].
      rename H1 into GET_SRC. symmetry in GET_SRC.

      assert (RELEASED_JOINED: joined_opt_view (views1 loc to) released_src).
      { destruct released_src0 as [released_src0|]; cycle 1.
        { inv RELEASED. inv MSG_LE. inv RELEASED. rewrite <- H0 in *.
          inv SIMMSG. inv RELEASED. econs. }
        inv MSG_LE. unfold released_src, TView.write_released. condtac; econs.
        unfold TView.write_tview. ss.
        setoid_rewrite LocFun.add_spec_eq. condtac.
        - exfalso. inv RELEASED. eapply RELEASE_SRC; eauto.
        - inv RELM_JOINED; ss.
          + eapply all_join_views_joined in JOINED. clear NIL. des.
            { subst. erewrite View.join_bot_l.
              eapply joined_view_exact; eauto. }
            erewrite <- View.le_join_r with (l:=View.singleton_ur loc to); cycle 1.
            { erewrite <- View.join_assoc. eapply View.join_r. }
            erewrite <- View.join_assoc. eapply joined_view_join.
            { inv JOINMEM1. hexploit COMPLETE; eauto. i. des.
              eapply joined_view_incl; eauto. i.
              eapply all_join_views_in_iff in IN. des. subst.
              eapply INCL in IN0. eauto. }
            { eapply joined_view_exact; eauto. }
          + erewrite View.join_bot_l. hexploit (REL1 loc); eauto.
            i. eapply joined_view_exact; eauto.
      }

      assert (MSG_LE_SRC: Message.le (Message.concrete val released_src) (Message.concrete val0 released_src0)).
      { inv MSG_LE. econs; auto. eapply max_le_joined_opt_view_max; eauto.
        etrans; eauto.
        inv WF1_TGT. eapply TViewFacts.write_released_mon; eauto.
      }

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val0 released_src0) (Message.concrete val released_src)); auto.
      intros [prom2_src' PROMISES_SRC'].
      hexploit (@Memory.lower_exists_le prom_src mem1_src loc from to (Message.concrete val0 released_src0) (Message.concrete val released_src)); eauto.
      intros [mem2_src MEM_SRC].

      hexploit (@Memory.remove_exists prom2_src' loc from to (Message.concrete val released_src)); auto.
      { eapply Memory.lower_get0 in PROMISES_SRC'. clear NIL. des. eauto. }
      intros [prom2_src PROMISES_SRC].

      assert (JOINMEM2: joined_memory views1 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.lower_o in GET0; eauto.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); eauto.
          ss. clear NIL. des; subst. inv GET0. rewrite H2 in *.
          inv RELEASED_JOINED. splits; auto.
          inv MSG_LE_SRC. inv RELEASED0. hexploit COMPLETE; eauto.
          i. des. auto.
        - i. exploit ONLY; eauto. i. clear NIL. des.
          eapply Memory.lower_get1 in GET0; eauto.
          des. inv MSG_LE0. eauto.
        - i. eapply List.Forall_impl; try apply CLOSED. ss.
          i. eapply Memory.lower_closed_view; eauto.
      }

      exists views1. esplits.
      - econs; eauto.
        + inv TVIEW. eapply TViewFacts.writable_mon; eauto.
        + econs; eauto. econs 3; eauto; ss.
          eapply message_le_to; eauto.
        + i. eapply sim_local_nonsynch_loc; eauto.
      - econs.
        + inv WF1_TGT. eapply TViewFacts.write_tview_mon; eauto.
        + ii. erewrite (@Memory.remove_o prom2_src); eauto.
          erewrite (@Memory.remove_o promises2); eauto.
          erewrite (@Memory.lower_o prom2_src'); eauto.
          erewrite (@Memory.lower_o promises0); eauto.
          condtac; eauto.
      - auto.
      - eapply sim_memory_lower; cycle 1; eauto.
      - eauto.
      - auto.
      - ii. ss.
        erewrite (@Memory.remove_o prom2_src) in GET0; eauto.
        erewrite (@Memory.lower_o prom2_src') in GET0; eauto.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss.
        apply or_strengthen in o. clear NIL. des.
        { setoid_rewrite LocFun.add_spec_neq; auto.
          exploit REL1; eauto. }
        apply NNPP in NOT. subst. setoid_rewrite LocFun.add_spec_eq.
        condtac.
        { exfalso. eapply RELEASE_SRC; eauto. }
        hexploit (REL1 loc); eauto. i.
        erewrite View.join_assoc. erewrite singleton_ur_join.
        unfold Time.join. condtac; auto.
        hexploit CONS_SRC; eauto. i.
        unguard. des; subst; ss.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      - i. ss.
      - inv SIMMSG. eauto.
      - auto.
      - econs.
        { econs.
          { refl. }
          { eapply max_le_joined_opt_view_le; eauto. }
        }
        { i. inv RELEASED; ss. }
    }
    { ss. }
  Qed.

  Lemma sim_memory_write
        views1
        prom1_src mem1_src prom1_tgt mem1_tgt prom2_tgt mem2_tgt
        (loc: Loc.t)
        from to msg kind_tgt rel
        (STEP_TGT: Memory.write prom1_tgt mem1_tgt loc from to msg prom2_tgt mem2_tgt kind_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (PROM1: sim_joined_promises views1 prom1_src prom1_tgt)
        (REL1: joined_released views1 prom1_src rel)
        (MLE: Memory.le prom1_src mem1_src)
        (MSG: __guard__ (msg = Message.undef \/ (exists val', msg = Message.concrete val' None)))
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (JOINED: joined_memory views1 mem1_src)
    :
      exists prom2_src mem2_src kind_src,
        (<<STEP_SRC: Memory.write prom1_src mem1_src loc from to msg prom2_src mem2_src kind_src>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<PROM2: sim_joined_promises views1 prom2_src prom2_tgt>>) /\
        (<<JOINED: joined_memory views1 mem2_src>>) /\
        (<<REL2: joined_released views1 prom2_src rel>>) /\
        (<<KIND: sim_op_kind kind_src kind_tgt>>)
  .
  Proof.
    inv STEP_TGT. inv PROMISE.
    (* add *)
    { hexploit add_succeed_wf; eauto. i. des.
      hexploit (@Memory.add_exists mem1_src loc from to msg); eauto.
      { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
        - econs; eauto.
        - i. inv H. eapply DISJOINT; eauto. }
      i. des.
      hexploit (@Memory.add_exists_le prom1_src mem1_src); eauto. i. des.
      hexploit (@Memory.remove_exists promises0).
      { eapply Memory.add_get0. eauto. }
      i. des.
      hexploit (@MemoryMerge.MemoryMerge.add_remove loc from to msg prom1_src); eauto. i. subst.
      hexploit (@MemoryMerge.MemoryMerge.add_remove loc from to msg prom1_tgt); eauto. i. subst.
      esplits.
      { econs; eauto. econs 1; eauto.
        i. exploit sim_memory_get_inv; try exact GET; eauto.
        { apply MEM1_SRC. }
        { apply MEM1_TGT. }
        i. des. inv FROM; cycle 1.
        { inv H2. eapply ATTACH; eauto. }
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.get_ts; try exact GET1. i. des.
        { subst. inv H2. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. inv TO; inv H3.
          exploit Memory.get_ts; try exact GET. i. des; timetac. inv x2. }
        exploit Memory.get_disjoint; [exact GET1|exact x0|..]. i. des.
        { subst. congr. }
        apply (x3 to); econs; ss; try refl.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. eauto. }
        { etrans; eauto. econs. ss. }
      }
      { eapply sim_memory_add; cycle 1; eauto. refl. }
      { auto. }
      { inv JOINED. econs.
        { i. erewrite (@Memory.add_o mem2) in GET; eauto. des_ifs.
          { ss. des; clarify. unguard. des; clarify. }
          { eapply COMPLETE; eauto. }
        }
        { ii. hexploit ONLY; eauto. i. des.
          eapply Memory.add_get1 in GET; eauto. }
        { i. eapply List.Forall_impl; try apply CLOSED. ss.
          i. eapply Memory.add_closed_view; eauto. }
      }
      { auto. }
      { auto. }
    }
    (* split *)
    { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des.
      assert (exists msg3_src,
                 (<<GET: Memory.get loc ts3 prom1_src = Some (from, msg3_src)>>) /\
                 (<<CONTENT: joined_promise_content (views1 loc ts3) loc ts3 (Some (from, msg3_src)) (Some (from, msg3))>>)).
      { specialize (PROM1 loc ts3).
        rewrite GET2 in PROM1. inv PROM1; eauto. esplits; eauto. }
      des. hexploit (@Memory.split_exists prom1_src loc from to ts3 msg); eauto. i. des.
      hexploit (@Memory.split_exists_le prom1_src mem1_src); eauto. i. des.
      hexploit (@Memory.remove_exists mem2 loc from to).
      { eapply Memory.split_get0 in H. des; eauto. }
      i. des. esplits.
      { econs; eauto. econs 2; eauto. inv CONTENT; ss. }
      { eapply sim_memory_split; cycle 1; eauto. refl. }
      { ii. erewrite (@Memory.remove_o mem1); eauto. erewrite (@Memory.remove_o prom2_tgt); eauto.
        erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.split_o promises2); eauto. des_ifs.
        guardH o. ss. des; clarify. inv CONTENT; ss.
        econs; eauto.
      }
      { inv JOINED. econs.
        { i. erewrite (@Memory.split_o mem0) in GET0; eauto. des_ifs.
          { ss. des; clarify. unguard. des; clarify. }
          { ss. guardH o. des; clarify.
            hexploit (COMPLETE loc ts3); eauto. i. des.
            splits; auto. i. hexploit (ONLY loc from0).
            { destruct (views1 loc from0); ss. }
            i. des. eapply Memory.split_get0 in H0. des; clarify.
          }
          { eapply COMPLETE; eauto. }
        }
        { i. eapply ONLY in SOME; eauto. des.
          eapply Memory.split_get1 in GET0; eauto. des. eauto. }
        { i. eapply List.Forall_impl; try apply CLOSED. ss.
          i. eapply Memory.split_closed_view; eauto. }
      }
      { ii. erewrite (@Memory.remove_o mem1) in GET0; eauto.
        erewrite (@Memory.split_o mem2) in GET0; eauto. des_ifs.
        { ss. des; clarify. eapply REL1; eauto. }
        { eapply REL1; eauto. }
      }
      { econs; eauto. inv CONTENT; econs.
        { refl. }
        { eapply max_le_joined_opt_view_le; eauto. }
      }
    }
    (* lower *)
    { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
      assert (exists msg0_src,
                 (<<GET: Memory.get loc to prom1_src = Some (from, msg0_src)>>) /\
                 (<<CONTENT: joined_promise_content (views1 loc to) loc to (Some (from, msg0_src)) (Some (from, msg0))>>)).
      { specialize (PROM1 loc to).
        rewrite GET in PROM1. inv PROM1; eauto. esplits; eauto. }
      des. hexploit (@Memory.lower_exists prom1_src loc from to msg0_src); eauto.
      { inv CONTENT; ss. inv MSG_LE; ss. unguard. econs; auto. des; clarify. }
      i. des.
      hexploit (@Memory.lower_exists_le prom1_src mem1_src); eauto. i. des.
      hexploit (@Memory.remove_exists mem2 loc from to).
      { eapply Memory.lower_get0 in H. des; eauto. }
      i. des. esplits.
      { econs; eauto. }
      { eapply sim_memory_lower; cycle 1; eauto. refl. }
      { ii. erewrite (@Memory.remove_o mem1); eauto. erewrite (@Memory.remove_o prom2_tgt); eauto.
        erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.lower_o promises2); eauto. des_ifs.
      }
      { inv JOINED. econs.
        { i. erewrite (@Memory.lower_o mem0) in GET1; eauto. des_ifs.
          { ss. des; clarify. unguard. des; clarify. }
          { eapply COMPLETE; eauto. }
        }
        { i. eapply ONLY in SOME; eauto. des.
          eapply Memory.lower_get1 in GET1; eauto. des. inv MSG_LE0. eauto. }
        { i. eapply List.Forall_impl; try apply CLOSED. ss.
          i. eapply Memory.lower_closed_view; eauto. }
      }
      { ii. erewrite (@Memory.remove_o mem1) in GET1; eauto.
        erewrite (@Memory.lower_o mem2) in GET1; eauto. des_ifs.
        { eapply REL1; eauto. }
      }
      { inv CONTENT; econs; eauto.
        { econs.
          { refl. }
          { eapply max_le_joined_opt_view_le; eauto. }
        }
        { inv RELEASED; ss. }
      }
    }
    (* cancel *)
    { unguard. des; clarify. }
  Qed.

  Lemma sim_local_write_na
        views1
        prom1_src mem1_src prom1_tgt mem1_tgt prom2_tgt mem2_tgt
        (loc: Loc.t)
        from to val msgs kinds_tgt kind_tgt rel
        ts_tgt ts_src
        (STEP_TGT: Memory.write_na ts_tgt prom1_tgt mem1_tgt loc from to val prom2_tgt mem2_tgt msgs kinds_tgt kind_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (PROM1: sim_joined_promises views1 prom1_src prom1_tgt)
        (REL1: joined_released views1 prom1_src rel)
        (MLE: Memory.le prom1_src mem1_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (TS: Time.le ts_src ts_tgt)
        (JOINED: joined_memory views1 mem1_src)
    :
      exists prom2_src mem2_src kinds_src kind_src,
        (<<STEP_SRC: Memory.write_na ts_src prom1_src mem1_src loc from to val prom2_src mem2_src msgs kinds_src kind_src>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINED: joined_memory views1 mem2_src>>) /\
        (<<PROM2: sim_joined_promises views1 prom2_src prom2_tgt>>) /\
        (<<JOINED: joined_memory views1 mem2_src>>) /\
        (<<REL2: joined_released views1 prom2_src rel>>) /\
        (<<KIND: sim_op_kind kind_src kind_tgt>>) /\
        (<<KINDS: List.Forall2 sim_op_kind kinds_src kinds_tgt>>)
  .
  Proof.
    revert prom1_src mem1_src rel ts_src PROM1 MEM1_SRC MEM1_TGT MEM1 REL1 MLE TS JOINED. induction STEP_TGT.
    { i. hexploit sim_memory_write; eauto.
      { right. eauto. }
      i. des. esplits; eauto.
      { econs 1; eauto. eapply TimeFacts.le_lt_lt; eauto. }
    }
    { i. hexploit sim_memory_write; eauto.
      i. des. hexploit (IHSTEP_TGT prom2_src mem2_src); eauto.
      { eapply Memory.write_closed; eauto.
        { unguard. des; clarify. econs; eauto. }
        { unguard. des; clarify. econs; eauto. eapply Time.bot_spec. }
      }
      { eapply Memory.write_closed; eauto.
        { unguard. des; clarify. econs; eauto. }
        { unguard. des; clarify. econs; eauto. eapply Time.bot_spec. }
      }
      { eapply write_memory_le; eauto. }
      { refl. }
      i. des. esplits; eauto.
      econs 2; eauto. eapply TimeFacts.le_lt_lt; eauto.
    }
  Qed.

  Lemma sim_local_write_na_step
        views1
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt mem2_tgt
        (loc: Loc.t)
        from to val ord_src ord_tgt msgs kinds kind
        (ORD: Ordering.le ord_src ord_tgt)
        (STEP_TGT: Local.write_na_step lc1_tgt sc1_tgt mem1_tgt loc from to val ord_tgt lc2_tgt sc2_tgt mem2_tgt msgs kinds kind)
        (LOCAL1: sim_local views1 lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (WFVIEWS1: wf_views views1)
        (JOINMEM1: joined_memory views1 mem1_src)
        (REL1: joined_released views1 (Local.promises lc1_src) (TView.rel (Local.tview lc1_src)))
        (CONS_TGT: Local.promise_consistent lc2_tgt)
    :
      exists kinds_src kind_src lc2_src sc2_src mem2_src,
        (<<STEP_SRC: Local.write_na_step lc1_src sc1_src mem1_src loc from to val
                                         ord_src lc2_src sc2_src mem2_src msgs kinds_src kind_src>>) /\
        (<<LOCAL2: sim_local views1 lc2_src lc2_tgt>>) /\
        (<<SC2: TimeMap.le sc2_src sc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views1 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views1>>) /\
        (<<REL2: joined_released views1 (Local.promises lc2_src) (TView.rel (Local.tview lc2_src))>>) /\
        (<<KIND: sim_op_kind kind_src kind>>) /\
        (<<KINDS: List.Forall2 sim_op_kind kinds_src kinds>>)
  .
  Proof.
    inv LOCAL1. inv STEP_TGT. hexploit sim_local_write_na; eauto.
    { eapply WF1_SRC. }
    { ss. eapply TVIEW. }
    i. des. esplits; eauto; ss.
    { econs; eauto. eapply TViewFacts.write_tview_mon; eauto. eapply WF1_TGT. }
    { ii. exploit REL2; eauto. i.
      replace (Ordering.le Ordering.acqrel ord_src) with false.
      2:{ destruct ord_src, ord_tgt; ss. }
      match goal with
      | H: List.In ?v0 _ |- List.In ?v1 _ => replace v1 with v0
      end; auto.
      setoid_rewrite LocFun.add_spec.
      destruct (LocSet.Facts.eq_dec loc0 loc).
      { subst. rewrite View.join_assoc. f_equal.
        rewrite singleton_ur_join. f_equal.
        rewrite TimeFacts.le_join_r; auto.
        specialize (PROM2 loc ts). rewrite GET in PROM2. inv PROM2.
        exploit CONS_TGT; eauto; ss. i.
        left. eapply TimeFacts.le_lt_lt; eauto.
        unfold TimeMap.join. unfold TimeMap.singleton.
        setoid_rewrite LocFun.add_spec_eq. eapply Time.join_r.
      }
      { refl. }
    }
  Qed.

  Lemma sim_thread_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt e_tgt pf_tgt
        (STEP: Thread.step pf_tgt e_tgt th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists e_src pf_src th1_src views1,
        (<<STEP: JThread.step pf_src e_src th0_src th1_src views0 views1>>) /\
        (<<SIM: sim_thread views1 th1_src th1_tgt>>) /\
        (<<EVENT: sim_event e_src e_tgt>>)
  .
  Proof.
    dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP.
    - inv STEP0.
      hexploit sim_local_promise; eauto. i. des. esplits.
      + econs.
        * econs. econs 1; eauto.
        * i. instantiate (1:=views2). clarify. eauto.
        * eauto.
        * eauto.
        * eauto.
        * ss.
      + ss.
      + eauto.
    - inv STEP0. inv LOCAL0.
      + esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_read; eauto.
        { refl. } i. des.
        exists (ThreadEvent.read loc ts val released_src ord). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * eauto.

      + hexploit sim_local_write; eauto.
        { econs. }
        { refl. } i. des.
        exists (ThreadEvent.write loc from to val released_src ord). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { eapply VIEWSLE. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * econs; eauto; refl.

      + hexploit sim_local_read; eauto.
        { refl. } i. des.
        hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
        hexploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
        hexploit sim_local_write; eauto.
        { refl. } i. des.
        exists (ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { eapply VIEWSLE. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * eauto.

      + hexploit sim_local_fence; eauto.
        { refl. }
        { refl. } i. des.
        exists (ThreadEvent.fence ordr ordw). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_fence; eauto.
        { refl. }
        { refl. } i. des.
        exists (ThreadEvent.syscall e). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_failure; eauto.  i. des.
        exists (ThreadEvent.failure). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_write_na_step; eauto.
        { refl. }
        i. des.
        eexists (ThreadEvent.write_na _ _ _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * econs.

      + hexploit sim_local_racy_read; eauto.
        { refl. }
        i. eexists (ThreadEvent.racy_read _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_racy_write; eauto.
        { refl. }
        i. eexists (ThreadEvent.racy_write _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.

      + hexploit sim_local_racy_update; eauto.
        { refl. }
        { refl. }
        i. eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits.
        * econs.
          { econs 2; eauto. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
          { ss. }
        * ss.
        * ss.
  Qed.

  Lemma sim_thread_opt_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt e_tgt
        (STEP: Thread.opt_step e_tgt th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists e_src th1_src views1,
        (<<STEP: JThread.opt_step e_src th0_src th1_src views0 views1>>) /\
        (<<SIM: sim_thread views1 th1_src th1_tgt>>) /\
        (<<EVENT: sim_event e_src e_tgt>>)
  .
  Proof.
    inv STEP.
    - esplits; eauto.
    - exploit sim_thread_step; eauto. i. des. esplits.
      + econs 2; eauto.
      + eauto.
      + eauto.
  Qed.

  Lemma sim_thread_tau_steps views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt
        (STEPS: rtc (@Thread.tau_step lang_tgt) th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists th1_src views1,
        (<<STEPS: JThread.rtc_tau th0_src th1_src views0 views1>>) /\
        (<<SIM: sim_thread views1 th1_src th1_tgt>>).
  Proof.
    ginduction STEPS; i.
    - esplits.
      + econs 1.
      + eauto.
    - inv H. inv TSTEP.
      exploit Thread.step_future; eauto. i. des.
      hexploit PromiseConsistent.rtc_tau_step_promise_consistent; try apply STEPS; eauto.
      intros CONS_TGT'.
      exploit sim_thread_step; eauto. i. des.
      hexploit JThread.step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. esplits.
      + econs 2; eauto. rewrite <- EVENT.
        eapply sim_event_machine_event; eauto.
      + eauto.
  Qed.

  Lemma sim_thread_reserve_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt
        (STEP: Thread.reserve_step th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists th1_src,
        (<<STEP: JThread.reserve_step views0 th0_src th1_src>>) /\
        (<<SIM: sim_thread views0 th1_src th1_tgt>>)
  .
  Proof.
    dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP. inv STEP0; inv STEP; [|inv LOCAL0].
    hexploit sim_local_promise; eauto. i. des.
    specialize (RESERVE eq_refl). des; clarify. inv KIND.
    esplits; eauto. econs. econs; eauto; ss.
    econs 1; eauto. econs; eauto.
  Qed.

  Lemma sim_thread_cancel_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt
        (STEP: Thread.cancel_step th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists th1_src,
        (<<STEP: JThread.cancel_step views0 th0_src th1_src>>) /\
        (<<SIM: sim_thread views0 th1_src th1_tgt>>)
  .
  Proof.
    dup SIM. inv SIM.
    apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
    assert (st0 = st).
    { inv SIM0.
      apply inj_pair2 in H2. apply inj_pair2 in H7. subst. auto. }
    subst. clear SIM0.
    inv STEP. inv STEP0; inv STEP; [|inv LOCAL0].
    hexploit sim_local_promise; eauto. i. des.
    specialize (RESERVE eq_refl). des; clarify. inv KIND.
    esplits; eauto. econs. econs; eauto; ss.
    econs 1; eauto. econs; eauto.
  Qed.

  Lemma sim_thread_rtc_reserve_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt
        (STEPS: rtc (@Thread.reserve_step _) th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists th1_src,
        (<<STEP: rtc (@JThread.reserve_step views0 _) th0_src th1_src>>) /\
        (<<SIM: sim_thread views0 th1_src th1_tgt>>)
  .
  Proof.
    ginduction STEPS; eauto. i.
    dup H. inv H0.
    exploit Thread.step_future; eauto. clear STEP. i. des.
    exploit sim_thread_reserve_step; eauto.
    { hexploit PromiseConsistent.rtc_tau_step_promise_consistent; cycle 1; eauto.
      eapply rtc_implies; try apply STEPS. clear.
      i. inv H. econs.
      { econs; eauto. }
      { ss. }
    }
    i. des. dup STEP. inv STEP0.
    exploit JThread.step_future; eauto. i. des. clear STEP1.
    exploit IHSTEPS; eauto. i. des. esplits.
    { econs 2; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_rtc_cancel_step views0 lang_src lang_tgt
        th0_src th0_tgt th1_tgt
        (STEPS: rtc (@Thread.cancel_step _) th0_tgt th1_tgt)
        (SIM: @sim_thread views0 lang_src lang_tgt th0_src th0_tgt)

        (WF_SRC: Local.wf (Thread.local th0_src) (Thread.memory th0_src))
        (WF_TGT: Local.wf (Thread.local th0_tgt) (Thread.memory th0_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th0_src) (Thread.memory th0_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th0_tgt) (Thread.memory th0_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th0_src))
        (MEM_TGT: Memory.closed (Thread.memory th0_tgt))
        (CONS_TGT: Local.promise_consistent (Thread.local th1_tgt))

        (REL: joined_released views0 (Local.promises (Thread.local th0_src)) (Local.tview (Thread.local th0_src)).(TView.rel))
        (JOINED: joined_memory views0 (Thread.memory th0_src))
        (VIEWS: wf_views views0)
    :
      exists th1_src,
        (<<STEP: rtc (@JThread.cancel_step views0 _) th0_src th1_src>>) /\
        (<<SIM: sim_thread views0 th1_src th1_tgt>>)
  .
  Proof.
    ginduction STEPS; eauto. i.
    dup H. inv H0.
    exploit Thread.step_future; eauto. clear STEP. i. des.
    exploit sim_thread_cancel_step; eauto.
    { hexploit PromiseConsistent.rtc_tau_step_promise_consistent; cycle 1; eauto.
      eapply rtc_implies; try apply STEPS. clear.
      i. inv H. econs.
      { econs; eauto. }
      { ss. }
    }
    i. des. dup STEP. inv STEP0.
    exploit JThread.step_future; eauto. i. des. clear STEP1.
    exploit IHSTEPS; eauto. i. des. esplits.
    { econs 2; eauto. }
    { eauto. }
  Qed.

  Inductive sim_configuration
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
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_configuration
        views
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration.

  Lemma joined_memory_cap views mem cap
        (JOINED: joined_memory views mem)
        (CAP: Memory.cap mem cap)
        (CLOSED: Memory.closed mem)
    :
      joined_memory views cap.
  Proof.
    inv JOINED. econs.
    - i. eapply Memory.cap_inv in GET; eauto. des; eauto; clarify.
    - i. exploit ONLY; eauto. i. des.
      eapply Memory.cap_le in GET; eauto. refl.
    - i. eapply List.Forall_impl; try apply CLOSED0; eauto.
      i. ss. eapply Memory.cap_closed_view; eauto.
  Qed.

  Lemma sim_thread_consistent lang views (th_src th_tgt: Thread.t lang)
        (SIM: sim_thread views th_src th_tgt)
        (CONSISTENT: Thread.consistent th_tgt)

        (WF_SRC: Local.wf (Thread.local th_src) (Thread.memory th_src))
        (WF_TGT: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc th_src) (Thread.memory th_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
        (MEM_SRC: Memory.closed (Thread.memory th_src))
        (MEM_TGT: Memory.closed (Thread.memory th_tgt))

        (REL: joined_released views (Local.promises (Thread.local th_src)) (Local.tview (Thread.local th_src)).(TView.rel))
        (JOINED: joined_memory views (Thread.memory th_src))
        (VIEWS: wf_views views)
    :
      JThread.consistent th_src views.
  Proof.
    ii. hexploit (@Memory.cap_exists (Thread.memory th_tgt)); eauto. i. des.

    dup SIM. inv SIM. apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.

    assert (SIM': sim_thread
                    views
                    (Thread.mk _ st lc_src sc_src mem1)
                    (Thread.mk _ st lc_tgt sc_tgt mem2)
           ).
    { econs; eauto.
      - eapply SimMemory.sim_memory_cap; eauto.
    }

    exploit CONSISTENT; eauto. i. des.

    - inv FAILURE. des. ss.
      hexploit non_silent_step_promise_consistent; eauto.
      { rewrite EVENT_FAILURE. ss. }
      i. des.
      hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto.
      { eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. } i. ss.
      exploit sim_thread_tau_steps; try apply STEPS; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply joined_memory_cap; eauto. }
      i. des. esplits; try apply STEPS0. eauto. left.

      inv SIM. apply inj_pair2 in H4. apply inj_pair2 in H5. subst.
      hexploit Thread.rtc_tau_step_future; eauto.
      { eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      i. des.
      hexploit JThread.tau_steps_future; eauto.
      { eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply joined_memory_cap; eauto. }
      i. des. ss.
      hexploit (@sim_thread_step views1 _ lang (Thread.mk _ st0 lc_src0 sc_src0 mem_src0)); eauto.
      i. des. inv STEP. ss. esplits.
      { hexploit non_silent_step_promise_consistent; eauto.
        { inv EVENT; ss. }
        i. des. clarify. eauto.
      }
      { inv EVENT; ss. }

    - hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto.
      { ii. erewrite PROMISES in *. erewrite Memory.bot_get in PROMISE. clarify. }
      { eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. } i. ss.
      exploit sim_thread_tau_steps; try apply STEPS; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { ii. erewrite PROMISES in *. erewrite Memory.bot_get in PROMISE. clarify. }
      { eapply joined_memory_cap; eauto. }
      i. des. esplits; try apply STEPS0. right.

      inv SIM. apply inj_pair2 in H4. apply inj_pair2 in H5. subst.
      eapply sim_local_memory_bot; eauto.
  Qed.

  Lemma step_sim_configuration views0 c_src0 c_tgt0 c_tgt1 e tid
        (STEP: Configuration.step e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration views0 c_src0 c_tgt0)
        (WF_SRC: JConfiguration.wf views0 c_src0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists c_src1 views1,
        (<<STEP: JConfiguration.step e tid c_src0 c_src1 views0 views1>>) /\
        (<<SIM: sim_configuration views1 c_src1 c_tgt1>>).
  Proof.
    inv SIM. inv STEP.
    destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.failure)).
    - ss.
      dup THS. specialize (THS tid). erewrite TID in THS. ss.
      unfold option_rel in THS. des_ifs.

      dup THS. inv THS.
      apply inj_pair2 in H3. subst. inv THS1.
      apply inj_pair2 in H2. apply inj_pair2 in H4. subst.

      inv WF_SRC. inv WF_TGT. ss. inv WF. inv WF0. inv WF1.
      hexploit THREADS; eauto. hexploit THREADS0; eauto. i. ss.

      dup STEP0. hexploit non_silent_step_promise_consistent; eauto.
      { rewrite H. ss. }
      i. des. ss. clarify.
      hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto. i. ss.
      hexploit sim_thread_tau_steps; ss; eauto. i. des.

      hexploit JThread.tau_steps_future; eauto. i. des.
      hexploit Thread.rtc_tau_step_future; eauto. i. ss. des.
      hexploit sim_thread_step; eauto. i. des.
      dup SIM0. inv SIM0.
      apply inj_pair2 in H6. apply inj_pair2 in H7. ss. subst.

      hexploit JThread.step_future; eauto. ss. i. des.

      esplits.
      + ss. eapply sim_event_machine_event in EVENT0. ss.
        erewrite <- EVENT0. econs.
        * eauto.
        * eapply STEPS0.
        * eauto.
        * i. rewrite EVENT0 in NORMAL. ss.
      + econs; eauto. i. ss.
        erewrite IdentMap.gsspec. erewrite IdentMap.gsspec. des_ifs.
        specialize (THS0 tid0). unfold option_rel in *. des_ifs.
        eapply sim_statelocal_le; eauto. etrans; eauto.

    - ss.
      dup THS. specialize (THS tid). erewrite TID in THS. ss.
      unfold option_rel in THS. des_ifs.

      dup THS. inv THS.
      apply inj_pair2 in H3. subst. inv THS1.
      apply inj_pair2 in H2. apply inj_pair2 in H4. subst.

      inv WF_SRC. inv WF_TGT. ss. inv WF. inv WF0. inv WF1.
      hexploit THREADS; eauto. hexploit THREADS0; eauto. i. ss.

      hexploit Thread.rtc_tau_step_future; eauto. i. ss. des.
      hexploit Thread.step_future; eauto. i. ss. des.

      hexploit PromiseConsistent.consistent_promise_consistent; eauto. i. ss.
      hexploit PromiseConsistent.step_promise_consistent; eauto. i.
      hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto. i. ss.

      hexploit sim_thread_tau_steps; try apply STEPS; eauto. i. des.
      hexploit JThread.tau_steps_future; eauto. i. des.
      hexploit sim_thread_step; eauto. i. des.

      dup SIM0. inv SIM0.
      apply inj_pair2 in H9. apply inj_pair2 in H8. ss. subst.
      hexploit JThread.step_future; eauto. ss. i. des.

      esplits.
      + ss. eapply sim_event_machine_event in EVENT0. ss.
        erewrite <- EVENT0. econs.
        * eauto.
        * eapply STEPS0.
        * eauto.
        * i. eapply sim_thread_consistent; eauto.
      + econs; eauto. i. ss.
        erewrite IdentMap.gsspec. erewrite IdentMap.gsspec. des_ifs.
        specialize (THS0 tid0). unfold option_rel in *. des_ifs.
        eapply sim_statelocal_le; eauto. etrans; eauto.
  Qed.

  (* Lemma single_step_sim_configuration views0 c_src0 c_tgt0 c_tgt1 e_tgt tid *)
  (*       (STEP: SConfiguration.step e_tgt tid c_tgt0 c_tgt1) *)
  (*       (SIM: sim_configuration views0 c_src0 c_tgt0) *)
  (*       (WF_SRC: JConfiguration.wf views0 c_src0) *)
  (*       (WF_TGT: Configuration.wf c_tgt0) *)
  (*   : *)
  (*     exists c_src1 views1 e_src, *)
  (*       (<<STEP: JConfiguration.single_step e_src tid c_src0 c_src1 views0 views1>>) /\ *)
  (*       (<<SIM: sim_configuration views1 c_src1 c_tgt1>>) /\ *)
  (*       (<<EVENT: sim_event e_src e_tgt>>). *)
  (* Proof. *)
  (*   inv SIM. inv STEP. ss. *)
  (*   dup THS. specialize (THS tid). rewrite TID in THS. ss. *)
  (*   unfold option_rel in THS. des_ifs. dep_clarify. *)
  (*   dup THS. dep_inv THS1. dep_inv THS. *)
  (*   inv WF_SRC. inv WF_TGT. ss. inv WF. inv WF0. inv WF1. *)
  (*   hexploit THREADS; eauto. hexploit THREADS0; eauto. i. ss. *)

  (*   hexploit Thread.rtc_cancel_step_future; eauto. i. des. ss. *)
  (*   hexploit Thread.opt_step_future; eauto. i. des. ss. *)
  (*   hexploit Thread.rtc_reserve_step_future; eauto. i. des. ss. *)

  (*   assert (CONSISTENT3: Local.promise_consistent lc4). *)
  (*   { destruct (classic (e_tgt = ThreadEvent.failure)). *)
  (*     { subst. eapply PromiseConsistent.rtc_reserve_step_promise_consistent2 in RESERVES; eauto. *)
  (*       inv STEP0. inv STEP; inv STEP0. inv LOCAL1. inv LOCAL2. ss. } *)
  (*     { hexploit PromiseConsistent.consistent_promise_consistent; eauto. } *)
  (*   } *)
  (*   assert (CONSISTENT2: Local.promise_consistent (Thread.local e3)). *)
  (*   { eapply PromiseConsistent.rtc_reserve_step_promise_consistent in RESERVES; eauto. } *)
  (*   assert (CONSISTENT1: Local.promise_consistent (Thread.local e2)). *)
  (*   { inv STEP0; eauto. *)
  (*     eapply PromiseConsistent.step_promise_consistent in STEP; eauto. } *)
  (*   assert (CONSISTENT0: Local.promise_consistent lc1). *)
  (*   { eapply PromiseConsistent.rtc_cancel_step_promise_consistent in CANCELS; eauto. } *)

  (*   hexploit sim_thread_rtc_cancel_step; eauto. i. des. *)
  (*   hexploit JThread.rtc_cancel_step_future; eauto. i. des. ss. *)
  (*   hexploit sim_thread_opt_step; eauto. i. des. *)
  (*   hexploit JThread.opt_step_future; eauto. i. des. ss. *)
  (*   hexploit sim_thread_rtc_reserve_step; eauto. i. des. *)
  (*   hexploit JThread.rtc_reserve_step_future; eauto. i. des. ss. *)

  (*   destruct th1_src1. ss. esplits. *)
  (*   + econs. *)
  (*     * eauto. *)
  (*     * eapply STEP. *)
  (*     * eapply STEP1. *)
  (*     * eapply STEP2. *)
  (*     * i. eapply sim_thread_consistent; eauto. *)
  (*       eapply CONSISTENT. ii. subst. inv EVENT; ss. *)
  (*   + dep_inv SIM1. econs; eauto. i. ss. *)
  (*     erewrite IdentMap.gsspec. erewrite IdentMap.gsspec. des_ifs. *)
  (*     specialize (THS0 tid0). unfold option_rel in *. des_ifs. *)
  (*     eapply sim_statelocal_le; eauto. *)
  (*   + auto. *)
  (* Qed. *)

  (* Lemma single_machine_step_sim_configuration views0 c_src0 c_tgt0 c_tgt1 e tid *)
  (*       (STEP: SConfiguration.machine_step e tid c_tgt0 c_tgt1) *)
  (*       (SIM: sim_configuration views0 c_src0 c_tgt0) *)
  (*       (WF_SRC: JConfiguration.wf views0 c_src0) *)
  (*       (WF_TGT: Configuration.wf c_tgt0) *)
  (*   : *)
  (*     exists c_src1 views1, *)
  (*       (<<STEP: JConfiguration.machine_single_step e tid c_src0 c_src1 views0 views1>>) /\ *)
  (*       (<<SIM: sim_configuration views1 c_src1 c_tgt1>>). *)
  (* Proof. *)
  (*   inv STEP. exploit single_step_sim_configuration; eauto. i. des. *)
  (*   esplits; eauto. *)
  (*   erewrite <- sim_event_machine_event; eauto. *)
  (* Qed. *)

  Lemma sim_configuration_terminal views c_src c_tgt
        (SIM: sim_configuration views c_src c_tgt)
        (TERMINAL: Configuration.is_terminal c_tgt)
    :
      Configuration.is_terminal c_src.
  Proof.
    ii. inv SIM. ss.
    specialize (THS tid). rewrite FIND in THS.
    unfold option_rel in THS. des_ifs. dependent destruction THS.
    exploit (TERMINAL tid); eauto. i. des. splits; auto.
    inv THREAD. econs. eapply sim_local_memory_bot; eauto.
  Qed.

  Lemma multi_step_machine_behavior views0 c_src0 c_tgt0
        (SIM: sim_configuration views0 c_src0 c_tgt0)
        (WF_SRC: JConfiguration.wf views0 c_src0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      behaviors Configuration.step c_tgt0 <2=
      behaviors Configuration.step c_src0.
  Proof.
    ii. revert views0 c_src0 SIM WF_SRC. induction PR.
    - i. econs 1. eapply sim_configuration_terminal; eauto.
    - i. exploit step_sim_configuration; eauto. i. des.
      econs 2.
      { eapply JConfiguration.step_configuration_step; eauto. }
      { eapply IHPR; eauto.
        { eapply Configuration.step_future in STEP; eauto. des. auto. }
        { eapply JConfiguration.step_future in STEP0; eauto. des. auto. }
      }
      { auto. }
    - i. exploit step_sim_configuration; eauto. i. des.
      econs 3.
      { eapply JConfiguration.step_configuration_step; eauto. }
    - i. exploit step_sim_configuration; eauto. i. des.
      econs 4.
      { eapply JConfiguration.step_configuration_step; eauto. }
      { eapply IHPR; eauto.
        { eapply Configuration.step_future in STEP; eauto. des. auto. }
        { eapply JConfiguration.step_future in STEP0; eauto. des. auto. }
      }
    - i. econs 5.
  Qed.

  (* Lemma machine_behavior views0 c_src0 c_tgt0 *)
  (*       (SIM: sim_configuration views0 c_src0 c_tgt0) *)
  (*       (WF_SRC: JConfiguration.wf views0 c_src0) *)
  (*       (WF_TGT: Configuration.wf c_tgt0) *)
  (*   : *)
  (*     behaviors SConfiguration.machine_step c_tgt0 <1= *)
  (*     behaviors SConfiguration.machine_step c_src0. *)
  (* Proof. *)
  (*   ii. eapply SConfiguration.multi_step_equiv in PR; auto. *)
  (*   eapply multi_step_machine_behavior in PR; eauto. *)
  (*   eapply SConfiguration.multi_step_equiv; eauto. eapply WF_SRC. *)
  (* Qed. *)
End JSim.
