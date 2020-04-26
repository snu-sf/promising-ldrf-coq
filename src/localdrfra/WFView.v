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

  Definition semi_contain_view (view: View.t) (vw0: View.t) (views1: list View.t): Prop :=
    forall (VIEWLE: View.le vw0 view),
    exists vw1,
      (<<IN: joined_view views1 vw1>>) /\
      (<<VIEWLE0: View.le vw0 vw1>>) /\
      (<<VIEWLE1: View.le vw1 view>>).

  Definition semi_sub_views (view: View.t) (views0 views1: list View.t): Prop :=
    forall vw0
           (IN: List.In vw0 views0),
      semi_contain_view view vw0 views1.

  Lemma contain_semi_contain_view view vw0 views1
        (IN: List.In vw0 views1)
    :
      semi_contain_view view vw0 views1.
  Proof.
    ii. exists vw0. splits; auto.
    - apply joined_view_exact; eauto.
    - refl.
  Qed.

  Lemma sub_semi_sub_views view views0 views1
        (INCL: forall vw (IN: List.In vw views0), List.In vw views1)
    :
      semi_sub_views view views0 views1.
  Proof.
    ii. eapply contain_semi_contain_view; eauto.
  Qed.

  Inductive joined_memory
            (views: Loc.t -> Time.t -> list View.t)
            (mem: Memory.t): Prop :=
  | joined_memory_intro
      (COMPLETE: forall loc ts from val released
                        (GET: Memory.get loc ts mem = Some (from, Message.concrete val (Some released))),

          (* (<<SINGLETON: joined_view (views loc ts) (View.singleton_ur loc ts)>>) /\ *)
          (* (<<JOINED: joined_view (views loc ts) released>>) /\ *)

          (* (<<JOINED: joined_view ((View.singleton_ur loc ts)::(views loc ts)) released>>) /\ *)

          (<<JOINED: joined_view (views loc ts) released>>) /\

          (<<INCL: forall view (IN: List.In view (views loc from)),
              List.In view (views loc ts)>>)
      )
      (ONLY: forall loc ts (SOME: views loc ts <> []),
          exists from val released,
            (<<GET: Memory.get loc ts mem = Some (from, Message.concrete val released)>>))
      (CLOSED: forall loc ts, List.Forall (fun vw => Memory.closed_view vw mem) (views loc ts))
  .

  Lemma joined_view_closed_aux
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

  Lemma joined_view_closed
        views view mem loc ts rel
        (JOINED: joined_view ((View.join rel (View.singleton_ur loc ts))::(views loc ts)) view)
        (MEM: joined_memory views mem)
        (RELEASE: Memory.closed_view rel mem)
        (INHABITED: Memory.inhabited mem)
        from val released
        (CLOSED: Memory.get loc ts mem = Some (from, (Message.concrete val released)))
    :
      Memory.closed_view view mem.
  Proof.
    apply joined_view_cons in JOINED. des.
    - eapply joined_view_closed_aux; eauto.
    - subst. eapply Memory.join_closed_view.
      + eapply Memory.join_closed_view; eauto.
        eapply Memory.singleton_ur_closed_view; eauto.
      + eapply joined_view_closed_aux; eauto.
  Qed.

  Lemma joined_opt_view_closed
        views view mem loc ts rel
        (JOINED: joined_opt_view ((View.join rel (View.singleton_ur loc ts))::(views loc ts)) view)
        (MEM: joined_memory views mem)
        (RELEASE: Memory.closed_view rel mem)
        (INHABITED: Memory.inhabited mem)
        from val released
        (CLOSED: Memory.get loc ts mem = Some (from, (Message.concrete val released)))
    :
      Memory.closed_opt_view view mem.
  Proof.
    inv JOINED; econs. eapply joined_view_closed; eauto.
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

  Lemma joined_view_sub views0 views1 view
        (VIEWSWF: List.Forall View.wf views1)
        (JOINED: joined_view views0 view)
        (INCL: semi_sub_views view views0 views1)
    :
      joined_view views1 view.
  Proof.
    unfold semi_sub_views in *.
    hexploit (@max_le_joined_view_exists views1 view); auto. i. des.
    assert (JOINED1: joined_view views1 max).
    { eapply max_le_joined_view_joined; eauto. }
    replace view with (View.join max view); cycle 1.
    { apply View.le_join_r.
      eapply max_le_joined_view_le; eauto. }
    assert (INCL1: forall vw0
                          (VIEWLE: View.le vw0 view)
                          (IN: List.In vw0 views0),
               exists vw1,
                 (<<IN: joined_view views1 vw1>>) /\
                 (<<VIEWLE0: View.le vw0 vw1>>) /\
                 (<<VIEWLE1: View.le vw1 max>>)).
    { i. exploit INCL; eauto. i. des. esplits; eauto.
      eapply max_le_joined_view_max; eauto. } clear INCL.
    clear MAX. ginduction JOINED; ss; i.
    - erewrite View.join_bot_r. auto.
    - exploit IHJOINED; eauto.
      { i. exploit INCL1; eauto. etrans; eauto. eapply View.join_r. }
      i. erewrite (@View.join_comm vw0 vw1).
      erewrite <- View.join_assoc.
      erewrite (View.join_comm).
      rewrite View.le_join_r; eauto.
      hexploit (INCL1 vw0); eauto.
      { eapply View.join_l. } i. des.
      etrans; eauto. etrans; eauto. eapply View.join_l.
  Qed.

  Definition joined_released
             (views: Loc.t -> Time.t -> list View.t)
             (prom: Memory.t)
             (rel: Loc.t -> View.t): Prop :=
    forall loc ts from val released
           (GET: Memory.get loc ts prom = Some (from, Message.concrete val (Some released))),
      joined_view (views loc ts) (View.join (rel loc) (View.singleton_ur loc ts))
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
      (VIEWSTO: forall loc ts, List.Forall (fun vw => Time.le (View.rlx vw loc) ts) (views2 loc ts))

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
            (loc: Loc.t) (ts: Time.t)
  : forall (msg_src msg_tgt: option (Time.t * Message.t)), Prop :=
  | joined_promise_content_concrete
      from val released_src released_tgt
      (RELEASED: max_le_joined_opt_view views released_tgt released_src)
      (NIL: views <> [])
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
    ii. exploit REL; eauto. i. des.
    destruct (views0 loc ts) eqn:VIEW.
    - eapply joined_view_incl; eauto. i. ss.
    - exploit VIEWSLE; eauto.
      { erewrite VIEW. ss. }
      i. rewrite x0. rewrite VIEW. eauto.
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
      + ss. ii. exploit REL; eauto. i.
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
        (CONS_TGT: Local.promise_consistent lc2_tgt)
        (VIEWSTO: forall loc ts, List.Forall (fun vw => Time.le (View.rlx vw loc) ts) (views1 loc ts))
    :
      exists msg_src views2 kind_src lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
        (<<LOCAL2: sim_local views2 lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views2 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views2>>) /\
        (<<VIEWSTO: forall loc ts, List.Forall (fun vw => Time.le (View.rlx vw loc) ts) (views2 loc ts)>>)
  .
  Proof.
    inv STEP_TGT. inv PROMISE.
    { hexploit add_succeed_wf; try apply MEM; eauto. i. des.
      destruct msg_tgt as [val released_tgt|].

      (* add concrete message *)
      { assert (NOATTACH: forall ts msg
                                 (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
        { i. exploit sim_memory_get_inv; try exact GET; eauto.
          { apply MEM1_SRC. }
          { apply MEM1_TGT. }
          i. des. inv FROM; cycle 1.
          { inv H. eauto. }
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

        set (views := (View.join (lc1_src.(Local.tview).(TView.rel) loc) (View.singleton_ur loc to))
                        ::(views1 loc from)).
        assert (VIEWWF: View.wf (View.join (TView.rel (Local.tview lc1_src) loc) (View.singleton_ur loc to))).
        { inv WF1_SRC. inv TVIEW_WF.
          eapply View.join_wf; eauto. eapply View.singleton_ur_wf. }
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs; eauto. }
        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then views
                                  else views1 l t).
        hexploit (@max_le_joined_opt_view_exists views released_tgt).
        { econs; auto. } i. des.

        hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val max)); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        { econs; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists (Message.concrete val max), views2.

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits; auto.
              inv MAX. eapply max_le_joined_view_joined; eauto.
            + ss. des; clarify. exfalso. eauto.
            + eapply COMPLETE; eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
            + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
          - unfold views2. ii. des_ifs.
            + ss. des; clarify. unfold views. econs.
              { inv WF1_SRC. inv TVIEW_CLOSED.
                eapply Memory.add_closed_view; eauto. }
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
        }

        esplits.
        { econs.
          - econs; eauto.
            eapply sim_message_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - econs. eapply joined_opt_view_closed; eauto.
            + instantiate (1:=to). instantiate (1:=loc).
              eapply max_le_joined_opt_view_joined; eauto.
              unfold views2. des_ifs; ss; des; clarify. eauto.
            + inv MEM1_SRC. eapply Memory.add_inhabited; eauto.
            + eapply Memory.add_get0; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. unfold views2.
            erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto. ss.
          - ss. ii. unfold views2.
            erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
            ss. des; clarify. econs; ss; auto.
            eapply joined_view_exact; ss. auto. }
        { eapply sim_memory_add; cycle 1; eauto. econs.
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. }
        { unfold views2. ii. des_ifs. ss. des; clarify. econs; ss.
          - exploit CONS_TGT.
            { eapply Memory.add_get0; eauto. }
            i. ss. left. eapply TimeFacts.le_lt_lt; eauto.
            inv LOCAL1. inv TVIEW. ss. specialize (REL0 loc). inv REL0.
            etrans; eauto. inv WF1_TGT. ss. inv TVIEW_WF.
            specialize (REL_CUR loc). inv REL_CUR. ss.
          - eapply List.Forall_impl; cycle 1.
            * eapply VIEWSTO.
            * ss. i. etrans; eauto. left. auto.
        }
      }

      (* add reserve *)
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.reserve); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to Message.reserve); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.reserve, views1.

        esplits.
        { econs.
          - econs; eauto. i. clarify.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
          - ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
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
        { auto. }
      }
    }

    (* split *)
    { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des. subst.

      set (views :=(lc1_src.(Local.tview).(TView.rel) loc)
                     ::(views1 loc from)).
      assert (VIEWSWF: List.Forall View.wf views).
      { unfold views. econs.
        { inv WF1_SRC. inv TVIEW_WF. ss. }
        eauto.
      }
      set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                then views
                                else views1 l t).
      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::views) released').
      { econs; auto. eapply View.singleton_ur_wf. } i. des.

      assert (exists msg3_src,
                 (<<GETSRC: Memory.get loc ts3 lc1_src.(Local.promises) = Some (from, msg3_src)>>) /\
                 (<<GETMEMSRC: Memory.get loc ts3 mem1_src = Some (from, msg3_src)>>) /\
                 (<<SIMMSG: sim_message msg3_src msg3>>)).
      { inv LOCAL1. inv WF1_SRC. dup PROMISES0. ss.
        specialize (PROMISES2 loc ts3). erewrite GET2 in *. inv PROMISES2.
        - esplits; eauto. inv WF1_TGT. exploit sim_memory_get; eauto.
          { i. des. symmetry in H0. apply PROMISES1 in H0. clarify. }
        - esplits; eauto. } des.

      hexploit (@Memory.split_exists lc1_src.(Local.promises) loc from to ts3 (Message.concrete val' max) msg3_src); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.split_exists_le lc1_src.(Local.promises) mem1_src loc from to ts3 (Message.concrete val' max) msg3_src); eauto.
      { inv WF1_SRC. auto. }
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.split_o in GET; eauto. unfold views2. des_ifs.
          + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
          + ss. des; clarify. splits; auto.
            * inv MAX. econs; ss; auto.
              eapply max_le_joined_view_joined; eauto.
            * unfold views. ii. econs; ss; auto.
              eapply joined_view_exact; ss; auto.
          + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
            ii; ss. des; auto. subst. inv LOCAL1. exploit REL; eauto.
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
          des_ifs; eauto. ss. des; clarify.
          hexploit (ONLY loc ts3); eauto. i. des. clarify. eauto.
        - unfold views2. i. des_ifs.
          + ss. des; clarify. unfold views. econs.
            * eapply Memory.split_closed_view; eauto.
              inv WF1_SRC. inv TVIEW_CLOSED. auto.
            * eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.split_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.split_closed_view; eauto.
      }

      exists (Message.concrete val' max), views2. esplits.
      { econs.
        - econs 2; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            unfold views2. des_ifs; ss; des; clarify.
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.split_inhabited; eauto.
          + eapply Memory.split_get0 in MEM_SRC. des; eauto.
        - ss.
      }
      { inv LOCAL1. econs; eauto.
        - ii. erewrite (@Memory.split_o prom2_src); eauto.
          erewrite (@Memory.split_o promises2); eauto. unfold views2. des_ifs.
          + ss. des; clarify. econs; eauto. ss.
          + ss. des; clarify.
            specialize (PROMISES0 loc ts3).
            rewrite GETSRC in *. erewrite GET2 in *.
            inv PROMISES0; eauto.
        - ss. ii. erewrite (@Memory.split_o prom2_src) in *; eauto. unfold views2.
          des_ifs; eauto.
          + ss. des; clarify. unfold views.
            econs; ss; auto. eapply joined_view_exact; ss; auto.
          + ss. des; clarify. eapply REL; eauto. }
      { eapply sim_memory_split; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { ii. unfold views2. des_ifs. }
      { unfold views2. ii. des_ifs. ss. des; clarify. econs; ss.
        - exploit CONS_TGT.
          { eapply Memory.split_get0 in PROMISES. des. eapply GET1. }
          i. ss. left. eapply TimeFacts.le_lt_lt; eauto.
          inv LOCAL1. inv TVIEW. ss. specialize (REL0 loc). inv REL0.
          etrans; eauto. inv WF1_TGT. ss. inv TVIEW_WF.
          specialize (REL_CUR loc). inv REL_CUR. ss.
        - eapply List.Forall_impl; cycle 1.
          { eapply VIEWSTO. }
          ss. i. left. eapply TimeFacts.le_lt_lt; eauto.
      }

    }

    (* lower *)
    { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
      subst. inv MSG_LE.
      inv LOCAL1. dup PROMISES0. ss.
      specialize (PROMISES1 loc to). erewrite GET in *. inv PROMISES1.

      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::(views1 loc to)) released0).
      { econs; auto. eapply View.singleton_ur_wf. } i. des.
      (* hexploit max_le_joined_opt_view_le; eauto. intros SIMMSG. *)

      assert (RELEASEDLE: View.opt_le max released_src).
      { eapply max_le_joined_opt_view_le_le; eauto. }
      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val max)); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.lower_exists_le prom_src mem1_src loc from to (Message.concrete val released_src) (Message.concrete val max)); eauto.
      { inv WF1_SRC. auto. }
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views1 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.lower_o in GET0; eauto. des_ifs.
          + ss. des; clarify. splits; auto.
            * econs; ss; auto. inv MAX.
              eapply max_le_joined_view_joined; eauto.
            * inv RELEASEDLE. exploit COMPLETE; eauto.
              { inv WF1_SRC. ss. eauto. }
              i. des. auto.
          + exploit COMPLETE; eauto.
        - i. erewrite (@Memory.lower_o mem2_src); eauto. des_ifs; eauto.
        - i. eapply List.Forall_impl; try apply CLOSED0. ss.
          i. eapply Memory.lower_closed_view; eauto. }

      exists (Message.concrete val max), views1. esplits.
      { econs.
        - econs 3; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.lower_inhabited; eauto.
          + eapply Memory.lower_get0; eauto.
        - ss.
      }
      { econs; eauto.
        - ii. erewrite (@Memory.lower_o prom2_src); eauto.
          erewrite (@Memory.lower_o promises2); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
        - ss. ii. erewrite (@Memory.lower_o prom2_src) in *; eauto. des_ifs; eauto.
          ss. des; clarify. inv RELEASEDLE. eapply REL; eauto. }
      { eapply sim_memory_lower; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { auto. }
      { auto. }
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
        - ss. ii. erewrite (@Memory.remove_o prom2_src) in *; eauto. des_ifs; eauto. }
      { eapply sim_memory_remove; cycle 1; eauto. }
      { assumption. }
      { auto. }
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
        (RELM_JOINED: joined_opt_view ((View.singleton_ur loc from)::(views1 loc from)) releasedm_src)
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
        (<<WFVIEWS2: wf_views views2>>)
  .
  Proof.
    inv WF1_SRC.
    exploit (@TViewFacts.write_future0 loc to releasedm_src ord_src (Local.tview lc1_src) sc1_src); eauto. i. des.

    set (released_src := (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
    exists released_src.
    set (write_tview := TView.write_tview (Local.tview lc1_src) sc1_src loc to ord_src).

    assert (CONS_SRC: forall loc0 ts0 from val released
                             (GET: Memory.get loc0 ts0 (Local.promises lc1_src) = Some (from, Message.concrete val released)),
               (<<EQ: loc0 = loc /\ ts0 = to>>) \/
               ((<<TS: Time.lt (View.rlx (TView.cur write_tview) loc0) ts0>>) /\
                (<<NEQ: __guard__(loc0 <> loc \/ loc0 = loc /\ Time.lt to ts0)>>))).
    { i. inv LOCAL1. ss. specialize (PROMISES0 loc0 ts0).
      erewrite GET in *. inv PROMISES0. symmetry in H.
      assert (((<<NEQ: __guard__(loc0 <> loc \/ ts0 <> to)>>) /\
               exists from0' val0' released_tgt0',
                 (<<GET_TGT: Memory.get loc0 ts0 lc2_tgt.(Local.promises) =
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
      exploit CONS_TGT; eauto. i. inv STEP_TGT. ss. splits.
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
                to = ts).
   { i. inv STEP_TGT. inv WRITE. ss.
      hexploit RELEASE.
      { destruct ord_tgt; ss; destruct ord_src; ss. }
      intros NONSYNCH. eapply sim_local_nonsynch_loc in NONSYNCH; eauto.
      inv LOCAL1. ss. specialize (PROMISES0 loc ts).
      erewrite GET in *. inv PROMISES0. symmetry in H.
      inv PROMISE; ss.
      - eapply Memory.add_get1 in H; cycle 1; eauto.
        eapply Memory.remove_get1 in H; eauto. des; eauto.
        exploit NONSYNCH; eauto. ss.
      - eapply Memory.split_get1 in H; cycle 1; eauto. des.
        eapply Memory.remove_get1 in GET2; eauto. des; eauto.
        exploit NONSYNCH; eauto. ss.
      - eapply Memory.lower_get1 in H; cycle 1; eauto. des. inv MSG_LE.
        eapply Memory.remove_get1 in GET2; eauto. des; eauto.
        exploit NONSYNCH; eauto. ss.
   }

    assert (SIMMSG: sim_message (Message.concrete val released_src) (Message.concrete val released_tgt)).
    { econs; eauto. inv STEP_TGT. inv LOCAL1. inv WF1_TGT.
      eapply TViewFacts.write_released_mon; eauto. }

    inv STEP_TGT. inv WRITE. inv PROMISE.
    { hexploit add_succeed_wf; try apply MEM; eauto. i. des.
      set (views :=((write_tview).(TView.rel) loc)
                     ::(views1 loc from)).
      set (views2 := fun (l: Loc.t) (t: Time.t) => if (loc_ts_eq_dec (l, t) (loc, to))
                                                   then views
                                                   else views1 l t).

      assert (NOATTACH: forall ts msg
                               (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
      { i. exploit sim_memory_get_inv; try exact GET; eauto.
        { apply MEM1_SRC. }
        { apply MEM1_TGT. }
        i. des. inv FROM; cycle 1.
        { inv H. eauto. }
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
      { econs; eauto. }
      intros [mem2_src MEM_SRC].
      hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val released_src)); eauto.
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
              eapply semi_joined_view_join.

              + dup RELM_JOINED. inv RELM_JOINED; ss; eauto.
                * econs; ss; auto. eapply

                  admit.
                * eapply semi_joined_view_bot.

                  s.

                admit.

              + econs; ss; auto. eapply joined_view_exact. ss. auto.

            -

                eapply semi_joined_

                     econs.



    set (released_src := (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
    exists released_src.
    set (write_tview := TView.write_tview (Local.tview lc1_src) sc1_src loc to ord_src).

              unfold views.



              admit.

            - ii. unfold views. econs; ss; auto.
              eapply joined_view_exact; ss; auto. }
          destruct (loc_ts_eq_dec (loc0, from0) (loc, to)).
          { guardH o. ss. des; subst. exfalso. eauto. }
          { eauto. }
        - unfold views2. i. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + ss. des; subst. esplits. eapply Memory.add_get0; eauto.
          + guardH o. exploit ONLY; eauto. i. des.
            eapply Memory.add_get1 in GET; eauto.
        - i. unfold views2. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
          + unfold views. ss. des; subst. unfold views. econs.
            * inv RELEASED_CLOSED. ss.
            * eapply List.Forall_impl; try apply CLOSED. ss.
              i. eapply Memory.add_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED. ss.
            i. eapply Memory.add_closed_view; eauto.
      }

      exists views2. esplits.
      - econs; eauto.
        + inv LOCAL1. inv TVIEW. eapply TViewFacts.writable_mon; eauto.
        + econs; eauto. econs; eauto.
          eapply sim_message_to; eauto.
        + i. eapply sim_local_nonsynch_loc; eauto.
      - inv LOCAL1. econs.
        + inv WF1_TGT. eapply TViewFacts.write_tview_mon; eauto.
        + ii. unfold views2.
          condtac; auto. ss. des. subst.
          eapply Memory.remove_get0 in PROMISES_SRC.
          eapply Memory.remove_get0 in REMOVE. des.
          rewrite GET0. rewrite GET2. econs.
        + unfold views2. ii. ss.
          exploit CONS_SRC; eauto. i. des.
          * subst. eapply Memory.add_get0 in PROMISES_SRC'. des.
            erewrite GET in *. inv GET0.
          * destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
            { exfalso. ss. unguard. des; subst; ss.
              eapply Time.lt_strorder; eauto. }
            ss. unguard. guardH o. des; subst.
            { setoid_rewrite LocFun.add_spec_neq; eauto. }
            { setoid_rewrite LocFun.add_spec_eq. condtac.
              { exfalso. eapply RELEASE_SRC in GET; auto.
                subst. eapply Time.lt_strorder; eauto. }
              exploit REL; eauto. i.
              eapply semi_joined_view_join; eauto.
              eapply joined_view_exact. ss. left.
              symmetry. eapply View.le_join_l.
              eapply View.singleton_ur_spec.
              - eapply View.singleton_ur_wf.
              - ss. unfold TimeMap.singleton.
                setoid_rewrite LocFun.add_spec_eq. left. auto. }
      - eauto.
      - eapply sim_memory_add; cycle 1; eauto.
      - eauto.
      - unfold views2. ii. condtac; auto. ss. des; subst.
        inv WF_TVIEW. ss. econs; auto.
    }


        { admit. }auto.

        econs.
        { inv WF1_SRC. inv TVIEW_WF. ss. }
        eauto.

        eauto.

        econs.
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. }
      }
      {


            destruct (Loc.eq_dec loc0 loc).
            { subst. des; ss.
              admit. }
            {




      assert (JOINEDVIEW: joined_opt_view
                            ((View.singleton_ur loc to)
                               ::(views2 loc to)) released_src).
      { unfold released_src. unfold TView.write_released. condtac; econs.
        assert (JOINEDVIEW: joined_view
                              ((View.singleton_ur loc to)
                                 ::(View.singleton_ur loc from)
                                 ::((write_tview).(TView.rel) loc)
                                 ::(lc1_src.(Local.tview).(TView.rel) loc)
                                 ::(views1 loc from))
                              (View.join
                                 (View.unwrap releasedm_src)
                                 (TView.rel (TView.write_tview (Local.tview lc1_src) sc1_src loc to ord_src) loc))).
        { eapply joined_view_join.
          - inv RELM_JOINED; ss; [|econs]. eapply joined_view_incl; eauto.
            i. ss. des; auto.
          - eapply joined_view_exact. ss. auto. }
        unfold views2. condtac; ss; des; ss.

        eapply joined_view_join.
        { ss. econs.
          { eapply View.singleton_ur_wf. }
          unfold views. econs.
          { setoid_rewrite IdentFun.add_spec_eq.
            inv TVIEW_WF. condtac.
            - apply View.join_wf; auto. apply View.singleton_ur_wf.
            - apply View.join_wf; auto. apply View.singleton_ur_wf. }
          auto.
        }



        eapply joined_view_sub; eauto.
        { ss. econs.
          { eapply View.singleton_ur_wf. }
          unfold views. econs.
          { setoid_rewrite IdentFun.add_spec_eq.
            inv TVIEW_WF. condtac.
            - apply View.join_wf; auto. apply View.singleton_ur_wf.
            - apply View.join_wf; auto. apply View.singleton_ur_wf. }
          auto.
        }
        { ii. exists vw0. splits; auto; try by refl.
          ss. des; subst; try by (eapply joined_view_exact; ss; auto).
          -


          eapply joined_view_exact; auto

          eapply

          destruct IN.
          - admit.
          - eapply joined_view_exact; auto.

          unfold views.

          ss; des; auto.

          - admit.
          -

                                    ss. des; eauto.
          - subst. right. exists (View.singleton_ur loc to). splits; auto.
            + apply View.singleton_ur_spec.
              * apply View.singleton_ur_wf.
              * ss. unfold TimeMap.singleton.
                setoid_rewrite LocFun.add_spec_eq. left. auto.
            + etrans; [|eapply View.join_r].
              setoid_rewrite LocFun.add_spec_eq. condtac.
              * eapply View.join_r.
              * eapply View.join_r.
          - subst. right. exists ((write_tview).(TView.rel) loc). splits; auto.
            + unfold write_tview, TView.write_tview. ss.
              setoid_rewrite LocFun.add_spec_eq. condtac.
              * etrans; [|eapply View.join_l].
                inv TVIEW_WF. auto.
              * etrans; [|eapply View.join_l]. refl.
            + etrans; [|eapply View.join_r]. refl. }
      }

      assert (NOATTACH: forall ts msg
                               (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
      { i. exploit sim_memory_get_inv; try exact GET; eauto.
        { apply MEM1_SRC. }
        { apply MEM1_TGT. }
        i. des. inv FROM; cycle 1.
        { inv H. eauto. }
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
      { econs; eauto. }
      intros [mem2_src MEM_SRC].
      hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val released_src)); eauto.
      intros [prom2_src' PROMISES_SRC'].
      hexploit (@Memory.remove_exists prom2_src' loc from to (Message.concrete val released_src)).
      { eapply Memory.add_get0. eauto. }
      intros [prom2_src PROMISES_SRC].

      hexploit MemoryMerge.MemoryMerge.add_remove; try apply PROMISES_SRC; eauto.
      hexploit MemoryMerge.MemoryMerge.add_remove; try apply REMOVE; eauto.
      i. ss. subst.

      hexploit TViewFacts.op_closed_tview; try apply SC1_SRC; eauto.
      instantiate (1:=ord_src). intros RELEASED_CLOSED.

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.add_o in GET; eauto. unfold views2.
          clear - COMPLETE ONLY CLOSED GET JOINEDVIEW NOATTACH.
          des_ifs; ss; try by (des; clarify).
          + des; clarify. splits; auto. rewrite H0 in *. inv JOINEDVIEW.
            unfold views2 in JOINED. des_ifs; des; ss.
          + des; clarify. splits; auto. rewrite H0 in *. inv JOINEDVIEW.
            unfold views2 in JOINED. des_ifs; des; ss.
          + des; clarify. exfalso. eauto.
          + eapply COMPLETE; eauto.
        - i. erewrite Memory.add_o; eauto. unfold views2 in *.
          clear - COMPLETE ONLY CLOSED SOME JOINEDVIEW NOATTACH.
          des_ifs; ss; try by (des; clarify); eauto.
        - i. unfold views2.
          clear - CLOSED MEM_SRC RELEASED_CLOSED. des_ifs.
          + ss. des; subst. unfold views. econs.
            * inv RELEASED_CLOSED. ss.
            * eapply List.Forall_impl; try apply CLOSED. ss.
              i. eapply Memory.add_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED. ss.
            i. eapply Memory.add_closed_view; eauto.
      }

      exists views2. esplits.
      - econs; eauto.
        + inv LOCAL1. inv TVIEW. eapply TViewFacts.writable_mon; eauto.
        + econs; eauto. econs; eauto.
          eapply sim_message_to; eauto.
        + i. eapply sim_local_nonsynch_loc; eauto.
      - inv LOCAL1. econs.
        + inv WF1_TGT. eapply TViewFacts.write_tview_mon; eauto.
        + ii. unfold views2.
          condtac; auto. ss. des. subst.
          eapply Memory.remove_get0 in PROMISES_SRC.
          eapply Memory.remove_get0 in REMOVE. des.
          rewrite GET0. rewrite GET2. econs.
        + unfold views2. ii. condtac; auto.
          * ss. des; subst. auto.
          * ss. destruct (Loc.eq_dec loc0 loc).
            { subst. des; ss.
              admit. }
            {




          ss.






          erewrite Memory.remove_get0; eauto.

          des_ifs.


                                                           REMOVE

          Memory.remove

          erewrite (@Memory.add_o prom2_src); eauto. erewrite (@Memory.add_o promises2); eauto.


        econ

          s; eauto.


          admit


          + eauto.
          + exploit ONLY; eauto.

          + des; clarify. splits; auto. rewrite H0 in *. inv JOINEDVIEW.
            unfold views2 in JOINED. des_ifs; des; ss.
          + des; clarify. splits; auto. rewrite H0 in *. inv JOINEDVIEW.
            unfold views2 in JOINED. des_ifs; des; ss.
          + des; clarify. exfalso. eauto.
          + eapply COMPLETE; eauto.


            splits; auto. rewrite H0 in *. inv JOINEDVIEW.
            unfold views2 in JOINED. des_ifs; des; ss.
          + ss. des; clarify. splits; auto.

            unfold released
            admit.
          +

                                            ; ss; des; clarify.


          clear ATTACH DISJOINT MSG_WF
                COMPLETE ONLY CLOSED
                PROMISES0 MEM REMOVE TS JOINEDVIEW
                WF_RELEASED RELM_JOINED PROMISES_SRC PROMISES_SRC'
                RELEASE MEM_SRC PROMISES FINITE TVIEW_CLOSED
                loc
          . des_ifs.

          condtac. condtac.

          destruct (loc_ts_eq_dec (loc0, ts) (@pair Loc.t Time.t loc to)); condtac.
          + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
          + ss. des; clarify. splits; auto.
            inv MAX. inv MAXLE. auto.
          + ss. des; clarify. exfalso. eauto.
          + eapply COMPLETE; eauto.
          +



          ss. destruct (loc_ts_eq_dec (loc0, ts) (loc, to)). ss.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)). ; condtac.
          des_ifs. condtac.
          des_ifs.

          des_if.
          condtac.

          + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
          + ss. des; clarify. splits; auto.
            inv MAX. inv MAXLE. auto.
          + ss. des; clarify. exfalso. eauto.
          + eapply COMPLETE; eauto.
        - unfold views2. i. des_ifs.
          + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
          + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
        - unfold views2. ii. des_ifs.
          + ss. des; clarify. unfold views. econs.
            { inv WF1_SRC. inv TVIEW_CLOSED.
              eapply Memory.add_closed_view; eauto. }
            eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.add_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.add_closed_view; eauto. }

        esplits.
        { econs.
          - econs; eauto.
            eapply sim_message_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - econs. eapply joined_opt_view_closed; eauto.
            + instantiate (1:=to). instantiate (1:=loc).
              eapply max_le_joined_opt_view_joined; eauto.
              unfold views2. des_ifs; ss; des; clarify. eauto.
            + inv MEM1_SRC. eapply Memory.add_inhabited; eauto.
            + eapply Memory.add_get0; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. unfold views2.
            erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto. ss.
          - ss. ii. unfold views2.
            erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
            ss. des; clarify. auto. }
        { eapply sim_memory_add; cycle 1; eauto. econs.
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. }
      }
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.reserve); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to Message.reserve); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.reserve, views1.

        esplits.
        { econs.
          - econs; eauto. i. clarify.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
          - ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
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
      }
    }


      exists views2. esplits.




              unfold write_tview, TView.write_tview. ss.

              eapply View.join_l


              des_

                apply TimeMap.singleton_spec.

            + c
            unfold TView.write_tview. ss.
            setoid_rewrite (IdentFun.add_spec_eq loc). condtac.
            + Local.write_step


      destruct msg_tgt as [val released_tgt|].
      { assert (NOATTACH: forall ts msg
                                 (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
        { i. exploit sim_memory_get_inv; try exact GET; eauto.
          { apply MEM1_SRC. }
          { apply MEM1_TGT. }
          i. des. inv FROM; cycle 1.
          { inv H. eauto. }
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

        set (views :=(lc1_src.(Local.tview).(TView.rel) loc)
                       ::(views1 loc from)).
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs.
          { inv WF1_SRC. inv TVIEW_WF. ss. }
          eauto.
        }
        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then views
                                  else views1 l t).

        hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::views) released_tgt).
        { econs; auto. eapply View.singleton_ur_wf. } i. des.

        hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val max)); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        { econs; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists (Message.concrete val max), views2.

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits; auto.
              inv MAX. inv MAXLE. auto.
            + ss. des; clarify. exfalso. eauto.
            + eapply COMPLETE; eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
            + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
          - unfold views2. ii. des_ifs.
            + ss. des; clarify. unfold views. econs.
              { inv WF1_SRC. inv TVIEW_CLOSED.
                eapply Memory.add_closed_view; eauto. }
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto. }

        esplits.
        { econs.
          - econs; eauto.
            eapply sim_message_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - econs. eapply joined_opt_view_closed; eauto.
            + instantiate (1:=to). instantiate (1:=loc).
              eapply max_le_joined_opt_view_joined; eauto.
              unfold views2. des_ifs; ss; des; clarify. eauto.
            + inv MEM1_SRC. eapply Memory.add_inhabited; eauto.
            + eapply Memory.add_get0; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. unfold views2.
            erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto. ss.
          - ss. ii. unfold views2.
            erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
            ss. des; clarify. auto. }
        { eapply sim_memory_add; cycle 1; eauto. econs.
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. }
      }
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.reserve); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to Message.reserve); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.reserve, views1.

        esplits.
        { econs.
          - econs; eauto. i. clarify.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
          - ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
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
      }
    }

    { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des. subst.

      set (views :=(lc1_src.(Local.tview).(TView.rel) loc)
                     ::(views1 loc from)).
      assert (VIEWSWF: List.Forall View.wf views).
      { unfold views. econs.
        { inv WF1_SRC. inv TVIEW_WF. ss. }
        eauto.
      }
      set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                then views
                                else views1 l t).
      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::views) released').
      { econs; auto. eapply View.singleton_ur_wf. } i. des.

      assert (exists msg3_src,
                 (<<GETSRC: Memory.get loc ts3 lc1_src.(Local.promises) = Some (from, msg3_src)>>) /\
                 (<<GETMEMSRC: Memory.get loc ts3 mem1_src = Some (from, msg3_src)>>) /\
                 (<<SIMMSG: sim_message msg3_src msg3>>)).
      { inv LOCAL1. inv WF1_SRC. dup PROMISES0. ss.
        specialize (PROMISES2 loc ts3). erewrite GET2 in *. inv PROMISES2.
        - esplits; eauto. inv WF1_TGT. exploit sim_memory_get; eauto.
          { i. des. symmetry in H0. apply PROMISES1 in H0. clarify. }
        - esplits; eauto. } des.

      hexploit (@Memory.split_exists lc1_src.(Local.promises) loc from to ts3 (Message.concrete val' max) msg3_src); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.split_exists_le lc1_src.(Local.promises) mem1_src loc from to ts3 (Message.concrete val' max) msg3_src); eauto.
      { inv WF1_SRC. auto. }
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.split_o in GET; eauto. unfold views2. des_ifs.
          + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
          + ss. des; clarify. splits.
            * inv MAX. eapply max_le_joined_view_joined; eauto.
            * ii. auto.
          + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
            i. des; auto. subst. inv LOCAL1. hexploit PROMISES0; eauto.
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
          des_ifs; eauto. ss. des; clarify.
          hexploit (ONLY loc ts3); eauto. i. des. clarify. eauto.
        - unfold views2. i. des_ifs.
          + ss. des; clarify. unfold views. econs.
            * eapply Memory.split_closed_view; eauto.
              inv WF1_SRC. inv TVIEW_CLOSED. auto.
            * eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.split_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.split_closed_view; eauto.
      }

      exists (Message.concrete val' max), views2. esplits.
      { econs.
        - econs 2; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            unfold views2. des_ifs; ss; des; clarify.
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.split_inhabited; eauto.
          + eapply Memory.split_get0 in MEM_SRC. des; eauto.
        - ss.
      }
      { inv LOCAL1. econs; eauto.
        - ii. erewrite (@Memory.split_o prom2_src); eauto.
          erewrite (@Memory.split_o promises2); eauto. unfold views2. des_ifs.
          + ss. des; clarify. econs; eauto. ss.
          + ss. des; clarify.
            specialize (PROMISES0 loc ts3).
            rewrite GETSRC in *. erewrite GET2 in *.
            inv PROMISES0; eauto.
        - ss. ii. erewrite (@Memory.split_o prom2_src) in *; eauto. unfold views2.
          des_ifs; eauto.
          + ss. des; clarify. auto.
          + ss. des; clarify. eapply REL; eauto. }
      { eapply sim_memory_split; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { ii. unfold views2. des_ifs. }
    }

    { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
      subst. inv MSG_LE.
      inv LOCAL1. dup PROMISES0. ss.
      specialize (PROMISES1 loc to). erewrite GET in *. inv PROMISES1.

      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::(views1 loc to)) released0).
      { econs; auto. eapply View.singleton_ur_wf. } i. des.
      (* hexploit max_le_joined_opt_view_le; eauto. intros SIMMSG. *)

      assert (RELEASEDLE: View.opt_le max released_src).
      { eapply max_le_joined_opt_view_le_le; eauto. }
      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val max)); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.lower_exists_le prom_src mem1_src loc from to (Message.concrete val released_src) (Message.concrete val max)); eauto.
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
        - econs 3; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.lower_inhabited; eauto.
          + eapply Memory.lower_get0; eauto.
        - ss.
      }
      { econs; eauto.
        - ii. erewrite (@Memory.lower_o prom2_src); eauto.
          erewrite (@Memory.lower_o promises2); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
        - ss. ii. erewrite (@Memory.lower_o prom2_src) in *; eauto. des_ifs; eauto.
          ss. des; clarify. inv RELEASEDLE. eapply REL; eauto. }
      { eapply sim_memory_lower; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { auto. }
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
        - ss. ii. erewrite (@Memory.remove_o prom2_src) in *; eauto. des_ifs; eauto. }
      { eapply sim_memory_remove; cycle 1; eauto. }
      { assumption. }
      { auto. }
    }



        views1
        lc1_src mem1_src
        lc1_tgt mem1_tgt
        lc2_tgt mem2_tgt
        loc from to msg_tgt kind_tgt
        (STEP_TGT: Local.write_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt)
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
      exists msg_src views2 kind_src lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
        (<<LOCAL2: sim_local views2 lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<JOINMEM2: joined_memory views2 mem2_src>>) /\
        (<<WFVIEWS2: wf_views views2>>)
  .
  Proof.
    inv STEP_TGT. inv PROMISE.
    { hexploit add_succeed_wf; try apply MEM; eauto. i. des.

      destruct msg_tgt as [val released_tgt|].
      { assert (NOATTACH: forall ts msg
                                 (GET: Memory.get loc ts mem1_src = Some (to, msg)), False).
        { i. exploit sim_memory_get_inv; try exact GET; eauto.
          { apply MEM1_SRC. }
          { apply MEM1_TGT. }
          i. des. inv FROM; cycle 1.
          { inv H. eauto. }
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

        set (views :=(lc1_src.(Local.tview).(TView.rel) loc)
                       ::(views1 loc from)).
        assert (VIEWSWF: List.Forall View.wf views).
        { unfold views. econs.
          { inv WF1_SRC. inv TVIEW_WF. ss. }
          eauto.
        }
        set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                  then views
                                  else views1 l t).
        hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::views) released_tgt).
        { econs; auto. eapply View.singleton_ur_wf. } i. des.

        hexploit (@Memory.add_exists mem1_src loc from to (Message.concrete val max)); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        { econs; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to (Message.concrete val max)); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists (Message.concrete val max), views2.

        assert (JOINMEM2: joined_memory views2 mem2_src).
        { inv JOINMEM1. econs.
          - i. erewrite Memory.add_o in GET; eauto. unfold views2. des_ifs.
            + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
            + ss. des; clarify. splits; auto.
              inv MAX. inv MAXLE. auto.
            + ss. des; clarify. exfalso. eauto.
            + eapply COMPLETE; eauto.
          - unfold views2. i. des_ifs.
            + ss. des; clarify. esplits. eapply Memory.add_get0; eauto.
            + guardH o. exploit ONLY; eauto. i. des. erewrite Memory.add_get1; eauto.
          - unfold views2. ii. des_ifs.
            + ss. des; clarify. unfold views. econs.
              { inv WF1_SRC. inv TVIEW_CLOSED.
                eapply Memory.add_closed_view; eauto. }
              eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto.
            + eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.add_closed_view; eauto. }

        esplits.
        { econs.
          - econs; eauto.
            eapply sim_message_to; eauto.
            eapply max_le_joined_message_le. econs; eauto.
          - econs. eapply joined_opt_view_closed; eauto.
            + instantiate (1:=to). instantiate (1:=loc).
              eapply max_le_joined_opt_view_joined; eauto.
              unfold views2. des_ifs; ss; des; clarify. eauto.
            + inv MEM1_SRC. eapply Memory.add_inhabited; eauto.
            + eapply Memory.add_get0; eauto.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. unfold views2.
            erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
            ss. des; clarify. econs; eauto. ss.
          - ss. ii. unfold views2.
            erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
            ss. des; clarify. auto. }
        { eapply sim_memory_add; cycle 1; eauto. econs.
          eapply max_le_joined_opt_view_le; eauto. }
        { assumption. }
        { ii. unfold views2. des_ifs. }
      }
      {
        hexploit (@Memory.add_exists mem1_src loc from to Message.reserve); auto.
        { ii. inv MEM1. hexploit (proj1 (COVER loc x)).
          - econs; eauto.
          - i. inv H. eapply DISJOINT; eauto. }
        intros [mem2_src MEM_SRC].
        hexploit (@Memory.add_exists_le lc1_src.(Local.promises) mem1_src loc from to Message.reserve); eauto.
        { inv WF1_SRC. auto. }
        intros [prom2_src PROMISES_SRC].
        exists Message.reserve, views1.

        esplits.
        { econs.
          - econs; eauto. i. clarify.
          - econs.
          - ss.
        }
        { inv LOCAL1. econs; eauto.
          - ii. erewrite (@Memory.add_o prom2_src); eauto.
            erewrite (@Memory.add_o promises2); eauto. des_ifs.
          - ss. ii. erewrite (@Memory.add_o prom2_src) in *; eauto. des_ifs; eauto.
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
      }
    }

    { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des. subst.

      set (views :=(lc1_src.(Local.tview).(TView.rel) loc)
                     ::(views1 loc from)).
      assert (VIEWSWF: List.Forall View.wf views).
      { unfold views. econs.
        { inv WF1_SRC. inv TVIEW_WF. ss. }
        eauto.
      }
      set (views2 := fun l t => if (loc_ts_eq_dec (l, t) (loc, to))
                                then views
                                else views1 l t).
      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::views) released').
      { econs; auto. eapply View.singleton_ur_wf. } i. des.

      assert (exists msg3_src,
                 (<<GETSRC: Memory.get loc ts3 lc1_src.(Local.promises) = Some (from, msg3_src)>>) /\
                 (<<GETMEMSRC: Memory.get loc ts3 mem1_src = Some (from, msg3_src)>>) /\
                 (<<SIMMSG: sim_message msg3_src msg3>>)).
      { inv LOCAL1. inv WF1_SRC. dup PROMISES0. ss.
        specialize (PROMISES2 loc ts3). erewrite GET2 in *. inv PROMISES2.
        - esplits; eauto. inv WF1_TGT. exploit sim_memory_get; eauto.
          { i. des. symmetry in H0. apply PROMISES1 in H0. clarify. }
        - esplits; eauto. } des.

      hexploit (@Memory.split_exists lc1_src.(Local.promises) loc from to ts3 (Message.concrete val' max) msg3_src); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.split_exists_le lc1_src.(Local.promises) mem1_src loc from to ts3 (Message.concrete val' max) msg3_src); eauto.
      { inv WF1_SRC. auto. }
      intros [mem2_src MEM_SRC].

      assert (JOINMEM2: joined_memory views2 mem2_src).
      { inv JOINMEM1. econs.
        - i. erewrite Memory.split_o in GET; eauto. unfold views2. des_ifs.
          + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
          + ss. des; clarify. splits.
            * inv MAX. eapply max_le_joined_view_joined; eauto.
            * ii. auto.
          + ss. des; clarify. exploit COMPLETE; eauto. i. des. splits; auto.
            i. des; auto. subst. inv LOCAL1. hexploit PROMISES0; eauto.
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
          des_ifs; eauto. ss. des; clarify.
          hexploit (ONLY loc ts3); eauto. i. des. clarify. eauto.
        - unfold views2. i. des_ifs.
          + ss. des; clarify. unfold views. econs.
            * eapply Memory.split_closed_view; eauto.
              inv WF1_SRC. inv TVIEW_CLOSED. auto.
            * eapply List.Forall_impl; try apply CLOSED0. ss.
              i. eapply Memory.split_closed_view; eauto.
          + eapply List.Forall_impl; try apply CLOSED0. ss.
            i. eapply Memory.split_closed_view; eauto.
      }

      exists (Message.concrete val' max), views2. esplits.
      { econs.
        - econs 2; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            unfold views2. des_ifs; ss; des; clarify.
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.split_inhabited; eauto.
          + eapply Memory.split_get0 in MEM_SRC. des; eauto.
        - ss.
      }
      { inv LOCAL1. econs; eauto.
        - ii. erewrite (@Memory.split_o prom2_src); eauto.
          erewrite (@Memory.split_o promises2); eauto. unfold views2. des_ifs.
          + ss. des; clarify. econs; eauto. ss.
          + ss. des; clarify.
            specialize (PROMISES0 loc ts3).
            rewrite GETSRC in *. erewrite GET2 in *.
            inv PROMISES0; eauto.
        - ss. ii. erewrite (@Memory.split_o prom2_src) in *; eauto. unfold views2.
          des_ifs; eauto.
          + ss. des; clarify. auto.
          + ss. des; clarify. eapply REL; eauto. }
      { eapply sim_memory_split; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { ii. unfold views2. des_ifs. }
    }

    { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
      subst. inv MSG_LE.
      inv LOCAL1. dup PROMISES0. ss.
      specialize (PROMISES1 loc to). erewrite GET in *. inv PROMISES1.

      hexploit (@max_le_joined_opt_view_exists ((View.singleton_ur loc to)::(views1 loc to)) released0).
      { econs; auto. eapply View.singleton_ur_wf. } i. des.
      (* hexploit max_le_joined_opt_view_le; eauto. intros SIMMSG. *)

      assert (RELEASEDLE: View.opt_le max released_src).
      { eapply max_le_joined_opt_view_le_le; eauto. }
      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val max)); auto.
      { econs. auto. }
      intros [prom2_src PROMISES_SRC].
      hexploit (@Memory.lower_exists_le prom_src mem1_src loc from to (Message.concrete val released_src) (Message.concrete val max)); eauto.
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
        - econs 3; eauto.
          eapply sim_message_to; eauto.
          eapply max_le_joined_message_le. econs; eauto.
        - econs. eapply joined_opt_view_closed; eauto.
          + instantiate (1:=to). instantiate (1:=loc).
            eapply max_le_joined_opt_view_joined; eauto.
          + inv MEM1_SRC. eapply Memory.lower_inhabited; eauto.
          + eapply Memory.lower_get0; eauto.
        - ss.
      }
      { econs; eauto.
        - ii. erewrite (@Memory.lower_o prom2_src); eauto.
          erewrite (@Memory.lower_o promises2); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
        - ss. ii. erewrite (@Memory.lower_o prom2_src) in *; eauto. des_ifs; eauto.
          ss. des; clarify. inv RELEASEDLE. eapply REL; eauto. }
      { eapply sim_memory_lower; cycle 1; eauto. econs.
        eapply max_le_joined_opt_view_le; eauto. }
      { assumption. }
      { auto. }
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
        - ss. ii. erewrite (@Memory.remove_o prom2_src) in *; eauto. des_ifs; eauto. }
      { eapply sim_memory_remove; cycle 1; eauto. }
      { assumption. }
      { auto. }
    }
  Qed.
