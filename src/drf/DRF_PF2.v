Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.

Require Import PF.
Require Import Race.
Require Import SimWhole.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Require Import DRF_PF.

Set Implicit Arguments.

Lemma step_lifting_raw
      lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt others updates otherspace

      (STEP: (@pred_step
                ((fun _ => True)
                   /1\ (write_not_in otherspace)
                   /1\ (no_update_on updates)
                   /1\ (no_read_msgs others)
                   /1\ (write_not_in others)
                   /1\ (no_read_msgs prom.(promised))) lang) e_tgt th_tgt th_tgt')

      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
      (NOATTATCH: not_attatched updates mem_src)

      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\
      (<<MEM: pf_sim_memory (others \2/ promised prom') mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates mem_src'>>) /\
      (<<UNCHANGED: unchanged_on otherspace mem_src mem_src'>>).
Proof.
  hexploit (forget_exists prom.(promised) mem_tgt); eauto. i. des.

  exploit self_promise_remove; try apply FORGET; eauto.
  i. des.

  inv MEM.
  assert (FORGET1: forget_memory others mem_inter mem_src0).
  { eapply forget_compose_middle; eauto. }

  inv STEP0.
  { exists mem_src, ThreadEvent.silent. esplits; eauto.
    - econs; eauto. eapply forget_compose; eauto.
    - refl. }

  exploit other_promise_remove; try eapply STEP1; eauto.
  i. des.

  exploit shorter_memory_step; try apply STEP0; eauto.
  i. des.

  exploit no_update_on_step; try apply STEP2; eauto.
  { refl. }
  i. des.

  exists mem_src'2, e_src0. esplits.
  - econs 2. eapply pred_step_mon; cycle 1; eauto.
    ss. i. des. eauto.
  - etrans; eauto.
  - econs.
    + eapply forget_compose; eauto.
    + etrans; eauto.
  - eauto.
  - exploit write_not_in_unchanged_on; try apply STEP3; eauto.
Qed.

Lemma step_lifting
      lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt others updates otherspace

      (STEP: (@pred_step
                ((fun _ => True)
                   /1\ (no_update_on updates)
                   /1\ (no_read_msgs others)) lang) e_tgt th_tgt th_tgt')

      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
      (NOATTATCH: not_attatched updates mem_src)

      (CONSISTENT: promise_consistent (Local.mk v' prom'))
      (OTHERSPACE: others \2/ otherspace <2= unchangables mem_tgt prom)

      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>>) /\
      (<<MEM: pf_sim_memory (others \2/ promised prom') mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates mem_src'>>) /\
      (<<UNCHANGED: unchanged_on otherspace mem_src mem_src'>>).
Proof.
  eapply step_lifting_raw; ss; eauto.
  dup STEP. inv STEP. econs; auto. inv STEP1. des.
  exploit step_wirte_not_in; eauto. ss. i.
  splits; eauto.
  - eapply write_not_in_mon; eauto.
  - eapply write_not_in_mon; eauto.
  - eapply consistent_read_no_self_promise; eauto.
Qed.



Lemma step_lifting_rtc
      lang others otherspace updates th_src th_tgt th_tgt'

      (STEP: rtc (tau (@pred_step
                         ((fun _ => True)
                            /1\ (no_update_on updates)
                            /1\ (no_read_msgs others)) lang)) th_tgt th_tgt')

      (FORGET: forget_thread others th_src th_tgt)

      (NOATTATCH: not_attatched updates th_src.(Thread.memory))
      (THWF: thread_wf th_tgt)
      (CONSISTENT: promise_consistent th_tgt'.(Thread.local))
      (OTHERSPACE: others \2/ otherspace <2= unchangables th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
  :
    exists th_src',
      (<<STEP: rtc (tau (@pred_step (no_promise) lang))
                   th_src th_src'>>) /\
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates th_src'.(Thread.memory)>>) /\
      (<<UNCHANGED: unchanged_on otherspace th_src.(Thread.memory) th_src'.(Thread.memory)>>).
Proof.
  revert th_src FORGET NOATTATCH THWF OTHERSPACE.
  induction STEP.
  - i. esplits; eauto. refl.
  - i. inv H. destruct y. destruct local. ss.
    dup TSTEP. inv TSTEP. inv STEP0.

    inv THWF.
    exploit Thread.step_future; eauto.
    ss. i. des.

    hexploit rtc_tau_step_promise_consistent.
    { eapply thread_steps_pred_steps; try apply STEP; eauto. }
    { eauto. }
    { ss. }
    { eauto. }
    { eauto. }
    i. ss.

    inv FORGET. ss.
    ss. exploit step_lifting; eauto.
    i. des.

    exploit IHSTEP; eauto; ss.
    { econs; eauto. }
    { ss. }
    { i. exploit unchangables_increase.
      - eapply STEP1.
      - eauto.
      - ss. }
    i. des. ss.

    exists th_src'. inv STEP0.
    { esplits; eauto. }
    { esplits; eauto.
      - eapply Relation_Operators.rt1n_trans; eauto.
        econs; eauto. etrans; eauto.
      - etrans; eauto. }
Qed.


Lemma updates_list_exists
      P lang th0 th1
      (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1)
  :
    exists (updates: Loc.t -> Prop),
      (<<COMPLETE:
         rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc)
                                 /1\ no_promise) lang)) th0 th1>>) /\
      (<<SOUND:
         forall loc (SAT: updates loc),
         exists th' th'' to valr valw releasedr releasedw ordr ordw,
           (<<STEPS: rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc)
                                             /1\ no_promise) lang)) th0 th'>>) /\
           (<<STEP: (@pred_step (P /1\ no_promise) lang)
                      (ThreadEvent.update loc (Memory.max_ts loc th0.(Thread.memory)) to valr valw releasedr releasedw ordr ordw)
                      th' th''>>)>>)
.
Proof.
  eapply Operators_Properties.clos_rt_rt1n_iff in STEPS.
  eapply Operators_Properties.clos_rt_rtn1_iff in STEPS.
  induction STEPS.
  - exists (fun _ => False). esplits; eauto. i. clarify.
  - des. inv H.
    destruct (classic (no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc) e)).
    + exists updates. esplits; eauto.
      eapply rtc_n1; eauto. econs; eauto. inv TSTEP. econs; eauto. des. esplits; eauto.
    + unfold no_update_on in H. des_ifs. apply NNPP in H.
      exists (fun l => l = loc \/ updates l).
      esplits; eauto.
      * eapply rtc_n1.
        { eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
        { econs; eauto. inv TSTEP. econs; eauto.
          des. esplits; eauto. ss. ii. des. eauto. }
      * i. des.
        { clarify. exists y, z. esplits; eauto.
          eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
        { exploit SOUND; eauto. i. des.
          exists th', th''. esplits; eauto.
          eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
Qed.


(* Lemma updates_list_exists *)
(*       P lang th0 th1 *)
(*       (BOT: th0.(Thread.local).(Local.promises) = Memory.bot) *)
(*       (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1) *)
(*   : *)
(*     exists (updates: Loc.t -> Time.t -> Prop), *)
(*       (<<COMPLETE: *)
(*          rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                  /1\ no_promise) lang)) th0 th1>>) /\ *)
(*       (<<SOUND: *)
(*          forall loc ts (SAT: updates loc ts), *)
(*          exists th' th'' to valr valw releasedr releasedw ordr ordw, *)
(*            (<<STEPS: rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                              /1\ no_promise) lang)) th0 th'>>) /\ *)
(*            (<<STEP: (@pred_step (P /1\ no_promise) lang) *)
(*                       (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw) *)
(*                       th' th''>>)>>) /\ *)

(*       (<<NOATTATCHED: not_attatched updates th0.(Thread.memory)>>) *)
(* . *)
(* Proof. *)
(*   eapply Operators_Properties.clos_rt_rt1n_iff in STEPS. *)
(*   eapply Operators_Properties.clos_rt_rtn1_iff in STEPS. *)
(*   induction STEPS. *)
(*   - exists (fun _ _ => False). esplits; eauto. *)
(*     + i. clarify. *)
(*     + ii. clarify. *)
(*   - des. inv H. *)
(*     destruct (classic (no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) e)). *)
(*     + exists updates. esplits; eauto. *)
(*       eapply rtc_n1; eauto. econs; eauto. inv TSTEP. econs; eauto. des. esplits; eauto. *)
(*     + unfold no_update_on in H. des_ifs. apply NNPP in H. *)
(*       exists (fun l t => (l = loc /\ t = tsr) \/ updates l t). *)
(*       esplits; eauto. *)

(*       * eapply rtc_n1. *)
(*         { eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*         { econs; eauto. inv TSTEP. econs; eauto. *)
(*           des. esplits; eauto. ss. ii. des. eauto. } *)
(*       * i. des. *)
(*         { clarify. exists y, z. esplits; eauto. *)
(*           eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*         { exploit SOUND; eauto. i. des. *)
(*           exists th', th''. esplits; eauto. *)
(*           eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*       * eapply not_attatched_sum; eauto. *)
(*         eapply attatched_preserve_rtc; try apply COMPLETE; eauto. *)
(*         { eapply update_not_attatched; eauto. *)
(*           eapply promise_bot_no_promise_rtc; try apply COMPLETE; eauto. } *)
(*         { i. des. clarify. } *)
(* Qed. *)



Inductive shifted_map mlast mcert
          (updates: Loc.t -> Prop)
          (sky gap: TimeMap.t)
          (f: Loc.t -> Time.t -> Time.t): Prop :=
| shifted_map_intro
    (PRSV: map_preserving (times_in_memory mcert) f)
    (SAME: forall l t (TLE: Time.le t (Memory.max_ts l mlast)),
        f l t = t)
    (INGAP: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (f l t) (gap l))
    (AFTERSKY: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (sky l) (f l t))
.

Lemma shifted_map_exists mlast mcert updates
      (MLE: Memory.le mlast mcert)
      (sky gap: TimeMap.t)
      (SKY: forall l, Time.lt (Memory.max_ts l mlast) (sky l))
      (GAP: forall l, Time.lt (Memory.max_ts l mlast) (gap l))
  :
    exists f, (<<SHIFTED: shifted_map mlast mcert updates sky gap f>>).
Proof.
  (* may be very hard... *)
Admitted.

Lemma shifted_map_preserving_last_mem  mlast mcert updates sky gap f
      (CLOSED: Memory.closed mlast)
      (SHIFTED: shifted_map mlast mcert updates sky gap f)
  :
    memory_map f mlast mlast.
Proof.
  inv SHIFTED. inv PRSV. econs; i.
  - exploit Memory.max_ts_spec; eauto. i. des.
    repeat erewrite SAME; eauto.
    + rewrite GET. unfold msg_map. des_ifs. repeat f_equal.
      inv CLOSED. exploit CLOSED0; try apply GET; eauto. i. des.
      inv MSG_CLOSED. inv CLOSED; ss. f_equal.
      destruct view. inv CLOSED1. unfold view_map, timemap_map. ss. f_equal.
      * extensionality l. erewrite SAME; auto.
        specialize (PLN l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
      * extensionality l. erewrite SAME; auto.
        specialize (RLX l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
    + exploit Memory.get_ts; try apply GET; eauto. i. des.
      * clarify.
      * left. eapply TimeFacts.lt_le_lt; eauto.
  - destruct msg_src as [from msg]. exploit Memory.max_ts_spec; eauto. i. des.
    esplits.
    + erewrite SAME; eauto.
    + eauto.
Qed.

Definition cap (m mcap: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  (<<NINMEM: ~ promised m l t>>) /\ (<<INCAPPED: promised mcap l t>>).

Definition no_acq_read_msgs (MSGS : Loc.t -> Time.t -> Prop)
           (e : ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.read loc to _ _ ordr => ~ (MSGS loc to) \/ Ordering.le ordr Ordering.relaxed
  | ThreadEvent.update loc from _ _ _ _ _ ordr _ => ~ (MSGS loc from) \/ Ordering.le ordr Ordering.relaxed
  | _ => True
  end.

Lemma consistent_no_sc_no_acq lang (th: Thread.t lang)
      (CONSISTENT: Thread.consistent th)
      mem1 sc1
      (CAP: Memory.cap th.(Thread.local).(Local.promises) th.(Thread.memory) mem1)
      (SC_MAX: Memory.max_full_timemap mem1 sc1)
  :
    exists th',
      (<<STEPS: rtc (tau (@pred_step (no_sc /1\ no_acq_read_msgs (cap th.(Thread.memory) mem1)) lang)) th th'>>) /\
      (<<CONSISTENT: promise_consistent th'.(Thread.local)>>) /\
      (<<PROMISES: forall l t (PROM: promised th.(Thread.local).(Local.promises) l t),
          ~ promised th'.(Thread.local).(Local.promises) l t>>).
Proof.
Admitted.

Lemma consistent_no_sc_no_acq lang (th: Thread.t lang)
      (CONSISTENT: Thread.consistent th)
      mem1 sc1
      (CAP: Memory.cap th.(Thread.local).(Local.promises) th.(Thread.memory) mem1)
      (SC_MAX: Memory.max_full_timemap mem1 sc1)
  :
    exists th',
      (<<STEPS: rtc (tau (@pred_step (no_sc /1\ no_acq_read_msgs (cap th.(Thread.memory) mem1)) lang)) th th'>>) /\
      (<<CONSISTENT: promise_consistent th'.(Thread.local)>>) /\
      (<<PROMISES: forall l t (PROM: promised th.(Thread.local).(Local.promises) l t),
          ~ promised th'.(Thread.local).(Local.promises) l t>>).
Proof.
Admitted.




Lemma future_lifting
      P lang th0 th1
      (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1)
  :
    exists (updates: Loc.t -> Time.t -> Prop),
      (<<COMPLETE:
         rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts)
                                 /1\ no_promise) lang)) th0 th1>>) /\





(* Lemma inv_monotone st proms sky updates mlast v0 v1 *)
(*       (LE: TimeMap.le v0 v1) *)
(*       (INV: Inv.t st proms sky updates mlast v1) *)
(*   : *)
(*     Inv.t st proms sky updates mlast v0. *)
(* Proof. *)
(*   inv INV. econs; i. *)
(*   - eapply PROMS; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(*   - eapply UPDATE; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(* Qed. *)

(* Lemma inv_hold_self *)
(*       st locked proms sky mem *)
(*       (SKY: TimeMap.le (Memory.max_timemap mem) sky) *)
(*       (PROM: forall l t, covered proms l t -> covered mem l t -> False) *)
(*   : *)
(*     Inv.hold st locked proms sky mem mem *)
(* . *)
(* Proof. *)
(*   ii. econs; i; ss; eauto. *)
(*   revert INV. induction FUTURE; ss; i.     *)
(*   clarify. unfold TimeMap.add in *. ss. *)
(*   des_ifs. *)
(*   - left. eapply TimeFacts.le_lt_lt; cycle 1; eauto. *)
(*     eapply IHFUTURE; ss. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(*   - eapply IHFUTURE; eauto. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(* Qed. *)

(* (* TODO *) *)
(* Lemma consistent_inhabited *)
(*       mlast skylast c_src c_tgt tid *)
(*       (FORGET: forget_config c_src c_tgt) *)
(*       (RACEFREE: pf_racefree c_src) *)
(*       (INHABITED: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.inhabited *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid')) *)
(*       (HOLD: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.hold *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid') c_src.(Configuration.memory)) *)
(*       (CONSISTENT: Thread.consistent *)
(*                      (c_tgt.(Configuration.mpreds) tid) *)
(*                      bot2 *)
(*                      (to_thread *)
(*                         (Threads.find tid c_tgt.(Configuration.threads)) *)
(*                         (c_tgt.(Configuration.sc)) *)
(*                         (c_tgt.(Configuration.memory)))) *)
(*   : *)
(*     Inv.inhabited *)
(*       (Threads.find tid c_src.(Configuration.threads)) *)
(*       (Locked.t (c_tgt.(Configuration.mpreds) tid)) *)
(*       ((Threads.find tid c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*       (Memory.max_timemap c_tgt.(Configuration.memory)) c_src.(Configuration.memory). *)
(* Admitted. *)


(* Definition not_stuck lang (st: Language.state lang) := *)
(*   exists st' e, Language.step _ e st st'. *)

(* Lemma same_add_same ths tid st *)
(*       (FIND: Threads.find tid ths = st) *)
(*       (STEP: not_stuck _ st.(StateLocal.state)) *)
(*   : *)
(*     Threads.add tid st ths = ths. *)
(* Proof. *)
(*   eapply IdentMap.eq_leibniz. ii. *)
(*   unfold Threads.find, Threads.add in *. *)
(*   rewrite IdentMap.Facts.add_o. des_ifs. *)
(*   exfalso. inv STEP. des. inv H. *)
(* Qed. *)

(* Ltac etatac := match goal with *)
(*                  [|- ?x = ?y] => *)
(*                  (try (destruct x; ss; clarify; eauto; fail));              *)
(*                  (try (destruct y; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction x; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction y; ss; clarify; eauto; fail)) *)
(*                end. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)

(*   assert (SIMPF: sim_pf_all *)
(*                    (Configuration.mk *)
(*                       (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                       (th3_src.(Thread.local)))  *)
(*                                    (Configuration.threads c1_src)) *)
(*                       (Configuration.sc c3_tgt) *)
(*                       th3_src.(Thread.memory) MPreds.init) *)
(*                    c3_tgt). *)

(*   { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         admit. *)
(*         (* inv STEPS_SRC0. *) *)
(*         (* econs; [|left]. econs. econs. econs; ss; eauto. *) *)
(*         (* etatac. *) *)
(*       } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)

(*   eapply rtc_tail in STEPS_SRC. des. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)







(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf mlast skylast *)
(*       (SIM: sim_pf c1_src c1_tgt mlast skylast) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf *)
(*                 c3_src c3_tgt *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then c3_src.(Configuration.memory) else skylast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)


(* (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)

(*                          >>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)






(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = to_thread Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)

(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)


(*       Thread.step Thread.t st lc sc mem1  *)

(*       Thread.t *)
(*       Thread.step *)
(* Configuration.step *)

(* opt (Thread.step *)


(* Lemma sim_pf_sim_whole: *)
(*   sim_pf_all <2= (sim_whole (fun _ => pftstep) Configuration.step). *)
(* Proof. *)
(*   pcofix CIH. ii. *)
(*   pfold. econs. *)
(*   - esplits; eauto. *)
(*     inv PR. inv SIM. inv FORGET. *)
(*     ii. specialize (THS tid). inv THS. *)
(*     rewrite FIND in *. ss. econs; eauto. *)
(*     specialize (TERMINAL_TGT tid). *)
(*     destruct (Threads.find tid (Configuration.threads x1)). ss. *)
(*     dependent destruction STATE. eapply TERMINAL_TGT; eauto. *)
(*   - i. exploit sim_pf_step; eauto. i. des. esplits; eauto. *)
(* Qed. *)

(* Theorem drf_pf *)
(*       s *)
(*       (RACEFREE: pf_racefree (Configuration.init s)) *)
(*   : *)
(*     behaviors Configuration.step (Configuration.init s) <1= *)
(*     behaviors (fun _ => pftstep) (Configuration.init s) *)
(* . *)
(* Proof. *)
(*   apply sim_whole_adequacy, sim_pf_sim_whole, sim_pf_init. ss. *)
(* Qed. *)

(* Lemma self_promise_remove_lifting *)
(*       lang st1 st2 lc1_src lc1_tgt lc2_tgt mem1_tgt mem2_tgt mem1_src sc1 sc2 P  *)
(*       (STATE1 : forget_local lc1_src lc1_tgt) *)
(*       (MEM1 : forget_memory (Local.is_promised_loc lc1_src) *)
(*                                   mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step P _)  *)
(*                       (Thread.mk lang st1 lc1_tgt sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2_tgt sc2 mem2_tgt)) *)
(*       (CONSISTENT : promise_view_consistent lc2_tgt) *)
(*   : *)
(*     exists lc2_src mem2_src, *)
(*       <<SRC_STEP : (rc (tau (@pred_step P _))) *)
(*                        (Thread.mk _ st1 lc1_src sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2_src sc2 mem2_src)>> /\ *)
(*       <<STATE1 : forget_local lc2_src lc2_tgt>> /\ *)
(*       <<MEM1 : forget_memory (Local.is_promised_loc lc2_src) *)
(*                                     mem2_src mem2_tgt>> *)
(* . *)
(* Proof. *)
(*   destruct TGT_STEP, TSTEP, STEP. *)
(*   dependent destruction STEP. dependent destruction STEP. *)
(*   - exists lc1_src, mem1_src. destruct LOCAL. subst. *)
(*     econs; eauto; [| econs]. *)
(*     + apply Relation_Operators.r_refl. *)
(*     + destruct STATE1; econs; eauto. *)
(*     + destruct MEM1. econs; eauto. admit. *)
(*   - admit. *)
(* Admitted. *)

(* Lemma other_promise_remove_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P proms *)
(*       (MEM1 : forget_memory proms mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                      no_read_msgs proms) _)  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                       no_read_msgs proms) _)   *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> /\ *)
(*       <<MEM1 : forget_memory proms mem2_src mem2_tgt>> *)
(* . *)
(* Admitted. *)

(* Lemma future_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P v1 v2 *)
(*       (TGT_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _))  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*       (INTERVAL_EMPTY : empty_interval v1 v2 (fun _ => True) mem1_src) *)
(*       (FUTURE : Memory.le mem1_src mem1_tgt) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _)) *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> *)
(* . *)
(* Admitted. *)
