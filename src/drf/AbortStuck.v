Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import APromiseConsistent.
From PromisingLib Require Import Loc.
Require Import Behavior.

Set Implicit Arguments.


(* TODO: unify with ADRF_PF1.v *)

Definition reserver_exists (c: Configuration.t) :=
  forall loc to from
         (RESERVE: Memory.get loc to c.(Configuration.memory) = Some (from, Message.reserve)),
  exists tid st lc,
    (<<TH: IdentMap.find tid c.(Configuration.threads) =
               Some (st, lc)>>) /\
    (<<PROM: Memory.get loc to lc.(Local.promises) = Some (from, Message.reserve)>>).

Lemma promise_new_reserve prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 mem1 = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 prom1 <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 mem0 = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 prom0 <> Some (from0, Message.reserve)>>)
.
Proof.
  inv PROMISE.
  - erewrite Memory.add_o in GET; eauto.
    erewrite Memory.add_o in NONE; eauto. des_ifs.
  - erewrite Memory.split_o in GET; eauto.
    erewrite Memory.split_o in NONE; eauto. des_ifs.
  - erewrite Memory.lower_o in GET; eauto.
    erewrite Memory.lower_o in NONE; eauto. des_ifs.
  - erewrite Memory.remove_o in GET; eauto.
    erewrite Memory.remove_o in NONE; eauto. des_ifs.
Qed.

Lemma write_new_reserve prom0 mem0 loc from to val released prom1 mem1 kind
      (wRITE: Memory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 mem1 = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 prom1 <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 mem0 = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 prom0 <> Some (from0, Message.reserve)>>)
.
Proof.
  inv wRITE. erewrite Memory.remove_o in NONE; eauto. des_ifs.
  - ss. des; clarify.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
    + inv PROMISE; ss; clarify.
    + eapply Memory.promise_get2 in PROMISE; auto. des. clarify.
  - eapply promise_new_reserve; eauto.
Qed.

Lemma step_new_reserve lang (th0 th1: Thread.t lang) e
      (STEP: Thread.step_allpf e th0 th1)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 th1.(Thread.memory) = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 th1.(Thread.local).(Local.promises) <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 th0.(Thread.memory) = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 th0.(Thread.local).(Local.promises) <> Some (from0, Message.reserve)>>)
.
Proof.
  inv STEP. inv STEP0; inv STEP.
  - inv LOCAL. ss.
    eapply promise_new_reserve in PROMISE; eauto.
  - inv LOCAL; ss; try by inv LOCAL0; ss.
    + inv LOCAL0. ss. eapply write_new_reserve in WRITE; eauto.
    + inv LOCAL1. inv LOCAL2. eapply write_new_reserve in WRITE; eauto.
Qed.

Lemma steps_new_reserve lang (th0 th1: Thread.t lang)
      (STEPS: rtc (tau (@Thread.step_allpf _)) th0 th1)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 th1.(Thread.memory) = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 th1.(Thread.local).(Local.promises) <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 th0.(Thread.memory) = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 th0.(Thread.local).(Local.promises) <> Some (from0, Message.reserve)>>)
.
Proof.
  ginduction STEPS.
  - i. clarify.
  - i. exploit IHSTEPS; eauto. i. des.
    inv H. exploit step_new_reserve; eauto.
Qed.

Lemma step_reserver_exists c0 c1 tid e
      (RESERVES: reserver_exists c0)
      (STEP: Configuration.step e tid c0 c1)
  :
    reserver_exists c1.
Proof.
  inv STEP.
  { ii. ss.
    destruct (classic (Memory.get loc to lc3.(Local.promises) = Some (from, Message.reserve))).
    - exists tid. erewrite IdentMap.gss. esplits; eauto.
    - exploit step_new_reserve.
      { econs; eauto. } all: eauto.
      i. des.
      exploit steps_new_reserve; eauto.
      i. des. ss.
      eapply RESERVES in GET0. des.
      assert (NEQ: tid <> tid0).
      { ii. clarify. }
      exists tid0. esplits; eauto.
      erewrite IdentMap.gso; eauto.
  }
  { ii. ss.
    destruct (classic (Memory.get loc to lc3.(Local.promises) = Some (from, Message.reserve))).
    - exists tid. erewrite IdentMap.gss. esplits; eauto.
    - exploit step_new_reserve.
      { econs; eauto. } all: eauto.
      i. des.
      exploit steps_new_reserve; eauto.
      i. des. ss.
      eapply RESERVES in GET0. des.
      assert (NEQ: tid <> tid0).
      { ii. clarify. }
      exists tid0. esplits; eauto.
      erewrite IdentMap.gso; eauto.
  }
Qed.

Definition Thread_consistent_failure lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1)
         (SC_MAX: Memory.max_full_timemap mem1 sc1),
    (<<FAILURE: Thread.steps_failure (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1)>>).

Definition Thread_consistent_normal lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1)
         (SC_MAX: Memory.max_full_timemap mem1 sc1),
  exists e2,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
    (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>).

Lemma thread_consistent_failure_or_normal lang (e: Thread.t lang)
      (CONSISTENT: Thread.consistent e)
      (CLOSED: Memory.closed (Thread.memory e))
  :
    (<<FAILURE: Thread_consistent_failure e>>) \/
    (<<NORMAL: Thread_consistent_normal e>>).
Proof.
  destruct (classic (Thread_consistent_failure e)); auto. right.
  ii. exploit CONSISTENT; eauto. i. des.
  - exfalso. eapply H. ii.
    exploit Memory.cap_inj.
    { eapply CAP. }
    { eapply CAP0. }
    { eauto. } i. subst.
    exploit Memory.max_full_timemap_inj.
    { eapply SC_MAX. }
    { eapply SC_MAX0. }
    i. subst. eauto.
  - eauto.
Qed.

Definition consistent_in_the_past (tids: Ident.t -> Prop) (c: Configuration.t) :=
  forall tid (TID: tids tid) lang st lc
         (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)),
  exists mem_past sc_past,
    (<<MEMORY: Memory.closed mem_past>>) /\
    (<<SC: Memory.closed_timemap sc_past mem_past>>) /\
    (<<LOCAL: Local.wf lc mem_past>>) /\
    (<<FUTUREMEM: Memory.future mem_past c.(Configuration.memory)>>) /\
    (<<FUTURESC: TimeMap.le sc_past c.(Configuration.sc)>>) /\
    (<<CONSISTENT: Thread_consistent_normal (Thread.mk _ st lc sc_past mem_past)>>).

Lemma consistent_in_the_past_step c0 c1 tid e
      (WF: Configuration.wf c0)
      (CONSISTENT: consistent_in_the_past (fun tid' => tid' <> tid) c0)
      (STEP: Configuration.step e tid c0 c1)
  :
    consistent_in_the_past (fun tid' => tid' <> tid) c1.
Proof.
  exploit Configuration.step_future; eauto. i. des.
  ii. exploit CONSISTENT.
  { eauto. }
  { inv STEP; ss.
    - erewrite IdentMap.gso in TH; eauto.
    - erewrite IdentMap.gso in TH; eauto. }
  i. des. esplits; eauto. etrans; eauto.
Qed.



Definition Threads_has_no_promise (tids: Ident.t -> Prop) (ths: Threads.t) :=
  forall tid (TIDS: tids tid) lang st lc
         (TH': IdentMap.find tid ths = Some (existT _ lang st, lc)),
    Local.is_terminal lc.

Lemma can_remove_all_promises (c0: Configuration.t) tid
      (CONSISTENT: consistent_in_the_past (fun tid' => tid' <> tid) c0)
      (RESERVER: reserver_exists c0)
      (WF: Configuration.wf c0)
      lang st lc
      (TH: IdentMap.find tid c0.(Configuration.threads) = Some (existT _ lang st, lc))
      (FAILURE: Thread_consistent_failure (Thread.mk _ st lc c0.(Configuration.sc) c0.(Configuration.memory)))
  :
    exists c1 c2,
      (<<STEPS: rtc Configuration.tau_step c0 c1>>) /\
      (<<NOPROMISE: Threads_has_no_promise (fun tid' => tid' <> tid) c1.(Configuration.threads)>>) /\
      (<<STEP: Configuration.step MachineEvent.failure tid c1 c2>>)
.
Admitted.

Lemma failure_thread_step_keep c0 c1 tid
      (STEP: Configuration.step MachineEvent.failure tid c0 c1)
  :
    exists lang st lc c1',
      (<<STEP: Configuration.opt_step MachineEvent.silent tid c0 c1'>>) /\
      (<<TH: IdentMap.find tid c1'.(Configuration.threads) = Some (existT _ lang st, lc)>>) /\
      (<<FAILURE: Thread_consistent_failure (Thread.mk _ st lc c1'.(Configuration.sc) c1'.(Configuration.memory))>>)
.
Proof.
  inv STEP; cycle 1.
  { destruct e; ss. }
  apply rtc_tail in STEPS. des.
  - destruct a2, e2. inv STEPS0. inv TSTEP.
    inv STEP0; inv STEP1; ss. inv LOCAL. esplits.
    + econs 2. rewrite <- EVENT. econs.
      * eauto.
      * eapply STEPS.
      * eapply STEP.
      * destruct e; ss.
      * ii. left. unfold Thread.steps_failure. esplits.
        { econs 1. }
        { econs 2. econs; eauto. }
    + ss. rewrite IdentMap.gss. ss.
    + ss. ii. unfold Thread.steps_failure. esplits.
      * econs 1.
      * econs 2. econs; eauto.
  - inv STEP0.
    { inv STEP; ss. }
    inv STEP. inv LOCAL. esplits.
     + econs 1.
     + eauto.
     + ii. ss. unfold Thread.steps_failure. esplits.
       * econs 1.
       * econs 2. econs; eauto.
Qed.

Inductive safe_sim (c: Configuration.t): Prop :=
| safe_sim_intro
    (CONSISTENT: consistent_in_the_past (fun _ => True) c)
    (RESERVER: reserver_exists c)
    (WF: Configuration.wf c)
.

Inductive Configuration_safe_other_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| Configuration_safe_other_step_failure
    pf tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf ThreadEvent.failure e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (NOPROMISE: Threads_has_no_promise (fun tid' => tid' <> tid) c1.(Configuration.threads))
  :
    Configuration_safe_other_step MachineEvent.failure tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
| Configuration_safe_other_step_normal
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (EVENT: e <> ThreadEvent.failure)
    (CONSISTENT: Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3)):
    Configuration_safe_other_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.

Lemma silent_step_safe_other_step
  :
    Configuration.step MachineEvent.silent <3= Configuration_safe_other_step MachineEvent.silent.
Proof.
  i. inv PR. econs 2; eauto.
Qed.








Section WRAP.

  Definition wrap_init (lang: language) (s: lang.(Language.syntax)) := Some (lang.(Language.init) s).

  Definition wrap_terminal (lang: language) (st: option lang.(Language.state)) :=
    match st with
    | Some st' => lang.(Language.is_terminal) st'
    | _ => False
    end.

  Inductive wrap_step (lang: language): ProgramEvent.t -> option lang.(Language.state) -> option lang.(Language.state) -> Prop :=
  | wrap_step_normal
      e st0 st1
      (NORMAL: e <> ProgramEvent.failure)
      (STEP: lang.(Language.step) e st0 st1)
    :
      wrap_step lang e (Some st0) (Some st1)
  | wrap_step_abort
      st0 st1
      (STEP: lang.(Language.step) ProgramEvent.failure st0 st1)
    :
      wrap_step lang ProgramEvent.silent (Some st0) None
  | wrap_step_any
      loc val ord
    :
      wrap_step lang (ProgramEvent.write loc val ord) None None
  | wrap_step_end
    :
      wrap_step lang ProgramEvent.failure None None
  .

  Definition wrap_lang (lang: language): language :=
    Language.mk (wrap_init lang) (wrap_terminal lang) (wrap_step lang).

  Definition wrap_code (langsynx: sigT (@Language.syntax ProgramEvent.t)): sigT (@Language.syntax ProgramEvent.t) :=
    let (lang, synx) := langsynx in (existT _ (wrap_lang lang) synx).

  Definition wrap_threads (s: Threads.syntax): Threads.syntax := IdentMap.map wrap_code s.

  Inductive Configuration_safe_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
  | Configuration_safe_step_failure
      pf tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.step pf ThreadEvent.failure e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (NOPROMISE: Threads_has_no_promise (fun _ => True) c1.(Configuration.threads))
    :
      Configuration_safe_step MachineEvent.failure tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
  | Configuration_safe_step_normal
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (EVENT: e <> ThreadEvent.failure)
      (CONSISTENT: Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3)):
      Configuration_safe_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
  .

  Conjecture safe_step_equivalent
    :
      forall (s: Threads.syntax),
        behaviors Configuration.step (Configuration.init s) <1=
        behaviors Configuration_safe_step (Configuration.init (wrap_threads s)).


Lemma safe_sim_step c0 c1 tid e
      (SAFE: safe_sim c0)
      (STEP: Configuration.step e tid c0 c1)
  :
    ((<<STEP: Configuration_safe_step e tid c0 c1>>) /\
     (<<SAFE: safe_sim c1>>)) \/
    (exists c1' c2',
        (<<STEPS: rtc (union (Configuration_safe_step MachineEvent.silent)) c0 c1'>>) /\
        (<<STEP: Configuration_safe_step MachineEvent.failure tid c1' c2'>>)).
Proof.
  inv SAFE. destruct (classic (e = MachineEvent.failure)); subst.
  - apply failure_thread_step_keep in STEP. des.
    hexploit can_remove_all_promises.
    + instantiate (1:=c1'). inv STEP0.
      * ii. eauto.
      * eapply consistent_in_the_past_step; eauto.
        ii. eauto.
    + inv STEP0; ss. eapply step_reserver_exists; eauto.
    + eapply Configuration.opt_step_future; eauto.
    + eauto.
    + eauto.
    + i. des. right. esplits.
      * transitivity c1'.
        { inv STEP0; eauto. econs; eauto. econs; eauto.
          eapply silent_step_safe_step; eauto. }
        { eapply rtc_implies; cycle 1; eauto.
          i. inv PR. econs; eauto. eapply silent_step_safe_step; eauto. }
      * instantiate (1:=c3). inv STEP; cycle 1.
        { destruct e; ss. }
        econs 1; eauto.
  - dup STEP. hexploit consistent_in_the_past_step; eauto.
    { ii. eauto. } intros PAST1.
    hexploit step_reserver_exists; eauto. intros RESERVER1.
    hexploit Configuration.step_future; eauto. i. des.
    inv STEP; clarify.
    { eapply thread_consistent_failure_or_normal in CONSISTENT0. des.
      - hexploit can_remove_all_promises; eauto.
        { ss. rewrite IdentMap.gss. ss. }
        i. des. right. esplits.
        + etrans; cycle 1.
          { eapply rtc_implies; cycle 1; eauto.
            i. inv PR. econs; eauto. eapply silent_step_safe_step; eauto. }
          { econs; [|refl]. econs; eauto.


          transitivity c1.
          { econs; [|refl]. econs; eauto. econs 2; eauto.

            inv STEP0; eauto. econs; eauto. econs; eauto.
            eapply silent_step_safe_step; eauto. }
          { eapply rtc_implies; cycle 1; eauto.
            i. inv PR. econs; eauto. eapply silent_step_safe_step; eauto. }
          *


          instantiate (1:=c1'). inv STEP0.
          * ii. eauto.
          * eapply consistent_in_the_past_step; eauto.
            ii. eauto.
        + inv STEP0; ss. eapply step_reserver_exists; eauto.
        + eapply Configuration.rtc_step_future; [|eauto].
          inv STEP0; eauto. econs; [|refl]. econs; eauto.
        + eauto.
        + eauto.
        + i. des. right. esplits.
          * transitivity c1'.
            { inv STEP0; eauto. econs; eauto. econs; eauto.
              eapply silent_step_safe_step; eauto. }
            { eapply rtc_implies; cycle 1; eauto.
              i. inv PR. econs; eauto. eapply silent_step_safe_step; eauto. }
          * instantiate (1:=c3). inv STEP; cycle 1.
            { destruct e; ss. }
            econs 1; eauto.
      -



        IdentMap.map



      destruct e0; ss.




        instantiate (1:=c2clear - STEPS


        (*   * inv STEP; ss. ii.  ss. rewrite  *)
    (*   ii. *)


    (* + ii. eapply CONSISTENT; eauto. *)
    (* + eauto. *)
      (* inv SAFE. inv STEP. *)
      (* - *)
      (*   admit. *)
      (* - *)
Admitted.



ThreadEvent.t


language