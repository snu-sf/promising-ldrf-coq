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
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
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
      (<<EVT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
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

      (CONSISTENT: Local.promise_consistent (Local.mk v' prom'))
      (OTHERSPACE: others \2/ otherspace <2= unchangables mem_tgt prom)

      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: opt_pred_step
                 (no_promise) e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
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
      (CONSISTENT: Local.promise_consistent th_tgt'.(Thread.local))
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


Inductive other_promises tid (ths: Threads.t): FLoc.t -> Time.t -> Prop :=
| other_promises_intro
    loc to
    tid' lang st lc
    (NEQ: tid <> tid')
    (FIND: IdentMap.find tid' ths = Some (existT _ lang st, lc))
    (PROMISED: promised lc.(Local.promises) loc to)
  :
    other_promises tid ths loc to
.

Inductive other_updates tid (updates: Ident.t -> FLoc.t -> Time.t -> Prop):
  FLoc.t -> Time.t -> Prop :=
| other_updates_intro
    loc to tid'
    (NEQ: tid <> tid')
    (UPDATES: updates tid' loc to)
  :
    other_updates tid updates loc to
.

Inductive other_space tid (ths: Threads.t) (mem: Memory.t): FLoc.t -> Time.t -> Prop :=
| other_space_intro
    loc to
    tid' lang st lc
    (NEQ: tid <> tid')
    (FIND: IdentMap.find tid' ths = Some (existT _ lang st, lc))
    (SPACE: concrete_covered lc.(Local.promises) mem loc to)
  :
    other_space tid ths mem loc to
.

Lemma other_space_same tid ths mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
  :
    other_space tid ths mem0 <2= other_space tid ths mem1.
Proof.
  i. inv PR. econs; eauto.
  eapply concrete_covered_same; eauto.
Qed.

Lemma race_lemma c tid0 tid1 lang0 lang1 st0 st1 lc0 lc1 th0 th1 e1 e2
      (NEQ: tid0 <> tid1)
      (RACEFREE: pf_racefree c)
      (WF: Configuration.wf c)
      (FIND0: IdentMap.find tid0 (Configuration.threads c) = Some (existT _ lang0 st0, lc0))
      (FIND1: IdentMap.find tid1 (Configuration.threads c) = Some (existT _ lang1 st1, lc1))
      (STEP0: rtc (tau (@Thread.program_step _)) (Thread.mk _ st0 lc0 c.(Configuration.sc) c.(Configuration.memory)) th0)
      (STEP1: rtc (tau (@Thread.program_step _)) (Thread.mk _ st1 lc1 th0.(Thread.sc) th0.(Thread.memory)) th1)
      (PROEVT0: can_step _ th0.(Thread.state) e1)
      (PROEVT1: can_step _ th1.(Thread.state) e2)
      (RACE: pf_race_condition e1 e2)
  :
    False.
Proof.
  eapply rtc_tail in STEP0. des; ss; clarify.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP2. inv STEP3. destruct th0, th1. exploit RACEFREE.
      * econs 2; [|econs 2; [|refl]].
        { econs. econs. econs.
          - eapply FIND0.
          - eapply STEP0.
          - eauto. }
        { econs. econs. econs.
          - ss. erewrite IdentMap.gso.
            + eapply FIND1.
            + eauto.
          - eapply STEP1.
          - eauto. }
      * econs; ss.
        { erewrite IdentMap.gso.
          - erewrite IdentMap.gss. eauto.
          - eauto. }
        { erewrite IdentMap.gss. eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
    + inv STEP2. destruct th0. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs. econs.
        { eapply FIND0. }
        { eapply STEP0. }
        { eauto. }
      * econs; ss.
        { erewrite IdentMap.gss. eauto. }
        { erewrite IdentMap.gso.
          - eapply FIND1.
          - eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP0. destruct th1. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs. econs.
        { eapply FIND1. }
        { eapply STEP1. }
        { eauto. }
      * econs; ss.
        { erewrite IdentMap.gso.
          - eapply FIND0.
          - eauto. }
        { erewrite IdentMap.gss. eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
    + exploit RACEFREE.
      * refl.
      * econs.
        { eapply FIND0. }
        { eapply FIND1. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * eauto.
Qed.

Lemma rtc_unchangables_increase lang (th0 th1: Thread.t lang)
      (STEP: rtc (Thread.tau_step (lang:=lang)) th0 th1)
  :
    unchangables th0.(Thread.memory) th0.(Thread.local).(Local.promises) <2=
    unchangables th1.(Thread.memory) th1.(Thread.local).(Local.promises).
Proof.
  induction STEP; eauto.
  i. inv H. inv TSTEP. eapply IHSTEP. eapply unchangables_increase; eauto.
Qed.

Lemma inv_step mem0 mem1 lang (st: Language.state lang)
      lc proms spaces aupdates updates mlast
      (INV: Inv.t mem0 _ st lc proms spaces aupdates updates mlast)
      (FUTURE: Memory.future mem0 mem1)
  :
    Inv.t mem1 _ st lc proms spaces aupdates updates mlast.
Proof.
  inv INV. econs; eauto.
  i. eapply concrete_covered_same; eauto.
Qed.

Lemma sim_pf_step
      c_src0 c_tgt0 c_tgt1 tid e mlast spaces updates aupdates
      (SIM: sim_pf mlast spaces updates aupdates c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    exists c_src1,
      ((<<STEP: opt_pftstep e tid c_src0 c_src1>>) /\
       (<<FORGET: forget_config c_src1 c_tgt1>>) /\
       (<<SAT: forall tid' (NEQ: tid <> tid') lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                      (TIDSRC: IdentMap.find tid' c_src1.(Configuration.threads) =
                               Some (existT _ lang_src st_src, lc_src))
                      (TIDTGT: IdentMap.find tid' c_tgt1.(Configuration.threads) =
                               Some (existT _ lang_tgt st_tgt, lc_tgt)),
           (<<FUTURE: unchanged_on (spaces tid') (mlast tid') c_src1.(Configuration.memory)>>) /\
           (<<NOATTATCH: not_attatched (updates tid') c_src1.(Configuration.memory)>>) /\
           (<<INV: Inv.t c_tgt1.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid') (updates tid') (aupdates tid') (mlast tid')>>)>>))
(* /\ *)
(*  (<<RACEFREE: pf_racefree c_src1>>) /\ *)
(*  (<<WFSRC: Configuration.wf c_src1>>) /\ *)
(*  (<<WFTGT: Configuration.wf c_tgt1>>)) *)

(* \/ *)
(* (<<ABORT: Configuration.step MachineEvent.abort tid c_src0 c_src1>>) *)
.
Proof.
  inv SIM. inv FORGET. dup THS. specialize (THS tid). inv STEP; ss.
  { admit. }
  { rewrite TID in THS. unfold option_rel in *. des_ifs. inv THS.
    dup WFTGT. inv WFTGT.
    exploit Thread.rtc_tau_step_future; eauto; ss.
    { inv WF. eauto. }
    i. des.
    exploit Thread.step_future; eauto.
    i. des.

    assert (CONSISTENT1: Local.promise_consistent lc3).
    { hexploit consistent_promise_consistent; eauto. }
    assert (CONSISTENT0: Local.promise_consistent e2.(Thread.local)).
    { hexploit step_promise_consistent; eauto. }

    set (oproms := all_promises c_tgt0.(Configuration.threads) (fun tid' => tid <> tid')).
    (* set (oproms := other_promises tid (Configuration.threads c_tgt0)). *)
    set (oupdates := other_updates tid updates).
    set (ospace := other_space tid (Configuration.threads c_tgt0) (Configuration.memory c_tgt0)).
    destruct lc0, lc1. ss. clarify.

    assert (OPROMS: (oproms \2/ promised promises0) = (all_promises c_tgt0.(Configuration.threads) (fun _ => True))).
    { extensionality loc. extensionality to.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      unfold oproms. split; i.
      - des.
        + inv H. econs; eauto.
        + econs; eauto.
      - inv H. destruct (classic (tid = tid0)).
        + right. clarify.
        + left. econs; eauto. }

    assert (OSPACE: oproms \2/ ospace <2= unchangables (Configuration.memory c_tgt0) promises0).
    { i. des.
      - inv PR. inv WF. destruct st.
        exploit THREADS; eauto. i. inv x2.
        inv PROMISED. destruct msg.
        exploit Memory.get_ts; eauto. i. des.
        { clarify. erewrite BOT in GET. clarify. }
        econs.
        + red. econs; eauto. econs; eauto; ss. refl.
        + ii. inv H. exploit DISJOINT; try eassumption.
          i. inv x2. ss. inv DISJOINT0.
          exploit DISJOINT1; try eassumption. i. des.
          eapply x2; eauto. econs; ss; eauto. refl.
      - inv PR. inv WF.
        exploit THREADS; eauto. i. inv x.
        inv SPACE.
        + econs.
          * red. econs; eauto.
          * ii. inv H. exploit DISJOINT; try eassumption.
            i. inv x. ss. inv DISJOINT0.
            exploit DISJOINT1; try eassumption. i. des.
            eapply x; eauto.
        + econs.
          * red. econs; [eapply PROMISES|]; eauto.
          * ii. inv H. exploit DISJOINT; try eassumption.
            i. inv x. ss. inv DISJOINT0.
            exploit DISJOINT1; try eassumption. i. des.
            eapply x; eauto. }

    hexploit (@hold_or_not (fun _ => True) ((no_update_on oupdates) /1\ (no_read_msgs oproms))).
    { eapply pred_steps_thread_steps. eapply STEPS. }
    i. des.

    - exploit step_lifting_rtc.
      + eapply pred_step_rtc_mon; [|apply HOLD]. i. ss. des.
        instantiate (1:=oproms). instantiate (1:=oupdates). eauto.
      + instantiate (1:=Thread.mk _ st1 (Local.mk tview0 Memory.bot) (Configuration.sc c_src0) (Configuration.memory c_src0)).
        rewrite SC. econs. rewrite OPROMS. auto.
      + ss. unfold oupdates. ii. inv SAT.
        eapply NOATTATCH; eauto.
      + inv WF. econs; eauto.
      + eauto.
      + eauto.
      + i. des. inv FORGET. destruct lc3. ss.
        destruct (classic (((no_update_on oupdates) /1\ (no_read_msgs oproms)) e0)).
        * exploit step_lifting.
          { econs. econs. eapply STEP0.
            splits; ss; eapply H. }
          { ss. }
          { ss. }
          { ss. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. eapply rtc_unchangables_increase in STEPS; ss; eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. des.
            assert (OPROMS': (oproms \2/ promised promises) =
                             (all_promises
                                (IdentMap.add
                                   tid
                                   (existT (Language.state (E:=ProgramEvent.t)) lang st3,
                                    (Local.mk tview promises))
                                   (Configuration.threads c_tgt0)))
                               (fun _ => True)).
            { extensionality loc. extensionality to.
              apply Coq.Logic.PropExtensionality.propositional_extensionality.
              unfold oproms. split; i.
              - des.
                + inv H1. econs; eauto. ss.
                  erewrite IdentMap.gso; eauto.
                + econs; eauto. ss.
                  erewrite IdentMap.gss; eauto. ss.
              - inv H1. ss. rewrite IdentMap.gsspec in *. des_ifs.
                + right. ss.
                + left. econs; eauto. }
            inv STEP1.
            - eapply rtc_tail in STEP. des; ss.
              + inv STEP1. esplits.
                * rewrite <- EVT. rewrite <- EVENT0.
                  econs 2. econs.
                  { eauto. }
                  { eapply no_promise_program_step_rtc; eauto. }
                  { eapply no_promise_program_step; eauto. }
                * econs; ss.
                  { i. repeat rewrite IdentMap.gsspec. des_ifs.
                    eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. ss.
                  rewrite IdentMap.gso in TIDSRC; auto.
                  rewrite IdentMap.gso in TIDTGT; auto.
                  exploit INV; eauto. i.
                  splits.
                  { etrans; eauto.
                    eapply unchanged_on_mon; eauto. i.
                    eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                  { eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { eapply inv_step; eauto. etrans; eauto. }
              + clarify. esplits.
                * rewrite <- EVT. econs.
                * econs; ss.
                  { i. rewrite IdentMap.gsspec. des_ifs.
                    - rewrite Heq. ss.
                    - eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. splits.
                  { etrans; eauto. refl. }
                  { i. eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { i. rewrite IdentMap.gso in TIDTGT; eauto.
                    exploit INV; eauto. i.
                    eapply inv_step; eauto. etrans; eauto. }
            - esplits.
              * rewrite <- EVT. econs 2. econs.
                { eauto. }
                { eapply no_promise_program_step_rtc; eauto. }
                { eapply no_promise_program_step; eauto. }
              * econs; ss.
                { i. repeat rewrite IdentMap.gsspec. des_ifs.
                  eapply THS0. }
                { rewrite OPROMS' in *. ss. }
              * i. ss.
                rewrite IdentMap.gso in TIDSRC; auto.
                rewrite IdentMap.gso in TIDTGT; auto.
                exploit INV; eauto. i.
                splits.
                { etrans; eauto.
                  eapply unchanged_on_mon.
                  - etrans; eauto.
                  - i. eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                { eapply not_attatched_mon; eauto.
                  i. econs; eauto. }
                { eapply inv_step; eauto. etrans; eauto. }
          }
        * apply not_and_or in H. des.
          { unfold no_update_on in H. des_ifs.
            apply NNPP in H. inv H.
            destruct (IdentMap.find tid' (Configuration.threads c_src0)) as
                [[[? ?] lc]|] eqn:FIND; cycle 1.
            { exfalso. eapply INVBOT in FIND. des.
              eapply UPDATESBOT; eauto. }
            specialize (THS0 tid'). rewrite FIND in *. des_ifs. inv THS0.
            exploit INV; eauto. i. inv x0.

            exploit AUPDATE.
            { eauto. }
            { etrans; eauto. eapply unchanged_on_mon; eauto.
              i. econs; eauto. }
            { eapply not_attatched_sum.
              - admit.
              - eapply not_attatched_mon; eauto.
                i. econs; eauto. }
            i. des. exfalso. eapply race_lemma; try eassumption.
            - eapply no_promise_program_step_rtc. eapply STEP.
            -
Admitted.


(*               eapply pred_step_rtc_mon; cycle 1. *)
(*               + eapply STEP. *)

(*                 [|eapply HOLD0]. *)


(*               eapply HOLD. *)
(*             - eauto. *)
(*             - eauto. *)
(*             - eauto. *)
(*             - eauto. *)

(*             exfaslo. *)


(*             - *)

(*                     eauto. } *)
(*                   { rewrite IdentMap.gso in TIDTGT; eauto. } *)




(*                   { *)

(*                     replace (oproms \2/ promised promises) with *)
(*                         (all_promises *)
(*                            (Configuration.mk *)
(*                               (IdentMap.add *)
(*                                  tid *)
(*                                  (existT (Language.state (E:=ProgramEvent.t)) lang st3, *)
(*                                   (Local.mk tview promises)) *)
(*                                  (Configuration.threads c_tgt0)) *)
(*                               (Configuration.sc c_src0) *)
(*                               memory3) (fun _ => True)) in MEM1; auto. *)



(*                   econsss. *)
(*                   inv STEP. *)


(*             inv FORGET. ss. ss. *)


(*             instantiate (1:=e0). *)

(*           admit. *)
(*         * *)


(*     - *)

(*           inv PR. *)


(*         inv WFSRC. inv WF1. econs; ss; eauto. *)
(*         eapply THREADS; eauto. *)


(*         eauto. *)


(*           { *)
(*         * eauto. *)
(*         * *)



(*         econs. *)

(*         instantiate (1:=Thread.mk _ st1 lc0 Configuration.sc c_src0 (Configuration.memory c_src0)). *)

(*         eauto. *)
(*       + *)

(*         instan *)

(*     ((fun _ => True) *)
(*                             /1\ (no_update_on updates) *)
(*                             /1\ (no_read_msgs others)) *)



(*         (Configuration.threads c_tgt0)). *)


(*                             /1\ (no_update_on updates) *)
(*                             /1\ (no_read_msgs others)) lang)) th_tgt th_tgt') *)


(*       (OTHERSPACE: others \2/ otherspace <2= unchangables th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises)) *)




(*       hexploit consistent_promise_consistent; eauto; ss. } *)


(*       - *)

(*     { inv WFTGT. eauto. } *)
(*     { inv WFTGT. eauto. } *)

(*       inv WFTGT. *)

(*     exploit rtc_tau_step_promise_consistent; eauto. *)


(*     assert (CONSISTENT1: Local.promise_consistent lc3). *)
(*     { exploit consistent_promise_consistent; eauto; ss. *)
(*       - *)


(*          (RACEFREE: pf_racefree c_src) *)
(*          (WFSRC: Configuration.wf c_src) *)
(*          (WFTGT: Configuration.wf c_tgt) *)




(*       (Configuration.init s) (Configuration.init s) *)
(* . *)
(* Proof. *)
(* Admitted. *)

Inductive sim_pf
          (mlast: Ident.t -> Memory.t)
          (spaces : Ident.t -> (FLoc.t -> Time.t -> Prop))
          (updates: Ident.t -> (FLoc.t -> Time.t -> Prop))
          (aupdates: Ident.t -> (FLoc.t -> Time.t -> Prop))
          (c_src c_tgt: Configuration.t) : Prop :=
| sim_pf_intro
    (FORGET: forget_config c_src c_tgt)

    (FUTURE:
       forall tid,
         unchanged_on (spaces tid) (mlast tid) c_src.(Configuration.memory))
    (NOATTATCH:
       forall tid,
         not_attatched (updates tid) c_src.(Configuration.memory))

    (INV:
       forall
         tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
         (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                  Some (existT _ lang_src st_src, lc_src))
         (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
                  Some (existT _ lang_tgt st_tgt, lc_tgt)),
         Inv.t c_tgt.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid) (updates tid) (aupdates tid) (mlast tid))

    (RACEFREE: pf_racefree c_src)
    (WFSRC: Configuration.wf c_src)
    (WFTGT: Configuration.wf c_tgt)
.




Lemma updates_list_exists
      P lang th0 th1
      (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1)
  :
    exists (updates: FLoc.t -> Prop),
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
          (updates: FLoc.t -> Prop)
          (sky gap: TimeMap.t)
          (f: FLoc.t -> Time.t -> Time.t): Prop :=
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

Definition cap (m mcap: Memory.t) (l: FLoc.t) (t: Time.t): Prop :=
  (<<NINMEM: ~ promised m l t>>) /\ (<<INCAPPED: promised mcap l t>>).

Definition no_acq_read_msgs (MSGS : FLoc.t -> Time.t -> Prop)
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
      (<<CONSISTENT: Local.promise_consistent th'.(Thread.local)>>) /\
      (<<PROMISES: forall l t (PROM: promised th.(Thread.local).(Local.promises) l t),
          ~ promised th'.(Thread.local).(Local.promises) l t>>).
Proof.
Admitted.

(* Lemma future_lifting *)
(*       P lang th0 th1 *)
(*       (BOT: th0.(Thread.local).(Local.promises) = Memory.bot) *)
(*       (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1) *)
(*   : *)
(*     exists (updates: FLoc.t -> Time.t -> Prop), *)
(*       (<<COMPLETE: *)
(*          rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                  /1\ no_promise) lang)) th0 th1>>) /\ *)





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
