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

Require Import PromiseConsistent.
Require Import Trace.
Require Import MemoryProps.
Require Import JoinedView.

Require Import LocalPF.
Require Import OrdStep.
Require Import RARace.
Require Import Stable.
Require Import PFtoRASimThread.
Require Import PFtoRAThread.

Set Implicit Arguments.


Definition option_rel3 {A B C} (P: A -> B -> C -> Prop)
           (a: option A) (b: option B) (c: option C): Prop :=
  match a, b, c with
  | Some x, Some y, Some z => P x y z
  | None, None, None => True
  | _, _, _ => False
  end.


Module PFtoRA.
  Section PFtoRA.
    Variable L: Loc.t -> bool.

    (* well-formedness *)

    Inductive wf_pf (tr: Trace.t) (c: Configuration.t): Prop :=
    | wf_pf_intro
        (WF: Configuration.wf c)
        (TRACE: forall tid lang st lc
                  (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)),
            TraceWF.wf tr lc.(Local.promises) c.(Configuration.memory))
    .

    Definition wf_j := JConfiguration.wf.

    Inductive wf_ra (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
    | wf_ra_intro
        (WF: Configuration.wf c)
        (RELS: forall tid lang st lc
                 (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)),
            ReleaseWrites.wf rels lc.(Local.promises) c.(Configuration.memory))
    .

    Lemma wf_pf_thread
          tr c tid lang st lc
          (WF: wf_pf tr c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_pf tr (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit TRACE; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_j_thread
          views c tid lang st lc
          (WF: wf_j views c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_j views (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit REL; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_ra_thread
          rels c tid lang st lc
          (WF: wf_ra rels c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_ra rels (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit RELS; eauto. i.
      econs; eauto.
    Qed.

    Lemma step_wf_pf
          tr1 tr e tid c1 c2
          (WF1: wf_pf tr1 c1)
          (STEP: pf_step_trace L tr e tid c1 c2):
      <<WF2: wf_pf (tr1 ++ tr) c2>>.
    Proof.
      exploit pf_step_trace_future; eauto; try apply WF1. i. des.
      inv STEP. ss.
      exploit wf_pf_thread; eauto. i.
      exploit Trace.steps_step_steps; eauto. i.
      exploit PFtoRAThread.steps_pf_future; try exact x1; eauto. i. des.
      econs; ss. i. Configuration.simplify; try apply x2.
      exploit wf_pf_thread; try eapply TH; eauto. i. inv x3. ss.
      apply TraceWF.wf_app.
      - hexploit TraceWF.steps_disjoint_other; [eapply x0|eapply TRACE|..]; eauto.
      - hexploit TraceWF.steps_disjoint; try eapply x1; eauto; try apply x0; s.
        inv WF1. inv WF0. inv WF1. eauto.
    Qed.

    Lemma steps_wf_j
          e tid c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEP: JConfiguration.step e tid c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.step_future; eauto.
    Qed.

    Lemma steps_wf_ra
          e tid rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (STEP: RAConfiguration.step L e tid rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      exploit RAConfiguration.step_future; try eapply WF1; eauto. i. des.
      inv STEP. ss.
      assert (STEPS': RAThread.steps lang L rels1 rels2
                                     (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))
                                     (Thread.mk _ st3 lc3 sc3 memory3)).
      { exploit RAThread.tau_steps_steps; eauto. i.
        inv STEP0; eapply RAThread.plus_step_steps; eauto. }
      exploit wf_ra_thread; eauto. i.
      hexploit RAThread.steps_rels_wf; try exact STEPS'; try apply x1. s. i.
      econs; ss. i. Configuration.simplify; ss.
      exploit wf_ra_thread; try eapply TH; eauto. i.
      inv WF1. inv WF. inv WF0.
      exploit DISJOINT; try exact n; eauto. i.
      hexploit RAThread.steps_rels_disjoint; try exact x; eauto. apply x1.
    Qed.


    (* sim *)

    Inductive sim_thread_sl (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
              (sc_pf sc_j sc_ra: TimeMap.t) (mem_pf mem_j mem_ra: Memory.t):
      forall (sl_pf sl_j sl_ra: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang st_pf lc_pf st_j lc_j st_ra lc_ra
        (SIM: PFtoRAThread.sim_thread L views rels
                                      (Thread.mk lang st_pf lc_pf sc_pf mem_pf)
                                      (Thread.mk lang st_j lc_j sc_j mem_j)
                                      (Thread.mk lang st_ra lc_ra sc_ra mem_ra)):
        sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra
                      (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j) (existT _ lang st_ra, lc_ra)
    .

    Inductive sim_conf (tr: Trace.t) (rels: ReleaseWrites.t): forall (c_pf c_ra: Configuration.t), Prop :=
    | sim_conf_intro
        views
        ths_pf sc_pf mem_pf
        ths_j sc_j mem_j
        ths_ra sc_ra mem_ra
        (SIM_TR: PFtoRAThread.sim_trace tr rels)
        (THS: forall tid,
            option_rel3
              (sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_j)
              (IdentMap.find tid ths_ra)):
        sim_conf tr rels
                 (Configuration.mk ths_pf sc_pf mem_pf)
                 (Configuration.mk ths_ra sc_ra mem_ra)
    .
  End PFtoRA.
End PFtoRA.
