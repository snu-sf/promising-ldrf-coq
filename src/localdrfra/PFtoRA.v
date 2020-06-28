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


Module PFtoRA.
  Section PFtoRA.
    Variable L: Loc.t -> bool.

    (* Definition option_rel3 {A B C} (P: A -> B -> C -> Prop) *)
    (*            (a: option A) (b: option B) (c: option C): Prop := *)
    (*   match a, b, c with *)
    (*   | Some x, Some y, Some z => P x y z *)
    (*   | None, None, None => True *)
    (*   | _, _, _ => False *)
    (*   end. *)

    (* Inductive sim_thread_sl (tr: Trace.t) (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t) *)
    (*           (sc_pf sc_j sc_ra: TimeMap.t) (mem_pf mem_j mem_ra: Memory.t): *)
    (*   forall (sl_pf sl_j sl_ra: {lang: language & Language.state lang} * Local.t), Prop := *)
    (* | sim_thread_sl_intro *)
    (*     lang st_pf lc_pf st_j lc_j st_ra lc_ra *)
    (*     (SIM: sim_thread L views rels *)
    (*                      (Thread.mk lang st_pf lc_pf sc_pf mem_pf) *)
    (*                      (Thread.mk lang st_j lc_j sc_j mem_j) *)
    (*                      (Thread.mk lang st_ra lc_ra sc_ra mem_ra)) *)
    (*     (SIM_TR: sim_trace tr rels) *)
    (*     (TRACE_WF: TraceWF.wf tr lc_pf.(Local.promises) mem_pf) *)
    (*     (RELS_WF: ReleaseWrites.wf rels lc_ra.(Local.promises) mem_ra): *)
    (*     sim_thread_sl tr views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra *)
    (*                   (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j) (existT _ lang st_ra, lc_ra) *)
    (* . *)

    (* Inductive sim_conf (rels: ReleaseWrites.t): forall (c_pf c_ra: Configuration.t), Prop := *)
    (* | sim_conf_intro *)
    (*     views *)
    (*     ths_pf sc_pf mem_pf *)
    (*     ths_j sc_j mem_j *)
    (*     ths_ra sc_ra mem_ra *)
    (*     (THS: forall tid, *)
    (*         option_rel3 *)
    (*           (sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra) *)
    (*           (IdentMap.find tid ths_pf) *)
    (*           (IdentMap.find tid ths_j) *)
    (*           (IdentMap.find tid ths_ra)): *)
    (*     sim_conf rels *)
    (*              (Configuration.mk ths_pf sc_pf mem_pf) *)
    (*              (Configuration.mk ths_ra sc_ra mem_ra) *)
    (* . *)

    (* Lemma sim_conf_steps *)
    (*       views1 rels2 c1_pf c1_j c1_ra *)
    (*       c2_pf trs *)
    (*       (SIM: sim_conf views rels c1_pf c1_j c1_ra) *)
    (*       (WF1_PF: Configuration.wf c1_pf) *)
    (*       (WF1_J: Configuration.wf c1_j) *)
    (*       (WF1_RA: Configuration.wf c1_ra) *)
    (*       (STEPS_PF: LOCALDRF.configuration_steps_trace c1_pf c2_pf): *)
    (*   exists  *)
  End PFtoRA.
End PFtoRA.
