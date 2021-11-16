Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Require Import Lia.

Require Import SeqLift.
(* Require Import Simple. *)

Section LANG.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Record sim_tview
         (f: Mapping.ts)
         (flag_src: Loc.t -> option Time.t)
         (rel_vers: Loc.t -> version)
         (tvw_src: TView.t) (tvw_tgt: TView.t)
    :
      Prop :=
    sim_tview_intro {
        sim_tview_rel: forall loc,
          sim_view (fun loc0 => loc0 <> loc) f (rel_vers loc) (tvw_src.(TView.rel) loc) (tvw_tgt.(TView.rel) loc);
        sim_tview_cur: sim_view (fun loc => flag_src loc = None) f (Mapping.vers f) tvw_src.(TView.cur) tvw_tgt.(TView.cur);
        sim_tview_acq: sim_view (fun loc => flag_src loc = None) f (Mapping.vers f) tvw_src.(TView.acq) tvw_tgt.(TView.acq);
      }.

  Variant wf_release_vers (vers: versions) (prom_tgt: Memory.t) (rel_vers: Loc.t -> version): Prop :=
  | wf_release_vers_intro
      (PROM: forall loc from to val released
                    (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val (Some released))),
          exists v,
            (<<VER: vers loc to = Some v>>) /\
            (<<REL: rel_vers loc = v>>))
  .

  Variant sim_local
          (f: Mapping.ts) (vers: versions)
          (flag_src: Loc.t -> option Time.t)
          (flag_tgt: Loc.t -> option Time.t)
    :
      Local.t -> Local.t -> Prop :=
  | sim_local_intro
      tvw_src tvw_tgt prom_src prom_tgt rel_vers
      (TVIEWW: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (PROMISES: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (RELVERS: wf_release_vers vers prom_tgt rel_vers)
      (FLAGTGT: forall loc ts (FLAG: flag_tgt loc = Some ts),
          tvw_src.(TView.cur).(View.rlx) loc = ts)
      (FLAGSRC: forall loc ts (FLAG: flag_src loc = Some ts),
          tvw_src.(TView.cur).(View.rlx) loc = ts)
    :
      sim_local
        f vers flag_src flag_tgt
        (Local.mk tvw_src prom_src)
        (Local.mk tvw_tgt prom_tgt)
  .

  Lemma sim_local_consistent f vers flag_src flag_tgt lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
        (WF: Mapping.wfs f)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii. ss.
    hexploit sim_promises_get_if; eauto. i. des.
    { eapply sim_timestamp_lt.
      { eapply sim_view_rlx.
        { eapply sim_tview_cur. eauto. }
        { ss. destruct (flag_src loc) eqn:FLAG; auto.
          erewrite sim_promises_none in PROMISE; eauto. ss.
        }
      }
      { eauto. }
      { eapply CONSISTENT; eauto. inv MSG0; ss. }
      { eauto. }
      { eapply mapping_latest_wf_loc. }
    }
    { eapply FLAGTGT in FLAG. subst. auto. }
  Qed.

  Variant max_values_src (vs: Loc.t -> option Const.t)
          (mem: Memory.t)
    :
      forall (lc: Local.t), Prop :=
  | max_values_src_intro
      tvw prom
      (MAX: forall loc v (VAL: vs loc = Some v),
          exists released,
            (<<MAX: max_readable
                      mem
                      prom
                      loc
                      (tvw.(TView.cur).(View.pln) loc)
                      v released>>))
      (NONMAX: forall loc (VAL: vs loc = None),
          forall val released,
            ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)
    :
      max_values_src vs mem (Local.mk tvw prom)
  .

  Variant max_values_tgt (vs: Loc.t -> option Const.t)
          (mem: Memory.t)
    :
      forall (lc: Local.t), Prop :=
  | max_values_tgt_intro
      tvw prom
      (MAX: forall loc v (VAL: vs loc = Some v),
          exists released,
            (<<MAX: max_readable
                      mem
                      prom
                      loc
                      (tvw.(TView.cur).(View.pln) loc)
                      v released>>))
    :
      max_values_tgt vs mem (Local.mk tvw prom)
  .

  Variant sim_thread
          (f: Mapping.ts) (vers: versions)
          (flag_src: Loc.t -> option Time.t)
          (flag_tgt: Loc.t -> option Time.t)
          (vs_src: Loc.t -> option Const.t)
          (vs_tgt: Loc.t -> option Const.t)
          mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt: Prop :=
  | sim_thread_intro
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (MAXSRC: max_values_src vs_src mem_src lc_src)
      (MAXTGT: max_values_src vs_src mem_src lc_src)
      (PERM: forall loc, option_rel (fun _ _ => True) (vs_src loc) (vs_tgt loc))
      (VERS: versions_wf f vers)
  .

  Lemma sim_thread_tgt_read_na
        f vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
        loc to_tgt val_tgt vw_tgt lc_tgt1
        (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt vw_tgt Ordering.na lc_tgt1)
        (SIM: sim_thread
                f vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
    :
      (<<LOCAL: lc_tgt0 = lc_tgt1>>) /\
      (<<VAL: forall val (VAL: vs_tgt loc = Some val), Const.le val_tgt val>>).
  Proof.
  Admitted.

  Lemma sim_thread_tgt_read_na
        f vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
        loc to_tgt val_tgt vw_tgt lc_tgt1
        (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt vw_tgt Ordering.na lc_tgt1)
        (SIM: sim_thread
                f vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
    :
      (<<LOCAL: lc_tgt0 = lc_tgt1>>) /\
      (<<VAL: forall val (VAL: vs_tgt loc = Some val), Const.le val_tgt val>>).
  Proof.
  Admitted.

  | na_read
  | step_silent
  | step_read
  | step_write
  | step_update
  | step_fence
  | step_syscall
  | step_write_na
  | step_racy_read
  | step_failure
  | step_racy_write
  | step_racy_update


  Lemma sim_thread_cap
        f0 vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
        cap_src cap_tgt
        (SIM: sim_thread
                f vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
        (CAPSRC: Memory.cap_tgt mem_src cap_src)
        (CAPTGT: Memory.cap_tgt mem_tgt cap_tgt)
    :
      exists f1,
        (<<MAPLE: Mapping.le f0 f1>>) /\
        (<<MAPWF: Mapping.wf f1>>) /\
        (<<SIM: sim_thread
                  f vers flag_src flag_tgt vs_src vs_tgt
                  mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt>>).


read


  Variant sim_thread
          (f: Mapping.ts) (vers: versions)
          (flag_src: Loc.t -> option Time.t)
          (flag_tgt: Loc.t -> option Time.t)
          (vs: Loc.t -> option (Time.t * Time.t))
          (st_src: lang_src.(Language.state))
          (st_tgt: lang_tgt.(Language.state))
    :
      forall
        (th_src: Thread.t lang_src)
        (th_tgt: Thread.t lang_tgt), Prop :=
  | sim_thread_intro
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (FLAGTGT: forall loc ts (FLAG: flag_tgt loc = Some ts),
          lc_tgt.(Local.tview).(TView.cur).(View.rlx) loc = ts)
      (FLAGSRC: forall loc ts (FLAG: flag_src loc = Some ts),
          lc_tgt.(Local.tview).(TView.cur).(View.rlx) loc = ts)
      (MAX: max_readable


    :
      sim_thread
        f vers flag_src flag_tgt vs st_src st_tgt
        (Thread.mk _ st_src lc_src sc_src mem_src)
        (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
  .

Local.program_step


      (MAX: forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)



Variant sim_promises
        (flag_src: Loc.t -> option Time.t)
        (flag_tgt: Loc.t -> option Time.t)
        (f: Mapping.ts)
        (vers: versions)
        (* (rmap: ReserveMap.t) *)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_promises_intro
    (MESSAGE: forall loc to from msg_tgt
                     (FLAGSRC: flag_src loc = None)
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)),
        exists fto ffrom msg_src,
          (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message_max (flag_tgt loc) f (vers loc to) msg_src msg_tgt>>))
    (SOUND: forall loc fto ffrom msg_src
                   (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)),
        (exists to from msg_tgt,
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
            (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) \/
        (exists vw, (<<FLAG: flag_tgt loc = Some vw>>) /\ (<<TS: msg_src <> Message.reserve -> Time.lt vw fto>>)))
    (NONE: forall loc to ts
                  (FLAGSRC: flag_src loc = Some ts),
        Memory.get loc to prom_src = None)
.



Variant max_readable (mem prom: Memory.t) (loc: Loc.t) (ts: Time.t) (val: Const.t) (released: option View.t): Prop :=



perm, flag, flag

        (vals_src val_tgt: Time.t -> option Time.t)
  :


 flag






  Variant _sim_seq
          (sim_seq:
             forall
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | sim_seq_normal
      (TERMINAL: sim_seq_terminal_case p0 d0 st_src0 st_tgt0)
      (NASTEP: sim_seq_na_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (ATSTEP: sim_seq_at_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (PARTIAL: sim_seq_partial_case p0 d0 st_src0 st_tgt0)
  | sim_seq_failure
      (FAILURE: sim_seq_failure_case p0 d0 st_src0)
  .
