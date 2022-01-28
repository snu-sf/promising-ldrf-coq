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

Require Import JoinedView.
Require Import SeqLift.
Require Import SeqLiftStep.
Require Import gSimulation.
Require Import Simple.

Require Import Pred.


Variant initial_finalized: Messages.t :=
  | initial_finalized_intro
      loc
    :
    initial_finalized loc Time.bot Time.bot Message.elt
.

Lemma configuration_initial_finalized s
  :
  finalized (Configuration.init s) = initial_finalized.
Proof.
  extensionality loc.
  extensionality from.
  extensionality to.
  extensionality msg.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  { inv H. ss. unfold Memory.init, Memory.get in GET.
    rewrite Cell.init_get in GET. des_ifs. }
  { inv H. econs; eauto. i. ss. unfold Threads.init in *.
    rewrite IdentMap.Facts.map_o in TID. unfold option_map in *. des_ifs.
  }
Qed.

Definition initial_mapping: Mapping.t :=
  Mapping.mk
    (fun v ts =>
       if PeanoNat.Nat.eq_dec v 0 then
         if (Time.eq_dec ts Time.bot) then Some (Time.bot)
         else None
       else None)
    0
    (fun _ ts => ts = Time.bot)
.

Definition initial_vers: versions :=
  fun loc ts =>
    if (Time.eq_dec ts Time.bot) then Some (fun _ => 0) else None.

Section LIFT.
  Let world := (Mapping.ts * versions)%type.

  Let world_bot: world := (fun _ => initial_mapping, initial_vers).

  Let world_messages_le (msgs: Messages.t) (w0: world) (w1: world): Prop :=
        let (f0, vers0) := w0 in
        let (f1, vers1) := w1 in
        Mapping.les f0 f1 /\ versions_le vers0 vers1.

  Let sim_memory (b: bool) (w: world) (views: Loc.t -> Time.t -> list View.t)
      (mem_src: Memory.t) (mem_tgt: Memory.t): Prop :=
        let (f, vers) := w in
        sim_memory (fun _ => None) f vers mem_src mem_tgt.

  Let sim_timemap (w: world)
      (tm_src: TimeMap.t) (tm_tgt: TimeMap.t): Prop :=
        let (f, vers) := w in
        sim_timemap (fun _ => True) f (Mapping.vers f) tm_src tm_tgt.

  Let sim_local (w: world) (views: Loc.t -> Time.t -> list View.t) (lc_src: Local.t) (lc_tgt: Local.t): Prop :=
        let (f, vers) := w in
        sim_local f vers (fun _ => None) (fun _ => None) lc_src lc_tgt.



  Lemma world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs).
  Proof.
    ii. econs.
    { ii. red. des_ifs. splits; auto.
      { refl. }
      { refl. }
    }
    { ii. unfold world_messages_le in *. des_ifs. des. splits; auto.
      { etrans; eauto. }
      { etrans; eauto. }
    }
  Qed.

  Lemma sim_local_memory_bot:
    forall w views lc_src lc_tgt
           (SIM: sim_local w views lc_src lc_tgt)
           (BOT: (Local.promises lc_tgt) = Memory.bot),
      (Local.promises lc_src) = Memory.bot.
  Proof.
    ii. unfold sim_local in *. des_ifs. inv SIM. ss. subst.
    inv PROMISES. eapply Memory.ext. ii.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts prom_src) eqn:EQ; auto. destruct p.
    hexploit SOUND; eauto. i. des; ss. rewrite Memory.bot_get in GET. ss.
  Qed.

  Lemma world_messages_le_mon:
    forall msgs0 msgs1 w0 w1
           (LE: world_messages_le msgs1 w0 w1)
           (MSGS: msgs0 <4= msgs1),
      world_messages_le msgs0 w0 w1.
  Proof.
    unfold world_messages_le. ii. des_ifs.
  Qed.

  Lemma sim_lift_gsim lang_src lang_tgt sim_terminal
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (SIM: @sim_seq_all _ _ sim_terminal st_src st_tgt)
    :
    @sim_thread_past
      world world_messages_le sim_memory sim_timemap sim_local
      lang_src lang_tgt sim_terminal false world_bot st_src Local.init TimeMap.bot Memory.init st_tgt Local.init TimeMap.bot Memory.init (JConfiguration.init_views, initial_finalized).
  Proof.
  Admitted.
End LIFT.
