From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import iCompatibility.

Require Import MergeStep.
Require Import ReorderStep.

Require Import ITreeLang.

Set Implicit Arguments.


(* merge load; instr *)

Lemma merge_load_load_sim_itree
      l o:
  sim_itree eq
            (r1 <- ITree.trigger (MemE.read l o);; r2 <- ITree.trigger (MemE.read l o);; Ret (r1, r2))
            (r1 <- ITree.trigger (MemE.read l o);; Ret (r1, r1)).
Proof.
  replace (r1 <- ITree.trigger (MemE.read l o);; r2 <- ITree.trigger (MemE.read l o);; Ret (r1, r2)) with
      (Vis (MemE.read l o) (fun r1 => Vis (MemE.read l o) (fun r2 => Ret (r1, r2)))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1.
      grind. repeat f_equal. extensionality r2. grind. }
  replace (r1 <- ITree.trigger (MemE.read l o);; Ret (r1, r1)) with
      (Vis (MemE.read l o) (fun r1 => Ret (r1, r1))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    exploit sim_local_read; try exact LOCAL0; eauto; try refl. i. des.
    exploit merge_read_read; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * eapply sim_itree_ret; eauto.
      * i. inv PR.
Qed.

Lemma merge_load_store_sim_itree
      l or ow:
  sim_itree eq
            (r1 <- ITree.trigger (MemE.read l or);; ITree.trigger (MemE.write l r1 ow);; Ret r1)
            (ITree.trigger (MemE.update l (MemE.fetch_add 0) or ow)).
Proof.
  replace (r1 <- ITree.trigger (MemE.read l or);; ITree.trigger (MemE.write l r1 ow);; Ret r1) with
      (Vis (MemE.read l or) (fun r1 => Vis (MemE.write l r1 ow) (fun _ => Ret r1))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1.
      grind. repeat f_equal. extensionality r2. grind. }
  replace (ITree.trigger (MemE.update l (MemE.fetch_add 0) or ow)) with
      (Vis (MemE.update l (MemE.fetch_add 0) or ow) (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    clarify. rewrite Const.add_0_r in *.
    exploit sim_local_read; try exact LOCAL; eauto; try refl. i. des.
    assert (VIEWLE: View.opt_le None releasedr) by eauto.
    exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
    exploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
    hexploit sim_local_write; try apply VIEWLE; try exact SC; try exact LOCAL0; eauto; try refl. i. des.
    rewrite SimPromises.unset_bot in *.
    esplits.
    + ss.
    + econs 2; [|econs 1].
      econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 3].
      * econs. ss.
      * eauto.
    + ss.
    + ss.
    + ss.
    + left. eapply paco11_mon.
      * apply sim_itree_ret; eauto.
      * ii. inv PR.
Qed.


(* merge store; instr *)

Lemma merge_store_load_sim_itree
      l
      v1 o1
      o2
      (O: Ordering.le Ordering.seqcst o2 -> Ordering.le Ordering.seqcst o1):
  sim_itree eq
            (ITree.trigger (MemE.write l v1 o1);; ITree.trigger (MemE.read l o2))
            (ITree.trigger (MemE.write l v1 o1);; Ret v1).
Proof.
  replace (ITree.trigger (MemE.write l v1 o1);; ITree.trigger (MemE.read l o2)) with
      (Vis (MemE.write l v1 o1) (fun _ => Vis (MemE.read l o2) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  replace (ITree.trigger (MemE.write l v1 o1);; Ret v1) with
      (Vis (MemE.write l v1 o1) (fun _ => Ret v1)).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* store *)
    hexploit sim_local_write_bot; try exact LOCAL1; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_read; try exact STEP_SRC; eauto using View.bot_spec. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * eapply sim_itree_ret; eauto.
      * i. inv PR.
Qed.

Lemma merge_store_store_sim_itree
      l o
      v1
      v2:
  sim_itree eq
            (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.write l v2 o))
            (ITree.trigger (MemE.write l v2 o)).
Proof.
  replace (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.write l v2 o)) with
      (Vis (MemE.write l v1 o) (fun _ => Vis (MemE.write l v2 o) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  replace (ITree.trigger (MemE.write l v2 o)) with
      (Vis (MemE.write l v2 o) (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write_None; try exact STEP_SRC; eauto; try by viewtac. i. des.
    + esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { ii. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2.
        econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { ii. inv PR. }
Qed.

Lemma merge_store_update_fetch_add_sim_itree
      l o
      v1
      or2
      (ORD: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst o):
  sim_itree eq
            (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.update l (MemE.fetch_add 0) or2 o))
            (ITree.trigger (MemE.write l v1 o);; Ret v1).
Proof.
  replace (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.update l (MemE.fetch_add 0) or2 o)) with
      (Vis (MemE.write l v1 o) (fun _ => Vis (MemE.update l (MemE.fetch_add 0) or2 o) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  replace (ITree.trigger (MemE.write l v1 o);; Ret v1) with
      (Vis (MemE.write l v1 o) (fun r => Ret v1)).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write; try exact STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
    + esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. ss. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read; try exact STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2. econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. s. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read; try apply STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { i. inv PR. }
Qed.

Lemma merge_store_update_cas_sim_itree
      l o
      v1 v2
      or2
      (ORD: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst o):
  sim_itree eq
            (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.update l (MemE.cas v1 v2) or2 o))
            (ITree.trigger  (MemE.write l v2 o);; Ret 1).
Proof.
  replace (ITree.trigger (MemE.write l v1 o);; ITree.trigger (MemE.update l (MemE.cas v1 v2) or2 o)) with
      (Vis (MemE.write l v1 o) (fun _ => Vis (MemE.update l (MemE.cas v1 v2) or2 o) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  replace (ITree.trigger  (MemE.write l v2 o);; Ret 1) with
      (Vis (MemE.write l v2 o) (fun _ => Ret 1)).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write; try exact STEP_SRC; eauto; try by viewtac. i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. ss. des_ifs. }
        { eapply merge_write_read; try exact STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2. econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. ss. des_ifs. }
        { eapply merge_write_read; try apply STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto. etrans; eauto. }
        { i. inv PR. }
Qed.


(* merge update; instr *)

Lemma merge_update_load_sim_itree
      l
      v1 or ow
      or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_itree eq
            (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow);; ITree.trigger (MemE.read l or2))
            (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow)).
Proof.
  replace (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow);; ITree.trigger (MemE.read l or2)) with
      (Vis (MemE.update l (MemE.fetch_add v1) or ow) (fun _ => Vis (MemE.read l or2) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r1. grind. }
  replace (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow)) with
      (Vis (MemE.update l (MemE.fetch_add v1) or ow) (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit merge_write_read; try apply LOCAL2; eauto.
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      rename or into ordr.
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      rename or into ordr.
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto; try by viewtac. i. des.
    hexploit sim_local_write_bot; try apply SC; try apply LOCAL2; eauto; try refl. i. des.
    exploit Local.write_step_future; try apply STEP_SRC; eauto; try by viewtac. i. des.
    exploit sim_local_read; try exact x0; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * apply sim_itree_ret; auto.
      * i. inv PR.
Qed.

Lemma merge_update_store_sim_itree
      l or ow
      v1 v2 v3:
  sim_itree eq
            (r <- ITree.trigger (MemE.update l (MemE.cas v1 v2) or ow);;
             (if (r: Const.t) then Ret tt else ITree.trigger (MemE.write l v3 ow));; Ret r)
            (ITree.trigger (MemE.update l (MemE.cas v1 v3) or ow)).
Proof.
  replace (r <- ITree.trigger (MemE.update l (MemE.cas v1 v2) or ow);;
           (if (r: Const.t) then Ret tt else ITree.trigger (MemE.write l v3 ow));; Ret r) with
      (Vis (MemE.update l (MemE.cas v1 v2) or ow)
           (fun r => if (r: Const.t) then Ret r
                     else Vis (MemE.write l v3 ow) (fun _ => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r. grind.
      repeat f_equal. extensionality u. grind. }
  replace (ITree.trigger (MemE.update l (MemE.cas v1 v3) or ow)) with
      (Vis (MemE.update l (MemE.cas v1 v3) or ow) (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto ; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update fail *)
    des_ifs. exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|eauto]. econs.
      * econs. econs 2. econs; [|econs 2]; try exact STEP_SRC. s.
        econs; eauto. ss. condtac; ss.
      * ss.
    + econs 1.
    + ss.
    + ss.
    + ss.
    + ss. left. eapply paco11_mon.
      * apply sim_itree_ret; eauto.
      * i. inv PR.
  - (* update success *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL2. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
    exploit merge_write_write_None; try exact STEP_SRC0; eauto.
    { inv STEP_SRC. inv MEM_SRC. exploit CLOSED; eauto. i. des.
      inv MSG_TS. ss. }
    i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      exploit reorder_read_promise_diff; try exact STEP_SRC; try exact STEP1; eauto.
      { inv LOCAL2. exploit MemoryFacts.write_time_lt; eauto. ii. inv H.
        eapply Time.lt_strorder. eauto.
      }
      i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs.
          - econs. econs 2. econs; [|econs 4]; try exact STEP4; try exact STEP_SRC0; eauto.
            econs; eauto. ss. condtac; ss.
          - auto.
        }
      * ss. econs 2. econs 2. econs; [|econs 3]; eauto. ss.
        des_ifs; clarify. econs; eauto.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto.
          - etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; eauto.
        { econs.
          - econs. econs 2. econs; [|econs 4]; try exact STEP_SRC; try exact STEP2; eauto.
            econs; eauto. ss. condtac; ss.
          - auto.
        }
      * ss. econs 2. econs 2. econs; [|econs 3]; eauto.
        des_ifs; clarify. econs; eauto.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto.
          - etrans; eauto. }
        { i. inv PR. }
Qed.

Lemma merge_update_update_sim_itree
      l or ow
      v1 v2
      or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_itree eq
            (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow);; ITree.trigger (MemE.update l (MemE.fetch_add v2) or2 ow))
            (ITree.trigger (MemE.update l (MemE.fetch_add (v1 + v2)) or ow)).
Proof.
  replace (ITree.trigger (MemE.update l (MemE.fetch_add v1) or ow);; ITree.trigger (MemE.update l (MemE.fetch_add v2) or2 ow)) with
      (Vis (MemE.update l (MemE.fetch_add v1) or ow)
           (fun _ => Vis (MemE.update l (MemE.fetch_add v2) or2 ow) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r. grind. }
  replace (ITree.trigger (MemE.update l (MemE.fetch_add (v1 + v2)) or ow)) with
      (Vis (MemE.update l (MemE.fetch_add (v1 + v2)) or ow)
           (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto ; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL2. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
    exploit merge_write_write; try exact STEP_SRC0; eauto.
    { inv STEP_SRC. inv MEM_SRC. exploit CLOSED; eauto. i. des.
      inv MSG_TS. ss. }
    i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      exploit reorder_read_promise_diff; try exact STEP_SRC; try exact STEP1; eauto.
      { inv LOCAL2. exploit MemoryFacts.write_time_lt; eauto. ii. inv H.
        eapply Time.lt_strorder. eauto.
      }
      i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 4]; try exact STEP4; try exact STEP_SRC0; eauto.
          - econs; eauto. s. eauto.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. s. rewrite Const.add_assoc. eauto. }
        { eapply merge_write_read; try exact STEP2; viewtac.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            rename or into ordr.
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            rename or into ordr.
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto.
          - rewrite Const.add_assoc. eauto.
          - etrans; eauto.
        }
        { i. inv PR. }
    + inv STEP1.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; eauto.
        econs. econs. econs 2. econs; [|econs 4]; try exact STEP_SRC; try exact STEP2; eauto.
        { econs. econs. s. eauto. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs; eauto. ss. rewrite Const.add_assoc. eauto. }
        { eapply merge_write_read; try exact STEP2; viewtac.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            rename or into ordr.
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            rename or into ordr.
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_itree_ret; eauto.
          - rewrite Const.add_assoc. auto.
          - etrans; eauto.
        }
        { i. inv PR. }
Qed.


(* merge fence; instr *)

Lemma merge_fence_fence_sim_itree
      ordr ordw:
  sim_itree eq
            (ITree.trigger (MemE.fence ordr ordw);; ITree.trigger (MemE.fence ordr ordw))
            (ITree.trigger (MemE.fence ordr ordw)).
Proof.
  replace (ITree.trigger (MemE.fence ordr ordw);; ITree.trigger (MemE.fence ordr ordw)) with
      (Vis (MemE.fence ordr ordw) (fun _ => Vis (MemE.fence ordr ordw) (fun r => Ret r))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r. grind. }
  replace (ITree.trigger (MemE.fence ordr ordw)) with
      (Vis (MemE.fence ordr ordw) (fun r => Ret r)).
  2:{ unfold ITree.trigger. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0]; ss;
    try (dependent destruction STATE); ss; clarify.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit sim_local_fence; try exact LOCAL0; try exact SC; eauto; try refl. i. des.
    exploit merge_fence_fence; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco11_mon.
      * apply sim_itree_ret; eauto. etrans; eauto.
      * ii. inv PR.
Qed.
