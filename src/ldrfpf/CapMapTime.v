Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.
Require Import Mapping.
Require Import CapFlex.
Require Import OrderedTimes.

Require Import LocalPFThread.
Require Import CapMap.
Require Import LocalPFThreadTime.

Set Implicit Arguments.



Section MIDDLE.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).

  Lemma sim_promise_memory_strong_le others self extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt mem_src'
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (PROM: sim_promise_strong L times self extra_self (extra_others \\3// extra_self) prom_src prom_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MEMSTRONG: sim_memory_strong L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt)
    :
      Memory.le prom_src mem_src'.
  Proof.
    ii. exploit MLESRC; eauto. intros GETSRC.
    set (MEM0:=(sim_memory_contents MEM) loc to).
    set (MEM1:=(sim_memory_strong_contents MEMSTRONG) loc to).
    set (PROM0:=(sim_promise_strong_contents PROM) loc to).
    rewrite LHS in PROM0. rewrite GETSRC in *.

    inv PROM0.
    { inv MEM0.
      - rewrite <- H in *. inv MEM1; ss. f_equal. f_equal.
        dup H1. symmetry in H1. eapply MLETGT in H1. rewrite H1 in *. clarify.
        destruct EXTRA; auto.
        set (MEM1:=(sim_memory_contents MEM) loc from_src). inv MEM1; clarify.
        { exfalso. eapply NEXTRA2; eauto. }
        { exfalso. eapply NEXTRA2; eauto. }
        { exfalso. eapply NEXTRA2; eauto. }
        eapply (sim_memory_wf MEM) in H. des.
        dup EXTRA. eapply UNIQUE in EXTRA. clarify.
        exploit memory_get_from_inj.
        { eapply GETSRC. }
        { symmetry. eapply H4. }
        i. des; clarify. exfalso. eapply NEXTRA1; eauto.
      - rewrite <- H in *. inv MEM1; ss. f_equal. f_equal.
        symmetry in H1. eapply MLETGT in H1. rewrite H1 in *. clarify.
      - rewrite <- H in *. inv MEM1; ss.
        + f_equal. f_equal. symmetry in H1. eapply MLETGT in H1. rewrite H1 in *. clarify.
        + f_equal. f_equal. symmetry in H1. eapply MLETGT in H1. rewrite H1 in *. clarify.
    }
    { symmetry in H. rename H into RHS.
      exploit MLETGT; eauto. intros GETTGT. rewrite GETTGT in *.
      inv MEM1. f_equal. f_equal. des; subst; auto.
      { exploit (sim_memory_wf MEM); eauto. i. des.
        exfalso. set (MEM2:=(sim_memory_strong_contents MEMSTRONG) loc from).
        inv MEM2; try by (eapply NEXTRA1; eauto).
        eapply UNIQUE in EXTRA0. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { symmetry. eapply H0. }
        i. des; clarify.
        inv MEM0; ss. eapply NEXTRA1; eauto.
      }
      { exploit (sim_memory_wf MEM); eauto. i. des.
        exfalso. set (MEM2:=(sim_memory_contents MEM) loc from_src).
        inv MEM2; try by (eapply NEXTRA1; eauto).
        eapply UNIQUE in EXTRA. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { eapply GETSRC. }
        i. des; clarify.
        inv MEM0; ss. eapply NEXTRA1; eauto.
      }
      { eapply sim_memory_extra_inj; eauto; ss; eauto.  }
    }
    { symmetry in H. rename H into RHS.
      exploit MLETGT; eauto. intros GETTGT. rewrite GETTGT in *.
      inv MEM0; ss. inv MEM1; ss. f_equal. f_equal. des; subst; auto.
      { exploit (sim_memory_wf MEM); eauto. i. des.
        exfalso. set (MEM2:=(sim_memory_strong_contents MEMSTRONG) loc from).
        inv MEM2; try by (eapply NEXTRA2; eauto).
        eapply UNIQUE in EXTRA0. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { symmetry. eapply H0. }
        i. des; clarify. apply TO. apply TimeFacts.antisym.
        { eapply memory_get_ts_le; eauto. }
        { apply Time.bot_spec. }
      }
      { exploit (sim_memory_wf MEM); eauto. i. des.
        exfalso. set (MEM2:=(sim_memory_contents MEM) loc from_src).
        inv MEM2; try by (eapply NEXTRA2; eauto).
        eapply UNIQUE in EXTRA. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { eapply GETSRC. }
        i. des; clarify. apply TO. apply TimeFacts.antisym.
        { eapply memory_get_ts_le; eauto. }
        { apply Time.bot_spec. }
      }
      { eapply sim_memory_extra_inj; eauto; ss; eauto.  }
    }
    { inv MEM0; ss; try by (exfalso; eapply NEXTRA; right; eauto).
      inv MEM1; ss; try by (exfalso; eapply NEXTRA; right; eauto).
      exploit ((sim_memory_wf MEM) loc from to).
      { right. auto. } i. des.
      eapply UNIQUE in EXTRA0. eapply UNIQUE in EXTRA1. subst. auto.
    }
  Qed.

  Lemma sim_memory_strong_sim_local others self extra_others extra_self
        mem_src mem_tgt lc_src lc_tgt mem_src'
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local L times self extra_self lc_src lc_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (PROM: sim_promise_strong L times self extra_self (extra_others \\3// extra_self)
                                  (Local.promises lc_src) (Local.promises lc_tgt))
        (MEMSTRONG: sim_memory_strong L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt)
    :
      Local.wf lc_src mem_src'.
  Proof.
    econs; ss.
    { eapply LOCALSRC. }
    { eapply concrete_promised_le_closed_tview.
      { eapply concrete_messages_le_concrete_promised_le.
        eapply sim_memory_same_concrete_messages_le.
        { eapply MEM. }
        { eapply sim_memory_strong_sim_memory; eauto. }
      }
      { eapply LOCALSRC. }
    }
    { eapply sim_promise_memory_strong_le; eauto.
      { eapply LOCALSRC. }
      { eapply LOCALTGT. }
    }
    { eapply LOCALSRC. }
    { eapply LOCALSRC. }
  Qed.

End MIDDLE.
