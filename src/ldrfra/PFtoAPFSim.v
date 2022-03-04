Require Import Lia.
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

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import MemoryMerge.
Require Import MemoryReorder.
Require Import Cover.
Require Import MemoryProps.

Require Import PFStep.
Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.

Set Implicit Arguments.


Module PFtoAPFSim.
  Section PFtoAPFSim.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Variant sim_memory (rels: Writes.t) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (EQ: forall loc (LOC: ~ L loc), mem_src loc = mem_tgt loc)
        (COVER: forall loc ts, covered loc ts mem_src -> covered loc ts mem_tgt)
        (SOUND: forall loc from to msg
                  (GET_SRC: Memory.get loc to mem_src = Some (from, msg))
                  (RESERVE: msg <> Message.reserve),
            (<<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)>>))
        (COMPLETE: forall loc ts from to msg
                     (LOC: L loc) (LE: Time.le ts to)
                     (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg))
                     (RESERVE: msg <> Message.reserve),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>) \/
            exists from' to' val ord,
              (<<IN: List.In (loc, to', ord) rels>>) /\
              (<<LT: Time.lt ts to'>>) /\
              (<<ORD: Ordering.le ord Ordering.na>>) /\
              (<<GET_SRC: Memory.get loc to' mem_src = Some (from', Message.concrete val None)>>))
        (UNDEF: forall loc from to msg
                  (LOC: L loc)
                  (GET: Memory.get loc to mem_src = Some (from, msg)),
            msg <> Message.undef)
    .
    Hint Constructors sim_memory.

    Inductive sim_statelocal (rels: Writes.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: lc_src = lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal.

    Inductive sim_thread (rels: Writes.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: (Thread.state e_src) = (Thread.state e_tgt))
        (LOCAL: (Thread.local e_src) = (Thread.local e_tgt))
        (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
        (MEMORY: sim_memory rels (Thread.memory e_src) (Thread.memory e_tgt))
    .
    Hint Constructors sim_thread.

    Lemma sim_thread_promise_consistent
          rels e_src e_tgt
          (SIM: sim_thread rels e_src e_tgt)
          (CONS: Local.promise_consistent (Thread.local e_tgt)):
      Local.promise_consistent (Thread.local e_src).
    Proof.
      inv SIM. rewrite LOCAL in *. ss.
    Qed.

    Lemma sim_memory_cons
          a rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (a :: rels) mem_src mem_tgt.
    Proof.
      inv MEM. econs; eauto. i.
      exploit COMPLETE; eauto. i. des; eauto.
      right. esplits; eauto. econs 2. ss.
    Qed.

    Lemma sim_memory_append
          e rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (Writes.append L e rels) mem_src mem_tgt.
    Proof.
      unfold Writes.append.
      destruct e; ss; condtac; ss; apply sim_memory_cons; ss.
    Qed.

    Lemma sim_memory_app
          rels' rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (rels' ++ rels) mem_src mem_tgt.
    Proof.
      inv MEM. econs; eauto. i.
      exploit COMPLETE; eauto. i. des; eauto.
      right. esplits; eauto.
      apply List.in_or_app. eauto.
    Qed.

    Lemma well_ordered mem:
      forall loc ts,
      (forall to (LT: Time.lt ts to), Memory.get loc to mem = None) \/
      (exists to from msg,
          (<<TO: Time.lt ts to>>) /\
          (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
          (<<MIN: forall to' (LT1: Time.lt ts to') (LT2: Time.lt to' to),
              Memory.get loc to' mem = None>>)).
    Proof.
      i. specialize (Cell.finite (mem loc)). i. des.
      cut ((forall to (IN: List.In to dom) (LT: Time.lt ts to), Memory.get loc to mem = None) \/
           (exists to from msg,
               (<<IN: List.In to dom>>) /\
               (<<TO: Time.lt ts to>>) /\
               (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
               (<<MIN: forall to' (IN: List.In to' dom)
                         (LT1: Time.lt ts to') (LT2: Time.lt to' to),
                   Memory.get loc to' mem = None>>))).
      { i. des.
        - left. i.
          destruct (Memory.get loc to mem) as [[]|] eqn:GET; ss.
          exploit H; eauto. i.
          exploit H0; eauto. i. congr.
        - right. esplits; eauto. i.
          destruct (Memory.get loc to' mem) as [[]|] eqn:GET'; ss.
          exploit H; try eapply GET'. i.
          exploit MIN; try exact x; eauto. i. congr.
      }
      clear H. induction dom; try by (left; ss). des.
      - destruct (TimeFacts.le_lt_dec a ts).
        { left. i. inv IN; eauto. timetac. }
        destruct (Memory.get loc a mem) as [[]|] eqn:GETA; cycle 1.
        { left. i. inv IN; eauto. }
        right. esplits; eauto; ss; eauto. i. des; timetac.
      - right.
        destruct (TimeFacts.le_lt_dec a ts).
        { esplits; try exact GET; ss; eauto. i. des; eauto. subst. timetac. }
        destruct (TimeFacts.le_lt_dec to a).
        { esplits; try exact GET; ss; eauto. i. des; eauto. subst. timetac. }
        destruct (Memory.get loc a mem) as [[]|] eqn:GETA; cycle 1.
        { esplits; try exact GET; ss; eauto. i. des; eauto. subst. ss. }
        esplits; try exact GETA; ss; eauto. i. des; eauto. subst. timetac.
    Qed.

    Lemma promise
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (MSG: L loc -> msg <> Message.undef)
          (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
      exists mem2_src,
        <<PROMISE_SRC: Memory.promise promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv MEM1. inv PROMISE_TGT; ss.
      { (* add *)
        exploit (@Memory.add_exists mem1_src loc from to msg).
        { eapply covered_disjoint; eauto.
          inv MEM. inv ADD. eauto.
        }
        { inv MEM. inv ADD. ss. }
        { inv MEM. inv ADD. ss. }
        i. des. esplits.
        { econs; eauto. i.
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. inv MEM. inv ADD. inv TO. }
          specialize (well_ordered mem1_tgt loc to). i. des.
          { exploit (COVER loc to').
            { econs; eauto. econs; ss. refl. }
            i. inv x2. inv ITV. ss.
            rewrite H in GET0; ss.
            eapply TimeFacts.lt_le_lt; eauto.
          }
          exploit Memory.get_ts; try exact GET0. i. des.
          { subst. inv TO. }
          destruct (TimeFacts.le_lt_dec to from0); cycle 1.
          { exploit Memory.add_get1; try exact GET0; eauto. i.
            exploit Memory.add_get0; try exact MEM. i. des.
            exploit Memory.get_disjoint; [exact x3|exact GET2|]. i. des.
            { subst. timetac. }
            apply (x4 to); econs; ss; try refl.
            - econs. ss.
            - inv MEM. inv ADD. ss.
          }
          inv l; cycle 1.
          { inv H. eapply ATTACH; eauto. }
          cut (exists from1 to1 msg1,
                  Memory.get loc to1 mem1_tgt = Some (from1, msg1) /\
                  Time.lt from1 from0 /\ Time.lt to to1).
          { i. des.
            destruct (TimeFacts.le_lt_dec to0 to1).
            - exploit Memory.get_disjoint; [exact GET0|exact H0|]. i. des; timetac.
              apply (x3 to0); econs; ss; try refl. etrans; eauto.
            - rewrite MIN in H0; ss.
          }
          destruct (TimeFacts.le_lt_dec to' from0).
          { exploit (COVER loc to').
            { econs; eauto. econs; ss. refl. }
            i. inv x3. inv ITV. ss.
            esplits; try exact GET1.
            - eapply TimeFacts.lt_le_lt; eauto.
            - exploit Memory.get_ts; try exact GET1. i. des; subst; timetac.
              eapply TimeFacts.lt_le_lt; try exact TO0. ss.
          }
          { exploit (@Time.middle_spec to from0); ss. i. des.
            exploit (COVER loc (Time.middle to from0)).
            { econs; eauto. econs; ss. econs. etrans; eauto. }
            i. inv x5. inv ITV. ss.
            esplits; try exact GET1.
            - etrans; try exact FROM; ss.
            - eapply TimeFacts.lt_le_lt; try exact x3. ss.
          }
        }
        econs; i.
        - apply Cell.ext. i.
          replace (Cell.get ts (mem2 loc0)) with (Memory.get loc0 ts mem2) by ss.
          replace (Cell.get ts (mem2_tgt loc0)) with (Memory.get loc0 ts mem2_tgt) by ss.
          erewrite (@Memory.add_o mem2); try exact x0.
          erewrite (@Memory.add_o mem2_tgt); try exact MEM.
          unfold Memory.get. rewrite EQ; ss.
        - rewrite add_covered in H; try exact x0.
          rewrite add_covered; try exact MEM.
          des; eauto.
        - erewrite Memory.add_o; eauto.
          revert GET_SRC. erewrite Memory.add_o; try exact x0.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.add_o; try exact MEM.
          condtac; ss.
          + i. des. clarify.
            exploit Memory.add_get0; try exact x0. i. des. eauto.
          + guardH o. i. exploit COMPLETE; eauto. i. des.
            * exploit Memory.add_get1; try exact GET_SRC; eauto.
            * exploit Memory.add_get1; try exact GET_SRC; eauto. i.
              right. esplits; try exact x1; eauto.
        - revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. clarify. eauto.
      }

      { (* split *)
        exploit Memory.split_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; i.
        - apply Cell.ext. i.
          replace (Cell.get ts (mem2 loc0)) with (Memory.get loc0 ts mem2) by ss.
          replace (Cell.get ts (mem2_tgt loc0)) with (Memory.get loc0 ts mem2_tgt) by ss.
          erewrite (@Memory.split_o mem2); try exact x0.
          erewrite (@Memory.split_o mem2_tgt); try exact MEM.
          unfold Memory.get. rewrite EQ; ss.
        - rewrite split_covered in H; try exact x0.
          rewrite split_covered; try exact MEM. eauto.
        - erewrite Memory.split_o; eauto.
          revert GET_SRC. erewrite Memory.split_o; try exact x0.
          repeat condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.split_o; try exact MEM.
          repeat condtac; ss.
          + i. des. clarify.
            exploit Memory.split_get0; try exact x0. i. des. eauto.
          + guardH o. i. des. clarify.
            exploit Memory.split_get0; try exact x0. i. des. eauto.
          + guardH o. guardH o0.
            i. exploit COMPLETE; eauto. i. des.
            * left. erewrite Memory.split_o; eauto. repeat condtac; ss; congr.
            * exploit Memory.split_get1; try exact GET_SRC; eauto. i. des.
              right. esplits; eauto.
        - revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + i. des. clarify. eauto.
          + guardH o. ii. des. clarify.
            exploit Memory.split_get0; try exact x0. i. des.
            eapply UNDEF; eauto.
      }

      { (* lower *)
        exploit Memory.lower_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; i.
        - apply Cell.ext. i.
          replace (Cell.get ts (mem2 loc0)) with (Memory.get loc0 ts mem2) by ss.
          replace (Cell.get ts (mem2_tgt loc0)) with (Memory.get loc0 ts mem2_tgt) by ss.
          erewrite (@Memory.lower_o mem2); try exact x0.
          erewrite (@Memory.lower_o mem2_tgt); try exact MEM.
          unfold Memory.get. rewrite EQ; ss.
        - erewrite lower_covered in H; try exact x0.
          erewrite lower_covered; try exact MEM. eauto.
        - erewrite Memory.lower_o; eauto.
          revert GET_SRC. erewrite Memory.lower_o; try exact x0.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.lower_o; try exact MEM.
          condtac; ss.
          + i. des. clarify.
            exploit Memory.lower_get0; try exact x0. i. des. eauto.
          + guardH o. i. exploit COMPLETE; eauto. i. des.
            * left. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            * exploit Memory.lower_get1; try exact GET_SRC; eauto. i. des.
              inv MSG_LE. inv RELEASED.
              right. esplits; eauto.
        - revert GET. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          i. des. clarify. eauto.
      }

      { (* remove *)
        exploit Memory.remove_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; i.
        - apply Cell.ext. i.
          replace (Cell.get ts (mem2 loc0)) with (Memory.get loc0 ts mem2) by ss.
          replace (Cell.get ts (mem2_tgt loc0)) with (Memory.get loc0 ts mem2_tgt) by ss.
          erewrite (@Memory.remove_o mem2); try exact x0.
          erewrite (@Memory.remove_o mem2_tgt); try exact MEM.
          unfold Memory.get. rewrite EQ; ss.
        - erewrite remove_covered in H; try exact x0.
          erewrite remove_covered; try exact MEM. des; eauto.
        - erewrite Memory.remove_o; eauto.
          revert GET_SRC. erewrite Memory.remove_o; try exact x0.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.remove_o; try exact MEM.
          condtac; ss.
          guardH o. i. exploit COMPLETE; eauto. i. des.
          + left. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          + exploit Memory.remove_get1; try exact GET_SRC; eauto. i. des.
            { subst. exploit Memory.remove_get0; try exact x0. i. des. congr. }
            right. esplits; eauto.
        - revert GET. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      }
    Qed.

    Lemma write
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (MSG: L loc -> msg <> Message.undef)
          (WRITE_TGT: Memory.write promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
      exists mem2_src,
        <<WRITE_SRC: Memory.write promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv WRITE_TGT.
      exploit promise; eauto; try apply MEM1_SRC. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_other
          rels mem1_src
          ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (LOC: ~ L loc)
          (WRITE_TGT: Memory.write_na ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind):
      exists mem2_src,
        <<WRITE_SRC: Memory.write_na ts promises1 mem1_src loc from to val promises2 mem2_src msgs kinds kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      revert mem1_src MEM1 LE1_SRC.
      induction WRITE_TGT; i.
      { exploit write; eauto. i. des. eauto. }
      exploit write; eauto. i. des.
      hexploit Memory.write_le; try exact WRITE_SRC; eauto. i.
      exploit IHWRITE_TGT; try exact MEM2; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma write_add_memory_add
          promises1 mem1 loc from to msg promises2 mem2
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 Memory.op_kind_add):
      (<<PROMISES: promises2 = promises1>>) /\
      (<<ADD: Memory.add mem1 loc from to msg mem2>>).
    Proof.
      inv WRITE. inv PROMISE. splits; ss.
      exploit MemoryMerge.add_remove; try exact PROMISES; eauto.
    Qed.

    Lemma reorder_add_write_add
          promises0 mem0 loc from1 to1 msg1 mem1
          from2 to2 msg2 promises2 mem2
          (ADD: Memory.add mem0 loc from1 to1 msg1 mem1)
          (WRITE: Memory.write promises0 mem1 loc from2 to2 msg2 promises2 mem2 Memory.op_kind_add):
      exists mem1',
        (<<WRITE: Memory.write promises0 mem0 loc from2 to2 msg2 promises2 mem1' Memory.op_kind_add>>) /\
        (<<ADD: Memory.add mem1' loc from1 to1 msg1 mem2>>).
    Proof.
      inv WRITE. inv PROMISE.
      exploit MemoryReorder.add_add; [exact ADD|exact MEM|]. i. des.
      exploit MemoryMerge.add_remove; [exact PROMISES|exact REMOVE|]. i. subst.
      esplits; try exact ADD2.
      econs; [econs; eauto|]; eauto. i.
      exploit Memory.add_get1; try exact ADD; eauto.
    Qed.

    Lemma reorder_write_write_na
          promises0 mem0 loc from1 to1 msg1 promises1 mem1 kind1
          ts from2 to2 val2 promises2 mem2 msgs2 kinds2 kind2
          (RESERVE_ONLY: OrdLocal.reserve_only L promises0)
          (LOC: L loc)
          (WRITE: Memory.write promises0 mem0 loc from1 to1 msg1 promises1 mem1 kind1)
          (WRITE_NA: Memory.write_na ts promises1 mem1 loc from2 to2 val2 promises2 mem2 msgs2 kinds2 kind2):
      exists mem1',
        (<<WRITE_NA: Memory.write_na ts promises0 mem0 loc from2 to2 val2 promises2 mem1' msgs2 kinds2 kind2>>) /\
        (<<ADD: Memory.add mem1' loc from1 to1 msg1 mem2>>).
    Proof.
      exploit OrdLocal.reserve_only_write_add; eauto. i. subst.
      exploit write_add_memory_add; eauto. i. des. subst.
      clear WRITE. revert ts mem0 mem1 promises2 mem2 kinds2 ADD WRITE_NA.
      induction msgs2 as [|[to' msg'] msgs]; i.
      { inv WRITE_NA.
        exploit OrdLocal.reserve_only_write_add; eauto. i. subst.
        exploit reorder_add_write_add; eauto. i. des.
        esplits; eauto.
      }
      inv WRITE_NA.
      hexploit OrdLocal.write_reserve_only; try exact WRITE_EX; eauto. i.
      exploit OrdLocal.reserve_only_write_add; try exact WRITE_EX; eauto. i. subst.
      exploit reorder_add_write_add; try exact ADD; eauto. i. des.
      exploit write_add_memory_add; try exact WRITE_EX. i. des. subst. clear ADD1.
      exploit IHmsgs; try exact ADD0; try exact WRITE_NA0. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_loc
          rels mem1_src
          ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind
          ord
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY: OrdLocal.reserve_only L promises1)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (LOC: L loc)
          (ORD: Ordering.le ord Ordering.na)
          (WRITE_TGT: Memory.write_na ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind):
      exists mem2_src,
        (<<WRITE_SRC: Memory.write promises1 mem1_src loc from to (Message.concrete val None) promises2 mem2_src kind>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>).
    Proof.
      revert ts mem1_tgt promises2 mem2_tgt kinds MEM1 WRITE_TGT.
      induction msgs as [|[to' msg'] msgs]; i.
      { inv WRITE_TGT.
        exploit write; eauto; ss. i. des.
        esplits; eauto using sim_memory_cons.
      }
      inv WRITE_TGT.
      exploit OrdLocal.reserve_only_write_add; try exact WRITE_EX; eauto. i. subst.
      exploit reorder_write_write_na; eauto. i. des.
      exploit IHmsgs; try exact WRITE_NA0; eauto. i. des.
      esplits; eauto.
      exploit Memory.write_na_times; try exact WRITE_NA. i. des.
      clear - ORD LOC MSG_EX ADD MEM2 WRITE_SRC x1.
      inv MEM2. econs; i.
      - rewrite EQ; ss.
        apply Cell.ext. i.
        replace (Cell.get ts (mem2_tgt loc0)) with (Memory.get loc0 ts mem2_tgt) by ss.
        erewrite (@Memory.add_o mem2_tgt); eauto.
        condtac; ss. des; subst; ss.
      - erewrite add_covered; try exact ADD. eauto.
      - exploit SOUND; eauto. i. des.
        exploit Memory.add_get1; try exact x; eauto.
      - i. revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; ss; eauto. i. des. clarify.
        exploit Memory.write_get2; try exact WRITE_SRC. i. des.
        right. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
      - exploit Memory.write_get_inv; try exact GET; eauto.
    Qed.

    Lemma promise_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
          (MSG1: forall promises2_src mem2_src
                   (PROMISE: Memory.promise (Local.promises lc1_src) mem1_src loc from to msg promises2_src mem2_src kind),
              Memory.closed_message msg mem2_src)
          (MSG2: L loc -> msg <> Message.undef):
      exists lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit promise; try exact MEM; eauto; try apply WF1_SRC; try apply MEM1_SRC. i. des.
      esplits; eauto.
    Qed.

    Lemma read_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released ord lc2_tgt
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_MEM1: Normal.normal_memory L mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      (exists lc2_src,
          (<<STEP_SRC: OrdLocal.read_step L Ordering.na lc1_src mem1_src loc to val released ord lc2_src>>) /\
          (<<LC2: lc2_src = lc2_tgt>>) /\
          (<<NORMAL_TVIEW2: Normal.normal_tview L (Local.tview lc2_src)>>)) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv MEM1. inv STEP_TGT.
      destruct (classic (Memory.get loc to mem1_src =
                         Some (from, Message.concrete val' released))) eqn:GET_SRC; cycle 1.
      { (* race *)
        destruct (L loc) eqn:LOC; cycle 1.
        { unfold Memory.get in GET. rewrite <- EQ in GET; ss. rewrite LOC. ss. }
        inv READABLE. inv NORMAL_TVIEW1.
        exploit COMPLETE; eauto; ss. i. des; try congr.
        right. unfold RARaceW.wr_race.
        esplits; try exact ORD0; eauto.
        rewrite CUR; ss.
      }
      destruct (classic (L loc /\ Ordering.le ord Ordering.plain /\
                         Time.lt (View.rlx (TView.cur (Local.tview lc1_tgt)) loc) to)).
      { (* race *)
        right. des. unfold RARaceW.wr_race.
        inv WRITES1. exploit COMPLETE0; try exact GET_SRC; eauto.
        { ii. subst. inv H1. }
        i. des.
        esplits; eauto.
      }
      left. esplits.
      - econs; eauto. rewrite OrdLocal.ordc_na; ss. eauto.
      - ss.
      - exploit Normal.read_step; try exact WF1_SRC; eauto. i.
        inv READABLE. inv NORMAL_TVIEW1. rewrite CUR in *; ss.
        inv PLN; ss.
        exfalso. apply H. splits; ss.
    Qed.

    Lemma write_step
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm released ord lc2_tgt sc2_tgt mem2_tgt kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val
                                      releasedm released ord lc2_tgt sc2_tgt mem2_tgt kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.plain
                                         lc1_src sc1_src mem1_src loc from to val
                                         releasedm released ord lc2_src sc2_src mem2_src kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write; try exact MEM1; eauto; try apply WF1_SRC; ss. i. des.
      esplits; eauto.
      econs; eauto. econs; eauto; try (condtac; ss).
      - unfold TView.write_released.
        repeat condtac; destruct ord; ss.
      - inv WRITABLE. econs. ss.
      - destruct ord; ss.
      - f_equal. unfold TView.write_released.
        repeat condtac; destruct ord; ss.
    Qed.

    Lemma write_na_step_other
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val ord lc2_tgt sc2_tgt mem2_tgt msgs kinds kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1_tgt mem1_tgt loc from to val ord
                                         lc2_tgt sc2_tgt mem2_tgt msgs kinds kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: Local.write_na_step lc1_src sc1_src mem1_src loc from to val ord
                                         lc2_src sc2_src mem2_src msgs kinds kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write_na_other; eauto; try apply WF1_SRC. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_step_loc
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val ord lc2_tgt sc2_tgt mem2_tgt msgs kinds kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (LOC: L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1_tgt mem1_tgt loc from to val ord
                                         lc2_tgt sc2_tgt mem2_tgt msgs kinds kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_na_step L Ordering.plain
                                            lc1_src sc1_src mem1_src loc from to val ord
                                            lc2_src sc2_src mem2_src [] [] kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write_na_loc; try exact MEM1; eauto; try apply WF1_SRC. i. des.
      esplits; eauto. econs 2; eauto.
      destruct (L loc); ss. econs; eauto.
      - exploit Memory.write_na_times; eauto. i. des.
        econs; eauto.
      - unfold TView.write_released. condtac; eauto.
        destruct ord; ss.
      - destruct ord; ss.
      - f_equal.
        unfold TView.write_tview. f_equal.
        repeat condtac; ss; destruct ord; ss.
    Qed.

    Lemma is_racy
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc to ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: Local.is_racy lc1_src mem1_src loc to ord>>) \/
      __guard__ (
          exists to ordw,
            (<<LOC: L loc>>) /\
            (<<HIGHER: Time.lt (View.rlx (TView.cur (Local.tview lc1_src)) loc) to>>) /\
            (<<IN: List.In (loc, to, ordw) rels>>) /\
            ((<<ORDW: Ordering.le ordw Ordering.na>>) \/
             (<<ORD: Ordering.le ord Ordering.na>>))).
    Proof.
      inv MEM1. inv STEP_TGT.
      destruct (L loc) eqn:LOC; cycle 1.
      { unfold Memory.get in GET. rewrite <- EQ in *; try congr.
        left. splits; eauto.
      }
      right. unguard.
      inv NORMAL_TVIEW1. rewrite CUR; try congr.
      exploit COMPLETE; eauto.
      { econs. eauto. }
      i. des.
      - hexploit UNDEF; eauto. i. destruct msg; ss.
        inv WRITES1. exploit COMPLETE0; eauto.
        { ii. subst. inv RACE. }
        i. des.
        esplits; eauto.
        destruct ord; eauto; exploit MSG2; ss.
      - esplits; eauto.
    Qed.

    Lemma racy_read_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc to val ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: OrdLocal.racy_read_step L Ordering.na lc1_src mem1_src loc to val ord>>) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - left. splits; ss. econs; eauto. rewrite OrdLocal.ordc_na; ss.
      - right. unfold RARaceW.wr_race.
        unguard; des; esplits; eauto.
    Qed.

    Lemma racy_write_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_write_step lc1_tgt mem1_tgt loc to ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: OrdLocal.racy_write_step L Ordering.plain lc1_src mem1_src loc to ord>>) \/
      (<<RACE: RARaceW.ww_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - left. splits; ss. econs; eauto. condtac; ss.
      - right. unfold RARaceW.ww_race.
        unguard. des; esplits; eauto.
    Qed.

    Lemma racy_update_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ordr ordw
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc to ordr ordw):
      ((<<LOC: ~ L loc>>) \/ (<<ORDR: Ordering.le ordr Ordering.na>>) \/ (<<ORDW: Ordering.le ordw Ordering.na>>)) /\
      (<<STEP_SRC: Local.racy_update_step lc1_src mem1_src loc to ordr ordw>>) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ordr>>).
    Proof.
      inv STEP_TGT; try by left; splits; eauto.
      exploit is_racy; eauto. i. des.
      - left. eauto.
      - right. unfold RARaceW.wr_race.
        unguard. des; esplits; eauto.
    Qed.

    Variant sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
    | sim_event_promise
        loc from to msg kind:
        sim_event (ThreadEvent.promise loc from to msg kind)
                  (ThreadEvent.promise loc from to msg kind)
    | sim_event_silent:
        sim_event ThreadEvent.silent ThreadEvent.silent
    | sim_event_read
        loc to val released ord:
        sim_event (ThreadEvent.read loc to val released ord)
                  (ThreadEvent.read loc to val released ord)
    | sim_event_write
        loc from to val released ord:
        sim_event (ThreadEvent.write loc from to val released ord)
                  (ThreadEvent.write loc from to val released ord)
    | sim_event_write_na
        loc msgs_src msgs_tgt from to val ord:
        sim_event (ThreadEvent.write_na loc msgs_src from to val ord)
                  (ThreadEvent.write_na loc msgs_tgt from to val ord)
    | sim_event_update
        loc from to valr valw releasedm released ordr ordw:
        sim_event (ThreadEvent.update loc from to valr valw releasedm released ordr ordw)
                  (ThreadEvent.update loc from to valr valw releasedm released ordr ordw)
    | sim_event_fence
        ordr ordw:
        sim_event (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
    | sim_event_syscall
        e:
        sim_event (ThreadEvent.syscall e) (ThreadEvent.syscall e)
    | sim_event_failure:
      sim_event ThreadEvent.failure ThreadEvent.failure
    | sim_event_racy_read
        loc to val ord:
      sim_event (ThreadEvent.racy_read loc to val ord)
                (ThreadEvent.racy_read loc to val ord)
    | sim_event_racy_write
        loc to val ord:
      sim_event (ThreadEvent.racy_write loc to val ord)
                (ThreadEvent.racy_write loc to val ord)
    | sim_event_racy_update
        loc to valr valw ordr ordw:
      sim_event (ThreadEvent.racy_update loc to valr valw ordr ordw)
                (ThreadEvent.racy_update loc to valr valw ordr ordw)
    .
    Hint Constructors sim_event.

    Lemma sim_event_eq_program_event
          e_src e_tgt
          (SIM: sim_event e_src e_tgt):
      ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
    Proof.
      inv SIM; ss.
    Qed.

    Lemma program_step
          rels lc1_src sc1_src mem1_src
          e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_MEM1: Normal.normal_memory L mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
          (MEM1_SRC: Memory.closed mem1_src)
          (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt):
      (exists e_src lc2_src sc2_src mem2_src,
          (<<STEP_SRC: OrdLocal.program_step L Ordering.na Ordering.plain 
                                             e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>>) /\
          (<<EVENT: sim_event e_src e_tgt>>) /\
          (<<RACY_READ: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_read loc to val ord), ~ L loc>>) /\
          (<<RACY_WRITE: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_write loc to val ord), ~ L loc>>) /\
          (<<RACY_UPDATE: forall loc to valr valw ordr ordw
                            (EVENT: e_tgt = ThreadEvent.racy_update loc to valr valw ordr ordw),
              ~ L loc \/ Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na>>) /\
          (<<LC2: lc2_src = lc2_tgt>>) /\
          (<<SC2: sc2_src = sc2_tgt>>) /\
          (<<MEM2: sim_memory (Writes.append L e_src rels) mem2_src mem2_tgt>>) /\
          (<<NORMAL_TVIEW2: Normal.normal_tview L (Local.tview lc2_src)>>) /\
          (<<NORMAL_MEM2: Normal.normal_memory L mem2_src>>)) \/
      (<<RACE: RARaceW.ra_race L rels (Local.tview lc1_src) (ThreadEvent.get_program_event e_tgt)>>).
    Proof.
      inv STEP_TGT.
      - left. esplits; eauto; ss. econs.
      - exploit read_step; eauto. i. des.
        + left. esplits; eauto; ss. econs. ss.
        + right. left. ss. esplits; eauto.
      - exploit write_step; eauto. i. des.
        dup STEP_SRC. inv STEP_SRC0.
        exploit Normal.write_step; try exact STEP; eauto; ss. i. des.
        left. esplits; [econs 3|..]; eauto; ss.
        eapply sim_memory_append; eauto.
      - exploit read_step; eauto. i. des; cycle 1.
        { right. left. esplits; ss; eauto. }
        dup STEP_SRC. inv STEP_SRC0.
        exploit Local.read_step_future; try exact STEP; eauto. i. des.
        exploit write_step; eauto. i. des.
        dup STEP_SRC0. inv STEP_SRC1.
        exploit Normal.write_step; try exact STEP0; eauto.
        { inv STEP. destruct releasedr; ss. eauto. }
        i. des.
        left. esplits; [econs 4|..]; eauto; ss.
        eapply sim_memory_append; eauto.
      - left. esplits; [econs 5|..]; eauto; ss.
        exploit Normal.fence_step; eauto.
      - left. esplits; [econs 6|..]; eauto; ss.
        exploit Normal.fence_step; eauto.
      - left. esplits; [econs 7|..]; eauto; ss.
      - destruct (L loc) eqn:LOC.
        + exploit write_na_step_loc; try exact LOCAL; eauto. i. des.
          exploit (@Normal.ord_program_step L Ordering.na Ordering.plain);
            try econs 8; eauto; ss. i. des.
          left. esplits; [econs 8|..]; eauto; ss.
          unfold Writes.append. ss. condtac; ss.
        + exploit write_na_step_other; try exact LOCAL; eauto; try congr. i. des.
          exploit Normal.write_na_step; try exact STEP_SRC; eauto. i. des.
          left. esplits; [econs 8| | | |M|..]; eauto; ss.
          * econs; eauto. condtac; ss. eauto.
          * unfold Writes.append. ss. condtac; ss.
      - exploit racy_read_step; try exact LOCAL; eauto. i. des.
        + left. esplits; [econs 9|..]; eauto; ss. i. clarify.
        + right. left. esplits; ss; eauto.
      - exploit racy_write_step; try exact LOCAL; eauto. i. des.
        + left. esplits; [econs 10|..]; eauto; ss. i. clarify.
        + right. right. esplits; ss; eauto.
      - exploit racy_update_step; try exact LOCAL; eauto. i. inv x0.
        + left. esplits; [econs 11|..]; eauto; ss.
          * des; eauto.
          * i. clarify. des; eauto.
        + right. left. esplits; ss; eauto.
    Qed.

    Lemma thread_step
          rels e1_src e1_tgt
          pf e_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (PROMISE: forall loc from to msg kind
                      (EVENT: e_tgt = ThreadEvent.promise loc from to msg kind),
              L loc /\ msg = Message.reserve)
          (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
      (exists e_src e2_src,
          (<<STEP_SRC: OrdThread.step L Ordering.na Ordering.plain pf e_src e1_src e2_src>>) /\
          (<<EVENT: sim_event e_src e_tgt>>) /\
          (<<RACY_READ: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_read loc to val ord), ~ L loc>>) /\
          (<<RACY_WRITE: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_write loc to val ord), ~ L loc>>) /\
          (<<RACY_UPDATE: forall loc to valr valw ordr ordw
                            (EVENT: e_tgt = ThreadEvent.racy_update loc to valr valw ordr ordw),
              ~ L loc \/ Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na>>) /\
          (<<SIM2: sim_thread (Writes.append L e_src rels) e2_src e2_tgt>>) /\
          (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>)) \/
      (<<RACE: RARaceW.ra_race L rels (Local.tview (Thread.local e1_src)) (ThreadEvent.get_program_event e_tgt)>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv NORMAL1_SRC. ss.
      inv STEP_TGT.
      { inv STEP. ss.
        exploit PROMISE; eauto. i. des. subst.
        exploit promise_step; try exact LOCAL; eauto; ss. i. des. subst.
        left. esplits.
        - econs 1; [econs|]; eauto. ii. clarify.
        - ss.
        - ss.
        - ss.
        - ss.
        - ss.
        - exploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
          econs; eauto.
      }
      inv STEP.
      exploit program_step; try exact LOCAL; eauto; ss. i. des; eauto.
      subst. left. esplits.
      - econs 2. econs; [|eauto]. inv EVENT; eauto.
      - ss.
      - ss.
      - ss.
      - ss.
      - ss.
      - ss.
    Qed.

    Lemma reserve_step
          rels e1_src e1_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
          (STEP_TGT: Thread.reserve_step e1_tgt e2_tgt):
      exists e2_src,
        (<<STEP_SRC: Thread.reserve_step e1_src e2_src>>) /\
        (<<SIM2: sim_thread rels e2_src e2_tgt>>) /\
        (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv NORMAL1_SRC. ss.
      inv STEP_TGT. inv STEP; inv STEP0; [|inv LOCAL].
      exploit promise_step; try exact LOCAL; eauto; ss. i. des.
      exploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      esplits.
      + econs 1. econs 1. econs; eauto.
      + eauto.
      + econs; eauto.
    Qed.

    Lemma cancel_step
          rels e1_src e1_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
          (STEP_TGT: Thread.cancel_step e1_tgt e2_tgt):
      exists e2_src,
        (<<STEP_SRC: Thread.cancel_step e1_src e2_src>>) /\
        (<<SIM2: sim_thread rels e2_src e2_tgt>>) /\
        (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv NORMAL1_SRC. ss.
      inv STEP_TGT. inv STEP; inv STEP0; [|inv LOCAL].
      exploit promise_step; try exact LOCAL; eauto; ss. i. des.
      exploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      esplits.
      + econs 1. econs 1. econs; eauto.
      + eauto.
      + econs; eauto.
    Qed.


    (* cap *)

    Lemma covered_max_ts
          mem1 mem2
          (INHABITED: Memory.inhabited mem1)
          (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2):
      forall loc, Time.le (Memory.max_ts loc mem1) (Memory.max_ts loc mem2).
    Proof.
      i. exploit (@Memory.max_ts_spec loc); try eapply INHABITED. i. des.
      exploit Memory.get_ts; eauto. i. des.
      { rewrite x1. apply Time.bot_spec. }
      exploit COVER.
      { econs; eauto. econs; try refl. ss. }
      s. i. inv x. inv ITV. ss.
      exploit Memory.max_ts_spec; try exact GET0. i. des.
      etrans; eauto.
    Qed.

    Lemma sim_memory_cap
          rels mem_src mem_tgt cap_src cap_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_SRC: Memory.closed mem_src)
          (CLOSED_TGT: Memory.closed mem_tgt)
          (CAP_SRC: Memory.cap mem_src cap_src)
          (CAP_TGT: Memory.cap mem_tgt cap_tgt):
      sim_memory rels cap_src cap_tgt.
    Proof.
      dup SIM. inv SIM0. econs; i.
      { apply Cell.ext. i.
        destruct (Cell.get ts (cap_src loc)) as [[from1 msg1]|] eqn:GET1.
        - inv CAP_TGT. exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des.
          + unfold Memory.get in x0. rewrite EQ in x0; ss.
            exploit SOUND0; eauto.
          + subst. inv x1.
            unfold Memory.get in MIDDLE. erewrite MIDDLE; eauto.
            econs; (try by unfold Memory.get; rewrite <- EQ; eauto); ss.
          + subst. unfold Memory.max_ts in *. rewrite EQ; ss. eauto.
        - destruct (Cell.get ts (cap_tgt loc)) as [[from2 msg2]|] eqn:GET2; ss.
          inv CAP_SRC. exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des.
          + unfold Memory.get in x0. rewrite <- EQ in x0; ss.
            exploit SOUND0; eauto. unfold Memory.get. i.
            rewrite GET1 in x. ss.
          + subst. inv x1.
            unfold Memory.get in MIDDLE. erewrite MIDDLE in GET1; eauto.
            econs; (try by unfold Memory.get; rewrite EQ; eauto); ss.
          + subst. unfold Memory.max_ts, Memory.get in *.
            rewrite <- EQ in GET1; ss. rewrite BACK in GET1. ss.
      }
      { rewrite <- memory_cap_covered; try exact CAP_TGT; eauto.
        rewrite <- memory_cap_covered in H; try exact CAP_SRC; eauto.
        inv H. ss. econs; ss. etrans; eauto.
        exploit covered_max_ts; eauto; try apply CLOSED_SRC. i. inv x0.
        - econs. apply Time.incr_mon. eauto.
        - inv H. rewrite H1. refl.
      }
      { exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; ss.
        exploit SOUND; eauto. i. des.
        inv CAP_TGT. exploit SOUND0; eauto.
      }
      { exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des; ss.
        exploit COMPLETE; try exact x0; eauto. i. des.
        - inv CAP_SRC. exploit SOUND0; eauto.
        - inv CAP_SRC. exploit SOUND0; eauto. i.
          right. esplits; eauto.
      }
      { ii. subst.
        exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; ss.
        eapply UNDEF; eauto.
      }
    Qed.
  End PFtoAPFSim.
End PFtoAPFSim.
