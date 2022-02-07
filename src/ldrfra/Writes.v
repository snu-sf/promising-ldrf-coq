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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import OrdStep.

Set Implicit Arguments.


Module Writes.
  Section Writes.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t * Ordering.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then (loc, to, ord) :: rels
        else rels
      | None => rels
      end.

    Variant wf (rels: t) (mem: Memory.t): Prop :=
    | wf_intro
        (SOUND: forall loc to ord (IN: List.In (loc, to, ord) rels),
            L loc /\
            exists from val released,
              Memory.get loc to mem = Some (from, Message.concrete val released))
        (COMPLETE: forall loc from to val released
                     (LOC: L loc)
                     (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
            exists ord, List.In (loc, to, ord) rels)
    .

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.

    Lemma promise_wf
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: wf rels mem1)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
          (MSG: L loc -> msg = Message.reserve):
      wf rels mem2.
    Proof.
      inv RELS1. econs; i.
      { exploit SOUND; eauto. i. des. split; ss.
        inv PROMISE; ss.
        - exploit Memory.add_get1; try exact x0; eauto.
        - exploit Memory.split_get1; try exact x0; eauto. i. des. eauto.
        - exploit Memory.lower_get1; try exact x0; eauto. i. des. inv MSG_LE. eauto.
        - erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
          des. subst. exploit Memory.remove_get0; try exact MEM. i. des. congr.
      }
      { revert GET. inv PROMISE; ss.
        - erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. clarify. exploit MSG; ss.
        - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + i. des. clarify. exploit MSG; ss.
          + guardH o. i. des. clarify. exploit MSG; ss.
        - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          i. des. clarify. exploit MSG; ss.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      }
    Qed.

    Lemma write_wf
          ord
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: wf rels mem1)
          (MSG: L loc -> exists val released, msg = Message.concrete val released)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      wf (if L loc then (loc, to, ord) :: rels else rels) mem2.
    Proof.
      condtac; cycle 1.
      { inv WRITE. eapply promise_wf; eauto. rewrite COND. ss. }
      inv RELS1. inv WRITE. econs; i.
      { inv IN.
        { clarify. split; ss.
          exploit MSG; eauto. i. des. subst.
          exploit Memory.promise_get0; try exact PROMISE.
          { destruct kind; ss. inv PROMISE. ss. }
          i. des. eauto.
        }
        exploit SOUND; eauto. i. des. split; ss.
        exploit MSG; eauto. i. des. subst.
        inv PROMISE; ss.
        - exploit Memory.add_get1; try exact x0; eauto.
        - exploit Memory.split_get1; try exact x0; eauto. i. des. eauto.
        - exploit Memory.lower_get1; try exact x0; eauto. i. des. inv MSG_LE. eauto.
      }
      { revert GET. inv PROMISE; ss.
        - erewrite Memory.add_o; eauto. condtac; ss.
          + i. des. clarify. eauto.
          + guardH o. i. exploit COMPLETE; eauto. i. des. eauto.
        - erewrite Memory.split_o; eauto. repeat condtac; ss.
          + i. des. clarify. eauto.
          + guardH o. i. des. clarify.
            exploit Memory.split_get0; try exact MEM. i. des.
            exploit COMPLETE; try exact GET0; eauto. i. des. eauto.
          + guardH o. guardH o0. i.
            exploit COMPLETE; eauto. i. des. eauto.
        - erewrite Memory.lower_o; eauto. condtac; ss.
          + i. des. clarify. eauto.
          + guardH o. i. exploit COMPLETE; eauto. i. des. eauto.
        - exploit MSG; eauto. i. des. subst. ss.
      }
    Qed.

    Lemma write_wf_other
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: wf rels mem1)
          (LOC: ~ L loc)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      wf rels mem2.
    Proof.
      exploit (@write_wf Ordering.na); try exact WRITE; eauto; ss.
      condtac; ss.
    Qed.

    Lemma write_na_wf
          rels ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (RELS1: wf rels mem1)
          (LOC: ~ L loc)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      wf rels mem2.
    Proof.
      induction WRITE.
      - exploit write_wf_other; eauto.
      - apply IHWRITE; ss.
        exploit write_wf_other; try exact WRITE_EX; eauto.
    Qed.

    Lemma step_wf
          ordcr ordcw rels lang pf e e1 e2
          (RELS1: wf rels (Thread.memory e1))
          (ORDCW: Ordering.le Ordering.plain ordcw)
          (STEP: @OrdThread.step lang L ordcr ordcw pf e e1 e2):
      wf (append e rels) (Thread.memory e2).
    Proof.
      unfold append.
      inv STEP; inv STEP0; inv LOCAL; try inv LOCAL0; ss.
      - eapply promise_wf; eauto.
      - inv STEP. eapply write_wf; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss.
        eapply write_wf; eauto.
      - inv STEP. revert ORD. condtac; ss.
        { destruct ord, ordcw; ss. }
        hexploit write_na_wf; eauto. rewrite COND. ss.
      - inv STEP. eapply write_wf; eauto.
    Qed.

    Lemma reserve_step_wf
          rels lang e1 e2
          (RELS1: wf rels (Thread.memory e1))
          (STEP: @Thread.reserve_step lang e1 e2):
      wf rels (Thread.memory e2).
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. ss.
      eapply promise_wf; eauto.
    Qed.

    Lemma cancel_step_wf
          rels lang e1 e2
          (RELS1: wf rels (Thread.memory e1))
          (STEP: @Thread.cancel_step lang e1 e2):
      wf rels (Thread.memory e2).
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. ss.
      eapply promise_wf; eauto.
    Qed.

    Lemma promise_disjoint
          promises1 mem1 loc from to msg promises2 mem2 kind
          promises
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      destruct (Memory.get loc to promises) as [[]|] eqn:GETP; ss.
      exploit LE; eauto. i.
      inv PROMISE; ss.
      - exploit Memory.add_get0; try exact MEM. i. des. congr.
      - exploit Memory.split_get0; try exact MEM. i. des. congr.
      - exploit Memory.lower_get0; try exact PROMISES. i. des.
        inv DISJOINT. exploit DISJOINT0; eauto. i. des. exfalso.
        exploit Memory.get_ts; try exact GETP. i. des; try congr.
        exploit Memory.get_ts; try exact GET. i. des; try congr.
        apply (x0 to); econs; try refl; ss.
      - exploit Memory.remove_get0; try exact PROMISES. i. des.
        inv DISJOINT. exploit DISJOINT0; eauto. i. des. exfalso.
        exploit Memory.get_ts; try exact GETP. i. des; try congr.
        exploit Memory.get_ts; try exact GET. i. des; try congr.
        apply (x0 to); econs; try refl; ss.
    Qed.

    Lemma write_disjoint
          promises1 mem1 loc from to msg promises2 mem2 kind
          promises
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      inv WRITE. eauto using promise_disjoint.
    Qed.

    Lemma write_na_disjoint
          ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          promises
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      induction WRITE; eauto using write_disjoint.
      exploit Memory.write_disjoint; try exact WRITE_EX; eauto. i. des. eauto.
    Qed.

    (* Lemma step_disjoint *)
    (*       ordrc ordwc rels lang pf e e1 e2 promises *)
    (*       (RELS1: wf rels (Local.promises (Thread.local e1)) (Thread.memory e1)) *)
    (*       (STEP: @OrdThread.step lang L ordrc ordwc pf e e1 e2) *)
    (*       (DISJOINT: Memory.disjoint (Local.promises (Thread.local e1)) promises) *)
    (*       (LE: Memory.le promises (Thread.memory e1)) *)
    (*       (RELS: wf rels promises (Thread.memory e1)): *)
    (*   wf (append e rels) promises (Thread.memory e2). *)
    (* Proof. *)
    (*   hexploit step_wf; eauto. ii. *)
    (*   exploit H; eauto. i. des. esplits; eauto. *)
    (*   unfold append in *. *)
    (*   inv STEP; inv STEP0; inv LOCAL; ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - inv LOCAL0. inv STEP. ss. revert IN. *)
    (*     repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss). *)
    (*     inv IN. eapply write_disjoint; eauto. *)
    (*   - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss. revert IN. *)
    (*     repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss). *)
    (*     inv IN. eapply write_disjoint; eauto. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - inv LOCAL0. inv STEP. ss. revert IN. *)
    (*     repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss). *)
    (*     inv IN. eapply write_na_disjoint; eauto. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (*   - exploit RELS; eauto. i. des. ss. *)
    (* Qed. *)
  End Writes.
End Writes.
