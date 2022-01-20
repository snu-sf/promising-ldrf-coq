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

Set Implicit Arguments.


Module RelWrites.
  Section RelWrites.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels
        else rels
      | None => rels
      end.

    Definition wf (rels: t) (promises mem: Memory.t): Prop :=
      forall loc to (IN: List.In (loc, to) rels),
        Memory.get loc to promises = None /\
        exists from val released,
          Memory.get loc to mem = Some (from, Message.concrete val released).

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.
  End RelWrites.
End RelWrites.
