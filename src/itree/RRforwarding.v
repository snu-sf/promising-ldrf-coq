Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.

Require Import FoldN.
Require Import Knowledge.

Require Import ITreeLangNotations.
Require Import ITreeLang.





Section DATA.

  Lemma inter_comm:
    forall s1 s2, IdentSet.eq (IdentSet.inter s1 s2) (IdentSet.inter s2 s1).
  Proof.
    ii. split.
    - i. eapply IdentSet.inter_spec in H. des. eapply IdentSet.inter_spec. auto.
    - i. eapply IdentSet.inter_spec in H. des. eapply IdentSet.inter_spec. auto.
  Qed.

  Lemma inter_assoc:
    forall s1 s2 s3, IdentSet.eq (IdentSet.inter s1 (IdentSet.inter s2 s3)) (IdentSet.inter (IdentSet.inter s1 s2) s3).
  Proof.
    ii. split.
    - i. eapply IdentSet.inter_spec in H. des. eapply IdentSet.inter_spec in H0. des.
      eapply IdentSet.inter_spec. split; auto. eapply IdentSet.inter_spec. auto.
    - i. eapply IdentSet.inter_spec in H. des. eapply IdentSet.inter_spec in H. des.
      eapply IdentSet.inter_spec. split; auto. eapply IdentSet.inter_spec. auto.
  Qed.

  Lemma inter_idem:
    forall s, IdentSet.eq (IdentSet.inter s s) s.
  Proof.
    ii. split.
    - i. eapply IdentSet.inter_spec in H. des; auto.
    - i. eapply IdentSet.inter_spec. auto.
  Qed.

  Lemma Subset_spec:
    forall s1 s2, IdentSet.Subset s1 s2 <-> IdentSet.eq s1 (IdentSet.inter s1 s2).
  Proof.
    ii. split; ii.
    - eapply IdentSet.Facts.In_s_m in H. split; ii.
      + eapply IdentSet.inter_spec. eauto.
      + eapply IdentSet.inter_spec in H0. des; auto.
      + auto.
    - eapply IdentSet.eq_leibniz in H. rewrite H in H0. eapply IdentSet.inter_spec in H0. des; auto.
  Qed.


  Definition IdentSetML :=
    @MLattice.mk_mlattice
      IdentSet.t IdentSet.eq IdentSet.eq_equiv IdentSet.eq_leibniz
      IdentSet.inter inter_comm inter_assoc inter_idem
      IdentSet.Subset Subset_spec.


  Definition bot := IdentSet.empty.
  Lemma bot_spec:
    forall s, IdentSet.Subset bot s.
  Proof.
    i. hexploit IdentSet.empty_spec. ii. unfold IdentSet.Empty in H. eapply H in H0. clarify.
  Qed.

End DATA.





Section ANALYSIS.

  (**
  Simple read-read forwarding:

  x =* l (read na); ... y =* l (read na);
  ->
  x =* l (read na); ... y = x (assign);

  Ordering:
  for insts in ...,

                      RR
  na               :  O
  rel(at write)    :  O
  acq(at read)     :  X
  rel-acq          :  X
  syscall          :  X

   **)

  Definition distl {T} l1 l2 (v1 v2: T) := if (Loc.eqb l1 l2) then v1 else v2.

  Definition RRfwd_load (ul: Loc.t) x o : Loc.t -> (local_update IdentSet.t) :=
    fun l t =>
      if (Ordering.le o Ordering.na)
      then distl ul l (IdentSet.add x t) (IdentSet.remove x t)
      else
        if (Ordering.le o Ordering.strong_relaxed)
        then distl ul l bot (IdentSet.remove x t)
        else bot.

  Definition RRfwd_write (ul: Loc.t) : Loc.t -> (local_update IdentSet.t) :=
    fun l t =>
      distl ul l bot t.

  Definition RRfwd_fence_r o : Loc.t -> (local_update IdentSet.t) :=
    fun _ t =>
      if (Ordering.le o Ordering.strong_relaxed)
      then t
      else bot.

  Definition RRfwd_fence_w o : Loc.t -> (local_update IdentSet.t) :=
    fun _ t =>
      if (Ordering.le o Ordering.acqrel)
      then t
      else bot.

  Definition RRfwd_assign x : Loc.t -> (local_update IdentSet.t) :=
    fun _ t => IdentSet.remove x t.

  Definition RRfwd_inst (i: Inst.t) : Loc.t -> (local_update IdentSet.t) :=
    fun l t =>
      match i with
      | Inst.skip => t
      | Inst.assign x e => (RRfwd_assign x) l t

      | Inst.load x ul o => (RRfwd_load ul x o) l t
      | Inst.store ul _ o => (RRfwd_write ul) l t

      (* same as load + store *)
      | Inst.update x ul rmw or ow =>
        let ut0 := (RRfwd_load ul x or) l t in
        let ut1 := (RRfwd_write ul) l ut0 in
        ut1

      | Inst.fence or ow =>
        let ut0 := (RRfwd_fence_r or) l t in
        let ut1 := (RRfwd_fence_w ow) l ut0 in
        ut1

      | Inst.syscall x es => bot
      | Inst.abort => t
      | Inst.choose x => (RRfwd_assign x) l t
      end
  .

  Definition N : nat := 1.

  Fixpoint RRfwd_block (b: block): Loc.t -> (local_update IdentSet.t) :=
    fun p d =>
      match b with
      | nil => d
      | cons hd tl =>
        match hd with
        | inst i =>
          let d0 := RRfwd_inst i p d in
          RRfwd_block tl p d0

        | ite _ b1 b2 =>
          let d1 := RRfwd_block b1 p d in
          let d2 := RRfwd_block b2 p d in
          let d3 := IdentSet.inter d1 d2 in
          RRfwd_block tl p d3

        | while _ wb =>
          let f := (RRfwd_block wb p) in
          let fp := fold_n f (S N) in
          let d0 := IdentSet.inter d (fp d) in
          RRfwd_block tl p d0
        end
      end.

End ANALYSIS.





Section ALG.

  Definition RRfwd_opt_inst (mp: GD IdentSet.t Loc.t) (i: Inst.t) : Inst.t :=
    match i with
    | Inst.load x l o =>
      match (IdentSet.choose (mp l)), o with
      | Some y, Ordering.na => (Inst.assign x (Inst.expr_var y))
      | _, _ => i
      end
    | _ => i
    end
  .


  Let GD := GD IdentSet.t Loc.t.
  Let inst_gd (i: Inst.t) : GD -> GD := mk_global (RRfwd_inst i).
  Let block_gd (b: block): GD -> GD := mk_global (RRfwd_block b).
  Let meet2 : GD -> GD -> GD := fun gd1 gd2 => (fun p => IdentSet.inter (gd1 p) (gd2 p)).

  Fixpoint RRfwd_opt_block (data: GD) (blk: block) : GD * block :=
    match blk with
    | nil => (data, blk)
    | cons hd tl =>
      match hd with
      | inst i =>
        let i1 := RRfwd_opt_inst data i in
        let data1 := inst_gd i data in
        let '(data2, tl1) := RRfwd_opt_block data1 tl in
        (data2, cons i1 tl1)

      | ite cond blk1 blk2 =>
        let '(data1, ublk1) := RRfwd_opt_block data blk1 in
        let '(data2, ublk2) := RRfwd_opt_block data blk2 in
        let data3 := meet2 data1 data2 in
        let '(data4, tl1) := RRfwd_opt_block data3 tl in
        (data4, cons (ite cond ublk1 ublk2) tl1)

      | while cond wb =>
        let f := (block_gd wb) in
        let fp := fold_n f (S N) in
        let data1 := meet2 data (fp data) in
        let '(_, wb1) := RRfwd_opt_block data1 wb in
        let '(data2, tl1) := RRfwd_opt_block data1 tl in
        (data2, cons (while cond wb1) tl1)

      end
    end.



  Let bot2 : GD := fun _ => bot.

  Definition RRfwd_opt_alg : block -> block :=
    fun code => snd (RRfwd_opt_block bot2 code).

End ALG.





Section Test.

  Import ITreeLangNotations.
  Import BinNums.

  Local Open Scope expr_scope.
  Local Open Scope inst_scope.
  Local Open Scope stmt_scope.
  Local Open Scope block_scope.

  Definition loc1 : Loc.t := xH.
  Definition loc2 : Loc.t := xO xH.
  Definition loc3 : Loc.t := xI xH.

  Definition a : Ident.t := xH.
  Definition b : Ident.t := Ident.succ a.
  Definition c : Ident.t := Ident.succ b.
  Definition d : Ident.t := Ident.succ c.

  Definition test0 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      c =#* loc1 Ordering.na;
      a =# (1: Const.t);
      b =#* loc1 Ordering.na
    }
  .
  Definition test0' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      c =#* loc1 Ordering.na;
      a =# (1: Const.t);
      b =# c
    }
  .
  Goal (RRfwd_opt_alg test0) = test0'.
  Proof. ss. Qed.

  Definition test1 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      c =#* loc1 Ordering.na;
      while# (1: Const.t) do#
      { a =# (1: Const.t);
        b =#* loc1 Ordering.na
      }
      end#
    }
  .
  Definition test1' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      c =#* loc1 Ordering.na;
      while# (1: Const.t) do#
      { a =# (1: Const.t);
        b =# c
      }
      end#
    }
  .
  Goal (RRfwd_opt_alg test1) = test1'.
  Proof. ss. Qed.

  Definition test2 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      a =#* loc1 Ordering.na;
      if# a
      then# { a =# (1: Const.t);
              b =#* loc1 Ordering.na
            }
      else# { b =#* loc1 Ordering.na; }
      fi#;
      c =#* loc1 Ordering.na
    }
  .
  Definition test2' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      a =#* loc1 Ordering.na;
      if# a
      then# { a =# (1: Const.t);
              b =#* loc1 Ordering.na
            }
      else# { b =# a; }
      fi#;
      c =# b
    }
  .
  Goal (RRfwd_opt_alg test2) = test2'.
  Proof. ss. Qed.

  Definition test3 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      a =#* loc1 Ordering.na;
      b =#* loc1 Ordering.na;
      c =#* loc1 Ordering.na
    }
  .
  Definition test3' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      a =#* loc1 Ordering.na;
      b =# a;
      c =# a
    }
  .
  Goal (RRfwd_opt_alg test3) = test3'.
  Proof. ss. Qed.

End Test.
