Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

From PromisingLib Require Import Event.

Require Import FoldN.
Require Import Knowledge.

Require Import ITreeLangNotations.
Require Import ITreeLang.





Section DATA.

  Variant Three := none | half | full.

  Program Instance eq_Equiv: Equivalence (@eq Three).
  Lemma eq_leibniz : forall x y : Three, eq x y -> x = y.
  Proof. auto. Qed.


  Definition meet (t1 t2: Three) :=
    match t1, t2 with
    | none, _ => none
    | _, none => none
    | full, t => t
    | t, full => t
    | half, half => half
    end.

  Lemma meet_comm: forall t1 t2, meet t1 t2 = meet t2 t1.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
  Qed.

  Lemma meet_assoc: forall t1 t2 t3, meet t1 (meet t2 t3) = meet (meet t1 t2) t3.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
  Qed.

  Lemma meet_idem: forall t, meet t t = t.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
  Qed.



  Definition le (t1 t2: Three) :=
    match t1, t2 with
    | none, _ => True
    | half, half | half, full => True
    | full, full => True
    | _, _ => False
    end.

  Lemma le_spec: forall t1 t2, le t1 t2 <-> t1 = (meet t1 t2).
  Proof.
    i. unfold le, meet. des_ifs.
  Qed.

  Definition ThreeML :=
    @MLattice.mk_mlattice
      Three eq eq_Equiv eq_leibniz
      meet meet_comm meet_assoc meet_idem
      le le_spec.


  Definition bot : Three := none.
  Lemma bot_spec: forall t, le bot t.
  Proof. i. ss. Qed.

  Lemma strict_order:
    forall d1 d2, not (le d1 d2) -> le d2 d1.
  Proof.
    i. unfold le in *. des_ifs.
  Qed.



  Definition level := 2.
  Lemma level_grounded: forall (t: Three), grounded eq le t level.
  Proof.
    i. econs. i. unfold lt in LT. des.
    destruct t, k'; ss; clarify.
    - clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify.
    - clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify.
    - clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify.
      clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify.
  Qed.

End DATA.





Section ANALYSIS.

  (**
  Dead Store Elimination:

  x = a (write na); ... x = b (write na);
  ->
  skip(dead store); ... x = b (write na);

  Ordering:
  for insts in ...,

                      WR
  na               :  O
  rel(at write)    :  O
  acq(at read)     :  O
  rel-acq          :  X
  syscall          :  X
  rel-while        :  X

   **)


  Definition distl {T} l1 l2 (v1 v2: T) := if (Loc.eqb l1 l2) then v1 else v2.

  Definition acq_flag (t: Three) :=
    match t with
    | none => none
    | half
    | full => half
    end.

  Definition rel_flag (t: Three) :=
    match t with
    | none
    | half => none
    | full => full
    end.

  Definition update_load ul o : Loc.t -> (local_update Three) :=
    fun l t =>
      if (Ordering.le o Ordering.strong_relaxed)
      then distl ul l none t
      else distl ul l none (acq_flag t).

  (*for update*)
  Definition update_read ul o : Loc.t -> (local_update Three) :=
    fun l t =>
      if (Ordering.le o Ordering.na)
      then distl ul l none t
      else distl ul l none (acq_flag t).

  Definition update_store ul o : Loc.t -> (local_update Three) :=
    fun l t =>
      if (Ordering.le o Ordering.na)
      then distl ul l full t
      else
        if (Ordering.le o Ordering.relaxed)
        then distl ul l none t
        else distl ul l none (rel_flag t).

  Definition update_fence_r o : Loc.t -> (local_update Three) :=
    fun _ t =>
      if (Ordering.le o Ordering.strong_relaxed)
      then t
      else (acq_flag t).

  Definition update_fence_w o : Loc.t -> (local_update Three) :=
    fun _ t =>
      if (Ordering.le o Ordering.relaxed)
      then t
      else
        if (Ordering.le o Ordering.acqrel)
        then (rel_flag t)
        else (rel_flag (acq_flag t)).

  Definition update_inst (i: Inst.t) : Loc.t -> (local_update Three) :=
    fun l t =>
      match i with
      | Inst.skip => t
      | Inst.assign x e => t

      | Inst.load _ ul o => (update_load ul o) l t
      | Inst.store ul _ o => (update_store ul o) l t

      (* read + store in backwards *)
      | Inst.update _ ul _ or ow =>
        let ut0 := (update_store ul ow) l t in
        let ut1 := (update_read ul or) l ut0 in
        ut1

      | Inst.fence or ow =>
        let ut0 := (update_fence_w ow) l t in
        let ut1 := (update_fence_r or) l ut0 in
        ut1

      | Inst.syscall x es => none
      | Inst.abort => t
      | Inst.choose _ => t
      end
  .

  Fixpoint update_block (blk: block) : Loc.t -> (local_update Three) :=
    fun l t =>
    match blk with
    | nil => t
    | cons hd tl =>
      match hd with
      | inst i =>
        let t1 := (update_block tl) l t in
        (update_inst i) l t1

      | ite cond blk1 blk2 =>
        let t1 := (update_block tl) l t in
        let tt := (update_block blk1) l t1 in
        let te := (update_block blk2) l t1 in
        meet tt te

      | while cond wb =>
        let t1 := (update_block tl) l t in
        let f := (update_block wb) l in
        let fp := fold_n f (S level) in
        let t2 := fp t1 in
        let t3 := fp half in
        meet t1 (meet t2 t3)

      end
    end.

End ANALYSIS.





Section ALG.

  Definition DSE_opt_inst (mp: Data Three Loc.t) (i: Inst.t) : Inst.t :=
    match i with
    | Inst.store l _ o =>
      match (mp l), o with
      | half, Ordering.na
      | full, Ordering.na => Inst.skip
      | _, _ => i
      end
    | _ => i
    end
  .


  Let GD := Data Three Loc.t.
  Let update0 (i: Inst.t) : GD -> GD := mk_global (update_inst i).
  Let update1 (b: block): GD -> GD := mk_global (update_block b).
  Let data_meet : GD -> GD -> GD := fun gd1 gd2 => (fun p => meet (gd1 p) (gd2 p)).
  Let datai: Data Three Loc.t := fun _ => half.

  Fixpoint DSE_opt_block (data: Data Three Loc.t) (blk: block) : (Data Three Loc.t) * block :=
    match blk with
    | nil => (data, blk)
    | cons hd tl =>
      let '(ud, utl) := DSE_opt_block data tl in
      match hd with
      | inst i =>
        let ui := DSE_opt_inst ud i in
        let udi := update0 i ud in
        (udi, cons ui utl)

      | ite cond blk1 blk2 =>
        let '(udt, ubt) := DSE_opt_block ud blk1 in
        let '(ude, ube) := DSE_opt_block ud blk2 in
        (data_meet udt ude, cons (ite cond ubt ube) utl)

      | while cond wb =>
        let f := (update1 wb) in
        let fp := fold_n f (1 + level) in
        let ud1 := fp ud in
        let ud2 := fp datai in
        let ud3 := data_meet ud (data_meet ud1 ud2) in
        let '(_, uwb) := DSE_opt_block ud3 wb in
        (ud3, cons (while cond uwb) utl)

      end
    end.

  Let data_bot: Data Three Loc.t := fun _ => bot.

  Definition DSE_opt_alg : block -> block :=
    fun code => snd (DSE_opt_block data_bot code).

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

  Definition x : Ident.t := xH.
  Definition y : Ident.t := xO xH.

  Definition test0 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =# (1: Const.t);
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test0' : block :=
    { skip#;
      x =# (1: Const.t);
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test0) = test0'.
  Proof. ss. Qed.

  Definition test1 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =# (1: Const.t);
      y =#* loc1 Ordering.na;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test1' : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =# (1: Const.t);
      y =#* loc1 Ordering.na;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test1) = test1'.
  Proof. ss. Qed.

  Definition test2 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test2' : block :=
    { skip#;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test2) = test2'.
  Proof. ss. Qed.

  Definition test3 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc2 *=# (0: Const.t) Ordering.acqrel;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test3' : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc2 *=# (0: Const.t) Ordering.acqrel;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test3) = test3'.
  Proof. ss. Qed.

  Definition test4 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test4' : block :=
    { skip#;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test4) = test4'.
  Proof. ss. Qed.

  Definition test5 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =#* loc2 Ordering.acqrel;
      loc3 *=# (0: Const.t) Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test5' : block :=
    { skip#;
      x =#* loc2 Ordering.acqrel;
      loc3 *=# (0: Const.t) Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test5) = test5'.
  Proof. ss. Qed.

  Definition test6 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc3 *=# (0: Const.t) Ordering.acqrel;
      x =#* loc2 Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test6' : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc3 *=# (0: Const.t) Ordering.acqrel;
      x =#* loc2 Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test6) = test6'.
  Proof. ss. Qed.

  Definition test7 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { y =#* loc1 Ordering.na;
        loc1 *=# (3: Const.t) Ordering.na
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test7' : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { y =#* loc1 Ordering.na;
        loc1 *=# (3: Const.t) Ordering.na
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test7) = test7'.
  Proof. ss. Qed.

  Definition test8 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { loc1 *=# (3: Const.t) Ordering.na;
        y =#* loc1 Ordering.na
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test8' : block :=
    { skip#;
      x =#* loc2 Ordering.acqrel;
      while# (1: Const.t) do#
      { loc1 *=# (3: Const.t) Ordering.na;
        y =#* loc1 Ordering.na
      }
      end#;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test8) = test8'.
  Proof. ss. Qed.

  Definition test9 : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc2 *=# (0: Const.t) Ordering.acqrel;
      while# (1: Const.t) do#
      { loc1 *=# (3: Const.t) Ordering.na;
      }
      end#;
      x =#* loc2 Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Definition test9' : block :=
    { loc1 *=# (1: Const.t) Ordering.na;
      loc2 *=# (0: Const.t) Ordering.acqrel;
      while# (1: Const.t) do#
      { skip#;
      }
      end#;
      x =#* loc2 Ordering.acqrel;
      loc1 *=# (5: Const.t) Ordering.na
    }
  .
  Goal (DSE_opt_alg test9) = test9'.
  Proof. ss. Qed.

End Test.
