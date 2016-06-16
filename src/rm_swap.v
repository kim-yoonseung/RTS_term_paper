Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Require Import def.
Require Import exec.

Require Import priority_proof.
Require Import exec_proof.

Fixpoint swap_taskset (tset:taskset) : taskset :=
  match tset with
  | [] => []
  | h1::t1 =>
    match t1 with
    | [] => [h1]
    | h2::t2 =>
      if (Nat.ltb h2.(period) h1.(period))
      then
        h2::h1::t2
      else
        h1::(swap_taskset t1)
    end
  end.

Lemma swap_taskset_preserves_length:
  forall (tset:taskset), length tset = length (swap_taskset tset).
Proof.
  intros tset.
  induction tset; eauto.
  simpl.
  destruct tset; eauto.
  destruct (period t <? period a); eauto.
  rewrite IHtset.
  eauto.
Qed.

Lemma swap_taskset_preserves_tasks:
  forall (tset:taskset) (t:task),
    In t tset <-> In t (swap_taskset tset).
Proof.
  intros tset t.
  assert (LEN:exists n, n = length tset).
  { eexists. reflexivity. }
  destruct LEN as [len LENEQ].
  generalize dependent tset.
  induction len; intros tset LENEQ.
  - destruct tset.
    + split; eauto.
    + inversion LENEQ.
  - destruct tset.
    + inversion LENEQ.
    + split.
      * intros IN.
        destruct (task_eq_dec t t0) eqn:DEC.
        -- simpl.
           destruct tset; eauto.
           destruct (period t1 <? period t0).
           ++ right. left. eauto.
           ++ left. eauto.
        -- simpl.
           destruct tset; eauto.
           destruct (period t1 <? period t0).
           ++ inversion IN.
              ** right. left. eauto.
              ** inversion H.
                 { left. eauto. }
                 { right. right. eauto. }
           ++ right.
              apply IHlen with (tset:=t1::tset).
              ** eauto.
              ** destruct IN.
                 { exfalso. eauto. }
                 { eauto. }
      * intros IN.
        simpl in IN.
        destruct tset; eauto.
        destruct (period t1 <? period t0).
        ++ inversion IN.
           ** right. left. eauto.
           ** inversion H.
              { left. eauto. }
              { right. right. eauto. }
        ++ destruct IN.
           ** left. eauto.
           ** right.
              apply IHlen with (tset:=t1::tset); eauto.
Qed.

Inductive sorted : (taskset) -> Prop :=
| Sorted_nil : sorted nil
| Sorted_one : forall t, sorted [t]
| Sorted_many : forall t1 t2 tl,
    t1.(period) <= t2.(period) ->
    sorted (t2::tl) ->
    sorted (t1::t2::tl).

Definition tset_swapped
           (tset1 tset2:taskset) (task1 task2:task):=
  exists (tl_bef tl_aft:taskset),
    (tset1 = tl_bef ++ [task1; task2] ++ tl_aft) /\
    (tset2 = tl_bef ++ [task2; task1] ++ tl_aft) /\
    task2.(period) < task1.(period).

Lemma tset_swapped_preserve_tasks:
  forall tset1 tset2 t1 t2,
    tset_swapped tset1 tset2 t1 t2 ->
    forall t, In t tset1 <-> In t tset2.
Proof.
  intros tset1 tset2 t1 t2 SW t.
  unfold tset_swapped in SW.
  destruct SW as [tl_bef [tl_aft [T1 [T2 PRD]]]].
  split.
  - intros IN.
    rewrite T1 in IN.
    rewrite T2.
    apply in_app_or in IN.
    destruct IN as [INb | IN].
    { apply in_or_app. left; eauto. }
    { apply in_app_or in IN.
      destruct IN as [IN12 | INa].
      { apply in_or_app. right.
        apply in_or_app. left.
        inversion IN12.
        - subst. right. left. eauto.
        - inversion H.
          * subst. left. eauto.
          * inversion H0.
      }
      { apply in_or_app. right.
        apply in_or_app. right. eauto. }
    }
  - intros IN.
    rewrite T2 in IN.
    rewrite T1.
    apply in_app_or in IN.
    destruct IN as [INb | IN].
    { apply in_or_app. left; eauto. }
    { apply in_app_or in IN.
      destruct IN as [IN12 | INa].
      { apply in_or_app. right.
        apply in_or_app. left.
        inversion IN12.
        - subst. right. left. eauto.
        - inversion H.
          * subst. left. eauto.
          * inversion H0.
      }
      { apply in_or_app. right.
        apply in_or_app. right. eauto. }
    }
Qed.

Lemma swap_taskset_spec:
  forall (tset_i tset_f:taskset),
    tset_f = swap_taskset tset_i ->
    (sorted tset_i /\ tset_f = tset_i) \/
    exists (task1 task2:task),
      tset_swapped tset_i tset_f task1 task2.
Proof.
  intros tset_i.
  induction tset_i as [| head_i tail_i].
  - intros. left.
    split; eauto. constructor.
  - intros tset_f Htset_f.
    destruct tail_i as [| h2_i t2_i].
    + left. simpl in *.
      split; eauto. constructor.
    + assert (EQf: swap_taskset (head_i :: h2_i :: t2_i) =
                   (if period h2_i <? period head_i then h2_i :: head_i :: t2_i else head_i :: swap_taskset (h2_i::t2_i))).
      { eauto. }
      destruct (period h2_i <? period head_i) eqn:PERC.
      { right.
        exists head_i, h2_i. exists nil, t2_i.
        split; eauto. split; subst; eauto.
        apply Nat.ltb_lt. eauto. }
      { rewrite EQf in Htset_f.
        destruct tset_f as [| head_f tail_f].
        { inversion Htset_f. }
        assert (Tf: tail_f = swap_taskset (h2_i :: t2_i)).
        { inversion Htset_f. eauto. }
        apply IHtail_i in Tf.
        destruct Tf as [SORT2 EQl | CHNGED].
        - left. split.
          + constructor.
            * apply Nat.ltb_ge; eauto.
            * inversion SORT2; eauto.
          + inversion SORT2. inversion Htset_f. subst. eauto.
        - right.
          destruct CHNGED as [task1 [task2 [tl_bef [tl_aft CHNGED]]]].
          exists task1, task2. exists (head_i::tl_bef), tl_aft.
          destruct CHNGED as [Hor [Hch PERC2]].
          split.
          + simpl. rewrite Hor. eauto.
          + split; eauto.
            simpl. rewrite Hch. inversion Htset_f; eauto.
      }
Qed.

Lemma swap_preserve_valid_tset:
  forall (tset:taskset),
    valid_tset tset ->
    valid_tset (swap_taskset tset).
Proof.
  unfold valid_tset. unfold tset_unique_id.
  intros tset [UID NOD].
  split.
  { intros t1 t2 INt1 INt2.
    specialize (swap_taskset_preserves_tasks tset). intros PRSV.
    rewrite <- PRSV in INt1.
    rewrite <- PRSV in INt2.
    apply UID; eauto. }
  { induction tset.
    - simpl. eauto.
    - simpl.
      destruct tset as [| tsh tst]; eauto.
      destruct (period tsh <? period a) eqn:PRD.
      + inversion NOD.
        inversion H2.
        constructor; eauto.
        * intros IN.
          subst.
          apply H1.
          destruct IN as [EQ | INtst].
          -- left; eauto.
          -- contradiction.
        * constructor; eauto.
          intros IN.
          apply H1.
          right. eauto.
      + inversion NOD.
        inversion H2.
        constructor; eauto.
        * intros IN.
          apply H1.
          apply swap_taskset_preserves_tasks; eauto.
        * apply IHtset; eauto.
          intros.
          apply UID; right; eauto.
  }
Qed.

Definition swap_priority_assigner (pr:priority_assigner)
  : priority_assigner :=
  fun (tset:taskset) => swap_taskset (pr tset).

Lemma swap_preserves_valid_priority_assigner:
  forall (pr:priority_assigner),
    valid_priority_assigner pr ->
    valid_priority_assigner (swap_priority_assigner pr).
Proof.
  unfold valid_priority_assigner.
  intros pr Cpr.
  intros tset t VT.
  unfold swap_priority_assigner.
  specialize (Cpr tset t VT).
  destruct Cpr as [INs VT2].
  split.
  - rewrite INs.
    apply swap_taskset_preserves_tasks.
  - apply swap_preserve_valid_tset. eauto.
Qed.

Lemma swap_spec:
  forall (pr:priority_assigner) (tset0 tset1 tset2:taskset),
    tset1 = pr tset0 ->
    tset2 = (swap_priority_assigner pr) tset0 ->
    (sorted tset1 /\ tset2 = tset1) \/
    exists (task1 task2:task),
      tset_swapped tset1 tset2 task1 task2.
Proof.
  intros pr tset0 tset1 tset2 EQpr EQspr.
  apply swap_taskset_spec.
  subst. eauto.
Qed.
