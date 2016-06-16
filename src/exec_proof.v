Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Require Import def.
Require Import exec.

Require Import priority_proof.

Section RUNNING_HELPERS.

  (* for find_task_id *)
  Lemma find_task_id_spec:
    forall (tid:nat) (t:task) (tset:taskset)
      (VT: valid_tset tset),
      find_task_id tid tset = Some t <->
      In t tset /\ t.(task_id) = tid.
  Proof.
    intros tid t tset VT.
    unfold valid_tset.
    revert t tid.
    induction tset as [| a tset]; intros.
    - split.
      + intros. inversion H.
      + intros. inversion H. inversion H0.
    - assert (VT2 : valid_tset tset).
      { eapply valid_tset_shrink; eauto. }
      split.
      + intros FIND.
        simpl in FIND.
        destruct (task_id a =? tid) eqn:EQB_ID.
        * split.
          { left. inversion FIND; eauto. }
          { apply beq_nat_true. inversion FIND. subst. eauto. }
        * apply IHtset in FIND; eauto.
          destruct FIND as [IN TID].
          split; eauto.
          right; eauto.
      + intros [IN TID].
        inversion IN.
        * subst. simpl.
          rewrite Nat.eqb_refl. eauto.
        * simpl.
          destruct (task_id a =? tid) eqn:EQB_ID.
          { apply beq_nat_true in EQB_ID.
            unfold valid_tset in VT.
            destruct VT as [UID NOD].
            unfold tset_unique_id in UID.
            assert (AG: task_id a <> task_id t \/ a = t).
            { eapply UID.
              - left; eauto.
              - right; eauto. }
            destruct AG as [NEQ | EQ].
            - subst. exfalso. apply NEQ; eauto.
            - subst. eauto.
          }
          { apply IHtset; eauto. }
  Qed.

  (* for get_nth_job_of_task *)

  Theorem get_next_nth_of_task_spec:
    forall (t:task) (time:nat) (nth:nat),
      get_next_nth_of_task t time = Some nth ->
      (nth_job_of_task t nth).(release_time) = time.
  Proof.
    intros.
    unfold nth_job_of_task.
    unfold get_next_nth_of_task in H.
    destruct (time <? start t) eqn:START; [inversion H| ].
    destruct ((time - start t) / period t * period t =? time - start t) eqn:EQB; [| inversion H].
    destruct t.
    simpl in *.
    inversion H.
    apply beq_nat_true in EQB.
    rewrite Nat.mul_comm.
    rewrite EQB.
    apply Nat.ltb_ge in START.
    apply le_plus_minus_r. eauto.
  Qed.

  (* for add_job_to_queue *)

  Lemma add_job_to_queue_preserve_valid_queue:
    forall (tset:taskset) (j:job) (q:queue),
      valid_tset tset ->
      (exists n, priority_of_tid j.(job_task_id) tset = Some n) ->
      valid_queue tset q ->
      (forall j', In j' q -> j'.(job_task_id) <> j.(job_task_id)) ->
      valid_queue tset (add_job_to_queue tset j q).
  Proof.
    intros tset j q VT EXn VQ DIFF.
    induction VQ.
    - simpl.
      inversion EXn.
      eapply Q_one. eauto.
    - simpl. rewrite -> H.
      destruct (priority_of_tid j.(job_task_id) tset) eqn:PR_IDj.
      + destruct (n0 <? n) eqn:LT.
        * econstructor; eauto.
          { apply Nat.ltb_lt in LT. omega. }
          { econstructor; eauto. }
        * econstructor; eauto.
          { apply Nat.ltb_ge in LT.
            assert (DIFFr: job_task_id j0 <> job_task_id j).
            { apply DIFF. left. eauto. }
            destruct (Nat.eq_dec n n0) eqn:DECn.
            { subst.
              exfalso. apply DIFFr.
              eapply priority_tid_unique; eauto. }
            { apply Nat.le_neq. eauto. }
          }
          { econstructor; eauto. }
      + econstructor; eauto.
    - simpl in *.
      + destruct (priority_of_tid (job_task_id j) tset) eqn:PR_IDj.
        { rewrite H. rewrite H0 in IHVQ.
          destruct (n <? n1) eqn:LT1.
          { destruct (n <? n2) eqn:LT2.
            - econstructor; eauto.
              + apply Nat.ltb_lt in LT1. omega.
              + econstructor; eauto.
            - econstructor; eauto.
              + apply Nat.ltb_lt in LT1. omega.
              + econstructor; eauto.
          }
          { rewrite H0.
            destruct (n <? n2) eqn:LT2.
            - econstructor; eauto.
              apply Nat.ltb_ge in LT1.
              destruct (Nat.eq_dec n1 n) eqn:DECn1.
              + subst.
                assert (EQjs: job_task_id j1 = job_task_id j).
                { eapply priority_tid_unique; eauto. }
                specialize (DIFF j1).
                exfalso. apply DIFF; eauto.
              + apply Nat.le_neq. eauto.
            - econstructor; eauto.
          }
        }
        { econstructor; eauto. }
  Qed.

  Lemma add_job_to_queue_preserve_job:
    forall (tset:taskset) (jq:queue) (j j':job),
      In j jq ->
      In j (add_job_to_queue tset j' jq).
  Proof.
    intros tset jq.
    induction jq as [| jh jq].
    - intros. inversion H.
    - intros.
      simpl.
      destruct (priority_of_tid j'.(job_task_id) tset) eqn:PR_IDj'.
      + destruct (priority_of_tid jh.(job_task_id) tset) eqn:PR_IDjh; eauto.
        destruct (n <? n0) eqn:LTn.
        { destruct H as [EQj | INj].
          - right. left. eauto.
          - right. right. eauto. }
        { destruct H as [EQj | INjq].
          - left. eauto.
          - right. apply IHjq. eauto.
        }
      + eauto.
  Qed.

End RUNNING_HELPERS.

Section RUNNING.

  Lemma filter_fails_spec:
    forall q qt qf time,
      filter_fails q time = (qt, qf) ->
      (forall j:job, (In j qt) -> (time < j.(deadline))) /\
      (forall j:job, (In j qf) -> (j.(deadline) <= time)).
  Proof.
    intros q.
    induction q as [| hq tq].
    - simpl. intros. inversion H.
      split; intros; contradiction.
    - simpl. intros.
      destruct (filter_fails tq time) eqn:ff.
      assert (ff2:=ff).
      apply IHtq in ff.
      destruct (time <? deadline hq) eqn:dl.
      + split.
        * inversion H.
          intros j INj.
          destruct INj as [EQhq | INq].
          { subst. apply Nat.ltb_lt; eauto. }
          { apply ff. eauto. }
        * inversion H. rewrite H2 in ff. apply ff.
      + split.
        * inversion H. rewrite H1 in ff. apply ff.
        * inversion H.
          intros j INj.
          destruct INj as [EQhq | INq].
          { subst. apply Nat.ltb_ge; eauto. }
          { apply ff. eauto. }
  Qed.

  Lemma filter_fails_origin:
    forall q qt qf time j,
      filter_fails q time = (qt, qf) ->
      In j qt \/ In j qf ->
      In j q.
  Proof.
    intros q.
    induction q as [| qh qt].
    - intros qt qf time j FF [INT | INF].
      + simpl in FF. inversion FF. subst; eauto.
      + simpl in FF. inversion FF. subst; eauto.
    - intros qt' qf time j FF [INT | INF].
      + simpl in FF.
        destruct (filter_fails qt time) eqn:FF2. 
        destruct (time <? deadline qh) eqn:DL.
        * inversion FF. subst.
          destruct INT as [EQqh | INq].
          { subst. left; eauto. }
          { eapply IHqt in FF2; eauto. right; eauto. }
        * inversion FF. subst.
          eapply IHqt in FF2; eauto. right; eauto.
      + simpl in FF.
        destruct (filter_fails qt time) eqn:FF2. 
        destruct (time <? deadline qh) eqn:DL.
        * inversion FF. subst.
          eapply IHqt in FF2; eauto. right; eauto.
        * inversion FF. subst.
          destruct INF as [EQqh | INq].
          { subst. left; eauto. }
          { eapply IHqt in FF2; eauto. right; eauto. }
  Qed.

  Lemma filter_fails_live:
    forall q qt qf time j,
      filter_fails q time = (qt, qf) ->
      In j qt ->
      time < j.(deadline) /\ In j q.
  Proof.
    intros q qt qf time j FF INj.
    assert (FFS:=FF).
    apply filter_fails_spec in FFS.
    destruct FFS as [L F].
    split; eauto.
    eapply filter_fails_origin; eauto.
  Qed.

  Lemma filter_fails_fail:
    forall q qt qf time j,
      filter_fails q time = (qt, qf) ->
      In j qf ->
      j.(deadline) <= time /\ In j q.
  Proof.
    intros q qt qf time j FF INj.
    assert (FFS:=FF).
    apply filter_fails_spec in FFS.
    destruct FFS as [L F].
    split; eauto.
    eapply filter_fails_origin; eauto.
  Qed.

End RUNNING.
