Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Require Import def.
Require Import exec.

Require Import priority_proof.
Require Import exec_proof.
Require Import rm_swap.


(* definition of rate monotonic *)
Definition rate_monotonic (pr:priority_assigner) (tset:taskset) : Prop :=
  forall (t1 t2:task) (n1 n2:nat) (new_tset:taskset),
    new_tset = pr tset -> 
    In t1 new_tset ->
    In t2 new_tset ->
    t1.(period) < t2.(period) <->
    (exists (n1 n2:nat), priority_of_tid t1.(task_id) new_tset = Some n1 /\
                  priority_of_tid t2.(task_id) new_tset = Some n2 /\
                  n1 < n2).


Definition valid_state (st:state) : Prop :=
  valid_tset st.(st_tset) /\ valid_queue st.(st_tset) st.(job_q).

(* Lemma init_valid_state *)

Parameter match_state_int : state -> state -> Prop.
Parameter match_state_int_id : forall (st:state), match_state_int st st.

(* Parameter match_state_init: *)
(*   forall (tset:taskset), match_state (init_state tset) (init_state (pr tset)). *)

Definition match_state (st1 st2:state): Prop :=
  match_state_int st1 st2 /\ st1.(fail_list) = [] /\ st2.(fail_list) = [].

Lemma swap_execute_one:
      forall (sti1 sti2 stf1:state),
        match_state sti1 sti2 ->
        execute_one sti1 = stf1 ->
        exists stf2, execute_one sti2 = stf2 /\
                match_state stf1 stf2.
Proof.
Admitted.

Lemma swap_execute_n:
  forall (n:nat) (sti1 sti2 stf1:state),
    match_state sti1 sti2 ->
    execute_n sti1 n = stf1 ->
    exists stf2, execute_n sti2 n = stf2 /\
            match_state stf1 stf2.
Proof.
  intros n.
  induction n as [| n'].
  { intros sti1 sti2 stf1 MS EX.
    simpl in *.
    inversion EX. subst.
    exists sti2. eauto. }
  { intros sti1 sti2 stf1 MS EX.
    simpl in *.
    destruct (execute_one sti1) eqn:EX1.
    { apply swap_execute_one with (sti2:=sti2) in EX1; eauto.
      destruct EX1 as [s' [EX2 MS2]].
      eapply IHn' in MS2; eauto.
      rewrite EX2. eauto. }
  }
Qed.

Lemma match_identical_states:
  forall (st:state), st.(fail_list) = nil -> match_state st st.
Proof.
  intros.
  unfold match_state.
  split; eauto.
  apply match_state_int_id.
Qed.

Lemma match_swapped_init_states:
  forall (tset tset1 tset2:taskset) (pr:priority_assigner),
    tset1 = pr tset ->
    tset2 = swap_priority_assigner pr tset ->
    match_state (init_state tset1) (init_state tset2).
Proof.
Admitted.

Lemma swap_schedulable_helper:
  forall (n:nat) (pr:priority_assigner) (tset:taskset) (st_f:state),
    valid_priority_assigner pr ->
    valid_tset tset ->
    run pr tset n = st_f ->
    exists (st_f':state), run (swap_priority_assigner pr) tset n = st_f' /\
                     match_state st_f st_f'.
Proof.
  unfold run.
  intros n pr tset.
  remember (pr tset) as tset1 eqn:T1.
  assert (T1':=T1).
  remember ((swap_priority_assigner pr) tset) as tset2 eqn:T2.
  eapply swap_spec in T1; eauto.
  destruct T1 as [[_ EQTL] | SW].
  { rewrite EQTL. intros.
    eexists. split; eauto.
    assert (MS: match_state (init_state tset1) (init_state tset1)).
    { unfold match_state.
      split.
      - apply match_state_int_id.
      - simpl. eauto.
    }
    eapply swap_execute_n in MS; eauto.
    inversion MS; eauto.
    inversion H2. rewrite H1 in H3. rewrite <- H3 in H4. eauto.
  }
  { intros st_f Pcond UID EX.
    eapply swap_execute_n in EX.
    - destruct EX as [stf2 [EX2 MS2]]; eauto.
    - eapply match_swapped_init_states; eauto.
  }
Qed.

Lemma swap_schedulable:
  forall (tset:taskset) (pr:priority_assigner),
    valid_tset tset ->
    valid_priority_assigner pr ->
    schedulable pr tset ->
    schedulable (swap_priority_assigner pr) tset.
Proof.
  unfold schedulable.
  intros tset pr VT Pcond SCH n.
  specialize (SCH n).
  destruct SCH as [st_f [RUN FL]].
  specialize (swap_schedulable_helper n pr tset st_f Pcond VT RUN).
  intros HLP.
  destruct HLP as [stf' [RUN' MS']].
  eexists; eauto. split; eauto.
  unfold match_state in MS'. inversion MS'. inversion H0; eauto.
Qed.

Fixpoint ntimes {X} (f:X->X) (n:nat) : X->X :=
  match n with
  | O => id
  | S n' => compose f (ntimes f n')
  end.

Lemma swap_n_pr_cond:
  forall n pr,
    valid_priority_assigner pr ->
    valid_priority_assigner (ntimes swap_priority_assigner n pr).
Proof.
  induction n as [| n'].
  -  intros. simpl.
     unfold id. eauto.
  - intros pr Pcond.
    simpl.
    apply swap_preserves_valid_priority_assigner.
    apply IHn'. eauto.
Qed.

Lemma swap_n_schedulable:
  forall (tasks:taskset) (pr:priority_assigner),
    valid_tset tasks ->
    valid_priority_assigner pr ->
    schedulable pr tasks ->
    forall (n:nat), schedulable (ntimes swap_priority_assigner n pr) tasks.
Proof.
  intros. generalize dependent tasks. generalize dependent pr.
  induction n.
  - intros pr Pcond tasks UID SCH.
    simpl.
    unfold id.
    auto.
  - intros pr Pcond tasks UID SCH.
    simpl.
    unfold compose.
    apply swap_schedulable; eauto.
    apply swap_n_pr_cond. eauto.
Qed.


Lemma swap_eventually_rm:
  forall (tset:taskset) (pr:priority_assigner),
  exists (n:nat), rate_monotonic (ntimes swap_priority_assigner n pr) tset.
Proof.
Admitted.

Theorem rm_is_optimal:
  forall (tset:taskset),
  forall (pr:priority_assigner),
    valid_tset tset ->
    valid_priority_assigner pr ->
    schedulable pr tset ->
    exists (rm_pr:priority_assigner),
      rate_monotonic rm_pr tset /\
      schedulable rm_pr tset.
Proof.
  intros tset pr UID Pcond SCH.
  assert (X:=swap_eventually_rm).
  specialize (X tset pr).
  destruct X as [swap_n RM].
  apply swap_n_schedulable with (n:=swap_n) (pr:=pr) in SCH; eauto.
Qed.
