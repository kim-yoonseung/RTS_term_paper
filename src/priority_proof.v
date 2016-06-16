Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Require Import def.

(* Lemmas for priority_of_task *)

Lemma existent_task_priority:
  forall (t:task) (tset:taskset),
    In t tset -> exists (n:nat), priority_of_tid t.(task_id) tset = Some n.
Proof.
  intros t tset.
  induction tset.
  - intros IN. inversion IN.
  - intros IN.
    inversion IN.
    + exists 0. simpl. subst.
      rewrite (Nat.eqb_refl (task_id t)). eauto.
    + apply IHtset in H.
      destruct H.
      simpl.
      destruct (task_id a =? task_id t).
      * eauto.
      * rewrite H. eauto.
Qed.

Lemma priority_less_than_length:
  forall (t:task) (tset:taskset) (n:nat),
    priority_of_tid t.(task_id) tset = Some n ->
    n < length tset.
Proof.
  intros t tset.
  induction tset; intros n PR.
  - inversion PR.
  - simpl in PR.
    destruct (task_id a =? task_id t).
    + inversion PR. simpl. omega.
    + destruct (priority_of_tid (task_id t) tset).
      * destruct n; inversion PR.
        simpl.
        apply lt_n_S.
        apply IHtset.
        eauto.
      * inversion PR.
Qed.

Lemma priority_tid_unique:
  forall (tid1 tid2:nat) (tset:taskset) (n:nat),
    valid_tset tset ->
    priority_of_tid tid1 tset = Some n ->
    priority_of_tid tid2 tset = Some n ->
    tid1 = tid2.
Proof.
  intros tid1 tid2 tset.
  induction tset.
  - intros. inversion H0.
  - intros.
    simpl in *.
    destruct (task_id a =? tid1) eqn:EQ1;
      destruct (task_id a =? tid2) eqn:EQ2.
    + apply beq_nat_true in EQ1.
      apply beq_nat_true in EQ2.
      omega.
    + inversion H0. subst.
      destruct (priority_of_tid tid2 tset).
      * inversion H1.
      * inversion H1.
    + inversion H1; subst.
      destruct (priority_of_tid tid1 tset).
      * inversion H0.
      * inversion H0.
    + destruct (priority_of_tid tid1 tset);
        destruct (priority_of_tid tid2 tset).
      * destruct n.
        ++ inversion H0.
        ++ inversion H0; inversion H1; subst.
           eapply IHtset; eauto.
           eapply valid_tset_shrink; eauto.
      * inversion H1.
      * inversion H0.
      * inversion H0.
Qed.

Lemma priority_unique:
  forall (t1 t2:task) (tset:taskset) (n:nat),
    valid_tset tset ->
    In t1 tset -> In t2 tset ->
    priority_of_tid t1.(task_id) tset = Some n ->
    priority_of_tid t2.(task_id) tset = Some n ->
    t1 = t2.
Proof.
  intros t1 t2 tset.
  induction tset; intros n VALID IN1 IN2 PR1 PR2.
  - inversion PR1.
  - destruct (Nat.eq_dec (task_id t1) (task_id a)) eqn:DEC1;
      destruct (Nat.eq_dec (task_id t2) (task_id a)) eqn:DEC2.
    + assert (EQ12: t1 = t2).
      { eapply VALID in IN1. eapply IN1 in IN2.
        destruct IN2 as [NEQ | EQ]; eauto.
        exfalso. apply NEQ. rewrite e. rewrite e0. reflexivity. }
      eauto.
    + simpl in PR1, PR2.
      rewrite e in PR1. rewrite Nat.eqb_refl in PR1.
      destruct (task_id a =? task_id t2) eqn:EQid.
      * apply beq_nat_true in EQid.
        exfalso. apply n0. rewrite EQid. reflexivity.
      * inversion PR1. subst.
        destruct (priority_of_tid (task_id t2) tset).
        ++ inversion PR2.
        ++ inversion PR2.
    + simpl in PR1, PR2.
      rewrite e in PR2. rewrite Nat.eqb_refl in PR2.
      destruct (task_id a =? task_id t1) eqn:EQid.
      * apply beq_nat_true in EQid.
        exfalso. apply n0. rewrite EQid. reflexivity.
      * inversion PR2. subst.
        destruct (priority_of_tid (task_id t1) tset).
        ++ inversion PR1.
        ++ inversion PR1.
    + destruct n.
      { inversion PR1.
        destruct (task_id a =? task_id t1) eqn:EQid.
        - apply beq_nat_true in EQid.
          exfalso. apply n0. eauto.
        - destruct (priority_of_tid (task_id t1) tset); inversion H0.
      }
      apply IHtset with (n:=n).
      * eapply valid_tset_shrink; eauto.
      * inversion IN1; eauto. exfalso. subst. eauto.
      * inversion IN2; eauto. exfalso. subst. eauto.
      * simpl in PR1.
        destruct (task_id a =? task_id t1) eqn:EQid.
        ++ inversion PR1.
        ++ destruct (priority_of_tid (task_id t1) tset); inversion PR1; eauto.
      * simpl in PR2.
        destruct (task_id a =? task_id t2) eqn:EQid.
        ++ inversion PR2.
        ++ destruct (priority_of_tid (task_id t2) tset); inversion PR2; eauto.
Qed.
