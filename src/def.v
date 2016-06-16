Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Section DEF.
  Record task : Set :=
    Task { task_id:nat; start:nat; period:nat; exec_time:nat}.

  Record job : Set :=
    Job { release_time:nat; deadline:nat; job_task_id:nat; time_left:nat }.

  (* test *)
  Definition task1 := Task 11 0 7 2.
  Definition task2 := Task 12 2 12 3.

  (* lemmas *)

  Theorem task_eq_dec : forall (t1 t2:task), {t1 = t2} + {t1 <> t2}.
  Proof.
    decide equality;
      eauto using PeanoNat.Nat.eq_dec.
  Qed.

  Theorem job_eq_dec : forall (j1 j2:job), {j1 = j2} + {j1 <> j2}.
  Proof.
    decide equality;
      eauto using PeanoNat.Nat.eq_dec.
  Qed.

  Definition queue := list job.

  Definition taskset := list task.

  (* valid taskset : each task has unique id *)
  Definition tset_unique_id (tset:taskset) : Prop :=
    forall (t1 t2:task),
      In t1 tset -> In t2 tset ->
      (t1.(task_id) <> t2.(task_id) \/ t1 = t2).

  Definition valid_tset (tset:taskset) : Prop :=
    tset_unique_id tset /\ NoDup tset.

  Lemma valid_tset_shrink:
    forall tset t,
      valid_tset (t::tset) -> valid_tset tset.
  Proof.
    unfold valid_tset. unfold tset_unique_id.
    intros tset t [UID NOD].
    split.
    - intros; apply UID; right; eauto.
    - inversion NOD; eauto.
  Qed.

  Fixpoint priority_of_tid (tid:nat) (tset:taskset) : option nat :=
  match tset with
  | [] => None
  | th::tl =>
    if (th.(task_id) =? tid) then Some 0 else
      match priority_of_tid tid tl with
      | None => None
      | Some n => Some (1 + n)
      end
  end.

  Inductive valid_queue (tset:taskset) : queue -> Prop :=
  | Q_empty: valid_queue tset []
  | Q_one : forall j (n:nat),
      priority_of_tid j.(job_task_id) tset = Some n ->
      valid_queue tset [j]
  | Q_many : forall j1 j2 jq n1 n2,
      priority_of_tid j1.(job_task_id) tset = Some n1 ->
      priority_of_tid j2.(job_task_id) tset = Some n2 ->
      n1 < n2 ->
      valid_queue tset (j2::jq) ->
      valid_queue tset (j1::j2::jq).

End DEF.

(* valid taskset generator *)
Section TASK_GEN.
  Record task_gen : Set :=
    TaskGen { tset_gen : taskset;
              next_id : nat ;
              validity : valid_tset tset_gen;
              next_id_property :
                forall (t:task),
                  In t tset_gen -> t.(task_id) < next_id
            }.

  Program Definition init_taskgen : task_gen :=
    TaskGen [] 0 _ _.
  Obligation 1.
  unfold valid_tset. unfold tset_unique_id.
  split.
  { intros.
    inversion H. }
  { constructor. }
  Qed.
  Obligation 2.
  contradiction.
  Qed.

  Program Definition add_task (tg:task_gen) (start period exec_time : nat)
    : task_gen :=
    let new_task := Task tg.(next_id) start period exec_time in
    TaskGen (new_task::tg.(tset_gen)) (1 + tg.(next_id))
            _ _.
  Obligation 1.
  unfold valid_tset. unfold tset_unique_id.
  split.
  {
    intros.
    destruct H; destruct H0.
    - try (subst; eauto).
    - apply (next_id_property tg) in H0.
      left. subst. simpl. omega.
    - apply (next_id_property tg) in H.
      left. subst. simpl. omega.
    - apply (validity tg); eauto.
  }
  { assert (VT:=validity tg).
    unfold valid_tset in VT. destruct VT as [UID NOD].
    assert (NID:=next_id_property tg).
    constructor; eauto.
    intros IN.
    apply NID in IN. simpl in IN.
    apply Nat.lt_irrefl in IN. eauto.
  }
  Qed.
  Obligation 2.
  destruct H.
  - subst. eauto.
  - apply (next_id_property tg) in H.
    omega.
  Qed.

End TASK_GEN.

