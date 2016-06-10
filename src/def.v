Require Export Coq.Lists.List.

Require Export Program.

Require Export Omega.

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

Definition task_id_of_job (j:job) : nat :=
  match j with
  | Job _ _ tid _ => tid
  end.

Definition queue := list job.

Record taskset : Set :=
  Taskset { tlist : list task ;
    next_id : nat ;
    id_unique :
      forall (t1 t2:task),
        In t1 tlist /\ In t2 tlist ->
        (t1.(task_id) <> t2.(task_id) \/ t1 = t2) ;
    next_id_property :
      forall (t:task),
        In t tlist -> t.(task_id) < next_id
  }.

(* generation of taskset *)
Program Definition empty_taskset : taskset :=
  Taskset [] 0 _ _.
Obligation 2.
contradiction.
Qed.

Program Definition add_task (tasks:taskset) (start period exec_time : nat)
  : taskset :=
  let new_task := Task tasks.(next_id) start period exec_time in
  Taskset (new_task::tasks.(tlist)) (1 + tasks.(next_id))
           _ _.
Obligation 1.
destruct H; destruct H0.
- try (subst; eauto).
- apply (next_id_property tasks) in H0.
  left. subst. simpl. omega.
- apply (next_id_property tasks) in H.
  left. subst. simpl. omega.
- apply (id_unique tasks). eauto.
Qed.
Obligation 2.
destruct H.
- subst. eauto.
- apply (next_id_property tasks) in H.
  omega.
Qed.

Fixpoint priority_of_task_int (t:task) (taskl:list task) : option nat :=
  match taskl with
  | [] => None
  | h::tl =>
    if (task_eq_dec t h) then Some 0 else
      match priority_of_task_int t tl with
      | None => None
      | Some n => Some (1 + n)
      end
  end.

Definition priority_of_task (t:task) (tasks:taskset) : option nat :=
  priority_of_task_int t tasks.(tlist).

(* Lemmas for priority_of_task *)

Lemma existent_task_priority_helper:
  forall (t:task) (taskl:list task),
    In t taskl ->
    exists (n:nat), priority_of_task_int t taskl = Some n.
Proof.
  intros t taskl.
  induction taskl.
  - intros IN. inversion IN.
  - intros IN.
    inversion IN.
    + exists 0. simpl. subst.
      destruct (task_eq_dec t t); eauto.
      exfalso. eauto.
    + apply IHtaskl in H.
      destruct H.
      simpl.
      destruct (task_eq_dec t a).
      * eauto.
      * rewrite H. eauto.
Qed.

Lemma existent_task_priority:
  forall (t:task) (tasks:taskset),
    In t tasks.(tlist) ->
    exists (n:nat), priority_of_task t tasks = Some n.
Proof.
  intros.
  unfold priority_of_task.
  apply existent_task_priority_helper. eauto.
Qed.

Lemma priority_less_than_length:
  forall (t:task) (taskl:list task) (n:nat),
    priority_of_task_int t taskl = Some n ->
    n < length taskl.
Proof.
  intros t taskl.
  induction taskl; intros n PR.
  - inversion PR.
  - simpl in PR.
    destruct (task_eq_dec t a).
    + inversion PR. simpl. apply Nat.lt_0_succ.
    + destruct (priority_of_task_int t taskl).
      * destruct n; inversion PR.
        simpl.
        apply lt_n_S.
        apply IHtaskl.
        eauto.
      * inversion PR.
Qed.

Lemma priority_unique_helper:
  forall (t1 t2:task) (taskl:list task) (n:nat),
    In t1 taskl -> In t2 taskl ->
    priority_of_task_int t1 taskl = Some n ->
    priority_of_task_int t2 taskl = Some n ->
    t1 = t2.
Proof.
  intros t1 t2 taskl.
  induction taskl; intros n IN1 IN2 PR1 PR2.
  - inversion PR1.
  - destruct (task_eq_dec t1 a) eqn:DEC1;
      destruct (task_eq_dec t2 a) eqn:DEC2.
    + subst; eauto.
    + simpl in PR1, PR2.
      rewrite DEC1 in PR1; rewrite DEC2 in PR2.
      inversion PR1. subst.
      destruct (priority_of_task_int t2 taskl); inversion PR2.
    + simpl in PR1, PR2.
      rewrite DEC1 in PR1; rewrite DEC2 in PR2.
      inversion PR2. subst.
      destruct (priority_of_task_int t1 taskl); inversion PR1.
    + destruct n.
      { inversion PR1.
        rewrite DEC1 in H0.
        destruct (priority_of_task_int t1 taskl); inversion H0. }
      apply IHtaskl with (n:=n).
      * inversion IN1; eauto. exfalso. eauto.
      * inversion IN2; eauto. exfalso. eauto.
      * simpl in PR1. rewrite DEC1 in PR1.
        destruct (priority_of_task_int t1 taskl); inversion PR1; eauto.
      * simpl in PR2. rewrite DEC2 in PR2.
        destruct (priority_of_task_int t2 taskl); inversion PR2; eauto.
Qed.

Lemma priority_unique:
  forall (t1 t2:task) (tasks:taskset) (n:nat),
    In t1 tasks.(tlist) -> In t2 tasks.(tlist) ->
    priority_of_task t1 tasks = Some n ->
    priority_of_task t2 tasks = Some n ->
    t1 = t2.
Proof.
  intros t1 t2 tasks.
  eapply priority_unique_helper.
Qed.  


(* running *)

Fixpoint find_task_id (tid:nat) (taskl:list task): option task :=
  match taskl with
  | [] => None
  | t::tl =>
    if (Nat.eqb t.(task_id) tid) then Some t else find_task_id tid tl
  end.

Definition find_task_id_from_tasks (tid:nat) (tasks:taskset): option task :=
  find_task_id tid tasks.(tlist).

Lemma find_task_id_helper:
  forall (tid:nat) (t:task) (taskl:list task)
    (UNIQ_ID: forall (t1 t2 : task),
       In t1 taskl /\ In t2 taskl -> task_id t1 <> task_id t2 \/ t1 = t2),
    find_task_id tid taskl = Some t <->
    In t taskl /\ t.(task_id) = tid.
Proof.
  intros.
  revert t tid.
  induction taskl; intros.
  - split.
    + intros. inversion H.
    + intros. inversion H. inversion H0.
  - assert (UNIQ_ID2 :forall t1 t2 : task, In t1 taskl /\ In t2 taskl -> task_id t1 <> task_id t2 \/ t1 = t2).
    {
      intros.
      apply UNIQ_ID.
      destruct H as [IN1 IN2].
      split; right; eauto.
    }
    split.
    + intros FIND.
      simpl in FIND.
      destruct (task_id a =? tid) eqn:EQB_ID.
      * split.
        { left. inversion FIND; eauto. }
        { apply beq_nat_true. inversion FIND. subst. eauto. }
      * apply IHtaskl in FIND; eauto.
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
          specialize (UNIQ_ID a t).
          assert (INS: In a (a::taskl) /\ In t (a::taskl)).
          { split; eauto.
            left. eauto. }
          apply UNIQ_ID in INS.
          destruct INS as [NEQ | EQ].
          - subst. contradiction.
          - subst. eauto.
        }
        { apply IHtaskl; eauto. }
Qed.
  
Lemma find_task_id_from_tasks_spec:
  forall (tid:nat) (t:task) (tasks:taskset),
    find_task_id_from_tasks tid tasks = Some t <->
    In t tasks.(tlist) /\ t.(task_id) = tid.
Proof.
  intros.
  unfold find_task_id_from_tasks.
  apply find_task_id_helper.
  apply tasks.(id_unique).
Qed.
           
Record state : Set :=
  State { tasks: taskset;
          time:nat;
          job_q:queue;
          jobs_from_tasks:
            forall (j:job),
              In j job_q ->
              exists t, find_task_id_from_tasks j.(job_task_id) tasks = Some t
        }.

Definition nth_job_of_task (t:task) (n:nat): job :=
  match t with
  | Task id s p e => Job (s + p * n) (s + p * n + p) id e
  end.

Definition get_next_nth_of_task (t:task) (time:nat) : option nat :=
  if (Nat.ltb time t.(start)) then None
  else
    let net_time := time - t.(start) in
    let n := Init.Nat.div net_time t.(period) in
    if (Nat.eqb (n * t.(period)) net_time) then Some n else None
.

Theorem get_next_nth_of_task_property:
  forall (t:task) (time:nat) (nth:nat),
    get_next_nth_of_task t time = Some nth ->
    (nth_job_of_task t nth).(release_time) = time.
Proof.
  intros.
  unfold nth_job_of_task.
  unfold get_next_nth_of_task in H.
  destruct (time0 <? start t) eqn:START; [inversion H| ].
  destruct ((time0 - start t) / period t * period t =? time0 - start t) eqn:EQB; [| inversion H].
  destruct t.
  simpl in *.
  inversion H.
  apply beq_nat_true in EQB.
  rewrite Nat.mul_comm.
  rewrite EQB.
  apply Nat.ltb_ge in START.
  apply le_plus_minus_r. eauto.
Qed.

(* Fixpoint priority_of_tid (tid:nat) (taskl: list task) : Option nat := *)
(*   match taskl with *)
(*   | [] => None *)
(*   | t::tl => *)
(*     if t.(task_id) = tid then  *)
  

Fixpoint add_job_to_queue (job_priority:job -> option nat) (j:job) (q:queue) : queue :=
  match q with
  | [] => [j]
  | h::t =>
    match job_priority j, job_priority h with
    | Some n, Some m => 
      if n <? m
      then j::q
      else h::(add_job_to_queue job_priority j t)
    | _, _ => q
    end
  end.

Lemma add_job_to_queue_spec:
  forall (jp:job->option nat) (ji j:job) (q:queue),
    In j (add_job_to_queue jp ji q) ->
    In j q \/ (j = ji).
Proof.
  intros jp ji j q.
  revert ji j.
  induction q.
  - intros. simpl in H.
    inversion H; eauto.
  - intros ji j IN.
    simpl in IN.
    destruct (jp ji); eauto.
    destruct (jp a); eauto.
    destruct (n <? n0) eqn:LTB.
    { inversion IN; eauto. }
    { inversion IN.
      - left. left. eauto.
      - apply IHq in H.
        inversion H.
        + left. right. eauto.
        + right; eauto.
    }
Qed.        

Fixpoint add_new_jobs_from_task_list (job_priority:job -> option nat) (taskl:list task) (time:nat) (q:queue) : queue :=
    match taskl with
    | [] => q
    | t::tl =>
      match get_next_nth_of_task t time with
      | None => add_new_jobs_from_task_list job_priority tl time q
      | Some n =>
        let new_q := add_job_to_queue job_priority (nth_job_of_task t n) q in
        add_new_jobs_from_task_list job_priority tl time new_q
      end
    end.

Definition priority_of_job (tasks:taskset) (j:job) : option nat :=
  match find_task_id j.(job_task_id) tasks.(tlist) with
  | None => None
  | Some t => priority_of_task t tasks
  end.

Definition add_new_jobs (tasks:taskset) (time:nat) (jq:queue) : queue :=
  let job_priority : job -> option nat := priority_of_job tasks in
  add_new_jobs_from_task_list job_priority tasks.(tlist) time jq.

Lemma add_new_jobs_spec_helper:
  forall (jp:job -> option nat) (taskl:list task)
    (time:nat) (jq:queue) (j:job)
    (UNIQ_ID: forall (t1 t2 : task),
        In t1 taskl /\ In t2 taskl -> task_id t1 <> task_id t2 \/ t1 = t2),
    In j (add_new_jobs_from_task_list jp taskl time jq) ->
    In j jq \/
    exists (t:task), find_task_id j.(job_task_id) taskl = Some t.
Proof.
  intros jp taskl.
  induction taskl.
  - intros. eauto.
  - intros time jq j UNIQ_ID IN.
    assert (UNIQ_ID2 :forall t1 t2 : task, In t1 taskl /\ In t2 taskl -> task_id t1 <> task_id t2 \/ t1 = t2).
    {
      intros.
      apply UNIQ_ID.
      destruct H as [IN1 IN2].
      split; right; eauto.
    }
    simpl in IN.
    destruct (get_next_nth_of_task a time) eqn:NTH.
    + apply IHtaskl in IN; eauto.
      destruct IN as [IN | FROM_TASK].
      * apply add_job_to_queue_spec in IN.
        destruct IN; eauto.
        right. exists a. simpl.
        unfold nth_job_of_task in H.
        destruct a. subst. simpl.
        rewrite Nat.eqb_refl. eauto.
      * right. destruct FROM_TASK as [t FIND].
        exists t. simpl.
        destruct (task_id a =? job_task_id j) eqn:EQB_ID; eauto.
        apply beq_nat_true in EQB_ID.
        rewrite <- EQB_ID in FIND.
        apply find_task_id_helper in FIND; eauto.
        destruct FIND as [INt EQ_ID].
        assert (INS: In a (a :: taskl) /\ In t (a :: taskl)).
        { split.
          - left. eauto.
          - right. eauto. }
        apply UNIQ_ID in INS.
        inversion INS.
        -- exfalso. apply H. eauto.
        -- subst. eauto.
    + apply IHtaskl in IN; eauto.
      destruct IN as [IN | EXT]; eauto.
        destruct EXT as [t FIND].
        right. exists t. simpl.
        destruct (task_id a =? job_task_id j) eqn:EQB_ID; eauto.
        apply beq_nat_true in EQB_ID.
        rewrite <- EQB_ID in FIND.
        apply find_task_id_helper in FIND; eauto.
        destruct FIND as [INt EQ_ID].
        assert (INS: In a (a :: taskl) /\ In t (a :: taskl)).
        { split.
          - left. eauto.
          - right. eauto. }
        apply UNIQ_ID in INS.
        inversion INS.
        -- exfalso. apply H. eauto.
        -- subst. eauto.
Qed.

Lemma add_new_jobs_spec:
  forall (tasks:taskset) (time:nat) (jq:queue) (j:job),
    In j (add_new_jobs tasks time jq) ->
    In j jq \/
    exists (t:task), find_task_id_from_tasks j.(job_task_id) tasks = Some t.
Proof.
  intros.
  unfold add_new_jobs in H.
  apply add_new_jobs_spec_helper with (jp:=priority_of_job tasks0) (time:=time0); eauto.
  apply tasks0.(id_unique).
Qed.

Fixpoint check_queue (time:nat) (q: queue) : bool :=
  (* if there's a job whose deadline is equal or less than cur deadline, return false, else return true *)
  match q with
  | [] => true
  | h::t =>
    if (Nat.leb h.(deadline) time) then false
    else check_queue time t
  end.

  
Program Definition execute_one (cur:state) : option state :=
  match cur with
  | State tasks time jq P =>
    if check_queue time jq
    then
      let new_jq := add_new_jobs tasks time jq in
      match new_jq with
      | [] => Some (State tasks (1 + time) [] _)
      | job::rest_jq =>
        let new_time_left := job.(time_left) - 1 in
        let final_jq :=
            if (Nat.eqb new_time_left 0)
            then rest_jq
            else (Job job.(release_time) job.(deadline) job.(job_task_id) new_time_left)::rest_jq
        in
        Some (State tasks (1 + time) final_jq _)
      end
    else None
  end.
Obligation 1.
contradiction.
Qed.
Obligation 2.
(* TODO *)




Fixpoint execute_n (cur_state:state) (n:nat) : option state :=
  match n with
  | O => Some cur_state
  | S n' =>
    match (execute_one cur_state) with
    | None => None
    | Some st => execute_n st n'
    end
  end.

Record priority_assigner: Type :=
  { sorter : taskset -> taskset;
    task_preservation :
      forall (tasks:taskset) (t:task),
        In t tasks.(tlist) <-> In t (sorter tasks).(tlist)
  }.

Definition run (pr:priority_assigner) (tasks:taskset) (n:nat) : option state :=
  let sorted_tasks := pr.(sorter) tasks in
  let init_state := State sorted_tasks 0 nil in
  execute_n init_state n.

Definition schedulable (pr:priority_assigner) (tasks: taskset) :=
  forall n:nat, exists final_state, run pr tasks n = Some final_state.

(* 1. optimality of RM *)
Section RM_optimality_proof.

  Definition rate_monotonic (f:priority_assigner) (tasks:taskset) : Prop :=
    forall (new_tasks:taskset),
      new_tasks = f.(sorter) tasks ->
      forall (t1 t2:task) (n1 n2:nat),
        In t1 new_tasks.(tlist) ->
        In t2 new_tasks.(tlist) ->
        t1.(period) < t2.(period) <->
        (exists (n1 n2:nat), priority_of_task t1 new_tasks = Some n1 /\
                      priority_of_task t2 new_tasks = Some n2 /\
                      n1 < n2).

  Section SWAP.
    Fixpoint swap_list (taskl:list task) : list task :=
      match taskl with
      | [] => []
      | h1::t1 =>
        match t1 with
        | [] => [h1]
        | h2::t2 =>
          if (Nat.ltb h2.(period) h1.(period))
          then
            h2::h1::t2
          else
            h1::(swap_list t1)
        end
      end.

    Lemma swap_list_preserves_length:
      forall (taskl:list task), length taskl = length (swap_list taskl).
    Proof.
      intros taskl.
      induction taskl; eauto.
      simpl.
      destruct taskl; eauto.
      destruct (period t <? period a); eauto.
      rewrite IHtaskl.
      eauto.
    Qed.

    Lemma swap_list_preserves_tasks:
      forall (t:task) (taskl:list task),
        In t taskl <-> In t (swap_list taskl).
    Proof.
      intros t taskl.
      assert (LEN:exists n, n = length taskl).
      { eexists. reflexivity. }
      destruct LEN as [len LENEQ].
      generalize dependent taskl.
      induction len; intros taskl LENEQ.
      - destruct taskl.
        + split; eauto.
        + inversion LENEQ.
      - destruct taskl.
        + inversion LENEQ.
        + split.
          * intros IN.
            destruct (task_eq_dec t t0) eqn:DEC.
            -- simpl.
               destruct taskl; eauto.
               destruct (period t1 <? period t0).
               ++ right. left. eauto.
               ++ left. eauto.
            -- simpl.
               destruct taskl; eauto.
               destruct (period t1 <? period t0).
               ++ inversion IN.
                  ** right. left. eauto.
                  ** inversion H.
                     { left. eauto. }
                     { right. right. eauto. }
               ++ right.
                  apply IHlen with (taskl:=t1::taskl).
                  ** eauto.
                  ** destruct IN.
                     { exfalso. eauto. }
                     { eauto. }
          * intros IN.
            simpl in IN.
            destruct taskl; eauto.
            destruct (period t1 <? period t0).
            ++ inversion IN.
               ** right. left. eauto.
               ** inversion H.
                  { left. eauto. }
                  { right. right. eauto. }
            ++ destruct IN.
               ** left. eauto.
               ** right.
                  apply IHlen with (taskl:=t1::taskl); eauto.
    Qed.

    Program Definition swap (tasks:taskset) : taskset :=
      Taskset (swap_list tasks.(tlist))
               tasks.(next_id) _ _.
    Obligation 1.
    apply (id_unique tasks0).
    split; apply swap_list_preserves_tasks; eauto.
    Qed.
    Obligation 2.
    apply (next_id_property tasks0).
    apply swap_list_preserves_tasks. eauto.
    Qed.

    Lemma swap_preserves_tasks:
      forall (t:task) (tasks:taskset), In t tasks.(tlist) <-> In t (swap tasks).(tlist).
    Proof.
      intros.
      destruct tasks0.
      simpl.
      apply swap_list_preserves_tasks.
    Qed.

    Program Definition swap_priority_assigner (pr:priority_assigner)
      : priority_assigner :=
      {| sorter := fun tl => swap (pr.(sorter) tl);
         task_preservation := _ |}.
    Obligation 1.
    rewrite (task_preservation pr).
    eapply swap_preserves_tasks.
    Qed.

  End SWAP.
  
  Lemma swap_schedulable:
    forall (tasks:taskset) (pa:priority_assigner),
      schedulable pa tasks ->
      schedulable (swap_priority_assigner pa) tasks.
  Proof.
  Admitted.

  Fixpoint ntimes {X} (f:X->X) (n:nat) : X->X :=
    match n with
    | O => id
    | S n' => compose f (ntimes f n')
    end.

  Lemma swap_n_schedulable:
    forall (tasks:taskset) (pa:priority_assigner),
      schedulable pa tasks ->
      forall (n:nat), schedulable (ntimes swap_priority_assigner n pa) tasks.
  Proof.
    intros. revert tasks0 pa H.
    induction n.
    - intros tasks pa SCH.
      simpl.
      unfold id.
      auto.
    - intros.
      simpl.
      unfold compose.
      apply swap_schedulable.
      apply IHn.
      eauto.
  Qed.

  Lemma swap_eventually_rm:
    forall (tasks:taskset) (pa:priority_assigner),
    exists (n:nat), rate_monotonic (ntimes swap_priority_assigner n pa) tasks.
  Proof.
  Admitted.

  Theorem rm_is_optimal:
    forall (tasks:taskset),
    forall (pa:priority_assigner),
      schedulable pa tasks ->
      exists (rm_pa:priority_assigner),
        rate_monotonic rm_pa tasks /\
        schedulable rm_pa tasks.
  Proof.
    intros tasks pa SCH.
    assert (X:=swap_eventually_rm).
    specialize (X tasks pa).
    destruct X as [swap_n RM].
    apply swap_n_schedulable with (n:=swap_n) in SCH.
    eexists. eauto.
  Qed.

End RM_optimality_proof.


(* 2. define schedulability checker and prove that
  yes => schedulable *)

Section RM_schedulability_checker.

  Variable rm : fixed_priority_assigner.

  (* TODO : axioms for rm *)
  
  Fixpoint CI_checker (tasks:taskset): bool :=
    (* TODO *)
    true.

  Theorem A:
    forall (tasks:taskset),
      CI_checker tasks = true ->
      schedulable (fixed_lifter rm) tasks.
  Proof.
  Admitted.
  
End RM_schedulability_checker.
