Require Import Coq.Lists.List.
Require Import Program.
Require Import Omega.

Require Import def.

Section EXEC_HELPERS.

  Fixpoint find_task_id (tid:nat) (tset:taskset): option task :=
    match tset with
    | [] => None
    | t::tl =>
      if (Nat.eqb t.(task_id) tid) then Some t else find_task_id tid tl
    end.

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

  Fixpoint add_job_to_queue (tset:taskset) (j:job) (q:queue) : queue :=
    match q with
    | [] => [j]
    | h::t =>
      match priority_of_tid j.(job_task_id) tset,
            priority_of_tid h.(job_task_id) tset with
      | Some n, Some m => 
        if n <? m
        then j::q
        else h::(add_job_to_queue tset j t)
      | _, _ => q
      end
    end.

  Fixpoint add_jobs_to_queue (tset:taskset) (newq:queue) (q:queue)
    : queue :=
    match newq with
    | [] => q
    | j::newq' =>
      let nq := add_job_to_queue tset j q in
      add_jobs_to_queue tset newq' nq
    end.

  Fixpoint generate_new_jobs (tset:taskset) (time:nat) : queue :=
    match tset with
    | [] => []
    | t::tl =>
      match get_next_nth_of_task t time with
      | None => generate_new_jobs tl time
      | Some n =>
        (nth_job_of_task t n)::generate_new_jobs tl time
      end
    end.

  Definition add_new_jobs (tset:taskset) (time:nat) (jq:queue)
    : queue :=
    let newjobs := generate_new_jobs tset time in
    add_jobs_to_queue tset newjobs jq.

End EXEC_HELPERS.

Section EXEC.
    Record state : Set :=
    State { st_tset: taskset;
            time:nat;
            job_q:queue;
            fail_list: queue
          }.

  Definition filter_fails (q:queue) (time:nat) : queue * queue :=
    partition (fun job => (Nat.ltb time job.(deadline))) q.

  Definition execute_one (cur:state) : state :=
    match cur with
    | State tset time jq fl =>
      let jq_at_start := add_new_jobs tset time jq in
      let jq_at_end :=
          match jq_at_start with
          | [] => []
          | job::rest =>
            let new_time_left := job.(time_left) - 1 in
            if (Nat.eqb new_time_left 0)
            then rest
            else (Job job.(release_time) job.(deadline) job.(job_task_id) new_time_left)::rest
          end
      in
      let (lives, fails) := filter_fails jq_at_end (1 + time) in
      State tset (1+time) lives fails
    end.

  Fixpoint execute_n (cur_state:state) (n:nat) : state :=
    match n with
    | O => cur_state
    | S n' => execute_n (execute_one cur_state) n'
    end.

  Definition priority_assigner : Type := taskset -> taskset.

  Definition valid_priority_assigner
             (pr:priority_assigner) : Prop :=
    forall (tset:taskset) (t:task),
      valid_tset tset ->
      (In t tset <-> In t (pr tset)) /\
      valid_tset (pr tset).

  Definition init_state (tset:taskset): state :=
    State tset 0 nil nil.

  Definition run (pr:priority_assigner) (tset:taskset) (n:nat) : state :=
    let sorted_tset := pr tset in
    execute_n (init_state sorted_tset) n.

  Definition schedulable (pr:priority_assigner) (tset: taskset) :=
    forall n:nat, exists final_state, run pr tset n = final_state /\
                          final_state.(fail_list) = nil.

End EXEC.
