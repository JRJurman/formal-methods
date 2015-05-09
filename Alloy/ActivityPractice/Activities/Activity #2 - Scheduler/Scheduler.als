open util/ordering[Step] as step
sig Step{}

/**
		The set of tasks, including the idle task.
*/
enum Task {IDLE, Java, Python, Ruby}

/**
		The (one and only) Scheduler.
*/
one sig Scheduler {
	onCPU :			Task -> Step,	// the task using the CPU
	blocked :		Task -> Step,	// the set of blocked tasks
	runnable :	Task -> Step	// the set of runnable tasks
}

pred OneTaskOnCPU[st : Step]{
	all st : Step |
		one Scheduler.onCPU.st
}

/**
		All tasks are either runnable or blocked, and
		no task is both runnable and blocked.
		(i.e., blocked and runnable partition task)
*/
pred Partitioning[st : Step] {
	Scheduler.(runnable.st + blocked.st) = Task
	no Scheduler.runnable.st & Scheduler.blocked.st
}

/**
		The IDLE task is always runnable.
*/
pred IDLE_Task_Runnable[st : Step] {
	IDLE in Scheduler.runnable.st
}

/**
		The IDLE task is on the cpu if and only if
		there are no other runnable tasks.
*/
pred IDLE_Task_LastToRun[st : Step] {
	IDLE = Scheduler.onCPU.st <=> IDLE =  Scheduler.runnable.st
}

/**
		The task on the CPU is a runnable task.
*/
pred onCPU_is_Runnable[st : Step] {
		Scheduler.onCPU.st in Scheduler.runnable.st
}

pred Invariant[st : Step] {
	OneTaskOnCPU[st]
	Partitioning[st]
	IDLE_Task_Runnable[st]
	IDLE_Task_LastToRun[st]
	onCPU_is_Runnable[st]
}

pred init[st : Step] {
//	Scheduler.onCPU.st != IDLE
	one Scheduler.onCPU.st
	Scheduler.onCPU.st + IDLE = Scheduler.runnable.st
	Scheduler.blocked.st = Task - IDLE - Scheduler.onCPU.st
}

pred init_exists {
	Invariant[step/first]
	init[step/first]
}
run init_exists for 4 but exactly 1 Step

assert init_closed {
	all st : Step | init[st] => Invariant[st]
}
check init_closed for 4 but exactly 1 Step

/*
 * Block the task currently on the CPU
 */
pred block[st : Step] {
	/*
   * Precondition
	 */
	st != step/last
	Scheduler.onCPU.st != IDLE

	let st' = next[st] {
	/*
	 * Effects
	 */
		Scheduler.runnable.st' = Scheduler.runnable.st - Scheduler.onCPU.st
		Scheduler.blocked.st' = Scheduler.blocked.st + Scheduler.onCPU.st

		IDLE = Scheduler.runnable.st' => Scheduler.onCPU.st' = IDLE
		IDLE != Scheduler.runnable.st' => 
			(			
				Scheduler.onCPU.st' in Scheduler.runnable.st' - IDLE &&
				one Scheduler.onCPU.st'
			)
	}
}

assert block_closed {
	all st : Step - (step/last) {
		Invariant[st] && block[st] => Invariant[next[st]]
	}
}
check block_closed for 4 but exactly 2 Step

pred block_exists {
	Invariant[step/first]
	block[step/first]
	Invariant[ next[step/first] ]
}
run block_exists for 4 but exactly 2 Step

pred unblock[st : Step, t L task] {
	st != last
	t in Scheduler.blocked.st

	let st' = next[st] {
		Scheduler.runnable.st' = Scheduler.runnable.st + t
		Scheduler.blocked.st' = Scheduler.blocked.st - t
		Scheduler.onCPU.st = IDLE => Scheduler.onCPU.set' = t
		Scheduler.onCPU.st != IDLE => Scheduler.onCPU.st' = Scheduler.onCPU.st
	}
}







