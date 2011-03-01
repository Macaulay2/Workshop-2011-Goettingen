-- Disclaimer:

-- You can only use apply or scan in parallel if the jobs to be done
-- are independent of each other.

pscan = (L, f) ->(
     -- A trivial task that will depend on all the other tasks
     waitforfinish = () -> true;
     collect = createTask waitforfinish;
     -- create all the tasks to be done     
     tasks = for l in L list (
     	  createTask (f, l)
	  );
     -- make them dependent on the collecting task
     for t in tasks do addDependencyTask (collect, t);
     -- start everybody
     for t in tasks do schedule t;
     schedule collect;
     while not isReady (collect) do sleep 1;
     )

papply = (L, f) ->(
     -- A trivial task that will depend on all the other tasks
     waitforfinish = () -> true;
     collect = createTask waitforfinish;
     -- create all the tasks to be done     
     tasks = for l in L list (
     	  createTask (f, l)
	  );
     -- make them dependent on the collecting task
     for t in tasks do addDependencyTask (collect, t);
     -- start everybody
     for t in tasks do schedule t;
     schedule collect;
     while not isReady (collect) do sleep 1;
     return for t in tasks list taskResult(t)
     )


