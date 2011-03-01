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

-- benchmark code

needsPackage "Markov"

-- If you have enough memory 2(# of cpus)+1 is OK.
allowableThreads = 3

-- Lets compute the GB of some ideal from algebraic statistics 100 times
R = markovRing (3,3,2,2)
S = {{{1},{2},{3,4}},{{3},{4},{1,2}}}
jobs = for t in 1..50 list markovIdeal(R,S);

timing1 = timing gb markovIdeal(R,S)
-- 1.5 seconds on my machine

--caveat: Can't use time for this one b/c it only measures 
--the time that the scheduling takes

start = currentTime();
pscan (jobs, gb); stop = currentTime();

--approximation in seconds
timeTaken = stop-start

--66 seconds on my machine, so approx 1.32 seconds per GB.
--There is an overhead!

