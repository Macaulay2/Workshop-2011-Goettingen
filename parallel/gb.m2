load "~/Goettingen-2011/parallel/parallel.m2"

-- benchmark code
needsPackage "Markov"

-- If you have enough memory 2(# of cpus)+1 is OK.
allowableThreads = 4

-- Lets compute the GB of some ideal from algebraic statistics 100 times
R = markovRing (3,3,2,2)
S = {{{1},{2},{3,4}},{{3},{4},{1,2}}}
jobs = for t in 1..50 list markovIdeal(R,S);

timing1 = timing gb markovIdeal(R,S)
-- 1.5 seconds on my machine

--caveat: Can't use time for this one b/c it only measures 
--the time that the scheduling takes

start = currentTime();pscan (jobs, gb); stop = currentTime();
timeTaken = stop-start

--66 seconds on my machine, so approx 1.32 seconds per GB.
--There is an overhead!
