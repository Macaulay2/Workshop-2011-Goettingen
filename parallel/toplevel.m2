restart
load "~/Goettingen-2011/parallel/parallel.m2"

longlist = for i in 1..3 list for i in 1..10000 list i;
f = (li) -> sort flatten li;
time f(longlist);
-- 2.4 seconds


-- estimate on one cpu: 2.4 * 50 = 120 seconds
allowableThreads = 3

jobs = for t in 1..50 list longlist;
start = currentTime();pscan (jobs, f); stop = currentTime();
stop-start

--71 seconds -- perfect!

allowableThreads = 2
jobs = for t in 1..50 list longlist;
start = currentTime();pscan (jobs, f); stop = currentTime();
stop-start

-- 123 seconds