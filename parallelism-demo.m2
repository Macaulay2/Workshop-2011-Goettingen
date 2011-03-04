allowableThreads
allowableThreads = 4
f = name -> (
     << "starting " << name << endl;
     for i to 2000000 do 0;
     << "ending " << name << endl;
     name | " result");
t = createTask (f, "t")
isReady t
schedule t,isReady t
t
isReady t
taskResult t
t
taskResult t
u = apply("a" .. "p", i -> createTask(f,i))
isReady \ u
schedule \ u;
cancelTask \ u;
isReady \ u
taskResult \ u
p = createTask(f,"p")
q = createTask(f,"q")
r = createTask(f,"r")
addStartTask(p,r)
addStartTask(q,r)
schedule \ {p,q}
p,q,r
taskResult\{p,q,r}
p = createTask(f,"p")
q = createTask(f,"q")
addCancelTask(p,q)
addCancelTask(q,p)
schedule\{p,q}
p,q
taskResult\{p,q}
p = createTask(f,"p")
q = createTask(f,"q")
r = createTask(f,"r")
addDependencyTask(r,p)
addDependencyTask(r,q)
schedule p
p,q,r
schedule q
p,q,r
applyParallel = (L, f) ->(
     collect := createTask identity;
     tasks := for l in L list createTask(f,l);
     for t in tasks do addDependencyTask (collect, t);
     scan(tasks,schedule);
     while not isReady collect do sleep 1;
     taskResult \ tasks)
applyParallel({"a","b","c","d"},f)
