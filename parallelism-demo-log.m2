
+ /Users/dan/src/M2/trunk/BUILD/dan/builds.tmp/mac64.production/StagingArea/x86_64-MacOS-10.6/bin/M2 --no-readline --print-width 113
Macaulay2, version 1.4.0.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, LLLBases, PrimaryDecomposition, ReesAlgebra,
               TangentCone

i1 : allowableThreads

o1 = 2

i2 : allowableThreads = 4

o2 = 4

i3 : f = name -> (
          << "starting " << name << endl;
          for i to 2000000 do 0;
          << "ending " << name << endl;
          name | " result");

i4 : t = createTask (f, "t")

o4 = <<task, created>>

o4 : Thread

i5 : isReady t

o5 = false

i6 : schedule t,isReady t

o6 = (<<task, created>>, false)

o6 : Sequence

i7 : starting t
ending t

     t

o7 = <<task, result available, task done>>

o7 : Thread

i8 : isReady t

o8 = true

i9 : taskResult t

o9 = t result

i10 : t

o10 = <<task, result delivered, task terminated>>

o10 : Thread

i11 : taskResult t
stdio:16:1:(3): error: thread result already retrieved

i12 : u = apply("a" .. "p", i -> createTask(f,i))

o12 = (<<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>, <<task,
      -----------------------------------------------------------------------------------------------------------
      created>>, <<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>,
      -----------------------------------------------------------------------------------------------------------
      <<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>, <<task, created>>)

o12 : Sequence

i13 : isReady \ u

o13 = (false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
      -----------------------------------------------------------------------------------------------------------
      false)

o13 : Sequence

i14 : schedule \ u;

i15 : starting a
starting b
starting c
ending c
starting d
ending b
starting e
ending a
starting f
ending d
starting g
ending e
starting h
ending f
starting i
cancelTask \ u;

i16 : stdio:5:26:(3):[1]: error: interrupted
stdio:5:26:(3):[1]: error: interrupted
stdio:5:26:(3):[1]: error: interrupted
isReady \ u

o16 = (true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false)

o16 : Sequence

i17 : u

o17 = (<<task, result available, task done>>, <<task, result available, task done>>, <<task, result available,
      -----------------------------------------------------------------------------------------------------------
      task done>>, <<task, result available, task done>>, <<task, result available, task done>>, <<task, result
      -----------------------------------------------------------------------------------------------------------
      available, task done>>, <<task, result available, task done>>, <<task, result available, task done>>,
      -----------------------------------------------------------------------------------------------------------
      <<task, result available, task done>>, <<task, running, cancellation requested>>, <<task, running,
      -----------------------------------------------------------------------------------------------------------
      cancellation requested>>, <<task, running, cancellation requested>>, <<task, running, cancellation
      -----------------------------------------------------------------------------------------------------------
      requested>>, <<task, running, cancellation requested>>, <<task, running, cancellation requested>>, <<task,
      -----------------------------------------------------------------------------------------------------------
      running, cancellation requested>>)

o17 : Sequence

i18 : p = createTask(f,"p")

o18 = <<task, created>>

o18 : Thread

i19 : q = createTask(f,"q")

o19 = <<task, created>>

o19 : Thread

i20 : r = createTask(f,"r")

o20 = <<task, created>>

o20 : Thread

i21 : addStartTask(p,r)

i22 : addStartTask(q,r)

i23 : schedule \ {p,q}

o23 = {<<task, created>>, <<task, created>>}

o23 : List

i24 : starting p
starting q
ending p
starting r
ending q
{*dummy position*} error: expected a function
ending r
p,q,r

o24 = (<<task, result available, task done>>, <<task, result available, task done>>, <<task, result available,
      -----------------------------------------------------------------------------------------------------------
      task done>>)

o24 : Sequence

i25 : taskResult\{p,q,r}

o25 = {p result, q result, r result}

o25 : List

i26 : p = createTask(f,"p")

o26 = <<task, created>>

o26 : Thread

i27 : q = createTask(f,"q")

o27 = <<task, created>>

o27 : Thread

i28 : addCancelTask(p,q)

i29 : addCancelTask(q,p)

i30 : schedule\{p,q}

o30 = {<<task, created>>, <<task, created>>}

o30 : List

i31 : starting p
starting q
ending p
stdio:5:26:(3):[1]: error: interrupted

      p,q

o31 = (<<task, result available, task done>>, <<task, result available, task done>>)

o31 : Sequence

i32 : taskResult\{p,q}

o32 = {p result, }

o32 : List

i33 : p = createTask(f,"p")

o33 = <<task, created>>

o33 : Thread

i34 : q = createTask(f,"q")

o34 = <<task, created>>

o34 : Thread

i35 : addCancelTask(p,q)

i36 : schedule p

o36 = <<task, created>>

o36 : Thread

i37 : starting p
ending p

      q

o37 = <<task, running, cancellation requested>>

o37 : Thread

i38 : schedule q

o38 = <<task, running, cancellation requested>>

o38 : Thread

i39 : schedule q

o39 = <<task, running, cancellation requested>>

o39 : Thread

i40 : q

o40 = <<task, running, cancellation requested>>

o40 : Thread

i41 : taskResult q
stdio:48:1:(3): error: thread not done yet

i42 : p = createTask(f,"p")

o42 = <<task, created>>

o42 : Thread

i43 : q = createTask(f,"q")

o43 = <<task, created>>

o43 : Thread

i44 : r = createTask(f,"r")

o44 = <<task, created>>

o44 : Thread

i45 : addDependencyTask(r,p)

i46 : addDependencyTask(r,q)

i47 : schedule p

o47 = <<task, created>>

o47 : Thread

i48 : starting p
ending p

      p,q,r

o48 = (<<task, result available, task done>>, <<task, created>>, <<task, created>>)

o48 : Sequence

i49 : schedule q

o49 = <<task, created>>

o49 : Thread

i50 : starting q
ending q
starting r
ending r

      p,q,r

o50 = (<<task, result available, task done>>, <<task, result available, task done>>, <<task, result available,
      -----------------------------------------------------------------------------------------------------------
      task done>>)

o50 : Sequence

i51 : applyParallel = (L, f) ->(
           collect := createTask identity;
           tasks := for l in L list createTask(f,l);
           for t in tasks do addDependencyTask (collect, t);
           scan(tasks,schedule);
           while not isReady collect do sleep 1;
           taskResult \ tasks)

o51 = applyParallel

o51 : FunctionClosure

i52 : applyParallel({"a","b","c","d"},f)
starting a
starting b
starting c
ending b
starting d
ending c
ending a
ending d

o52 = {a result, b result, c result, d result}

o52 : List

i53 : -- end of buffer parallelism-demo.m2

i54 : 