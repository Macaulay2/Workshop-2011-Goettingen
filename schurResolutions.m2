loadPackage"SchurRings"

recsyz = method()
recsyz (Thing) := (el) -> min(el,0)
recsyz (RingElement) := (el) ->
(
     T := ring el;
     listForm el/((u,v)->T_u*recsyz(v))//sum
     )

schurResolution = method()

schurResolution(RingElement,List,ZZ,ZZ) := (rep,M,d,c) ->
(
     schurRes(rep,M,d,c)
     )

schurResolution(RingElement,List,ZZ) := (rep,M,d) ->
(
     schurRes(rep,M,d,0)
     )

schurRes = method()
schurRes(RingElement,List,ZZ,ZZ) := (rep,M,d,c) ->
(
     T = ring rep;
     n := schurLevel T;
     plets := new MutableList;
     plets#0 = 1_T;
     for i from 1 to d do plets#i = plethysm({i},rep);
     
     mods := new MutableList from (M | toList((d+1-#M):0));
     
     notdone := true;
     k := 0;
     syzy := new MutableList;
     syzy#k = {};
     local mo;
     
     while notdone do
     (
	  for i from 0 to d do
	  (
     	       mo = 0_T;	       
	       for sy in syzy#k do
	       	    if sy#0 <= i then mo = mo + sy#1 * plets#(i-sy#0)
		    else break;
	       mo = mo - mods#i;
	       newsyz = recsyz(mo);
	       if newsyz != 0 then syzy#k = syzy#k | {(i,-newsyz)};
	       mods#i = mo - newsyz;
	       );
     	  if c == 0 then notdone = not (syzy#k == {})
	  else notdone = (k<c);
     	  k = k + 1;
	  print k;
	  syzy#k = {};
 	  );
     select(toList syzy,i-> i != {})
     )

end

restart
load "schurResolutions.m2"

S = schurRing(QQ,s,4)
rep = s_{2}
M = {1_S,s_{2},s_{4},s_{6},s_{8},s_{10}}
d = 4
c = 2
schurResolution(rep,M,d,c)
schurResolution(rep,M,d)


T1 = schurRing(QQ,t1,2)
T2 = schurRing(T1,t2,2)
T3 = schurRing(T2,t3,2)
rep = T1_{1}*T2_{1}*T3_{1}
d = 6
c = 2
M = {1_T3} | apply(splice{1..d},i->T1_{i}*T2_{i}*T3_{i})
schurResolution(rep,M,d,c)
schurResolution(rep,M,d)

R1 = schurRing(QQ,r1,6)
R2 = schurRing(R1,r2,3)
k = 3 --maximal minors
rep = R1_{1}*R2_{1}
d = 6
c = 4
M = {1_R2} | apply(splice{1..d},i->(select(partitions i,j->#j < 3)/(l->toList l))/(par->R1_par*R2_par)//sum)
time schurResolution(rep,M,d)
