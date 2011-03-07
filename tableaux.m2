---------------
---Compositions
---------------
local ncomp;
local lcomp;
local tempcomp;

compositions(List,ZZ) := (l,n) ->
(
     k := #l;
     d := sum(l)-l#(k-1);
     ncomp = 0;
     lcomp = new MutableList;
     tempcomp = new MutableList;
     comp(l,n,d);
     toList lcomp
     )

comp = method()
comp(List,ZZ,ZZ) := (l,n,d) ->
(
     k := #l;
     if k == 1 then 
     (
	  tempcomp#0 = n;
	  if n<=l#0 then
	  (
	       lcomp#ncomp = toList tempcomp;
	       ncomp = ncomp + 1;
	       );
	  )
     else for p from max(n-d,0) to min(l#(k-1),n) do     
     (
	  tempcomp#(k-1) = p;
	  comp(drop(l,-1),n-p,d-l#(k-2));
	  );
     )

---------------------
----Standard Tableaux
---------------------

--tableaux are given by lists of their column entries
--assumed to be skew symmetric within columns

local tempTab
local tempLam
local auxlam
local auxrho
local auxc
local auxk
local listOfTableaux

standardTableaux = method()
standardTableaux(List,List) := (lam,rho) ->
(
     auxlam = lam;
     auxrho = rho;
     auxc = lam#0;
     auxk = #lam;
     tempTab = new MutableList from auxk:{};--partially constructed tableau
     tempLam = new MutableList from auxk:0;--lengths of rows of tempTab     
     nc := join({auxc},splice{auxk:0});--number of columns of a given size
     listOfTableaux = {};
     stdTabRec(nc,0);
     listOfTableaux               
     )

stdTabRec = method()
stdTabRec(List,ZZ) := (nc,i) ->
(
if i == #auxrho then listOfTableaux = listOfTableaux | {tabTranspose(toList tempTab)} else
(     
  bdscomp := new MutableList from auxk:0;
  cate := nc#auxk;
  for j from 1 to auxk do
  (
       bdscomp#(auxk-j) = min(auxlam#(auxk-j)-cate,nc#(auxk-j));
       cate = cate + nc#(auxk-j);
       );
  for comp in compositions(toList bdscomp,auxrho#i) do
  (
       for j from 0 to #auxlam-1 do 
       (
	    tempTab#j = tempTab#j | toList(comp#j:i+1);
	    tempLam#j = tempLam#j + comp#j;
	    );
       stdTabRec(nc-(comp|{0})+({0}|comp),i+1);
       for j from 0 to #auxlam-1 do 
       (
	    tempLam#j = tempLam#j - comp#j;
	    tempTab#j = drop(tempTab#j,-comp#j);
	    );
       );
     )
)

tabTranspose = method()
tabTranspose(List) := tab ->
(
     lam := apply(tab,i->#i);
     newTab := new MutableList from (lam#0:{});
     for i from 0 to #lam-1 do
     	  for j from 0 to lam#i-1 do
	       newTab#j = newTab#j | {tab#i#j};
     toList newTab
     )

perTab = method()
perTab(List,List) := (per,tab) ->
(
     apply(tab,i->apply(i,j->per#(j-1)))
     )

----------------
------Steven Sam
----------------

-- Input: 
-- List T: a tableau, e.g., {{0,1,2},{2,3}}
-- Output:
-- If T not standard (weakly increasing rows, increasing columns), return 
-- first violating entry (starting from bottom to top, left to right);
-- otherwise return null
isStandard = T -> (
     i := #T-2;
     while i >= 0 do (
	  a := T#i;
	  b := T#(i+1);
	  n := #b;
	  for j from 0 to n-1 do if a#j > b#j then return (i,j);
	  i = i-1;
	  );
     null
     )

-- Input:
-- List T: a tableau
-- Integer col: specify a column
-- Integer row{1,2}, specify two rows
-- Output:
-- Take all entries in row1 from column col to the end and all entries in
-- row2 from beginning to col, and return all possible permutations of these
-- entries (ignoring that some entries might be equal). The output is given in 
-- the form a hash table where the keys are the resulting tableau and the 
-- values are -1
shuffle = (T, col, row1, row2) -> (
     len1 := #(T#row1);
     len2 := #(T#row2);
     truncatedrow1 := (T#row1)_{0..col-2}; -- grab row1 entries
     truncatedrow2 := (T#row2)_{col..len2-1}; -- grab row2 entries
     L := join((T#row1)_{col-1..len1-1}, (T#row2)_{0..col-1});
     sgnL := sgn L;
     P := permutations L;
     output := {};
--     error "Debug me";
{*     P = apply(P, i-> (for j from 0 to #T-1 list (
		    if j == row1 then sort join(truncatedrow1, i_{0..len1-col})
	       	    else if j == row2 then sort join(i_{len1-col+1..#i-1}, truncatedrow2)
	       	    else T#j)));
*}
     
     P = apply(P, i-> (sgn(join(truncatedrow1, i_{0..len1-col}))*sgn(join(i_{len1-col+1..#i-1}, truncatedrow2))*sgn(i)*sgnL,
	            (for j from 0 to #T-1 list (
		    if j == row1 then sort join(truncatedrow1, i_{0..len1-col})
	       	    else if j == row2 then sort join(i_{len1-col+1..#i-1}, truncatedrow2)
	       	    else T#j))));

     
     coeff := 0;
     for i in P do if last i == T then coeff = coeff + first i;
     if coeff == 0 then return new HashTable from {} else
     (
     	  for i in P do if last i != T then output = append(output, (last i, (first i) * (-1) / coeff));
     	  return hashTable(plus, output);
	  )
     )

-- Input:
-- List T: a tableau
-- Output:
-- Writes T as a linear combination of other tableaux T' s.t. T'<T if T is not 
-- standard, otherwise writes T = T. The equalities are expressed in a hash 
-- table which contains tableaux T_i as keys and their values c_i which 
-- represent coefficients: T = c_1T_1 + ... + c_nT_n
towardStandard = T -> (
     x := isStandard T;
     if x === null then return new HashTable from {T=>1};
     H := new MutableHashTable from shuffle(T, x#1+1, x#0, x#0+1);
     if H #? T then (
	  coeff := -(H#T) + 1;
	  remove(H,T);
	  prehash := {};
	  for i in keys H do 
	  prehash = append(prehash, (i, H#i / coeff));
	  return hashTable(prehash)
     	  ) 
     else return new HashTable from H
     )

-- Input:
-- List t: a tableau
-- MutableHashTable h: a hash table which memoizes recursive calls and 
-- stores the coefficients of the straightening of t into standard tableaux
STRAIGHT = new MutableHashTable;
straighten = method()
straighten(List) := t -> (
     sg := t/(i->sgn i)//product;
     if sg == 0 then return new HashTable from {};
     t = apply(t, i->sort(i));
     if STRAIGHT#?t then new HashTable from apply(keys STRAIGHT#t,i->(i=> sg*STRAIGHT#t#i)) else
     (
     h := new MutableHashTable from {};
     straighten(t, h);
     STRAIGHT#t = new HashTable from h#t; 
     new HashTable from apply(keys h#t,i->(i => sg*h#t#i))
     )
     )

straighten(List, MutableHashTable) := (t, h) -> (
     sg := t/(i->sgn i)//product;
     if sg == 0 then (h#t = new HashTable from {};return null;);
     if h #? t then return null;
     if isStandard(t) === null then 
     h#t = new HashTable from {t => 1};
     
     firstIter := towardStandard(t);
     H := hashTable({}); -- straightening of t
     for i in keys firstIter do (
	  coeff := firstIter#i;
     	  straighten(i, h);
	  temp := {};
	  for j in keys h#i do temp = append(temp, (j, coeff * (h#i)#j));
	  H = merge(H, hashTable(temp), plus);
     	  temp = {};
	  for j in keys H do if H#j != 0 then temp = append(temp,(j,H#j));
	  H = hashTable(temp);
	  );
     h#t = H;
     return null;
     )

------
sgn = method()
sgn(List) := l ->
(
     n := #l-1;
     sg := 1;
     for i from 0 to n-1 do
     	  for j from i+1 to n do
	       if l#i>l#j then sg = -sg else
	       if l#i == l#j then (sg = 0;break;);
     sg
     )

-------Generate all the partitions of a set
-------with a given shape
locS = local locS;
locL = local locL;
locLengthL = local locLengthL;
locParts = local locParts;
locPartitions = local locPartitions;
genPartitions = local genPartitions;

genPartitions = method()
genPartitions(ZZ) := (k)->
(
     if k==length locS then (locLPos = locLPos | {toList locPos}) else
     (
     for i from 0 to locLengthL-1 do
     	  if (#locParts#i<locL#i) then
	  (
	       locParts#i = locParts#i | {locS#k};
	       locPos#k = i+1;
	       genPartitions(k+1);
	       locParts#i = drop(locParts#i,-1);
	       );
     )
);

partitions(List,BasicList) := (S,L)->
(
     locS = toList S;
     locL = L;
     locLengthL = #L;
     locParts = new MutableList;
     locPos = new MutableList;
     for i from 0 to locLengthL-1 do locParts#i = {};
     locLPos = {};
     genPartitions(0);
     locLPos
     )

--------end generate partitions

----2nd secant
secondSecant = method()
secondSecant(List,List,List) := (lam0,lam1,lam2) ->
(
     tlam0 := toList conjugate new Partition from lam0;
     spar := 0;
     T0 := for i from 0 to #tlam0 - 1 list (l = splice{spar+1..spar+tlam0#i};spar = spar + tlam0#i;l);
     sTab1 := StdTab#(lam1,splice{d:1});
     sTab2 := StdTab#(lam2,splice{d:1});
     indR := flatten for i in sTab1 list for j in sTab2 list {i,j};
     print(#indR);
     gensR := indR/(i->z_i);
     R := QQ[gensR,MonomialSize=>4];
     QR := QQ[];
     rels := matrix{#indR:{0_QR}};

     time for col in T0 do
     	  for i from 0 to #col-2 do
	  (
	       j := #col-1;
     	       print("straighten");
	       time newsTab1 := apply(sTab1,T -> straighten(T/(c->(c/(r->if r == col#i then col#j
					else if r == col#j then col#i
					else r)))));
	       time newsTab2 := apply(sTab2,T -> straighten(T/(c->(c/(r->if r == col#i then col#j
					else if r == col#j then col#i
					else r)))));
	       print("relations");
     	       rel := mutableMatrix(QR,#sTab1*#sTab2,#sTab1*#sTab2);
	       c := 0;
	       time for i1 from 0 to #sTab1-1 do
	       	    for i2 from 0 to #sTab2-1 do
		    (
			 T := {sTab1#i1,sTab2#i2};
			 strT1 := newsTab1#i1;
			 strT2 := newsTab2#i2;
			 for a in keys strT1 do
			      for b in keys strT2 do
			      	   rel_(index(z_({a,b})),c) = strT1#a*strT2#b;
			 rel_(index(z_T),c) = rel_(index(z_T),c) + 1;
			 c = c + 1;
			 );
	       rels = rels | matrix(rel);
	       );
      for co from 0 to #T0-2 do
      (
 	       col := T0#co;
	       j := T0#(co+1)#0;
	       newsTab1 := new MutableList;
	       newsTab2 := new MutableList;
	       print("straighten");
	       time for i from 0 to #col - 1 do
	       (
		    newsTab1#i = apply(sTab1,T -> straighten(T/(c->(c/(r->if r == col#i then j
					     else if r == j then col#i
					     else r)))));
	       	    newsTab2#i = apply(sTab2,T -> straighten(T/(c->(c/(r->if r == col#i then j
					     else if r == j then col#i
					     else r)))));
		    );
	       print("relations");
	       rel := mutableMatrix(QR,#sTab1*#sTab2,#sTab1*#sTab2);
	       c := 0;
     	       time for i1 from 0 to #sTab1-1 do
	       	    for i2 from 0 to #sTab2-1 do
     	       	    (
		    T := {sTab1#i1,sTab2#i2};
     		    for i from 0 to #col - 1 do
		    (
			 strT1 := newsTab1#i#i1;
			 strT2 := newsTab2#i#i2;
			 for a in keys strT1 do
			      for b in keys strT2 do
			      	   rel_(index(z_({a,b})),c) = rel_(index(z_({a,b})),c)+strT1#a*strT2#b;
			 );
		    rel_(index(z_T),c) = rel_(index(z_T),c) - 1;
  		    c = c + 1;
		    );
	       rels = rels | matrix(rel);
	   );
     time if rels != 0 then
     (
     	  print(numgens source rels);
	  grb := gb(rels);
     	  grbin := forceGB leadTerm grb;
     	  mat := id_(QR^(#indR)) % grbin;
     	  indR = select(for i from 0 to #indR-1 list if mat_{i} != 0 then indR#i else null,i->i=!= null);
     	  gensR = indR/(i->z_i);
     	  R = QQ[gensR,MonomialSize=>4];
     	  print(#indR);
	  print(#indR == scalarProduct(internalProduct(Q_(lam0),Q_(lam1)),Q_(lam2)));
	  );
     
     kerf := ideal(1_R);
     
for p in kpar do
(
     sT0 := StdTab#(lam0,p);
     sT1 := StdTab#(lam1,p);
     sT2 := StdTab#(lam2,p);
     gensS := sT0/(i->A_i)|sT1/(i->B_i)|sT2/(i->C_i);
     S := QQ[gensS,MonomialSize=>4];
     if #gensS == 0 then continue;--because kernel of map to QQ[] has a bug
     f := map(S,R,for T in indR list
	  (
     	       T1 := T#0;
	       T2 := T#1;
	       pars := partitions(splice{1..d},p);
	       sum for pa in pars list
	       (
		    sTr0 := straighten(T0/(i->(i/(j->pa#(j-1)))));
		    pA := apply(keys sTr0,i->if (sTr0#i == 0) then 0 else sTr0#i * A_i)//sum;
		    sTr1 := straighten(T1/(i->(i/(j->pa#(j-1)))));
		    pB := apply(keys sTr1,i->if (sTr1#i == 0) then 0 else sTr1#i * B_i)//sum;
		    sTr2 := straighten(T2/(i->(i/(j->pa#(j-1)))));
		    pC := apply(keys sTr2,i->if (sTr2#i == 0) then 0 else sTr2#i * C_i)//sum;
		    pA*pB*pC
		    )
	       ));
     kerf = intersect(kerf, ker f);
     kerf = ideal({0_R}|select(flatten entries gens kerf,i->degree i == {1}));
     );
--(numgens R-numgens source mingens kerf,(gens R)%kerf)
numgens R-numgens source mingens kerf
--mingens kerf
)

recsyz = method()
recsyz (Thing) := (el) -> min(el,0)
recsyz (RingElement) := (el) ->
(
     T := ring el;
     listForm el/((u,v)->T_u*recsyz(v))//sum
     )
----end 2nd secant

end

restart
load "tableaux.m2"
loadPackage"SchurRings"
S = schurRing(QQ,s,6)
scalarProduct(s_{2}^3,s_{4,2}) == #standardTableaux({4,2},{2,2,2})

restart
load "tableaux.m2"
loadPackage"SchurRings"
--sym^n(sym^d)

n = 5
d = 3

S = schurRing(QQ,s,n*d)
pl = plethysm(s_{n},s_{d})
s_{d}^n

rho = toList(n:d)
lam = {5,5,3,1,1}

sTab = standardTableaux(lam,rho);
#sTab
R = QQ[apply(sTab,i->z_i)]

perms = permutations splice{1..n};
rels = {}

time for per in perms do
     for tab in sTab do
     (
     	  print(per,tab);
	  time str = straighten perTab(per,tab);
     	  rels = rels | {z_tab-sum for ke in keys str list(try z_ke * str#ke else 0)};
	  )
     
I = ideal rels;
#sTab - numgens source mingens I
mgI = mingens I;
mgI

k = 3
kpar = select(partitions n,i->#i==k)
kers = {}

par = kpar#0

for par in kpar do
(
     sTabs = standardTableaux(lam,d*toList(par));
     T = QQ[apply(sTabs,i->z_i)];
     f = map(T,R,some list);--what's the list?
     kers = kers | {ker f};
     )


--Weyman,Landsberg - 2nd secant of Segre
restart
loadPackage"SchurRings"
load"tableaux.m2"

d = 9
k = 3

Q = schurRing(QQ,q,d)
S1 = schurRing(QQ,s1,3)
S2 = schurRing(S1,s2,3)
S3 = schurRing(S2,s3,3)

s = s1_{1}*s2_{1}*s3_{1}
sP = symmetricPower(d,s);


partsd = select(partitions d,i->#i<=k)/(i->toList i);
kpar = select(partsd,i->#i==k);

StdTab = new MutableHashTable;
time for lam in partsd do
     for par in kpar do
     	  StdTab#(lam,par) = standardTableaux(lam,par)

par = splice{d:1}
time for lam in partsd do
     StdTab#(lam,par) = standardTableaux(lam,par);
     
pd = partsd

hilbFcnd = 0

--secondSecant({9},{7,2},{7,2})

for i0 from 0 to #pd-1 do
     for i1 from i0 to #pd-1 do
     	  for i2 from i1 to #pd-1 do
	  (
     	       lam0 := pd#i0;
	       lam1 := pd#i1;
	       lam2 := pd#i2;
	       if recsyz(sP - S1_lam0*S2_lam1*S3_lam2) == 0 then
	       (
		    print(lam0,lam1,lam2);
		    coeff := secondSecant(lam2,lam1,lam0);
     	       	    plam = permutations({lam2,lam1,lam0});
		    for pe in plam do
		    (
			 mon = S1_(pe#0)*S2_(pe#1)*S3_(pe#2);
			 if recsyz(hilbFcnd-mon) != 0 then hilbFcnd = hilbFcnd + coeff*mon;
			 )
		    )
     	       )
hilbFcnd
--hilbFcnd-sP+S1_{2,1,1}*S2_{2,1,1}*S3_{2,1,1}*s--degree 5--works
--hilbFcnd-sP+S1_{2,1,1}*S2_{2,1,1}*S3_{2,1,1}*symmetricPower(2,s)-S1_{4,1,1}*S2_{2,2,2}*S3_{2,2,2}-S2_{4,1,1}*S1_{2,2,2}*S3_{2,2,2}-S3_{4,1,1}*S2_{2,2,2}*S1_{2,2,2}-S1_{2,2,1}*S2_{2,2,1}*S3_{2,2,1}*s--degree 6--works
--hilbFcnd-sP+S1_{2,1,1}*S2_{2,1,1}*S3_{2,1,1}*symmetricPower(3,s)-(S1_{4,1,1}*S2_{2,2,2}*S3_{2,2,2}+S2_{4,1,1}*S1_{2,2,2}*S3_{2,2,2}+S3_{4,1,1}*S2_{2,2,2}*S1_{2,2,2})*s-S1_{2,2,1}*S2_{2,2,1}*S3_{2,2,1}*symmetricPower(2,s)+S1_{2,2,2}*S2_{2,2,2}*S3_{2,2,2}*s--degree 7--works
time hilbFcnd-sP+S1_{2,1,1}*S2_{2,1,1}*S3_{2,1,1}*symmetricPower(4,s)-(S1_{4,1,1}*S2_{2,2,2}*S3_{2,2,2}+S2_{4,1,1}*S1_{2,2,2}*S3_{2,2,2}+S3_{4,1,1}*S2_{2,2,2}*S1_{2,2,2})*symmetricPower(2,s)-S1_{2,2,1}*S2_{2,2,1}*S3_{2,2,1}*symmetricPower(3,s)+S1_{2,2,2}*S2_{2,2,2}*S3_{2,2,2}*symmetricPower(2,s)--degree 8--works


Q = schurRing(QQ,q,6)
internalProduct(q_{3,1,1},q_{3,1,1})