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
straighten = method()
straighten(List) := t -> (
     sg := t/(i->sgn i)//product;
     h := new MutableHashTable from {};
     t = apply(t, i->sort(i));
     straighten(t, h);
     new HashTable from apply(keys h#t,i->(i => sg*h#t#i))
     )

straighten(List, MutableHashTable) := (t, h) -> (
     if t != apply(t, i -> sort i) then error"Debug";
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


end

restart
load "tableaux.m2"
straighten({{3,2},{1}})
straighten({{2,3},{1}})
straighten({{3,2},{2,3}})
straighten({{4,1},{3,2}})
straighten({{3,2,1},{3,2}})
straighten({{4,2,3,3,3},{1,2}})

straighten({{3,2},{3,2},{1},{1}})
t = {{3,2},{3,2},{1},{1}}

compositions({6,0,0,0},5)
standardTableaux({3},{1,1,1})
standardTableaux({2,1},{1,1,1})
standardTableaux({1,1,1},{1,1,1})
standardTableaux({2,1},{3})

standardTableaux({3,3,3},{1,1,1,1,1,1,1,1,1})
#oo
loadPackage"SchurRings"
S = schurRing(QQ,s,6)
scalarProduct(s_{2}^3,s_{4,2}) == #standardTableaux({4,2},{2,2,2})

restart
load "tableaux.m2"
loadPackage"SchurRings"
--sym^n(sym^d)

n = 3
d = 2

S = schurRing(QQ,s,n*d)
pl = plethysm(s_{n},s_{d})
s_{d}^n

rho = toList(n:d)
lam = {4,2}

sTab = standardTableaux(lam,rho)
R = QQ[apply(sTab,i->z_i)]

perms = permutations splice{1..n}
rels = {}

per = perms#2
tab = sTab#1

for per in perms do
     for tab in sTab do
     (
	  str = straighten perTab(per,tab);
     	  rels = rels | {z_tab-sum for ke in keys str list(try z_ke * str#ke else 0)};
	  )
     
I = ideal rels
#sTab - numgens source mingens I
mingens I
rels
straighten({{3,2},{1}})
straighten({{2,1},{3}})
straighten({{3,2},{3,2},{1},{1}})
straighten({{2,1},{2,1},{3},{3}})
straighten({{4,1},{3,2}})
