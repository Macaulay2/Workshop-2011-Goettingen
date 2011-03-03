newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "Inferring nested canalyzing functions for given time-course
    data",
    DebuggingMode => true
)
installPackage "RationalPoints";


export{interpolate, idealOfPoints, ncfIdeal, kernPhi, getSingleNcfList, getNcfLists}
--returns a List of Nested Canalyzing Functions for the given HashTable of one variable
--MHT is the table with the expermental data, 
--permutation is a list with the wanted permutation,
--and fieldChar is the Characteristic
getSingleNcfList = method()
getSingleNcfList (HashTable, List, ZZ) := List => (MHT, Permutation, fieldChar) -> (
     n := #first keys MHT; -- Get number of variables
     L := subsets n;
     L = apply( L, l -> apply( l, i -> i + 1) ) ;
     C := ZZ/fieldChar[apply( L, l -> (getSymbol "c")_l)];
     QC := C /ideal apply(gens C, x ->x^fieldChar-x);
     B := QC[apply( L, l -> (getSymbol "b")_l), MonomialOrder => Eliminate 2^n];
     QB := B / ideal apply(gens B, x -> x^fieldChar-x);
     R := QB[(getSymbol "x")_1..(getSymbol "x")_n];
     QR := R / ideal apply(gens R, x -> x^fieldChar-x);
     g := interpolate(MHT,QR);
     h := idealOfPoints(MHT,QR) ;
     ncf := ideal flatten entries gens gb ideal(apply( L, t -> 
	       ncfIdeal( t, QR, Permutation))|{(gens C)#(numgens C-1)-1}
     );
     ncf = lift(ncf, C);
     G := kernPhi(g,h,QR);
     solutions := primaryDecomposition(G+ncf);
     s := apply( solutions, I -> rationalPoints I );
     apply( s, ss -> sum ( subsets gens R, flatten ss, (x, c) -> c*(product x) ) )   
   )

-- construct the generators for the ideal that encodes the relation of
-- coefficients for n-- ideal with relation of coefficients for nested canalyzing functions
-- equation 3.8 in Jarrah et al
-- given a subset S \subseteq [n], return the relation of that generator
ncfIdeal = method()
ncfIdeal (List, Ring, List) := RingElement => (S, QR, Sigma) -> (
  n := numgens QR;
  -- c_{ l } = (gens QR)#indeces#l
  indeces := new MutableHashTable;
  L := subsets n;
  L = apply( L, l -> apply( l, i -> i + 1 ));
  apply( #L, i -> indeces#(L#i) = Sigma#i );
  rS := max S;
  compl := toList (set( 1..rS)  -  set S);
  C := gens coefficientRing coefficientRing QR;
  C#(indeces#S) - C#(indeces#(toList (1..rS))) *
    product( compl, i -> 
      C#( indeces#(toList (set (1..n) - set {Sigma#i} ) ))
    )
)

--returns a list "Ls" of lists of CNFs for each variable,
--"Ls"_i is a list with the CNFs of the ith variable matching the input data 
getNcfLists = method()
getNcfLists (Matrix , List, ZZ) := List=> (inputMatrix,Permutation,fieldChar) ->
(
   
     rows:= numgens target inputMatrix;
     assert(rows>1);
     fullDataHashTable := new MutableHashTable;
     fullDataHashTable# (flatten entries  inputMatrix^{0} ) = flatten entries inputMatrix^{1};
     currentRow:=1;
     while (currentRow<rows -1) do
     (
	  if (fullDataHashTable#?(flatten entries  inputMatrix^{currentRow})===false) then
	       fullDataHashTable#(flatten entries  inputMatrix^{currentRow} ) = flatten entries inputMatrix^{currentRow+1}
	  else
	       if (fullDataHashTable#(flatten entries  inputMatrix^{currentRow})!= fullDataHashTable# (flatten entries  inputMatrix^{currentRow+1})) then
		    throw "inconsistent input data ";
	  currentRow=currentRow+1;
     );
     cols := numgens source inputMatrix;
     resultFunctionListOfLists:={};
          apply(cols, currCol->
	       (
		    dataHashTableForSingleVar:=copy fullDataHashTable;
		    apply(keys fullDataHashTable, key -> 
			 dataHashTableForSingleVar#key=(fullDataHashTable#key)_currCol
		    );
	            currFunctionList:=getSingleNcfList(dataHashTableForSingleVar,Permutation,fieldChar);
		    resultFunctionListOfLists=resultFunctionListOfLists |{currFunctionList};	       
	 ));
     resultFunctionListOfLists
)


  
-- generate a function that interpolates a given time course
-- T is a Hash table, with T#Input(t)=Output(t+1)
interpolate = method() 
interpolate (HashTable, Ring) := (T, R) -> (
  sum (keys T, A -> T#A * product(numgens R, i -> ( 1- ( (gens R)_i - A_i) )))
) 

-- construct generator for the ideal that vanishes on all given time points
-- only access the keys of the hashtable T
idealOfPoints = method()
idealOfPoints(HashTable, Ring) := (T,R) -> (
  product (keys T, A -> 
    1 - product(numgens R, i -> (1 - ((gens R)_i - A_i))) 
  )
)

kernPhi = method()
kernPhi (RingElement, RingElement, Ring) := Ideal => (g, h, QR) -> (
  n := numgens QR;
  B := gens coefficientRing QR;
  C := gens coefficientRing coefficientRing QR;
  pp := sum( subsets gens QR, B, (x,b) -> (product x) * b);
  f := g + pp*h;
  W := apply( subsets gens QR, xx -> (
    m := (product xx);
    coefficient( m_QR, f) )
  );
  ideal lift( selectInSubring(1, gens gb ideal (W - C) ), 
       ambient coefficientRing coefficientRing QR)
)
    

beginDocumentation()

doc ///
Key
  getNcfLists
        (getNcfLists, HashTable, List, ZZ)
Headline
  Inferring nested canalyzing functions for given time-course data
Usage
	        P = getSingleNcfList(TimeCourseDataTable, Permutation, Characteristic)
Inputs
	        TimeCourseDataTable : HashTable with the time-course data
		Permutation : List with the wanted variable ordering
		Characteristic : ZZ 
Outputs
 P : List
	 of Lists of nested canalyzing functions fitting the data for each variable
Description
        Text
       	    For each variable, the complete list of all nested canalyzing 
	    functions interpolating the given data set on the given time course data. 
	    A function is in the output if it is nested canalyzing 
	    in the given variable order
--Example
  --T=new MutableHashTable;
 -- T#{1,1}=1;
 -- T#{1,0}=0;
 -- T#{0,1}=0;
 -- T#{0,0}=0;
 -- per = {0,1,2,3};
--  "jakob=2;"
--  "solutions = getSingleNcfList(T,per,jakob)"}
     
SeeAlso
///

doc ///
Key
  interpolate 
Headline
  construct polynomial that interpolates the data test
Usage
  interpolate HashTable
Consequences
Description
  Text
  Example 
    xxx;
    
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
  fieldChar=2;
  qring=ZZ/fieldChar
  inputMatrix=matrix {{1,1,1},{0,1,1},{0,0,1},{1,1,0},{1,0,1},{0,1,1}}
  inputMatrix=matrix {{0,0,0},{0,1,0},{1,1,0},{0,1,1},{1,1,1},{0,0,0}}
  inputMatrix=sub(inputMatrix,qring)
  Permutation={0,1,2,3,4,5,6,7}  
 resultListOfLists=  getNCFLists(inputMatrix,Permutation,fieldChar)  
  
     
     
///

TEST ///
installPackage "RationalPoints"
T=new MutableHashTable	   
T#{1,1}=1
T#{1,0}=0
T#{0,1}=0
T#{0,0}=0
per = {0,1,2,3}
jakob=2
solutions = getSingleNcfList(T,per,jakob)
genVars=gens ring solutions_0
referenceSolutions=genVars_0*genVars_1
assert(#solutions==1)
assert(solutions_0==referenceSolutions)
--assert( apply( solutions, I -> rationalPoints I) == {{{0, 0, 0, 1}}} )
 
///
TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
  n = 5
  L = subsets n
  L = apply( L, l -> apply( l, i -> i + 1) ) 
  C = ZZ/2[apply( L, l -> c_l)];
  QC = C /ideal apply(gens C, x -> x^2-x)
  B = QC[apply( L, l -> b_l)]
  QB = B / ideal apply(gens B, x -> x^2-x)
  R = QB[x_1..x_n];
  QR = R / ideal apply(gens R, x -> x^2-x);
  S = {1,2,4};
  p = ncfIdeal(S, QR, toList(0..#L-1)) 
  assert( p == c_{1,2,4} - c_{1,2,3,4}*c_{1,2,4,5} )
  ///

TEST ///
T=new MutableHashTable	   
T#{1,1}=1
T#{1,0}=0
T#{0,1}=0
T#{0,0}=0
n = #first keys T 
L = subsets n
L = apply( L, l -> apply( l, i -> i + 1) ) ;
C = ZZ/2[apply( L, l -> c_l)];
QC = C /ideal apply(gens C, x -> x^2-x)
B = QC[apply( L, l -> b_l), MonomialOrder => Eliminate 2^n]
QB = B / ideal apply(gens B, x -> x^2-x)
R = QB[x_1..x_n];
QR = R / ideal apply(gens R, x -> x^2-x)
g := interpolate(T,QR)
assert( g == x_1*x_2)
h := idealOfPoints(T,QR)
assert( h == 0 ) 
ncf := ideal flatten entries gens gb ideal(apply( L, t 
	  -> ncfIdeal( t, QR, toList(0..#L-1)))|{c_(toList(1..n))-1}
     )
ncf = lift(ncf, C)
installPackage "RationalPoints"
assert( rationalPoints ncf ==  {{0, 0, 0, 1}, {1, 0, 0, 1}, {0, 1, 0, 1}, {1,
1, 0, 1}, {0, 0, 1, 1}, {1, 0, 1, 1}, {0, 1, 1, 1}, {1, 1, 1, 1}} )
G := kernPhi(g,h,QR)
assert( G == lift(ideal(c_{1, 2}+1,c_{2},c_{1},c_{}), C) ) 
solutions := primaryDecomposition(G+ncf)
installPackage "RationalPoints"
--viewHelp RationalPoints
assert( apply( solutions, I -> rationalPoints I) == {{{0, 0, 0, 1}}} ) 
///

TEST ///
T=new MutableHashTable	   
T#{0,0,0} = 1
T#{0,1,0} = 1
T#{1,1,0} = 0
T#{0,1,1} = 1
T#{1,1,1} = 0
n = #first keys T 
L = subsets n
L = apply( L, l -> apply( l, i -> i + 1) ) ;
C = ZZ/2[apply( L, l -> c_l)];
QC = C /ideal apply(gens C, x -> x^2-x)
B = QC[apply( L, l -> b_l), MonomialOrder => Eliminate 2^n]
QB = B / ideal apply(gens B, x -> x^2-x)
R = QB[x_1..x_n];
QR = R / ideal apply(gens R, x -> x^2-x)
g := interpolate(T,QR)
assert( g == x_1*x_2*x_3+x_1*x_3+x_2*x_3+x_1+x_3+1)
h := idealOfPoints(T,QR)
assert( h == x_1*x_2*x_3+x_1*x_2+x_1*x_3+x_2*x_3+x_1+x_3 ) 
ncf := ideal flatten entries gens gb ideal(apply( L, t -> 
	  ncfIdeal( t, QR, toList(0..7)))|{c_(toList(1..n))-1}
     )
ncf = lift(ncf, C)
installPackage "RationalPoints"
G := kernPhi(g,h,QR)
assert( G == ideal apply(flatten entries gens ideal(c_{1, 3}+c_{1, 2,
3},c_{3}+c_{2, 3},c_{2},c_{1}+c_{1, 2}+1,c_{}+1), g -> lift(g,C)) )
solutions := primaryDecomposition(G+ncf)
installPackage "RationalPoints"
--viewHelp RationalPoints
s := apply( solutions, I -> rationalPoints I )
apply( s, ss -> sum ( subsets gens R, flatten ss, (x, c) -> c*(product x) ) )
netList oo
assert( apply( solutions, I -> rationalPoints I) == {{{1, 1, 0, 0, 0, 1, 0, 1}}, {{1, 0, 0, 1, 0, 1, 0, 1}}, {{1, 1, 0, 0, 1, 1, 1, 1}}} )
///

TEST ///
T=new MutableHashTable	   
T#{1,1}=1
n = #first keys T 
L = subsets n
L = apply( L, l -> apply( l, i -> i + 1) ) ;
C = ZZ/2[apply( L, l -> c_l)];
QC = C /ideal apply(gens C, x -> x^2-x)
B = QC[apply( L, l -> b_l), MonomialOrder => Eliminate 2^n]
QB = B / ideal apply(gens B, x -> x^2-x)
R = QB[x_1..x_n];
QR = R / ideal apply(gens R, x -> x^2-x)
g := interpolate(T,QR)
assert( g == x_1*x_2)
h := idealOfPoints(T,QR)
assert( h == x_1*x_2+1 ) 
ncf := ideal flatten entries gens gb ideal(apply( L, t -> 
	  ncfIdeal( t, QR, toList(0..3)))|{c_(toList(1..n))-1})
ncf = lift(ncf, C)
installPackage "RationalPoints"
G := kernPhi(g,h,QR)
assert( G == ideal apply(flatten entries gens ideal(c_{}+c_{1}+c_{2}+c_{1, 2}+1), g -> lift(g,C)) )
solutions := primaryDecomposition(G+ncf)
installPackage "RationalPoints"
--viewHelp RationalPoints
assert( apply( solutions, I -> rationalPoints I) == {{{0, 0, 0, 1}}, {{1, 1, 0, 1}}, {{1, 0, 1, 1}}, {{0, 1, 1, 1}}}) 
///


end

--

restart 
load "./Goettingen-2011/NCF.m2"
loadPackage "NCF"
check "NCF"
T=new MutableHashTable	   
T#{1,1}=1
T#{1,0}=0
T#{0,1}=0
T#{0,0}=0
T=new MutableHashTable	   
T#{1,1}=1
permutation = {0,2,1,3};
n = 2
L = subsets n
L = apply( L, l -> apply( l, i -> i + 1) ) ;
C = ZZ/2[apply( L, l -> c_l)];
QC = C /ideal apply(gens C, x -> x^2-x)
B = QC[apply( L, l -> b_l), MonomialOrder => Eliminate 2^n]
QB = B / ideal apply(gens B, x -> x^2-x)
R = QB[x_1..x_n];
QR = R / ideal apply(gens R, x -> x^2-x)
g := interpolate(T,QR)
h := idealOfPoints(T,QR)
ncf := ideal(apply( L, t -> 
	  ncfIdeal( t, QR, permutation))|{c_(toList(1..n))-1}
     )
ncf = lift(ncf, C)
G := kernPhi(g,h,QR)
solutions := primaryDecomposition(G+ncf)
installPackage "RationalPoints"
--viewHelp RationalPoints
apply( solutions, I -> rationalPoints I)
rationalPoints first solutions

list sigma 

ncfIdeal = method()
ncfIdeal (List, Ring, List) := RingElement => (S, QR, sigma) -> (
  n := numgens QR;
  -- c_{ l } = (gens QR)#indeces#l
  indeces := new MutableHashTable;
  L := subsets n;
  L = apply( L, l -> apply( l, i -> i + 1 ));
  apply( #L, i -> indeces#(L#i) = sigma#i );
  rS := max S;
  compl := toList (set( 1..rS)  -  set S);
  C := gens coefficientRing coefficientRing QR;
  C#(indeces#S) - C#(indeces#(toList (1..rS))) *
    product( compl, i -> 
      C#( indeces#(toList (set (1..n) - set {sigam#i} ) ))
    )
)


restart 
--load "./Goettingen-2011/NCF.m2"
loadPackage ("NCF", FileName => "./Goettingen-2011/NCF.m2" ) 
installPackage ("NCF", FileName => "./Goettingen-2011/NCF.m2" )
check "NCF"


restart 
--load "./Goettingen-2011/NCF.m2"
loadPackage "NCF"
installPackage "NCF"
check "NCF"