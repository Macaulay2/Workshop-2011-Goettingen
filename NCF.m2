newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "Inferring nested canalyzing functions for given time-course
    data",
    DebuggingMode => true
)

needsPackage "RationalPoints";


export{interpolate, idealOfPoints, ncfIdeal, kernPhi, getSingleNcfList,
getNcfLists, convertDotFileToHashTable, extractTimecourse}


-- given a matrix with time course data for the variables in L
-- extract only those time points of variables in inputs
-- deal with inconsistenties
-- T has the form T#{0,1,0,} = 1
-- make table for x, depending on W#x
extractTimecourse = method()
extractTimecourse (Matrix, List, String, HashTable) := HashTable => ( D, L, x, W) -> (
  inputs := W#x;
  xPos := position(L, l -> l==x);
  T := new MutableHashTable;
  inconsistentTransitions := {};
  pos := positions( L, l -> member(l, inputs) );
  scan( drop(entries D, -1), drop(entries D, 1), (inputRow, outputRow) -> (
    if not member( inputRow_pos, inconsistentTransitions) then (
      if T#?(inputRow_pos) then (
        if T#(inputRow_pos) != outputRow_xPos then (
          remove(T, inputRow_pos);
          inconsistentTransitions = inconsistentTransitions | {inputRow_pos};
          print "Inconsistent data found, ignoring it"
        )
      )  
      else
        T#(inputRow_pos) = outputRow_xPos
      )
    )
  );
  T
)


--returns a List of Nested Canalyzing Functions for the given HashTable of one variable
--MHT is the table with the expermental data, 
--permutation is a list with the wanted permutation,
--and fieldChar is the Characteristic
-- gens: a list of names of generators
getSingleNcfList = method()
getSingleNcfList (HashTable, List, ZZ, List) := List => (MHT, Permutation, fieldChar, gens) -> (
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
     h := idealOfPoints(MHT,QR);
     -- g+<h> F2[x1,x2, ..., xn]
     ncf := ideal flatten entries gens gb ideal(apply( L, t -> 
	       ncfIdeal( t, QR, Permutation))|{(gens C)#(numgens C-1)-1}
     ); --F2[c0, c1, ..., c[n] ]
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

--main routine, the user interfaces with this routine
-- L list of variable names
-- W wiring diagram 
-- D time course data
mainNCF = method()
mainNCF (List, HashTable, Matrix) := List => (L, W, D) -> (
  apply(L, x -> (
    partialData := extractTimecourse( D, L, x, W);
    n := getSingleNcfList( partialData, {}, 2, W#x);
    print ("The functions for " | x | " are " | toString n)
    )
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
 

-- given the filename of a .dot file, return the hash table T
-- T#(xi) = all xjs that influcence xi 
convertDotFileToHashTable = method()
convertDotFileToHashTable String := HashTable => filename -> (  
  content := lines get filename;
  numLines := #content;
  content = apply( numLines-2, i -> content_(i+1) );
  nameLines := select( content, l -> match( "label", l) );
  variableNames := new MutableHashTable;
  scan( nameLines, l -> if match( ///^(.+)\s.*"(.+)",///, l ) then (
    node := substring( lastMatch_1, l);
    name := substring( lastMatch_2, l);
    variableNames#node = name;
    )
  );
  dependencies := new MutableHashTable;
  dependencyLines := select( content, l -> match( "->", l) );
  scan(dependencyLines, l -> (
    match( ///^(.*)\s->\s(.*);///, l );
    source := substring( lastMatch_1, l);
    target := substring( lastMatch_2, l);
    if dependencies#?target then 
      dependencies#target = dependencies#target | {source}
    else 
      dependencies#target = {source};
    )
  );
  variableNames;
  dependencies;
  dep := new MutableHashTable;
  dependencies = new HashTable from dependencies;
  scanPairs (dependencies, (target, sourceList) -> (
    dep#(variableNames#target) = apply( sourceList, s -> variableNames#s)
    )
  );
  dep
)


beginDocumentation()

doc ///
Key
  getSingleNcfList
  (getSingleNcfList, HashTable, List, ZZ, List)
Headline
  Inferring nested canalyzing functions for given time-course data for a single variable
Usage
	        P = getSingleNcfList(TimeCourseDataTable, Permutation, Characteristic, generators)
Inputs
	TimeCourseDataTable : HashTable
	  with the time-course data for a single variable as a function of all variables . 
	  The keys of the TimeCourseDataTable shoult be the variable values at time t 
	  and the assigned entries are the values of the variable of interest at time (t+1)
	Permutation : List
	  with the wanted variable ordering
	Characteristic : ZZ 
Outputs
 P : List
    of nested canalyzing functions fitting the data for one variable which values are given with the input parameter "TimeCourseDataTable"
Description
  Text
	    For one variable, the complete list of all nested canalyzing 
	    functions interpolating the given data set on the given time course data. 
	    A function is in the output if it is nested canalyzing 
	    in the given variable order
  Example
    T=new MutableHashTable;
    T#{1,1}=1;
    T#{1,0}=0;
    T#{0,1}=0;
    T#{0,0}=0;
    permutation = {0,1,2,3};
    fieldChar=2;
    solutions = getSingleNcfList(T,permutation,fieldChar)
SeeAlso
///

doc ///
Key
  getNcfLists
  (getNcfLists, Matrix, List, ZZ)
Headline
  Inferring nested canalyzing functions for given time-course data
Usage
	        P = getNcfList(TimeCourseDataTable, Permutation, Characteristic)
Inputs
	TimeCourseDataTable : Matrix
	  with the time-course data
	    
	Permutation : List
	  with the wanted variable ordering
	Characteristic : ZZ 
	  characteristic of the field. Each entry of the TimeCourseDataTable is converted to an element of the field
Outputs
 P : List
	 of Lists of nested canalyzing functions fitting the data for each variable,
	 "P"_i is a list with the CNFs of the ith variable matching the input data for the given ordering (Permutation)
Description
  Text
	    For each variable, the complete list of all nested canalyzing 
	    functions interpolating the given data set on the given time course data. 
	    A function is in the output if it is nested canalyzing 
	    in the given variable order
  Example
    inputMatrix = matrix { {1,1},  {1,0},  {0,1}, {0,0} ,{0,0} };
    permutation = {0,1,2,3};
    fieldChar=2;
    field=ZZ/fieldChar;
    inputMatrix=sub(inputMatrix,field)
    solutions = getNcfLists(inputMatrix,permutation,fieldChar)
    
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
///

TEST ///
  fieldChar=2;
  qring=ZZ/fieldChar
  --inputMatrix=matrix {{1,1,1},{0,1,1},{0,0,1},{1,1,0},{1,0,1},{0,1,1}}
  inputMatrix=matrix {{0,0,0},{0,1,0},{1,1,0},{0,1,1},{1,1,1},{0,0,0}}
  inputMatrix=sub(inputMatrix,qring)
  Permutation={0,1,2,3,4,5,6,7}  
 resultListOfLists=  getNcfLists(inputMatrix,Permutation,fieldChar)  
  
     
     
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
loadPackage "NCF"
convertDotFileToHashTable "wiring.out1.dot"
D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}}
D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}, {0, 0,0,0}}
D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}, {1,0,0,0}}
L = { "GeneA", "GeneB", "ProteinC", "GeneD"}
W = new HashTable from { "GeneA" => {"GeneA", "ProteinC"} }
extractTimecourse( D, L, "GeneA", W)
