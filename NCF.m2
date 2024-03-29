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


export{getWiring, mainNCF, interpolate, idealOfPoints, ncfIdeal, kernPhi, getSingleNcfList, convertDotStringToHashTable, convertDotFileToHashTable, extractTimecourse}


-- given a matrix with time course data for the variables in L
-- extract only those time points of variables in inputs
-- deal with inconsistencies
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


-- Returns a List of Nested Canalyzing Functions for the given HashTable of one variable
-- T is the table with the experimental data, 
-- sigma is a list with the wanted permutation,
-- p is the Characteristic
-- gensR: a list of names of generators
getSingleNcfList = method()
getSingleNcfList (HashTable, List, ZZ, List) := List => (T, sigma, p, gensR) -> (
     if (#T > 0) then (     -- we have some time course data
       n := #first keys T; -- Get number of variables
       assert(n == #gensR)
     ) else 
       n = #gensR;

     R := ZZ/p[gensR];
     QR := R/ideal apply(gens R, x -> x^p - x);
     g := (interpolate(T, QR))_QR;      -- in case it is constant it must be in QR and not ZZ
     h := (idealOfPoints(T, QR))_QR;

     C := ZZ/p[ vars(0..2^n-1) ];
     QC := C / ideal apply(gens C, x -> x^p - x);
     ncf := ideal apply( gens C, x -> ncfIdeal( x, QC, sigma) );
     ncf = ncf + ideal ( last gens C -1 );  -- c_[n] = 1
     ncf = lift(ncf, C);

     R = QC[ gensR ];
     QR = R / ideal apply(gens R, x -> x^p - x);


     G := kernPhi(g,h,QC);
     solutions := primaryDecomposition(G+ncf);
     s := apply( solutions, I -> rationalPoints I );
     apply( s, ss -> sum ( subsets gens R, flatten ss, (x, c) -> c*(product x) ) )   
)

-- Construct the generators for the ideal that encodes the relation of
-- coefficients for n-- ideal with relation of coefficients for nested canalyzing functions
-- equation 3.8 in Jarrah et al
-- given a subset S \subseteq [n], return the relation of that generator
ncfIdeal = method()
ncfIdeal (RingElement, Ring, List) := RingElement => (c, QC, sigma) -> (
  n := lift(log( char QC, numgens QC),ZZ);
  S := subsets n;
  T := new MutableHashTable;
  scan( subsets n, gens QC, (S,c) -> T#S = c );
  i := position( gens QC, x -> x == c );
  rS := max ( S_i );
  rSset := set (0..rS);
  complement := toList( rSset - set S_i );
  c - T#(toList rSset) * 
    product( complement, i -> (
      T#(toList(set last S - set {i} ) )
      )
    )
)

-- Main routine, the user interfaces with this routine
-- L list of variable names
-- W wiring diagram 
-- D time course data
mainNCF = method()
mainNCF (List, HashTable, Matrix) := List => (L, W, D) -> (
  apply(L, x -> (
    partialData := extractTimecourse( D, L, x, W);
    n := getSingleNcfList( partialData, {}, 2, W#x);
    print ("The functions for " | x | " are " | toString n);
    n
    )
  )
)

  
-- Generate a function that interpolates a given time course
-- T is a Hash table, with T#Input(t)=Output(t+1)
interpolate = method() 
interpolate (HashTable, Ring) := (T, R) -> (
  sum (keys T, A -> T#A * product(numgens R, i -> ( 1- ( (gens R)_i - A_i) )))
) 

-- Construct generator for the ideal that vanishes on all given time points
-- Only access the keys of the hashtable T, with T#Input(t)=Output(t+1)
idealOfPoints = method()
idealOfPoints(HashTable, Ring) := (T,R) -> (
  product (keys T, A -> 
    1 - product(numgens R, i -> (1 - ((gens R)_i - A_i))) 
  )
)

kernPhi = method()
kernPhi (RingElement, RingElement, Ring) := Ideal => (g, h, QC) -> (
  p := char QC;
  n := numgens ring g; 
  B := QC[ vars(0..2^n-1) ];
  QB := B / ideal apply(gens B, x -> x^p - x);
  R := QB[gens ring g];
  QR := R / ideal apply(gens R, x -> x^p - x);
  pp := sum( subsets gens QR, gens B, (x,b) -> (product x) * b);
  f := sub(g,QR) + pp*sub(h,QR);
  W := apply( subsets gens QR, xx -> (
    m := (product xx);
    coefficient( m_QR, f) 
    )
  );
  ideal lift( selectInSubring(1, gens gb ideal (W - gens QC) ), ambient QC)
)
 

-- Given the filename of a .dot file, return the hash table T
-- T#(xi) = all xjs that influcence xi 
convertDotFileToHashTable = method()
convertDotFileToHashTable String := HashTable => filename -> (  
  content := get filename;
  convertDotStringToHashTable( content )
)

convertDotStringToHashTable = method()
convertDotStringToHashTable String := HashTable => content -> (
  content = lines content;
  numLines := #content;
  print numLines;
  print content;
  content = apply( numLines-2, i -> content_(i+1) );
  nameLines := select( content, l -> match( "label", l) );
  variableNames := new MutableHashTable;
  scan( nameLines, l -> if match( ///^\s*(.+)\s.*"(.+)",///, l ) then (
    node := substring( lastMatch_1, l);
    name := substring( lastMatch_2, l);
    variableNames#node = name;
    )
  );
  dependencies := new MutableHashTable;
  dependencyLines := select( content, l -> match( "->", l) );
  scan(dependencyLines, l -> (
    match( ///^\s*(.*)\s->\s(.*);///, l );
    source := substring( lastMatch_1, l);
    target := substring( lastMatch_2, l);
    if dependencies#?target then 
      dependencies#target = dependencies#target | {source}
    else 
      dependencies#target = {source};
    )
  );
  dep := new MutableHashTable;
  dependencies = new HashTable from dependencies;
  scanPairs (dependencies, (target, sourceList) -> (
    dep#(variableNames#target) = apply( sourceList, s -> variableNames#s)
    )
  );
  dep
)


-- takes variable List 'variableNames' and dependency matrix 'adjDataMatrix':
-- If  variableNames#j depends on variableNames#i then adjDataMatrix_i_j is equals to one, otherwise to zero
-- returns a HashTable with the variable names X_i as keys; the corresponding entry is a list of variables X_i depends on.
getWiring = method()
getWiring(List, Matrix) := HashTable => (variableNames, adjDataMatrix) -> (
  dependencies := new MutableHashTable;
  assert(#variableNames==numgens source adjDataMatrix);
  assert(#variableNames==numgens target adjDataMatrix);
  apply(#variableNames, colindex -> (
    deplist := {}; 
    apply (#variableNames, rowindex -> (
      if (adjDataMatrix_rowindex_colindex == 1_ZZ) then
        deplist = deplist|{variableNames_rowindex}
      ));
      dependencies#[variableNames_colindex]=deplist;
    )
    );
  dependencies
)

beginDocumentation()

doc ///
Key
  getWiring
  (getWiring, List, Matrix)
Headline
  computes a HashTable with variable dependencies for given variable list and a given dependency matrix
Usage
 dependencyTable =  getWiring( variableList, dependencyMatrix );
Inputs
  variableList: List
   a list of variable names
  dependencyMatrix: Matrix
   If  variableNames#j depends on variableNames#i then dependencyMatrix_i_j is equals to one, otherwise to zero	
Outputs
  DHT: HashTable 
   with the variable names X_i as keys; the corresponding entry is a list of variables X_i depends on.
Description
  Text
   computes a HashTable with variable dependencies for given variable list and a given dependency matrix
  Example
   varList = { "Elephant", "cat" , "mouse" } ;
   dependencyMatrix = matrix { {0,1,0}, {0,0,0}, {0,0,1} }; 
   dependencyTable  = getWiring( varList, dependencyMatrix )
///

doc ///
Key
  getSingleNcfList
  (getSingleNcfList, HashTable, List, ZZ, List)
Headline
  Inferring nested canalyzing functions for given time-course data for a single variable
Usage
  P = getSingleNcfList(TimeCourseDataTable, Permutation, Characteristic, ringGenerators)
Inputs
  TimeCourseDataTable : HashTable
   with the time-course data for a single variable as a function of all variables . 
   The keys of the TimeCourseDataTable shoult be the variable values at time t 
   and the assigned entries are the values of the variable of interest at time (t+1)
  Permutation : List
    with the wanted variable ordering
  Characteristic : ZZ 
  ringGenerators : List
Outputs
 P : List
  of nested canalyzing functions fitting the data for one variable which values are given with the input parameter "TimeCourseDataTable"
Description
  Text
   For one variable, the complete list of all nested canalyzing 
   functions interpolating the given data set on the given time course data. 
   A function is in the output if it is nested canalyzing 
   in the given variable order (permutation)
  Example
    T = new MutableHashTable;
    T#{1,1}=1;
    T#{1,0}=0;
    T#{0,1}=0;
    T#{0,0}=0;
    permutation = {0,1,2,3};
    fieldChar=2;
    mons := monoid [x_1,x_4];
    Field:=ZZ/fieldChar;
    Rng=Field(mons);
    gensR=gens Rng;
    solutions = getSingleNcfList(T,permutation,fieldChar,gensR)
///


doc ///
Key
  mainNCF
Headline
  Inferring nested canalyzing functions for given time-course data
Usage
  ncfList = mainNCF(varibleNames, wiringDiagram, timeCourseDataMatrix, sigma) 
Inputs
  variableNames : List
    strings with the names of all variables
  wiringDiagram : HashTable
    discribing the dependencies of all the variables  
  timeCourseDataMatrix : Matrix
    with the time-course data	    
  sigma : List
    with the wanted variable ordering
Outputs
   ncfList : List
    of Lists of nested canalyzing functions fitting the data for each variable,
    "ncfList"_i is a list with the CNFs of the ith variable matching the input data for the given ordering (Permutation)

Consequences
Description
  Text
  Example 
    xxx;
  Code
  Pre
///

TEST ///
  T=new MutableHashTable	   
  T#{1,1}=1
  T#{1,0}=0
  T#{0,1}=0
  T#{0,0}=0
  assert( toString getSingleNcfList( T, {}, 2, {"GeneA", "GeneB"}) == "{GeneA*GeneB}" )
///

TEST ///
  T=new MutableHashTable	   
  T#{1,1}=1
  T#{1,0}=0
  T#{0,1}=0
  T#{0,0}=0
  per = {0,1,2,3}
  --assert( apply( solutions, I -> rationalPoints I) == {{{0, 0, 0, 1}}} )
///

TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
  nnn = 5
  C = ZZ/2[ vars(0..2^nnn-1) ] 
  QC = C /ideal apply(gens C, x -> x^2-x)
  S = {1,2,4};
  QC_22
  p = ncfIdeal(QC_22, QC, {} ) 
  -- w = F* (E*x) 
  assert( p == value "x*E*F + w" )
///

TEST ///
  T=new MutableHashTable	   
  T#{1,1}=1
  T#{1,0}=0
  T#{0,1}=0
  T#{0,0}=0
  n = #first keys T 
  --assert( rationalPoints ncf ==  {{0, 0, 0, 1}, {1, 0, 0, 1}, {0, 1, 0, 1}, {1, 1, 0, 1}, {0, 0, 1, 1}, {1, 0, 1, 1}, {0, 1, 1, 1}, {1, 1, 1, 1}} )
  --assert( G == lift(ideal(c_{1, 2}+1,c_{2},c_{1},c_{}), C) ) 
  --viewHelp RationalPoints
  --assert( apply( solutions, I -> rationalPoints I) == {{{0, 0, 0, 1}}} ) 
///

TEST ///
  M = matrix {{0,0,0}, {0,1,0}, {1,1,0}, {0,1,1}, {1,1,1}}
  T=new MutableHashTable	   
  T#{0,0,0} = 1
  T#{0,1,0} = 1
  T#{1,1,0} = 0
  T#{0,1,1} = 1
  T#{1,1,1} = 0
  L = {"GeneA", "GeneB", "ProteinA"};
  W = new MutableHashTable;
  W#"GeneA" = {"GeneA", "GeneB", "ProteinA"};
  W#"GeneB" = {"GeneA", "GeneB", "ProteinA"};
  W#"ProteinA" = {"GeneA", "GeneB", "ProteinA"};
  mainNCF( L, W, M) 

  n = #first keys T 
  --assert( g == x_1*x_2*x_3+x_1*x_3+x_2*x_3+x_1+x_3+1)
  --assert( h == x_1*x_2*x_3+x_1*x_2+x_1*x_3+x_2*x_3+x_1+x_3 ) 
  --assert( G == ideal apply(flatten entries gens ideal(c_{1, 3}+c_{1, 2, 3},c_{3}+c_{2, 3},c_{2},c_{1}+c_{1, 2}+1,c_{}+1), g -> lift(g,C)) )
  --assert( apply( solutions, I -> rationalPoints I) == {{{1, 1, 0, 0, 0, 1, 0, 1}}, {{1, 0, 0, 1, 0, 1, 0, 1}}, {{1, 1, 0, 0, 1, 1, 1, 1}}} )
///

TEST ///
  T=new MutableHashTable	   
  T#{1,1}=1
  n = #first keys T 
  assert( toString getSingleNcfList(T, {}, 2, {"var1", "var2"}) == "{var1*var2, var1*var2+var1+1, var1*var2+var2+1, var1*var2+var1+var2}" )
///

TEST ///
  --W = convertDotFileToHashTable "wiring.out1.dot"
  W = convertDotStringToHashTable "digraph test {
node1 [label=\"x1\", shape=\"box\"];
node2 [label=\"x2\", shape=\"box\"];
node1 -> node1;
node2 -> node1;
node1 -> node2;
}"
  D = matrix { {0,0}, {0,1}, {0,1} }
  L = {"x1", "x2" }
  --extractTimecourse( D, L, "x1", W)
  --extractTimecourse( D, L, "x2", W)
  s := mainNCF( L, W, D);
  assert( toString s == "{{x1*x2, x1*x2+x1}, {x1+1}}")
///

TEST ///
  T = new HashTable
  assert( toString getSingleNcfList(T, {}, 2, {"oneVariable"}) == "{oneVariable, oneVariable+1}")
///

TEST ///
  T = new HashTable
  assert( toString getSingleNcfList(T, {}, 2, {"firstVariable", "secondVariable"}) == "{firstVariable*secondVariable, firstVariable*secondVariable+1, firstVariable*secondVariable+firstVariable, firstVariable*secondVariable+firstVariable+1, firstVariable*secondVariable+secondVariable, firstVariable*secondVariable+secondVariable+1, firstVariable*secondVariable+firstVariable+secondVariable, firstVariable*secondVariable+firstVariable+secondVariable+1}")
///

TEST ///
  --W = convertDotFileToHashTable "wiring.out1.dot"
  W = convertDotStringToHashTable "digraph test {
  node1 [label=\"x1\", shape=\"box\"];
  node2 [label=\"x2\", shape=\"box\"];
  node1 -> node1;
  node2 -> node1;
  node1 -> node2;
  }"
  L = {"x1", "x2" }
  D = matrix { {0,0}, {0,1}, {0,1} }
  s := mainNCF( L, W, D);
  assert( toString s == "{{x1*x2, x1*x2+x1}, {x1+1}}")
///

end

--

restart 
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


variableNames={"Jakob","Erti", "Franzi"}
adjDataMatrix = matrix {{0,1,0},{1,1,1},{1,0,0}}

restart 
--load "./Goettingen-2011/NCF.m2"
loadPackage ("NCF", FileName => "./Goettingen-2011/NCF.m2" ) 
installPackage ("NCF", FileName => "./Goettingen-2011/NCF.m2" )
check "NCF"


restart 
loadPackage "NCF"
W = convertDotFileToHashTable "wiring.out1.dot"
--W = convertDotFileToHashTable "trastuzumab.dot"
D = matrix { {0,0}, {0,1}, {0,1} }
L = {"x1", "x2" }
--L = apply( 19, i -> ( "x" | toString (i+1) ) )
--D = matrix {{}}
--T = new HashTable
--extractTimecourse( D, L, "x1", W)
--extractTimecourse( D, L, "x2", W)
mainNCF( L, W, D)


D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}}
D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}, {0, 0,0,0}}
D = matrix { {0,0,1,0}, {1,0,1,0}, {0,1,1,1}, {1,0,0,1}, {1,0,1,0}, {1,0,0,0}}
L = { "GeneA", "GeneB", "ProteinC", "GeneD"}
W = new HashTable from { "GeneA" => {"GeneA", "ProteinC"} }
extractTimecourse( D, L, "GeneA", W)

restart 
loadPackage "NCF"
check "NCF"
