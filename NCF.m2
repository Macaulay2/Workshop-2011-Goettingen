
newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "Inferring nested canalyzing functions for given time-course
    data",
    DebuggingMode => true
)

export{interpolate, idealOfPoints, ncfIdeal, kernPhi}

-- construct the generators for the ideal that encodes the relation of
--coefficients for ncf
-- ideal with relation of coefficients for nested canalyzing functions
-- equation 3.8 in Jarrah et al
-- given a subset S \subseteq [n], return the relation of that generator
ncfIdeal = method()
ncfIdeal (List, Ring) := RingElement => (S, QR) -> (
  n := numgens QR;
  -- c_{ l } = (gens QR)#indeces#l
  indeces := new MutableHashTable;
  L := subsets n;
  L = apply( L, l -> apply( l, i -> i + 1 ));
  apply( #L, i -> indeces#(L#i) = i );
  rS := max S;
  compl := toList (set( 1..rS)  -  set S);
  C := gens coefficientRing coefficientRing QR;
  C#(indeces#S) - C#(indeces#(toList (1..rS))) *
    product( compl, i -> 
      C#( indeces#(toList (set (1..n) - set {i} ) ))
    )
)

  
-- generate a function that interpolates a given time course
-- T is a Hash table, with T#Input(t)=Output(t+1)
interpolate = method() 
interpolate (HashTable, Ring) := (T, R) -> (
  sum (keys T, A -> T#A * product(numgens R, i -> ( 1- ( (gens R)_i - A_i) )))
) 


-- construct generator for the ideal that vanishes on all given time points
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
  ideal lift( selectInSubring(1, gens gb ideal (W - C) ), ambient coefficientRing coefficientRing QR)
)




beginDocumentation()

doc ///
Key
  NCF
Headline
  Inferring nested canalyzing functions for given time-course data
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
  interpolate 
Headline
  construct polynomial that interpolates the data
Usage
  interpolate HashTable
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
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
  p = ncfIdeal(S, QR) 
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
ncf := ideal flatten entries gens gb ideal(apply( L, t -> ncfIdeal( t, QR))|{c_(toList(1..n))-1})
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
ncf := ideal flatten entries gens gb ideal(apply( L, t -> ncfIdeal( t, QR))|{c_(toList(1..n))-1})
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
ncf := ideal flatten entries gens gb ideal(apply( L, t -> ncfIdeal( t, QR))|{c_(toList(1..n))-1})
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
loadPackage "NCF"
check "NCF"
T=new MutableHashTable	   
T#{1,1}=1
T#{1,0}=0
T#{0,1}=0
T#{0,0}=0
T=new MutableHashTable	   
T#{1,1}=1
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
ncf := ideal(apply( L, t -> ncfIdeal( t, QR))|{c_(toList(1..n))-1})
ncf = lift(ncf, C)
G := kernPhi(g,h,QR)
solutions := primaryDecomposition(G+ncf)
installPackage "RationalPoints"
--viewHelp RationalPoints
apply( solutions, I -> rationalPoints I)
rationalPoints first solutions



R = QQ[a,b,c,d,e]
QR = R / ideal product gens R

I = ideal( a*b*(a*b-c), d*(d-e) )
J = ideal( c*(a*b-c), e*(d-e) )
decompose( I + ideal product gens R) 
traps = decompose( J + ideal product gens R) 
traps#0 + traps#1
decompose( oo + ideal product gens R)

apply( apply( subsets traps, tt -> if tt == {} then ideal 0 else ideal gens gb sum tt), union -> decompose(union + ideal product gens R) )
netList oo




