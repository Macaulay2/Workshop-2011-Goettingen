
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
  coeff := apply( subsets gens QR, xx -> (
    m := (product xx);
    coefficient( m_QR, f) )
  );
  coeff - C
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
kernP := kernPhi(g,h,QR)
selectInSubring (1, gens gb ideal kernP)





primaryDecomposition(ideal(kernP)+ncf)


f = b_{} + b_{1}*x_1 + b_{2}*x_2 + (b_{} + b_{1}+b_{2}+b_{1,2})*x_1*x_2
m = x_1*x_2
coefficient(m,f)
