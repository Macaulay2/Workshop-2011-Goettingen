
newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "",
    DebuggingMode => true
    )

export{g, IdealofPoints, ncfIdeal}
 -- Actual code here!


-- ideal with relation of coefficients for nested canalyzing functions
-- 3.8
-- given a subset S \subseteq [n], return the relation of that generator
ncfIdeal = method()
ncfIdeal (List, ZZ, Ring) := RingElement => (S, n, QR) -> (
  -- c_{ l } = (gens QR)#indeces#l
  indeces := new MutableHashTable;
  L := subsets n;
  L = apply( L, l -> apply( l, i -> i + 1 ));
  apply( #L, i -> indeces#(L#i) = i+n );
  rS := max S;
  compl := toList (set( 1..rS)  -  set S);
  (gens QR)#(indeces#S) - (gens QR)#(indeces#(toList (1..rS))) *
    product( compl, i -> 
      (gens QR)#( indeces#(toList (set (1..n) - set {i} ) ))
    )
)

  

g=method() 
g (HashTable, Ring) := (T,R)->
 (--T is a HashTable
    sum (keys T, A->T#A*product(numgens R,i->(1-((gens R)_i-A_i))))
    ) 

IdealofPoints=method()
IdealofPoints (HashTable, Ring) := (T,R) -> 
     (-- T is a HashTable
	  ideal(
	  product (keys T, A->1-product(numgens R,i->(1-((gens R)_i-A_i))))
	  )
     )

beginDocumentation()

  doc
  ///
  Key
  NCF
  Headline
  Description
  Text
  Example
  Caveat
  SeeAlso
  ///

  doc
  ///
  Key
  Headline
  Usage
  Inputs
  Outputs
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
  R = ZZ/2[x_1..x_n, apply( L, l -> c_l), apply( L, l -> b_l) ]
  QR = R / ideal apply(gens R, x -> x^2-x)
  S = {1,2,4};
  p = ncfIdeal(S,n,QR) 
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

R=ZZ/2[x1,x2]/ideal(x1^2-x1,x2^2-x2)


restart 
loadPackage "NCF"
n = 5
L = subsets n
L = apply( L, l -> apply( l, i -> i + 1) ) 
R = ZZ/2[x_1..x_n, apply( L, l -> c_l), apply( L, l -> b_l) ]
QR = R / ideal apply(gens R, x -> x^2-x)
ideal apply(L, S-> ncfIdeal(S,n,QR) )
variableCount=n
 nlist=apply(variableCount,i->i+1)
 mons = apply(subsets nlist,i->product apply(i,j->x_j))
  B=ZZ/2[apply(subsets nlist,i->b_i)]
  alternativeR=ZZ/2[x_1..x_n]
  altQR= alternativeR/ideal(apply(gens alternativeR, x-> x^2-x))
 BQR=B**altQR
