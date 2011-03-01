newPackage(
	"MonomialAlgebras",
    	Version => "0.1", 
    	Date => "Feb 27, 2011",
    	Authors => {
                  },
    	Headline => "Monomial algebras",
	CacheExampleOutput => false,
	AuxiliaryFiles => false,
    	DebuggingMode => true
        )

-- For information see documentation key "MonomialAlgebras" below.

export({decomposeMonomialCurve,
	  decomposeMonomialAlgebra,
	  decomposeSimplicialHomogeneousMonomialAlgebra,
	  homogenizeSemigroup,
	  adjoinPurePowers,
	  monomialAlgebraIdeal})


decomposeMonomialCurve=method()
decomposeMonomialCurve(List):= A -> (
   kk:=QQ;
   x:=symbol x;
   s:=symbol s;
   t:=symbol t;
   if not gcd A ==1 then print "WARNING: exponents not relatively prime";
   n := #A;
   d := max A;
   deglist := prepend({0,d}, for i from 0 to n-1 list {A_i, d-A_i});
   S := kk[x_0..x_n, Degrees =>deglist];
   P := kk[s,t, Degrees =>{{1,0}, {0,1}}];
   maplist := deglist/(D->s^(D_1)*t^(D_0));
   I := ker map(P,S,maplist);
   N := S^1/(ideal(x_0,x_n)+I);
   bN := basis N;
   L := partition(p -> (first p)%d, last degrees bN);
   --replace each value by itself normalized then divided by d, 
   --with a twist to show the amount of normalization.
   L1 := applyValues(L,LL -> (
	  min1 := min(LL/first);
	  min2 := min(LL/last);
	  LL1 := {LL/(p->{(first p - min1)//d, (last p - min2)//d}),  (min1+min2)//d}
     ));
   a:=local a;
   b:=local b;
   T := kk[a,b];
   --Now make ideals in T by grouping the degrees in genDegs by congruence class.
  applyValues(L1, LL->( 
     (ideal apply(first LL, m->T_0^(first m)*T_1^(last m)))*(T^{-last LL}))
	  )
)

decomposeMonomialAlgebra=method()
decomposeMonomialAlgebra(RingMap):= f -> (
S:=target f;
P:=source f;
p := numgens P;
n := numgens S;
B := degrees S;
C:=degrees P;
c := sum C;
m := #B_0;
I := monomialAlgebraIdeal S;
N := S^1/(f(ideal vars P)+I);
bN := last degrees basis N;
C1 := gens gb transpose matrix C;
L := partition(j->(transpose matrix {j})%C1,bN);
L1 := applyPairs(L,(k,v) -> (k,apply(v, v1->
	       (entries transpose((transpose matrix{v1})-k))#0)));
applyPairs (L1, (k,V)->(  
     vm := transpose matrix V;
     Cm := transpose matrix C;
     coef := vm//Cm;
     mins := transpose matrix {for i from 0 to numrows coef -1 list 
            min (entries coef^{i})#0};
     Mins := mins * matrix{{numcols vm:1}};
     coef1 := coef-Mins;
     (k,{ideal(apply(numcols coef1, 
		  v->product(apply(p, j->P_j^(coef1_v_j))))), k+Cm*mins})
           ))
)


decomposeSimplicialHomogeneousMonomialAlgebra=method()
decomposeSimplicialHomogeneousMonomialAlgebra(List):= A -> (
--A should be a list of elements of NN^(m-1), all of total degree <=d, (thought of
--as homogeneous elements of degree d in NN^m.
B := adjoinPurePowers homogenizeSemigroup A;
d := sum B_0;
m := #B_0;
n := #B;
   kk:=QQ;
   x:=symbol x;
   s:=symbol s;
   t:=symbol t;
S := kk[x_0..x_(n-1), Degrees => B];
C :=  apply(m, i-> apply(m, j -> if(j == i) then d else 0));  -- pure powers
P := kk[s_0..s_(m-1), Degrees => C];
I := monomialAlgebraIdeal S;
N := S^1/(ideal(x_0..x_(m-1))+I);
bN := basis N;
L := partition(p -> p/(i -> i%d), last degrees bN);
--print L;
--replace each value by itself normalized then divided by d, 
--with a twist to show the amount of normalization.
L1 := applyValues(L,LL -> (
	  degLL0 := (sum LL_0)//d;
--	  degLL = (min(LL/sum))//d;
	  LL1 := LL / (l -> (apply(l - LL_0,j->j//d)));
	  mins := apply(#LL_0, i -> min apply(LL1, l -> l#i));
	  {LL1 / (l -> l-mins), degLL0 + sum(mins)}
     ));
a := local a;
T := kk[a_0..a_(m-1)];
--Now make ideals in T by grouping the degrees in genDegs by congruence class.
applyValues(L1, LL->( 
	  LLf := first LL;
     (ideal apply(LLf, mm->product(apply(#mm, i-> T_i^(mm_i)))))*(T^{-last LL}))
	  )
)
homogenizeSemigroup=method()
homogenizeSemigroup(List):= A ->(
     d := max (A/sum);
     A/(a->append(a, d-sum a))
     )

adjoinPurePowers=method()
adjoinPurePowers(List) := B -> (
     d :=  sum B_0;
     m := #(B_0);
     unique(apply(m, i-> apply(m, j -> if(j == i) then d else 0)) | B)
     )

monomialAlgebraIdeal=method()
monomialAlgebraIdeal(PolynomialRing) := (R) -> (
     --R should be a multigraded poly ring
     --forms the ideal in R corresponding to the degree monoid algebra
     --generated by monomials x^(B_i), where B is the list of degrees of
     --the variables of R
     B:=degrees R;
     m := #B_0;
     t := local t;
     k:= coefficientRing R;
     T := k[t_0..t_(m-1)];
     targ :=  apply(B, b -> product(apply (#b, i-> t_i^(b_i))));
     ker map(T,R,targ)
     )



------------------------------------------------------------------------------------------



beginDocumentation()

doc ///
  Key
    MonomialAlgebras
  Headline
    Decompose a monomial algebra as a module over a subalgebra.
  Description
    Text
      {\bf Overview:}
      
      Consider a semigroup A in \mathbb{N}^m and a subsemigroup B \subset A.
      such that K[A] is finite over K[B].
      
      The corresponding monomial algebra K[A] is decomposed as a direct sum of ideals in K[B]. In
      
      Le Tuan Hoa, Juergen Stueckrad: Castelnuovo�Mumford regularity of simplicial toric rings.
      
      it is shown that this decomposition exists in the case that K[B] is isomorphic to a polynomial ring
      and is the Noether normalization of K[A] (the simplicial case). It is easy to see that the same is true
      in the general case.
      
      {\bf Setup:}

      This package requires Macaulay2 version 1.4 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("MonomialAlgebras")

      
///


doc ///
  Key
    decomposeMonomialCurve
    (decomposeMonomialCurve,List)
  Headline
    Decomposition for the monomial curve.
  Usage
    decomposeMonomialCurve(A)
  Inputs
    A:List
        of integers containing (dehomogenized) generators of A
  Outputs
    :HashTable
  Description
   Text
     This is a convenient special case of the general function @TO decomposeMonomialAlgebra@.  

     The list A is expected to contain dehomogenized generators of a semigroup.
     This function transforms A into a homogeneous semigroup containing
     powers of the variables. The corresponding monomial algebra
     is decomposed as a direct sum of ideals in its Noether normalization.

     For example the homogeneous coordinate ring of the smooth rational quartic decomposes
     as follows:

   Example
     A = {1,3,4};
     decomposeMonomialCurve A
   Text

     Some more smooth space curves:

   Example
     for d from 4 to 10 do (A = {1,d-1,d};print(A,decomposeMonomialCurve A));
///

doc ///
  Key
    monomialAlgebraIdeal
    (monomialAlgebraIdeal, PolynomialRing)
  Headline
    Compute the ideal of a Monomial Algebra
  Usage
    monomialAlgebraIdeal P
  Inputs
    P: PolynomialRing
       degree monoid is used
  Outputs
    :Ideal
  Description
   Text
     Returns the matrix of relations on the 
     degree monoid of the polynomial ring P
     as an ideal of P.
   Example
     kk=ZZ/101
     B = {{1,2},{3,0},{0,4},{0,5}}
     S = kk[x_0..x_3, Degrees=> B]
     monomialAlgebraIdeal S
     C = {{1,2},{0,5}}
     P = kk[y_0,y_1, Degrees=> C]
     monomialAlgebraIdeal P
///     

doc ///
  Key
    decomposeMonomialAlgebra
    (decomposeMonomialAlgebra,RingMap)
  Headline
    Decomposition of one monomial algebra over a subalgebra
  Usage
    decomposeMonomialAlgebra f
  Inputs
    f : RingMap
        between multihomogenous polynomial rings
  Outputs
    :HashTable
       Let A be the degree monoid of the @TO target@ of f and analogously B for the @TO source@.
       The @TO keys@ are representatives of congruence classes in ZZ*A / ZZ*B.
       The value associated to a key k is a tuple whose first component is an ideal of
       K[B] isomorphic to the K[B]-submodule of K[A] consisting of elements in the class k,
       and whose second component is an element of ZZ*A that is the translation
       vector between the weights of the ideal and the weights of the submodule of
       K[A].
  Description
   Text

     Let K[A] be the monomial algebra of the degree monoid of the @TO target@ of f and 
     let analogously K[B] for @TO source@ of f. Assume that K[A] is finite as a K[B]-module.
     
     The monomial algebra K[A] is decomposed as a direct sum of ideals in K[B].
     
   Example
      A = {{4,2},{10,6},{3,7},{3,6}}
      B = {{4,2},{10,6},{3,7}}
      S = ZZ/101[x_0..x_(#A-1), Degrees=>A];
      P = ZZ/101[x_0..x_(#B-1), Degrees=>B];     
      f = map(S,P)
      decomposeMonomialAlgebra f
   Text
   
      Some simpler examples:

   Example
      A = adjoinPurePowers homogenizeSemigroup {{1,2},{3,0},{0,4},{0,5}}
      B = adjoinPurePowers homogenizeSemigroup {{0,5}}
      S = ZZ/101[x_0..x_(#A-1), Degrees=>A];
      P = ZZ/101[x_0..x_(#B-1), Degrees=>B];     
      f = map(S,P)
      decomposeMonomialAlgebra f      
   Text
   
    Consider the family of smooth monomial curves in $P^3$, the one of degree $d$
    having parametrization 
    $$
     (s,t) \mapsto (s^d, s^{d-1}t, st^{d-1} t^d)\in P^3.
    $$

   Example
     kk=ZZ/101;
     L= for d from 4 to 10 list (f= map(kk[x_0..x_3,Degrees=>{{d,0},{d-1,1},{1,d-1},{0,d}}], kk[x_0,x_3,Degrees=>{{d,0},{0,d}}]));
     (L/decomposeMonomialAlgebra)/print
   Text
     
     Using @TO decomposeMonomialCurve@ the same example is:
        
   Example
     for d from 4 to 10 do (decomposeMonomialCurve{1,d-1,d})     
///



doc ///
  Key
    decomposeSimplicialHomogeneousMonomialAlgebra
    (decomposeSimplicialHomogeneousMonomialAlgebra,List)
  Headline
    Decomposition for the monomial curve.
  Usage
    decomposeSimplicialHomogeneousMonomialAlgebra(A)
  Inputs
    A:List
        containing generators of A
  Outputs
    :HashTable
       The @TO keys@ are representatives of congruence classes in ZZ*A
       modulo the subgroup generated by the degrees of the Noether normalization T.
       The value associated to a key k is a submodule of a rank 1 free module over
       T isomorphic to the T-submodule of K[A] consisting of elements in the class k.
  Description
   Text
     The list A contains dehomogenized generators of a semigroup.
     This function transforms A into a homogeneous semigroup containing
     powers of the variables. The corresponding monomial algebra
     is decomposed as a direct sum of ideals in its Noether normalization.
     
   Example
      A = {{1,2},{3,0},{0,4},{0,5}}
      decomposeSimplicialHomogeneousMonomialAlgebra (A)
   Text
     Using "decomposeMonomialAlgebra" we could do the same example as follows:
   Example
      B = adjoinPurePowers homogenizeSemigroup A
      C = adjoinPurePowers homogenizeSemigroup {{0,5}}
      S = ZZ/101[x_0..x_(#B-1), Degrees=>B]
      P = ZZ/101[x_0..x_(#C-1), Degrees=>C]      
      f = map(S,P)
      decomposeMonomialAlgebra f      
   Text
   
    Consider the family of smooth monomial curves in $P^3$, the one of degree $d$
    having parametrization 
    $$
     (s,t) \mapsto (s^d, s^{d-1}t, st^{d-1} t^d)\in P^3.
    $$
   
   Example
     for d from 4 to 10 do (A = {{d,0},{d-1,1},{1,d-1},{0,d}}; print decomposeSimplicialHomogeneousMonomialAlgebra A)
   Text
     The case of homogeneous monomial curves can be done with simpler notation using 
     the command @TO decomposeMonomialCurve@
///

doc ///
  Key
    adjoinPurePowers
  Headline
    adjoin semigroup elements corresponding to pure powers of variables
  Usage
    adjoinPurePowers A
  Inputs
    A:List
        of lists of ZZ, containing generators of A, all of the same degree d.
  Outputs
    :List
        of lists of ZZ. Same as A, but with elements of the form {d,0...}, {0,d,0...}...
	prepended.
  Description
   Text
      used to simplify the input of complicated homogeneous semigroups     
   Example
      A = {{1,4}, {2,3}}
      adjoinPurePowers A
///


      
      



{*
restart
uninstallPackage("MonomialAlgebras")
installPackage("MonomialAlgebras",RerunExamples=>true);
installPackage("MonomialAlgebras");
viewHelp MonomialAlgebras
*}
