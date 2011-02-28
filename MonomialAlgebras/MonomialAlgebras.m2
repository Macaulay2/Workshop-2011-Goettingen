needsPackage "Polyhedra"

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

export({decomposeMonomialCurve})

needsPackage "Polyhedra"

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


------------------------------------------------------------------------------------------



beginDocumentation()

doc ///
  Key
    MonomialAlgebras
  Headline
    Monomial Algebras.
  Description
    Text
      {\bf What's new:}

      {\it Version 0.01:}

      First version.

      {\bf Overview:}
      
      Consider a semigroup A in \mathbb{N}^m and a subsemigroup B \subset A
      such that rank(G(B))=rank(G(A)).
      
      We decompose k[A] as a K[B]-module into a direct sum of ideals of K[B].
      
      {\bf Setup:}

      This package requires Macaulay2 version 1.4 or newer.

      Install this @TO Package@ by doing

      @TO installPackage@("MonomialAlgebras")

      {\bf Examples:}

      {\bf Curves:}

      @TO "Curve Example 1"@

      
///


doc ///
  Key
    decomposeMonomialCurve
    (decomposeMonomialCurve,List)
  Headline
    Decomposition for the monomial curve.
  Usage
    decomposeMonomialCurve(I)
  Inputs
    L:List
        containing generators of A
  Outputs
    :List
  Description
   Text
        Compute the decomposition for a curve parametrized by the monomials t^a with a \in A
        and B given by the first and the last element of A.

   Example
     A = {1,3,4};
     decomposeMonomialCurve A
///



doc ///
  Key
    "Curve Example 1"
  Description
   Text
   
    Consider
   
   Example
     A = {1,3,4};
     decomposeMonomialCurve A
///




{*
uninstallPackage("MonomialAlgebras")
installPackage("MonomialAlgebras",RerunExamples=>true);
installPackage("MonomialAlgebras");
*}
