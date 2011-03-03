{*makeTensor1 = method()
makeTensor1(List) := (L) ->(
     --make the tensor product module F = \otimes L_i
     --with 
     --F.cache.modules = L
     --F.cache.Lranks list of ranks
     --F.cache.toOrdinal 
     --     a function that takes a list I of ZZ with I_j<rank L_i 
     --	    and returns the ordinal position of the corresponding basis vector of F
     --F.cache.fromOrdinal 
     --     a function that takes an integer and returns the index set I
     --     of the basis vector in that ordinal position.
     
     --eventually the L_i might also be modules with structure of this type.
     n := #L;
     Lranks := L/rank;
     LToOrdinal = apply(L, G -> 
	  if not G.cache.?toOrdinal then G.cache.toOrdinal = i->i);
     LFromOrdinal = apply(L, G -> 
	  if not G.cache.?fromOrdinal then G.cache.fromOrdinal = i->i);
     --make list whose i-th term is the product of all but the last i+1 elements of L,
     --with i starting at 0. (thus Lprods_(n-1) = 1, the empty product.)
     Lprods = for i from 0 to n-1 list product (Lranks_{i+1..n-1});
     F := (ring L_0)^(product Lranks);
     F.cache.modules = L;
     F.cache.ranks = Lranks;
     F.cache.toOrdinal = I -> sum apply(#I, j->(L_j).cache.toOrdinal(I#j)*(Lprods#j));
     F.cache.fromOrdinal = p -> reverse (for i from 0 to n-1 list(
     	                         pcomponent = p%Lranks#(n-1-i);
					 p = (p-pcomponent)//Lranks#(n-1-i);
					 (L#(n-1-i)).cache.fromOrdinal pcomponent));
    F )
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk= ZZ/101
S = kk[a,b,c]

L = {S^2, S^3, S^5}
F = makeTensor1(L)
F.cache.toOrdinal {1,2,4}
for d from 0 to 29 do print (d == F.cache.toOrdinal F.cache.fromOrdinal d)
///
*}
