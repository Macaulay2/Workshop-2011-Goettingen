{*Make the first map of a generic tensor complex
not yet done:

Needed for the tensor complex:
**map of wedge^d A \otimes wedge^d B to Sym(A\otimes B).
**map of wedge^d A \otimes Sym^d B to wedge^d(A\otimes B).



Not needed now, but would be nice:
exterior multiplication and contraction and trace
functoriality for exterior product
functoriality for symmetric product

Note that explict free modules can be identified with their duals!
*}
---
makeExplicitFreeModule = method()
makeExplicitFreeModule(Ring,ZZ) := (S,r) -> (
     --Explicit free modules have cached data about and
     --underlying free module or modules,
     --a list of objects that name basis elements (typically integer lists)
     --a function that takes a basis object and returns its ordinal position,
     --and a function that takes an ordinal and returns a basis object.
     E := S^r;
     E.cache.underlyingModules = {S^r};
     E.cache.basisList = splice {0..r-1};
     E.cache.fromOrdinal = j -> j;
     E.cache.toOrdinal = j -> j;
     E)
makeExplicitFreeModule(Module) := F -> (
     --if F is not yet an "explicit" free module (as witnessed by the
     --absence of F.cache.basisList), make it into one.
     if F.cache.?basisList then F else (
     F.cache.underlyingModules = {F};
     F.cache.basisList = splice {0..rank F -1};
     F.cache.fromOrdinal = j -> j;
     F.cache.toOrdinal = j -> j;
     F))

--shortcuts:
underlyingModules = E -> E.cache.underlyingModules; uM = underlyingModules
basisList = E -> E.cache.basisList ; bL = basisList
fromOrdinal = E -> E.cache.fromOrdinal; fO = fromOrdinal
toOrdinal = E -> E.cache.toOrdinal; tO = toOrdinal

///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
basisList F
E = makeExplicitFreeModule(S^5)
basisList E
E = makeExplicitFreeModule F
///

makeExteriorPower = method()
makeExteriorPower(Module, ZZ) := (F,d) ->(
     --make the exterior power free module, with cache similar to makeTensor.
     --generators are given in revlex order. NOTE: that the basisList is 
     --a list of  subsets of basisList F, NOT a list of 0-1 lists.
     --Can convert back and forth with multisetToMonomial and monomialToMultiset
     makeExplicitFreeModule F;
     E := (ring F)^(binomial(rank F,d));
     E.cache.underlyingModules = {F};     
     E.cache.basisList = subsets(basisList F, d);
     {*The following would give them as 0-1 vectors, but ONLY when basisList F
     is a list of integers:
     ((subsets(basisList F, d))/(s->
	               apply(rank F, i-> #select(1,s,j->j==i))
		       ));
     *}
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)

///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
E = makeExteriorPower(F,2)
basisList E
E2 = makeExteriorPower(E,2)
basisList E2
///

multiSubsets = method()
multiSubsets (List,ZZ) := (L,d) -> (
     --(ordered) d element subsets allowing repetition
     ss := subsets(#L+d-1,d);
     ss1 := ss/(I -> apply(#I, i-> I_i-i));
     apply(ss1, I-> apply(I, i-> L#i))
     )
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
L = {A, {1,2}}
multiSubsets(L,2)
///

makeSymmetricPower = method()
makeSymmetricPower(Module, ZZ) := (F,d) ->(
     --make the symmetric power free module, with cache similar to makeTensor.
     makeExplicitFreeModule F;
     E := (ring F)^(binomial(rank F+d-1, d));
     E.cache.underlyingModules = {F};
     E.cache.basisList = multiSubsets(basisList F,d);
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)

multisetToMonomial=method();
multisetToMonomial(List, List) := (L, mL) -> 
     --changes a list of elements of L with repetitions to a list of
     --integers, of length #L whose i-th entry is the number of times L_i
     --occurs in mL
      apply(L, i-> #positions(mL, j-> j==i))

monomialToMultiset=method()
monomialToMultiset(List, List) := (L,mm) ->(
     --changes a list mm of integers to a list of elements of L
     --where the i-th element of L is repeated m_i times
     flatten apply(#mm, i-> splice{mm_i:L_i}))
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F = makeExplicitFreeModule(S,4)
E = makeSymmetricPower(F,2)
basisList E
N=(basisList E)/(I->multisetToMonomial(basisList F, I))
N/(I->monomialToMultiset(basisList F, I))
(toOrdinal E) {0,3}
(fromOrdinal E) 7
E = makeSymmetricPower(S^4, 2)
basisList E
(toOrdinal E) {0,3}
(fromOrdinal E) 7
///



productList = method()
productList(List):= L->(
     --takes a list of lists, and forms  list of  tuples of elements, in order
     --{0,0}, {0,1}, ...
     Pp := if #L == 0 then {}
     else if #L == 1 then L#0
     else if #L == 2 then flatten (apply(L_0,i->apply(L_1, j->{i,j})))
     else (
	  P0 = productList drop (L, -1);
	  P1 = last L;
	  Pp = (apply(P0,a->apply(P1,b->append(a,b))));
	  --the following line removes the outermost-but-one set of parens
	  splice(Pp/toSequence));
--     for i from 1 to #L-2 do Pp = flatten Pp;
     Pp)
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
L0 = {}
productList L0
L1 = {toList(0..1)}
productList L1
L2 = {toList(0..1),toList(0..2)}
productList L2

L3 = {toList(0..1),toList(0..2),toList(0..1)}
P = productList L3

L4 = {toList(0..1),toList(0..2),toList(0..1),toList(0,1)}
productList L4


M1= {{0, 0}, {0, 1}}
M2 = {{0, 2}, {1, 2}}
L = {M1,M2}
productList L
M3 = {A,B}
L = {M1,M2,M3}
productList L


///

makeTensorProduct = method()
makeTensorProduct (List) := (L) ->(
     L/makeExplicitFreeModule;
     E := (ring L_0)^(product (L/rank));
     E.cache.underlyingModules = L;
     E.cache.basisList = productList(L/basisList);
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)
///
--Note: this is automatically associative!! the commutativity iso is just permuting
--the basis elements.
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F1 = makeExplicitFreeModule(S,2)
F2 = makeExplicitFreeModule(S,3)
F3 = makeExplicitFreeModule(S,5)
E = makeTensorProduct {F1,F2,F3}
--E = makeTensorProduct {S^1,S^2,S^3}
basisList E
(toOrdinal E) {0,2,3}
(fromOrdinal E) 5
///

makeTensorProductMap = method()
makeTensorProductMap (List,Module,Module) := (f,Tsource, Ttarget) ->(
     --given a list of maps f_i: F_i \to G_i, make the tensor product.
     --assume that Tsource = makeTensorProduct (L/source), and similarly for Ttarget.
	       F := f/source;
	       if F != underlyingModules Tsource then error "bad source";
	       G := f/target;
	       if G != underlyingModules Ttarget then error "bad target";	       	       
     map(Ttarget, Tsource, (i,j) -> (
	       I := (fromOrdinal Tsource) j;
	       J := (fromOrdinal Ttarget) i;
	       product apply(#I, u->(f_u)_(((toOrdinal G_u) (J_u)), (toOrdinal F_u) (I_u))))
	  )
     )
makeTensorProductMap (List) := f ->(
     --given a list of maps f_i: F_i \to G_i, make the tensor product.
     --creates Tsource = makeTensorProduct (f/source), and similarly for Ttarget.
	       F := f/source;
	       G := f/target;
     	       Tsource := makeTensorProduct F;
     	       Ttarget := makeTensorProduct G;	       
     map(Ttarget, Tsource, (i,j) -> (
	       I := (fromOrdinal Tsource) j;
	       J := (fromOrdinal Ttarget) i;
	       product apply(#I, u->(f_u)_(((toOrdinal G_u) (J_u)), (toOrdinal F_u) (I_u))))
	  )
     )


makeTrace = method()
makeTrace Module := F ->(
     --make the map S^1 \to F \otimes F
     --where S = ring F and we identify F and F^*
     makeExplicitFreeModule F;
     S := ring F;
     T := makeTensorProduct{F,F};
     S1 := makeExplicitFreeModule(S^1);
     map(T, S1, (i,j) ->(
	   I := (fromOrdinal T)i;
	   if I_0 == I_1 then 1_S else 0_S
	   )))


///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
makeTrace(S^3)
T = makeTensorProduct{S^3, S^3}
///

///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c,d,e,f]
F1 = makeExplicitFreeModule(S,2)
F2 = makeExplicitFreeModule(S,2)
G1= makeExplicitFreeModule(S,2)
G2= makeExplicitFreeModule(S,1)
Ts = makeTensorProduct {F1,F2}
Tt = makeTensorProduct {G1,G2}
f1 = map(G1,F1, {{a,b},{c,d}})
f2 = map(G2,F2, {{e,f}})

makeTensorProductMap ({f1,f2},Ts,Tt)
makeTensorProductMap ({f2,f1})
f1
f2
///

makeSymmetricMultiplication = method()
makeSymmetricMultiplication(Module,ZZ, ZZ) := (F, d,e) ->(
     --make the map Sym^d(F)\otimes Sym^e F \to Sym^(d+e) F
     --Assume SdF = Sym_d F etc.
     Sd = makeSymmetricPower(F,d);
     Se = makeSymmetricPower(F,e);
     Sde = makeSymmetricPower(F,d+e);
     SdSe = makeTensorProduct{Sd,Se};
     toMonomial = (M,I)->multisetToMonomial(basisList((underlyingModules M)#0),I);
     map(Sde,SdSe , (i,j) -> if
       toMonomial(Sde,(fromOrdinal Sde)i) == toMonomial(Sde,(fromOrdinal SdSe)j)
            		    then 1_S else 0_S
	)
     )

{*     if underlyingModule SdF != underlyingModule SeF then error"bad modules";
     if SdF != makeSymmetricPower(F,d) then error"bad first module";
     if SeF != makeSymmetricPower(F,e) then error"bad second module";
*}    
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
makeSymmetricMultiplication(S^2, 1,1)
makeSymmetricMultiplication(S^2, 2,1)
d = 2;e=1;
///

///
--Associativity:
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F3 = S^3
F5 = S^5
F = makeTensorProduct{F2,F3,F5}
F1 = makeTensorProduct{F3,F2,F5}
G = makeTensorProduct{makeTensorProduct{F2,F3},F5}
basisList F
basisList F1
basisList G
///

{*
DtoTensor = method()
DtoTensor (Module) := F -> (
     --Assumes F = D^b G;
     --returns map D^b G --> G\otimes...\otimes G.
     G := (underlyingModules F)#0;
     g := rank G;
     b:=0;
     while binomial(g+b-1,g)<rank F do b = b+1;
     s := signs rank F;
     P = permutations rank F;
     tG := makeTensorProduct(splice{b:G});
     map(tG,F,(i,j) -> )

signs = n->(
     --list the signs of the permutations, in the order they
     --are produced by permuations n. SLOW for n>=7.
          ZF := ZZ^n;
          (permutations n)/(p-> det ZF_p))
*}
///
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
signs 3

time for n from 0 to 8 do print time (signs n;)
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F = makeSymmetricPower(F2, 3)
DtoTensor F
///


--still not quite right
wedgeDToWedge = method()
wedgeDToWedge (Module, Module) := (F,G) -> (
     --requires 
     -- F =  wedge^b F0 \otimes D^b(F1)
     --and 
     -- G = wedge^b(F0\otimes F1).
     --creates the equivariant embedding F->G.
     
     --sort out the underlying modules and ranks
     rankF := rank F;
     WbF0 := (underlyingModules F)#0;
     F0 := (underlyingModules WbF0)#0;
     f0 := rank F0;
     wbf0 := rank WbF0;
     DbF1 := (underlyingModules F)#1;
     dbf1 := rank DbF1;
     F1 := (underlyingModules DbF1)#0;
     f1 := rank F1;     
     F0F1 = (underlyingModules G)#0;
     if F0 != (underlyingModules F0F1)#0 then error"bad modules";
     if F1 != (underlyingModules F0F1)#1 then error"bad modules";     

     --find b
     b:=0;     
     while binomial(f1+b-1,b)<dbf1 do b = b+1;
     
     --make the map
     map(G,F,(i,j)->(
     BG = (fromOrdinal G) i;
     BF = (fromOrdinal F) j;
     BG0 = BG/first; -- corresponds to an element of wedge^b F0
     BG1 = BG/last; -- corresponds to an element of wedge^b F1
     BF0 =  BF_{0..b -1};
     BF1 = BF_{b..2*b-1};-- corresponds to an element of D^b F1
     error"";
     if BG0 != BF0 then 0 -- this assumes that both BG0 and BF#0 will be in order. True??
     else if contents BG1 != BF#1 then 0
     else (perm = apply #B
	  )
     )	  
	  )
)

permSign = method()
permSign(List, List) := (L,M) ->(
     --L,M are lists of the same length, possibly with repetitions.
     -- Returns 0 if the elements and multiplicities don't match. 
     )
///
--map of wedge^d A \otimes Sym^d B to wedge^d(A\otimes B).
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
FF2 = S^4
FF3 = S^3
DbFF2 = makeSymmetricPower(FF2, 2)
WbFF3 = makeExteriorPower(FF3,2)
F = makeTensorProduct{WbFF3, DbFF2}
G = makeExteriorPower(makeTensorProduct{FF3,FF2},2)
wedgeDToWedge(F,G)
for i from 0 to rank G -1 do for j from 0 to rank F -1 do(
     BG = (fromOrdinal G) i;
     BF = (fromOrdinal F) j;
     BG0 = BG/first; -- corresponds to an element of wedge^b F0
     BG1 = BG/last; -- corresponds to an element of wedge^b F1
     BF0 =  BF_{0..b -1};
     BF1 = BF_{b..2*b-1};-- corresponds to an element of D^b F1
     print (BG1, BF1))
)
///
end

