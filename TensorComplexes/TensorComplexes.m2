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
underlyingModules = E -> E.cache.underlyingModules
basisList = E -> E.cache.basisList
fromOrdinal = E -> E.cache.fromOrdinal
toOrdinal = E -> E.cache.toOrdinal

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
      apply(L, i-> #positions(mL, j-> j==i))
     --changes a list of elements of L with repetitions to a list of
     --integers, of length #L whose i-th entry is the number of times L_i
     --occurs in mL
monomialToMultiset=method()
monomialToMultiset(List, List) := (L,mm) ->(
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
     --takes a list of lists, and forms the list of tuples of elements, in order
     --{0,0}, {0,1}, ...
     if #L <= 1 then flatten L else 
     flatten apply(L_0, i->apply( productList drop(L,1), j-> flatten {i,j}))
     )
{*
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
L0 = {}
productList L0
L1 = {toList(0..1)}
productList L1
L2 = {toList(0..1),toList(0..1)}
productList L2
L3 = {toList(0..1),toList(0..1),toList(0..1)}
productList L3
L4 = {toList(0..1),toList(0..1),toList(0..1),toList(0,1)}
productList L4
*}

makeTensorProduct = method()
makeTensorProduct (List) := (L) ->(
     L/makeExplicitFreeModule;
     E := (ring L_0)^(product (L/rank));
     E.cache.underlyingModules = L;
     E.cache.basisList = productList(L/basisList);
     E.cache.fromOrdinal = j -> (basisList E)#j;
     E.cache.toOrdinal = I -> position(basisList E, J->J==I);
     E)
{*
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
E = makeTensorProduct {S^1,S^2,S^3}
basisList E
(toOrdinal E) {0,2,3}
(fromOrdinal E) 5
*}

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

--this isn't right yet:
wedgeToWedgeSym = method()
wedgeToWedgeSym (Module, Module, ZZ) := (F,G,b) -> (
     --creates the map 
     --A :=(wedge^b F) \otimes (Sym^b G)^* \to wedge^b(F\otimes G^*) =: B.
     wedgeF = makeExteriorPower(F,b);
     symG = makeSymmetricPower(G,b);
     A = makeTensorProduct{wedgeF,symG}; --wedgeSym
     B = makeExteriorPower(makeTensorProduct{F,G},b); --wedge
     map(A,B,(i,j)->(
	       I = (fromOrdinal A)i;
	       J = (fromOrdinal B)j;
	       --we have to divide J, and recombine it! Sort of like:
	       --J_0 is a tuple that is a basis elt of F**G
	       --J_1 is too. We must extract the two parts and make
	       --a tuple that is a basis element of wedgF ** symG.
)          

///
--map of wedge^d A \otimes Sym^d B to wedge^d(A\otimes B).
restart
load "~/src/Goettingen-2011/TensorComplexes/TensorComplexes.m2"
kk = ZZ/101
S = kk[a,b,c]
F2 = S^2
F3 = S^3
F5 = S^5
B =makeExteriorPower(makeTensorProduct{F3,F5},2)
A = makeTensorProduct{makeExteriorPower(F3, 2), makeSymmetricPower(F5,2)}
bB = basisList B
bA = basisList A
wedgeSymToWedge(F3,F5,2)
rank A
rank B
rank oo
BU = basisList U;
flatten(BT_0)


///
end

