needsPackage ("SimplicialComplexes");


newPackage (
  "MonomialIdealResolutions",
  Version=>"0.1",
  Date => "march 2011",
  Authors => {{Name => "Eduardo Saenz De Cabezon Irigara", Email => "eduardo.saenz-de-cabezon@unirioja.es"},
              {Name => "Oscar Fernandez-Ramos", Email => "caribefresno@gmail.com"},
              {Name => "Christof Söger", Email => "csoeger@uos.de"}},
  Headline => "various decomposability routines for simplicial complexes",
  DebuggingMode => false
)

needsPackage ("SimplicialComplexes");
-------------------
-- Exports
-------------------
export {      
  isStable,
  isElement,
  EK,
  EKResolution,
  scarf,  
  isSQStable,
  AHH,
  AHHResolution,
  simplicialResolutionDifferential,
  simplicialResolution
}

-------------------
-- Exported Code
-------------------

lcmMon=method();
lcmMon(List, List):= (L1,L2) -> (
      apply(L1,L2, (a,b)->max({a,b}))   
)  

scarf=method();
scarf(MonomialIdeal):= I -> (
     print cpuTime ();
 labels:=apply(I_*, m->flatten exponents m);
 n:=numgens I;
 faceSet:={{}};
 degreeSet:={apply(length labels_0,k->0)};
 local deg;
 for i from 0 to length labels-1 do(
--      print("i=",i);
     for j from 0 to length faceSet-1 do(
--	  print("j=",j);
--	  print(degreeSet_j,labels_i);
	  deg=lcmMon(degreeSet_j,labels_i);
          if not member(deg,degreeSet) then
--	       print faceSet_j;
	       faceSet=faceSet|{faceSet_j|{i}};
	       degreeSet=degreeSet|{deg};	  
     );	      
 );
x:=getSymbol "x";
--R:=QQ[apply(n,i->getSymbol ("x_"|toString i))];
R:=QQ[x_0..x_(n-1)];
l:=apply (drop(faceSet,1),f->product(apply(f,i->R_(x_i))));
print cpuTime();
return simplicialComplex l;
print cpuTime();
)


EK = method()
EK(ZZ,MonomialIdeal):= (n,I)->(
   --- create the nth differential in Eliahou-Kervaire's resolution
   retVal := Nothing;
   if (n == 0) then 
      retVal = gens I
   else
   {
      R := ring I;
      symbolsList:=admissibleSymbols(I);
      sourceList:=symbolsList_(positions (symbolsList,i->first degree(promote(i_0,R))==n));
      targetList:=symbolsList_(positions (symbolsList,i->first degree(promote(i_0,R))==n-1));
      getCoeff := (i,j) -> if (liftable(sourceList_j_0//targetList_i_0,R) and (targetList_i_1==sourceList_j_1)) then
                             (-1)^(position(positions(flatten exponents(sourceList_j_0),r->r!=0),s->s==position(first entries vars R,t->t==sourceList_j_0//targetList_i_0)))
			   else if  (liftable(sourceList_j_0//targetList_i_0,R) and (canonicalDecomp(lift(sourceList_j_0//targetList_i_0,R)*sourceList_j_1,first entries gens I)==targetList_i_1)) then
                             (-1)^(1+position(positions(flatten exponents(sourceList_j_0),r->r!=0),s->s==position(first entries vars R,t->t==sourceList_j_0//targetList_i_0)))
			   else 0_R;
       myFn := (i,j) -> (tempElt := sourceList_j_0 / targetList_i_0;
	    	      	 if (liftable (tempElt,R)) then tempElt2:=(lift(tempElt,R)*sourceList_j_1)//canonicalDecomp(lift(tempElt,R)*sourceList_j_1,first entries gens I);
	                if (liftable(tempElt,R) and (targetList_i_1==sourceList_j_1) ) then  getCoeff(i,j)*lift(tempElt,R)
			  else if (liftable(tempElt,R) and (targetList_i_1==canonicalDecomp(lift(tempElt,R)*sourceList_j_1,first entries gens I))) then 
			       getCoeff(i,j)*(tempElt2)
			 else 0_R);      
      retVal = map(R^(-apply(targetList, i -> (degree(promote(i_1,R)*promote(i_0,R))))), R^(-apply(sourceList, i -> (degree(promote(i_1,R)*promote(i_0,R))))), myFn);
   };
   retVal
)

EKResolution=method();
EKResolution(MonomialIdeal):=(I)->(
    chainComplex(apply((0..numgens(ring I)-1), i -> EK(i,I)))
)

isElement = method();
isElement(RingElement, MonomialIdeal) := Boolean => (f,I) -> (
  all (exponents f,
    fexp -> any(I_*, g -> all(fexp, flatten exponents g, (fe,ge) -> fe >= ge ))
  )
);


-- PURPOSE: check if a monomial ideal is stable
-- INPUT:   a monomial ideal
-- OUTPUT:  true if the ideal is stable and false otherwise. 
-- COMMENT: checks only for the ordering in which the variables appear in the ring  

isStable = method();
isStable(MonomialIdeal) := Boolean => (I) -> (
  genlist := I_*;
  S:=ring I;
  not any(
    #genlist, i-> (
      g:=I_i; mv:=maxVar(g); f:=lift(g/S_mv,S);
      any(mv, j -> not isElement(f*S_j,I))
    )
  )
);

--The following is the Squarefree version (SQ) of isStable.
--NOTE: squarefree stable is different from squarefree and stable

isSQStable = method();
isSQStable(MonomialIdeal) := Boolean => (I) -> (
  genlist := I_*;
  S:=ring I;
  not any(
    #genlist, i-> (
      g:=I_i; mv:=maxVar(g); vars:=positions((first exponents g)_{0..mv},i->i==0);f:=lift(g/S_mv,S);
      any(vars, j -> not isElement(f*S_j,I))
    )
  )
);


--Aramova-herzog-Hibi gave a resolution for squarefree stable monomial ideals
--which basically corresponds to Eliahou-kervaire's for stable ideals

AHH = method()
AHH(ZZ,MonomialIdeal):= (n,I)->(
   --- create the nth differential in Aramova-Herzog's resolution
   retVal := Nothing;
   if (n == 0) then 
      retVal = gens I
   else
   {
      R := ring I;
      symbolsList:=admissibleSQSymbols(I);
      sourceList:=symbolsList_(positions (symbolsList,i->first degree(promote(i_0,R))==n));
      targetList:=symbolsList_(positions (symbolsList,i->first degree(promote(i_0,R))==n-1));
      getCoeff := (i,j) -> if (liftable(sourceList_j_0//targetList_i_0,R) and (targetList_i_1==sourceList_j_1)) then
                             (-1)^(position(positions(flatten exponents(sourceList_j_0),r->r!=0),s->s==position(first entries vars R,t->t==sourceList_j_0//targetList_i_0)))
			   else if  (liftable(sourceList_j_0//targetList_i_0,R) and (canonicalDecomp(lift(sourceList_j_0//targetList_i_0,R)*sourceList_j_1,first entries gens I)==targetList_i_1)) then
                             (-1)^(1+position(positions(flatten exponents(sourceList_j_0),r->r!=0),s->s==position(first entries vars R,t->t==sourceList_j_0//targetList_i_0)))
			   else 0_R;
       myFn := (i,j) -> (tempElt := sourceList_j_0 / targetList_i_0;
	    	      	 if (liftable (tempElt,R)) then tempElt2:=(lift(tempElt,R)*sourceList_j_1)//canonicalDecomp(lift(tempElt,R)*sourceList_j_1,first entries gens I);
	                if (liftable(tempElt,R) and (targetList_i_1==sourceList_j_1) ) then  getCoeff(i,j)*lift(tempElt,R)
			  else if (liftable(tempElt,R) and (targetList_i_1==canonicalDecomp(lift(tempElt,R)*sourceList_j_1,first entries gens I))) then 
			       getCoeff(i,j)*(tempElt2)
			 else 0_R);      
      retVal = map(R^(-apply(targetList, i -> (degree(promote(i_1,R)*promote(i_0,R))))), R^(-apply(sourceList, i -> (degree(promote(i_1,R)*promote(i_0,R))))), myFn);
   };
   retVal
)

AHHResolution=method();
AHHResolution(MonomialIdeal):=(I)->(
     R:=ring(I);
     maxlevel:=length(R_*)-max(apply(I_*,i->(maxVar(i)+1-first degree(i))))-1;
     chainComplex(apply((0..maxlevel), i -> AHH(i,I)))
)



simplicialResolutionDifferential=method();

simplicialResolutionDifferential(ZZ,MonomialIdeal,SimplicialComplex):=(n,I,C) -> (
    retVal := Nothing;
    if (n == 0) then 
      retVal = gens I
    else
    {
     R:=ring I;
     sourceL:=flatten apply(first entries faces(n,C),i->exponents(i));
     targetL:=flatten apply(first entries faces(n-1,C),i->exponents(i));
     sourceMonos:=apply(sourceL,k->myLcm(apply(positions(k,i->i!=0),j->I_j)));
     targetMonos:=apply(targetL,k->myLcm(apply(positions(k,i->i!=0),j->I_j)));
      getCoeff := (i,j) -> if (not member(-1,sourceL_j-targetL_i)) then
                             (-1)^(position(positions(sourceL_j,s->s!=0),t->sourceL_j_t!=targetL_i_t))
			   else 0_R;
      myFn := (i,j) -> (tempElt := sourceMonos_j / targetMonos_i;
	                if (liftable(tempElt,R)) then getCoeff(i,j)*lift(tempElt,R) else 0_R);
      retVal = map(R^(-apply(targetMonos, i -> degree i)), R^(-apply(sourceMonos, i -> degree i)), myFn);
    };
    retVal
     )


simplicialResolution=method();
simplicialResolution(MonomialIdeal, SimplicialComplex):=(I,C)-> (
     R:=ring(I);
     if (length(first entries faces(0,C))!=numgens I) then error "the number of vertices of the simplicial complex has to be the same as the number of generators of the ideal";
     chainComplex(apply((0..dim C),i->simplicialResolutionDifferential(i,I,C)))
     )


-------------------
-- Local-Only Code
-------------------

--lcm function taken from package "ChainComplexExtras.m2"
myLcm = method()
myLcm(List):=(ringList)->(
   --- just a short method computing the lcm of the list of elements
   myList := apply(ringList, i -> ideal(i));
   (intersect myList)_0
)

admissibleSymbolsMonomial=method();
admissibleSymbolsMonomial(RingElement):=(m)->(
	  R:=ring m;
     lista:=subsets toList(0..maxVar(m)-1);
     mySubsets:=apply (lista, i->product(apply(i,j->R_j)));
     apply(mySubsets,i->(i,m))    
     )

admissibleSymbols=method();
admissibleSymbols(MonomialIdeal):=(M)->(
     flatten apply(first entries gens M,i->admissibleSymbolsMonomial(i))
     )

-- Given a monomial 'm' in the ideal I, returns the unique monomial 'u' in the minimal generating system of the monomial ideal, G(I),
-- satisfying m=u*m' with max(u)<=min(m'). The map from the set of monomials of I, M(I), to G(I) defined by this function is called
-- the canonical decomposition in [EK]
canonicalDecomp=method();
canonicalDecomp(RingElement,List):=(m,G)->( 
     vm:=flatten exponents m;  
     vG:=apply(G,g->flatten exponents g);
     n:=length vm-1;
     for j from 0 to length G-1 do(
	for i from 0 to n do(
	     if vG_j_i>vm_i then break;
	     if (vG_j_i<=vm_i and any(toList(i+1..n-1),k->vG_j_k>vm_k)) then break;
	     return G_j;  
	);       
     );	
     return("Error: this monomial does not belong to the ideal")  
)

--
--

maxVar=method();
maxVar(RingElement):=(m)->(
     max positions(first(exponents(m)),i->i!=0)
);

--The squarefree (SQ) versions of admissible symbols
admissibleSQSymbolsMonomial=method();
admissibleSQSymbolsMonomial(RingElement):=(m)->(
     R:=ring m;
     lista:=subsets positions((first exponents (m))_{0..maxVar(m)},i->i==0);
     mySubsets:=apply (lista, i->product(apply(i,j->R_j)));
     apply(mySubsets,i->(i,m))    
     )

admissibleSQSymbols=method();
admissibleSQSymbols(MonomialIdeal):=(M)->(
     flatten apply(first entries gens M,i->admissibleSQSymbolsMonomial(i))
     )


-------------------
-- Documentation
-------------------
beginDocumentation()

doc ///
   Key
       MonomialIdealResolutions
   Headline
       resolutions of some monomial ideals.
   Description
       Text
          This package includes Eliahou-Kervaire resolution for stable monomial ideals. 
           It also includes Aramova-Herzog-Hibi resolution for squarefree stable monomial ideals (note that squarefree stable is different from "squarefree and stable").
           References:

           [EK] S. Eliahou and M. Kervaire, "Minimal Resolutions of Some Monomial Ideals"
	    J. Algebra 129 (1990), 1--25.
	   [AHH] A.Aramova, J. Herzog and T. Hibi, "Squarefree lexsegment ideals"
	   Mat. Zeitschrift 228 (1998), 353-378
///

doc ///
   Key
       isStable
		 (isStable, MonomialIdeal)
   Headline
       checks whether a monomial ideal is stable
   Usage
       isStable I
   Inputs
       I: MonomialIdeal
   Outputs
       B: Boolean
           returns true if and only if I is stable
   Description
       Text
           Determines if the monomial ideal I is stable. It uses the ordering of variables given by the ring of I. 
       Example
           R = QQ[x,y,z];
           I = monomialIdeal(x^3,x^2*y,x*y^2,y^3);
           isStable I
           J = monomialIdeal(x^3,x*y^2,y^3);
           isStable J
   SeeAlso
     MonomialIdeal
	  isElement 
	  isSQStable
///
doc ///
   Key
       isSQStable
		 (isSQStable, MonomialIdeal)
   Headline
       checks whether a monomial ideal is squarefree stable
   Usage
       isSQStable I
   Inputs
       I: MonomialIdeal
   Outputs
       B: Boolean
           returns true if and only if I is squarefree stable
   Description
       Text
           Determines if the monomial ideal I is squarefree stable. It uses the ordering of variables given by the ring of I. 
       Example
           R = QQ[x,y,z];
           I = monomialIdeal(x*y,x*z,y*z);
           isSQStable I
           J = monomialIdeal(x,y*z);
           isStable J
   SeeAlso
     MonomialIdeal
	  isElement 
	  isStable
///
doc ///
   Key
       isElement
		 (isElement, RingElement, MonomialIdeal)
   Headline
       check whether an element of the ring is in the monomial ideal or not
   Usage
       isElement(f,I)
   Inputs
       f: RingElement 
       I: MonomialIdeal
   Outputs
       B: Boolean
   Description
       Text
           This function check if f belongs to I
       Example
         R=QQ[x,y,z];
         f=x*y^2+x^3*y*z+z^2;
         g=x^2*y+x*y*z+x^3*z^3;
         I=monomialIdeal(x*y,x^3*z);
         isElement(f,I)
         isElement(g,I)
   SeeAlso
      isSubset
///

doc ///
   Key
       EK
       (EK,ZZ,MonomialIdeal)
   Headline
       e
   Usage
       a
   Inputs
       n: ZZ
		 I: MonomialIdeal
   Outputs
       m: 
   Description
       Text
        e 
       Example
        
   SeeAlso
      
///

doc ///
   Key
       EKResolution
		 (EKResolution,MonomialIdeal)
   Headline
       constructs the minimal free resolution given by S. Eliahou and M. Kervaire in [EK] for a stable monomial ideal. 
   Usage
       EKResolution I
   Inputs
       I: MonomialIdeal
   Outputs
       C: ChainComplex
   Description
       Text
         It computes degrees of modules and differencials in the minimal resolution of I  
       Example
         R=QQ[x,y,z];
         I=monomialIdeal(x^2,x*y,y^2,y*z);
         EKResolution(I)
   SeeAlso
      MonomialIdeal
      ChainComplex
      res
///


doc ///
   Key
       AHH
   Headline
       e
   Usage
       a
   Inputs
       n: ZZ
		 I: MonomialIdeal
   Outputs
       m: 
   Description
       Text
        e 
       Example
        
   SeeAlso
      
///

doc ///
   Key
       AHHResolution
   Headline
       constructs the minimal free resolution given by A. Aramova, J. Herzog and T. Hibi in [AHH] for a squarefree stable monomial ideal. 
   Usage
       AHHResolution I
   Inputs
       I: MonomialIdeal
   Outputs
       C: ChainComplex
   Description
       Text
         It computes degrees of modules and differencials in the minimal resolution of I  
       Example
         R=QQ[x,y,z];
         I=monomialIdeal(x*y,x*z,y*z);
         AHHResolution(I)
   SeeAlso
      MonomialIdeal
      ChainComplex
      res
///

-------------------
-- Tests
-------------------

-- Tests isElement
TEST ///
R = QQ[x,y,z];
I = monomialIdeal(x^3,x^2*y,x*y^2,y^3);
assert(isElement(x^3+x^6-x*y^3, I));
assert(isElement(y^3, I));
assert(not isElement(x^2, I));
assert(not isElement(x*y, I));
assert(not isElement(x*y*z, I));
///


-- Tests isStable
TEST ///
R = QQ[x,y,z];
I = monomialIdeal(x^3,x^2*y,x*y^2,y^3);
assert(isStable I);
J = monomialIdeal(x^3,x*y^2,y^3);
assert(not isStable J);
///

