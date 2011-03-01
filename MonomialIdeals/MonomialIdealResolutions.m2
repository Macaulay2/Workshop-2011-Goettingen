newPackage ("MonomialIdealResolutions", Version=>"0.1", Date => "march 2011")

-------------------
-- Exports
-------------------
export {      
  isStable,
  isElement,
  EK,
  EKresolution  
}

-------------------
-- Exported Code
-------------------


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
    chainComplex(apply(numgens(ring I), i -> EK(i,I)))
)



isElement = method();
isElement(RingElement, MonomialIdeal) := Boolean => (f,I) -> (
  any(#I_*, i -> liftable(f/I_i,ring I))
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

-------------------
-- Local-Only Code
-------------------

--
--

admissibleSymbolsMonomial=method();
admissibleSymbolsMonomial(RingElement):=(m)->(
     lista:=subsets toList(0..maxVar(m));
     R:=ring(m);
     mySubsets:=apply (lista, i->product(apply(i,j->R_j)));
     apply(mySubsets,i->(i,m))    
     )

admissibleSymbols=method();
admissibleSymbols(MonomialIdeal):=(M)->(
     apply(first entries gens M,i->admissibleSymbolsMonomial(i))
     )

-- Given a monomial 'm' in the ideal I, returns the unique monomial 'u' in the minimal generating system of the monomial ideal, G(I),
--    satisfying m=u*m' with max(u)<=min(m'). The map from the set of monomials of I, M(I), to G(I) defined by this function is called
--    the canonical decomposition in [EK]

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

           References:

           [EK] S. Eliahou and M. Kervaire, "Minimal Resolutions of Some Monomial Ideals"
	    J. Algebra 129 (1990), 1--25.
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
///

doc ///
   Key
       isElement
   Headline
       check whether an element of the ring is in the ideal or not
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
	 I=ideal(x*y,x^3*z);
	 isElement(f,I)
   SeeAlso
      isSubset
///

doc ///
   Key
       EK
   Headline
       e
   Usage
       a
   Inputs
       e
   Outputs
       e
   Description
       Text
        e 
       Example
        
   SeeAlso
      e
///

doc ///
   Key
       EKResolution
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
	 I=ideal(x^2,x*y,y^2,y*z);
	 EKResolution(I)
   SeeAlso
      MonomialIdeal
      ChainComplex
      res
///
