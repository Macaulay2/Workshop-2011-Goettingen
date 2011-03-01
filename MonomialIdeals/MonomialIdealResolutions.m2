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

isElement = method();
isElement(RingElement, MonomialIdeal) := Boolean => (f,I) -> (
  any(#I_*, i -> f%I_i == 0)
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

doc ///
   Key
       isStable
   Headline
       
   Usage
       
   Inputs
       
   Outputs
       
   Description
       Text
         
       Example
        
   SeeAlso
      
///

doc ///
   Key
       isElement
   Headline
       
   Usage
       
   Inputs
       
   Outputs
       
   Description
       Text
         
       Example
        
   SeeAlso
      
///

doc ///
   Key
       EK
   Headline
       
   Usage
       
   Inputs
       
   Outputs
       
   Description
       Text
         
       Example
        
   SeeAlso
      
///doc

 ///
   Key
       EKresolution
   Headline
       
   Usage
       
   Inputs
       
   Outputs
       
   Description
       Text
         
       Example
        
   SeeAlso
      
///