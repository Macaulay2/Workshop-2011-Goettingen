
newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "", Email => "", HomePage => ""}},
    Headline => "",
    DebuggingMode => true
    )

export
{}
 -- Actual code here!

g=method 
g (HashTable, Ring) := (T,R)->
 (--T is a HashTable
    sum (keys T, A->T#A*product(numgens R,i->(1-((gens R)_i-A_i))))
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
  ///




end

--

restart 
loadPackage "NCF"



T=new MutableHashTable	   
T#{1,1}=1
T#{1,0}=0
T#{0,1}=0
T#{0,0}=0

R=ZZ/2[x1,x2]/ideal(x1^2-x1,x2^2-x2)

peek T
-- Polynomial Formating 3.1                                                                                                                                                        
keys T

