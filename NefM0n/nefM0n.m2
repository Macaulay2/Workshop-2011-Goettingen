-- -*- coding: utf-8 -*-
newPackage(
        "NefM0n",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {}

-- Code here
export {keelSum, keelAvgIndices, boundaryRing, fCurveIneqsCB}

BoundaryRing = new Type of HashTable

protect M0nIndices;
protect M0nList;
protect M0nComplement;

listComplement = (L, K) -> toSequence sort toList(set L - set K)


--**************************************************************************      
--**************************************************************************
     
boundaryRing = method()
boundaryRing ZZ := n-> (
     nList := toSequence(1..n);
     Indices := reverse flatten apply(n-3, i-> subsets(nList, i+2));
     Indices = Indices/toSequence;
     D := getSymbol "D";
     BDivs := apply(Indices, i-> D_i);
     R := QQ[BDivs];
     
     I:= ideal for i in Indices list R_(D_i) - R_(D_(listComplement(nList, i)));
     
     RBnd := R/I;
     
     E := new HashTable from for i in Indices list (i => RBnd_(D_i));

     
     B:= new BoundaryRing from {
	  M0nIndices => Indices, 
	  M0nList => nList,
	  Ring => RBnd,
	  Variables =>  E,
	  M0nComplement => i -> toSequence (elements (set nList - set i))
	  };
     
     B
     )

BoundaryRing_List := (B,i) -> B.Variables#i


-- Define the ideal I = ideal( D_J - D_{J^c}) \subseteq R. Redundancies included to make code more transparent.

keelSum = method()
keelSum (List, BoundaryRing) := (K,R)-> (
     --Input a split four-tuple K = {{i,j}, {k,l}}
     -- and output the sum
     --  \sum_{{i,j} \subseteq J, {k,l} subseteq J^c} D_J
     
     if #(set K_0 * set K_1) != 0 then error "expected pairs in the list to be disjoint";
     bndsum:= 0;
     apply(R.M0nIndices, j-> (
      	       if (isSubset(K_0, set(j)) and isSubset( K_1, set R.M0nComplement j) )
	       then bndsum = bndsum + (R#Variables)#j;
	       )
       	  );
     bndsum
     );


--**************************************************************************      
--**************************************************************************

keelAvgIndices = method()
keelAvgIndices (Sequence, List, BoundaryRing) := (J, IList, R) -> (
     --Input a sequence J (i.e. a boundary index J), 
     -- a list of lists IList = {IList_x} (with each IList_x a four-tuple),
     -- and the BoundaryRing R,
     -- and output average of numerical equivalence class of D_J
     -- over all Keel relations I_x 
     
     --error messages
    --if not all (IList, x-> #x == 4) then error "expected elements of the list of the second argument to all have cardinality four";
    
     
     
     avg:= 0;
     counter:= 0;
     i:={};
     j:={};
  
     for x from 0 to (#IList - 1)
		-- only include in the average those Keel relations of I_x
		--  such that I_x \int J ==2, that is, D_J appears in I_x 
		when ( # (set IList_x * set J) == 2 )
		do (
		i = toList(set IList_x * set J );
		j = listComplement(IList_x, toList(set IList_x * set J ));
		counter = counter + 2;
		avg = avg - 2*keelSum({i,j},R) 
		          + keelSum({{i_0, j_0}, {i_1, j_1}},R)
			  + keelSum({{i_0, j_1}, {i_1, j_0}},R)
			  + 2*(R#Variables)#J;
			  );
	   return (avg/counter))
      
      
      
--**************************************************************************      
--**************************************************************************
fCurveIneqsCB = method()
fCurveIneqsCB (ZZ, String) := (n, fileName)->(
     --input an integer n and a string
     -- outputs to the file fileName the F-inequalities for M_{0,n}
     -- with respect to the sl_2 level 1 conformal block divisor class basis
     -- for N^1(\M_{0,n})_QQ
     ofile := openOutAppend fileName;
     nList := toList(1..n);
     

     --generate F-indices, that is, four-tuples {n1, n2, n3, n4} such that
     -- n1 <= .. <= n4 and n1 + ... + n4 = n     
     fIndices := {};
     fIndices := select({1,1,1,1}..{n,n,n,n}, p-> sum p = n)
  --   for n1 from 1 to n do (
    --	  for n2 from 1 to n do (
--	       for n3 from 1 to n do (
--	      	    for n4 from 1 to n do(
--		   	 if (n1 <= n2 and n2 <= n3 and n3 <= n4 and (n1 + n2 + n3 + n4 == n)) then	    
--	      	   	 fIndices = fIndices | {{n1, n2, n3, n4}}
--	      	   	 );    
--	      	    );
  --  	       );
    -- 	  );
     
     
     --Generate F-curves in \M_{0,n}, that is partitions {N1, N2, N3, N4} of {1..n}
     fCurves := {};
     apply(fIndices, t -> (
	       for N1 in subsets(nList, t_0) do (
     	       	    N1c := listComplement(nList, N1);
	       	    for N2 in subsets(N1c, t_1) do (
		    	 --Eliminate duplicates by only 
		    	 if (t_0 != t_1 or (t_0 == t_1 and N1_0 < N2_0))
		    	 then (
		    	      N2c := listComplement(N1c, N2);
			      for N3 in subsets(N2c, t_2) do (
			      	   if (t_1 != t_2 or (t_1 == t_2 and N2_0 < N3_0))
			      	   then (
				   	N3c := listComplement(N2c, N3);
				   	for N4 in subsets(N3c, t_3) do (
					     if (t_2 != t_3 or (t_2 == t_3 and N3_0 < N4_0) )
					     then (
			 	   	     	  fCurves = fCurves | {{N1, N2, N3, N4}}
					     	  )--end if then
				   	     )--end for over N4
			 	   	)--end if then
		       		   )--end for over N3
		       	      )--end if then     
	       	    	 )--end for over N2
	       	    )--end for over N1
	       )--end t -> ()
	  );--end apply


         --Output inequalities F(N1, N2, N3, N4) in CB coordinates to the file fileName,
	 -- i.e. output \cdot D \geq 0, where [D] = \sum d_I [DD_I]
	 apply(fCurves, F -> (
	  	   for i from 2 to floor(n/2) do (
     	       		apply(subsets(nList, 2*i), I -> (
	       		 	  -- Calculate the intersection of the F-curve F with the CB-divisor D_I,
	       		 	  --  namely, F \cdot D_I = 1 if \prod i=1^4 #(F_i \cap I)  odd, 0 else
	       		 	  parity := (#(set I * set F_0 ) * #(set I * set F_1 ) * #(set I * set F_2 ) * #(set I * set F_0 ) );
	       		 	  if odd parity 
	       		 	  then (
			      	       fileName << " +d_" << I;
			      	       )
			 	  )--end I -> ()
	  	    	     )--end apply over I
     	       		);-- end for over 2i, the cardinality of I
	  	   fileName << ">= 0" << endl;
	  	   )-- end F-> ()
          
     	  );-- end apply     
     fileName << close;
     );

end
beginDocumentation()

doc ///
Key
  FultonM0n
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
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
restart
loadPackage "FultonM0n"
R = boundaryRing 7;
S = R#Ring
keelSum({{1,3},{2,4}}, R)
tex keelAvgIndices( (1,2,3), {{2,3,4,5}}, R)
tex keelAvgIndices( (1,2,3), {{1,2,4,5}, {1,2,4,6}, {1,2,5,6}, {1,3,4,5}, {1,3,4,6}, {1,3,5,6}, {2,3,4,5}, {2,3,4,6}, {2,3,5,6}},R)

fCurveIneqsCB (5, "fIneqs5.txt") 