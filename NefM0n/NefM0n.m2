-- -*- coding: utf-8 -*-
newPackage(
        "NefM0n",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "Lars Kastner", 
                  Email => "kastner@math.fu-berlin.de", 
                  HomePage => "http://page.mi.fu-berlin.de/lkastner"},
	     {Name => "Paul Larsen", 
                  Email => "larsen@math.hu-berlin.de", 
                  HomePage => "www.math.hu-berlin.de/~larsen"}},
        Headline => "",
        DebuggingMode => true
        )

export {}

-- Code here
export {keelSum, keelAvgIndices, boundaryRing, fCurveIneqsLPSOLVE, fCurveIneqsMatrix, cJinDDI, cJinD}

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
fCurveIneqsLPSOLVE = method()
fCurveIneqsLPSOLVE (ZZ, String) := (n, fileName)->(
     --input an integer n and a string
     -- outputs to the file fileName the F-inequalities for M_{0,n}
     -- with respect to the sl_2 level 1 conformal block divisor class basis
     -- for N^1(\M_{0,n})_QQ
     ofile := openOutAppend fileName;
     nList := toList(1..n);
     

     --generate F-indices, that is, four-tuples {n1, n2, n3, n4} such that
     -- n1 <= .. <= n4 and n1 + ... + n4 = n     
     
     fIndices := select({1,1,1,1}..{n,n,n,n}, p-> (sum p == n) and (p#0<=p#1) and (p#1<=p#2) and (p#2<=p#3));
     
     --Generate F-curves in \M_{0,n}, that is partitions {N1, N2, N3, N4} of {1..n}
     
     fCurves := flatten flatten flatten flatten apply(fIndices, t -> (
	       for N1 in subsets(nList, t_0) list (
		    N1c := listComplement(nList, N1);
		    for N2 in select(subsets(N1c, t_1), N2 -> t_0 != t_1 or (t_0 == t_1 and N1_0 < N2_0)) list (
		    	 --Eliminate duplicates by only 
			 N2c := listComplement(N1c, N2);
			 for N3 in select(subsets(N2c, t_2), N3 -> (t_1 != t_2 or (t_1 == t_2 and N2_0 < N3_0))) list (
			      N3c := listComplement(N2c, N3);
			      for N4 in select(subsets(N3c, t_3), N4 ->  (t_2 != t_3 or (t_2 == t_3 and N3_0 < N4_0) )) list (
				   {N1, N2, N3, N4}
				   ) -- end for over N4
			      ) -- end for over N3
			 ) -- end for over N2
		    ) -- end for over N1
	       ) -- end t->(
	  ); -- end apply
				          
			      	


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

minimalValue = method()
minimalValue(Matrix, Vector) := (A, u) -> (
     S := replace("\\}","]",replace("\\{", "[", toString entries A));
     S = "my $p = new Polytope<Rational>(INEQUALITIES =>" | S | ");";
     tmp := temporaryFileName()|".poly";
     polyIn := openOut(tmp);
     polyIn << "use application \"polytope\";" << endl;
     polyIn << S << endl;
     polyIn << "my $u = new Vector<Rational>(";
     polyIn << replace("\\{|\\}","", toString entries u);
     polyIn << ");" << endl;
     polyIn << "$p->LP = new LinearProgram<Rational>(LINEAR_OBJECTIVE=>$u);" << endl;
     polyIn << "print $p->LP->MINIMAL_VALUE;";
     close polyIn;
     run("polymake --script " | tmp | " > " | tmp | ".out");
     get(tmp | ".out")
     )

minimalVertex = method()
minimalVertex(Matrix, Vector) := (A, u) -> (
     S := replace("\\}","]",replace("\\{", "[", toString entries A));
     S = "my $p = new Polytope<Rational>(INEQUALITIES =>" | S | ");";
     tmp := temporaryFileName()|".poly";
     polyIn := openOut(tmp);
     polyIn << "use application \"polytope\";" << endl;
     polyIn << S << endl;
     polyIn << "my $u = new Vector<Rational>(";
     polyIn << replace("\\{|\\}","", toString entries u);
     polyIn << ");" << endl;
     polyIn << "$p->LP = new LinearProgram<Rational>(LINEAR_OBJECTIVE=>$u);" << endl;
     polyIn << "print $p->LP->MINIMAL_VERTEX;";
     close polyIn;
     run("polymake --script " | tmp | " > " | tmp | ".out");
     polyOut := get(tmp | ".out");
     polyOut = vector apply(separate(" ", polyOut), n-> value n)
     )

getLinComb = method()
getLinComb(Matrix, Vector, Vector) := (A, u, v) -> (
     pos := positions(entries A*v, i-> i==0);
     )

--**************************************************************************      
--**************************************************************************
fCurveIneqsMatrix = method()
fCurveIneqsMatrix (ZZ) := (n)->(
     --input an integer n and a string
     -- outputs the array with row vectors corresponding to F-inequalities for M_{0,n}
     -- with respect to the sl_2 level 1 conformal block divisor class basis
     -- for N^1(\M_{0,n})_QQ
     nList := toList(1..n);
     

     --generate F-indices, that is, four-tuples {n1, n2, n3, n4} such that
     -- n1 <= .. <= n4 and n1 + ... + n4 = n     
     
     fIndices := select({1,1,1,1}..{n,n,n,n}, p-> (sum p == n) and (p#0<=p#1) and (p#1<=p#2) and (p#2<=p#3));
     
     --Generate F-curves in \M_{0,n}, that is partitions {N1, N2, N3, N4} of {1..n}
     
     fCurves := flatten flatten flatten flatten apply(fIndices, t -> (
	       for N1 in subsets(nList, t_0) list (
		    N1c := listComplement(nList, N1);
		    for N2 in select(subsets(N1c, t_1), N2 -> t_0 != t_1 or (t_0 == t_1 and N1_0 < N2_0)) list (
		    	 --Eliminate duplicates by only 
			 N2c := listComplement(N1c, N2);
			 for N3 in select(subsets(N2c, t_2), N3 -> (t_1 != t_2 or (t_1 == t_2 and N2_0 < N3_0))) list (
			      N3c := listComplement(N2c, N3);
			      for N4 in select(subsets(N3c, t_3), N4 ->  (t_2 != t_3 or (t_2 == t_3 and N3_0 < N4_0) )) list (
				   {N1, N2, N3, N4}
				   ) -- end for over N4
			      ) -- end for over N3
			 ) -- end for over N2
		    ) -- end for over N1
	       ) -- end t->(
	  ); -- end apply	
	  

         --Output inequalities F(N1, N2, N3, N4) in CB coordinates to the file fileName,
	 -- i.e. output \cdot D \geq 0, where [D] = \sum d_I [DD_I]
	 
	 
	 
	fMatrix := toList apply(fCurves, F -> (
		   apply(select (subsets(nList), I-> (#(set I) >= 4 and even (#(set I ))) ), 
	                           I -> (
	        		 -- Calculate the intersection of the F-curve F with the CB-divisor D_I,
	       		 	  --  namely, F \cdot DD_I = 1 if \prod i=1^4 #(F_i \cap I)  odd, 0 else
	       		 	  parity := (#(set I * set F_0 ) * #(set I * set F_1 ) * #(set I * set F_2 ) * #(set I * set F_0 ) );
	       		 	  if odd parity 
	       		 	  then (
				       1
			      	       --fileName << " 1";
			      	       )
				  else ( 0 )
     	       				)--end I->()
				   
     	  )--end apply
		  

	  	   )-- end F-> ()
          
     	  )-- end apply     
     )





--**************************************************************************      
--**************************************************************************

--Calculate the coefficient of D_J in the divisor DD_I
cJinDDI = method()
cJinDDI (Sequence, List) := (J, I) -> (
     --Input a sequence J and a list I, where I indexes the basis element DD_I,
     -- and J indexes the boundary divisor D_J, and
     -- outputs the coefficient of D_J in (the obvious representative of) DD_I
     
     cJ:= 0;
     k := #(set I * set J );
     i := #(set I);
     --if odd i then print "Warning: the cardinality of I must be even."; 
     if even k 
     	  then (
	    cJ = k*(i - k)/(4*(i-1));
	       )--end if then |I*J| even
	  else (
	       cJ =(k-1)*(i - k - 1)/(4*(i-1));
	       );--end else |I*J| odd 
	 cJ
     )


--Generate coefficient c_J of the boundary divisors \D_J in 
-- D = \sum_{I, 4 \leq |I| \leq n, |I| even} d_I D_I = \sum_{J} c_J \D_J

cJinD = method()
cJinD (Sequence, ZZ) := (J, n) -> (
     --Inputs a boundary index and appendable output file out
     -- outputs coefficient c_J of \D_J to the file out
     nList := toList(1..n);
     apply(select (subsets(nList), I-> (#(set I) >= 4 and even (#(set I ))) ), 
	                           I -> (
	        			cJinDDI(J,I)
     	       				)--end I->()
				   
     	  )--end apply
     )--end cJcoeff

end
--Output all coefficients of boundary divisors
apply(subsets(nList), J -> (
	  (
	  if (2 <= #(set(J)) and #(set(J)) < n/2)
	  then (
	       --print " in loop ";
	       cJinD(J, ofile);
	       --cJcoeff(J);
	       )-- end if 2 <= |J| < n/2
	  else if (#(set(J)) == n/2 and isSubset({1},J)) 
	  then (
	       cJinD(J, ofile);
	       )-- end else if |J| == n/2
	  
	  );-- end J-> ()
	  )
     );-- end apply
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
loadPackage "NefM0n"
R = boundaryRing 6;
S = R#Ring
keelSum({{1,3},{2,4}}, R)
tex keelAvgIndices( (1,2,3), {{2,3,4,5}}, R)
tex keelAvgIndices( (1,2,3), {{1,2,4,5}, {1,2,4,6}, {1,2,5,6}, {1,3,4,5}, {1,3,4,6}, {1,3,5,6}, {2,3,4,5}, {2,3,4,6}, {2,3,5,6}},R)

fCurveIneqsLPSOLVE(6, "fIneqs6.txt") 
M = matrix fCurveIneqsMatrix 5

cJinDDI((1,2), {1,2,3,4,5,6,7,8})
v = cJinD((1,2), 8)
w = cJinD((3,4,5,6,7,8), 8)
v - w
