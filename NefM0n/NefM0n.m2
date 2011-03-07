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
export {listComplement, 
        keelSum, 
	keelSumList, 
	keelAvg, 
	keelAvgList, 
	bndJList,
	keelAvgIndices,
	coeffKinKeelAvgJ, 
	boundaryRing, 
	fCurveIneqsLPSOLVE, 
	fCurveIneqsMatrix, 
	cJinDDI, 
	cJinD, 
	m1,
	minimalValue}

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

--listComplement = method()
--listComplement (List, List) := (L, K) -> toSequence sort toList(set L - set K)

keelSum = method()
keelSum (List, BoundaryRing) := (K,R)-> (
     --Input a split four-tuple K = {{i,j}, {k,l}}
     -- and output the sum
     --  \sum_{{i,j} \subseteq J, {k,l} subseteq J^c} D_J
     
     if #(set K_0 * set K_1) != 0 then error "expected pairs in the list to be disjoint";
     bndsum:= 0;
     apply(R.M0nIndices, j-> (
      	       if (isSubset(K_0, set j ) and isSubset( K_1, set R.M0nComplement j) )
	       then bndsum = bndsum + (R#Variables)#j;
	       )
       	  );
     bndsum
     );

--**************************************************************************      
--**************************************************************************
keelAvg = method()
keelAvg (Sequence, BoundaryRing) := (J, R) -> (
     --Input sequence J (index of boundary divisor D_J) and Boundary Ring R
     -- and output average of numerical equivalence class of D_J
     -- over all Keel relations involving D_J
     avg:= 0;
     counter:= 0; --should be 0
     apply(toList subsets(J, 2), i-> 
     	  --loop over subsets of cardinality two in J
     	  apply(toList subsets(R.M0nComplement J, 2), j->
	       --loop over subsets of cardinality two in J^c
	       (
		    counter = counter + 2;
		    avg = avg - 2*keelSum({i,j}, R) 
		          + keelSum({{i_0, j_0}, {i_1, j_1}}, R)
		    	  + keelSum({{i_0, j_1}, {i_1, j_0}}, R)
		    	  + 2*(R#Variables)#J;
	     		  )
		     )
		);

	   avg/counter
	   )
            
--**************************************************************************      
--**************************************************************************
keelAvgIndices = method()
keelAvgIndices (Sequence, List, BoundaryRing) := (J, IList, R) -> (
     --Input a sequence J (i.e. a boundary index J), 
     -- a list of lists IList = {IList_x} (with each IList_x a four-tuple),
     -- and the BoundaryRing R,
     -- and output average of numerical equivalence class of D_J
     -- over all Keel relations I_x 
 
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
	   return (avg/counter)
	   )
      
      
--**************************************************************************      
--**************************************************************************

keelSumList = method()
keelSumList (List, ZZ) := (K,n)-> (
     --Input a split four-tuple K = {{i,j}, {k,l}}
     -- and output the sum
     --  \sum_{{i,j} \subseteq J, {k,l} subseteq J^c} D_J
     -- as a list indexed by D_J
     
     nList := toList(1..n);
     if #(set K_0 * set K_1) != 0 then error "expected pairs in the list to be disjoint";
     
     bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );
     apply(bndIndices, j-> (
      	     if ( (isSubset(K_0, set j ) and isSubset( K_1, set listComplement(nList, j)) )
		  or (isSubset(K_0, set listComplement(nList,j) ) and isSubset( K_1, set j)) )
	     then 1
	     else 0
	       )
       	  )  
     )

--**************************************************************************      
--**************************************************************************
bndJList = method()
bndJList (Sequence, ZZ) := (J,n) -> (
     --Inputs sequence J and integer n, where J is the index of a boundary divisor D_J, n is from \M_{0,n}, and
     -- outputs a list giving the coordinate of \D_J in list indexed by all boundary divisors
      nList := toList(1..n);
      bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );
      apply(bndIndices, j -> if j==toList J then 1 else 0)
     
     )

--**************************************************************************      
--**************************************************************************
keelAvgList = method()
keelAvgList (Sequence, ZZ) := (J, n) -> (
     --Input sequence J (index of boundary divisor D_J) and Boundary Ring R
     -- and output average of numerical equivalence class of D_J
     -- over all Keel relations involving D_J
     nList := toList(1..n);
     if (#J > floor(n/2) or (#J == floor(n/2) and not isSubset({1},J)) ) then J = listComplement(nList, J);
        
     bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );	
     avg:= apply(bndIndices, i->0);
     counter:= 0; --should be 0
     apply(toList subsets(J, 2), i-> 
     	  --loop over subsets of cardinality two in J
     	  apply(toList subsets(listComplement(nList, J), 2), j->
	       --loop over subsets of cardinality two in J^c
	       (
		    counter = counter + 2;
		    avg = avg - 2*keelSumList({i,j}, n) 
		          + keelSumList({{i_0, j_0}, {i_1, j_1}}, n)
		    	  + keelSumList({{i_0, j_1}, {i_1, j_0}}, n)
		    	  + 2*bndJList(J,n);
	     		  )
		     )
		);

	   avg/counter
	   )
--**************************************************************************      
--**************************************************************************
coeffKinKeelAvgJ = method()
coeffKinKeelAvgJ (Sequence, Sequence, ZZ) := (K, J, n) -> (
     --Inputs two sequences J, K, where J gives the index of the 
     -- boundary divisors D_J averaged over the Keel relations,
     -- namely in keelAvg(J,n), and 
     -- K gives the index of the boundary divisor whose coefficient
     -- we seek in the average of D_J;
     --Outputs the coefficient of D_K in the average D_J = (...)
     avgJ := keelAvgList(J,n);
     nList := toList(1..n);
     k:= 0;
     
     
     bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );	
     for j from 0 to #bndIndices - 1 do (if toList K == bndIndices_j then k = j );
     avgJ_k
     ) 

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

--**************************************************************************      
--**************************************************************************

m1 = method();
m1(List, List) := (F, c) -> (
     zeros := transpose matrix {toList (numRows (matrix F) : 0)};
     A := zeros | matrix F;
     val := minimalValue(A, vector flatten {0,c});
     << val << endl;
     if val == "-inf" then (
	  --todo
	  matrix flatten {entries A,{flatten {{1},c}}, {flatten {{-1},-c}}}
	  )
     else (
	  value val
	  )
     )

--**************************************************************************      
--**************************************************************************

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

--**************************************************************************      
--**************************************************************************

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

--**************************************************************************      
--**************************************************************************

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
	 
	 
	selection := select(subsets(nList), I-> (#I >=4) and even (#I));
	<< "selection: " << #selection << endl;
	fMatrix := toList apply(fCurves, F -> (
		   apply(selection, 
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
     --Inputs a boundary index and integer
     -- outputs coefficient c_J of \D_J as a vector
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
R = boundaryRing 10;
S = R#Ring
tex keelAvg((1,2,3), R)

print keelSum({{1,3},{2,4}}, R)
keelSumList({{1,2},{4,5}},6)
bndJList((1,2),6)

keelAvgList ((1,2,3), 8)

tex keelAvgIndices( (1,2,3), {{2,3,4,5}}, R)
tex keelAvgIndices( (1,2,3), {{1,2,4,5}, {1,2,4,6}, {1,2,5,6}, {1,3,4,5}, {1,3,4,6}, {1,3,5,6}, {2,3,4,5}, {2,3,4,6}, {2,3,5,6}},R)

fCurveIneqsLPSOLVE(6, "fIneqs6.txt") 
M = fCurveIneqsMatrix 6;
Mmat = matrix M


cJinDDI((1,2), {1,2,3,4,5,6,7,8})
v = cJinD((1,2,3), 6)
#v

v - w

M123 = m1(M,v)
M123array = entries M123;



bndIndices = select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );	
     avg= apply(bndIndices, i->0)
avg = {};
i = {1,2}
j = {3,4}
J = (1,2,6)

keelSumList({i,j},n)
J = (1,2,3)
K = (1,2,3,4)
coeffKinKeelAvgJ (K, J, 8)
keelAvgList((1,2,3), 6)

n=6
nList = toList(1..n);
avgJ = keelAvgList((1,2,3),n)
keelAvgList((4,5,6), n)
coeff= 0;
   
     avgJ#0
     
     bndIndices = select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );	
     for j from 0 to #bndIndices - 1 do (if toList K == bndIndices_j then k = j )
k
     coeff
     
     --OK, now fiddle with proof of Fulton's conjecture
 
--n = 5
F = fCurveIneqsMatrix 5
c = cJinD((1,2), 5)
--Code from Lars's function m1
zeros = transpose matrix {toList (numRows (matrix F) : 0)}
A = zeros | matrix F
vector flatten {0,c}     
val = minimalValue(A, vector flatten {0,c})
     
     
     --n = 6
 F = fCurveIneqsMatrix 6
c = cJinD((1,2,3), 6)
--Code from Lars's function m1
     zeros = transpose matrix {toList (numRows (matrix F) : 0)}
     A = zeros | matrix F
     
     val = minimalValue(A, vector flatten {0,c})
     
     
Ac123 = matrix flatten {entries A,{flatten {{1},c}}, {flatten {{-1},-c}}};
c14 = cJinD((1,4), 6)    
coeffKinKeelAvgJ ((1,4), (1,2,3), 6)
minimalValue(Ac123, vector flatten {0,c14})

c125 = cJinD((1,2,5), 6)
coeffKinKeelAvgJ((1,2,5), (1,2,3),6)
minimalValue(Ac123, vector flatten {0,c125})


-- n=7
F = fCurveIneqsMatrix 7;
c123 = cJinD((1,2,3), 7);

zeros = transpose matrix {toList (numRows (matrix F) : 0)};
A = zeros | matrix F;
      
Ac123 = matrix flatten {entries A,{flatten {{1},c}}, {flatten {{-1},-c}}};      
          
val = minimalValue(A, vector flatten {0,c})

c124 = cJinD((1,2,4), 7)
coeffKinKeelAvgJ ((1,2,4), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c124})
--get c124 >= 3, need only c124 >= 0


c145 = cJinD((1,4,), 7)
coeffKinKeelAvgJ ((1,4,5), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c145})
--get c145 >= 0, but need c145 >= 1/6

c456 = cJinD((4,5,6), 7)
coeffKinKeelAvgJ ((4,5,6), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c456})
-- get c456 undbounded, but need c456 >= -1/2

c14 = cJinD((1,4), 7)
coeffKinKeelAvgJ ((1,4), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c14})
-- get c14 >= 0, need only c14 >= 1/6

--Consider then -1 <= c145 <= 1/6
Ac123c145 = matrix flatten {entries A,{flatten {{1},c}}, {flatten {{-1},-c}}};>>>>>>> .r13079
