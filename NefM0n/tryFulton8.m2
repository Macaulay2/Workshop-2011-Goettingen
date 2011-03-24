restart
loadPackage "NefM0n"
-- n=8
F = fCurveIneqsMatrix 8;
zeros = transpose matrix {toList (numRows (matrix F) : 0)};
A = zeros | matrix F;

--cij
c12 = cJinD((1,2), 8);
val = minimalValue(A, vector flatten {0, c12})
--obtain c12 >= 0
      
      
--cijk
c123 = cJinD((1,2,3), 8);
--val = minimalValue(A, vector flatten {0, c123})
--Ac123 = matrix flatten {entries A,{flatten {{1},c123}}};      
          
val = minimalValue(Ac123, vector flatten {0,c123})
--obtain c123 unbounded below

-- Assume c123 the most negative of ALL coefficients (including cijkl), set to -1
Ac123 = matrix flatten {entries A,{flatten {{1},c123}}, {flatten{{-1}, -c123}} }; 
	       
--Determine coefficients of other boundary divisors in average for \D_{123}
coeffKinKeelAvgJ ((1,2), (1,2,3), 8)
--get coeff \D_{12} = -1/3, nothing more to do since c12 >= 0

coeffKinKeelAvgJ ((4,5), (1,2,3), 8)
--get coeff \D_{45} = -1/10, done

coeffKinKeelAvgJ ((1,4), (1,2,3), 8)
--get coeff \D_{14} = 2/15
c14 = cJinD((1,4), 8);
minimalValue(Ac123, vector flatten {0,c14})
-- obtain c14 >= 0, either input other inequalities from c123 being most negative, or new average

coeffKinKeelAvgJ ((1,2,4), (1,2,3), 8)
--get coeff \D_{124} = -1/15
c124 = cJinD((1,2,4), 8);
minimalValue(Ac123, vector flatten {0,c124})
--get c124 >= 3 (this looks familiar)

coeffKinKeelAvgJ ((1,4,5), (1,2,3), 8)
--get coeff \D_{145} = 1/6
c145 = cJinD((1,4,5), 8);
Ac123c145 = matrix flatten {entries M,{flatten {{1},c145}} }; 
minimalValue(Ac123c145, vector flatten {0,c145})
--get c145 unbounded below

coeffKinKeelAvgJ ((4,5,6), (1,2,3), 8)
--get coeff \D_{456} = 1/6
c456 = cJinD((4,5,6), 8);
Ac123c456 = matrix flatten {entries Ac123, {flatten {{1},c456}} };
minimalValue(Ac123c456, vector flatten {0,c456})
--get c456 >= -1 (by assumption of c123 being most negative)

-- cijkl
coeffKinKeelAvgJ((1,2,3,4), (1,2,3), 8)
--get coeff \D_{1234} = -3/5
c1234 = cJinD((1,2,3,4), 8);
Ac123c1234 = matrix flatten {entries Ac123, {flatten {{1},c1234}} };
minimalValue(Ac123c1234, vector flatten {0, c1234})
--get c1234 >= -1

coeffKinKeelAvgJ((1,2,4,5), (1,2,3), 8)
--get coeff \D_{1245} = 1/10
c1245 = cJinD((1,2,4,5), 8);
Ac123c1245 = matrix flatten {entries Ac123, {flatten {{1},c1245}} };
minimalValue(Ac123c1245, vector flatten {0, c1245})
--get c1245 >= -1

coeffKinKeelAvgJ((1,4,5,6), (1,2,3), 8)
--get coeff \D_{1234} = 1/10
c1456 = cJinD((1,4,5,6), 8);
Ac123c1456 = matrix flatten {entries Ac123, {flatten {{1},c1456}} };
minimalValue(Ac123c1456, vector flatten {0, c1456})
--get c1456 >= -1

coeffKinKeelAvgJ((4,5,6,7), (1,2,3), 8)
--get coeff \D_{4567} = 1/10
c4567 = cJinD((4,5,6,7), 8);
Ac123c4567 = matrix flatten {entries Ac123, {flatten {{1},c4567}} };
minimalValue(Ac123c4567, vector flatten {0, c4567})
--get c4567 >= -1

--######################
--To cases of inequalities failing
--######################
--Assume -1 <= c145 <= 1/6
c145 = cJinD((1,4,5), 8);
Ac123c145 = matrix flatten {entries M,{flatten {{1/6},-c145}}, {flatten {{1}, c145} }}; 
minimalValue(Ac123c145, vector flatten {0, c145})

c12 = cJinD((1,2), 8)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (1,2), 8)
-- coeff of \D_12 = 0, done

coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,3), 8)
-- coeff of \D_23 = -1, done

coeffLinKeelAvgJK((1,2,3),(1,4,5), (4,5), 8)
-- coeff of \D_45 = -1, done


c14 = cJinD((1,4), 8)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (1,4), 8)
minimalValue(Ac123c145, vector flatten {0, c14})
--coeff od \D_14 = 0, done

c24 = cJinD((2,4), 8)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,4), 8)
--coeff of \D_24 = 1/2
minimalValue(Ac123c145, vector flatten {0, c24})
--obtain c_24 >= 0

c25 = cJinD((2,5), 8)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,5), 8)
--coeff of \D_25 = 1/2
minimalValue(Ac123c145, vector flatten {0, c25})
--obtain c_25 >= 0

c67 = cJinD((6,7), 8)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (6,7), 8)
--coeff od \D_67 = 0, done

coeffLinKeelAvgJK((1,2,3),(1,4,5), (1,2,4), 8)
-- coeff of c124 = 1/2
c124 = cJinD((1,2,4), 8);
minimalValue(Ac123c145, vector flatten {0, c124})
-- obtain c124 >= -1/18

coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,3,4), 8)
-- coeff of c234 = 0
c234 = cJinD((2,3,4), 8);
minimalValue(Ac123c145, vector flatten {0, c234})
-- obtain c234 >= -1


--Subcase of -1 <= c145 <= 1/6: assume additionally that 0 <= c24 <= 1/2
Ac123c145c24 = matrix flatten {entries Ac123c145, {flatten {{1/2},-c24}}}; 

c25 = cJinD((2,5), 8);
minimalValue(Ac123c145c24, vector flatten {0, c25})
--need c25 >= 1, get c25 >= 0

c125 = cJinD((1,2,5), 8);
minimalValue(Ac123c145c24, vector flatten {0, c125})
--need c125 >= 1, get c125 >= 3, as before

c256 = cJinD((2,5,6), 8);
minimalValue(Ac123c145c24, vector flatten {0, c256})
--need c256 >= 1, get c256 >= 91/180

c1256 = cJinD((1,2,5,6), 8);
minimalValue(Ac123c145c24, vector flatten {0, c1256})
--need c1256 >= 1, get >= 2381/765

c34 = cJinD((3,4), 8);
minimalValue(Ac123c145c24, vector flatten {0, c34})
--need c34 >= 1, get >= 0 

keelAvgJK((1,2,3), (1,4,5), 8)

createMat123 = method()
createMat123(ZZ) := n -> (
     F := fCurveIneqsMatrix n;
     zeros := transpose matrix {toList (numRows (matrix F) : 0)};
     A := zeros | matrix F;
     c123 := cJinD((1,2,3), n);
     A = matrix flatten {entries A,{flatten {{1},c123}}, {flatten{{-1}, -c123}} };
     nList := toList(1..n);
     bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );
     bndIndices1 = apply(bndIndices, J -> cJinD(flatten sequence J, n));
     bndIndices1 = apply(bndIndices1, cJ -> {flatten {{1},cJ}});
     B := matrix flatten bndIndices1;
     M := A || B
     
     --apply(bndIndices, J -> {J,minimalValue(M, vector flatten{0, cJinD(flatten sequence J, n)})})
     )



M = createMat123(8)
minimalValue(M, vector flatten {0, c14})

J = (1,2,3)
isSubset(J,nList)
bndIndices(8)
nList := toList(1..8);
n = 8
bndIndices = select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );
bndIndices
isSubset(bndIndices#0,nList)
flatten sequence {1,2,3}
matrix flatten bndIndices

avgLists = method()
avgLists(List, List, ZZ) := (L, J, n) -> (
     correctSets := (i, A, B, nList) -> (
	  jList := subsets(listComplement(nList,flatten sequence unique flatten {toList A, toList B}),2);
	  apply(jList, j-> { i, j})
	  );
     nList := toList(1..n);
     bndIndices := select (subsets(nList), j -> ( (#j >= 2 and #j < floor n/2) or (#j == floor n/2 and isSubset({1},j) ) ) );
     avg:= toList (#bndIndices : 0);
     twotuples := flatten apply(subsets(nList,2), i-> apply(subsets(listComplement(nList, i),2), j-> (i,j)));
     --<< twotuples << endl;
     ans := select(twotuples, t -> (
	  all(L, l -> (#(set t#0 * set l) == 2 and #(set t#1 * set l)==0) or  (#(set t#0 * set l) == 0 and #(set t#1 * set l)==2))
	  
	  ));
     bjl:= sum(apply(J, j->bndJList(sequence j,n)));
     counter :=0;
     for t in ans do (
	  i := t#0;
	  j := t#1;
	  tw1 := ({i#0,j#0},{i#1,j#1});
	  tw2 := ({i#0,j#1},{i#1,j#0});
	  if all(J, l -> not ((#(set tw1#0 * set l) == 2 and #(set tw1#1 * set l)==0) or  (#(set tw1#0 * set l) == 0 and #(set tw1#1 * set l)==2))) then (
	       avg = avg - keelSumList(toList t, n) + keelSumList(toList tw1, n) + bjl;
	       counter = counter+1;
	       );
	  if all(J, l -> not ((#(set tw2#0 * set l) == 2 and #(set tw2#1 * set l)==0) or  (#(set tw2#0 * set l) == 0 and #(set tw2#1 * set l)==2))) then (
	       avg = avg - keelSumList(toList t, n) + keelSumList(toList tw2, n) + bjl;
	       counter = counter+1;
	       );
	  );
     avg/counter
           
     )

L = {{1,2,3},{1,3,5}}
avgLists(L,{{6,8}},8)

