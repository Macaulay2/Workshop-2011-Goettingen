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
Ac123c145 = matrix flatten {entries Ac123,{flatten {{1},c145}} }; 
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
Ac123c145 = matrix flatten {entries Ac123,{flatten {{1/6},-c145}}, {flatten {{1}, c145} }}; 
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
minimalValue(Ac123c145, vector flatten {0, c24})
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



---Next consider -1 <= c456 <= 3/10
c456 = cJinD((4,5,6), 8);
Ac123c456 = matrix flatten {entries Ac123,{flatten {{3/10},-c456}}, {flatten {{1}, c456} }}; 
minimalValue(Ac123c456, vector flatten {0, c456})

c12 = cJinD((1,2), 8);
coeffLinKeelAvgJK((1,2,3), (4,5,6), (1,2), 8)
