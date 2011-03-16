restart
loadPackage "NefM0n"
-- n=7
F = fCurveIneqsMatrix 7;
c123 = cJinD((1,2,3), 7);

zeros = transpose matrix {toList (numRows (matrix F) : 0)};
A = zeros | matrix F;
      
Ac123 = matrix flatten {entries A,{flatten {{1},c123}}, {flatten {{-1},-c123}}};      
          
val = minimalValue(Ac123, vector flatten {0,c123})

--Case i in thesis
c124 = cJinD((1,2,4), 7)
coeffKinKeelAvgJ ((1,2,4), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c124})
--get c124 >= 3, need only c124 >= 0

--Case ii in thesis
c145 = cJinD((1,4,5), 7)
coeffKinKeelAvgJ ((1,4,5), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c145})
--get c145 unbounded, but need c145 >= 1/6, so assume -1 <= c145 <= 1/6, 
-- and try new representative
Ac123c145 = matrix flatten {entries Ac123,{flatten {{1/6},-c145}}, {flatten {{1}, c145} }}; 
minimalValue(Ac123c145, vector flatten {0, c145})
coeffLinKeelAvgJK ((1,2,3), (1,4,5), (2,4), 7)
c24 = cJinD((2,4), 7)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,4), 7)
minimalValue(Ac123c145, vector flatten {0, c24})

c146 = cJinD((1,4,6), 7)
coeffLinKeelAvgJK((1,2,3),(1,4,5), (1,4,6), 7)
minimalValue(Ac123c145, vector flatten {0, c146})

c167 = cJinD((1,6,7), 7);
coeffLinKeelAvgJK((1,2,3),(1,4,5), (1,6,7), 7)
minimalValue(Ac123c145, vector flatten {0, c167})

c245 = cJinD((2,4,5), 7);
coeffLinKeelAvgJK((1,2,3),(1,4,5), (2,4,5), 7)
minimalValue(Ac123c145, vector flatten {0, c245})


--Case iii in thesis
c456 = cJinD((4,5,6), 7)
coeffKinKeelAvgJ ((4,5,6), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c456})
-- get c456 undbounded, but need c456 >= -1/2
--So assume -1 <= c456 <= 0 (to make Case iv easier)
Ac123c456 = matrix flatten {entries Ac123,{flatten {{0},-c456}}, {flatten {{1}, c456} }}; 
	       
c14 = cJinD((1,4), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4), 7)
minimalValue(Ac123c456, vector flatten {0, c14})
--Require c14 >= 2/9, get c14 >= 1

c145 = cJinD((1,4,5), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4,5), 7)
minimalValue(Ac123c456, vector flatten {0, c145})
--Require c145 >= 1/9, get c14 >= 13/3

c147 = cJinD((1,4,7), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4,7), 7)
minimalValue(Ac123c456, vector flatten {0, c147})
--Require c147 >= 2/9, get c147 >= 53/45

c457 = cJinD((4,5,7), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (4,5,7), 7)
minimalValue(Ac123c456, vector flatten {0, c457})
--Require c457 >= -1/3, get c457 >= 2

--Case iii in thesis (fiddle)
c456 = cJinD((4,5,6), 7)
coeffKinKeelAvgJ ((4,5,6), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c456})
-- get c456 undbounded, but need c456 >= -1/2
--So assume -1 <= c456 <= 1/2 (to make Case iv easier???)
Ac123c456 = matrix flatten {entries Ac123,{flatten {{1/2},-c456}}, {flatten {{1}, c456} }}; 
	       
c14 = cJinD((1,4), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4), 7)
minimalValue(Ac123c456, vector flatten {0, c14})
--Require c14 >= 2/9, get c14 >= 1

c145 = cJinD((1,4,5), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4,5), 7)
minimalValue(Ac123c456, vector flatten {0, c145})
--Require c145 >= 1/9, get c14 >= 13/3

c147 = cJinD((1,4,7), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (1,4,7), 7)
minimalValue(Ac123c456, vector flatten {0, c147})
--Require c147 >= 2/9, get c147 >= 53/45

c457 = cJinD((4,5,7), 7)
coeffLinKeelAvgJK((1,2,3),(4,5,6), (4,5,7), 7)
minimalValue(Ac123c456, vector flatten {0, c457})
--Require c457 >= -1/3, get c457 >= 2


--Case iv in thesis
c14 = cJinD((1,4), 7)
coeffKinKeelAvgJ ((1,4), (1,2,3), 7)
minimalValue(Ac123, vector flatten {0,c14})
-- get c14 >= 0, need c14 >= 1/6

--Consider then 0 <= c14 <= 1/6, cxyz >= 0, caxy >= 1/6 for all a \in {1,2,3}
--  and x,y,z \in {4,5,6,7}, and all other cijk >= -1
c124 = cJinD((1,2,4), 7);
c125 = cJinD((1,2,5), 7);
c126 = cJinD((1,2,6), 7);
c127 = cJinD((1,2,7), 7);
c134 = cJinD((1,3,4), 7);
c135 = cJinD((1,3,5), 7);
c136 = cJinD((1,3,6), 7);
c137 = cJinD((1,3,7), 7);
c234 = cJinD((2,3,4), 7);
c235 = cJinD((2,3,5), 7);
c236 = cJinD((2,3,6), 7);
c237 = cJinD((2,3,7), 7);

c456 = cJinD((4,5,6), 7);
c457 = cJinD((4,5,7), 7);
c467 = cJinD((4,6,7), 7);
c567 = cJinD((5,6,7), 7);
c145 = cJinD((1,4,5), 7);
c146 = cJinD((1,4,6), 7);
c147 = cJinD((1,4,7), 7);
c156 = cJinD((1,5,6), 7);
c157 = cJinD((1,5,7), 7);
c167 = cJinD((1,6,7), 7);
c245 = cJinD((2,4,5), 7);
c246 = cJinD((2,4,6), 7);
c247 = cJinD((2,4,7), 7);
c256 = cJinD((2,5,6), 7);
c257 = cJinD((2,5,7), 7);
c267 = cJinD((2,6,7), 7);
c345 = cJinD((3,4,5), 7);
c346 = cJinD((3,4,6), 7);
c347 = cJinD((3,4,7), 7);
c356 = cJinD((3,5,6), 7);
c357 = cJinD((3,5,7), 7);
c367 = cJinD((3,6,7), 7);


Ac123c14 = matrix flatten {entries Ac123, {flatten {{1/6},-c14}}};

--Can also add the following inequalities, but they seem not to be necessary
                                      {flatten {{0}, c456}},
				      {flatten {{0}, c457}},
				      {flatten {{0}, c467}},
				      {flatten {{0}, c567}},
				      {flatten {{-1/6}, c145}},
				      {flatten {{-1/6}, c146}},
				      {flatten {{-1/6}, c147}},
				      {flatten {{-1/6}, c156}},
				      {flatten {{-1/6}, c157}},
				      {flatten {{-1/6}, c167}},
				      {flatten {{-1/6}, c245}},
				      {flatten {{-1/6}, c246}},
				      {flatten {{-1/6}, c247}},
				      {flatten {{-1/6}, c256}},
				      {flatten {{-1/6}, c257}},
				      {flatten {{-1/6}, c267}},
				      {flatten {{-1/6}, c345}},
				      {flatten {{-1/6}, c346}},
				      {flatten {{-1/6}, c347}},
				      {flatten {{-1/6}, c356}},
				      {flatten {{-1/6}, c357}},
				      {flatten {{-1/6}, c367}},
				      
				      {flatten {{1}, c124}},
				      {flatten {{1}, c125}},
				      {flatten {{1}, c126}},
				      {flatten {{1}, c127}}, 
				      {flatten {{1}, c134}},
				      {flatten {{1}, c135}},
				      {flatten {{1}, c136}},
				      {flatten {{1}, c137}}, 
				      {flatten {{1}, c234}},
				      {flatten {{1}, c235}},
				      {flatten {{1}, c236}},
				      {flatten {{1}, c237}}	
					 };

coeffLinKeelAvgJnotK((1,2,3), (1,4), (1,2,4), 7)
minimalValue(Ac123c14, vector flatten {0, c124})
--get >= 3, as before, need >= -1/8

coeffLinKeelAvgJnotK((1,2,3), (1,4), (1,2,5), 7)
minimalValue(Ac123c14, vector flatten {0, c125})
--get >= 16/3, better than before, need >= 1/8

coeffLinKeelAvgJnotK((1,2,3), (1,4), (1,4,5), 7)
minimalValue(Ac123c14, vector flatten {0, c145})
--get >= 257/198, as in thesis, need >= 1/12

coeffLinKeelAvgJnotK((1,2,3), (1,4), (2,4,5), 7)
minimalValue(Ac123c14, vector flatten {0, c245})
--get >= 41/36, as in thesis, need >=1/4

coeffLinKeelAvgJnotK((1,2,3), (1,4), (1,5), 7)
c15 = cJinD((1,5), 7);
minimalValue(Ac123c14, vector flatten {0, c15})
--get >= 7/6, as in thesis, need >=1/6
