loadPackage "Polyhedra"
loadPackage "FourierMotzkin"
load "Polyhedra1.m2"

restart

m = matrix {{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1},{1,-1,-1,0,0},{1,-1,0,-1,0},{1,-1,0,0,-1},{1,0,-1,-1,0},{1,0,-1,0,-1},{1,0,0,-1,-1}}
eff = posHull transpose m
nef = dualCone eff

p = convexHull transpose matrix {{1,0,0,0,0}}

p = p + nef -- Die Zeile kann man weglassen, dann bekommt man eine andere Fehlermeldung.

p1 = convexHull transpose matrix {{0,0,0,0,0},{0,-1,0,0,0}}
p2 = convexHull transpose matrix {{0,0,0,0,0},{0,0,-1,0,0}}
p3 = convexHull transpose matrix {{0,0,0,0,0},{0,0,0,-1,0}}
p4 = convexHull transpose matrix {{0,0,0,0,0},{0,0,0,0,-1}}

r1 = convexHull transpose matrix {{0,0,0,0,0},{1,-1,-1,0,0}}
r2 = convexHull transpose matrix {{0,0,0,0,0},{1,-1,0,-1,0}}
r3 = convexHull transpose matrix {{0,0,0,0,0},{1,-1,0,0,-1}}
r4 = convexHull transpose matrix {{0,0,0,0,0},{1,0,-1,-1,0}}
r5 = convexHull transpose matrix {{0,0,0,0,0},{1,0,-1,0,-1}}
r6 = convexHull transpose matrix {{0,0,0,0,0},{1,0,0,-1,-1}}

p = minkowskiSum(p,p1)
p = minkowskiSum(p,p2)
p = minkowskiSum(p,p3)
p = minkowskiSum(p,p4)

p = minkowskiSum(p,r1)
p = minkowskiSum(p,r2)
p = minkowskiSum(p,r3)
p = minkowskiSum(p,r4)
p = minkowskiSum(p,r5)
p = minkowskiSum(p,r6)

newMinkSum = (P,Q) -> (
     facePairBuilder := (k,P) -> (
	  L := faceBuilder(k,P);
	  HS := halfspaces P;
	  HS = apply(numRows HS#0, i -> ((HS#0)^{i},(HS#1)^{i}));
	  apply(L, l -> (
		    l = (toList l#0,toList l#1);
		    (l,select(HS, hs -> all(l#0, v -> (hs#0)*v - hs#1 == 0) and all(l#1, r -> (hs#0)*r == 0))))));
     uniqueColumns := M -> matrix{(unique apply(numColumns M, i -> M_{i}))};
     n := ambDim P;
     HPP := hyperplanes P;
     HPQ := hyperplanes Q;
     HP := if HPP == (0,0) or HPQ == (0,0) then (map(ZZ^0,ZZ^n,0),map(ZZ^0,ZZ^1,0)) else (
	  k := transpose mingens ker transpose(HPP#0|| -HPQ#0);
	  if k == 0 then (map(ZZ^0,ZZ^n,0),map(ZZ^0,ZZ^1,0)) else (
	       dHPP := numRows HPP#0;
	       (k_{0..dHPP-1} * HPP#0,k*(HPP#1||HPQ#1))));
     d := n - numRows(HP#0);
     if d != n then (
	  if numRows HPP#0 == numRows HP#0 then HPP = (map(ZZ^0,ZZ^n,0),map(ZZ^0,ZZ^1,0)) else (
	       kPP := (transpose mingens ker(HP#0 * transpose HPP#0))_{0..(numRows HPP#0)-1};
	       HPP = (kPP * HPP#0,kPP * HPP#1));
	  if numRows HPQ#0 == numRows HP#0 then HPQ = (map(ZZ^0,ZZ^n,0),map(ZZ^0,ZZ^1,0)) else (
	       kPQ := (transpose mingens ker(HP#0 * transpose HPQ#0))_{0..(numRows HPQ#0)-1};
	       HPQ = (kPQ * HPQ#0,kPQ * HPQ#1)));
     LP := reverse apply(dim P + 1, k -> facePairBuilder(k,P));
     LP = LP | toList(max(0,d-#LP):{});
     LQ := reverse apply(dim Q + 1, k -> facePairBuilder(k,Q));
     LQ = LQ | toList(max(0,d-#LQ):{});
     HS := unique flatten apply(d, i -> (
	       if i == 0 then flatten for f in LQ#(d-1) list (
		    if f#1 == {} then (
			 entP := flatten entries((HPQ#0)*(rays P));
			 maxP := flatten entries((HPQ#0)*(vertices P));
			 if all(entP, e -> e == 0) then {(HPQ#0,matrix{{max maxP}} + HPQ#1),(-HPQ#0,-(matrix{{min maxP}} + HPQ#1))}
			 else if all(entP, e -> e <= 0) then {(HPQ#0,matrix{{max maxP}} + HPQ#1)} 
			 else if all(entP, e -> e >= 0) then {(-HPQ#0,-(matrix{{min maxP}} + HPQ#1))}
			 else continue)
		    else if all(flatten entries((f#1#0#0)*(rays P)), e -> e <= 0) then (
			 mP := max flatten entries((f#1#0#0)*(vertices P));
			 --mP = transpose makePrimitiveMatrix transpose(f#1#0#0|(f#1#0#1 + matrix{{mP}}));
			 {(f#1#0#0,f#1#0#1 + matrix{{mP}})}) else continue)
	       else if i == d-1 then flatten for f in LP#(d-1) list (
		    if f#1 == {} then (
			 entQ := flatten entries((HPP#0)*(rays Q));
			 maxQ := flatten entries((HPP#0)*(vertices Q));
			 if all(entQ, e -> e == 0) then {(HPP#0,matrix{{max maxQ}} + HPP#1),(-HPP#0,-(matrix{{min maxQ}} + HPP#1))}
			 else if all(entQ, e -> e <= 0) then {(HPP#0,matrix{{max maxQ}} + HPP#1)} 
			 else if all(entQ, e -> e >= 0) then {(-HPP#0,-(matrix{{min maxQ}} + HPP#1))}
			 else continue)
		    else if all(flatten entries((f#1#0#0)*(rays Q)), e -> e <= 0) then (
			 mQ := max flatten entries((f#1#0#0)*(vertices Q));
			 --mQ = transpose makePrimitiveMatrix transpose(f#1#0#0|(f#1#0#1 + matrix{{mQ}}));
			 {(f#1#0#0,f#1#0#1 + matrix{{mQ}})}) else continue)
	       else flatten for Pface in LP#i list (
		    for Qface in LQ#(d-i-1) list (
			 PfaceHS := if Pface#1 != {} then (matrix apply(Pface#1, f -> {f#0}) || HPP#0,matrix apply(Pface#1, f -> {f#1}) || HPP#1) else HPP;
			 QfaceHS := if Qface#1 != {} then (matrix apply(Qface#1, f -> {f#0}) || HPQ#0,matrix apply(Qface#1, f -> {f#1}) || HPQ#1) else HPQ;
			 dP := rank PfaceHS#0;
			 dQ := rank QfaceHS#0;
			 PfaceHS = ((PfaceHS#0)^{0..dP-1},(PfaceHS#1)^{0..dP-1});
			 QfaceHS = ((QfaceHS#0)^{0..dQ-1},(QfaceHS#1)^{0..dQ-1});
			 kPQ := transpose mingens ker transpose(PfaceHS#0|| -QfaceHS#0); 
			 if numRows kPQ != 1 then continue else (
			      dPfaceHS := numRows PfaceHS#0;
			      newHS := kPQ_{0..dPfaceHS-1} * PfaceHS#0 | kPQ*(PfaceHS#1||QfaceHS#1);
			      --newHS = transpose makePrimitiveMatrix newHS;
			      newHS = (submatrix'(newHS,{n}),newHS_{n});
			      checkValueP := (newHS#0 *(Pface#0#0#0))_(0,0);
			      checkValueQ := (newHS#0 *(Qface#0#0#0))_(0,0);
			      if all(flatten entries(newHS#0 *(vertices P)), e -> e <= checkValueP) and all(flatten entries(newHS#0 *(vertices Q)), e -> e <= checkValueQ) then (
				   if all(Pface#0#1, r -> (newHS#0 *r)_(0,0) <= 0) and all(Qface#0#1, r -> (newHS*r)_(0,0) <= 0) then newHS else continue) 
			      else if all(flatten entries(newHS#0 *(vertices P)), e -> e >= checkValueP) and all(flatten entries(newHS#0 *(vertices Q)), e -> e >= checkValueQ) then (
				   if all(Pface#0#1, r -> (newHS#0 *r)_(0,0) >= 0) and all(Qface#0#1, r -> (newHS*r)_(0,0) >= 0) then (-(newHS#0),-(newHS#1)) else continue) 
			      else continue)))));
     HS = (matrix apply(HS, e -> {first e}),matrix apply(HS, e -> {last e}));
     V := matrix {unique flatten apply(numColumns vertices P, i -> apply(numColumns vertices Q, j -> (vertices P)_{i}+(vertices Q)_{j}))};
     R := promote(rays P | rays Q,QQ) | map(target V,QQ^1,0);
     V = (map(QQ^1,source V,(i,j)->1) || V) | (map(QQ^1,source R,0) || R);
     HS = sort makePrimitiveMatrix transpose(-(HS#1)|HS#0);
     HS = uniqueColumns HS;
     HP = sort makePrimitiveMatrix transpose(-(HP#1)|HP#0);
     HP = uniqueColumns HP;
     polyhedronBuilder reverse fMReplacement(V,HS,HP))
