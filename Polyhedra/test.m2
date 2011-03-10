loadPackage "Polyhedra"

restart
fixme = false
loadPackage "FourierMotzkin"
load "Polyhedra1.m2"

A = hyperplanes hypercube 2

C = posHull A

B = map(QQ^2,QQ^4,0)
c1 = convexHull (A||B)
c2 = convexHull (B||A)

P = minkowskiSum(c1,c2)
dim P
mixedVolume{P,P,P,P}

A1 = vertices P
B1 = map(ZZ^2,ZZ^16,0)
c11 = convexHull ( A1||B1)
c12 = convexHull (B1||A1)
Q = minkowskiSum(c11,c12)

m = matrix {{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1},{1,-1,-1,0,0},{1,-1,0,-1,0},{1,-1,0,0,-1},{1,0,-1,-1,0},{1,0,-1,0,-1},{1,0,0,-1,-1}}
eff = posHull transpose m
nef = dualCone eff

p = convexHull transpose matrix {{1,0,0,0,0}}


apply(hyperplanes p, m-> m||-m)
--p = p + nef -- Die Zeile kann man weglavertex condition polytope halfspaces hyperplanes rankssen, dann bekommt man eine andere Fehlermeldung.

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

--if R == {} then R = map(ZZ^(numRows LS),ZZ^0,0) else R = sort matrix {unique apply(R, makePrimitiveMatrix)};
   
restart
fixme = false
loadPackage "FourierMotzkin"
load "Polyhedra1.m2"
p = convexHull transpose matrix {{1,0,0,0,0}};
p1 = convexHull transpose matrix {{0,0,0,0,0},{0,-1,0,0,0}};
p2 = convexHull transpose matrix {{0,0,0,0,0},{0,0,-1,0,0}};
p3 = convexHull transpose matrix {{0,0,0,0,0},{0,0,0,-1,0}};
p4 = convexHull transpose matrix {{0,0,0,0,0},{0,0,0,0,-1}};

p = minkowskiSum(p,p1);
numColumns vertices p
p = minkowskiSum(p,p2);
numColumns vertices p
p = minkowskiSum(p,p3);
numColumns vertices p
p = minkowskiSum(p,p4);
numColumns vertices p
p = minkowskiSum(p,r1)
fixme = true
p = minkowskiSum(p,r2)
vertices p
p = minkowskiSum(p,r3)
p = minkowskiSum(p,r4)
p = minkowskiSum(p,r5)
p = minkowskiSum(p,r6)

restart
installPackage "Polyhedra2"
check "Polyhedra2"

R = QQ[a]
S = R[x]
f = a*x
coefficients(f)
