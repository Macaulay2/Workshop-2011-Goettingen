
-- -*- coding: utf-8 -*-
newPackage(
	"KustinMiller",
    	Version => "0.5", 
    	Date => "August 19, 2010",
    	Authors => {{Name => "Janko Boehm", 
		  Email => "boehm@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/jb/"},
                  {Name => "Stavros Papadakis", 
		  Email => "papadak@math.ist.utl.pt", 
		  HomePage => "http://www.math.ist.utl.pt/~papadak/"}
                   },
    	Headline => "Unprojection and the Kustin-Miller complex construction",
    	DebuggingMode => true
        )


-- Install this package with the Macaulay2 command:

-- installPackage "KustinMiller"

-- For more installation instructions see documentation key
-- KustinMiller below

-- This package has been written and tested with M2 version 1.3.1


--------------------------------------------------------------------

-- the commands available to the user:

export({"Complex","complex","facets","faces","fvector","dimension","simplexRing","Face","vertices","faceIdeal","face","isSubface","substituteFace","substituteComplex","isFace"})

export({"idealToComplex","complexToIdeal"})

export({"stellarSubdivision","link","subRing"})

export("delta")

export({"kustinMillerComplex","differentials"})

export({"shiftComplex","dualComplex","unprojectionHomomorphism","isExact","verbose"})

-- export("koszulComplexFromParts","buchsbaumEisenbudCyclicRes"})



-------------------------------------------------------------------------------------------
-- simplicial complexes and Stanley-Reisner rings

-------------------------------------------------------
-- The class of all complexes

Complex = new Type of List

Complex#{Standard,AfterPrint} = m -> (
   S:=symbol S;
   if (toList m)!={face {}} then (
      S= "complex with "|#m|" facets on the vertices "|net(face((entries(vars(simplexRing m)))#0))
   ) else (
      S= "empty complex"
   );
      << endl;
      << concatenate(interpreterDepth:"o") << lineNumber << " : "
      <<S;
      << endl;)

---------------------------------------------------------
-- create a complex

complex=method()
complex(List):=(L)->(new Complex from L)

----------------------------------------------------------
-- compare two complexes

Complex == Complex :=(C1,C2)->(
if not(simplexRing C1 === simplexRing C2) then return(false);
return(compareFacesj(facets C1,facets C2))
)


compareFacesj=method()
compareFacesj(List,List):=(L1,L2)->(
anz:=0;
tst:=true;
j:=0;
while j<#L1 and tst==true do (
  anz=0;
  for jj from 0 to #L2-1 do (
    if L2#jj == L1#j then anz=anz+1;
  );
  if anz!=1 then tst=false;
j=j+1);
tst)


----------------------------------------------------------
-- the underlying polynomial ring of a simplicial complex

simplexRing=method()
simplexRing Complex := C -> ring C#0#0
dimension=method()
dimension Complex := C->-1+max apply(C,j->#j)
facets=method()
facets Complex := C->(
L:=toList C;
L1:={};
q:=0;
while q<#L do (
  L1=append(L1,new Face from L#q);
q=q+1);
L1)

Face = new Type of List

vertices=method()
vertices Face := F -> toList F

net Face := (f)-> (
v:=vertices(f);
if #v==0 then return(net({}));
horizontalJoin(apply(v,j->net(j)|net(" "))))


Face#{Standard,AfterPrint} = m -> (
      << endl;
      << concatenate(interpreterDepth:"o") << lineNumber << " : "
      << "face with "|#vertices(m)|" vertices"
      << endl;)


dimension Face := F->-1+#(vertices F)
simplexRing Face :=F->(
r:=ring F#0;
for j from 1 to #F-1 do (
  if ring(F#j)=!=r then error("Not all vertices in the same ring");
);
r)

faceIdeal=method()
faceIdeal Face := F->(
R:=simplexRing  F;
ideal listMinus((entries vars R)#0,vertices F)
);

face=method()
face(List):= (L)-> new Face from L

Face == Face := (F,G)->(
if #(vertices F)!=(#(vertices G)) then return(false);
if set vertices F === set vertices G then return(true);
R1:=ring F#0;
R2:=ring G#0;
if set vertices (substituteFace(F,R2)) === set vertices G then return(true);
if set vertices (substituteFace(G,R1)) === set vertices F then return(true);
false)



listMinus=method()
listMinus(List,List):=(L1,L2)->(
L3:={};
q:=0;
while q<#L1 do (
  if member(L1#q,L2)==false then L3=append(L3,L1#q);
q=q+1);
L3)


idealToComplex=method()
idealToComplex(Ideal) := (I) ->   (
      R:=ring I;
      n:=rank source vars R;
      helptempL := decompose I ;
      outdata := {} ;
      i:=0;j:=0;
      for i from 0 to (# helptempL -1)  do   (
          small := {};
          for j from 1 to n do  
              if (isSubset (ideal (R_(j-1)), helptempL_i) == false) then small = append(small, {R_(j-1)});
          outdata  =  append (outdata, new Face from flatten small)  );
      complex outdata    )

idealToComplex(MonomialIdeal) := (I) ->   (idealToComplex ideal I)


complexToIdeal=method()
complexToIdeal(Complex):= (D0) ->   (
     R:=simplexRing D0;
     D:=toList D0;
     n:=rank source vars R;
     outdata := {};
     for i from 0 to  (#D -1)  do   (
         small := ideal(0_R);
         for j from 1 to n do 
             if  (isSubset ({R_(j-1)}, D_i) == false) then (small = small + ideal(R_(j-1)));
         outdata = append( outdata, small)
      );
      intersect outdata  )

faces=method()
faces(Complex):=(C)->(
fc:=facets C;
R:=simplexRing C;
n:=rank source vars R;
L:={};
L1:=set {};
for j from 0 to n do (
  L1=set {};
  for jj from 0 to #fc-1 do (
    L1=L1 +  set subsets(fc#jj,j);
  );
  L1=toList L1;
  L1=apply(L1,a->new Face from a);
  L=append(L,L1);
);
L)

faces(Complex,ZZ):=(C,d)->(
fc:=facets C;
R:=simplexRing C;
n:=rank source vars R;
L1:=set {};
j:=d+1;
  L1=set {};
  for jj from 0 to #fc-1 do (
    L1=L1 +  set subsets(fc#jj,j);
  );
  L1=toList L1;
  L1=apply(L1,a->new Face from a);
L1)


fvector=method()
fvector(Complex):=(C)->(
fc:=faces C;
apply(fc,j->#j))

isSubface=method()
isSubface(Face,Face):=(F,G)->(
v1:=set vertices F;
v2:=set vertices G;
isSubset(v1,v2))

isFace=method()
isFace(Face,Complex):=(F,C)->(
tst:=false;
q:=0;
while q<#C and tst==false do (
  if isSubface(F,C#q)==true then tst=true;
q=q+1);
tst)

substituteFace=method()
substituteFace(Face,PolynomialRing):=(F,R)->(
v:=vertices(F);
L:={};
j:=0;
for j from 0 to #v-1 do L=append(L,sub(v#j,R));
new Face from L)

substituteComplex=method()
substituteComplex(Complex,PolynomialRing):=(C,R)->(
apply(C,F->substituteFace(F,R)))


-------------------------------------------------------------------------


positionRing=method()
positionRing(RingElement):=(m)->(
v:=(entries vars ring m)#0;
for q from 0 to #v-1 do (
if v#q==m then return(q);
);
);

--R=QQ[x_1..x_10]
--positionRing(x_1)

isContigous=method()
isContigous(List):=(X)->(
if X=={} then return(false);
X1:=sort(X);
p2:=X1#(#X1-1);
p1:=X1#0;
if abs(positionRing(p2)-positionRing(p1))==#X1-1 then return(true);
false);

{*
isContigous({x_2,x_3,x_6,x_4,x_5,x_8,x_7})
isContigous({x_2,x_3,x_6,x_4,x_5,x_8,x_7})
isContigous({x_1,x_2,x_5,x_3})
*}


contigousSubsets=method()
contigousSubsets(List):=(W)->(
select(subsets(W),isContigous))

{*
contigousSubsets({x_4,x_5})
contigousSubsets({x_3,x_4})
contigousSubsets({x_1,x_2,x_3})
contigousSubsets({x_2,x_3,x_4})
contigousSubsets({x_1,x_2,x_4})
*}


maximalElements=method()
maximalElements(List):=(L)->(
L2:=L;
L1:=maxmon(L2);
while #L1<#L2 do (
  L2=L1;
  L1=maxmon(L2);
);
L1)

--maximalElements({{x_1,x_2,x_3},{x_1,x_2},{x_3,x_4},{x_2,x_3,x_4,x_7,x_8}})

maxmon=method()
maxmon(List):=(L)->(
rm:=-1;
j:=0;
jj:=0;
while j<#L and rm==-1 do (
  jj=0;
  while jj<#L and rm==-1 do (
    if j!=jj and isSubset(set L#j,set L#jj)==true then rm=j;
  jj=jj+1);
j=j+1);
--print(rm);
L1:={};
j=0;
while j<#L do (
  if j!=rm then L1=append(L1,L#j);
j=j+1);
L1);

--maxmon({{x_1,x_2,x_3},{x_1,x_2},{x_3,x_4},{x_2,x_3,x_4,x_7,x_8}})

maximalContigousSubsets=method()
maximalContigousSubsets(List):=(L)->(
maximalElements(contigousSubsets(L)))

{*
maximalContigousSubsets({x_1,x_2,x_4})
maximalContigousSubsets({x_1,x_2,x_4,x_5,x_7,x_8,x_9})
*}


isEndset=method()
isEndset(List):=(L)->(
v:=(entries vars ring L#0)#0;
if isSubset({v#0},L)==true or isSubset({v#(#v-1)},L)==true then return(true);
false)

{*
isEndset({x_1,x_2})
isEndset({x_1,x_3})
isEndset({x_2,x_3})
*}


removeEndsets=method()
removeEndsets(List):=(L)->(
L1:={};
j:=0;
for j from 0 to #L-1 do (
  if isEndset(L#j)==false then L1=append(L1,L#j);
);
L1);

{*
removeEndsets({{x_1,x_2},{x_3,x_4}})
removeEndsets({{x_1,x_3},{x_7,x_8}})

removeEndsets(maximalContigousSubsets({x_1,x_2,x_4}))
removeEndsets(maximalContigousSubsets({x_1,x_2,x_4,x_5,x_7,x_8}))
*}

oddContigousNonEndsets=method()
oddContigousNonEndsets(List):=(L)->(
L2:={};
j:=0;
L1:=removeEndsets(maximalContigousSubsets(L));
for j from 0 to #L1-1 do (
  if odd(#(L1#j))==true then L2=append(L2,L1#j);
);
L2)

{*
maximalContigousSubsets({x_1,x_2,x_4,x_5,x_7,x_8,x_9})
removeEndsets(oo)
oddContigousNonEndsets({x_1,x_2,x_4,x_5,x_7,x_8,x_9})
*}

isFaceOfCyclicPolytope=method()
isFaceOfCyclicPolytope(List,ZZ):=(W,d)->(
 if W=={} then return(true);
 if #oddContigousNonEndsets(W)<=d-#W then return(true);
false);

{*
isFaceOfCyclicPolytope({x_2,x_3},3)
isFaceOfCyclicPolytope({x_3,x_4},3)
isFaceOfCyclicPolytope({x_4,x_9},3)
*}

facesOfBoundaryOfCyclicPolytope=method()
facesOfBoundaryOfCyclicPolytope(ZZ,PolynomialRing):=(d,R)->(
M:=(entries vars R)#0;
L:={{{}}};
S:={};
S1:={};
for j from 1 to #M do (
 if j<=d then (
  S=subsets(M,j);
  S1={};
  for jj from 0 to #S-1 do (
    if isFaceOfCyclicPolytope(S#jj,d)==true then S1=append(S1,face S#jj);
  );
  L=append(L,S1);
 ) else (
  L=append(L,{});
 );
);
L);

{*
R=QQ[x_0..x_6]
L=facesOfBoundaryOfCyclicPolytope(4,R)
apply(L,j->#j)
*}


boundaryComplexOfCyclicPolytope=method()
boundaryComplexOfCyclicPolytope(ZZ,PolynomialRing):=(d,R)->(
M:=(entries vars R)#0;
S:=subsets(M,d);
S1:={};
for jj from 0 to #S-1 do (
  if isFaceOfCyclicPolytope(S#jj,d)==true then S1=append(S1,face S#jj);
);
complex S1);


delta=method()
delta(ZZ,PolynomialRing):=(d,R)->(boundaryComplexOfCyclicPolytope(d,R))


kustinMillerComplex=method(Options=>{verbose=>0})

kustinMillerComplex(Ideal,Ideal,PolynomialRing):=opt->(I,J,T0)->(
if ring I =!= ring J then error("expected ideals in the same ring");
if I+J!=J then error("expected first ideal contained in second");
cI:=res I;
cJ:=res J;
kustinMillerComplex(cI,cJ,T0,opt));


kustinMillerComplex(ChainComplex,ChainComplex,PolynomialRing):=opt->(cI0,cJ0,T0)->(
if opt.verbose>1 then (
  print("------------------------------------------------------------------------------------------------------------------------");
  print("");
  print("res(I): ");
  print("");
  for j from 1 to length(cI0) do (
    print("a_"|j|" = "|net(cI0.dd_j)|" : "|net(degrees source cI0.dd_j)|" -> "|net(degrees target cI0.dd_j));print("");
  );
  print("");
   print("------------------------------------------------------------------------------------------------------------------------");
  print("");
  print("res(J): ");
  print("");
  for j from 1 to length(cJ0) do (
    print("b_"|j|" = "|net(cJ0.dd_j)|" : "|net(degrees source cJ0.dd_j)|" -> "|net(degrees target cJ0.dd_j));print("");
  );
   print("------------------------------------------------------------------------------------------------------------------------");
  print("");
);
I:=ideal(cI0.dd_1);
J:=ideal(cJ0.dd_1);
R:=ring I;
if R =!= ring J then error("expected complexes over the same ring");
v:= gens R;
K:=coefficientRing R;
S:=K[toSequence(join({T0_0},v))];
cI:=substitute(cI0,S);
cJ:=substitute(cJ0,S);
g:=length(cJ);
Is:=substitute(I,S);
Js:=substitute(J,S);
dualcI:= shiftComplex ( dualComplex cI, -codim I);
dualcJ:= shiftComplex ( dualComplex cJ, -codim I);
phi:=unprojectionHomomorphism(I,J);
gJ:=gens source phi;
degshift:=(degree phi)#0;
if opt.verbose>1 then (
   print("phi: "|toString((entries gJ)#0)|" -> "|toString((entries phi)#0));
   print "";
   print("degree phi = "|degshift);
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
IJmap:=sub(matrix entries phi,S)*((gens ideal (dualcJ.dd_0))//(gens Js));
alphaDual:=extend(dualcI,dualcJ, map(dualcI#0,dualcJ#0,IJmap));
w:=(alphaDual_(length cI))_0_0;
alpha:={};
for j from 1 to g-1 do (
  alpha=append(alpha, sub(w^(-1),S)*(transpose alphaDual_(g-1-j)));
);
if opt.verbose>1 then (
   print("");
   for j from 1 to #alpha do (
    print("alpha_"|j|" = "|net(alpha_(j-1)));print("");
   );
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
--print(phi,IJmap,alphaDual,w);
--cU:=extend(cJ,cI,map(cJ_0,cI_0, {{1_S}}));
cJ1:=shiftComplex(cJ ,1);
--print(sub(matrix entries phi,S),(gens ideal (cJ1.dd_0)));
betaMap:=sub(matrix entries phi,S)*((gens ideal (cJ1.dd_0))// (gens Js));
--print((gens ideal (cJ1.dd_0))// (gens Js));
--print(cJ.dd_0,cJ1.dd_0);
beta1:=extend(cI,cJ1,map((cI#0,cJ1#0,betaMap)));
beta:={};
for j from 0 to g-1 do (
  beta=append(beta, -(beta1_j));
);
if opt.verbose>1 then (
   for j from 1 to #beta-1 do (
    print("beta_"|j|" = "|net(beta_(j-1)));print("");
   );
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
u:=-(beta1_(length cI))_0_0;
if opt.verbose>1 then (
   print("u = "|toString(u));
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
h:={0_S};
for j from 1 to g-1 do (
  tC1:= chainComplex { id_(S^(rank (cI#j)))};
  tC2:= chainComplex { cI.dd_j };
  --print(tC1);
  --print(tC2);
  --print(beta#(j-1)*alpha#(j-1));
  hi:= (extend ( tC2, tC1, map (tC2#0, tC1#0,  beta#(j-1)*alpha#(j-1) - h#(j-1)*cI.dd_j  )));
  h=append(h,hi_1);
  --print(h);
);
if opt.verbose>1 then (
   for j from 1 to #h-1 do (
    print("h_"|j|" = "|net(h_(j-1)));print("");
   );
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
L:={};
for j from 1 to g do (
  if g==2 then (
   if j==1 then (
     beta1:=beta#0;
     inL:={cI.dd_1,beta1,cJ.dd_1,S_0};
   );
   if j==2 then (
     ai:=cJ.dd_j;
     bim1:=cI.dd_(j-1);
     alphaim1:=alpha#(j-2);
     inL={alphaim1,ai,bim1,u,S_0};
   );
  );
  if g>=3 then (
   if j==1 then (
     beta1=beta#0;
     inL={cI.dd_1,beta1,cJ.dd_1,S_0};
   );
   if j==2 then (
     b2:=cI.dd_2;
     a2:=cJ.dd_2;
     beta2:=beta#1;
     h1:=h#1;
     inL={b2,beta2,h1,a2,alpha#0,S_0};
   );
   if j>=3 and j<=g-2 then (
     bi:=cI.dd_j;
     ai=cJ.dd_j;
     bim1=cI.dd_(j-1);
     alphaim1=alpha#(j-2);
     betai:=beta#(j-1);
     him1:=h#(j-1);
     inL={bi,betai,him1,ai,alphaim1,bim1,S_0};
     --print inL;
     --print apply(inL,j->(rank target j,rank source j));
   );
   if j>=3 and j==g-1 then (
     ai=cJ.dd_j;
     bim1=cI.dd_(j-1);
     alphaim1=alpha#(j-2);
     him1=h#(j-1);
     betai=beta#(j-1);
     inL={betai,him1,ai,alphaim1,bim1,S_0};
   );
   if j>=3 and j==g then (
     ai=cJ.dd_j;
     bim1=cI.dd_(j-1);
     alphaim1=alpha#(j-2);
     inL={alphaim1,ai,bim1,u,S_0};
   );
  );
  L=append(L,differentials(inL,j,g,degshift));
);
if opt.verbose>1 then (
   for j from 1 to #L do (
    print("f_"|j|" = "|net(L_(j-1))|" : "|net(degrees source L_(j-1))|" -> "|net(degrees target L_(j-1)));print("");
   );
   print("");
   print("------------------------------------------------------------------------------------------------------------------------");
   print("");
);
--return(L);
chainComplex(L))

--kustinMillerComplex(I,J,QQ[t])


{*
restart
installPackage("KustinMiller")
R = QQ[x_1..x_4,z_1..z_4, T]
I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
betti res I
J = ideal (z_1..z_4)
betti res J
cc=kustinMillerComplex(I,J,QQ[t]);
S=ring cc
cc
betti cc
isExact cc
cc.dd_1
cc.dd_2
cc.dd_3
cc.dd_4

*}


--kustinMillerComplex(L#0,L#1,QQ[t])





checkSameRing=method()
checkSameRing(List):=(L)->(
for j from 0 to #L-2 do (
  if (ring L#j)=!=(ring L#(j+1)) then return(false);
);
true)



differentials=method()
differentials(List,ZZ,ZZ,ZZ):=(L,i,g,degshift)->(
--print g;
if i<0 or i>g then error("wrong index");
--print(i,g,L);
if checkSameRing(L)==false then error("expected input over the same ring");
if g==2 then (
 if i==1 then (
   b1:=L#0;beta1:=L#1;a1:=L#2;T:=L#3;
   if rank target b1 != rank target beta1 or rank target b1 != rank target a1 then error("wrong size step "|(toString(i)));
   --print(beta1,a1);
   return(makeGrading((beta1+T*a1),L,{i,g},degshift));
 );
 if i==2 then (
  alphaim1:=L#0;ai:=L#1;bim1:=L#2;u:=L#3;T=L#4;
  if rank target alphaim1 != rank target ai then error("wrong size step "|(toString(i)));
  if rank source alphaim1 != rank source ai then error("wrong size step "|(toString(i)));
  --if rank source ai != rank source bim1 then error("wrong size step "|(toString(i)));  
  return(makeGrading((-alphaim1+(-1)^i*u^(-1)*T*ai),L,{i,g},degshift))
 );
);
if g==3 then (
 if i==1 then (
   b1=L#0;beta1=L#1;a1=L#2;T=L#3;
   if rank target b1 != rank target beta1 or rank target b1 != rank target a1 then error("wrong size step "|(toString(i)));
   --print(b1|(beta1+T*a1));
   return(makeGrading(b1|(beta1+T*a1),L,{i,g},degshift));
 );
 if i==2 then (
  b2:=L#0;beta2:=L#1;h1:=L#2;a2:=L#3;alpha1:=L#4;T=L#5;
  --print(rank target b2,rank target beta2);
  --print(rank target b2,rank target h1);
  if rank target b2 != rank target beta2 or rank target b2 != rank target h1 then error("wrong size step "|(toString(i)));
  if rank source a2 != rank source beta2 then error("wrong size step "|(toString(i)));
  if rank target a2 != rank target alpha1 then error("wrong size step "|(toString(i)));  
  if rank source h1 != rank source alpha1 then error("wrong size step "|(toString(i)));
  n:=rank source b2;
  m:=rank target a2;
  R:=ring b2;
  zero1:=map(R^m,R^n,0);
  --print((beta2|(h1+T*id_(R^(rank target b2))))||((-a2)|(-alpha1)));
  return(makeGrading((beta2|(h1+T*id_(R^(rank target b2))))||((-a2)|(-alpha1)),L,{i,g},degshift));
 );
 if i==3 then (
  alphaim1=L#0;ai=L#1;bim1=L#2;u=L#3;T=L#4;
  if rank target alphaim1 != rank target ai then error("wrong size step "|(toString(i)));
  if rank source alphaim1 != rank source ai then error("wrong size step "|(toString(i)));
  if rank source ai != rank source bim1 then error("wrong size step "|(toString(i)));  
  return(makeGrading((-alphaim1+(-1)^i*u^(-1)*T*ai)||(bim1),L,{i,g},degshift))
 );
);
if i==1 then (
   b1=L#0;beta1=L#1;a1=L#2;T=L#3;
   if rank target b1 != rank target beta1 or rank target b1 != rank target a1 then error("wrong size step "|(toString(i)));
   --print(b1|(beta1+T*a1));
   return(makeGrading(b1|(beta1+T*a1),L,{i,g},degshift));
);
if i==2 then (
  b2=L#0;beta2=L#1;h1=L#2;a2=L#3;alpha1=L#4;T=L#5;
  --print(rank target b2,rank target beta2);
  --print(rank target b2,rank target h1);
  if rank target b2 != rank target beta2 or rank target b2 != rank target h1 then error("wrong size step "|(toString(i)));
  if rank source a2 != rank source beta2 then error("wrong size step "|(toString(i)));
  if rank target a2 != rank target alpha1 then error("wrong size step "|(toString(i)));  
  if rank source h1 != rank source alpha1 then error("wrong size step "|(toString(i)));
  n=rank source b2;
  m=rank target a2;
  R=ring b2;
  zero1=map(R^m,R^n,0);
  --print((b2|beta2|(h1+T*id_(R^(rank target b2))))||(zero1|(-a2)|(-alpha1)));
  return(makeGrading((b2|beta2|(h1+T*id_(R^(rank target b2))))||(zero1|(-a2)|(-alpha1)),L,{i,g},degshift));
);
if i>=3 and i<=g-2 then (
  bi:=L#0;betai:=L#1;him1:=L#2;ai=L#3;alphaim1=L#4;bim1=L#5;T=L#6;
  if rank target bi != rank target betai or rank target bi != rank target him1 then error("wrong size step "|(toString(i)));
  if rank source ai != rank source betai then error("wrong size step "|(toString(i)));
  if rank target ai != rank target alphaim1 then error("wrong size step "|(toString(i)));  
  if rank source him1 != rank source alphaim1 then error("wrong size step "|(toString(i)));
  if rank source bim1 != rank source alphaim1 then error("wrong size step "|(toString(i)));
  n=rank source bi;
  m=rank target ai;
  l:=rank source ai;
  k:=rank target bim1;
  R=ring bi;
  zero1=map(R^m,R^n,0);
  zero2:=map(R^k,R^n,0);
  zero3:=map(R^k,R^l,0);
  return(makeGrading((bi|betai|(him1+(-1)^i*T*id_(R^(rank target bi))))||(zero1|(-ai)|(-alphaim1))||(zero2|zero3|bim1),L,{i,g},degshift))
);
if i>=3 and i==g-1 then (
  betai=L#0;him1=L#1;ai=L#2;alphaim1=L#3;bim1=L#4;T=L#5;
  if rank target betai != rank target him1 then error("wrong size step "|(toString(i)));
  if rank source ai != rank source betai then error("wrong size step "|(toString(i)));
  if rank target ai != rank target alphaim1 then error("wrong size step "|(toString(i)));  
  if rank source him1 != rank source alphaim1 then error("wrong size step "|(toString(i)));
  if rank source bim1 != rank source alphaim1 then error("wrong size step "|(toString(i)));
  l=rank source ai;
  k=rank target bim1;
  R=ring ai;
  zero3=map(R^k,R^l,0);
  return(makeGrading((betai|(him1+(-1)^i*T*id_(R^(rank source bim1))))||((-ai)|(-alphaim1))||(zero3|bim1),L,{i,g},degshift))
);
if i>=3 and i==g then (
  alphaim1=L#0;ai=L#1;bim1=L#2;u=L#3;T=L#4;
  if rank target alphaim1 != rank target ai then error("wrong size step "|(toString(i)));
  if rank source alphaim1 != rank source ai then error("wrong size step "|(toString(i)));
  if rank source ai != rank source bim1 then error("wrong size step "|(toString(i)));  
  return(makeGrading((-alphaim1+(-1)^i*u^(-1)*T*ai)||(bim1),L,{i,g},degshift))
);
error("wrong index"))

makeGrading=method()
makeGrading(Matrix,List,List,ZZ):=(M,L,ig,degshift)->(
i:=ig#0;
g:=ig#1;
R:=ring M;
if g==2 then (
   if i==1 then (
     b1:=L#0;beta1:=L#1;a1:=L#2;T:=L#3;
     return(map(target b1,(source a1)**R^{-degshift},M));
   );
   if i==2 then (
     alphaim1:=L#0;ai:=L#1;bim1:=L#2;u:=L#3;T=L#4;
     return(map((target ai)**R^{-degshift},(source bim1)**R^{-degshift},M));
   );
);
if g==3 then (
 if i==1 then (
   b1=L#0;beta1=L#1;a1=L#2;T=L#3;
   return(map(target b1,(source b1)++(source a1)**R^{-degshift},M));
 );
 if i==2 then (
   b2:=L#0;beta2:=L#1;h1:=L#2;a2:=L#3;alpha1:=L#4;T=L#5;
   return(map((target b2)++(target a2)**R^{-degshift},((source a2)**R^{-degshift})++(target b2)**R^{-degshift},M));
 );
 if i==3 then (
   alphaim1=L#0;ai=L#1;bim1=L#2;u=L#3;T=L#4;
   return(map(((target ai)**R^{-degshift})++(target bim1)**R^{-degshift},(source bim1)**R^{-degshift},M));
 );
);
if g>3 then (
  if i==1 then (
    b1=L#0;beta1=L#1;a1=L#2;T=L#3;
    return(map(target b1,(source b1)++(source a1)**R^{-degshift},M));
  );
  if i==2 then (
    b2=L#0;beta2=L#1;h1=L#2;a2=L#3;alpha1=L#4;T=L#5;
    return(map((target b2)++(target a2)**R^{-degshift},(source b2)++((source a2)**R^{-degshift})++(target b2)**R^{-degshift},M));
  );
  if i>=3 and i<=g-2 then (
    bi:=L#0;betai:=L#1;him1:=L#2;ai=L#3;alphaim1=L#4;bim1=L#5;T=L#6;
    return(map((target bi)++((target ai)**R^{-degshift})++(target bim1)**R^{-degshift},(source bi)++((source ai)**R^{-degshift})++(target bi)**R^{-degshift},M));
  );
  if i>=3 and i==g-1 then (
    betai=L#0;him1=L#1;ai=L#2;alphaim1=L#3;bim1=L#4;T=L#5;
    return(map((source bim1)++((target ai)**R^{-degshift})++(target bim1)**R^{-degshift},((source ai)**R^{-degshift})++(source bim1)**R^{-degshift},M));
  );
  if i>=3 and i==g then (
    alphaim1=L#0;ai=L#1;bim1=L#2;u=L#3;T=L#4;
    return(map(((target ai)**R^{-degshift})++(target bim1)**R^{-degshift},(source bim1)**R^{-degshift},M));
  );
);
error("wrong index"))


shiftComplex= method()
shiftComplex(ChainComplex,ZZ) := (CJ,p) ->  (
    CJShifted := new ChainComplex;
    CJShifted.ring = ring CJ;
    for i from min(CJ) -p  to max (CJ)-p   do  CJShifted#i = (CJ#(i+p));
    for i from min(CJ) -p+1  to max (CJ)-p   do  CJShifted.dd_i = CJ.dd_(i+p);
    CJShifted   )


dualComplex= method()
dualComplex(ChainComplex)  := (CJ) -> (
  dual CJ;
  CJdual := new ChainComplex; 
  CJdual.ring = ring CJ;
  for i from -max(CJ) to -min(CJ) do  CJdual#i = CJ#(-i);
  for i from -max(CJ)+1  to -min(CJ) do  CJdual.dd#i = transpose  CJ.dd_(-i+1); 
  CJdual )

unprojectionHomomorphism=method()
unprojectionHomomorphism(Ideal,Ideal):=(I,J)->(
R:=ring I;
if ring I =!= ring J then error("expected ideals in the same ring");
if I+J!=J then error("expected first ideal contained in second");
M:=Hom(J,R^1/I);
if rank source gens M != 2 then (
   for j from 0 to -1+rank source gens M do (
      phi:=homomorphism M_{j};
      gJ:=gens source phi;
      print("phi: "|toString((entries gJ)#0)|" -> "|toString((entries phi)#0));
   );
   error("wrong number of generators");
);
f1:=homomorphism M_{0};
f2:=homomorphism M_{1};
if J+I==I+ideal (entries f1)#0 then (
 return(f2)
) else (
 return(f1)
))



{*
cycResDef=method()
cycResDef(ZZ,PolynomialRing,PolynomialRing):=(d,R,Z)->(
     -- we generate the input ideals C(d,m) and C(d-2,m-1)
     -- compute their minimal resolutions and from these
     -- the minimal resolution von C(d,m+1)
     -- in the end the computation of the resolutions of 
     -- C(d,m) and C(d-2,m-1) will be replaced by calling 
     -- cycRes recursively
     v:=gens R;
     if d==#v-1 then error("Expected non-hypersurface");
     if d>#v-1 then error("Not enough vertices");
     vI:=v_{0..(#v-2)};
     vJ:=v_{0..(#v-3)};
     K:=coefficientRing R;
     RI:=K[toSequence vI];
     vI=apply(vI,j->sub(j,RI));
     RJ:=K[toSequence vJ];
     vJ=apply(vJ,j->sub(j,RJ));
     CI:=delta(d,RI);
     --print(fvector CI,fvector CJ);  
     I:=complexToIdeal CI;
     if d-2>0 then (  
       CJ:=delta(d-2,RJ);
       J0:=complexToIdeal CJ;
     ) else (
       J0=ideal vars RJ;
     );
     if odd(d)==true then (
       if #(gens Z)!=2 then error("Base ring should have 2 variables");
       z1:=Z_0;
       z2:=Z_1;
       vJs:=join({z1},vJ_{1..#vJ-2},{z2});
       vU:=join({z1},vI,{z2});
       T0:=K[last v];
     ) else (
       if #(gens Z)!=1 then error("Base ring should have 1 variable");
       z:=Z_0;
       vJs=join({z},vJ_{1..#vJ-1});
       vU=join({z},vI);
       T0=K[last v];
     );
RJs:=K[toSequence vJs];
J:=sub(J0,toList apply(#vJ,j->vJ#j=>RJs_j));
RU:=K[toSequence vU];
I=sub(I,RU);
J=sub(J,RU);
--return({I,J});
--print(betti res I,betti res J);
--C:=delta(d,R);
--IC:=complexToIdeal C;
--print betti res IC;
kustinMillerComplex(I,J,T0));
--kustinMillerComplex(I,J,QQ[t])

--cycRes(4,R)

*}
{* 
installPackage("CyclicPolytopeRes")
R=QQ[x_1..x_8]
C=delta(4,R)
I=complexToIdeal C
betti res I
L=cycResDef(4,R,QQ[z])

kustinMillerComplex(L#0,L#1,QQ[t])

*}

{*
installPackage("CyclicPolytopeRes")
R=QQ[x_1..x_8]
cycRes(4,R)
*}

{*
buchsbaumEisenbudCyclicSyzygyMatrix=method()
buchsbaumEisenbudCyclicSyzygyMatrix(PolynomialRing) := (R) -> (
  d:=rank source vars R - 3;
  v0:=gens R;
  --v:=v0_{#v0-1,0..#v0-2};
  v:=v0;
  BEentries :=  (d,i,j) -> (
      tempResult := 0_R ;
      if (j==i+1) then  tempResult = v_(i-1) ;
      if (i==j+1) then  tempResult = -v_(j-1) ;
      if (i == 1) and (j ==d) then   tempResult = -v_(d-1);
      if (i == d) and (j ==1) then   tempResult = v_(d-1);
      tempResult );
  matrix toList apply (1..d+3, i-> toList apply (1..d+3, j ->  BEentries (d+3,i,j))) )

buchsbaumEisenbudCyclicGens=method()
buchsbaumEisenbudCyclicGens(PolynomialRing) := (R) -> (
s:=buchsbaumEisenbudCyclicSyzygyMatrix R;
d:=rank source vars R - 3;
p:=gens pfaffians(d+2,s);
L:={}; 
for i from 0 to d+2 do L = append(L , (-1)^(i)*p_(d+2-i)_0);
matrix {L})
--buchsbaumEisenbudCyclicGens R

buchsbaumEisenbudCyclicRes=method()
buchsbaumEisenbudCyclicRes(PolynomialRing) := (R) -> (
if even(# gens R) ==true then error("odd dimension not yet implemented"); 
g:=buchsbaumEisenbudCyclicGens R;
s:=buchsbaumEisenbudCyclicSyzygyMatrix R;
chainComplex {g,s,transpose g,map(R^1,R^0,0)})

--BuchsbaumEisenbudCyclicRes R

koszulComplexFromParts=method()
koszulComplexFromParts(PolynomialRing):=(R)->(
if # gens R <= 2 then return(res ideal vars R);
--if # gens R == 3 then return(buchsbaumEisenbudCyclicRes R);
K:=coefficientRing R;
v:=gens R;
S:=K[v_{1..#v-1}];
S1:=K[v_0];
--S:=K[v_{0..#v-2}];
--S1:=K[v_(#v-1)];
c:=koszulComplexFromParts S;
c1:=koszulComplexFromParts S1;
cc:=substitute(c,R)**substitute(c1,R);
-- remove trailing zero
cn:= new ChainComplex;
cn.ring = ring cc;
for i from min(cc) to max(cc)-1 do cn#i = R^(degrees (cc#i));
for i from min(cc)+1 to max(cc)-1 do cn.dd_i = cc.dd_i;
cn)
--koszulComplexFromParts R



cycRes=method(Options=>{verbose=>0,UseBuchsbaumEisenbud=>true})
cycRes(ZZ,PolynomialRing):=opt->(d,R)->(
     v:=gens R;
     if d>#v-1 then error("Not enough variables compared to dimension");
     -- boundary cases:
     if d==0 then (
       -- complete intersection case
       return(koszulComplexFromParts R);
     );
     if d==#v-1 then (
       -- hypersurface case
       cc:=res complexToIdeal delta(d,R);
       return(cc)
     );
     if opt.UseBuchsbaumEisenbud==true and d==#v-3 then (
       -- Pfaffian case
       --cc:=res complexToIdeal delta(d,R);
       cc=buchsbaumEisenbudCyclicRes R;
       return(cc)
     );
     vI:=v_{0..(#v-2)};
     vJ:=v_{0..(#v-3)};
     K:=coefficientRing R;
     RI:=K[toSequence vI];
     vI=apply(vI,j->sub(j,RI));
     RJ:=K[toSequence vJ];
     vJ=apply(vJ,j->sub(j,RJ));
     CI:=delta(d,RI);
     --CJ:=delta(d-2,RJ);
     --print(fvector CI,fvector CJ);  
     I:=complexToIdeal CI;
     --J0:=complexToIdeal CJ;
     if d-2>0 then (  
       CJ:=delta(d-2,RJ);
       J0:=complexToIdeal CJ;
     ) else (
       J0=ideal vars RJ;
     );
     if odd(d)==true then (
       z:=symbol z;
       Z:=K[z_1,z_2];
       z1:=Z_0;
       z2:=Z_1;
       vJs:=join({z1},vJ_{1..#vJ-2},{z2});
       vU:=join({z1},v,{z2});
       T0:=K[T];
     ) else (
       z=symbol z;
       Z=K[z];
       z=Z_0;
       vJs=join({z},vJ_{1..#vJ-1});
       vU=join({z},vI);
       T0=K[last v];
     );
RJs:=K[toSequence vJs];
J:=sub(J0,toList apply(#vJ,j->vJ#j=>RJs_j));
RU:=K[toSequence vU];
I=sub(I,RU);
J=sub(J,RU);
--return({I,J});
--print(betti res I,betti res J);
--C:=delta(d,R);
--IC:=complexToIdeal C;
--print betti res IC;
--print vars T0;
--cI:=res I;
cI:=sub(cycRes(d,RI,opt),RU);
--cJ:=res J;
cJ:=sub(cycRes(d-2,RJs,opt),RU);
if opt.verbose>1 then (
  print("");
  print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
);
if opt.verbose>0 then (
  print "";
  print((printC(d,RI))|"   +   "|(printC(d-2,RJs))|"   ->   "|(printC(d,R)));
  print "";
);
--print "J";
--print cJ.dd_1;
--print complexToIdeal delta(d-2,RJs);
--print "I";
--print cI.dd_1;
--print complexToIdeal delta(d,RI);
--print("-->",d,vars RI,(cycRes(d,RI)).dd_1);
substitute(kustinMillerComplex(cI,cJ,T0,verbose=>opt.verbose),R));

printC=method()
printC(ZZ,PolynomialRing):=(d,R)->("delta("|d|","|(toString gens R)|")")
*}

substitute(ChainComplex,Ring):=(cc,S)->(
    dual cc;
    cn:= new ChainComplex;
    cn.ring = S;
    for i from min(cc) to max(cc) do cn#i = S^(degrees (cc#i));
    for i from min(cc)+1 to max(cc) do cn.dd_i = sub(cc.dd_i,S);
    cn)

-- substitute(L,R)


{*

installPackage("CyclicPolytopeRes")
R=QQ[x_1..x_6]
L=cycRes(2,R)

*}


--C:=delta(d,R);
--IC:=complexToIdeal C;
--res IC)



isExact=method()
isExact(ChainComplex):=(cc)->(
tst:=true;
for j from min(cc)+1 to max(cc) do (
    if cc.dd_(j)*cc.dd_(j+1) !=0 then return false;
    if (HH^j cc) !=0 then return false;
);
true)




coFace=method()
coFace(Face,Face):=(F,G)->(
v1:=vertices F;
v2:=vertices G;
new Face from listMinus(v2,v1))



stellarSubdivisionSimplex=method()
stellarSubdivisionSimplex(Face,Face,PolynomialRing,PolynomialRing):=(D,s,n,R)->(
   L := {};
   --print(s,D,isSubface(s,D));
   if  isSubface(s,D)==false then ( 
      L = complex {substituteFace(D,R)};
   ) else ( 
      L=subdivideFace (D,s,n,R);
   );
L)

stellarSubdivision=method()
stellarSubdivision(Complex,Face,PolynomialRing):= (D,s0,n)  ->  (
   R1:=simplexRing D;
   s:=substituteFace(s0,R1);
   if isFace(s,D)==false then (
      use simplexRing D;
      error("not a face");
   );
   L :={};
   fc:=facets D;
   i:=0;
   R1=simplexRing D;
   K:=coefficientRing R1;
   v:=join(gens R1,gens n);
   R:=K[v];
   for i from 0 to #fc-1  do (
     L = join(L,stellarSubdivisionSimplex (fc#i,s,n,R));
   );
complex L)

joinFaces=method()
joinFaces(Face,Face):=(F,G)->(
v1:=vertices F;
v2:=vertices G;
new Face from (v1|v2))


subdivideFace=method()
subdivideFace(Face,Face,PolynomialRing,PolynomialRing):= (D,s,n,R) -> (
   comp := substituteFace(coFace(s,D),R);
   nface:= substituteFace(new Face from {n_0},R);
   nc:=joinFaces(comp,nface);
   L := {};
   i:=0;
   nfc:={};
   vs:=vertices s;
   vn:=n_{0};
   for i from 0 to  #vs-1 do (
      nfc=joinFaces(nc,substituteFace(coFace(new Face from {vs#i},s),R));
      L= append(L,nfc);
   );
complex L)



{*
R=QQ[x_1..x_6]
I=ideal(product((entries vars R)#0))
D=idealToComplex I
Dsigma=stellarSubdivision(D,face {x_1,x_2,x_3},QQ[t])

R=QQ[y_1..y_6]
I=ideal(product((entries vars R)#0))
C=createComplex(6,I)
stellarSubd(7,{1,2,3},C)


*}


------------------------------------------------------------------------
-- link and closed star
	 
selectFaces=method()
selectFaces(List,Function):=(C,f)->(
--L1:={};
L2:={};
q:=#C-1;
qq:=0;
while q>=0 do (
  qq=0;
  --L2={};
  while qq<#(C#q) do (
    if isSubfaceList(C#q#qq,L2)==false then (
     if f(C#q#qq)==true then L2=append(L2,C#q#qq);
    );
  qq=qq+1);
  --L1=append(L1,L2);
q=q-1);
L2)

isSubfaceList=method()
isSubfaceList(Face,List):=(F,L)->(
for q from 0 to #L-1 do (
  if isSubface(F,L#q)==true then return(true);
);
false)

{*
closedStar=method()
closedStar(Face,Complex):=(F,C0)->(
C:=faces C0;
complex selectFaces(C,j->isClosedStarFace(j,F,C)))


isClosedStarFace=method()
isClosedStarFace(Face,Face,List):=(G,F,C)->(
q:=0;
qq:=0;
gf:=set vertices(F) + set vertices(G);
while q<#C do (
  qq=0;
  while qq<#(C#q) do (
    if (set vertices(C#q#qq))===gf then (return(true));
  qq=qq+1);
q=q+1);
false)
*}

isLinkFace=method()
isLinkFace(Face,Face,List):=(G,F,C)->(
if (set vertices G)*(set vertices F)=!=set {} then return(false);
q:=0;
qq:=0;
gf:=set vertices(F) + set vertices(G);
while q<#C do (
  qq=0;
  while qq<#(C#q) do (
    if (set vertices(C#q#qq))===gf then (return(true));
  qq=qq+1);
q=q+1);
false)
--link(F,C)

-- > export
link=method(Options=>{subRing=>false})
link(Face,Complex):=opts->(F,C0)->(
C:=faces C0;
fc:=selectFaces(C,j->isLinkFace(j,F,C));
R:=simplexRing C0;
var:=toList (set ((entries vars R)#0)-(set F));
if opts.subRing==true then (
   K:=coefficientRing ring var#0;
   Rsmall:=K[var];
   fc=apply(fc,j->substituteFace(j,Rsmall));
);
complex fc)





------------------------------------------------------------------------------------------------------------------
-- documentation and tests

beginDocumentation()

doc ///
  Key
    KustinMiller
  Headline
    Unprojection and the Kustin-Miller complex construction
  Description
    Text
      This package implements the construction of the Kustin-Miller complex [1]. This is the
      fundamental construction of resolutions in unprojection theory [2].

      The main goal of unprojection theory is to provide a substitute for structure theorems
      not available for Gorenstein rings of codimension >3.

      It has been applied in various cases to construct new varieties, e.g., in [3], [4] for Campedelli surfaces and Calabi-Yau varieties.
      
      We provide a general command @TO kustinMillerComplex@ for the Kustin-Miller construction and demonstrate it at several examples connecting unprojection theory
      and combinatorics like stellar subdivisions of simplicial complexes [5],
      minimal resolutions of Stanley-Reisner rings of boundary complexes {\Delta}(d,m) 
      of cyclic polytopes of dimension d on m vertices [6], and the classical 
      (non-monomial) Tom example of unprojection [2].
      

      {\bf References:}

      For the Kustin-Miller complex see:

      [1] {\it A. Kustin and M. Miller, Constructing big Gorenstein ideals from small ones, J. Algebra 85 (1983)}, 303-322.

      [2] {\it Papadakis, Kustin-Miller unprojection with complexes,  J. Algebraic Geometry 13 (2004) 249-268}, @HREF"http://arxiv.org/abs/math/0111195"@

      For constructing new varieties see for example:

      [3] {\it J. Neves and S. Papadakis, A construction of numerical Campedelli surfaces with ZZ/6 torsion, Trans. Amer. Math. Soc. 361 (2009), 4999-5021}.

      [4] {\it J. Neves and S. Papadakis, Parallel Kustin-Miller unprojection with an application to Calabi-Yau geometry, preprint, 2009, 23 pp}, @HREF"http://arxiv.org/abs/0903.1335"@

      For the stellar subdivision case see:

      [5] {\it J. Boehm, S. Papadakis: Stellar subdivisions and Stanley-Reisner rings of Gorenstein complexes}, @HREF"http://arxiv.org/abs/0912.2151"@

      For the case of cyclic polytopes see:

      [6] {\it J. Boehm, S. Papadakis: On the structure of Stanley-Reisner rings associated to cyclic polytopes}, @HREF"http://arxiv.org/abs/0912.2152"@


      {\bf Examples:}

      @TO "Cyclic Polytopes"@  -- Minimal resolutions of Stanley-Reisner rings of boundary complexes of cyclic polytopes

      @TO "Stellar Subdivisions"@  -- Stellar subdivisions and unprojection

      @TO "Tom"@  -- The Tom example of unprojection

      
      {\bf Key functions and data types:}

      {\it The central function of the package is:}

      @TO kustinMillerComplex@  -- The Kustin-Miller complex construction


      {\it Also important is the function to represent the unprojection data as a homomorphism:}

      @TO unprojectionHomomorphism@ -- Compute the homomorphism associated to an unprojection pair


      {\it Types and functions used to compare with the combinatorics:}

      @TO Complex@  --  The class of all simplicial complexes
      
      @TO Face@  --  The class of all faces of simplicial complexes

      @TO complexToIdeal@  --  Compute the Stanley-Reisner ideal associated to a simplicial complex

      @TO idealToComplex@  --  Compute the Stanley-Reisner complex associated to a monomial square free ideal

      @TO delta@  --  The boundary complex of a cyclic polytope

      @TO stellarSubdivision@  -- Compute the stellar subdivision of a simplicial complex


      {\bf Installation:}

      Put the file {\it KustinMiller.m2} somewhere into the path of Macaulay2      
      (usually into the directory .Macaulay2/code inside your home directory, type
      path in M2 to see the path) and do inside M2

      @TO installPackage@ "KustinMiller"

///




doc ///
  Key
    idealToComplex
    (idealToComplex,Ideal)
    (idealToComplex,MonomialIdeal)
  Headline
    Compute the Stanley-Reisner complex.
  Usage
    idealToComplex(I)
  Inputs
    I:Ideal
  Outputs
    D:Complex
  Description
   Text
        Compute the Stanley-Reisner @TO Complex@ D of the monomial square free ideal I.

   Example
     K=QQ;
     R=K[x_0..x_4]
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0)
     idealToComplex I
  SeeAlso
     complexToIdeal
     Complex
///


TEST ///
     K=QQ;
     R=K[x_0..x_4];
     D=idealToComplex  ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     assert(D==complex {face {x_0, x_2}, face {x_1, x_3}, face {x_2, x_4}, face {x_1, x_4}, face {x_0, x_3}});
///


doc ///
  Key
    Complex
  Headline
   The class of all simplicial complexes.
  Description
   Text
        The class of all simplicial complexes on the variables of a @TO PolynomialRing@.
        A complex is represented by its maximal faces.

   Text
        A complex can be constructed from a reduced monomial @TO Ideal@ by the method
        @TO idealToComplex@

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D =idealToComplex I
     simplexRing D
     dimension D
     L=facets D
     D==complex L
     complexToIdeal D
  SeeAlso
     idealToComplex
     complexToIdeal
     facets
     faces
     Face
///




doc ///
  Key
    Face
  Headline
   The class of faces of simplicial complexes.
  Description
   Text
        The class of faces of simplicial complexes on the variables of a polynomial ring.
        The faces are lists of variables of the @TO PolynomialRing@

   Text
        The maximal faces can be obtained from a simplicial @TO Complex@ by the method
        @TO facets@

   Example
     K=QQ;
     R=K[x_0..x_4];
     face {x_0,x_1}
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D =idealToComplex I
     fc=facets D
     fc#0
  SeeAlso
     face
     idealToComplex
     Complex
     facets
     faces
///


doc ///
  Key
    (symbol ==,Face,Face)
  Headline
   Compare two faces.
  Usage
    F==G
  Inputs
    F:Face
    G:Face
  Outputs
    :Boolean
  Description
   Text
        Checks whether F and G are equal.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1}
     G=face {x_1,x_0}
     F==G
  SeeAlso
     Face
     face
     idealToComplex
     Complex
     facets
     faces
///



doc ///
  Key
    face
    (face,List)
  Headline
    Generate a face.
  Usage
    face(L)
  Inputs
    L:List
  Outputs
    :Face
  Description
   Text
        Generates a face out of a list L.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1}
  SeeAlso
     Face
     face
     idealToComplex
     Complex
     facets
     faces
///


doc ///
  Key
    facets
    (facets,Complex)
  Headline
    The facets of a simplicial complex.
  Usage
    facets(D)
  Inputs
    D:Complex
  Outputs
    D:List
  Description
   Text
        Returns the facets of a complex represented as a @TO List@ of lists of vars simplexRing D.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I;
     facets D
  SeeAlso
     Complex
     Face
     faces
     idealToComplex
     simplexRing
///


doc ///
  Key
    dimension
    (dimension,Complex)
    (dimension,Face)
  Headline
    The dimension of a simplicial complex or a face of a simplicial complex.
  Usage
    dimension(D)
    dimension(F)
  Inputs
    D:Complex
    F:Face
  Outputs
    :ZZ
  Description
   Text
        Returns the dimension of a simplicial @TO Complex@ or of a @TO Face@ of a simplicial complex.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I
     dimension D
     fc=facets D
     dimension fc#0
  SeeAlso
     Complex
     Face
     facets
     faces
     idealToComplex
///


doc ///
  Key
    vertices
    (vertices,Face)
  Headline
    The vertices of a face of a simplicial complex.
  Usage
    vertices(F)
  Inputs
    F:Face
  Outputs
    :List
  Description
   Text
        Returns a @TO List@ with the vertices of a @TO Face@ of a simplicial complex.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I
     fc=facets D
     vertices fc#0
  SeeAlso
     Complex
     Face
     facets
     faces
     idealToComplex
///



doc ///
  Key
    isFace
    (isFace,Face,Complex)
  Headline
    Test whether a face is a face of a given complex.
  Usage
    isFace(F,C)
  Inputs
    F:Face
    C:Complex
  Outputs
    :Boolean
  Description
   Text
        Test whether F is a face of C.

   Example
     K=QQ;
     R=K[x_1..x_5];
     C=idealToComplex ideal (x_1*x_2,x_3*x_4*x_5)
     F1=face {x_1,x_2}
     F2=face {x_1,x_3}
     isFace(F1,C)
     isFace(F2,C)
  SeeAlso
     Complex
     Face
     facets
     faces
     idealToComplex
///




doc ///
  Key
    isSubface
    (isSubface,Face,Face)
  Headline
    Test whether a face is a subface of another face.
  Usage
    isSubface(F,G)
  Inputs
    F:Face
    G:Face
  Outputs
    :Boolean
  Description
   Text
        Test whether F is a subface of G.

   Example
     K=QQ;
     R=K[x_0..x_4];
     G=new Face from {x_0,x_1,x_2}
     F1=new Face from {x_0,x_2}
     F2=new Face from {x_0,x_3}
     isSubface(F1,G)
     isSubface(F2,G)
  SeeAlso
     Complex
     Face
     facets
     faces
///


doc ///
  Key
    substituteFace
    (substituteFace,Face,PolynomialRing)
  Headline
    Substitute a face to a different ring.
  Usage
    substituteFace(F,R)
  Inputs
    F:Face
    R:PolynomialRing
  Outputs
    :Face
  Description
   Text
        Substitute a face to a different simplex ring. R should contain the variables of the @TO simplexRing@ of F.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1,x_2}
     S=R**K[y]
     substituteFace(F,S)
  SeeAlso
     Complex
     face
     Face
     facets
     faces
     idealToComplex
///

doc ///
  Key
    substituteComplex
    (substituteComplex,Complex,PolynomialRing)
  Headline
    Substitute a complex to a different ring.
  Usage
    substituteComplex(F,R)
  Inputs
    F:Complex
    R:PolynomialRing
  Outputs
    :Complex
  Description
   Text
        Substitute a complex to a different simplex ring. R should contain the variables of the @TO simplexRing@ of C.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     C=idealToComplex I
     simplexRing C
     S=R**K[y]
     C1=substituteComplex(C,S)
     simplexRing C1
  SeeAlso
     Complex
     substituteFace
     idealToComplex
///


doc ///
  Key
    faceIdeal
    (faceIdeal,Face)
  Headline
    The ideal of a face of a simplicial complex.
  Usage
    faceIdeal(F)
  Inputs
    F:Face
  Outputs
    :Ideal
  Description
   Text
        Returns the @TO Ideal@ of a @TO Face@ of a simplicial complex D.
        Here D is considered as the subcomplex of a simplex on the variables and this ideal defines the stratum of the dual simplex which corresponds to F.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I
     fc=facets D
     faceIdeal fc#0
  SeeAlso
     Complex
     Face
     facets
     faces
     vertices
     idealToComplex
///


doc ///
  Key
    simplexRing
    (simplexRing,Complex)
    (simplexRing,Face)
  Headline
    The underlying polynomial ring of a simplicial complex, face, fan or cone.
  Usage
    simplexRing(D)
    simplexRing(F)
  Inputs
    D:Complex
    F:Face
  Outputs
    R:PolynomialRing
  Description
   Text
       Returns the @TO PolynomialRing@ of a simplicial @TO Complex@ or a @TO Face@ of a simplicial complex.
       This is the ring with variables corresponding to the vertices of D or the underlying complex D of F.
       It is the Stanley-Reisner ring of the simplex into which D embeds.
       This simplex is 
       complex {(entries vars R)#0}

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0)
     D=idealToComplex I
     simplexRing D
     fc=facets D
     simplexRing fc#0
     S=complex {(entries vars R)#0}
     complexToIdeal S
  SeeAlso
     Complex
     facets
     faces
     idealToComplex
///




doc ///
  Key
    complexToIdeal
    (complexToIdeal,Complex)
  Headline
    Compute the Stanley-Reisner ideal.
  Usage
    complexToIdeal(D)
  Inputs
    D:Complex 
        a simplicial complex on the variables of some polynomial ring R.
  Outputs
    :Ideal
  Description
   Text
        Computes the Stanley-Reisner ideal of D in R.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I
     complexToIdeal(D)
  SeeAlso
     idealToComplex
///


TEST ///
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex I; 
     assert(I==complexToIdeal(D));
///




doc ///
  Key
    fvector
    (fvector,Complex)
  Headline
    Returns the F-vector of a complex
  Usage
    fvector(C)
  Inputs
    C:Complex
  Outputs
    :List
  Description
   Text
       Compute the F-vector of a simplicial @TO Complex@ C.

   Example
     K=QQ;
     R=K[x_0..x_4]
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0)
     C=idealToComplex I
     fvector(C)
  SeeAlso
     Complex
     Face
     faces
     idealToComplex
///



doc ///
  Key
    faces
    (faces,Complex)
    (faces,Complex,ZZ)
  Headline
    Returns the faces of a complex
  Usage
    faces(C)
  Inputs
    C:Complex
    d:ZZ
       from -1 to dim(C)
  Outputs
    L:List
  Description
   Text
       Compute the faces of a simplicial @TO Complex@ C.
       The result is a @TO List@ L. The j-th entry L#j of L
       is a list of the faces of C of dimension j.

       If the second argument d is specificed then a list of the faces of dimension d is returned.

   Example
     K=QQ;
     R=K[x_0..x_4]
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0)
     C=idealToComplex I
     faces(C)
   Text

   Example
     K=QQ;
     R=K[x_0..x_4]
     I=ideal(x_0*x_1,x_2*x_3*x_4)
     C=idealToComplex I
     faces(C)
     faces(C,1)
  SeeAlso
     Complex
     Face
     facets
     idealToComplex
///





doc ///
  Key
    (net,Face)
  Headline
    Printing faces or cones.
  Usage
    net(F)
  Inputs
    F:Face
  Outputs
    :Net
  Description
   Text
        Prints faces. The vertices are printed without any brackets and with one space between them.

   Example
     K=QQ;
     R=K[x_0..x_4];
     face {x_0,x_1}
  SeeAlso
     Complex
///



doc ///
  Key
    delta
    (delta,ZZ,PolynomialRing)
  Headline
    Boundary complex of cyclic polytope.
  Usage
    delta(d,R)
  Inputs
    d:ZZ
       positive
    R:PolynomialRing
  Outputs
    :Complex
  Description
   Text
      Boundary complex of a cyclic polytope of dimension d on the variables of R as vertices, i.e., {\Delta}(d,m) if m is the number of variables of R.

   Example
     K=QQ;
     R=K[x_0..x_6];
     C=delta(4,R)
     fvector C
     I=complexToIdeal C
     betti res I
  SeeAlso
     complexToIdeal
     fvector
///


doc ///
  Key
    complex
    (complex,List)
  Headline
    Create a complex.
  Usage
    complex(L)
  Inputs
    L:List
  Outputs
    :Complex
  Description
   Text
     Create a complex.
     The list L is assumed to contain the facets.
     
     The facets are assumed to be of class @TO Face@, all of them over the same @TO PolynomialRing@.
     
     This command is equivalent to @TO "new"@ @TO Complex@ @TO "from"@ L.
     
   Example
     K=QQ;
     R=K[x_0..x_4];
     S=complex {{x_0,x_1},{x_1,x_2},{x_2,x_3},{x_3,x_4},{x_4,x_0}}
     complexToIdeal S
  SeeAlso
     Complex
     Face
     complexToIdeal
     fvector
///



doc ///
  Key
    (symbol ==,Complex,Complex)
  Headline
   Compare two complexes.
  Usage
    C1==C2
  Inputs
    C1:Complex
    C2:Complex
  Outputs
    :Boolean
  Description
   Text
     Checks whether C1 and C2 are equal.

   Example
     K=QQ;
     R=K[x_0..x_4];
     C1=complex {face {x_1,x_2},face {x_2,x_3}}
     C2=complex {face {x_2,x_3},face {x_2,x_1}}
     C3=complex {face {x_1,x_2},face {x_2,x_4}}
     C1==C2
     C1==C3
  SeeAlso
     Face
     face
     Complex
///


doc ///
  Key
    verbose
    [kustinMillerComplex,verbose]
  Headline
    Option to print intermediate data
  Description
   Text
    @TO Option@ to print the intermediate results.

    It takes @TO ZZ@ values (standard is 0), increasing the amount of output with the value.
///


doc ///
  Key
    kustinMillerComplex
    (kustinMillerComplex,Ideal,Ideal,PolynomialRing)
    (kustinMillerComplex,ChainComplex,ChainComplex,PolynomialRing)
  Headline
    Compute Kustin-Miller resolution of the unprojection of I in J
  Usage
    kustinMillerComplex(I,J,S)
    kustinMillerComplex(cI,cJ,S)
  Inputs
    J:Ideal
    I:Ideal
        contained in J
    cI:ChainComplex
        resolution of I
    cJ:ChainComplex
        resolution of J
    T0:PolynomialRing
        over the the same @TO coefficientRing@ as the @TO ring@ R of J and I
        with one new variable T.
  Outputs
    :ChainComplex
        over R**T0
  Description
   Text
    Compute Kustin-Miller resolution of the unprojection of I in J (or
    equivalently of J \subset R/I) with unprojection variable T.

    We have the following setup:

    Assume R is a @TO PolynomialRing@ over a field, the degrees of all
    variables positive and I inside J inside R two homogeneous ideals of R
    such that R/I and R/J are Gorenstein and dim(R/J)=dim(R/I)-1.

    For a description of this resolution and how it is computed see for example Section 2.3 of

    J. Boehm, S. Papadakis: On the structure of Stanley-Reisner rings associated to cyclic polytopes, @HREF"http://arxiv.org/abs/0912.2152"@


    It is also possible to specify minimal resolutions of I and J.

    Note that @TO kustinMillerComplex@ returns a chain complex over a new ring R**T0.
    So to avoid printing the variables of this ring when printing the chain complex
    just give a name to the ring (e.g., do S = @TO ring@ cc  to call it S).

    We illustrate the process at the example described in Section 5.5 of 

    Papadakis, Kustin-Miller unprojection with complexes,  J. Algebraic Geometry 13 (2004) 249-268, @HREF"http://arxiv.org/abs/math/0111195"@


   Example
     R = QQ[x_1..x_4,z_1..z_4]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     betti res I
     J = ideal (z_1..z_4)
     betti res J
     cc=kustinMillerComplex(I,J,QQ[T]);
     S=ring cc
     cc
     betti cc
     isExact cc
     print cc.dd_1
     print cc.dd_2
     print cc.dd_3
     print cc.dd_4
  SeeAlso
    kustinMillerComplex
    differentials
    unprojectionHomomorphism
///


doc ///
  Key
    differentials
    (differentials,List,ZZ,ZZ,ZZ)
  Headline
    Generate the differentials of the Kustin-Miller resolution
  Usage
    differentials(L,j,g,s)
  Inputs
    L:List
       with entries of type @TO Matrix@ and the last entry of type @TO RingElement@,
       all of them defined over the same ring.
    g:ZZ
       positive
    j:ZZ
       from 1 to g
    s:ZZ
  Outputs
    :Matrix
  Description
   Text
    Generate the j-th differential of a Kustin-Miller resolution
    of length g. So, e.g., for j=1 we obtain the relations of the 
    ring resolved and for j=2 the first syzygies of those.

    We use the notation of Section 2.3 of

    J. Boehm, S. Papadakis: On the structure of Stanley-Reisner rings associated to cyclic polytopes, @HREF"http://arxiv.org/abs/0912.2152"@ [math.AC]

    For any j the @TO last@ entry of L should be the variable T.

    For j=1 we assume L = \{ b_1, beta_1, a_1, T \}.

    For j=2 we assume L = \{ b_2, beta_2, h_1, a_2, alpha_1, T \}.

    For j=3,...,g-1 we assume L = \{ b_j, beta_j, h_{j-1}, a_j, alpha_{j-1}, b_{j-1}, T \}.

    For j=g-1 we assume L = \{ beta_{g-1}, h_{g-1}, a_{g-1}, alpha_{g-2}, b_{g-2}, T \}.

    For j=g we assume L = \{ alpha_{g-1}, a_g, b_{g-1}, u, T \}.
    
    Finally s equals k_1-k_2.

  SeeAlso
    kustinMillerComplex
  Caveat
    This is not really a user level function, however it is exported as occasionally it can be useful.
    The export may be removed at some point.
///



doc ///
  Key
    shiftComplex
    (shiftComplex,ChainComplex,ZZ)
  Headline
    Shift the indexing of a chain complex
  Usage
    shiftComplex(cc,p)
  Inputs
    cc:ChainComplex
    p:ZZ
  Outputs
    cs:ChainComplex
  Description
   Text
     Shifts the chain complex cc by p, i.e., returns a new chain complex CS
     with cs_i =  cc_{i+p} and the same differentials as cc.     

   Example
     R = QQ[x_1..x_4,z_1..z_4, T]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     cc = res I
     betti cc
     cs=shiftComplex(cc,-3)
     betti cs
  SeeAlso
     res
     betti
///

doc ///
  Key
    dualComplex
    (dualComplex,ChainComplex)
  Headline
    Dualize a chain complex
  Usage
    dualComplex(cc)
  Inputs
    cc:ChainComplex
  Outputs
    dc:ChainComplex
  Description
   Text
     Dualizes the chain complex cc, i.e., dc is the chain complex with modules
     dc_p = (dual cc_(-p)) and  differentials dc_p \to dc_{p-1}   the  transpose of cc_{-p+1} \to cc_p 

     Other than the M2 method (dual,ChainComplex) we do
     not introduce an alternating sign.

   Example
     R = QQ[x_1..x_4,z_1..z_4, T]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     cc = res I
     betti cc
     dc=dualComplex(cc)
     betti dc
  SeeAlso
     (dual,ChainComplex)
///

doc ///
  Key
    unprojectionHomomorphism
    (unprojectionHomomorphism,Ideal,Ideal)
  Headline
    Compute the homomorphism associated to an unprojection pair
  Usage
    unprojectionHomomorphism(I,J)
  Inputs
    J:Ideal
    I:Ideal
        contained in J
  Outputs
    f:Matrix
  Description
   Text
    Compute the deformation associated to the unprojection of I in J (or
    equivalently of J \subset R/I where R=ring(I)), i.e., a homomorphism phi:J \to R/I
    such that the unprojected ideal is given by the ideal

    (T*u-phi(u)| u \in J )

    of R[T].

    The result is represented by a matrix f with @TO source@(f) = @TO image@ @TO gens@ I
    and @TO target@(f) = @TO cokernel@ @TO gens@ I.

   Example
     R = QQ[x_1..x_4,z_1..z_4, T]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     J = ideal (z_1..z_4)
     unprojectionHomomorphism(I,J)
  SeeAlso
    kustinMillerComplex
    differentials
///


doc ///
  Key
    isExact
    (isExact,ChainComplex)
  Headline
    Test whether a chain complex is exact.
  Usage
    isExact(cc)
  Inputs
    cc:ChainComplex
  Outputs
    :Boolean
  Description
   Text
    Test whether a chain complex is exact (except at position 0)

   Example
     R = QQ[x_1..x_4,z_1..z_4]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     cc= res I
     isExact cc
  SeeAlso
    res
///

doc ///
  Key
    (substitute,ChainComplex,Ring)
  Headline
    Substitute a chain complex to a new ring.
  Usage
    substitute(cc,R)
  Inputs
    cc:ChainComplex
    R:Ring
  Outputs
    :ChainComplex
  Description
   Text
    Substitute a chain complex cc to a new ring R.

   Example
     R=QQ[x_1..x_4,z_1];
     cc=res ideal(x_4*x_3, -x_1*x_2+x_4*z_1);
     cs=substitute(cc,QQ[x_1..x_4])
     print cs.dd_1
  SeeAlso
    substitute
///


doc ///
  Key
    stellarSubdivision
    (stellarSubdivision,Complex,Face,PolynomialRing)
  Headline
    Compute the stellar subdivision of a simplicial complex.
  Usage
    stellarSubdivision(D,F,S)
  Inputs
    D:Complex 
        a simplicial complex on the variables of the polynomial ring R.
    F:Face
        a face of D
    S:PolynomialRing
        a polynomial ring in one variable corresponding to the new vertex
  Outputs
    :Complex
        the stellar subdivision of D with respect to F and S
  Description
   Text
        Computes the stellar subdivision of a simplicial complex D by subdividing the face F with a new vertex
        corresponding to the variable of S.
        The result is a complex on the variables of R**S. It is a subcomplex of the simplex on the variables of R**S.
   Example
     R=QQ[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     betti res I
     D=idealToComplex(I)
     fc=facets D
     S=QQ[x_5]
     D5=stellarSubdivision(D,fc#0,S)
     I5=complexToIdeal D5
     betti res I5
   Text

   Example
     R=QQ[x_1..x_6]
     I=ideal(product((entries vars R)#0))
     D=idealToComplex I
     S=QQ[x_7]
     Dsigma=stellarSubdivision(D,face {x_1,x_2,x_3},S)
     betti res complexToIdeal Dsigma
  SeeAlso
     idealToComplex
     facets
     complexToIdeal
///


TEST ///
     K=QQ;
     R=K[x_0..x_4];
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=idealToComplex(I)
     S=K[x_5]
     D5=stellarSubdivision(D,new Face from {x_0,x_2},S)
     I5=complexToIdeal D5
     use ring I5
     assert(I5==ideal(x_4*x_5,x_3*x_5,x_1*x_5,x_3*x_4,x_0*x_4,x_2*x_3,x_1*x_2,x_0*x_2,x_0*x_1));
///




doc ///
  Key
    link
    (link,Face,Complex)
  Headline
    The link of a face of a complex.
  Usage
    link(F)
  Inputs
    F:Face
    C:Complex
  Outputs
    :Complex
  Description
   Text
        The link of the face F of the complex C.
   Example
     R=QQ[x_0..x_4]
     I=ideal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0)
     C=idealToComplex I
     F=(faces C)#1#0
     link(F,C)
     F=(faces C)#2#0
     link(F,C)
  SeeAlso
    idealToComplex
    faces
///


doc ///
  Key
    "Cyclic Polytopes"
  Headline
    Constructing minimal resolutions for Stanley-Reisner rings of boundary complexes of cyclic polytopes
  Description
   Text
    In the following example we construct the minimal resolution of the Stanley-Reisner ring of
    the codimension 4 cyclic polytope {\Delta}(4,8) from those of the
    cyclic polytopes {\Delta}(2,6) and {\Delta}(4,7) (the last one being Pfaffian).

    Of course this process can be iterated, for details see

    {\it J. Boehm, S. Papadakis: On the structure of Stanley-Reisner rings associated to cyclic polytopes}, @HREF"http://arxiv.org/abs/0912.2152"@

   Example
     K=QQ;
     C26=delta(2,K[z,x_2..x_6])
     R=K[z,x_1..x_7]
     J=sub(complexToIdeal C26,R)
     c26=res J;
     betti c26
     C47=delta(4,K[x_1..x_7])
     I=sub(complexToIdeal C47,R)
     c47=res I;
     betti c47
     cc=kustinMillerComplex(c47,c26,K[x_8]);
     betti cc
   Text

     We compare with the combinatorics, i.e., check that
     the Kustin-Miller complex at the special fiber z=0 indeed resolves 
     the Stanley-Reisner ring of {\Delta}(4,8).

   Example
     R'=K[x_1..x_8];
     C48=delta(4,R')
     I48=complexToIdeal C48
     betti res I48
     I48==sub(ideal cc.dd_1,R')
   Text

     We finish the example by printing the differentials of the Kustin-Miller complex:

   Example
     print cc.dd_1
     print cc.dd_2
     print cc.dd_3
  SeeAlso
    kustinMillerComplex
    res
    betti
///

doc ///
  Key
    "Stellar Subdivisions"
  Headline
    The Kustin-Miller complex for stellar subdivisions
  Description
   Text
    We consider a Gorenstein* simplicial complex C and the complex C' obtained by
    stellar subdivision (see @TO stellarSubdivision@) of a face F of C,
    and the corresponding Stanley-Reisner ideals I and I'.

    We construct a resolution of I' from a resolution of I and from a resolution of the
    Stanley-Reisner ideal of the link of F using the Kustin-Miller complex construction 
    implemented in @TO kustinMillerComplex@. Note that this resolution
    is not necessarily minimal (for facets it is).

    For details see

    {\it J. Boehm, S. Papadakis: Stellar subdivisions and Stanley-Reisner rings of Gorenstein complexes}, @HREF"http://arxiv.org/abs/0912.2151"@


    (1) The simplest example:

    The stellar of the edge \{x_1,x_2\}\  of the triangle with vertices x_1,x_2,x_3.
    The new vertex is x_4 and z_1 is the base of the unprojection deformation.

   Example
    K=QQ;
    R=K[x_1..x_3,z_1];
    I=ideal(x_1*x_2*x_3)
    Ilink=I:ideal(x_1*x_2)
    J=Ilink+ideal(z_1)
    cI=res I
    betti cI
    cJ=res J
    betti cJ
    cc=kustinMillerComplex(cI,cJ,K[x_4]);
    S=ring cc
    cc
    betti cc
    isExact cc
    print cc.dd_1
    print cc.dd_2
   Text

    Obviously the ideal resolved by the Kustin-Miller complex at the special fiber z_1=0
    is the Stanley-Reisner ideal of the stellar subdivision (i.e., of a 4-gon).


    (2) Stellar of the facet \{x_1,x_2,x_4,x_6\}\  of the simplicial complex of the complete intersection (x_1*x_2*x_3,x_4*x_5*x_6)
    resulting in a Pfaffian:

   Example
    R=K[x_1..x_6,z_1..z_3];
    I=ideal(x_1*x_2*x_3,x_4*x_5*x_6)
    Ilink=I:ideal(x_1*x_2*x_4*x_6)
    J=Ilink+ideal(z_1*z_2*z_3)
    cI=res I
    betti cI
    cJ=res J
    betti cJ
    cc=kustinMillerComplex(cI,cJ,K[x_7]);
    S=ring cc
    cc
    betti cc
    isExact cc
    print cc.dd_1
    print cc.dd_2
    print cc.dd_3
   Text

    We compare with the combinatorics, i.e., check that the ideal
    resolved by the Kustin Miller complex at the special fiber is the
    Stanley-Reisner ideal of the stellar subdivision:

   Example
    R=K[x_1..x_6];
    C=idealToComplex ideal(x_1*x_2*x_3,x_4*x_5*x_6)
    fvector C
    F=face {x_1,x_2,x_4,x_6}
    R'=K[x_1..x_7];
    C'=substituteComplex(stellarSubdivision(C,F,K[x_7]),R')
    fvector C'
    I'=sub(ideal(cc.dd_1),R')
    C'==idealToComplex I'
   Text

    One observes that in this case the resulting complex is minimal
    This is always true for stellars of facets.


    (3) Stellar of an edge:

   Example
    R=K[x_1..x_5,z_1];
    I=ideal(x_1*x_2*x_3,x_4*x_5)
    C=idealToComplex I
    fvector C
    F=face {x_1,x_2}
    Ilink=I:ideal(product F)
    J=Ilink+ideal(z_1)
    cI=res I
    betti cI
    cJ=res J
    betti cJ
    cc=kustinMillerComplex(cI,cJ,K[x_6]);
    S=ring cc
    cc
    betti cc
    isExact cc
    print cc.dd_1
    print cc.dd_2
    print cc.dd_3
    print cc.dd_4
   Text

    (4) Starting out with the Pfaffian elliptic curve:

   Example
    R=K[x_1..x_5,z_1];
    I=ideal(x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_1)
    Ilink=I:ideal(x_1*x_3)
    J=Ilink+ideal(z_1)
    cI=res I
    betti cI
    cJ=res J
    betti cJ
    cc=kustinMillerComplex(cI,cJ,K[x_10]);
    betti cc
   Text

    (5) One more example of a stellar of an edge starting with a codimension 4 complete intersection:
 
   Example
    R=K[x_1..x_9,z_1];
    I=ideal(x_1*x_2,x_3*x_4,x_5*x_6,x_7*x_8*x_9)
    Ilink=I:ideal(x_1*x_3)
    J=Ilink+ideal(z_1)
    cI=res I
    betti cI
    cJ=res J
    betti cJ
    cc=kustinMillerComplex(cI,cJ,K[x_10]);
    S=ring cc;
    cc
    betti cc
   Text

    We compare again compare with the combinatorics:

   Example
    R=K[x_1..x_9];
    C=idealToComplex sub(I,R)
    fvector C
    F=face {x_1,x_3}
    R'=K[x_1..x_10];
    C'=substituteComplex(stellarSubdivision(C,F,K[x_10]),R')
    fvector C'
    I'=sub(ideal(cc.dd_1),R')
    C'==idealToComplex I'
  SeeAlso
    kustinMillerComplex
    res
    betti
///

doc ///
  Key
    "Tom"
  Headline
    The Kustin-Miller complex for Tom
  Description
   Text
    The Kustin-Miller complex construction for the Tom example which can be found in Section 5.5 of 

    Papadakis, Kustin-Miller unprojection with complexes,  J. Algebraic Geometry 13 (2004) 249-268, @HREF"http://arxiv.org/abs/math/0111195"@

    Here we pass from a Pfaffian to codimension 4.

   Example
     R = QQ[x_1..x_4,z_1..z_4]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     cI=res I
     betti cI
     J = ideal (z_1..z_4)
     cJ=res J
     betti cJ
     cc=kustinMillerComplex(cI,cJ,QQ[T]);
     S=ring cc
     cc
     betti cc
     isExact cc
     print cc.dd_1
     print cc.dd_2
     print cc.dd_3
     print cc.dd_4
  SeeAlso
    kustinMillerComplex
    res
    betti
///


TEST ///
     R = QQ[x_1..x_4,z_1..z_4]
     I =  ideal(z_2*z_3-z_1*z_4,x_4*z_3-x_3*z_4,x_2*z_2-x_1*z_4,x_4*z_1-x_3*z_2,x_2*z_1-x_1*z_3)
     cI=res I
     betti cI
     J = ideal (z_1..z_4)
     cJ=res J
     betti cJ
     cc=kustinMillerComplex(cI,cJ,QQ[T]);
assert(rank(cc#1)==9;
assert(rank(cc#2)==16);
assert(isExact(cc)==true);
///

doc ///
  Key
    subRing
    [link,subRing]
  Headline
    Option to consider the link as a complex on its natural set of vertices
  Description
   Text
    @TO Boolean@ @TO Option@ to consider the link as a complex on its natural set of vertices.
///


{*

*}

-- uninstallPackage("KustinMiller")
-- installPackage("KustinMiller")
-- installPackage("KustinMiller",RerunExamples=>true)
-- viewHelp("KustinMiller")
