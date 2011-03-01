newPackage(
	"RandomCurves",
    	Version => "0.5", 
    	Date => "February 20, 2011",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	            {Name => "Hans-Christian Graf v. Bothmer",
	             Email => "bothmer@uni-math.gwdg.de",
		     HomePage => "http://www.crcg.de/wiki/User:Bothmer"}		 
                   },
    	Headline => "Construction of random smooth curves of various kinds and related computations",
    	DebuggingMode => true
        )

if not version#"VERSION" >= "1.4" then error "this package requires Macaulay2 version 1.4 or newer"

export{"nextPrime",
     "randomRationalPoint",
     "imageUnderRationalMap",
     "randomDistinctPlanePoints",
     "distinctPlanePoints",
     "randomNodalPlaneCurve",
     "searchRandomNodalPlaneCurve",
     "completeLinearSystemOnNodalPlaneCurve",
     "randomSpaceCurve",
     "randomHartshorneRaoModule",
     "knownUnirationalComponentOfSpaceCurves",
     "expectedShape",
     "randomCurveOfGenusUpTo14",
     "randomCurveOfGenus14",
     "randomNormalCurveOfGenus8AndDegree14",
     "randomCurveOfGenus8With8Points",
     "randomCanonicalCurve",
     "Attempts",
     "Certify",
     "InCodim"}

nextPrime=method()
nextPrime ZZ:=n->(
      if n <= 2 then return 2;
      p:=if n%2==0 then n+1 else n;
      while not isPrime p do p=p+2;
      p)

randomRationalPoint=method()
randomRationalPoint Ideal := I->(
     R:=ring I;
     if char R == 0 then error "expected a finite ground field";
     if class R =!= PolynomialRing then error "expected an ideal in a polynomial ring";
     n:=dim I-1;
     if n==0 then error "expected a positive dimensional scheme";
     trial:=1;
     while (
	  -- intersect with a random complementary linear subspace
     	  H:=ideal random(R^1,R^{n:-1});
     	  pts:=decompose (I+H);
     	  pts1:=select(pts,pt-> degree pt==1 and dim pt ==1);
     	  #pts1<1) do (trial=trial+1);
     pts1_0)

imageUnderRationalMap=method()
imageUnderRationalMap(Ideal,Matrix):=(J,L)->(
     if not same degrees source L then error "expected homogeneous forms of a single degree";
     kk:=coefficientRing ring J;
     x := getSymbol "x";
     S:=kk(monoid [x_0..x_(rank source L-1)]);
     RJ:=ring J/J;
     ideal mingens ker map(RJ,S,sub(L,RJ))     
     )

randomDistinctPlanePoints=method(TypicalValue=>Ideal,Options=>{Certify=>false,Attempts=>infinity})
randomDistinctPlanePoints(ZZ,PolynomialRing):=opt->(k,R)->(
     if dim R != 3 then error "expected a polynomial ring in three variables";
     if degrees R !={{1}, {1}, {1}} then error "polynomial ring is not standard graded";
     if not ( instance(opt.Attempts, ZZ) and opt.Attempts > 0 or opt.Attempts === infinity )
          then error "Attempts: expected a positive integer or infinity";
	  
     n := ceiling((-3+sqrt(9.0+8*k))/2); 
     eps := k-binomial(n+1,2);
     for i from 1 do (
	  if i > opt.Attempts then error "failed to find distinct points";
	  -- a random Hilbert-Burch matrix:
	  B := random(R^{n+1-eps:0,2*eps-n:-1},R^{n-2*eps:-1,eps:-2});
	  I := minors(rank source B,B);
     	  if not opt.Certify or distinctPlanePoints I then return I; 
	  ))

distinctPlanePoints=method(TypicalValue=>Boolean);
distinctPlanePoints Ideal:= I-> dim I==1 and dim (I+minors(2,jacobian I))<=0
distinctPlanePoints List:= L-> degree intersect L == sum(L,I->degree I)

randomNodalPlaneCurve=method(TypicalValue=>Ideal,Options=>{Certify=>false,Attempts=>infinity})
randomNodalPlaneCurve(ZZ,ZZ,PolynomialRing):=opt->(d,delta,R)->(
     if dim R != 3 then error "expected a polynomial ring in three variables";
     if degrees R !={{1}, {1}, {1}} then error "polynomial ring is not standard graded";
     if not ( instance(opt.Attempts, ZZ) and opt.Attempts > 0 or opt.Attempts === infinity )
          then error "Attempts: expected a positive integer or infinity";
     -- choose delta distinct random plane points
     I:= (
	  if opt.Certify then randomDistinctPlanePoints(delta,R,Certify=>true) 
	  else if opt.Attempts>0 then randomDistinctPlanePoints(delta,R,Attempts=>opt.Attempts) 
	  else randomDistinctPlanePoints(delta,R)
	  );
     if I==0 then return ideal 0_R;
     -- choose (if possible) a curve of deg d with double points in the given points
     I2:=gens saturate(I^2); f:= 0_R;
     if all(degrees source I2,c->c_0 > d) then return ideal 0_R ;
     while(f=I2*random(source I2,R^{-d});f==0) do ();
     if not opt.Certify and opt.Attempts==0 then return ideal f; 
     singF:=ideal f + ideal jacobian f;
     ok:= degree singF == delta and dim singF <= 1;
     if opt.Certify and ok then return ideal f; 
     count:=1;
     if opt.Attempts<=1 then return ideal 0_R else 
     	  while count < opt.Attempts and not ok do (
	       count=count+1;
	       I=randomDistinctPlanePoints(delta,R,Certify=>true);
	       I2=gens saturate(I^2);
	       -- if not any(degrees source I2,c->c_0<= d) == 0 then (f = 0_R; break)
	       -- FG: did you mean the following: 
	       if not any(degrees source I2,c->c_0<= d) then (f = 0_R; break)
     	       else while(
		    f=I2*random(source I2,R^{ -d });
		    f==0) do ();
	       singF=ideal f + ideal jacobian f;
	       ok = degree singF==delta and dim singF <= 1;
	       not ok); 
     ideal if ok then f else  0_R)

completeLinearSystemOnNodalPlaneCurve=method()
completeLinearSystemOnNodalPlaneCurve(Ideal,List):=(J,D)->(
     singJ:=saturate(ideal jacobian J+J);-- adjoint ideal
     H:=ideal (mingens ideal(gens intersect(singJ,D_0) %J))_(0,0);
     E0:=((J+H):D_0):(singJ^2); -- residual divisor   
     assert(degree J *degree H - degree D_0 -2*degree singJ==degree E0);
     L1:=mingens ideal (gens truncate(degree H, intersect(E0,D_1,singJ)))%J;
     h0D:=(tally degrees source L1)_{degree H}; -- h^0 O(D)
     L:=L1_{0..h0D-1}; -- matrix of homogeneous forms, L/H =L(D) subset K(C) 
     (L,(gens H)_(0,0)))

searchRandomNodalPlaneCurve=method(TypicalValue=>Ideal,Options=>{Certify=>false,Attempts=>infinity,InCodim=>-1})
searchRandomNodalPlaneCurve(ZZ,ZZ,PolynomialRing):=opt->(d,delta,R)->(
     p:=char R;
     expectedCodim:=3*delta-binomial(d+2,2)+1;
     cd:=max(expectedCodim,opt.InCodim);
     t1:=cpuTime();
     I:=randomNodalPlaneCurve(d,delta,R);
     apply(9,i-> (randomNodalPlaneCurve(d,delta,R)));
     t2:=cpuTime();     
     t:=p^cd*(t2-t1)/10;
     if t < 60.0 then print ("-- estimated expected running time "| toString t | " seconds")
     else if t/60 < 60.0 then print( "-- estimated expected running time "|toString (t/60) | " minutes")
     else if t/60/60 < 24.0 then print( "-- estimated expected running time " |toString (t/60/60) | " hours") 
     else print( "-- roughly expected running time "| toString (t/60/60/24)| " days");
     count:=0;
     maxcount:=if opt.Attempts==infinity then 2*p^cd else opt.Attempts;
     while ( degree I =!= d and count<maxcount) do (
	  I=randomNodalPlaneCurve(d,delta,R,Certify=>opt.Certify);count=count+1);
     I)

randomSpaceCurve=method(TypicalValue=>Ideal,Options=>{Attempts=>0,Certify=>false})
randomSpaceCurve(ZZ,ZZ,PolynomialRing) := opt->(d,g,R)->(			 
     if not knownUnirationalComponentOfSpaceCurves(d,g) then return null;
     G:=expectedShape(d,g,3);
     n:=4;
     while  d*n+1-g>binomial(n+3,3)  do n=n+1;
     HRao1:=select(
	  apply(toList(1..n),j->(j,max(d*j+1-g-binomial(3+j,3),0))),
	  i-> i_1 !=0);
     HRao:=apply(HRao1,i->i_1);
     if #HRao==0 then (
	  if length G !=2
	  then error "cannot be ACM" 
	  else return minors(rank G_2,random(R^(-degrees G_1),R^(-degrees G_2)))
	  );
     e:=HRao1_0_0;
     M:=randomHartshorneRaoModule(d,g,R);     	       
     fM:=res( M);
     t1:=tally degrees fM_3;
     t2:=tally degrees G_2;
     t3:=unique degrees G_2;
     H:=R^(apply(t3,d->t2_d-t1_d:-d));
     phi:= fM.dd_3++id_H;
     N:=random(R^(-degrees G_1),target phi)*phi;
     J:=ideal syz transpose N;
     if not opt.Certify then return J;
     singJ := minors(2,jacobian J)+J;
     if dim singJ==0 and dim M==0 then return J;
     if opt.Attempts<= 0 then return null;
     J=randomSpaceCurve(d,g,R,opt.Certify=>true,Attempts=>opt.Attempts-1);
     J)

knownUnirationalComponentOfSpaceCurves=method()
knownUnirationalComponentOfSpaceCurves(ZZ,ZZ) := (d,g)->(
     n:=4;
     while 
     d*n+1-g>binomial(n+3,3)  
     do n=n+1;
     HRao1:=select(apply(toList(1..n),n->(n,max(d*n+1-g-binomial(3+n,3),0))), i-> i_1 !=0);
     G:=expectedShape(d,g,3);
     if length G >3 then return false;
     if #HRao1 >3 then return false;
     if #HRao1 <=1 then return true;
     HRao:=apply(HRao1,i->i_1);
     if #HRao <=2 then if HRao=={1,1} or HRao=={2,1} or HRao=={1,2} then return false else return true;
     a:=HRao_0,b:=HRao_1,c:=HRao_2;
     b>=4*a or b>=4*c
     or
     b<4*a and -6*a+4*b-c>=0
     or
     b<4*c and -6*c+4*b-a>=0
     or
     b<4*a and 6*c-4*b+a>0 and 4*(4*c-b)-10*(6*c-4*b+a)>=c
     or
     b<4*c and 6*a-4*b+c>0 and 4*(4*a-b)-10*(6*a-4*b+c)>=a
     )

randomHartshorneRaoModule=method(TypicalValue=>Module,Options=>{Attempts=>0})
randomHartshorneRaoModule(ZZ,ZZ,PolynomialRing):=opt->(d,g,R)->(
     if not knownUnirationalComponentOfSpaceCurves(d,g) then 
     error ("no construction implemented for degree ",toString d, " and genus ", toString g);
     G:=expectedShape(d,g,3);
     --if length G>3 then error "either 2H special or not of maximal rank";
     n:=4;
     while d*n+1-g>binomial(n+3,3) do n=n+1;
     HRao1:=select(apply(toList(1..n),n->(n,max(d*n+1-g-binomial(3+n,3),0))), i-> i_1 !=0);
     HRao:=apply(HRao1,i->i_1);
     e:=HRao1_0_0;
     M:=randomHartshorneRaoModule(e,HRao,R);
     attempt:=1;
     while true do (
     	  if apply(toList(e..e+#HRao-1),i->hilbertFunction(i,M))==HRao then return M;
	  if opt.Attempts <= attempt then return null;
	  M=randomHartshorneRaoModule(e,HRao,R);
	  attempt=attempt+1;
	  ))

randomHartshorneRaoModule(ZZ,List,PolynomialRing):=opt->(e,HRao,R)->(
     if dim R != 4 then error "expected a polynomial ring in 4 variables";
     if degrees R !={{1}, {1}, {1}, {1}} then error "polynomial ring is not standard graded";
     if #HRao > 3 then error "no method implemented for Hartshorne Rao modue of diameter >3";
     trybackwards:=false;
     M:=coker(matrix{{1_R}});sb:=M;A:=M;
     a:=0;b:=0;c:=0;b1:=0;b2:=0;b3:=0;c2:=0;a2:=0;
     if #HRao==1 then (a=HRao_0;M=coker (vars R**R^{a:-e}));
     if #HRao==2 then (
	 a=HRao_0;
	 b=HRao_1;
         if b>= 4*a then M=coker(random(R^{a:0,b-4*a:-1},R^{10*a+4*(b-4*a):-2})**R^{ -e }) 
	 else if 10*a-4*(4*a-b)<0 then M=coker(random(R^a,R^{4*a-b:-1})**R^{ -e }) 
	 else M=coker(random(R^a,R^{4*a-b:-1,10*a-4*(4*a-b):-2})**R^{ -e }));
     if #HRao==3 then (
	  a=HRao_0;b=HRao_1;c=HRao_2;b1=4*a-b;
	  if b1>=0 then (
	       b2=10*a-4*b1-c;
	       if b2>0 then (
		     b3=20*a-10*b1-4*b2; 
	             if b3>0 then M=coker(random(R^a,R^{b1:-1,b2:-2,b3:-3})**R^{ -e })
		     else M=coker(random(R^a,R^{b1:-1,b2:-2})**R^{ -e }))
	       else (
		    c2=-b2;
		    if -10*c2+4*b1<a then trybackwards=true 
		    else (
			 sb=syz random(R^c2,R^{b1:-1});
			 A=sb*random(source sb, R^{a:-2});
			 M=coker( map( R^{a:-e},R^{b1:-e-1},transpose A));)
		    ))
	   else (
	       a2=-b1;
	       b2=10*a+4*a2-c;	       
	       if b2>0 then (
		    b3=20*a+10*a2-4*b2;
	            if b3>0 then M=coker(random(R^a,R^{b1:-1,b2:-2,b3:-3})**R^{-e})
		    else M=coker(random(R^{a:0,a2:-1},R^{b2:-2})**R^{-e}))
	       );
        if trybackwards then (
	  a=HRao_2;b=HRao_1;c=HRao_0;b1=4*a-b;
	  if b1>=0 then (
	       b2=10*a-4*b1-c;
	       if b2>0 then (
		     b3=20*a-10*b1-4*b2; 
	             if b3>0 then M=coker(random(R^a,R^{b1:-1,b2:-2,b3:-3}))
		     else M=coker(random(R^a,R^{b1:-1,b2:-2})))
	       else (
		    c2=-b2;
		    if -10*c2+4*b1<a then error ("no method to construct a natural module with Hilbert function", toString (c,b,a)) 
		    else (
			 sb=syz random(R^c2,R^{b1:-1});
			 A=sb*random(source sb, R^{a:-2});
			 M=coker( map(R^{a:0},R^{b1:-1},transpose A));)))
	  else (
	       a2=-b1;b2=10*a+4*a2-c;
	       if b2>0 then (
		    b3=20*a+10*a2-4*b2;
		    if b3>0 then M=coker(random(R^{a:0,a2:-1},R^{b2:-2,b3:-3}))
		    else M=coker(random(R^{a:0,a2:-1},R^{b2:-2})););
	       );
          fM:=res M;
	  M=(coker transpose fM.dd_4)**R^{-e-6});
	  );
     M)

expectedShape=method()
expectedShape(RingElement):= q ->(
     cq:=coefficients q;
     mons1:=(entries cq_0)_0;
     ranks1:=apply(entries cq_1,r->r_0);
     m:=#mons1;
     ranks:=apply(m,i->lift(ranks1_(m-i-1),ZZ));
     mons:=apply(m,i->mons1_(m-i-1));
     degs:=apply(m,i->degree mons_i);
     switches:=select(toList(0..m-2),i->ranks_i*ranks_(i+1)<0);
     pd:=#switches;
     T:=ring q;
     F:=new ChainComplex;
     F.ring=T;
     F_0=T^(apply(toList(0..switches_0),i->ranks_i:-degs_i));
     j:=0;
     while j<pd-1 do (
         F_(j+1)=T^(apply(toList(switches_j+1..switches_(j+1)),i->abs(ranks_i):-degs_i));
     	 j=j+1);
    F_pd=T^(apply(toList(switches_(pd-1)+1..#mons-1),i->abs(ranks_i):-degs_i));
    F_(pd+1)=T^0;
    F)

expectedShape(ZZ,ZZ,ZZ):=(d,g,r)->(
     -- we assume C non-degenerate, O_C(2) nonspecial and maximal rank
     t:=symbol t;
     T:=ZZ[t];
     b:=d+r+1;
     p:=sum(b,i->(if i>1 then min(d*i+1-g,binomial(r+i,r)) else binomial(r+i,r))*t^i);
     q:=p*(1-t)^(r+1)%t^b;
     expectedShape q)

randomCurveOfGenusUpTo14=method(TypicalValue=>Ideal,Options=>{Certify=>false})
randomCurveOfGenusUpTo14(ZZ,Ring):= opt -> (g,F)->(
     if g>14 or g<4 then error "no method implemented";
     x:= local x;
     R:=F;d:=0;
     if g<=10 then (
	  if isField F then R=F[x_0..x_2];
	  if numgens R =!= 3 then error "expected a ring with 3 variables or a field";
	  s:=floor(g/3); -- the speciality of a plane model of minimal degree
	  d=g+2-s; -- the degree of the plane model
	  delta:=binomial(d-1,2)-g; -- the number of double points of the plane model
	  return randomNodalPlaneCurve(d,delta,R,Certify=>opt.Certify))
     else if g<14 then (
	  if isField F then R=F[x_0..x_3];
          if numgens R =!= 4 then error "expected a ring with 4 variables or a field";     
          d = if g==11 then g-1 else g;
	  return randomSpaceCurve(d,g,R,Certify=>opt.Certify))
     else (
	  if isField F then R=F[x_0..x_6];
	  if numgens R =!= 7 then error "expected a ring with 7 variables or a field";
	  return randomCurveOfGenus14(R,Certify=>opt.Certify))
     )

randomCurveOfGenus8With8Points=method(Options=>{Certify=>false})
randomCurveOfGenus8With8Points(PolynomialRing) := opt-> R ->(
     --Input: R a polynomial ring in 8 variables, 
     --Output: a pir of an ideal of a canonical curve C
     --        together with a list of ideals of 8 points
     --Method: Mukai's structure theorem on genus 8 curves.
     --  Note that the curves are have general Clifford index. 
     FF:=coefficientRing R;
     p:=symbol p;
     -- coordinate ring of the Plucker space:
     P:=FF[flatten apply(6,j->apply(j,i->p_(i,j)))]; 
     skewMatrix:=matrix table(6,6,
	  (i,j) -> (
	       if i<j then p_(i,j)
	       else if i>j then -p_(j,i)
	       else 0_P));
     -- ideal of the Grassmannian G(2,6):
     IGrass:=pfaffians(4,skewMatrix);
     points:=apply(8,k->exteriorPower(2,random(P^2,P^6)));
     ideals:=apply(points,pt->ideal( vars P*(syz pt**P^{-1})));  
     -- linear span of the points:
     L1 := intersect ideals;
     if opt.Certify then if degree L1 != 8 then return (null,null);
     L:= super basis(1,L1);
     if opt.Certify then if dim ideal L != 8 then return (null,null);
     phi:=vars P%L; -- coordinates as function on the span
     -- actually the last 8 coordinates represent a basis
     phi2:= matrix{toList(7:0_R)}|vars R; 
     -- matrix for map from R to P/IC
     IC:=ideal (gens IGrass%L); --the ideal of C on the span
     -- obtained as the reduction of the Grassmann equation mod L
     IC2:=ideal mingens substitute(IC,phi2);
     idealsOfPts:=apply(ideals,Ipt->
         ideal mingens ideal sub(gens Ipt%L,phi2));
     (IC2,idealsOfPts))

randomNormalCurveOfGenus8AndDegree14=method(TypicalValue=>Ideal,Options=>{Certify=>false})
randomNormalCurveOfGenus8AndDegree14(PolynomialRing) := opt-> S -> (
     -- Input:  S coordinate ring of P^6
     -- Output: ideal of a curve in P^6
     x:=symbol x;
     FF:=coefficientRing S;
     R:=FF[x_0..x_7];
     (I,points):=randomCurveOfGenus8With8Points(R,Certify=>opt.Certify);
     if I === null then return null;
     D1:=intersect apply(4,i->points_i); -- divisors of degree 4 
     D2:=intersect apply(4,i->points_(4+i));
     -- compute the complete linear system |K+D1-D2|, note K=H1
     H1:=gens D1*random(source gens D1,R^{-1});
     E1:=(I+ideal H1):D1; -- the residual divisor
     L:=mingens ideal(gens intersect(E1,D2)%I); 
     if opt.Certify then if source L != R^{7:-2} then return null;
     -- the complete linear system
     -- note: all generatore of the intersection have degree 2.
     RI:=R/I; -- coordinate ring of C' in P^7
     phi:=map(RI,S,substitute(L,RI));
     ideal mingens ker phi)

randomCurveOfGenus14=method(TypicalValue=>Ideal,
     Options=>{Certify=>false})
-- The default value of the option Certify is false, because 
-- certifying smoothness is expensive
randomCurveOfGenus14 PolynomialRing :=opt ->( S-> (
     -- Input: S PolynomialRing in 7 variables
     -- Output: ideal of a curve of genus 14
     -- Method: Verra's proof of the unirationality of M_14
     IC':=randomNormalCurveOfGenus8AndDegree14(S,Certify=>opt.Certify);
     if IC'===null then return null;
     -- Choose a complete intersection:
     CI:=ideal (gens IC'*random(source gens IC',S^{5:-2}));
     IC:=CI:IC'; -- the desired residual curve
     if not opt.Certify then return IC;
     if not (degree IC ==18 and codim IC == 5 and genus IC ==14) 
        then return null;
     someMinors :=minors(5, jacobian CI);
     singCI:=CI+someMinors;
     if not (degree singCI==28 and codim singCI==6) 
        then return null;
     someMoreMinors:=minors(5, jacobian (gens IC)_{0..3,5});
     singC:=singCI+someMoreMinors;
     if codim singC == 7 then return IC else return null))

randomCanonicalCurve=method(TypicalValue=>Ideal,Options=>{Certify=>false})
randomCanonicalCurve(ZZ,PolynomialRing) := opt ->(g,R)->(
     if numgens R != g then error ("expected a polynomial ring in ",toString g," variables");
     if g>14 then error "no method known or implemented for curves of genus >14";
     if g<=2 then error "for g<=2 the canonical system is not very ample";
     I:= ideal 0_R; 
     ok:= not opt.Certify;
     FF:=coefficientRing R;
     x:=symbol x;S:=FF[x_0..x_2];
     if g==3 then while (
	  I=ideal random(4,R); 
	  if opt.Certify then ok=codim ((ideal jacobian I)+I)==3;
	  ok) do return I;
     --if g==4 then while (I=ideal random (R^1,R^{-2,-3}; 
     -- 	  if opt.Certify then ok=codim ((ideal jacobian I)+I)==4;
     -- 	  ok) do return I;
     if g<=10 and g>=4 then ( -- Severi's approach
	  --apply(4..10,g->(d=ceiling((2*g+6)/3);delta=binomial(d-1,2)-g;(g,d,delta)))
	  d:=ceiling((2*g+6)/3); -- rho = g-3*(g+2-d) >=0 <=> d>=(2g+6)/3
	  delta:=binomial(d+2,2)-g;
	  J:=randomNodalPlaneCurve(d,delta,S,Certify=>opt.Certify);
	  KC:=(gens intersect(saturate(ideal jacobian J +J),(ideal vars S)^{d-3}))_{0..(g-1)};
	  SJ:=S/J;
	  phi:=map(SJ,R,substitute(KC,SJ));
	  I=ideal mingens ker phi;
	  return I);
     y:=symbol y;
     --FF=ZZ/101;g=11;R=FF[x_0..x_(g-1)]
     S=FF[y_0..y_3];RS:=R**S;omegaC:=0;graph:=0;     
     if g==11 then (
	  I=randomSpaceCurve(12,g,S,Certify=>opt.Certify);
	  omegaC=presentation prune truncate(0,Ext^1(I,S^{-4}));
     	  graph=substitute(vars R,RS)*substitute(omegaC,RS);	  	    
	  time J=saturate(ideal graph,substitute(y_0,RS));	  
          I=ideal mingens substitute(J,R);
	  return I);
     if g==12 then (
	  I=randomSpaceCurve(12,g,S,Certify=>opt.Certify);
	  omegaC=presentation prune truncate(0,Ext^1(I,S^{-4}));
     	  graph=substitute(vars R,RS)*substitute(omegaC,RS);	  	    
	  time J=saturate(ideal graph,substitute(y_0,RS));	  
          I=ideal mingens substitute(J,R);
	  return I);
      if g==13 then (
	   I=randomSpaceCurve(13,g,S,Certify=>opt.Certify);
	  omegaC=presentation prune truncate(0,Ext^1(I,S^{-4}));
     	  graph=substitute(vars R,RS)*substitute(omegaC,RS);	  	    
	  time J=saturate(ideal graph,substitute(y_0,RS));	  
          I=ideal mingens substitute(J,R);
	  return I);
     S=FF[y_0..y_6];RS=R**S;
     --g=14,R=FF[x_0..x_13]
     if g==14 then (
	  I=randomCurveOfGenus14(S,Certify=>opt.Certify);
     	  fI:=res I;
	  omegaC=presentation truncate(0,((coker transpose fI.dd_5)**S^{-7}));
     	  graph=substitute(vars R,RS)*substitute(omegaC,RS);	  	    
	  J=saturate(ideal graph,substitute(y_0,RS));	  
          I=ideal mingens substitute(J,R);
     	  --genus I==g and degree I == 2*g-2
	  return I)
     )	  


beginDocumentation()

doc ///
  Key
    nextPrime
    (nextPrime,ZZ)
  Headline
    compute the smallest prime greater than or equal to n
  Usage
    nextPrime n
  Inputs
    n: ZZ
  Outputs
    p: ZZ
        the smallest prime $p \ge n$
  Description
     Example
       p=nextPrime 10000
///

doc ///
  Key
    randomRationalPoint
    (randomRationalPoint,Ideal)
  Headline
    pick a random rational point on the variety defined by an ideal
  Usage
    randomRationalPoint I
  Inputs
    I: Ideal
       in a polynomial ring over a finite ground field K
  Outputs
     : Ideal 
       of a K-rational point on V(I)
  Description
     Text
        We look for a K-rational point in a random intersection 
        of X with a complementary linear subspace. 
     Example
        p=nextPrime 10000
	kk=ZZ/p
	R=kk[x_0..x_3]
        I=ideal(random(4,R),random(10,R)); 
        time randomRationalPoint I  
  Caveat
     The scheme needs to have at least one K rational point. Otherwise the function does not halt.   
/// 


doc ///
  Key 
    imageUnderRationalMap
    (imageUnderRationalMap,Ideal,Matrix)
  Headline
    Compute the image of the scheme under a rational map 
  Usage
    I = imageUnderRationalMap(J,L) 
  Inputs
    J: Ideal 
       in a polynomial ring
    L: Matrix
       of homogeneous polynomials of equal degrees
  Outputs
    I: Ideal
       of the image of the scheme defined by J under the rational map defined by L
  Description
     Example
       p=nextPrime 10000
       kk=ZZ/p
       R=kk[t_0,t_1]
       I=ideal 0_R
       L=matrix{{t_0^4,t_0^3*t_1,t_0*t_1^3,t_1^4}}  
       J=imageUnderRationalMap(I,L)
       betti J
///
doc ///
  Key
    randomDistinctPlanePoints
    (randomDistinctPlanePoints,ZZ,PolynomialRing)
    [randomDistinctPlanePoints,Certify]
    [randomDistinctPlanePoints,Attempts]
  Headline
    Generates the ideal of k random points in the coordinate ring $R$ of $\\P^{ 2}$ 
  Usage
    I = randomDistinctPlanePoints(k,R)
  Inputs
    k:ZZ
        the number of points
    R:PolynomialRing
    	 homogeneous coordinate ring of $\PP^{ 2}$
    Certify => Boolean
       whether to certify the result
    Attempts => ZZ
       the maximum number of times to try to find an example
  Outputs
    I :Ideal 
          of the points.
  Description
   Text
     Creates the ideal of the points via a random choice of their 
     Hilbert-Birch matrix, which is taken to be of generic shape.
   Example
     kk=ZZ/101;	
     R=kk[x_0..x_2];
     I=randomDistinctPlanePoints(5,R,Attempts=>infinity)
  SeeAlso
     distinctPlanePoints
///


doc ///    
  Key
    distinctPlanePoints
  Headline
    Checks whether the input describes distinct points
///

doc ///
  Key
    (distinctPlanePoints,Ideal)
  Headline  
    Checks whether the ideal I defines points in $\PP^2$ with their reduced structure
  Usage
    distinctPlanePoints I
  Inputs
    I:Ideal 
         which defines a subscheme of $\PP^2$
  Outputs
    :Boolean 
  Description
   Text 
     Checks whether the ideal I defines points in $\PP^2$ with their reduced 
     structure via the Jacobian criterion.
   Example
     R = QQ[x,y,z]
     distinctPlanePoints ideal(x,y*z)  
     distinctPlanePoints ideal(x,y^2)  
  SeeAlso
     randomDistinctPlanePoints
///

doc ///    
  Key
    (distinctPlanePoints,List)
  Headline
    whether the collections have points in common
  Usage
    distinctPlanePoints L
  Inputs
    L:List 
        of ideals of collections of points in $\PP^2$
  Outputs
    :Boolean 
       whether the collections have points in common or not.
  Description
   Example
     R = QQ[x,y,z]
     distinctPlanePoints {ideal(x,y),ideal(x,z)}
     distinctPlanePoints {ideal(x,y),ideal(x+y,x-y)}
  SeeAlso
     randomDistinctPlanePoints
///

doc ///
  Key
    randomNodalPlaneCurve
    (randomNodalPlaneCurve,ZZ,ZZ,PolynomialRing)
    [randomNodalPlaneCurve,Certify]
    [randomNodalPlaneCurve,Attempts]
  Headline
    create the ideal of a random nodal plane curve
  Usage
    I = randomNodalPlaneCurve(d,delta,R)
  Inputs
    d:ZZ 
        the desired degree, 
    delta: ZZ
          the desired number of nodes,
    R:PolynomialRing
          the homogeneous coordinate ring of $\PP^2$.
    Certify => Boolean
       whether to certify the result
    Attempts => ZZ
       the maximum number of times to try to find an example
  Outputs
    I :Ideal 
          of a random nodal plane curve curve 
  Description
   Text 
      The procedure starts by choosing 
      
      1) an ideal I of delta random points in $\PP^2$, and then returns
  
      2) the principal ideal generated by an random element in the saturated square J=saturate(I^2) of degree d.
      
      If the procedure fails, for example if J_d=0, then the zero ideal is returned.
      Under the option {\tt Certified=>true}, the result is certified by establishing that
       
      1) the points are distinct nodes, and that
	
      2) the curve has ordinary nodes at these points
	
      by using the Jacobian criterion applied to the singular locus of the curve.
      Under the option {\tt Attempts=>n}, the program makes {\tt n} attempts in both steps to achieve the desired goal.
      Here {\tt n} can be infinity. 
   Example
      kk=ZZ/101
      R=kk[x_0..x_2]
      randomNodalPlaneCurve(5,6,R,Certify=>true)
  SeeAlso
     randomDistinctPlanePoints
     distinctPlanePoints  
     completeLinearSystemOnNodalPlaneCurve
     searchRandomNodalPlaneCurve
///

doc ///
  Key
    completeLinearSystemOnNodalPlaneCurve 
    (completeLinearSystemOnNodalPlaneCurve,Ideal,List)
  Headline
    Compute the complete linear system of a divisor on a nodal plane curve
  Usage
    (L,h)=completeLinearSystemOnNodalPlaneCurve(I,D)
  Inputs
    I:Ideal 
        of a nodal plane curve C, 
    D: List
        \{D_0,D_1\} of ideals representing effective divisors on C
  Outputs
    L:Matrix
      of homogeneous forms with 1 row and with number of columns equal to $h^0(D_0-D_1)$
    h:RingElement
      such that L_{(0,i)}/h represents a basis of $H^0 O(D_0-D_1)$
  Description
   Text 
     Compute the complete linear series of D_0-D_1 on the normalization of C
     via adjoint curves and double linkage.
  SeeAlso
     randomNodalPlaneCurve
     searchRandomNodalPlaneCurve
///
      

doc ///
  Key
    searchRandomNodalPlaneCurve
    (searchRandomNodalPlaneCurve,ZZ,ZZ,PolynomialRing)
    [searchRandomNodalPlaneCurve,Certify]
    [searchRandomNodalPlaneCurve,Attempts]
    [searchRandomNodalPlaneCurve,InCodim]
  Headline
    Search for a random nodal plane curve and returns its ideal
  Usage
    searchRandomNodalPlaneCurve(d,delta,R)
  Inputs
    d:ZZ 
        the desired degree, 
    delta: ZZ
          the desired number of nodes,
    R:PolynomialRing
          the homogeneous coordinate ring of $\PP^2$.
    Certify => Boolean
       whether to certify the result
    Attempts => ZZ
       the maximum number of times to try to find an example
    InCodim => ZZ
       the expected codimension of the desired objects within the family 
  Outputs
    :Ideal 
         
  Description
   Text 
      The procedure starts by choosing 
      
      1) an ideal I of delta random points in $\PP^{ 2}$, and then returns
  
      2) the principle ideal generated by an random element in the saturated square J=saturate(I^2) of degree d.
      
      For a general set of points J_d=0, hence the procedure fails. However we repeat these steps until we
      are lucky and hit a case with J_d nonzero. In view of the Weil formulas the expected running time
      depends on the time t_1 to compute I and J_d once, the codimension c of the desired locus and 
      the number of elements q in the finite ground field :
      	   t_1*q^c.
   Text	   
      An estimate of this quantity is displayed. 
      Under the option Certify=>true, the result is certified by establishing, that
       
      1) the delta points are distinct nodes, and that
	
      2) the curve has ordinary nodes in these points and no further singularities.
	
      by using the jacobian criterion applied to the singular locus of the curve. In case of failure
      we continue the search. 
      Under the option Attempts=>n, the program makes n attempts at most to achieve the desired goal.
      n can be infinity. In case the option InCodim=>c, the naive computation of c is replaced by this value.
      In case of final failure the zero ideal is returned.

      If {\tt InCodim=>c} is specified, then the expected running time of the algorithm is 
      roughly t*q^c, where t is the CPU time required to rule out one non-example, 
      and q is the number of field elements.
      The expected running time is printed.

   Example 
       kk=ZZ/19;
       R=kk[x_0..x_2];
       d=6;delta=10;
   Text
       We compute the expected codimension:
   Example
       c = 3*delta-binomial(d+2,2)+1
       setRandomSeed "beta"
       time I=searchRandomNodalPlaneCurve(d,delta,R,InCodim=>c,Certify=>true)
       singI=saturate(I+ideal jacobian I)
       betti singI
       dim singI==1, degree singI==delta
       dim (singI+minors(2,jacobian singI))==0   
   Text
       We offer another example.
   Example 
       kk=ZZ/5;
       R=kk[x_0..x_2];
       d=6,delta=10
       c = 3*delta-binomial(d+2,2)+1
       setRandomSeed "alpha";
       time I=searchRandomNodalPlaneCurve(d,delta,R,Certify=>true)
       singI=saturate(I+ideal jacobian I)
       betti singI
       dim singI==1, degree singI==delta
       dim (singI+minors(2,jacobian singI))==0      
  SeeAlso
     randomNodalPlaneCurve     
///     

doc ///
  Key
    randomSpaceCurve
    (randomSpaceCurve,ZZ,ZZ,PolynomialRing)
    [randomSpaceCurve,Certify]
    [randomSpaceCurve,Attempts] 
  Headline
    Generates the ideal of a random space curve of genus g and degree d
  Usage
    randomSpaceCurve(d,g,R)
  Inputs
    d:ZZ
        the desired degree
    g:ZZ
        the desired genus
    R:PolynomialRing
    	 homogeneous coordinate ring of $\PP^{ 3}$
    Certify => Boolean
       whether to certify the result
    Attempts => ZZ
       the maximum number of times to try to find an example
  Outputs
    :Ideal 
          of R
  Description
   Text
     Creates the ideal of a random curve of degree d and genus g via the construction of its expected 
     Hartshorne-Rao module, which should have diameter $\le 3$. 
   Text
     The construction is implemented for non-degenerate, linearly normal curves C of maximal rank with O_C(2) non-special, where moreover
     both C and its Hartshorne-Rao module
     have a "natural" free resolution. There are 63 possible families satifying the four conditions above. 
     Our method can provide random curves in 60 of these families, simultaneously proving the unirationality of each of these 60 components of the 
     Hilbert scheme. 
   Example
     R=ZZ/20011[x_0..x_3];
     d=10;g=7;
     betti res (J=randomSpaceCurve(d,g,R))
     betti res randomHartshorneRaoModule(d,g,R)
     degree J==d and genus J == g
   Text
     We verify that the Hilbert scheme has (at least) 60 components consisting of smooth non-degenerate curves
     with $h^1 O_C(2)=0$. The degree d, genus g and Brill-Noether number $\rho$ of these families and the generic Betti tables
     are given below.
   Example
     kk=ZZ/20011;
     R=kk[x_0..x_3];
     L=flatten apply(toList(0..40),g->apply(toList(3..30),d->(d,g)));
     halpenBound = d ->(d/2-1)^2;
     L = select(L,(d,g) -> 
	  g <= halpenBound d
	  and
	  knownUnirationalComponentOfSpaceCurves(d,g));
     #L
     hashTable apply(L,(d,g) -> (
	       J = randomSpaceCurve(d,g,R);
	       assert (degree J == d and genus J == g);
	       (d,g) => g-4*(g+3-d) => betti res J))
///
   

doc ///
  Key 
    knownUnirationalComponentOfSpaceCurves
    (knownUnirationalComponentOfSpaceCurves,ZZ,ZZ)
  Usage 
    knownUnirationalComponentOfSpaceCurves(d,g)
  Inputs
    d: ZZ
    g: ZZ
  Outputs
     : Boolean
	  whether there is a component of maximal rank curves of degree d 
	  and genus g in $\PP^{ 3}$ with O_C(2) non-special and Hartshorne-Rao module of diameter $\le 3$
	  that have a natural free resolution
  Description
    Text
      For diameter = 3 the construction is possible
      unless the expected Betti table of the Hartshorne-Rao module has shape
    
     a b c1 - - 
     
     - - c2 - -
      
     - - c3 d e 
    
     with both 4b-10c1 < a and 4d-10c3 < e. For diameter > 4 the routine returns false,
     though we actually do know a couple of constructions which work in a few further cases.
///

doc ///
  Key 
    randomHartshorneRaoModule
    (randomHartshorneRaoModule,ZZ,ZZ,PolynomialRing)
    (randomHartshorneRaoModule,ZZ,List,PolynomialRing)
    [randomHartshorneRaoModule,Attempts]
  Headline
    Compute a random Hartshorne-Rao module
  Usage 
    randomHartshorneRaoModule(d,g,R)
    randomHartshorneRaoModule(e,HRao,R)
  Inputs
    d: ZZ
       the degree of the desired curve
    g: ZZ
       the genus of the desired curve
    R: PolynomialRing
       coordinate ring of $\PP^{ 3}$
    e: ZZ 
       smallest degree of the Hartshorne-Rao module
    HRao: List
       desired dimensions of $H^1(\PP^3,I_C(n))$
    Attempts => ZZ
       the maximum number of times to try to find an example
  Outputs
     : Module
  Description
    Text
      Returns the ideal of a maximal rank curves of degree d 
      and genus g in $\PP^{ 3}$ with O_C(2) non-special and Hartshorne-Rao module of diameter $\le 3$, 
      which have a natural free resolution.
    Text
      For diameter =3 the construction is possible
      unless the expected Betti table of the Hartshorne-Rao module has shape
    
     a b c1 - - 
     
     - - c2 - -
      
     - - c3 d e 
    
     with both 4b-10c1 < a and 4d-10c3 < e. For diameter >4 the routine returns false,
     though we actually do know of a couple of constructions which work in a few further cases.
/// 

doc ///
  Key
    expectedShape
    (expectedShape,RingElement)
  Headline
    compute the "expected" shape from the Hilbert numerator
  Usage
    F=expectedShape q
  Inputs
    q: RingElement
       a polynomial in ZZ[t]
  Outputs
    F: ChainComplex
       a trivial free graded complex over ZZ[t] whose Betti table has Hilbert numerator q,
       assuming that each sign change in the coefficients of q corresponds to a step
  Description
    Example
      T=ZZ[t]
      q=1-3*t^2+2*t^3
      expectedShape q
      betti oo
      q=1-5*t^2+5*t^3-t^5
      expectedShape q
      betti oo
///

doc ///
  Key
    (expectedShape,ZZ,ZZ,ZZ)
  Usage
    F=expectedShape(d,g,r)
  Inputs
    d: ZZ
       the degree
    g: ZZ
       the genus
    r: ZZ
       dimension of $\PP^{ r}$
  Outputs
    F: ChainComplex
       a free graded chain complex with trivial differential and with Hilbert numerator the same as 
       for a nondegenerate maximal-rank curve of genus g and degree d in $\PP^{ r}$, with O_C(2) non-special.
  Description
    Example
      betti expectedShape(4,0,4)
      betti expectedShape(15,16,3)
///

doc ///
  Key
    randomCurveOfGenusUpTo14
    (randomCurveOfGenusUpTo14,ZZ,Ring)
    [randomCurveOfGenusUpTo14,Certify]
  Headline
    Compute a random curve of genus g
  Usage
    I=randomCurveOfGenusUpTo14(g,R)
  Inputs
    g: ZZ
       the genus
    R: Ring
       a field or a polynomial ring in 3,4 or 7 variables for $3\le g \le 10$, $11\le g \le 13$ or $g=14$ respectively
    Certify => Boolean
       whether to certify the result
  Outputs
    I: Ideal 
       of a curve of geometric genus g
  Description
    Text
      Pick a random curve of genus $g\le 14$ based on the unirationality proof for $\mathcal M_g$
      of Severi, Sernesi, Chang-Ran or Verra.
    Example
      FF=ZZ/101;
      I=randomCurveOfGenusUpTo14(9,FF)
      I=randomCurveOfGenusUpTo14(12,FF);
      betti res I
      ring I
      I=randomCurveOfGenusUpTo14(14,FF);
      betti res I
      ring I
///

doc ///
  Key
    randomCurveOfGenus8With8Points
    (randomCurveOfGenus8With8Points,PolynomialRing)
    [randomCurveOfGenus8With8Points,Certify]
  Headline
    Compute a random curve of genus 8 with 8 marked point 
  Usage
    (I,idealsOfPts)=randomCurveOfGenus8With8MarkedPoints S
  Inputs
    S: PolynomialRing
       homogeneous coordinate ring of $\PP^7$
    Certify => Boolean
       whether to certify the result
  Outputs
    I: Ideal 
       a canonical curve C of genus 8
    idealsOfPts: List
       8 ideals of K-rational points on C      
  Description
    Text
      According to Mukai any smooth curve of genus 8 and Clifford index 3
      is the transversal intersection $C=\PP^7 \cap\ G(2,6) \subset \ \PP^{15}$.
      In particular this is true for the general curve of genus 8.
      Picking 8 points in the Grassmannian $G(2,6)$ at random and \PP^7 as their span
      gives the result. 
    Example
      FF=ZZ/10007;S=FF[x_0..x_7];
      (I,points)=randomCurveOfGenus8With8Points S;
      betti res I 
      points     
/// 

doc ///
  Key
    randomNormalCurveOfGenus8AndDegree14
    (randomNormalCurveOfGenus8AndDegree14,PolynomialRing)
    [randomNormalCurveOfGenus8AndDegree14,Certify]
  Headline
    Compute a random normal curve of genus g=8 and degree 14
  Usage
    I=randomNormalCurveOfGenus8AndDegree14 S
  Inputs
    S: PolynomialRing
       in 7 variables
    Certify => Boolean
       whether to certify the result
  Outputs
    I: Ideal 
       of a curve of geometric genus 8 and degree 14 in \PP^6
  Description
    Text
      The construction is based on Mukai's unirational description of $M_{8,8}$
      of the moduli space of genus 8 with 8 marked points.
    Example
      FF=ZZ/10007;S=FF[x_0..x_6];
      I=randomNormalCurveOfGenus8AndDegree14 S;
      betti res I      
///  

doc ///
  Key
    randomCurveOfGenus14
    (randomCurveOfGenus14,PolynomialRing)
    [randomCurveOfGenus14,Certify]
  Headline
    Compute a random curve of genus 14  
  Usage
    I=randomCurveOfGenus14 S
  Inputs
    S: PolynomialRing
       homogeneous coordinate ring of \PP^6
    Certify => Boolean
       whether to certify the result
  Outputs
    IJ: Ideal 
       a curve C of genus 14 and degree 18 in \PP^6  
  Description
    Text
      According to Verra, a general genus 14 curve $C$ arizes as the residual
      intersection of the 5 quadrics in the homogeneous ideal of a general 
      normal curve $E$ of genus 8 and degree 14 in \PP^6. These in turn can be 
      constructed using Mukai's Theorem on genus 8 curves: Every smooth 
      genus 8 curve with general Clifford index arizes as the intersection 
      of the Grassmannian $G(2,6) \subset \PP^{14}$ with a transversal $\PP^7$.
      Taking $\PP^7$ as the span of general or random $8$ points 
      $$p_1,\ldots, p_8 \in{} G(2,6)$$ gives  $E$ together with a general divisor
      $ H=K_E+D_1-D_2$ of degree 14 where $D_1=p_1+\ldots+p_4$ and $D_2=p_5+\ldots+p_8$.
      
      The fact that the example below works can be seen as computer aided proof of the 
      unirationality of $M_{14}$. It proves the unirationality of $M_{14}$ for
      fields of the choosen finite characteristic 10007, for fields of characteristic 0
      by sem-continuity, and, hence, for all but finitely many primes $p$.
    
    Example
      FF=ZZ/10007;S=FF[x_0..x_6];
      setRandomSeed("alpha")
      time I=randomCurveOfGenus14(S,Certify=> true);
      betti res I      
/// 
doc ///
  Key
    randomCanonicalCurve
    (randomCanonicalCurve,ZZ,PolynomialRing)
    [randomCanonicalCurve,Certify]
  Headline
    Compute a random canonical curve of genus at most 14  
  Usage
    I=randomCanonicalCurve(g,S)
  Inputs
    g: ZZ
       the genus
    R: PolynomialRing
       homogeneous coordinate ring of $\PP^{ g-1}$
    Certify => Boolean
       whether to certify the result
  Outputs
    I: Ideal 
       of a canonical curve $C$ of genus $g$
  Description
    Text
      Compute a random canonical curve of genus $g \le{} 14$, based on the proofs of unirationality of
      $M_g$ by Severi, Sernesi, Chang-Ran and Verra.     
    Example
      g=14;
      FF=ZZ/10007;
      R=FF[x_0..x_(g-1)];
      setRandomSeed "alpha";
      time betti(I=randomCanonicalCurve(g,R))
      genus I == g and degree I ==2*g-2      
/// 
     
doc ///
  Key  
    Certify
  Headline 
    certify the result
  Description
     Text
        This optional argument is used with probabilistic algorithms to specify whether the result should be certified.
///

doc ///
  Key  
    Attempts
  Headline 
    the maximum number of times to try to find an example
  Description
     Text
        This optional argument is used with probabilistic algorithms to specify how many times to try to find an example.
///


doc ///
  Key  
    InCodim
  Headline 
    the expected codimension of the desired objects within the family 
  Description
     Text
       Optional argument in a search algorithm giving the codimension of the locus of desired objects within the family.
///

doc ///
  Key
    RandomCurves
  Headline
    Construction of random curves of various kinds and related computations
  Description
    Text
      The moduli space $M_g$
      of curves of genus $g \le 14$ is unirational, as proved by Severi, Sernesi, Chang-Ran and Verra.
      The methods used in their proofs allow us to find points in $M_g$.
      In particular, for a finite field $F$ we can try to find curves defined over $F$ at random, 
      if we choose random values for the parameters
      in the unirational construction. This yields various probabilistic algorithms for picking random curves
      of various kinds.
      
      For example 
      
      * random plane curves of degree $d$ with $\delta$ nodes, provided $binomial(d+2,2)-3*\delta > 0$
      
      * random curves of degree $d$ and genus $g$ in $\PP^{ 3}$, provided the Hartshorne-Rao module is easy to construct
      
      * random canonical curves of genus $g \le 14$
      
      As a byproduct of this package we can prove that the Hilbert scheme of curves in $\PP^{ 3}$ has at least 60
      unirational components corresponding to non-degenerate linearly normal maximal rank curves with $h^1 {\cal O}_C(2)=0$
      For many details see the item randomSpaceCurves.
      
      Sometimes it is possible to find points over a very small finite field $F_q$ in moduli spaces or 
      Hilbert schemes by searching: if the space is dominated by a parameter space $M$ that has small
      codimension in an unirational variety $G$, and if we can test quickly enough whether a random point p of G(F_q) is in M(F_q),
      for a finite field F_q, then we might find good points p in M(F_q) within reasonable
      running time. We call an algorithm based on these ideas a {\em search algorithm}; in case M itself is
      unirational we speak of {\em random choices}. We use this naming convention for the functions of this package.
      
      For both types of probabilistic algorithm we provide options. With the option {\tt Certify=>True}, 
      the result of the probabilistic algorithm gets certified, for example that the ideal returned 
      describes indeed a smooth curve. The option {\tt Attempts=>n} gives an upper bound {\tt n} for the number of
      attempts to find the desired object. For a search algorithm, the option {\tt InCodim=>c} computes the expected 
      running time of a search algorithm assuming that the codimension of M in G is c, and bounds the number of attempts
      accordingly.
///

doc ///
  Key
    "randomObject"
  Headline
    Guideline for the implementation of random objects
  Description
    Text
     Given a unirational moduli space $M$ together with a map $U \rightarrow M$
     of objects the function randomObject returns a random point in an open subset of $M$ or null.
     
///

-------------- TESTS --------------------


TEST ///
     assert(nextprime(100)==101);
///



TEST ///
     setRandomSeed"alpha";
     p=nextPrime(10000)
     kk=ZZ/p ;
     R=kk[x_0..x_2];
     I=ideal(random(4,R)); 
     time randomRationalPoint I     
///
	  
TEST ///
     setRandomSeed"alpha";
     kk=ZZ/101;
     R=kk[x_0..x_2];
     I=randomDistinctPlanePoints(5,R,Certify=>true);
     assert(degree I == 5 or I==ideal 0_R);
     I=randomDistinctPlanePoints(5,R,Attempts=>infinity);
     assert(degree I == 5);
///

TEST ///
    setRandomSeed"alpha";
    kk=ZZ/2;
    R=kk[x_0..x_2];
    I=randomNodalPlaneCurve(5,6,R,Attempts=>10);
    singI=I + ideal jacobian I;
    assert((degree singI,dim singI,distinctPlanePoints singI)==(1,3,false) or 
           (degree singI,dim singI,distinctPlanePoints singI)==(6,1,true))
kk=ZZ/101;
R=kk[x_0..x_2];
I=randomNodalPlaneCurve(5,6,R,Certify=>true);
degree I;
assert(degree I==5 or I==0);
I=randomNodalPlaneCurve(5,6,R);
degree I;
assert(degree I==5 or I==0);
///
TEST ///
setRandomSeed"alpha"
p=3
kk=ZZ/p
R=kk[x_0..x_2]
d=6,delta=10
expectedGenus=binomial(d-1,2)-delta
time I=searchRandomNodalPlaneCurve(d,delta,R)
assert(I==0 or degree I==d) 
time I=searchRandomNodalPlaneCurve(d,delta,R,Certify=>true,InCodim=>4)
singI =I + ideal jacobian I
assert(I==0 or (degree singI==delta and degree I==d))
time I=searchRandomNodalPlaneCurve(d,delta,R,Attempts=>p^4)
///


TEST ///
     R=ZZ/101[x_0..x_3];
     d=12,g=11;
     betti(J=randomSpaceCurve(d,g,R))
     assert (degree J==d and genus J == g)	  
///

TEST ///
     kk=ZZ/101
     R=kk[x_0..x_3]
     d=10,g=7
     HRao1=select(apply(toList(1..7),n->(n,max(d*n+1-g-binomial(3+n,3),0))), i-> i_1 !=0)
     HRao=apply(HRao1,i->i_1)
     e=HRao1_0_0
     M=randomHartshorneRaoModule(e,HRao,R)
     assert(apply(toList(e..e+#HRao-1),i->hilbertFunction(i,M))==HRao)
     betti res M
///

TEST ///
FF=ZZ/10007; S=FF[x_0..x_6];    
time betti(J=randomCurveOfGenus14 S)
-- used 2.19 seconds
betti res J
///
end

restart
uninstallPackage("RandomCurves")
installPackage("RandomCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp"RandomCurves"

loadPackage("RandomCurves")