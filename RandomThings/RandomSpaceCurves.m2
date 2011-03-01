newPackage(
	"RandomSpaceCurves",
    	Version => "0.6", 
    	Date => "March 1, 2011",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	            {Name => "Hans-Christian Graf v. Bothmer",
	             Email => "bothmer@uni-math.gwdg.de",
		     HomePage => "http://www.crcg.de/wiki/User:Bothmer"}		 
                   },
    	Headline => "Construction of random smooth space curves",
    	DebuggingMode => true
        )

if not version#"VERSION" >= "1.4" then error "this package requires Macaulay2 version 1.4 or newer"

export{"nextPrime",
     "randomSpaceCurve",
     "randomHartshorneRaoModule",
     "knownUnirationalComponentOfSpaceCurves",
     "expectedShape",
     "Attempts",
     "Certify"
     }

nextPrime=method()
nextPrime ZZ:=n->(
      if n <= 2 then return 2;
      p:=if n%2==0 then n+1 else n;
      while not isPrime p do p=p+2;
      p)


--------------------
-- Finite Modules --
--------------------


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



------------------
-- Space Curves --
------------------

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

------------------------------------
-- Hilbert Function and Numerator --
------------------------------------

-- calculate the numerator of a Hilbert 
hilbertNumerator = (L,t) -> (    
      p:=sum(L#,i->(if i>1 then min(d*i+1-g,binomial(r+i,r)) else binomial(r+i,r))*t^i);
     q:=p*(1-t)^(r+1)%t^b;

     


-----------------------------
-- Expected Betti Tableaus --
-----------------------------

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
    "RandomCurves"
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


-------------- TESTS --------------------


TEST ///
     assert(nextprime(100)==101);
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
uninstallPackage("RandomSpaceCurves")
installPackage("RandomSpaceCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
viewHelp"RandomSpaceCurves"

loadPackage("RandomSpaceCurves")