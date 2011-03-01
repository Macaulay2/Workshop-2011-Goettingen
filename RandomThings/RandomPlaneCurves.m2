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