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
     "hilbertNumerator",
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

------------------------------------
-- Hilbert Function and Numerator --
------------------------------------

-- calculate the numerator of a Hilbert function 
-- from the frist d+r+1 values where
-- d is the regularity of the corresponding module
-- and r is the dimension of the ambient space
--
-- L = a list of dimensions
-- r = the dimension of the ambient space
-- t = the variable to be used in the numerator
hilbertNumerator = (L,r,t) -> (
     -- the beginning of the hilbert series
     p:=sum(#L,i->L#i*t^i); 
     -- the numerator
     p*(1-t)^(r+1)%t^(#L)
     )

TEST ///
   T = QQ[t]; 
   assert (hilbertNumerator({1,3,0,0,0,0},3,t) == 3*t^5-11*t^4+14*t^3-6*t^2-t+1)
///

TEST /// 
    T = QQ[t];  
    assert (hilbertNumerator ({1, 4, 10, 15, 20, 25, 30, 35, 40},3,t) == -t^5+5*t^4-5*t^3+1)
///

   

-----------------------------
-- Expected Betti Tableaus --
-----------------------------

-- convert c*t^d to (c,R^(abs(c):-d))
-- assumes only one term c*t^d
-- ring of t must be over ZZ
-- and singly graded
--
-- this funciton is needed to construct 
-- ChainComplexes of expected shape from
-- a HilberNumerator
oneTermToFreeModule = (mon,R) -> (
     -- the coefficient of the monomial
     c := lift((last coefficients mon)_0_0,ZZ);
     -- the degree of the monmial
     d := sum degree mon;
     (c,R^{abs(c):-d})
     )

TEST ///
  T = QQ[t];
  assert (oneTermToFreeModule(-4*t^3,T)==(-4,T^{4:-3}))
///



-- construct a minimal free resolution with expected betti tableau
expectedShape=method()


-- calculates a minimal free resolution with expected betti tableau
-- from a hilbert Numerator
--
-- For this every term a_i*t^i will represent a summand R^{abs(a_i):-i}
-- The step where this summand is used depends on the number of
-- sign switches that occur in the hilbert numerator befor this monomial  
expectedShape(RingElement,Ring):= (hilbNum,R) ->(
     -- find terms of hilbert Numerator
     -- smallest degree first
     termsHilbNum := reverse terms hilbNum;
     -- convert terms into pairs (coefficient, FreeModule)
     summands := apply(termsHilbNum,m->oneTermToFreeModule(m,R));
     -- make empty chain comples
     F := new ChainComplex;
     F.ring = ring hilbNum;
     -- put the summands into the appropriate step of F
     -- j contains the current step
     j := -1;
     -- previous Coefficient is needed to detect sign changes
     previousCoefficient := -(first summands)#0;
     -- step through all summands     
     for s in summands do (
	  -- has a sign change occured?
     	  if (s#0*previousCoefficient) < 0 then (
	       -- sign change => next step in the resolution
	       j = j+1;
	       -- start new step with current summand
	       F_j = s#1 )
     	  else (
	       -- no sign change => add currend summand to currend step
     	       F_j = F_j ++ s#1;
	       );
	  -- store previous coefficient
     	  previousCoefficient = s#0;
     	  );
     -- return the complex
     F
     )

-- if no ring is given, the ring of the HilbertNumerator is used
expectedShape(RingElement):= (hilbNum) -> expectedShape(hilbNum,ring hilbNum)

 

-- erase following code when new code is tested
--expectedShapeOld(ZZ,ZZ,ZZ):=(d,g,r)->(
     -- we assume C non-degenerate, O_C(2) nonspecial and maximal rank
--     t:=symbol t;
--     T:=ZZ[t];
--     b:=d+r+1;
--     p:=sum(b,i->(if i>1 then min(d*i+1-g,binomial(r+i,r)) else binomial(r+i,r))*t^i);
--     q:=p*(1-t)^(r+1)%t^b;
--     expectedShape q)

-- calculate the expected shape of the betti tableau
-- for a curve of degree d, genus g in IP^r.
-- we assume C non-degenerate, O_C(2) nonspecial and maximal rank
-- R the coordinate Ring of IP^r with r+1 variables
expectedShape(ZZ,ZZ,Ring) := (d,g,R)->(
     r := (dim R)-1;
     b := d+r+1;
     L := apply(b,i->(if i>1 then 
	       min(d*i+1-g,binomial(r+i,r)) 
	       else binomial(r+i,r)));
     expectedShape(hilbertNumerator(L,r,(gens R)#0),R)
     )

--expectedShape(ZZ,ZZ,ZZ) := (d,g,r)->(
--     t:=symbol t;
--     T:=ZZ[t];
--     b:=d+r+1;
--     L:=apply(b,i->(if i>1 then 
--	       min(d*i+1-g,binomial(r+i,r)) 
--	       else binomial(r+i,r)));
--     expectedShape hilbertNumerator(L,r,t)
--     )

TEST ///
    x = symbol x
    R = QQ[x_0..x_3]; 
    e = expectedShape(5,1,R);
    b = new BettiTally from {
	 (0,{0},0) => 1, 
	 (1,{3},3) => 5,
      	 (2,{4},4) => 5, 
	 (3,{5},5) => 1
    	 };
    assert((betti e) == b)
///

TEST ///
    T = QQ[t]; 
    e = expectedShape hilbertNumerator({1,3,0,0,0,0},3,t);
    b = new BettiTally from {
	 (0,{0},0) => 1, 
	 (1,{1},1) => 1,
      	 (1,{2},2) => 6, 
	 (2,{3},3) => 14, 
	 (3,{4},4) => 11, 
	 (4,{5},5) => 3};
    assert((betti e) == b)
/// 



--------------------
-- Finite Modules --
--------------------


randomHartshorneRaoModule=method(TypicalValue=>Module,Options=>{Attempts=>0})
randomHartshorneRaoModule(ZZ,ZZ,PolynomialRing):=opt->(d,g,R)->(
     if not knownUnirationalComponentOfSpaceCurves(d,g) then 
     error ("no construction implemented for degree ",toString d, " and genus ", toString g);
     G:=expectedShape(d,g,R);
     --if length G>3 then error "either 2H special or not of maximal rank";
     n:=4;
     while d*n+1-g>binomial(n+3,3) do n=n+1;
     HRao1:=select(apply(toList(1..n),n->(n,max(d*n+1-g-binomial(3+n,3),0))), i-> i_1 !=0);
     HRao:=apply(HRao1,i->i_1);
     e:=HRao1_0_0;
     M:=randomHartshorneRaoModule(e,HRao,R);
     return M;
     -- this return was not in the original code by Frank
     attempt:=1;
     while true do (
     	  if apply(toList(e..e+#HRao-1),i->hilbertFunction(i,M))==HRao then return M;
	  if opt.Attempts <= attempt then return null;
	  M=randomHartshorneRaoModule(e,HRao,R);
	  attempt=attempt+1;
	  ))

-- calculate the number of expected syzygies of a
-- random a x b matrix with linear entries in R
expectedLinearSyzygies = (a,b,R) -> (
     n := dim R;
     b*n-a*binomial(n+1,2)
     )

TEST ///
    R = ZZ/101[x_0..x_3];
    assert(expectedLinearSyzygies(2,6,R) == 
	 (betti res coker random(R^{2:0},R^{6:-1}))#(2,{2},2)
	 )
///

-- Try to construct a random HartshorneRau module of
-- length 3 starting at the beginning of the
-- minimal free resolution.
-- 
-- The main difficulty is in getting the number of 
-- linear syzygies of the first matrix in the resolution right
--
-- HRau = {h1,h2,h3} the Hilbertfunction of the desired module 
-- R the ring where the module should live. It is assumed, that 
-- this ring has 4 variables and is singly graded.
randomHartshorneRaoModuleDiameter3oneDirection = (HRao,R) -> (
     -- construct a chain complex with expected betti tableau
     -- and 0 differentials
     F := expectedShape(hilbertNumerator(HRao|{0,0,0,0},3,(gens R)#0),R);
     -- the betti Tableau of F to find out later if linear syzygies 
     -- are requried (this is the difficult part in the construction)
     expectedBetti := betti F;
     -- find betti Numbers of the linear strand
     linearStrand := for i from 0 list (if expectedBetti#?(i,{i},i) then expectedBetti#(i,{i},i) else break);
     -- construction depends on lenth of linear strand.
     if #linearStrand == 0 then error"linear Stand has lenght 0. This should never happen";
     if #linearStrand == 1 then (
	  -- first matrix can neither have nor be required to have linear syzygies
	  -- choose first matrix randomly
     	  return coker random (F_0,F_1)
	  );
     if #linearStrand == 2 then (
	  -- no linear syzygies of the first matrix are requried
	  -- check if first matrix always has unwanted syzygies
	  if expectedLinearSyzygies(linearStrand#0,linearStrand#1,R) <= 0 then (
	       -- no unwanted syzygies
	       -- choose first matrix randomly
     	       return coker random (F_0,F_1)
	       );
     	  );	       
     if #linearStrand == 3 then (
	  -- is the number of expected syzygies == the number of required syzygies?
	  if expectedLinearSyzygies(linearStrand#0,linearStrand#1,R) == linearStrand#2 then (
	       -- choose first matrix randomly
     	       return coker random (F_0,F_1)
	       );
	  -- too many syzygies?
	  if expectedLinearSyzygies(linearStrand#0,linearStrand#1,R) > linearStrand#2 then (
	       -- in this case the construction method will not work
	       return null     	       
	       );
	  -- too few syzygies?
	  if expectedLinearSyzygies(linearStrand#0,linearStrand#1,R) < linearStrand#2 then (
	       -- try to choose the syzygies first
	       -- this will work if the transpose of a generic map between
	       -- 1. and 2. module of the linear strand has more expected syzygies
	       -- than required in the 0. step
     	       if expectedLinearSyzygies(linearStrand#2,linearStrand#1,R) >= linearStrand#0 then (
	       	    -- syzygies of the transpose of second step in linear strand
	       	    s := syz random(R^{linearStrand#2:2},R^{linearStrand#1:1});
	       	    -- choose linearStrand#0 syzygies randomly among those and transpose again
	       	    return coker (transpose (s*random(source s,R^{linearStrand#0:0})));
	       	    );
	       )
      	   );
      -- if we arrive here there were either to few or to many linear
      -- syzygies required	  
      return null     	       
      );

-- these will become examples
R = ZZ/101[x_0..x_3];
betti res randomHartshorneRaoModuleDiameter3oneDirection({1,4,1},R)
betti res randomHartshorneRaoModuleDiameter3oneDirection({1,4,2},R)
betti res randomHartshorneRaoModuleDiameter3oneDirection({1,3,2},R)
betti res randomHartshorneRaoModuleDiameter3oneDirection({2,3,1},R)
-- this is a pathological case since 2<-5 has 2 syzygies in 4 variables
-- while the expected number is 0



-- Try to construct a random Hartshorne-Rau module of
-- length 3 by starting at both ends of the expected
-- minimal free resolution.
--
-- HRau = {h1,h2,h3} the Hilbertfunction of the desired module 
-- R the ring where the module should live. It is assumed, that 
-- this ring singly graded. It is checked that the ring has 4 variables
randomHartshorneRaoModuleDiameter3 = (HRao,R)->(
     if #HRao != 3 then error"Hilbert function has to have length 3";
     -- start at the beginning of the resolution    
     M := randomHartshorneRaoModuleDiameter3oneDirection(HRao,R);
     -- did this direction work?
     if M =!= null and apply(3,i->hilbertFunction(i,M)) == HRao then return M;
     -- start at the end of the resolution
     Mdual := randomHartshorneRaoModuleDiameter3oneDirection(reverse HRao,R);
     Fdual := res Mdual;
     M = (coker transpose Fdual.dd_4)**R^{ -6};
     return M
     )

-- these will become examples
betti res randomHartshorneRaoModuleDiameter3({1,4,1},R)
betti res randomHartshorneRaoModuleDiameter3({1,4,2},R)
-- the two following are strictly not to specification,
-- sind the resolution is not expected
betti res randomHartshorneRaoModuleDiameter3({1,3,2},R)
betti res randomHartshorneRaoModuleDiameter3({2,3,1},R)
-- this should not work
--betti res randomHartshorneRaoModuleDiameter3({1,2,3,4},R)

-- Try to construct a random Hartshorne-Rau module of
-- length 2. Here the only problem is, that the
-- generic module may not have expected syzgies
--
-- HRau = {h1,h2} the Hilbertfunction of the desired module 
-- R the ring where the module should live. It is assumed, that 
-- this ring has 4 variables and is singly graded.
randomHartshorneRaoModuleDiameter2 = (HRao,R)->(
     if #HRao != 2 then error"Hilbert function has to have length 2";
     -- some special cases with non expected resoluton
     --
     --if HRao == {1,1} then return coker random(R^{0},R^{3:-1,1:-2});
     --if HRao == {1,2} then return coker random(R^{0},R^{2:-1,3:-2});
     --if HRao == {2,1} then return coker random(R^{2:0},R^{7:-1});
     --
     -- the standart construction still works since the unexpected
     -- part is not in the first 2 steps.
     --
     -- now assume expected resolution
     --
     -- always start at the beginning of the resolution    
     F := expectedShape(hilbertNumerator(HRao|{0,0,0,0},3,(gens R)#0),R);
     -- the betti Tableau of F to find out later if linear syzygies 
     -- are requried (this is the difficult part in the construction)
     expectedBetti := betti F;
     M := coker random(F_0,F_1)
     )

-- Construct a random Hartshorne-Rau module of
-- length 1. This allways works
--
-- HRau = {h1} the Hilbertfunction of the desired module 
-- R the ring where the module should live. It is assumed, that 
-- this ring has 4 variables and is singly graded.
randomHartshorneRaoModuleDiameter1 = (HRao,R)->(
     if #HRao != 1 then error"Hilbert function has to have length 1";
     return coker (vars R**R^{HRao#0:0})
     )

randomHartshorneRaoModule(ZZ,List,PolynomialRing):=opt->(e,HRao,R)->(
     if dim R != 4 then error "expected a polynomial ring in 4 variables";
     if degrees R !={{1}, {1}, {1}, {1}} then error "polynomial ring is not standard graded";
     if #HRao > 3 then error "no method implemented for Hartshorne Rao modue of diameter >3";
     M := null;
     if #HRao == 1 then M = randomHartshorneRaoModuleDiameter1(HRao,R);
     if #HRao == 2 then M = randomHartshorneRaoModuleDiameter2(HRao,R);
     if #HRao == 3 then M = randomHartshorneRaoModuleDiameter3(HRao,R);
     if M === null then return null else return M**R^{ -e};
     )

     

------------------
-- Space Curves --
------------------

-- given a betti Table b and a Ring R make a chainComplex 
-- over R-Module with that has betti diagramm b.
-- negative entries are ignored
-- rational entries produce an error
-- multigraded R's work only if the betti Tally
-- contains degrees of the correct degree length
Ring ^ BettiTally := (R,b) -> (
     F := new ChainComplex;
     F.ring = R;
     --apply(pDim b,i->F_i = null);
     for k in keys b do (
	  -- the keys of a betti table have the form
	  -- (homological degree, multidegree, weight)
	  (i,d,h) := k;
	  -- use F_i since it gives 0 if F#0 is not defined
	  F#i = F_i ++ R^{b#k:-d};
	  );
     F
     )

TEST ///
     R = QQ[x_0..x_3];
     b = betti (random(R^{1,2},R^{0,0,1}))	  
     assert (b == betti (R^b))
///

-- the Harshorne Rao module of a curve is defined as 
-- M = \oplus_i H^1(I_C(-i)) is can also be obtained as
-- the cokernel of the transpose of the last map
-- in a minimal free resolution of a curve
--
-- conversly one can construct a curve, by first
-- constructing the Harshorne Rao Module an therefore
-- the last matrix in the minimal free resolution of 
-- the curve
randomSpaceCurve=method(TypicalValue=>Ideal,Options=>{Attempts=>0,Certify=>false})

randomSpaceCurve(ZZ,ZZ,PolynomialRing) := opt->(d,g,R)->(			 
     if not knownUnirationalComponentOfSpaceCurves(d,g) then return null;
     G:=expectedShape(d,g,R);
     -- calculate values of h^1 that are forced by the maximal rank assumption
     h1 := for i from 0 when ((i<4) or(d*i+1-g)>binomial(i+3,3)) list max(d*i+1-g-binomial(3+i,3),0);
     -- calculate offset (i.e. number of leading 0's in h1)
     e := 0; for i in h1 when i==0 do e=e+1;
     -- calculate support of Hartshorne Rao Moduole
     HRao := select(h1,i->i!=0);
     -- if the Hartshorne Rao Module is zero, the curve is ACM
     -- and it can be defined by the minors of an appropriate
     -- Hilbert-Birch-Matrix
     if #HRao==0 then (
	  if length G !=2
	  then error "cannot be ACM" 
	  else return minors(rank G_2,random(G_1,G_2))
	  );
     M:=randomHartshorneRaoModule(e,HRao,R);
     if M === null then return null;     	       
     F :=res M;
     -- detect syzygies in the second step, that do not 
     -- come from the HR-Module
     H := R^((betti G_2)-(betti F_3));
     -- calculate a presentation matrix of 
     -- the ideal of the curve
     N := random(G_1,F_2++H_0)*(F.dd_3++id_(H_0));
     -- calculate the ideal presented by this matrix
     return ideal syz transpose N
     )


-- old certification for SpaceCurves 

--     if not opt.Certify then return J;
--     singJ := minors(2,jacobian J)+J;
--     if dim singJ==0 and dim M==0 then return J;
--     if opt.Attempts<= 0 then return null;
--     J=randomSpaceCurve(d,g,R,opt.Certify=>true,Attempts=>opt.Attempts-1);
--     J)

knownUnirationalComponentOfSpaceCurves=method()
knownUnirationalComponentOfSpaceCurves(ZZ,ZZ) := (d,g)->(
     n:=4;
     while 
     d*n+1-g>binomial(n+3,3)  
     do n=n+1;
     HRao1:=select(apply(toList(1..n),n->(n,max(d*n+1-g-binomial(3+n,3),0))), i-> i_1 !=0);
     G:=expectedShape(d,g,QQ[x_0..x_3]);
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
    (expectedShape,ZZ,ZZ,Ring)
  Usage
    F=expectedShape(d,g,R)
  Inputs
    d: ZZ
       the degree
    g: ZZ
       the genus
--    r: ZZ
--       dimension of $\PP^{ r}$
    R: Ring
       the coordinate Ring of $\PP^{ r}$
  Outputs
    F: ChainComplex
       a free graded chain complex with trivial differential and with Hilbert numerator the same as 
       for a nondegenerate maximal-rank curve of genus g and degree d in $\PP^{ r}$, with O_C(2) non-special.
  Description
    Example
      betti expectedShape(4,0,QQ[x_0..x_4])
      betti expectedShape(15,16,QQ[x_0..x_3])
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