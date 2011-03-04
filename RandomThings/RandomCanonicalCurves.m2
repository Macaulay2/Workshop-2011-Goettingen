needsPackage"RandomObjects"
newPackage(
	"RandomCanonicalCurves",
    	Version => "0.6", 
    	Date => "March 4, 2011",
    	Authors => {{Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	            {Name => "Hans-Christian Graf v. Bothmer",
	             Email => "bothmer@uni-math.gwdg.de",
		     HomePage => "http://www.crcg.de/wiki/User:Bothmer"}		 
                   },
    	Headline => "Construction of random smooth canonical curves up to genus 14",
    	DebuggingMode => true
        )

if not version#"VERSION" >= "1.4" then error "this package requires Macaulay2 version 1.4 or newer"

export{
     "canonicalCurve",
     "randomCanonicalCurve",
     "certifyCanonicalCurve"
     }

needsPackage"RandomObjects"
needsPackage"RandomSpaceCurves"
needsPackage"RandomPlaneCurves"
needsPackage"RandomGenus14Curves"


randomCanonicalModelOfPlaneCurve = method(Options => {Certify => false})

-- input: 
--    d degree of plane nodal curve
--    g geometric genus of plane nodal curve
--    R ring with g variables
-- output:
--    I Ideal of R describing a canonical model
randomCanonicalModelOfPlaneCurve (ZZ,ZZ,Ring) := opt -> (d,g,R) -> (
	  x := local x;
	  S := (coefficientRing R)[x_0..x_2];
	  delta:=binomial(d-1,2)-g;
	  J:=(random nodalPlaneCurve)(d,delta,S,Certify=>opt.Certify,Attempts=>1);
	  KC:=(gens intersect(saturate(ideal jacobian J +J),(ideal vars S)^(d-3)))_{0..(g-1)};
	  SJ:=S/J;
	  phi:=map(SJ,R,substitute(KC,SJ));
	  I:=ideal mingens ker phi;
	  return I);
     
randomCanonicalModelOfSpaceCurve = method(Options => {Certify => false})

-- input: 
--    d degree of space curve
--    g geometric genus of space curve
--    R ring with g variables
-- output:
--    I Ideal of R describing a canonical model
randomCanonicalModelOfSpaceCurve (ZZ,ZZ,Ring) := opt -> (d,g,R) -> (
     y := local y;
     S := (coefficientRing R)[y_0..y_3];
     RS := R**S;
     I := (random spaceCurve)(d,g,S,Certify=>opt.Certify,Attempts=>1);
     omegaC := presentation prune truncate(0,Ext^1(I,S^{ -4}));
     graph := substitute(vars R,RS)*substitute(omegaC,RS);	  	    
     J := saturate(ideal graph,substitute(y_0,RS));	  
     Icanonical := ideal mingens substitute(J,R);
     return Icanonical);

      
randomCanonicalCurve=method(TypicalValue=>Ideal,Options=>{Certify=>false})

-- construct a random canonical curve of genus g
-- by using plane cuves, space curves and verras construction for g=14
-- R a ring with g variables
randomCanonicalCurve(ZZ,PolynomialRing):= opt -> (g,R)->(
     if g>14 or g<4 then error "no method implemented";
     d := null;
     if g<=10 then (
	  s:=floor(g/3); -- the speciality of a plane model of minimal degree
	  d=g+2-s; -- the degree of the plane model
	  return randomCanonicalModelOfPlaneCurve(d,g,R,Certify=>opt.Certify));
     if g==11 then return randomCanonicalModelOfSpaceCurve(12,11,R,Certify=>opt.Certify);
     if g==12 then return randomCanonicalModelOfSpaceCurve(12,12,R,Certify=>opt.Certify);
     if g==13 then return randomCanonicalModelOfSpaceCurve(13,13,R,Certify=>opt.Certify);
     if g==14 then return (random canonicalCurveGenus14)(R,Certify=>opt.Certify,Attempts=>1);
     )

certifyCanonicalCurve = method(TypicalValue => Boolean)

-- the canonical curve does not need to be certified,
-- since in the construction the smoothness gets already
-- certified by (randomPlaneCurve and randomSpaceCurve).
certifyCanonicalCurve (Ideal,PolynomialRing) := (I,R) -> true

--- interface for (random canonicalCurveGenus14)
canonicalCurve = new RandomObject from {
     Construction => randomCanonicalCurve,
     Certification => certifyCanonicalCurve
     }

beginDocumentation()


doc ///
  Key
    randomCanonicalCurve
    (randomCanonicalCurve,ZZ,PolynomialRing)
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



end

restart
uninstallPackage("RandomCanonicalCurves")
installPackage("RandomCanonicalCurves",RerunExamples=>true,RemakeAllDocumentation=>true);
--viewHelp"RandomCanonicalCurves"

restart
needsPackage"RandomCanonicalCurves"
apply(4..14,g->(
	  time print (g,binomial(g-2,2), rank source mingens (I=randomCanonicalCurve(g,(ZZ/101)[x_0..x_(g-1)])))
     ))