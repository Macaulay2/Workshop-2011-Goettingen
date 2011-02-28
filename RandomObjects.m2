newPackage ("RandomObjects",
      	Version => "0.1", 
    	Date => "March 1, 2011",
    	Authors => {
	     {Name     => "Hans-Christian Graf v. Bothmer",
	      Email    => "bothmer@uni-math.gwdg.de",
	      HomePage => "http://www.crcg.de/wiki/User:Bothmer"},
	      
	     {Name     => "Florian Geiss",
	      Email    => "fg@math.uni-sb.de",
	      HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	 
	     {Name     => "Daniel R. Grayson", 
	      Email    => "dan@math.uiuc.edu",
	      HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	 
	     {Name     => "Frank-Olaf Schreyer", 
	      Email    => "schreyer@math.uni-sb.de", 
	      HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}},
        Headline => "framework for making random objects in algebraic geometry",
    	DebuggingMode => true
        )
     
     
     
export {"Certify", "RandomObject", "Attempts", "Certification", "Construction", "Parameters" }

RandomObject = new Type of MutableHashTable
globalAssignment RandomObject
random RandomObject := randomopts -> Object -> (
     if Object.?Function then return Object.Function;
     Object.Function = f := method ( Options => join(Object#Options, { Certify => false, Attempts => infinity }) );
     parameters := Object.Parameters;
     f parameters := opts -> args -> for i from 1 do (
	  if i > opts.Attempts then return null;
	  object := (Object.Construction opts) args;
	  if object === null then continue;
	  if not opts.Certify then return object;
	  if Object.Certification(opts, args, object) then return object;
	  );
     f)

doc ///
Key
 RandomObject
Headline
 framework for creation of random objects
Description
 Text
    RandomObject provides the framework for the construction of random objects parametrized by a unirational moduli space $M$.
    
    RandomObject has MutableHashTable as ancestor and needs to have the following keys:
    
    * Parameters: defines parameter types that specify the moduli space M (e.g. ZZ for the genus g in the case of the moduli space of curves)
    
    * Options: Options for the construction of the random objects 
    
    * Construction: the function assigned to this key contains a unirationality construction.
    
    * Certification: the certification function is used to check whether the constructed object fulfills certain conditions.
    
    
    
    In the following simple example we construct plane curves of degree $d$. The Certification checks whether they are irreducible.
    
 Example
    constructPlaneCurve = opts -> ((d,R) -> ideal random(R^1,R^{1:-d}))
 
    certifyPlaneCurve = (opts, args, object) -> #decompose object==1

    planeCurve = new RandomObject from {
	 Parameters => (ZZ,Ring),
     	 Options    => {Color => Blue},
     	 Construction => constructPlaneCurve,
     	 Certification => certifyPlaneCurve
     	 }
    
 Text
    We construct a curve of degree $2$ as follows
  
 Example
    R=ZZ/3[x_0..x_2];
    (random planeCurve)(2,R)
 
 Text
    We can certify the curve by using the Option Certify
 
 Example    
    (random planeCurve)(2,R,Certify=>true)
    
 Text 
    As the coefficient field is a small finite field there is a certain chance that the curve is not irreducible.
    We can check this if we limit the number of attempts to $1$. If the curve is then reducible, {\tt null} is returned. 
 
 Example
    tally apply(3^4,i->(random planeCurve)(2,R,Certify=>true,Attempts=>1) === null)
     
///

end
restart
uninstallPackage"RandomObjects";
installPackage"RandomObjects";
viewHelp RandomObjects
kk=ZZ/3;
R=kk[x_0..x_2];
tally apply(3^4, i-> null===(random Foo)(2,R,Certify=>true,Attempts=>1))
