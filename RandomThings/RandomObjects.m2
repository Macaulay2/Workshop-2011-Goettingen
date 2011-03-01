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
       
export {
     "Certify", 
     "RandomObject", 
     "isImplemtedRandom",
     "isImplemented",
     "Attempts", 
     "Certification", 
     "Construction", 
     "ParameterTypes",
     "constructRandomObject",
     "randomObjectViaStrategy",
     "randomObjectViaStrategyIsImplemented" }

RandomObject = new Type of MutableHashTable
globalAssignment RandomObject
random RandomObject := randomopts -> Object -> args -> (
     -- if the args consist of a single element make it into a sequence
     if not instance(args, Sequence) then args = 1:args;
     -- default values for certify and attempts
     cert := false;
     att := infinity;
     -- strip off certify and attempts from the argument list
     args = toSequence (for x in args list (
	  if instance(x,Option) then (
	       if x#0 === Certify then (cert = x#1 ; continue )
	       else
	       if x#0 === Attempts then (att = x#1 ; continue )
	       else x
	       )
	  else x));
     -- try to construct the object until either the maximum number of 
     -- attempts is reached or a (certified) object is constructed  
     for i from 1 do (
	  if i > att then return null;
	  object := Object.Construction args;
	  if object === null then continue;
	  if not cert then return object;
	  if Object.Certification prepend(object, args) then return object;
	  ))

isImplementedRandom=method()
isImplementedRandom RandomObject:= randomopts -> Object -> Object.isImplemented
     
doc ///
Key
 RandomObject
Headline
 framework for creation of random objects
Description
 Text
    RandomObject provides the framework for the construction of random objects parametrized by a unirational moduli space $M$.
    
    RandomObject has MutableHashTable as ancestor and needs to have the following keys:
        
    * Options: Options for the construction of the random objects 
    
    * Construction: the method function assigned to this key contains a unirationality construction.
    
    * Certification: the method function assigned to this key checks whether the constructed object fulfills certain conditions.
    
    In the following example we construct plane curves of degree $d$. The Certification checks whether they are irreducible over the coefficient field.
    
 Example
    constructPlaneCurve = method(TypicalValue=>Ideal)
    constructPlaneCurve(ZZ,PolynomialRing):=(d,R) -> ideal random(R^1,R^{1:-d})
 
    certifyPlaneCurve = method(TypicalValue=>Boolean)
    certifyPlaneCurve(Ideal,ZZ,PolynomialRing):=(I,d,R)-> #decompose I==1

    planeCurve = new RandomObject from {
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


doc ///
  Key
    "(myrandom,RandomObject)"
  Headline
    constructs a random object of type object
  Usage
    o=random(randomObjectClass)
  Inputs
    randomObjectClass : RandomObject 
  Outputs
    o : Thing
  Description
    Text 
  SeeAlso  
///
end

restart
uninstallPackage"RandomObjects";
installPackage"RandomObjects";
viewHelp RandomObjects
kk=ZZ/3;
R=kk[x_0..x_2];
tally apply(3^4, i-> null===(random Foo)(2,R,Certify=>true,Attempts=>1))
