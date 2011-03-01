needsPackage "RandomObjects"
newPackage(
	"RandomFoo",
    	Version => "0.1", 
    	Date => "February 28, 2011",
    	Authors => {{Name => "Dan Grayson", 
		  Email => "", 
		  HomePage => ""},
	            {Name => "Hans-Christian Graf v. Bothmer",
	             Email => "bothmer@uni-math.gwdg.de",
		     HomePage => "http://www.crcg.de/wiki/User:Bothmer"},
		    {Name => "Florian Geiss",
		     Email=> "fg@math.uni-sb.de",
		     HomePage =>"http://www.math.uni-sb.de/ag/schreyer/"}		 
                   },
    	Headline => "Construction of random objects",
    	DebuggingMode => true
        )
export { "Foo", "Color", "Blue" }
needsPackage "RandomObjects"

CreateFoo = opts -> genus -> random 10 + genus

CertifyFoo =  (opts, args, object) -> object > 5

Foo = new RandomObject from {
     Types => ZZ,
     Options => {Color => Blue},
     Create => CreateFoo,
     Certify => CertifyFoo
     }

beginDocumentation()

doc ///
  Key
     "Foo"
  Headline
     Create a random foo
  Usage
    (random Foo) n
  Inputs
    n : ZZ
       a number
  Outputs
    : ZZ
       a number
  Description
    Text 
     This function adds a random number, in the range 0..9, to {\tt n} and returns the result.
    Example
     (random Foo) 14
    Text
     If a foo of another color is desired, then add an optional argument of the form { \tt Color => thecolor }.
    Example
     (random Foo)(14, Color => Ochre)
    Text
     If certification is desired, which means the result is greater than 5, then add { \tt Certify => true }.
    Example
     (random Foo)(14, Certify => true)
  SeeAlso  
///
end

restart;
uninstallPackage"RandomFoo";
installPackage"RandomFoo";
viewHelp"RandomFoo";
