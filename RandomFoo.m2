needsPackage "RandomObjects"
newPackage "RandomFoo"
export { "Foo", "Color", "Blue" }
needsPackage "RandomObjects"
Foo = new RandomObject from {
     Types => ZZ,
     Options => {Color => Blue},
     Create => opts -> genus -> random 10 + genus,
     Certify => (opts, args, object) -> object > 5
     }
