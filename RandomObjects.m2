newPackage "RandomObjects"
export { "RandomObject", "Attempts", "Certify", "Create", "Types" }
RandomObject = new Type of MutableHashTable
random RandomObject := randomopts -> Object -> (
     if Object.?Function then return Object.Function;
     Object.Function = f := method ( Options => join(Object#Options, { Certify => false, Attempts => infinity }) );
     types := Object.Types;
     f types := opts -> args -> for i from 1 do (
	  if i > opts.Attempts then return null;
	  object := (Object.Create opts) args;
	  if object === null then continue;
	  if not opts.Certify then return object;
	  if Object.Certify(opts, args, object) then return object;
	  );
     f)
