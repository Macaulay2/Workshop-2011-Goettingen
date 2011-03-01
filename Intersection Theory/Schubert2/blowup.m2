needsPackage "Schubert2"
needs "Schubert2/pushfor.m2"
blowup = method()
blowup(AbstractVariety, AbstractVariety, RingMap, Matrix) := 
  (X,Y,iupper, ilower) -> (
     -- eventually, the input will be an AbstractVarietyMap
     -- assumption: 
     A := intersectionRing Y;
     B := intersectionRing X;
     if A =!= source iupper then error "expected intersection ring";
     if B =!= target iupper then error "expected intersection ring";
     -- next line should be: 
     -- N := iupper tangentBundle Y - tangentBundle X;
     TY := abstractSheaf(X, Rank=>dim Y, ChernClass=>iupper chern tangentBundle Y);
     N :=  TY - tangentBundle X;
     x := local x;
     d := rank N;
     PN := projectiveBundle'(dual N, VariableNames => {,{x}}); -- x = chern(1,OO_PN(1))
     F := first PN.Bundles;
     C := intersectionRing PN;
     (BasAModule, bas, iLowerMod) := pushFwd iupper;
     -- iLowerMod(element b of B) = one column matrix over A whose product with bas is b
     n := numgens BasAModule;
     -- the fundamental idea: we build the Chow ring of the blowup as an algebra over A
     -- we introduce one algebra generator per basis element of B over A, and we let the first generator, E_0, play a special role:
     -- if z is the first chern class of OO_PN(-1), we think of E_0^j * E_i as z^j E_i.  In particular, E_0 itself we identify with 1_B.
     -- For this to work, we are depending on the ordering of pushFwd!
     D1 := A[E_0..E_(n-1), Join=>false];
     alphas := first entries bas;
     Ndual := dual N;
     blist := for i from 1 to d list chern(d-i, Ndual);
     -- three types of relations.
     -- 1. relations on the generators of B as an A-module
     -- After imposing these relations, we are left with the symmetric algebra Sym_A(B) where B is considered as an A-module
     I1 := ideal((vars D1 * (relations BasAModule)));
     -- 2. mult map on the E_i and E_j
     -- The multiplication of classes from PN in the Chow ring of the blowup is given by:
     -- if j_* is the pushforward from PN to the Chow ring of the blowup, then j_*(a) * j_*(b) = j_*(zab)
     I2 := promote( ideal select( flatten (
             for i from 1 to n-1 list 
	       for j from i to n-1 list (
		    f := (vars D1) * iLowerMod (alphas#i * alphas#j);
		    E_i * E_j - E_0 * f
	  )), x -> x != 0), D1);
     -- 3. linear relations
     -- This imposes the fundamental relations which express the Chow ring of the blowup as a group quotient of the A and the Chow ring of PN.
     -- Specifically, if b is an element of B, we impose that i_*(b) = b * -chern(d-1, Q) where Q = N / O(-1) is the universal quotient bundle
     -- on PN.
     I3 := ideal for i from 0 to n-1 list (
     	  f1 := matrix ilower * (iLowerMod alphas#i);
	  f2 := sum for j from 0 to d-1 list (
     	       E_0^j * ((vars D1) * iLowerMod(blist#j * alphas#i))
	       );
	  f1-f2);
     -- Finally, we impose the defining relation on the Chow ring of PN, that is, we impose that
     -- the sum of chern(1,O(-1))^i * chern(d-i, N) for i from 0 to d is 0. 
     I4 := ideal {sum for i from 0 to d list (
	       (-E_0)^i * ((vars D1) * iLowerMod(chern(d-i, N)))
	       )};
     D := D1/(I1 + I2 + I3 + I4);
     Ytilde := abstractVariety(dim Y, D);
     xpowers := matrix {for i from 0 to d-1 list x^i};
     E0powers := transpose matrix {for i from 0 to d-1 list (-E_0)^i};
     jLower := (f) -> (
	  -- takes an element f of C, returns an element of D
	  cf := last coefficients(f, Monomials => xpowers);
	  cf = lift(cf, B);
	  cfA := matrix {apply(flatten entries cf, iLowerMod)};
	  (vars D * cfA * E0powers)_(0,0)
	  );
     Ytilde.TangentBundle = abstractSheaf(Ytilde, 
	  ChernCharacter => ch tangentBundle Y - jLower(ch tangentBundle(PN/X) * (todd OO(x))^-1));
     (Ytilde, PN, jLower)
     )
