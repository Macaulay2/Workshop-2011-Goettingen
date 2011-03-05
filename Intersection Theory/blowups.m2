needsPackage "PushForward"
needsPackage "Schubert2"

exceptionalDivisor = method()
exceptionalDivisor AbstractVariety := X -> (
     if X.?ExceptionalDivisor then X.ExceptionalDivisor else
     error "Variety is not a blowup")

blowup = method()
blowup(AbstractVarietyMap) := 
  (incl) -> (
     -- incl should be an inclusion of a closed subvariety.
     -- is this checkable in any way?
     -- could check whether rank N = difference in dimensions
     X := source incl;
     Y := target incl;
     A := intersectionRing Y;
     B := intersectionRing X;
     iuppermatrix := matrix {apply(gens A, a -> incl^* a)};
     iupper := map(B,A, iuppermatrix);
     N :=  (incl^* tangentBundle Y) - tangentBundle X;
     x := local x;
     d := rank N;
     if not (d == dim Y - dim X) then error "Expected a finite morphism";
     Ndual := dual N;
     PN := projectiveBundle'(Ndual, VariableNames => {,{x}}); -- x = chern(1,OO_PN(1))
     C := intersectionRing PN;
     (BasAModule, bas, iLowerMod) := pushFwd iupper;     
     -- iLowerMod(element b of B) = one column matrix over A whose product with bas is b
     n := numgens BasAModule;
     -- the fundamental idea: we build the Chow ring of the blowup as an algebra over A
     -- we introduce one algebra generator per basis element of B over A, and we let the first generator, E_0, play a special role:
     -- if z is the first chern class of OO_PN(-1), we think of E_0^j * E_i as z^j E_i.  In particular, E_0 itself we identify with 1_B.
     -- For this to work, we are depending on the ordering of pushFwd: the element 1_B must be the first generator returned!
     
     --The setup below will break if we ever end up with multigraded Chow rings, because pushFwd does not properly support multigraded maps
     E := getSymbol "E";
     D1 := A( monoid [E_0..E_(n-1), Join=>false, Degrees => (flatten degrees BasAModule) + splice{n:1}]);
     alphas := first entries bas;
     -- three types of relations.
     -- 1. relations on the generators of B as an A-module
     -- After imposing these relations, we are left with the symmetric algebra Sym_A(B) where B is considered as an A-module
     I1 := ideal((vars D1 * (relations BasAModule)));
     -- 2. mult map on the E_i and E_j
     -- The multiplication of classes from PN in the Chow ring of the blowup is given by:
     -- if j_* is the pushforward from PN to the Chow ring of the blowup, then j_*(a) * j_*(b) = j_*(zab)
     I2 := ideal flatten (
             for i from 1 to n-1 list 
	       for j from i to n-1 list (
		    f := (vars D1) * iLowerMod (alphas#i * alphas#j);
		    D1_(E_i) * D1_(E_j) - D1_(E_0) * f
	  ));
     -- 3. linear relations
     -- This imposes the fundamental relations which express the Chow ring of the blowup as a group quotient of the sum of A and the Chow ring of PN.
     -- Specifically, if b is an element of B, we impose that incl_*(b) = b * ctop(Q) where Q = N / O(-1) is the universal quotient bundle
     -- on PN.
     blist := for i from 1 to d list chern(d-i, Ndual);
     I3 := ideal for i from 0 to n-1 list (
     	  f1 := promote(incl_* (alphas#i), D1);
	  f2 := sum for j from 0 to d-1 list (
     	       D1_(E_0)^j * ((vars D1) * iLowerMod(blist#j * alphas#i))
	       );
	  f1 + (-1)^d * f2);
     -- Finally, we impose the defining relation on the Chow ring of PN, that is, we impose that
     -- the sum of chern(1,O(1))^i * chern(d-i, N) for i from 0 to d is 0. 
     I4 := ideal {sum for i from 0 to d list (
	       (-D1_(E_0))^i * ((vars D1) * iLowerMod(chern(d-i, N)))
	       )};
     I := trim (I1 + I2 + I3 + I4);
     D := D1/I; -- the Chow ring of the blowup
     Ytilde := abstractVariety(dim Y, D); 
     xpowers := matrix {for i from 0 to d-1 list x^i};
     E0powers := transpose matrix {for i from 0 to d-1 list (-D1_(E_0))^i};
     jLower := (f) -> (
	  -- takes an element f of C, returns an element of D
	  cf := last coefficients(f, Monomials => xpowers);
	  cf = lift(cf, B);
	  cfA := matrix {apply(flatten entries cf, iLowerMod)};
	  (vars D * cfA * E0powers)_(0,0)
	  );
     Ytilde.ExceptionalDivisor = abstractSheaf(Ytilde, Rank => 1, ChernClass => 1_D + D_(E_0));
     pushforwardPN := method();
     pushforwardPN C := a -> jLower a;
     -- to pull back a class from the blowup to PN we take E_i to -x*alphas#i; this corresponds to
     -- the fact that pushing forward and then pulling back a class on PN is the same as multiplying by x = c_1(O(1))
     jUpper := map(C, D, (for i from 0 to n-1 list -x * alphas#i) | flatten entries promote(iuppermatrix,C));
     pullbackPN := method();
     pullbackPN ZZ := pullbackPN QQ := a -> promote(a,C);
     pullbackPN D := a -> jUpper a;
     pullbackPN AbstractSheaf := F -> (
	  if variety F =!= Ytilde then error "pullback: variety mismatch";
	  abstractSheaf(PN,Rank => rank F,ChernClass => pullbackPN chern F));
     -- earlier formula, appears to be incorrect
     -- correct version: 
     -- ch tangentBundle Y - jLower(ch(tangentBundle(PN/X) ** OO_PN(-1)) * (todd OO_PN(-1))^-1)
     -- == ch tangentBundle Y - jLower(ch(dual first bundles PN) * (todd OO(-x))^-1)
     -- why this is correct: consider exact sequences:
     -- (a) 0 -> tangentBundle Ytilde -> tangentBundle Y -> j_* Q -> 0 (Q the univ. quotient bundle of rank d on PN)
     {*Ytilde.TangentBundle = abstractSheaf(Ytilde, 
	  ChernCharacter => ch tangentBundle Y - jLower(ch tangentBundle(PN/X) * (todd OO(x))^-1));*}
     Ytilde.TangentBundle2 = abstractSheaf(Ytilde,
	  ChernCharacter => ch tangentBundle Y - jLower(ch(dual first bundles PN) * (todd OO(-x))^-1));
     pullbackY := method();
     pullbackY ZZ := pullbackY QQ := pullbackY A := a -> promote(a,D);
     pullbackY AbstractSheaf := F -> (
	  if variety F =!= Y then error "pullback: variety mismatch";
	  abstractSheaf(Ytilde,Rank => rank F,ChernClass => pullbackY chern F)
	  );
     -- We construct the tangent bundle using GRR without denominators
     -- Specifically, we use the formula of Fulton Example 15.4.1
     g := PN / X;
     alpha := sum for j from 0 to d list (
     	  sum for k from 0 to d-j list (
	       (binomial(d-j, k) - binomial(d-j, k+1)) * x^k * (g^* chern(j, N))));
     Ytilde.TangentBundle = abstractSheaf(Ytilde,
	  Rank => dim Y,
	  ChernClass => chern(pullbackY tangentBundle Y) + jLower (chern(g^* tangentBundle X) * alpha));
     PNmap := new AbstractVarietyMap from {
	  global target => Ytilde,
	  global source => PN,
	  PushForward => pushforwardPN,
	  PullBack => pullbackPN
	  };
     pushforwardPN AbstractSheaf := F -> (
	  if variety F =!= PN then "pushforward: variety mismatch";
	  abstractSheaf(Ytilde, ChernCharacter => pushforwardPN (ch F * todd PNmap))
	  );
     -- to push forward from Ytilde to Y, consider a class a + b on Ytilde, where a is pulled back from Y and b is pushed forward from PN
     -- pushing forward a is easy: since the blowup is birational, we send a to itself on Y
     -- to push forward b, we find the coefficient in b of the relative class of a point in PN over X, then push this coefficient forward from X to Y
     -- BUT, the formulae of I3 already re-express the relative class of a point (which is E_0^(d-1)) in terms of lower-degree classes
     -- so pushing forward is as simple as taking the constant coefficient!
     pushforwardY := method();
     pushforwardY D := a -> (
	  lift(coefficient(1_D, a), A)
	  );
     Ymap := new AbstractVarietyMap from {
	  global target => Y,
	  global source => Ytilde,
	  PushForward => pushforwardY,
	  PullBack => pullbackY
	  };
     pushforwardY AbstractSheaf := F -> (
	  if variety F =!= Ytilde then error "pushforward: variety mismatch";
	  abstractSheaf(Y, ChernCharacter => pushforwardY (ch F * todd Ymap))
	  );
     integral D := a -> integral Ymap_* a;
     (Ytilde, PN, PNmap, Ymap)
     )

end
-- test/example code
restart
loadPackage "Schubert2"
load "./blowups.m2"
X = flagBundle({1,0}, VariableNames =>{s,q})
Y = flagBundle({1,2}, VariableNames =>{a,b})
f = X / point
i = map(Y,X, dual first bundles X)
(Ytilde, PN, PNmap, Ymap) = blowup(i)
assert (integral Ymap_* (E_0^2) == -1)
assert (integral PNmap^* E_0 == -1)
assert (integral ctop tangentBundle Ytilde == 4)

X = flagBundle({2,3}, VariableNames => {s,q})
S = first bundles X
L = exteriorPower(2, dual S)
Y = flagBundle({1,9}, VariableNames => {a,b})
i = map(Y,X,L)
(Ytilde, PN, PNmap, Ymap) = blowup(i)
E = PNmap_* chern(0, OO_PN)
quadric = chern(1,OO_Y(2))
propertransform = (Ymap^* quadric) - E
-- 5 generic quadrics containing the Grassmannian cut it out
propertransform^5
E^5
(Ymap^* quadric)^5
assert (propertransform^5 == 0)

intersectionRing Ytilde
Ymap_* E_0^9
Q = OO_PN^9 - first bundles PN
chern Q
i_*(q_3^2)
