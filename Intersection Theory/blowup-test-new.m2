restart
loadPackage "Schubert2"
load "./blowups.m2"

-- blow up of P5 along the Veronese
P5 = flagBundle({1,5}, VariableNames=>{,z})
P2 = flagBundle({1,2})
B = intersectionRing P2
A = intersectionRing P5
incl = map(P5, P2, OO_P2(2))
(Ytilde,PN,PNmap,Ymap) = blowup(incl)
ct = ctop tangentBundle Ytilde
integral Ymap_* ct
assert( oo == 12 )
E = PNmap_* chern(0,OO_PN)
quadric = chern(1,OO_P5(2))
propertransform = (Ymap^* quadric) - E
-- conics tangent to 5 lines
assert (integral propertransform^5 == 1)
sextic = chern(1,OO_P5(6))
propertransform = (Ymap^* sextic) - 2* E
-- conics tangent to 5 general conics
integral propertransform^5
assert (integral propertransform^5 == 3264)

-- blow up a point on P^2
X = flagBundle({1,0}, VariableNames =>{s,q})
Y = flagBundle({1,2}, VariableNames =>{a,b})
f = X / point
i = map(Y,X, dual first bundles X)
(Ytilde, PN, PNmap, Ymap) = blowup(i)
assert (integral Ymap_* (E_0^2) == -1)
assert (integral PNmap^* E_0 == -1)
assert (integral ctop tangentBundle Ytilde == 4)

-- Blow up a twisted cubic in P^3, then check that the proper transforms
-- of three quadric surfaces containing that twisted cubic have product == 0
X = flagBundle({1,1})
Y = flagBundle({1,3})
i = map(Y, X, OO_X(3))
(Ytilde, PN, PNmap, Ymap) = blowup(i)
quadric = chern(1,OO_Y(2))
E = PNmap_* chern(0,OO_PN)
propertransform = (Ymap^* quadric) - E
assert(propertransform^3 == 0)
cubic = chern(1,OO_Y(3))
-- the same formula (see Eisenbud and Harris' book, section on
-- intersections of surfaces in P3 containing a curve) gives that intersecting
-- the proper transforms of two quadric surfaces containing our twisted cubic
-- with the proper transform of a cubic containing it should give 1
-- To visualize this, consider taking the cubic surface to be a quadric union
-- a hyperplane.  Then the hyperplane intersects the twisted cubic in three
-- points, so it intersects the other two quadrics in one point off of the
-- twisted cubic, and this formula counts that point.
assert(integral (propertransform^2 *((Ymap^* cubic) - E)) == 1)
