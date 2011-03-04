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
i = map(Y,X, OO_X)
(Ytilde, PN, PNmap, Ymap) = blowup(i)
E = PNmap_* chern(0,OO_PN)
assert (integral (E^2) == -1)
assert (integral PNmap^* E == -1)
assert (integral ctop tangentBundle Ytilde == 4)

-- blow up a point in P^7
X = flagBundle({1,0}, VariableNames =>{s,q})
Y = flagBundle({1,7}, VariableNames =>{a,b})
i = map(Y,X, dual first bundles X)
(Ytilde, PN, PNmap, Ymap) = blowup(i)
assert (integral ctop tangentBundle Ytilde == 14)

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

--The same check, with variables.  Again, see Eisenbud and Harris
B = base(r,s,t)
X = flagBundle({1,1},B)
Y = flagBundle({1,3},B)
i = map(Y,X,OO_X(3))
(Ytilde, PN, PNmap, Ymap) = blowup(i)
intersectionRing Ytilde
rsurf = chern(1,OO_Y(r))
ssurf = chern(1,OO_Y(s))
tsurf = chern(1,OO_Y(t))
E = PNmap_* chern(0,OO_PN)
rtrans = (Ymap^* rsurf) - E
strans = (Ymap^* ssurf) - E
ttrans = (Ymap^* tsurf) - E
rtrans*strans*ttrans
integral oo
assert(oo == r*s*t - 3 * (r + s + t) + 10)


-- G(2,5) is cut out by 5 quadrics in P^9
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
