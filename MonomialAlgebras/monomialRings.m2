doc ///
   Key
   Headline
   Usage
   Inputs
   Outputs
   Consequences
    Item
   Description
    Text
    Code
    Pre
    Example
   Subnodes
   Caveat
   SeeAlso
///




--next case to write: Simplicial semigroups, any dimension.

--In general, if a ``base''
--semigroup generated by B \subset NN^n generates a lattice L subset ZZ^n,
--of finite index, then for any intermediate semigroup 
-- B \subset A \subset NN^n
--such that A generates all of ZZ^n
--the semigroup ring of B decomposes into fractional ideals indexed by ZZ^/L.
--(maybe this is proven by Hoa+Stueckrad)

decomposeMonomialCurve = A -> (
     if not gcd A ==1 then print "WARNING: exponents not relatively prime";
n := #A;
d := max A;
deglist := prepend({0,d}, for i from 0 to n-1 list {A_i, d-A_i});
S := kk[x_0..x_n, Degrees =>deglist];
P := kk[s,t, Degrees =>{{1,0}, {0,1}}];
maplist := deglist/(D->s^(D_1)*t^(D_0));
I := ker map(P,S,maplist);
N := S^1/(ideal(x_0,x_n)+I);
bN := basis N;
L := partition(p -> (first p)%d, last degrees bN);
--replace each value by itself normalized then divided by d, 
--with a twist to show the amount of normalization.
L1 := applyValues(L,LL -> (
	  min1 := min(LL/first);
	  min2 := min(LL/last);
	  LL1 := {LL/(p->{(first p - min1)//d, (last p - min2)//d}),  (min1+min2)//d}
     ));
a:=local a;
b:=local b;
T := kk[a,b];
--Now make ideals in T by grouping the degrees in genDegs by congruence class.
applyValues(L1, LL->( 
     (ideal apply(first LL, m->T_0^(first m)*T_1^(last m)))*(T^{-last LL}))
	  )
)
{*
--under construction!
decomposeMonomialAlgebra = A -> (
--A should be a list of elements of NN^(m-1), all of total degree <=d, (thought of
--as homogeneous elements of degree d in NN^m.
n = #A;
d = max A;
deglist = prepend({0,d}, for i from 0 to n-1 list {A_i, d-A_i});
S = kk[x_0..x_n, Degrees =>deglist];
P = kk[s,t, Degrees =>{{1,0}, {0,1}}];
maplist = deglist/(D->s^(D_1)*t^(D_0));
I = ker map(P,S,maplist);
N = S^1/(ideal(x_0,x_n)+I);
bN = basis N;
L = partition(p -> (first p)%d, last degrees bN);
--replace each value by itself normalized then divided by d, 
--with a twist to show the amount of normalization.
L1 = applyValues(L,LL -> (
	  min1 = min(LL/first);
	  min2 = min(LL/last);
	  LL1 = {LL/(p->{(first p - min1)//d, (last p - min2)//d}),  (min1+min2)//d}
     ));
a:=local a;
b:=local b;
T = kk[a,b];
--Now make ideals in T by grouping the degrees in genDegs by congruence class.
applyValues(L1, LL->( 
     (ideal apply(first LL, m->T_0^(first m)*T_1^(last m)))*(T^{-last LL}))
	  )
)
*}

homog = A ->(
     d := max (A/sum);
     A/(a->append(a, d-sum a))
     )

monomialAlgebra = (R,A) -> (
     --R should be a standard poly ring with at least as many vars as #A.
     --#A is a list of lists of ZZ, all of the same length m-1.
     --forms the ideal in R corresponding defining the monomial algebra
     --generated by monomials x^(B_i), where B is the list of homogenizations
     -- of the lists in A.
     d := max (A/sum);
     B = homog A;
     n = #B;
     nR = numgens R;
     if nR < n then error "not enough variables in R";
     t := local t;
     k:= coefficientRing R;
     T = k[t_0..t_(#A_0)];
     targ =  apply(B, b -> product(apply (#b, i-> t_i^(b_i))));
     Targ = targ |splice {nR-n:0_T};
     ker map(T,R,Targ)
     )
     
     
///
restart
load "~/src/Goettingen-2011/monomialRings.m2"
A = {{1,2},{3,0}, {0,4},{0,5}} -- increasing integers, initial zero implied
S = kk[a,b,c,d,e]
monomialAlgebra (S,A)
B
homog B
M = transpose matrix B
gens gb image M
--decomposeMonomialAlgebra A

///


maxNumGens = H -> max ((values H)/numgens)


end

restart
load "~/src/Goettingen-2011/monomialRings.m2"
A = {1,3,4} -- increasing integers, initial zero implied
decomposeMonomialCurve A
for d from 4 to 10 do (
     A = {1,d-1,d};
     print A;
     print decomposeMonomialCurve A)

d=9
for a from 1 to d-2 do (
     A = {1,a,d-1, d};
     print A;
     print decomposeMonomialCurve A)


n = 3+random 20
A = {1}
g = 1
for i from 2 to n do (
     g1 = random(g+1,g+10);
     A = append(A,g1);
     g = g1)
A
#A
max A
maxNumGens (time L = decomposeMonomialCurve A)
--example with #A = 49, max A = 260 done in 30 sec.
L

