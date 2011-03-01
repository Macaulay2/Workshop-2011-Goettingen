restart
load "~/Goettingen-2011/parallel/parallel.m2"

allowableThreads = 3

-- This one works 
R = QQ[a,b,c,d];
I = ideal (a^2-2*a*b*c, d^3-4*a+19*b, a*d-2*a*c^2, a+b+c+b^19, 7*a^13*b^19+4*a^2-c^13+d^15);

pscan ({I,I,I,I,I,I,I,I}, gb);
