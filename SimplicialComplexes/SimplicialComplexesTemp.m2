-- -*- coding: utf-8-unix -*-
-- Code for Simplicial Complexes Extras

--------------------------------------------------------------------------------
-- Copyright 2017  Jason McCullough
-- 
-- You may redistribute this program under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2 of the
-- License, or any later version.
--------------------------------------------------------------------------------

-- Janko added class Face to be used in other packages
-- should not affect the functionality present previously

newPackage(
	"SimplicialComplexesTemp",  -- MERGE ME number 2
    	Version => "1.0", 
    	Date => "July 19, 2017",
    	Authors => {
	     {Name => "Jason McCullough", Email => "jmccullo@iastate.edu", HomePage => "http://users.rider.edu/~jmccullough"}
	     },
    	Headline => "simplicial complexes add-ons",
    	DebuggingMode => false,
	PackageExports=>{ "SimplicialComplexes"}
    	)


export {"simplicialJoin","poincareSphere","dunceHat","suspension","composition"}

-- Jason's area to work in

poincareSphere = method(Options=>{Variable => "x"})
poincareSphere(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_16];
    L := {{1,2,4,9},
	{1,2,4,15},
	{1,2,6,14},
	{1,2,6,15},
	{1,2,9,14},
	{1,3,4,12},
	{1,3,4,15},
	{1,3,7,10},
	{1,3,7,12},
	{1,3,10,15},
	{1,4,9,12},
	{1,5,6,13},
	{1,5,6,14},
	{1,5,8,11},
	{1,5,8,13},
	{1,5,11,14},
	{1,6,13,15},
	{1,7,8,10},
	{1,7,8,11},
	{1,7,11,12},
	{1,8,10,13},
	{1,9,11,12},
	{1,9,11,14},
	{1,10,13,15},
	{2,3,5,10},
	{2,3,5,11},
	{2,3,7,10},
	{2,3,7,13},
	{2,3,11,13},
	{2,4,9,13},
	{2,4,11,13},
	{2,4,11,15},
	{2,5,8,11},
	{2,5,8,12},
	{2,5,10,12},
	{2,6,10,12},
	{2,6,10,14},
	{2,6,12,15},
	{2,7,9,13},
	{2,7,9,14},
	{2,7,10,14},
	{2,8,11,15},
	{2,8,12,15},
	{3,4,5,14},
	{3,4,5,15},
	{3,4,12,14},
	{3,5,10,15},
	{3,5,11,14},
	{3,7,12,13},
	{3,11,13,14},
	{3,12,13,14},
	{4,5,6,7},
	{4,5,6,14},
	{4,5,7,15},
	{4,6,7,11},
	{4,6,10,11},
	{4,6,10,14},
	{4,7,11,15},
	{4,8,9,12},
	{4,8,9,13},
	{4,8,10,13},
	{4,8,10,14},
	{4,8,12,14},
	{4,10,11,13},
	{5,6,7,13},
	{5,7,9,13},
	{5,7,9,15},
	{5,8,9,12},
	{5,8,9,13},
	{5,9,10,12},
	{5,9,10,15},
	{6,7,11,12},
	{6,7,12,13},
	{6,10,11,12},
	{6,12,13,15},
	{7,8,10,14},
	{7,8,11,15},
	{7,8,14,15},
	{7,9,14,15},
	{8,12,14,15},
	{9,10,11,12},
	{9,10,11,16},
	{9,10,15,16},
	{9,11,14,16},
	{9,14,15,16},
	{10,11,13,16},
	{10,13,15,16},
	{11,13,14,16},
	{12,13,14,15},
	{13,14,15,16}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)

dunceHat = method(Options=>{Variable => "x"})
dunceHat(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_16];
    L := {{1,2,4},
{1,2,7},
{1,2,8},
{1,3,4},
{1,3,5},
{1,3,6},
{1,5,6},
{1,7,8},
{2,3,5},
{2,3,7},
{2,3,8},
{2,4,5},
{3,4,8},
{3,6,7},
{4,5,6},
{4,6,8},
{6,7,8}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)

-- end Jason's work area

-- Claudiu's work area

--experts say that we only need | for joining simplicial complexes

externalJoin = method()
externalJoin(SimplicialComplex,SimplicialComplex) := (S1,S2) -> (
    R1 := ring S1;
    R2 := ring S2;
    if R1 === R2 then internalJoin(S1,S2) else
    (
	R := R1 ** R2;
	n1 := numgens R1;
	n2 := numgens R2;
	i1 := map(R,R1,apply(n1,j -> R_j));
	i2 := map(R,R2,apply(n2,j -> R_(n1+j)));
	newS1 := simplicialComplex apply(flatten entries facets S1,f -> i1(f));
	newS2 := simplicialComplex apply(flatten entries facets S2,f -> i2(f));
	internalJoin(newS1,newS2)
	)
    )
---internal join of simplical complexes
--given two simplicial complexes S1,S2, the internal join
--computes the simplicical complex whose faces are the unions of
--faces of S1 and S2
internalJoin = method()
internalJoin(SimplicialComplex,SimplicialComplex) := (S1,S2) ->
(
    fS1 := flatten entries facets(S1);
    fS2 := flatten entries facets(S2);
    simplicialComplex(flatten for f1 in fS1 list for f2 in fS2 list lcm(f1,f2))
    ) 


SimplicialComplex | SimplicialComplex := (S1,S2) -> externalJoin(S1,S2)

cone(SimplicialComplex) := (S) -> (
    R := ring S;
    k := coefficientRing R;
    Q := k(monoid[getSymbol "X"]);
    point := simplicialComplex {Q_0};
    S | point
    )


suspension = method()
suspension(SimplicialComplex):= (S)-> (
    R := ring S;
    k := coefficientRing R;
    Q := k(monoid[getSymbol "X", getSymbol "Y"]);  
    points := simplicialComplex{Q_0,Q_1};
    S | points
    )




composition = method()
composition(SimplicialComplex, List) := (K,L)-> (
    RK := ring K ;
    m := numgens(RK); ---m is the size of the underlying set of the simplicial complex K
    R := apply(L, i->ring i);
    N := apply(R,i->numgens i);
    aux := R#0;
    for i from 1 to #R-1 do aux=aux**R#i ;
    Q := aux;
    ind := 0;
    inc := for i from 0 to #R-1 list (
    	I := apply(N#i, t->Q_(ind + t));
    	ind=ind + N#i;
    	map(Q,R#i, I  )
    	);
    listFacetsK := flatten entries facets(K);
    simplicialComplex flatten for monF in listFacetsK list(
    	F := {}; ---F is the index set of the facet of K corresponding to the monomial monF
    	FC := {}; ---FC is the complement of F in {1,...,m}
    	for i from 0 to m-1 do(
    	    if monF%RK_i==0 then F=F|{i} 
    	    else FC=FC|{i};
        );
        prodOverF := product for i in F list (inc#i)(product(gens(R#i)));
	---prodOverF is the product of the simplices corresponding to the 
	---simplicial complexes indexed by elements of F
        auxset := set{infinity};
    	for i in FC do(
    	    set2 := set( flatten entries inc#i(facets(L#i)) );
    	    auxset=auxset**set2;    
    	    );
    	tupfacets := toList auxset;
    	for tup in tupfacets list(
    	    auxtup := tup;
    	    partialfacet := product while auxtup =!= infinity list (
	    	auxfct := auxtup_1; auxtup = auxtup_0;auxfct);
    	    partialfacet*prodOverF    
    	    )
	)
)




end


----Claudiu's Test Area
restart
installPackage"SimplicialComplexesTemp"

r1 = QQ[a,b]
s1 = simplicialComplex {a,b}
r2 = QQ[a,c]
s2 = simplicialComplex {a,c}
s1 | s2

cone(s1)
suspension(s2)

-----


------bug?-----
restart
R1 = QQ[a]
R2 = QQ[a]
R = R1 ** R2
dim R
i1 = map(R,R1)
i2 = map(R,R2)
i1(R1_0) - i2(R2_0)


n1 = numgens R1
n2 = numgens R2
i1 = map(R,R1,apply(n1,j -> R_j))
i2 = map(R,R2,apply(n2,j -> R_(n1+j)))
i1(R1_0) - i2(R2_0)

----end Claudiu's Test Area


-- Jason test area --

restart
F = ZZ/2
loadPackage "SimplicialComplexesTemp"
S = poincareSphere(F,Variable => x)
T = dunceHat(F,Variable => y)
zero HH_1 S
zero HH_2 S
prune HH_3 S


-- end Jason test area



------Josh test area


---composition
restart
loadPackage "SimplicialComplexesTemp"
R=QQ[x_1,x_2,x_3,x_4]
R1=QQ[a,b,c,d]
R2=QQ[e,f,g]
K=simplicialComplex {x_1,x_2,x_3*x_4}
L1=simplicialComplex {a*b,b*d,d*c,a*c}
L2=simplicialComplex {e*f,f*g}
L={L1,L2,L2,L2}

composition(K,L)




-----------composition examples1
R=QQ[x,y,z]
O=QQ[o]
o1=simplicialComplex(monomialIdeal flatten entries vars O)
o1 = simplicialComplex{1_O}
K=simplicialComplex {x,y*z}
composition(K,splice{3:o1})
composition(o1,{K})


-----------composition examples2


o = getSymbol"o"
O=QQ[o_1..o_2]
R1=QQ[a,b]
R2=QQ[c,d]
S1=simplicialComplex {a,b}
S2=simplicialComplex {c,d}
o2= simplicialComplex{1_O}
composition(o2,{S1,S2})
S1|S2
