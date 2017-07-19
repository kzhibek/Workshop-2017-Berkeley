----------------------------------------------------------------
--************************************************************--
--Functions for computing sigma                               --
--************************************************************--
----------------------------------------------------------------


--Computes Non-Sharply-F-Pure ideals over polynomial rings for (R, fm^{a/(p^{e1}-1)}), 
--at least defined as in Fujino-Schwede-Takagi.
sigmaAOverPEMinus1Poly ={HSL=> false}>> o -> (fm, a1, e1) -> ( 
     Rm := ring fm;
     pp := char Rm;
     m1 := 0;
	e2 := e1;
	a2 := a1;
	--if e1 = 0, we treat (p^e-1) as 1.  
     if (e2 == 0) then (e2 = 1; a2 = a1*(pp-1));
     if (a2 > pp^e2-1) then (m1 = floor((a2-1)/(pp^e2-1)); a2=((a2-1)%(pp^e2-1)) + 1 );
     --fpow := fm^a2;
     IN := frobeniusRoot(e2,ideal(1_Rm)); -- this is going to be the new value.
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  This stops after finitely many steps.  
     while (IN != IP) do(
		IP = IN;
	  	IN = frobeniusRootRingElements(e2,a2,fm,IP); -- frobeniusRoot(e2,ideal(fpow)*IP);
	  	count = count + 1
     );

     --return the final ideal and the HSL number of this function
     if (o.HSL == true) then {IP*ideal(fm^m1),count} else IP*ideal(fm^m1)
)

--Computes Non-Sharply-F-pure ideals for non-polynomial rings with respect to no pair.
sigmaQGor ={HSL=> false}>> o -> (Rm, gg) -> (
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     hk := findQGorGen(Rm, gg);
     
     IN := ideal(1_Sm);
     count := 0;
     IP := ideal(0_Sm);
     
     while (IN != IP) do(
     	IP = IN;
     	IN = frobeniusRoot(gg,ideal(hk)*IP);
     	count = count + 1
     );
     
     --return the ideal and HSL
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP, Rm)
)

--Computes Non-Sharply-F-Pure ideals for non-polynomial rings
--gg is the Gorenstein index
sigmaAOverPEMinus1QGor  ={HSL=> false}>> o -> (fk, a1, e1, gg) -> (
     Rm := ring fk;
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     pp := char Rm;
     ek := lcm(e1,gg); --we need to raise things to common powers
     hk := findQGorGen(Rm, gg); --it will be faster to find the Q-Gorenstein generator
     hl := hk^(sub((pp^ek - 1)/(pp^gg - 1), ZZ) ); --
	fm := lift(fk, Sm); --lift fk to the ambient ring
	fpow := fm^(a1*sub( (pp^ek - 1)/(pp^e1-1), ZZ) );


	IN := sigmaAOverPEMinus1Poly(hk,1,gg);
	count := 0;
	IP := ideal(0_Sm);

	while (IN != IP) do(
		IP = IN;
		IN = frobeniusRoot(e1, ideal(fpow*hl)*IP);
		count = count + 1
	);
	
     --return the final ideal
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP,Rm)
	
)



----------------------------------------------------------------
--************************************************************--
--Functions for checking whether a ring/pair is F-pure/regular--
--************************************************************--
----------------------------------------------------------------

-- Given an ideal I of polynomial ring R
-- this uses Fedder's Criterion to check if R/I is F-pure
-- Recall that this involves checking if I^[p]:I is in m^[p]
-- Note:  We first check if I is generated by a regular sequence.

isFPure = method(Options => {FrobeniusRootStrategy => Substitution, IsLocal=>false});

isFPure := I1->(
    local answer;
    p1:=char ring I1;
    if (o.IsLocal == true) then (
        maxIdeal:= monomialIdeal(first entries vars ring I1);  

        local cond;
    
        if codim(I1)==numgens(I1) then(
	        L:=flatten entries gens I1;
	        cond = isSubset(ideal(product(#L, l-> fastExp(p1-1,L#l))),frobenius( maxIdeal ));
        	if(cond==false) then answer=true else answer=false;
    	)
        else(
	        cond = isSubset((frobenius( I1 )):I1,frobenius( maxIdeal ));
        	if(cond==false) then answer=true else answer=false;
	    );    
    )
    else (
        nonFPureLocus := frobeniusRoot(1, frobenius(I1) : I1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy );
        if (nonFPureLocus == ideal(sub(1, ideal(I1)))) then answer = true else answer = false;
    );
    answer
);



--********************************************
--Some functions for the purpose of checking whether a map of rings is a splitting.  It also computes images of (field) trace.
--********************************************

needsPackage "PushForward"; 

--checks whether f1 : R1 -> S1 splits as a map of R1-modules
isMapSplit = (f1) -> (
	J1 := imageOfRelativeCanonical(f1);
	val := false;
	if (1 % J1 == 0) then val = true;
	
	val
)

--computes the image of Hom_R1(S1, R1) -> R1.
imageOfRelativeCanonical = (f1) -> (
	outList := pushFwd(f1);
--	myGenerators := first entries (outList#1);	
	target1 := (outList#2)(sub(1, target f1));
	
	h1 := map(outList#0, (source f1)^1, target1);
	
	d1 := Hom(h1, (source f1)^1);
	
	trim ideal( first entries gens image d1)
)

--computes the image of trace : S \to R if S is a finite R-module.
imageOfTrace = (f1) -> (
	print "Warning, this only works right now if S is a free module.  We should try to fix it...";
	outList := pushFwd(f1);
	myGenerators := first entries (outList#1);	
	i := 0;
	traceList := {};
	newMap := null;
	newMatrix := null;
	S1 := target f1;
	
	while (i < #myGenerators) do (
		newMap = map(S1^1, S1^1, {{myGenerators#i}});
		newMatrix = pushFwd(newMap, f1);
		traceList = append(traceList, trace newMatrix);
		i = i+1;
	);
	
	trim ideal traceList
)


