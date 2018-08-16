--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%s
----------------------------------------------------------------------------------
-- CONTENTS
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

----------------------------------------------------------------------------------
-- Nu computations

-- Main functions: nuList, nu

-- Auxiliary Functions: nu1, binarySearch, binarySearchRecursive, linearSearch,
--     testPower, testRoot, testFrobeniusPower, nuInternal

----------------------------------------------------------------------------------
-- FThreshold approximations

-- Main functions: fptApproximation, ftApproximation, criticalExponentApproximation

----------------------------------------------------------------------------------
-- FThreshold computations and estimates

-- Main function: fpt

-- Auxiliary functions: fSig, isFRegularPoly

----------------------------------------------------------------------------------
-- FPT/F-Jumping number check

-- Main functions: isFPT, isFJumpingExponent

-- Auxiliary functions: sigma


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for computing (nu_I)^J(p^e), (nu_f)^J(p^e)
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


---------------------------------------------------------------------------------
-- nu1(I,J) finds the maximal N such that I^N is not contained in J, i.e., nu_I^J(1)
nu1 = method( TypicalValue => ZZ )

nu1 ( Ideal, Ideal ) :=  ZZ => ( I, J ) ->
(
    if not isSubset( I, radical J ) then
        error "nu1: The first ideal is not contained in the radical of the second";
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

-- for polynomials, we use fastExponentiation
nu1 ( RingElement, Ideal ) := ZZ => ( f, J ) ->
(
    if not isSubset( ideal f, radical J ) then
        error "nu1: The polynomial is not contained in the radical of the ideal";
    d := 1;
    while not isSubset( ideal fastExponentiation( d, f ), J ) do d = d + 1;
    d - 1
)

---------------------------------------------------------------------------------
-- TESTS
-- purpose is to verify containment in Frobenius powers

-- testRoot(J,a,I,e) checks whether J^a is a subset of I^[p^e] by checking whether (J^a)^[1/p^e] is a subset of I
testRoot = ( J, a, I, e ) -> isSubset( frobeniusRoot( e, a, J ), I )

-- testPower(J,a,I,e) checks whether J^a is  a subset of I^[p^e], directly
testPower = method( TypicalValue => Boolean )

testPower ( Ideal, ZZ, Ideal, ZZ ) := Boolean => ( J, a, I, e ) ->
    isSubset( J^a, frobenius( e, I ) )

-- for polynomials, use fastExponentiation
testPower ( RingElement, ZZ, Ideal, ZZ ) := Boolean => ( f, a, I, e ) ->
    isSubset( ideal fastExponentiation( a, f ), frobenius( e, I ) )

-- testFrobeniusPower(J,a,I,e) checks whether J^[a] is a subset of I^[p^e]
testFrobeniusPower = method( TypicalValue => Boolean )

testFrobeniusPower ( Ideal, ZZ, Ideal, ZZ ) := Boolean => ( J, a, I, e ) ->
    isSubset( frobeniusPower( a, J ), frobenius( e, I ) )

testFrobeniusPower ( RingElement, ZZ, Ideal, ZZ ) := Boolean => ( f, a, I, e ) ->
    testRoot( f, a, I, e )

-- hash table to select test function from option keyword
test := new HashTable from
    {
	FrobeniusPower => testFrobeniusPower,
	FrobeniusRoot => testRoot,
	StandardPower => testPower
    }

---------------------------------------------------------------------------------
-- SEARCH FUNCTIONS

-- Each *Search(I,J,e,a,b,testFunction) searches for the last n in [a,b) such that
-- testFunction(I,n,J,e) is false, assuming that test(I,a,J,e) is false and test(I,b,J,e)
-- is true.

-- Non-recursive binary search, based on our previous code
binarySearch = ( I, J, e, startPt, endPt, testFunction ) ->
(
    a := startPt;
    b := endPt;
    local c;
    while b > a+1 do
    (
	c = floor( (a+b)/2 );
	if testFunction( I, c, J, e ) then b = c else a = c
    );
    a
)

-- Recursive binary search
binarySearchRecursive = ( I, J, e, a, b, testFunction ) ->
(
    if b <= a+1 then return a;
    c := floor( (a+b)/2 );
    if testFunction( I, c, J, e )
        then binarySearchRecursive( I, J, e, a, c, testFunction )
	else binarySearchRecursive( I, J, e, c, b, testFunction )
)

-- Linear search
linearSearch = ( I, J, e, a, b, testFunction ) ->
(
    c := a+1;
    while not testFunction( I, c, J, e ) do c = c+1;
    c-1
)

-- hash table to select search function from option keyword
search := new HashTable from
    {
	Binary => binarySearch,
	BinaryRecursive => binarySearchRecursive,
	Linear => linearSearch
    }

---------------------------------------------------------------------------------
-- OPTION PACKAGES

optNuList :=
{
    ContainmentTest => null,
    UseColonIdeals => false,
    Search => Binary
}

optNu := optNuList | { ComputePreviousNus => true }

---------------------------------------------------------------------------------
-- INTERNAL FUNCTION

nuInternal = optNu >> o -> ( n, f, J ) ->
(
    -- Return answer in a trivial case (per Blickle-Mustata-Smith convention)
    if f == 0 then return toList( (n+1):0 );

    -- Verify if option values are valid
    checkOptions( o,
	{
	    ContainmentTest => { StandardPower, FrobeniusRoot, FrobeniusPower, null },
	    Search => { Binary, Linear, BinaryRecursive },
	    UseColonIdeals => Boolean,
	    ComputePreviousNus => Boolean
	}
    );

    -- Check if f is in a polynomial ring over a finite field
    if not isPolynomialRingOverFiniteField ring f then
        error "nuInternal: expected polynomial or ideal in a polynomial ring over a finite field";
    -- Setup
    p := char ring f;
    isPrincipal := if isIdeal f then (numgens trim f) == 1 else true;
    searchFct := search#(o.Search);
    comTest := o.ContainmentTest;
    -- choose appropriate containment test, if not specified by user
    if comTest === null then
	comTest = if instance(f, RingElement) then FrobeniusRoot
	    else StandardPower;
    testFct := test#(comTest);
    local N;

    nu := nu1( f, J ); -- if f is not in rad(J), nu1 will return an error
    theList := { nu };

    if not o.ComputePreviousNus then
    (
	-- This computes nu in a non-recursive way
	if n == 0 then return theList;
 	N = if isPrincipal or comTest === FrobeniusPower
	     then p^n else (numgens trim J)*(p^n-1)+1;
     	return { searchFct( f, J, n, nu*p^n, (nu+1)*N, testFct ) }
    );
    if o.UseColonIdeals and isPrincipal then
    -- colon ideals only work for polynomials
    (
	-- This computes nu recursively, using colon ideals.
	-- Only nu(p)'s are computed, but with respect to ideals other than J
	I := J;
	g := if isIdeal f then (trim f)_*_0 else f;
	scan( 1..n, e ->
	    (
		I = I : ideal( fastExponentiation( nu, g ) );
		nu =  last nuInternal( 1, g, I, ContainmentTest => comTest );
	      	theList = append( theList, p*(last theList) + nu );
	      	I = frobenius I
	    )
	)
    )
    else
    (
	N = if isPrincipal or comTest === FrobeniusPower
	     then p else (numgens trim J)*(p-1)+1;
	scan( 1..n, e ->
	    (
		nu = searchFct( f, J, e, p*nu, (nu+1)*N, testFct );
    	       	theList = append( theList, nu )
    	    )
    	)
     );
     theList
)

---------------------------------------------------------------------------------
-- EXPORTED METHODS

nuList = method( Options => optNuList, TypicalValue => List );

nuList ( ZZ, Ideal, Ideal ) := List => o -> ( e, I, J ) ->
    nuInternal( e, I, J, o )

-- Dan: I changed Options => true to Options => optNuList above in order to make
-- things compile, and I'm worried that's messing up our default options here.

nuList ( ZZ, RingElement, Ideal ) := List => o -> ( e, I, J ) ->
    nuInternal( e, I, J, o )

nuList ( ZZ, Ideal ) :=  List => o -> ( e, I ) ->
    nuList( e, I, maxIdeal I, o )

nuList ( ZZ, RingElement ) := List => o -> ( e, f ) ->
    nuList( e, f, maxIdeal f, o )


nu = method( Options => optNu, TypicalValue => ZZ );

nu ( ZZ, Ideal, Ideal ) := ZZ => o -> ( e, I, J ) ->
    last nuInternal( e, I, J, o )

nu ( ZZ, RingElement, Ideal ) := ZZ => o -> ( e, f, J ) ->
    last nuInternal( e, f, J, o )

nu ( ZZ, Ideal ) := ZZ => o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu ( ZZ, RingElement ) := ZZ => o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

-- Nus can be computed using generalized Frobenius powers, by using
-- ContainmentTest => FrobeniusPower. For convenience, here are some shortcuts:

muList = method( Options => optNuList );
muList ( ZZ, Ideal, Ideal) := o -> (e, I, J) ->
    nuList( e, I, J, o, ContainmentTest => FrobeniusPower );

muList ( ZZ, Ideal) := o -> (e, I) ->
    nuList( e, I, o, ContainmentTest => FrobeniusPower );

muList ( ZZ, RingElement, Ideal) := o -> (e, f, J) ->
    nuList( e, f, J, o, ContainmentTest => FrobeniusPower );

muList ( ZZ, RingElement ) := o -> (e, f) ->
    nuList( e, f, o, ContainmentTest => FrobeniusPower );

mu = method( Options => optNu);
mu ( ZZ, Ideal, Ideal) := o -> (e, I, J) -> nu( e, I, J, ContainmentTest => FrobeniusPower );

mu ( ZZ, Ideal) := o -> (e, I) -> nu( e, I, ContainmentTest => FrobeniusPower );

mu ( ZZ, RingElement, Ideal) := o -> (e, f, J) -> nu( e, f, J, ContainmentTest => FrobeniusPower );

mu ( ZZ, RingElement) := o -> (e, f) -> nu(e, f, ContainmentTest => FrobeniusPower );
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for approximating, guessing, estimating F-Thresholds and crit exps
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Approximates the F-pure Threshold
--Gives a list of nu_I(p^d)/p^d for d=1,...,e
fptApproximation = method( TypicalValue => List )

fptApproximation ( ZZ, Ideal ) := List => ( e, I ) ->
(
     p := char ring I;
     nus := nuList( e, I );
     apply( nus, 0..e, (n,k) -> n/p^k )
)

fptApproximation ( ZZ, RingElement ) := List => ( e, f ) ->
    fptApproximation( e, ideal f )

--Approximates the F-Threshold with respect to an ideal J
--More specifically, this gives a list of nu_I^J(p^d)/p^d for d=1,...,e

ftApproximation = method( TypicalValue => List )

ftApproximation ( ZZ, Ideal, Ideal ) := List => ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then
        error "ftApproximation: F-threshold undefined";
    p := char ring I;
    nus := nuList( e, I, J );
    apply( nus, 0..e, (n,k) -> n/p^k )
)

ftApproximation ( ZZ, RingElement, Ideal ) := List => ( e, f, J ) ->
   ftApproximation( e, ideal(f), J )

criticalExponentApproximation = method( TypicalValue => List )

criticalExponentApproximation ( ZZ, Ideal, Ideal ) := List => ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then
        error "criticalExponentApproximation: critical exponent undefined";
    p := char ring I;
    mus := muList( e, I, J );
    apply( mus, 0..e, (n,k) -> n/p^k )
)

criticalExponentApproximation (ZZ, RingElement, Ideal) := List => ( e, f, J ) ->
    criticalExponentApproximation( e, ideal f, J )

--Gives a list of guesses for the F-pure threshold of f.  It returns a list of all numbers in
--the range suggested by nu(e,  ) with maxDenom as the maximum denominator
fptGuessList = ( f, e, maxDenom ) ->
(
    n := nu(e,f);
    p := char ring f;
    findNumberBetween( maxDenom, n/(p^e-1), (n+1)/p^e )
)

----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------

--- Computes the F-signature for a specific value a/p^e
--- Input:
---	f - some polynomial in two or three variables in a ring R of PRIME characteristic
---	a - some positive integer between 0 and p^e
---	e - some positive integer
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Code is based on work of Eric Canton
fSig = ( f, a, e ) ->
(
     R := ring f;
     p := char R;
     1 - p^( -e * dim( R ) ) * degree( frobenius( e, maxIdeal R ) + ideal( fastExponentiation( a, f ) ) )
)

-- F-pure threshold estimation, at the origin.
-- e is the max depth to search in.
-- FRegularityCheck is whether the last isFRegularPoly is run (which can take a significant amount of time).
-- This is essentially the same as the old estFPT, with a couple more tests, and changes to make the code clearer.
fpt = method(
    Options =>
        {
	    FRegularityCheck => true,
	    Verbose => false,
	    UseSpecialAlgorithms => true,
	    NuCheck => true,
	    DepthOfSearch => 1
	}
);

fpt RingElement := o -> f ->
(
    -- give an answer in a trivial case
    if f == 0 then return 0;

    -- Check if option values are valid
    checkOptions( o,
        {
	    FRegularityCheck => Boolean,
	    Verbose => Boolean,
	    UseSpecialAlgorithms => Boolean,
	    NuCheck => Boolean,
	    DepthOfSearch => ( k -> instance( k, ZZ ) and k > 0 )
	}
    );

    -- Check if polynomial has coefficients in a finite field
    if not isPolynomialOverFiniteField f  then
        error "fpt: expected polynomial with coefficients in a finite field";

    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at
    p := char ring f;
    if not isSubset( ideal f, M ) then
        error "fpt: polynomial is not in the homogeneous maximal ideal";

    if o.Verbose then print "\nStarting fpt ...";

    -- Check if fpt equals 1
    if not isSubset( ideal f^(p-1), frobenius M ) then
    (
        if o.Verbose then print "\nnu(1,f) = p-1, so fpt(f) = 1.";
        return 1
    );

    if o.Verbose then print "\nfpt is not 1 ...";

    -- Check if one of the special FPT functions can be used...

    if o.UseSpecialAlgorithms then
    (
	if o.Verbose then print "\nVerifying if special algorithms apply...";
	if isDiagonal f then
	(
	    if o.Verbose then
	        print "\nPolynomial is diagonal; calling diagonalFPT ...";
            return diagonalFPT f
        );
        if isBinomial f then
        (
            if o.Verbose then
	        print "\nPolynomial is a binomial; calling binomialFPT ...";
            return binomialFPT f
        );
        if isBinaryForm f then
        (
            if o.Verbose then
	        print "\nPolynomial is a binary form; calling binaryFormFPT ...";
            return binaryFormFPT( f, Verbose => o.Verbose )
        )
    );

    if o.Verbose then print "\nSpecial fpt algorithms were not used ...";

    -- Compute nu(e,f)
    e := o.DepthOfSearch;
    n := nu( e, f );

    if o.Verbose then
         print( "\nnu has been computed: nu(" | toString(e) | ",f) = " | toString n | " ..." );

    -- If nu = 0, we just return some information
    if n == 0 then
    (
	if o.Verbose then
	    print "\nThe nu computed isn't fine enough. Try using a higher value for the option DepthOfSearch.";
	return { 0, 1/p^e }
    );

    -- Check to see if either nu/(p^e-1) or (nu+1)/p^e is the fpt
    if o.NuCheck then
    (
        -- Check to see if nu/(p^e-1) is the fpt
	-- (uses the fact that there are no fpts between nu/p^e and nu/(p^e-1))
	if not isFregular( n/(p^e-1), f ) then
	(
	    if o.Verbose then print "\nFound answer via nu/(p^e-1).";
	    return n/(p^e-1)
	)
      	else if o.Verbose then print "\nnu/(p^e-1) is not the fpt ...";

        --check to see if (nu+1)/p^e is the FPT
	if isFPT( (n+1)/p^e, f ) then
	(
	    if o.Verbose then print "\nFound answer via (nu+1)/(p^e).";
	    return (n+1)/p^e
	)
      	else if o.Verbose then print "\n(nu+1)/p^e is not the fpt ..."
    );

    -- Do the F-signature computation
    local s1;
    local s2;

    if o.Verbose then print "\nBeginning F-signature computation ...";
    s2 = fSig( f, n, e );
    if o.Verbose then
        print( "\nFirst F-signature computed: s(f,nu/p^e) = " | toString s2 | " ..." );
    s1 = fSig( f, n-1, e );
    if o.Verbose then
	print( "\nSecond F-signature computed: s(f,(nu-1)/p^e) = " | toString s1 | " ..." );

    a := xInt( (n-1)/p^e, s1, n/p^e, s2 );

    if o.Verbose then
        print( "\nComputed F-signature intercept: " | toString a | " ..." );

    -- Now check to see if F-signature line crosses at (nu+1)/p^e. If so, then that's the fpt
    if (n+1)/p^e == a then
    (
	if  o.Verbose then
	    print "\nF-signature line crosses at (nu+1)/p^e, so that is the fpt.";
	return a
    );

    if o.FRegularityCheck then
    (
	if o.Verbose then print "\nStarting final check ...";
        if not isFregular( a, f ) then
        (
	   if o.Verbose then
	       print "\nFinal check successful; fpt is the F-signature intercept.";
	   return a
      	)
	else if o.Verbose then print "\nFinal check didn't find the fpt ..."
    );

    if o.Verbose then
        print(
	    "\nfpt lies in the interval " |
	    ( if o.FRegularityCheck then "( " else "[ " ) |
	    toString a |
	    ", " |
	    toString( (n+1)/p^e ) |
	    ( if o.NuCheck then " )." else " ]." )
        );
    { a, (n+1)/p^e }
)

fpt ( List, List ) := o -> ( L, m ) -> 
binaryFormFPT( L, m, Verbose => o.Verbose )

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for checking if given numbers are F-jumping numbers
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--compareFPT see if a number is less than, equal to, or greater than the FPT.
--It returns -1 if less
--it returns 0 if equal
--it returns 1 if greater
compareFPT = method( Options => {MaxCartierIndex => 10, FrobeniusRootStrategy => Substitution, AssumeDomain=>true, QGorensteinIndex => 0});

--gets a nonzero generator of an ideal.
getNonzeroGenerator := (I2) -> (
    i := 0;
    flag := false;
    genList := first entries gens I2;
    localZero := sub(0, ring I2);
    while ((i < #genList) and (flag == false)) do (
        if (genList#i != localZero) then (
            flag = true;
        );
        i = i + 1;
    );
    if (flag == true) then (
        genList#(i-1)
    )
    else (
        null
    )
);

isLocallyPrincipalIdeal := (I2) -> (
    localGen := getNonzeroGenerator(I2);
    if (localGen === null) then (
        return {false, sub(0, ring I2)};
    );
    inverseIdeal := (ideal(localGen) : I2);
    idealProduct := inverseIdeal*I2;
    isLocPrinc := (reflexify(idealProduct) == idealProduct);
    if (isLocPrinc == true) then (
        return {true, inverseIdeal};
    )
    else (
        return {false, sub(0, ring I2)};
    );

);

--helper function for compareFPT
getDivisorIndex = method();
getDivisorIndex := (maxIndex, divisorialIdeal) -> (
    fflag := false;
    cartIndex := 0;
    curIdeal := null;
    locPrincList := null;
    while ( (fflag == false) and (cartIndex < maxIndex) ) do (
        cartIndex = cartIndex + 1;
        curIdeal = reflexivePower(cartIndex, divisorialIdeal);
        locPrincList = isLocallyPrincipalIdeal(curIdeal);
        if (locPrincList#0 == true) then (
            fflag = true;
        );
    );
    if ((cartIndex <= 0) or (fflag == false)) then error "getDivisorIndex: Ring does not appear to be Q-Gorenstein, perhaps increase the option MaxCartierIndex.  Also see the documentation for isFregular.";
    return cartIndex;
);

compareFPT(Number, RingElement) := o -> (t, f) -> (
    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if (class(R1) === PolynomialRing) then return compareFPTPoly(t, f);
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := canonicalIdeal(R1);
    pp := char R1;
    cartIndex := 0;
    fList := {f};
    tList := {t};
    local computedTau;
    local computedHSLGInitial;
    local computedHSLG;
    --computedTau := ideal(sub(0, R1));

    if (o.QGorensteinIndex > 0) then (
        cartIndex = o.QGorensteinIndex;
    )
    else (
        cartIndex = getDivisorIndex(o.MaxCartierIndex, canIdeal);
    );
    h1 := sub(0, S1);
    --first we do a quick check to see if the test ideal is easy to compute
    if ((pp-1)%cartIndex == 0) then (
        J1 := testElement( R1 );
        try (h1 = QGorensteinGenerator( 1, R1)) then (
            computedTau = testModule(tList, fList, ideal(sub(1, R1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain);
            if (isSubset(ideal(sub(1, R1)), computedTau#0)) then return -1;  --at this point we know that this is not the FPT
        ) else (
             h1 = sub(0, S1);
        )
    );
    --now compute the test ideal in the general way (if the index does not divide...)
    gg := first first entries gens trim canIdeal;
    dualCanIdeal := (ideal(gg) : canIdeal);
    nMinusKX := reflexivePower(cartIndex, dualCanIdeal);
    gensList := first entries gens trim nMinusKX;

    runningIdeal := ideal(sub(0, R1));
    omegaAmb := sub(canIdeal, S1) + ideal(R1);
    u1 := (frobeniusTraceOnCanonicalModule(I1, omegaAmb));

    t2 := append(tList, 1/cartIndex);
    f2 := fList;

    for x in gensList do (
        f2 = append(fList, x);
        runningIdeal = runningIdeal + (testModule(t2, f2, canIdeal, u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain))#0;
    );

    newDenom := reflexify(canIdeal*dualCanIdeal);
    computedTau = (runningIdeal*R1) : newDenom;
    if (isSubset(ideal(sub(1, ambient R1)), computedTau)) then return -1;  --at this point we know that this is not the FPT

    --now we have to run the sigma computation
    if (not (h1 == (sub(0, R1)))) then (
        baseTau:= testModule(0/1, sub(1, R1), ideal(sub(1, R1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain);
        if (not isSubset(ideal(sub(1, R1)), (baseTau#0))) then error "compareFPT: The ambient ring must be F-regular."; --the ambient isn't even F-regular
        decomposedExponent := decomposeFraction(pp, t, NoZeroC => true);
        a1 := decomposedExponent#0;
        b1 := decomposedExponent#1;
        c1 := decomposedExponent#2;
        if (a1 > (pp^c1-1)) then(
            a1quot := floor( (a1-1)/(pp^c1 - 1));
            a1rem := a1 - (pp^c1-1)*a1quot;
            computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, baseTau#0, {h1});
            computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, f}, computedHSLGInitial#0);
        )
        else (
            computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, baseTau#0, {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
            computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, computedHSLGInitial#0);
        );
        if (not isSubset(ideal(sub(1, R1)), computedHSLG)) then return 1; --the fpt we picked is too small
    )
    else(--there should be an algorithm that works here
        error "compareFPT:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";
    );
    return 0; --it is the FPT!
);

compareFPTPoly = method(Options => {FrobeniusRootStrategy => Substitution});

compareFPTPoly(Number, RingElement) := o -> (t, f) -> (
    --first we gather background info on the ring (QGorenstein generators, etc.)
    S1 := ring f;
    pp := char S1;
    cartIndex := 0;
    fList := {f};
    tList := {t};
    local computedTau;
    local computedHSLG;
    local computedHSLGInitial;
    --computedTau := ideal(sub(0, R1));

    h1 := sub(1, S1);
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = testModule(tList, fList, ideal(sub(1, S1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>true);
    if (isSubset(ideal(sub(1, S1)), computedTau#0)) then return -1;  --at this point we know that this is not the FPT

    --now we have to run the sigma computation
    decomposedExponent := decomposeFraction(pp, t, NoZeroC => true);
    a1 := decomposedExponent#0;
    b1 := decomposedExponent#1;
    c1 := decomposedExponent#2;
    if (a1 > (pp^c1-1)) then(
        a1quot := floor( (a1-1)/(pp^c1 - 1));
        a1rem := a1 - (pp^c1-1)*a1quot;
        computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, ideal(sub(1, S1)), {h1});
        computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, f}, computedHSLGInitial#0);
    )
    else (
        computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, ideal(sub(1, S1)), {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, computedHSLGInitial#0);
    );
    if (not isSubset(ideal(sub(1, S1)), computedHSLG)) then return 1; --the fpt we picked is too small

    return 0; --it is the FPT!
);


--isFPT, determines if a given rational number is the FPT of a pair in a
-- polynomial ring.

isFPT = method( Options => {MaxCartierIndex => 10, FrobeniusRootStrategy => Substitution, AssumeDomain=>true, QGorensteinIndex => 0} )


-- Dan: We should use the "Origin" option somehow... 
isFPT ( Number, RingElement ) := o -> ( t, f ) ->
(
    return (0 == compareFPT(t/1, f, MaxCartierIndex => o.MaxCartierIndex, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain, QGorensteinIndex => o.QGorensteinIndex ));
);

-- isFJumpingExponent determines if a given rational number is an
-- F-jumping exponent
--***************************************************************************
--This needs to be speeded up, like the above function
--***************************************************************************

-- Dan: isn't is safer to have AssumeDomain default to "false" here?
isFJumpingExponent = method( Options => {MaxCartierIndex => 10, FrobeniusRootStrategy => Substitution, AssumeDomain=>true, QGorensteinIndex => 0} )

isFJumpingExponent ( Number, RingElement ) := o -> ( t, f ) ->
(
    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if (class(R1) === PolynomialRing) then return isFJumpingExponentPoly(t, f);
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := canonicalIdeal(R1);
    pp := char R1;
    cartIndex := 0;
    fList := {f};
    tList := {t};
    computedTau := null;
    computedHSLG := null;
    computedHSLGInitial := null;
    --computedTau := ideal(sub(0, R1));

    if (o.QGorensteinIndex > 0) then (
        cartIndex = o.QGorensteinIndex;
    )
    else (
        cartIndex = getDivisorIndex(o.MaxCartierIndex, canIdeal);
    );
    h1 := sub(0, S1);
    --first we do a quick check to see if the test ideal is easy to compute
    if ((pp-1)%cartIndex == 0) then (
        J1 := testElement( R1 );
        try (h1 = QGorensteinGenerator( 1, R1)) then (
            computedTau = testModule(tList, fList, ideal(sub(1, R1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain);
        ) else (
             h1 = sub(0, S1);
        )
    )
    else(--there should be an algorithm that works here
        error "isFJumpingExponent:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";
    );

    --now compute the test ideal in the general way (if the index does not divide...)
    if (not (computedTau === null)) then ( --this code will be enabled eventually
        gg := first first entries gens trim canIdeal;
        dualCanIdeal := (ideal(gg) : canIdeal);
        nMinusKX := reflexivePower(cartIndex, dualCanIdeal);
        gensList := first entries gens trim nMinusKX;

        runningIdeal := ideal(sub(0, R1));
        omegaAmb := sub(canIdeal, S1) + ideal(R1);
        u1 := (frobeniusTraceOnCanonicalModule(I1, omegaAmb));

        t2 := append(tList, 1/cartIndex);
        f2 := fList;

        for x in gensList do (
            f2 = append(fList, x);
            runningIdeal = runningIdeal + (testModule(t2, f2, canIdeal, u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain))#0;
        );

        newDenom := reflexify(canIdeal*dualCanIdeal);
        computedTau = (runningIdeal*R1) : newDenom;
    );
    --now we have to run the sigma computation
    if (not (h1 == (sub(0, R1)))) then (
        baseTau:= testModule(0/1, sub(1, R1), ideal(sub(1, R1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain);
        decomposedExponent := decomposeFraction(pp, t, NoZeroC => true);
        a1 := decomposedExponent#0;
        b1 := decomposedExponent#1;
        c1 := decomposedExponent#2;
        if (a1 > (pp^c1-1)) then(
            a1quot := floor( (a1-1)/(pp^c1 - 1));
            a1rem := a1 - (pp^c1-1)*a1quot;
            computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, baseTau#0, {h1});
            computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, f}, computedHSLGInitial#0);
        )
        else (
            computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, baseTau#0, {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
            computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, computedHSLGInitial#0);
        );
    )
    else(--there should be an algorithm that works here
        error "isFJumpingExponent:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";
    );
    return (not isSubset(computedHSLG, computedTau));
)

isFJumpingExponentPoly = method( Options => {FrobeniusRootStrategy => Substitution} )

isFJumpingExponentPoly ( Number, RingElement ) := o -> ( t, f ) ->
(
    S1 := ring f;
    pp := char S1;
    cartIndex := 1;
    fList := {f};
    tList := {t};
    computedTau := null;
    computedHSLG := null;
    computedHSLGInitial := null;
    --computedTau := ideal(sub(0, R1));

    h1 := sub(1, S1);
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = (testModule(tList, fList, ideal(sub(1, S1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>true))#0;

    --now we have to run the sigma computation
    decomposedExponent := decomposeFraction(pp, t, NoZeroC => true);
    a1 := decomposedExponent#0;
    b1 := decomposedExponent#1;
    c1 := decomposedExponent#2;
    if (a1 > (pp^c1-1)) then(
        a1quot := floor( (a1-1)/(pp^c1 - 1));
        a1rem := a1 - (pp^c1-1)*a1quot;
        computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, ideal(sub(1, S1)), {h1});
        computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, f}, computedHSLGInitial#0);
    )
    else (
        computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, ideal(sub(1, S1)), {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, computedHSLGInitial#0);
    );

    return (not isSubset(computedHSLG, computedTau));
)
