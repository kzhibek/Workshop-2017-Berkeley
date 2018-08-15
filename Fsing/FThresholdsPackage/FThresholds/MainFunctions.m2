--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
nu1 = method()

nu1 ( Ideal, Ideal ) :=  ( I, J ) -> 
(
    if not isSubset( I, radical J ) then 
        error "nu1: The first ideal is not contained in the radical of the second";
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

-- for polynomials, we use fastExponentiation
nu1 ( RingElement, Ideal ) := ( f, J ) -> 
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
testPower = method()

testPower ( Ideal, ZZ, Ideal, ZZ ) := ( J, a, I, e ) -> 
    isSubset( J^a, frobenius( e, I ) )

-- for polynomials, use fastExponentiation
testPower ( RingElement, ZZ, Ideal, ZZ ) := ( f, a, I, e ) -> 
    isSubset( ideal fastExponentiation( a, f ), frobenius( e, I ) )

-- testFrobeniusPower(J,a,I,e) checks whether J^[a] is a subset of I^[p^e]
testFrobeniusPower = method()

testFrobeniusPower ( Ideal, ZZ, Ideal, ZZ ) := ( J, a, I, e ) -> 
    isSubset( frobeniusPower( a, J ), frobenius( e, I ) )

testFrobeniusPower ( RingElement, ZZ, Ideal, ZZ ) := ( f, a, I, e ) -> 
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
    -- Verify if option values are valid
    checkOptions( o,
	{
	    ContainmentTest => { StandardPower, FrobeniusRoot, FrobeniusPower, null },
	    Search => { Binary, Linear, BinaryRecursive },
	    UseColonIdeals => Boolean,
	    ComputePreviousNus => Boolean
	}
    );

    -- Return error if f is 0
    if f == 0 then 
        error "nuInternal: zero is not a valid input";

    -- Check if f is in a polynomial ring over a finite field
    if not isPolynomialRingOverFiniteField ring f then 
        error "nuInternal: expected polynomial or ideal in a polynomial ring over a finite field";

    -- decide which containment test to use, if not specified by user
    comTest := o.ContainmentTest;
    if comTest === null then 
	comTest = if instance(f, RingElement) then FrobeniusRoot 
	    else StandardPower;
    
    p := char ring f;
    nu := nu1( f, J ); -- if f is not in rad(J), nu1 will return an error
    theList := { nu };
    isPrincipal := if isIdeal f then (numgens trim f) == 1 else true;
    searchFct := search#(o.Search);
    testFct := test#(comTest);
    local N;

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

nuList = method( Options => optNuList )

nuList ( ZZ, Ideal, Ideal ) := o -> ( e, I, J ) -> 
    nuInternal( e, I, J, o )

-- Dan: I changed Options => true to Options => optNuList above in order to make 
-- things compile, and I'm worried that's messing up our default options here. 

nuList ( ZZ, RingElement, Ideal ) := o -> ( e, I, J ) -> 
    nuInternal( e, I, J, o )

nuList ( ZZ, Ideal ) :=  o -> ( e, I ) -> 
    nuList( e, I, maxIdeal I, o )


nuList ( ZZ, RingElement ) := o -> ( e, f ) -> 
    nuList( e, f, maxIdeal f, o )
   

nu = method( Options => optNu )

nu ( ZZ, Ideal, Ideal ) := o -> ( e, I, J ) -> 
    last nuInternal( e, I, J, o )

nu ( ZZ, RingElement, Ideal ) := o -> ( e, f, J ) -> 
    last nuInternal( e, f, J, o )

nu ( ZZ, Ideal ) := o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu ( ZZ, RingElement ) := o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

-- Nus can be computed using generalized Frobenius powers, by using 
-- ContainmentTest => FrobeniusPower. For convenience, here are some shortcuts: 

muList = optNuList >> o -> x -> 
    nuList( x, o, ContainmentTest => FrobeniusPower ) 

mu = optNu >> o -> x -> nu( x, o, ContainmentTest => FrobeniusPower ) 

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for approximating, guessing, estimating F-Thresholds and crit exps
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Approximates the F-pure Threshold
--Gives a list of nu_I(p^d)/p^d for d=1,...,e
fptApproximation = method()

fptApproximation ( ZZ, Ideal ) := ( e, I ) ->
(
     p := char ring I;
     nus := nuList( e, I );
     apply( nus, 0..e, (n,k) -> n/p^k )
)

fptApproximation ( ZZ, RingElement ) := ( e, f ) -> 
    fptApproximation( e, ideal f )

--Approximates the F-Threshold with respect to an ideal J
--More specifically, this gives a list of nu_I^J(p^d)/p^d for d=1,...,e

ftApproximation = method()

ftApproximation ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then 
        error "ftApproximation: F-threshold undefined";
    p := char ring I;
    nus := nuList( e, I, J );
    apply( nus, 0..e, (n,k) -> n/p^k )
)

ftApproximation ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> 
   fptApproximation( e, ideal(f), J )

criticalExponentApproximation = method()

criticalExponentApproximation ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then 
        error "criticalExponentApproximation: critical exponent undefined";
    p := char ring I;
    mus := muList( e, I, J );
    apply( mus, 0..e, (n,k) -> n/p^k )
)

criticalExponentApproximation ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> 
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

--Determines if a pair (R, f^t) is F-regular at a prime
--ideal Q in R, where R is a polynomial ring  
isFRegularPoly = ( f, t, Q ) -> not isSubset( testIdeal( t, f ), Q )

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
)

fpt RingElement := QQ => o -> f -> 
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
	    DepthOfSearch => ZZ  	
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
            return binaryFormFPT f 
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
	if not isFRegularPoly( f, n/(p^e-1), M ) then 
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
        if not isFRegularPoly( f, a, M ) then 
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

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for checking if given numbers are F-jumping numbers
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--isFPT, determines if a given rational number is the FPT of a pair in a 
-- polynomial ring. 

isFPT = method( Options => { Verbose=> false } )

isFPT ( QQ, RingElement ) := o -> ( t, f ) -> 
(
    if not isPolynomialOverFiniteField f  then 
        error "isFPT: expected a polynomial with coefficients in a finite field";
    R := ring f;
    p := char R;
    --this writes t = a/(p^b(p^c-1))
    (a,b,c) := toSequence decomposeFraction( p, t );

    -- sigma
    a1 := if c == 0 then a-1 else floor( (a-1)/(p^c-1) );
    Sigma := if c == 0 then sigma(f,p-1,1) else sigma(f,(a-1)%(p^c-1)+1,c);	
    if o.Verbose then print "\nSigma Computed";
	
    if not isSubset( ideal 1_R, frobeniusRoot(b,a1,f,Sigma) ) then
        return false; 

    if o.Verbose then print "\nWe know t <= FPT";
    
    -- Higher tau
    a2 := if c == 0 then a else floor( a /(p^c-1) );
    Tau := if c == 0 then ideal 1_R else testIdeal( fracPart(a/(p^c-1)), f );
    if o.Verbose then print "\nHigher tau Computed";
    
    not isSubset( ideal 1_R, frobeniusRoot(b,a2,f,Tau) )
)

isFPT ( ZZ, RingElement ) := o -> ( t, f ) -> isFPT( t/1, f, o )

-- isFJumpingExponent determines if a given rational number is an 
-- F-jumping exponent
--***************************************************************************
--This needs to be speeded up, like the above function
--***************************************************************************

isFJumpingExponent = method( Options => {Verbose=> false} )

isFJumpingExponent ( QQ, RingElement ) := o -> ( t, f ) -> 
(
    if not isPolynomialOverFiniteField f  then 
        error "isFJumpingExponent: expected a polynomial with coefficients in a finite field";
    p := char ring f;
    --this writes t = a/(p^b(p^c-1))
    (a,b,c) := toSequence decomposeFraction( p, t );
    Tau := frobeniusRoot( b, testIdeal( t*p^b, f ) );
    if o.Verbose then print "\nHigher tau Computed";

    local Sigma;
    if c == 0 then
        Sigma = frobeniusRoot( b, ideal( f^(a-1) ) * sigma( f, p-1, 1 ) )
    else Sigma = frobeniusRoot( b, sigma( f, a, c ) );
    if o.Verbose then print "\nSigma Computed";

    -- if sigma is not contained in tau, this is an F-jumping number
    not isSubset( Sigma, Tau )
)

isFJumpingExponent ( ZZ, RingElement ) := o -> ( t, f ) -> 
    isFJumpingExponent( t/1, f, o )

----------------------------------------------------------------
--************************************************************--
--Functions for computing sigma                               --
--************************************************************--
----------------------------------------------------------------

--Computes Non-Sharply-F-Pure ideals over polynomial rings for 
-- (R, f^{a/(p^{e}-1)}), at least defined as in Fujino-Schwede-Takagi.
-- If e = 0, we treat p^e-1 as 1.
sigma = ( f, a, e ) -> 
(
    R := ring f;
    p := char R;
    m := 0;
    s := if e == 0 then 1 else e;
    b := if e == 0 then a*(p-1) else a;
    if b > p^s-1 then 
    (
	m = floor( (b-1)/(p^s-1) ); 
	b = (b-1)%(p^s-1) + 1
    );
    newIdeal := ideal 1_R;
    oldIdeal := ideal 0_R; 
     
    -- This stops after finitely many steps.  
    while newIdeal != oldIdeal do
    (
        oldIdeal = newIdeal;
        newIdeal = frobeniusRoot( s, b, f, oldIdeal ) 
    );
    newIdeal * ideal( f^m )
)
