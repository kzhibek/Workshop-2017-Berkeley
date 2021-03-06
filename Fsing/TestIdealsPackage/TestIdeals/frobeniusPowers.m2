--*************************************************
--*************************************************
--This file is used for taking various types of 
--powers of ideals in characteristic p>0. 
--*************************************************
--*************************************************



--Computes powers of elements in char p>0, using that Frobenius is an endomorphism. If 
--N = N_0 + N_1 p + ... + N_e p^e, where 0 <= N_i < p, then this computes f^N as
--f^(N_0) (f^(N_1))^p ... (f^(N_e))^(p^e). 

fastExponentiation = method( TypicalValue => RingElement )

fastExponentiation ( ZZ, RingElement ) := RingElement => ( N, f ) ->
(
    if N < 0 then error "fastExponentiation: first argument must a nonnegative integer.";
    p := char ring f;
    if p == 0 then return f^N; 
    E:=adicExpansion(p,N);
    product(#E, e -> sum( terms f^(E#e), g -> g^(p^e) ) )
)

--------------------------------------------------------------------------------------------------------

--Outputs the p^e-th Frobenius power of an ideal, or the p^e-th (entry-wise) Frobenius power of a matrix.

frobeniusMethod =  method( Options => { FrobeniusRootStrategy => Substitution } );

frobeniusMethod ( ZZ, Ideal ) := Ideal => o -> ( e, I ) ->
(
    R := ring I;
    p := char R;
    if p == 0 then 
        error "frobeniusMethod: expected an ideal in a ring of positive characteristic.";
    if e == 0 then return I;
    if e < 0 then return frobeniusRoot( -e, I, o );
    G := I_*;
    if #G == 0 then ideal( 0_R ) else ideal( apply( G, j -> fastExponentiation( p^e, j ) ) )
)

frobeniusMethod ( ZZ, Matrix ) := Matrix => o -> ( e, M ) ->
(
    p := char ring M;
    if p == 0 then 
        error "frobenius: expected an matrix with entries in a ring of positive characteristic.";
    if e == 0 then return M;
    if e < 0 then error "frobenius: first argument must be nonnegative.";
    matrix apply( entries M, u -> apply( u, j -> fastExponentiation( p^e, j ) ) )
)

frobeniusMethod ( Ideal ) := Ideal => o -> I -> frobeniusMethod( 1, I, o )

frobeniusMethod ( Matrix ) := Matrix => o -> M -> frobeniusMethod( 1, M )

FrobeniusOperator = new Type of MethodFunctionWithOptions

frobenius = new FrobeniusOperator from frobeniusMethod

FrobeniusOperator ^ ZZ := ( f, n ) -> ( x -> f( n, x ) )

--------------------------------------------------------------------------------------------------------

--This is an internal function. Given ideals I, J and a positive integer e, consider
--the following chain of ideals:
--K_1 = (I*J)^[1/p^e] and K_{s+1} = (I*K_s)^[1/p^e]
--This chain is ascending, and has the property that once two consecutive terms
--agree, the chain stabilizes.  This function outputs the stable ideal of this chain.

stableIdeal = { FrobeniusRootStrategy => Substitution } >> o -> ( e, I, J ) -> 
(
    K := ideal( 0_( ring I ) );
    L := frobeniusRoot( e, I*J, o );
    while not isSubset( L, K ) do
    (
    	K = L;              
    	L = frobeniusRoot( e, I*K, o );
    );
    trim K 
)

--------------------------------------------------------------------------------------------------------

--Outputs the generalized Frobenius power of an ideal; either the N-th Frobenius power of N/p^e-th one.

frobeniusPower = method( 
    Options => { FrobeniusPowerStrategy => Naive, FrobeniusRootStrategy => Substitution },
    TypicalValue => Ideal 
);

--Computes the integral generalized Frobenius power I^[N]
frobeniusPower ( ZZ, Ideal ) := Ideal => o -> ( N, I ) -> 
(
    R := ring I;
    p := char R;
    if p == 0 then 
        error "frobeniusPower: expected an ideal in a ring of positive characteristic.";
    G := first entries mingens I;
    if #G == 0 then return ideal( 0_R );
    if #G == 1 then return ideal( fastExponentiation( N, G#0 ) );
    E := adicExpansion( p, N );
    product( #E, m -> frobenius( m, I^( E#m ) ) )
)

--Computes the generalized Frobenius power I^[N/p^e]
frobeniusPowerHelper = { FrobeniusPowerStrategy => Naive, FrobeniusRootStrategy => Substitution } >> 
    o -> ( e, N, I ) ->
(   
    R := ring I;
    p := char R;
    G := first entries mingens I;
    if #G == 0 then return ideal( 0_R );
    rem := N % p^e;
    M := N // p^e;
    J := frobeniusPower( M, I );  --component when applying Skoda's theorem     
    if o.FrobeniusPowerStrategy == Safe then 
    (
	E := adicExpansion( p, rem );
	J * product( #E, m -> frobeniusRoot( e-m, I^( E#m ), FrobeniusRootStrategy => o.FrobeniusRootStrategy ) );  
        --step-by-step computation of generalized Frobenius power of I^[rem/p^e]
        --using the base p expansion of rem/p^e < 1
    )
    else J * frobeniusRoot( e, frobeniusPower( rem, I ), FrobeniusRootStrategy => o.FrobeniusRootStrategy )  --Skoda to compute I^[N/p^e] from I^[rem/p^e] 
)

--Computes the generalized Frobenius power I^[t] for a rational number t 
frobeniusPower( QQ, Ideal ) := Ideal => o -> ( t, I ) ->
(
    if t < 0 then error "frobeniusPower: expected a nonnegative exponent.";
    p := char ring I;
    if p == 0 then 
        error "frobeniusPower: expected an ideal in a ring of positive characteristic.";
    ( a, b, c ) := toSequence decomposeFraction( p, t ); --write t = a/(p^b*(p^c-1))
    if c == 0 then frobeniusPowerHelper( b, a, I, o )  --if c = 0, call simpler function
        else 
	(
	    rem := a % ( p^c - 1 );      
	    quot := a // ( p^c - 1 );     
	    J := stableIdeal( c, frobeniusPower( rem, I ), I, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
	    frobeniusRoot( b, frobeniusPower( quot, I ) * J, FrobeniusRootStrategy => o.FrobeniusRootStrategy )
        )
)
