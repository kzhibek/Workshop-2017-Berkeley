doc ///
     Key
          UseSpecialAlgorithms
     Headline
          An option for the function fpt to check whether the input is a diagonal, binomial, or binary form.
     Description
          Text
               Default value for fpt is {\tt true}.  If {\tt true}, the function fpt first checks whether the input is a
               diagonal, binomial, or binary form (i.e., a homogeneous polynomial in 2 variables).  If it is, the function fpt applies
               specialized algorithms.  Can take on only Boolean values.
     SeeAlso
          fpt
///

doc ///
     Key
          ComputePreviousNus
     Headline
          An option for the function nu to compute nus recursively.
     Description
          Text
               If {\tt true}, then nu values are computed recursively, in succession; otherwise, another method can be applied.
	       Can take on only Boolean values. Default value for nu and nuList is {\tt true}.
     SeeAlso
          nu
///

doc ///
     Key
          ContainmentTest
     Headline
          An option for functions nu and nuList to specify containment test used.
     Description
          Text
               Specifies which test you use to check containment of powers of ideals. Valid values are {\tt FrobeniusPower},
	       {\tt FrobeniusRoot}, and {\tt StandardPower}.  Default for nu and nuList applied to a polynomial is {\tt FrobeniusRoot},
	       and applied to an ideal is {\tt StandardPower}.
///

doc ///
     Key
         criticalExponentApproximation
         (criticalExponentApproximation,ZZ,Ideal,Ideal)
         (criticalExponentApproximation,ZZ,RingElement,Ideal)
     Headline
        gives a list of \mu_I^J(p^d)/p^d or \mu_f^J(p^d)/p^d for d = 0,...,e.
     Usage
          criticalExponentApproximation(e,I,J)
          criticalExponentApproximation(e,f,J)
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text
             This returns a list of $\mu_I^J(p^d)/p^d$ or $\mu_f^J(p^d)/p^d$ for $d = 0,...,e$.  As $d$ approaches $\infty$,
	     the sequence of these terms converges to the critical exponent of $I$ or $f$ with respect to $J$.
	 Example
             R = ZZ/5[x,y];
             I = ideal(x^2,x*y,y^2);
             f = x^2 + y^3;
             m = ideal(x,y);
             criticalExponentApproximation(2,I,m)
             criticalExponentApproximation(2,f,m)
///

doc ///
     Key
         fpt
	 (fpt, RingElement)
	 [fpt, FRegularityCheck]
	 [fpt, NuCheck]
	 [fpt, UseSpecialAlgorithms]
--	 [fpt, DepthOfSearch]
     Headline
         attempts to compute the F-pure threshold of a polynomial at the origin
     Usage
          fpt(f)
     Inputs
        f:RingElement
	    a polynomial with coefficients in a finite field
        UseSpecialAlgorithms => Boolean
            specifies whether to check if $f$ is diagonal, binomial, or a binary form, and then apply appropriate algorithms
        FRegularityCheck => Boolean
            specifies whether to check if the lower bound derived from the $F$-signature function is the $F$-pure threshold of $f$
    	NuCheck => Boolean
            specifies whether to check if $\nu/(p^e-1)$ or $(\nu+1)/p^e$ is the $F$-pure threshold of $f$, where $e$ is the value of the option {\tt DepthOfSearch} and $\nu=\nu_f(p^e)$
        DepthOfSearch => ZZ
            specifies the power of the characteristic to be used in the search for the $F$-pure threshold
     Outputs
        :List
	    which contains the endpoints of an interval containing the $F$-pure threshold of $f$
        Q:QQ
	    the $F$-pure threshold of $f$
     Description
          Text
              This function tries to find the exact value for the $F$-pure threshold of $f$ at the origin, and returns that value, if possible.
	      Otherwise, it returns an interval containing the $F$-pure threshold.

	      If the option {\tt UseSpecialAlgorithms} is set to {\tt true} (the default value), then the function first checks whether $f$ is a diagonal polynomial, a binomial, or a form in two variables, respectively.
	      If it is one of these, algorithms of D. Hernandez, or D. Hernandez and P. Teixeira, are executed to compute the $F$-pure threshold of $f$.

	      When no special algorithm is available or {\tt UseSpecialAlgorithms} is set to {\tt false}, {\tt fpt} computes $\nu = \nu_f(p^e)$, where $e$ is the value of the option {\tt DepthOfSeach}.
	      If {\tt NuCheck} is set to {\tt true} (its default value), then checks are run to verify whether either $\nu/(p^e-1)$ or $(\nu+1)/p^e$ equals the $F$-pure threshold.

	      If the $F$-threshold has not been found, then it lies in the interval $(\nu/(p^e-1),(\nu+1)/p^e)$ or $[\nu/(p^e-1),(\nu+1)/p^e]$, depending on whether {\tt NuCheck} was performed.
	      The function then uses the convexity of the $F$-signature function and a secant line argument to narrow down this interval containing the $F$-pure threshold.

	      When {\tt FRegularityCheck} is set to {\tt true} (its default value), a check (which can take significant time) is run to verify whether the left-hand endpoint of the interval containing the $F$-pure threshold is the exact answer.

	      If no exact answer was found, then a list containing the endpoints of an interval containing the $F$-pure threshold of $f$ is returned.
	      Whether that interval is open, closed, or a mixed interval depends on the options passed; if the option {\tt Verbose} is set to {\tt true}, the precise interval will be printed.
///

doc ///
     Key
         fptApproximation
         (fptApproximation,ZZ,Ideal)
         (fptApproximation,ZZ,RingElement)
     Headline
         Gives a list of nu_I(p^d)/p^d for d=0,...,e.
     Usage
          fptApproximation(e,I)
          fptApproximation(e,f)
     Inputs
         e:ZZ
         I:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text
             This returns a list consisting of nu_I(p^d)/p^d for d = 0,...,e.  The sequence {nu_I(p^d)/p^d} converges to the F-pure threshold.
///


doc ///
     Key
          FRegularityCheck
     Headline
          An option for the function fpt
     Description
          Text
               Enables the user to check whether the given pair is F-regular at the given maximal ideal
	            (so that if not, the F-pure threshold can be determined from the F-signature function).
		    Only takes on Boolean values.
     SeeAlso
          fpt
///


doc ///
     Key
         ftApproximation
         (ftApproximation,ZZ,Ideal,Ideal)
         (ftApproximation,ZZ,RingElement,Ideal)
     Headline
         Gives a list of nu_I^J(p^d)/p^d for d=0,...,e.
     Usage
         ftApproximation(e,I,J)
         ftApproximation(e,f,J)
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text
             This returns a list of nu_I^J(p^d)/p^d for d = 0,...,e.  As d approaches infinity, the sequence {nu_I^J(p^d)/p^d} converges
	     to the F-threshold of I or f with respect to J.
///

doc ///
     Key
        fptGuessList
     Headline
        Tries to guess the FPT in a really naive way (this should be improved).
     Usage
         fptGuessList(f,e,d)
     Inputs
         f:RingElement
         e:ZZ
         d:ZZ
     Outputs
        :List
     Description
        Text
             This tries to guess the FPT.  In particular, it computes the number nu such that nu/(p^e - 1) <= FPT < (nu+1)/p^e.  It then outputs a list of all rational numbers with denominators less than or equal to d, which lie in that range.  WARNING:  There are several improvements which should be made to this function to rule out many of the possibilies.
///

doc ///
     Key
        isFJumpingExponent
        (isFJumpingExponent,QQ,RingElement)
     Headline
        Checks whether a given number is an F-jumping number
     Usage
         isFJumpingExponent(t,f,Verbose=>V)
     Inputs
         t:QQ
         f:RingElement
         V:Boolean
     Outputs
        :Boolean
     Description
        Text
            Returns true if t is an F-jumping number, otherwise it returns false.
///

doc ///
     Key
        isFPT
        (isFPT,QQ,RingElement)
     Headline
        Checks whether a given number is the FPT
     Usage
          isFPT(t,f,Verbose=>V,Origin=>W)
     Inputs
        t:QQ
        f:RingElement
        V:Boolean
        W:Boolean
     Outputs
        :Boolean
     Description
        Text
             Returns true if t is the FPT, otherwise it returns false.  If Origin is true, it only checks it at the homogeneous maximal ideal.
///


doc ///
     Key
         nu
         (nu,ZZ,Ideal,Ideal)
         (nu,ZZ,Ideal)
         (nu,ZZ,RingElement,Ideal)
         (nu,ZZ,RingElement)
--         [nu, ComputePreviousNus]
--         [nu, ContainmentTest]
--         [nu, Search]
--         [nu, UseColonIdeals]
     Headline
        Gives $\nu_I^J(p^e)$ or $\nu_f^J(p^e)$
     Usage
          nu(e,I,J)
          nu(e,I)
          nu(e,f,J)
          nu(e,f)
          ComputePreviousNus => Boolean
          ContainmentTest => Symbol
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :ZZ
     Description
        Text
            Given an ideal I in a polynomial ring k[x_1, ..., x_n], nu(e, I, J) outputs the maximal integer \nu{}   such that I^\nu is not contained in the ideal J^{[p^e]}. This number is denoted \nu_I^J(p^e) in "F-thresholds and Bernstein-Sato Polynomials" by Mustata-Takagi-Watanabe. If the input is (ZZ,Ideal) then the function computes the maximal integer \nu{} such that I^\nu in not contained in (x_1, ...,x_n)^{[p^e]}. If a RingElement f is passed instead of an ideal I, this function computes nu of the principal ideal generated by f. This is used frequently to compute the F-pure threshold.

            If the option {\tt ComputePreviousNus} is set to {\tt true}, nu will recursively compute nu(d, I) for d = 0,..., e.

            The option {\tt ContainmentTest} specifies the algorithm used to test the containment of I^n in J^{[p^e]}. Valid values for {\tt ContainmentTest} are {\tt FrobeniusPower, FrobeniusRoot}, and {\tt StandardPower}. By default, {\tt ContainmentTest} is set to {\tt FrobeniusPower} is nu is passed a RingElement f, and {\tt ContainmentTest} is set to {\tt StandardPower} if nu is passed an Ideal I.

            The function nu works by searching a list of integers for the above number \nu. The option {\tt Search} specifies the search algorithm used to do so. Valid values for {\tt Search} are {\tt Binary, BinaryRecursive}, and {\tt Linear}.

            The option {\tt UseColonIdeals} specifies whether or not nu uses colon ideals to compute \nu in an iterative way.

     SeeAlso
        nuList
///

doc ///
     Key
          NuCheck
     Headline
          An option for the function fpt to specify whether the user would like to check whether nu/(p^e-1) or (nu+1)/p^e is the F-pure threshold.
     Description
          Text
               Takes on only Boolean values.  Default value for fpt is {\tt true}.
     SeeAlso
          fpt
///

doc ///
     Key
         nuList
         (nuList,ZZ,Ideal,Ideal)
         (nuList,ZZ,Ideal)
         (nuList,ZZ,RingElement,Ideal)
         (nuList,ZZ,RingElement)
--         [nuList, ContainmentTest]
--         [nuList, Search]
--         [nuList, UseColonIdeals]
     Headline
          Lists $\nu_I^J(p^d)$ or $\nu_f^J(p^d)$ for d = 1,...,e
     Usage
          nuList(e,I,J)
          nuList(e,I)
          nuList(e,f,J)
          nuList(e,f)
          ContainmentTest => Symbol
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :List
     Description
        Text
            Given an ideal I in a polynomial ring k[x_1,...,x_n], this function computes nu(d, I, J) recursively for d = 0,...,e; see @TO nu@, and similarly if nuList is passed (ZZ, Ideal), (ZZ, RingElement, Ideal), or (ZZ, RingElement).
     SeeAlso
        nu
///

doc ///
     Key
          Search
     Headline
          An option for the functions nu and nuList
     Description
          Text
               Lets user specify the order in which ideal containment of powers are computed. Valid values are
	            {\tt Binary, BinaryRecursive}, and {\tt Linear}.
     SeeAlso
          nu
          nuList
///

doc ///
     Key
          UseColonIdeals
     Headline
          An option for nu and nuList
     Description
          Text
               Valid values are {\tt true} and {\tt false}.
     SeeAlso
          nu
          nuList
///
