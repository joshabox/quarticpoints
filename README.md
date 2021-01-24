This is the Magma and Sage code accompanying the article "Elliptic curves over quartic fields not containing root 5 are modular".

To verify the claims made in the paper, the following files should be run:

- X0105.m (this file does all checks for the chapter on X_0(105))
- X_0(105)modw35 bitangents (this file funs the bitangent check).
- Xs3b5b7.m (this file does all checks for the chapter on X(s3,b5,b5))
- Xb5ns7pts.m (this file runs the sieve and Chabauty for quartic points on Xb5ns7)
- X1.m (this file runs the sieves and Chabauty for X_1)
- X2.m (this file runs the sieves and Chabauty for X_2)
- KolyvaginLogachevCheck.sage (this file computes L(f,1) for the cusp forms defined in the final section)


The following files contain functions or data that are used in the files above:

- ozmansiksek2.m (functions written by Ozman and Siksek)
- usefulfunctions.m (a variety of different "useful" functions)
- QuarticsieveXb5ns7.m (the sieve for quartic points on Xb5ns7)
- X1andX2sieve.m (the sieve for X1 and X2, including computations of maps and models)
- cuspforms.m (q-expansions of cusp forms defining canonical models for X_1, X_2, X(b5,ns7) and X(b3,ns7)).