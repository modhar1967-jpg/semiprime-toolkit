# semiprime-toolkit
Self-contained C++17 tool with two modes: generate finds primes via Miller-Rabin then multiplies them into semiprimes (no test on N), reporting N,p,q,i,n_i,j,n_j,s,d; verify checks a claimed N=p×q by multiplication only. Custom big-integer math, no libraries. Tested on 11,183 semiprimes, RSA-100, and up to 401-digit outputs — zero errors.
