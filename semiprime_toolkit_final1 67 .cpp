// ============================================================================
//Modhar Mohammed Torki1 Fawaz Modhar Mohammed21Department of Electrical, Electronic and Communications Engineering, Basra University —modhar1967@gmail.com2Department of Computer Engineering, Basra University — fawazmodhar@gmail.com


// Unified Semiprime Toolkit -- companion code to:
// "A Test-Free Algorithm for Generating Semiprime Numbers in Any Interval:
//  Closed-Form Factor-Distance Coordinates from Directional Multiplication"
//
// Combines, in one self-contained file (no external numerical library):
//   MODE 1: generate  -- finds every prime A_k(n) for n in [n_start,n_end]
//            (the one test performed, applied only to these candidates),
//            then forms every pairwise product directly. Each product is a
//            semiprime BY CONSTRUCTION; no test is ever applied to it.
//            Reports N, p, q, i, n_i, j, n_j, s, d for every result.
//   MODE 2: verify    -- given a claimed N and its generative coordinates
//            (i, n_i, j, n_j), recomputes p=A_i(n_i), q=A_j(n_j), forms
//            p*q via the same arbitrary-precision multiplication, and
//            checks it against the claimed N digit-for-digit. No
//            Miller-Rabin call and no division are used in this mode.
//
// Both modes share the same underlying BigUInt/BigInt arithmetic and the
// same generator A_k(n) = X + rho_k + C*n, so n_i, n_j, N may be of
// arbitrary size in either mode.
// ============================================================================

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cstdint>
#include <random>
#include <chrono>
using namespace std;
using namespace chrono;

// ============================================================================
// SECTION 1: Self-contained arbitrary-precision arithmetic (base 10^9)
// ============================================================================
struct BigUInt {
    static constexpr uint64_t BASE = 1000000000ULL;
    vector<uint32_t> limbs; // little-endian

    BigUInt() { limbs.push_back(0); }
    BigUInt(uint64_t v) { if (v==0) limbs.push_back(0); while (v>0){ limbs.push_back((uint32_t)(v%BASE)); v/=BASE; } if(limbs.empty()) limbs.push_back(0); }

    static BigUInt fromString(const string& s) {
        BigUInt r; r.limbs.clear();
        int len = (int)s.size();
        for (int i = len; i > 0; i -= 9) {
            int start = max(0, i-9);
            r.limbs.push_back((uint32_t)stoul(s.substr(start, i-start)));
        }
        if (r.limbs.empty()) r.limbs.push_back(0);
        r.trim();
        return r;
    }
    void trim() { while (limbs.size() > 1 && limbs.back()==0) limbs.pop_back(); }
    bool isZero() const { return limbs.size()==1 && limbs[0]==0; }
    bool isOdd() const { return limbs[0] & 1; }

    static int cmp(const BigUInt&a, const BigUInt&b) {
        if (a.limbs.size()!=b.limbs.size()) return a.limbs.size()<b.limbs.size()?-1:1;
        for (int i=(int)a.limbs.size()-1;i>=0;i--) if (a.limbs[i]!=b.limbs[i]) return a.limbs[i]<b.limbs[i]?-1:1;
        return 0;
    }
    friend bool operator==(const BigUInt&a,const BigUInt&b){return cmp(a,b)==0;}

    static BigUInt add(const BigUInt&a,const BigUInt&b){
        BigUInt r; r.limbs.clear(); uint64_t carry=0;
        size_t n=max(a.limbs.size(),b.limbs.size());
        for(size_t i=0;i<n||carry;i++){
            uint64_t sum=carry;
            if(i<a.limbs.size()) sum+=a.limbs[i];
            if(i<b.limbs.size()) sum+=b.limbs[i];
            r.limbs.push_back((uint32_t)(sum%BASE)); carry=sum/BASE;
        }
        if(r.limbs.empty()) r.limbs.push_back(0);
        r.trim(); return r;
    }
    static BigUInt sub(const BigUInt&a,const BigUInt&b){ // a>=b required
        BigUInt r; r.limbs.clear(); int64_t borrow=0;
        for(size_t i=0;i<a.limbs.size();i++){
            int64_t diff=(int64_t)a.limbs[i]-borrow-(i<b.limbs.size()?(int64_t)b.limbs[i]:0);
            if(diff<0){diff+=BASE;borrow=1;} else borrow=0;
            r.limbs.push_back((uint32_t)diff);
        }
        r.trim(); return r;
    }
    static BigUInt mul(const BigUInt&a,const BigUInt&b){
        vector<uint64_t> tmp(a.limbs.size()+b.limbs.size(),0);
        for(size_t i=0;i<a.limbs.size();i++){
            uint64_t carry=0;
            for(size_t j=0;j<b.limbs.size()||carry;j++){
                uint64_t cur=tmp[i+j]+carry;
                if(j<b.limbs.size()) cur+=(uint64_t)a.limbs[i]*b.limbs[j];
                tmp[i+j]=cur%BASE; carry=cur/BASE;
            }
        }
        BigUInt r; r.limbs.assign(tmp.begin(),tmp.end()); r.trim(); return r;
    }
    static BigUInt mulSmall(const BigUInt&a,uint64_t m){
        BigUInt r; r.limbs.clear(); uint64_t carry=0;
        for(size_t i=0;i<a.limbs.size()||carry;i++){
            uint64_t cur=carry+(i<a.limbs.size()?(uint64_t)a.limbs[i]*m:0);
            r.limbs.push_back((uint32_t)(cur%BASE)); carry=cur/BASE;
        }
        r.trim(); return r;
    }
    // Schoolbook long division: returns quotient, sets rem.
    static BigUInt divmod(const BigUInt&a, const BigUInt&b, BigUInt& rem) {
        BigUInt quotient; quotient.limbs.assign(a.limbs.size(), 0);
        BigUInt cur; cur.limbs = {0};
        for (int i = (int)a.limbs.size()-1; i >= 0; i--) {
            cur.limbs.insert(cur.limbs.begin(), a.limbs[i]);
            cur.trim();
            uint64_t lo=0, hi=BASE-1, x=0;
            while (lo <= hi) {
                uint64_t mid = lo + (hi-lo)/2;
                BigUInt t = mulSmall(b, mid);
                if (cmp(t, cur) <= 0) { x = mid; lo = mid+1; } else { if(mid==0) break; hi = mid-1; }
            }
            quotient.limbs[i] = (uint32_t)x;
            cur = sub(cur, mulSmall(b, x));
        }
        quotient.trim();
        rem = cur;
        return quotient;
    }
    static BigUInt mod(const BigUInt&a, const BigUInt&b) { BigUInt r; divmod(a,b,r); return r; }
    static BigUInt mulmod(const BigUInt&a,const BigUInt&b,const BigUInt&m){ return mod(mul(a,b), m); }
    static BigUInt powmod(BigUInt base, BigUInt exp, const BigUInt& mod_) {
        BigUInt result(1ULL);
        base = mod(base, mod_);
        BigUInt zero(0ULL);
        while (!(exp == zero)) {
            if (exp.isOdd()) result = mulmod(result, base, mod_);
            base = mulmod(base, base, mod_);
            BigUInt rem; exp = divmod(exp, BigUInt(2ULL), rem);
        }
        return result;
    }
    string toString() const {
        string s = to_string(limbs.back());
        for (int i=(int)limbs.size()-2;i>=0;i--){ string p=to_string(limbs[i]); s += string(9-p.size(),'0')+p; }
        return s;
    }
};
ostream& operator<<(ostream& os, const BigUInt& v){ return os << v.toString(); }

// Signed wrapper, since d = (rho_j-rho_i)/2 + C(n_j-n_i)/2 can be negative.
struct BigInt {
    bool neg=false; BigUInt mag;
    BigInt(): mag(0ULL) {}
    static BigInt fromUInt(BigUInt m, bool n=false){ BigInt r; r.mag=m; r.neg=n && !m.isZero(); return r; }
    static BigInt fromLL(long long v){ BigInt r; r.neg=v<0; r.mag=BigUInt((uint64_t)(v<0?-v:v)); return r; }
    static BigInt add(const BigInt&a,const BigInt&b){
        BigInt r;
        if(a.neg==b.neg){ r.mag=BigUInt::add(a.mag,b.mag); r.neg=a.neg; }
        else if(BigUInt::cmp(a.mag,b.mag)>=0){ r.mag=BigUInt::sub(a.mag,b.mag); r.neg=a.neg; }
        else { r.mag=BigUInt::sub(b.mag,a.mag); r.neg=b.neg; }
        if(r.mag.isZero()) r.neg=false;
        return r;
    }
    static BigInt mulSmall(const BigInt&a,int64_t m){
        BigInt r; r.mag=BigUInt::mulSmall(a.mag,(uint64_t)(m<0?-m:m)); r.neg=a.neg!=(m<0);
        if(r.mag.isZero()) r.neg=false; return r;
    }
    static BigInt divSmallExact(const BigInt&a,int64_t d){
        BigUInt rem; BigUInt q = BigUInt::divmod(a.mag, BigUInt((uint64_t)(d<0?-d:d)), rem);
        BigInt r; r.mag=q; r.neg=a.neg!=(d<0);
        if(r.mag.isZero()) r.neg=false; return r;
    }
    string toString() const { return (neg?"-":"") + mag.toString(); }
};
ostream& operator<<(ostream& os, const BigInt& v){ return os << v.toString(); }

// ============================================================================
// SECTION 2: The generator A_k(n) = X + rho_k + C*n  (Eq. 1 of the paper)
// ============================================================================
constexpr long long X = 7, C = 30;
constexpr long long A_RESIDUE[8] = {0,4,6,10,12,16,22,24};

BigUInt A_big(int k, const BigUInt& n) {
    return BigUInt::add(BigUInt((uint64_t)(X+A_RESIDUE[k])), BigUInt::mulSmall(n, C));
}
// Compute s, d (Eq. 4) from generative coordinates, returned as 2s, 2d
// (always exact integers here since 2X+rho_i+rho_j is always even).
pair<BigInt,BigInt> compute_2s_2d(int i, const BigUInt& ni, int j, const BigUInt& nj) {
    BigInt two_s = BigInt::add(
        BigInt::add(BigInt::fromLL(2*X+A_RESIDUE[i]+A_RESIDUE[j]),
                    BigInt::mulSmall(BigInt::fromUInt(ni), C)),
        BigInt::mulSmall(BigInt::fromUInt(nj), C));
    BigInt two_d = BigInt::add(
        BigInt::fromLL(A_RESIDUE[j]-A_RESIDUE[i]),
        BigInt::add(BigInt::mulSmall(BigInt::fromUInt(nj), C),
                    BigInt::mulSmall(BigInt::fromUInt(ni), -C)));
    return {two_s, two_d};
}

// ============================================================================
// SECTION 3: Miller-Rabin on BigUInt (used ONLY in generate mode, to verify
// candidate FACTORS -- never applied to a generated product N).
// ============================================================================
mt19937_64 rng_engine(chrono::steady_clock::now().time_since_epoch().count());
BigUInt randomBigUIntBelow(const BigUInt& bound) {
    BigUInt r; r.limbs.assign(bound.limbs.size(), 0);
    for (auto& l : r.limbs) l = (uint32_t)(rng_engine() % BigUInt::BASE);
    r.trim();
    return BigUInt::mod(r, bound);
}
bool mr_witness_big(const BigUInt& n, const BigUInt& a, const BigUInt& d, int r) {
    BigUInt one(1ULL), nMinus1 = BigUInt::sub(n, one);
    BigUInt x = BigUInt::powmod(a, d, n);
    if (x == one || x == nMinus1) return true;
    for (int i = 0; i < r-1; i++) { x = BigUInt::mulmod(x, x, n); if (x == nMinus1) return true; }
    return false;
}
bool is_prime_big(const BigUInt& n, int rounds = 20) {
    BigUInt zero(0ULL), one(1ULL), two(2ULL);
    if (n == zero || n == one) return false;
    if (n == two) return true;
    if (!n.isOdd()) return false;
    BigUInt d = BigUInt::sub(n, one);
    int r = 0;
    while (!d.isOdd()) { BigUInt rem; d = BigUInt::divmod(d, two, rem); r++; }
    BigUInt nMinus4 = BigUInt::sub(n, BigUInt(4ULL));
    for (int i = 0; i < rounds; i++) {
        BigUInt a = BigUInt::add(randomBigUIntBelow(nMinus4), two);
        if (!mr_witness_big(n, a, d, r)) return false;
    }
    return true;
}

// ============================================================================
// SECTION 4: MODE 1 -- generate
// ============================================================================
void mode_generate(const string& n_start_str, const string& n_end_str, int mr_rounds, bool sorted_output, bool self_verify) {
    BigUInt n_start = BigUInt::fromString(n_start_str);
    BigUInt n_end   = BigUInt::fromString(n_end_str);

    struct PF { int k; BigUInt n; BigUInt value; };
    vector<PF> primes;

    BigUInt n = n_start, one(1ULL);
    auto t0 = high_resolution_clock::now();
    long long candidates = 0;
    while (BigUInt::cmp(n, n_end) <= 0) {
        for (int k = 0; k < 8; k++) {
            BigUInt v = A_big(k, n);
            candidates++;
            if (is_prime_big(v, mr_rounds)) primes.push_back({k, n, v});
        }
        n = BigUInt::add(n, one);
    }
    auto t1 = high_resolution_clock::now();
    double find_time = duration<double>(t1-t0).count();

    cerr << "[generate] candidates tested (factors only): " << candidates
         << "   primes found: " << primes.size()
         << "   time: " << find_time << " s\n";

    struct Result { BigUInt N, p, q; int i,j; BigUInt ni,nj; BigInt s,d; string line; };
    vector<Result> results;
    long long generated = 0;
    for (size_t a = 0; a < primes.size(); a++) {
        for (size_t b = a; b < primes.size(); b++) {
            auto& Ai = primes[a]; auto& Aj = primes[b];
            BigUInt N = BigUInt::mul(Ai.value, Aj.value); // the ONLY operation on N
            auto [two_s, two_d] = compute_2s_2d(Ai.k, Ai.n, Aj.k, Aj.n);
            BigInt s = BigInt::divSmallExact(two_s,2), d = BigInt::divSmallExact(two_d,2);
            string line = N.toString() + "," + Ai.value.toString() + "," + Aj.value.toString() + ","
                 + to_string(Ai.k) + "," + Ai.n.toString() + "," + to_string(Aj.k) + "," + Aj.n.toString() + ","
                 + s.toString() + "," + d.toString();
            results.push_back({N, Ai.value, Aj.value, Ai.k, Aj.k, Ai.n, Aj.n, s, d, line});
            generated++;
        }
    }

    if (sorted_output) {
        auto ts0 = high_resolution_clock::now();
        sort(results.begin(), results.end(), [](const Result&a, const Result&b){
            return BigUInt::cmp(a.N, b.N) < 0;
        });
        auto ts1 = high_resolution_clock::now();
        cerr << "[generate] sort time (by N, ascending): " << duration<double>(ts1-ts0).count() << " s\n";
    }

    cout << "N,p,q,i,n_i,j,n_j,s,d\n";
    for (auto& r : results) cout << r.line << "\n";

    // ---- Built-in self-verification (no external tool, no Python) ----
    // Independently recomputes p=A_i(n_i), q=A_j(n_j), N=p*q, and checks
    // s^2-d^2=N for every generated result, using the SAME arbitrary-
    // precision routines but a fresh, separate recomputation path -- this
    // is what previously required an external Python script; it is now
    // part of the tool itself.
    long long verify_errors = 0;
    double verify_time = 0;
    if (self_verify) {
        auto tv0 = high_resolution_clock::now();
        for (auto& r : results) {
            BigUInt p_check = A_big(r.i, r.ni);
            BigUInt q_check = A_big(r.j, r.nj);
            BigUInt N_check = BigUInt::mul(p_check, q_check);
            bool ok = (p_check.toString()==r.p.toString()) && (q_check.toString()==r.q.toString())
                      && (N_check.toString()==r.N.toString());
            // s^2 - d^2 == N (sign-aware for d)
            BigUInt s2 = BigUInt::mul(r.s.mag, r.s.mag);
            BigUInt d2 = BigUInt::mul(r.d.mag, r.d.mag);
            BigUInt sd_diff = (BigUInt::cmp(s2,d2)>=0) ? BigUInt::sub(s2,d2) : BigUInt::sub(d2,s2);
            ok = ok && (sd_diff.toString() == r.N.toString());
            if (!ok) { verify_errors++; cerr << "[verify] MISMATCH at N=" << r.N << "\n"; }
        }
        auto tv1 = high_resolution_clock::now();
        verify_time = duration<double>(tv1-tv0).count();
    }

    cerr << "[generate] generated " << generated << " semiprimes from " << primes.size()
         << " verified primes -- zero tests performed on any of them."
         << (sorted_output ? " Output sorted by N (ascending)." : " Output in search order.") << "\n";
    if (self_verify) {
        cerr << "[verify] self-check (p,q,N,s,d all independently recomputed): "
             << (generated - verify_errors) << "/" << generated << " passed, "
             << verify_errors << " errors, time " << verify_time << " s\n";
        cerr << "SUMMARY_ROW," << generated << "," << find_time << "," << verify_time << "," << verify_errors << "\n";
    }
}

// ============================================================================
// SECTION 5: MODE 2 -- verify (multiplication-only certificate check)
// ============================================================================
void mode_verify(const string& N_claimed, int i, const string& ni_str, int j, const string& nj_str) {
    BigUInt ni = BigUInt::fromString(ni_str);
    BigUInt nj = BigUInt::fromString(nj_str);
    BigUInt p = A_big(i, ni);
    BigUInt q = A_big(j, nj);
    BigUInt N_recomputed = BigUInt::mul(p, q); // the ONLY operation used

    bool match = (N_recomputed.toString() == N_claimed);
    auto [two_s, two_d] = compute_2s_2d(i, ni, j, nj);

    cout << "Claimed N            : " << N_claimed << "\n";
    cout << "p = A_" << i << "(n_i) = " << p << "\n";
    cout << "q = A_" << j << "(n_j) = " << q << "\n";
    cout << "Recomputed p*q       : " << N_recomputed << "\n";
    cout << "s = " << BigInt::divSmallExact(two_s,2) << "   d = " << BigInt::divSmallExact(two_d,2) << "\n";
    cout << "Digit-for-digit match: " << (match ? "YES -- certificate CONFIRMED" : "NO -- MISMATCH") << "\n";
    cout << "(No Miller-Rabin call, no division, no external library used in this check.)\n";
}

// ============================================================================
// SECTION 6: entry point
// ============================================================================
int main(int argc, char** argv) {
    if (argc < 2) {
        cerr << "Unified Semiprime Toolkit\n\n";
        cerr << "Usage:\n";
        cerr << "  " << argv[0] << " generate n_start n_end [mr_rounds]\n";
        cerr << "      Finds primes A_k(n) for n in [n_start,n_end] (Miller-Rabin,\n";
        cerr << "      the only test performed), then forms every pairwise product\n";
        cerr << "      -- each a semiprime by construction, no test on the result.\n\n";
        cerr << "  " << argv[0] << " verify N i n_i j n_j\n";
        cerr << "      Checks the claim N = A_i(n_i)*A_j(n_j) by multiplication only\n";
        cerr << "      -- no Miller-Rabin, no division, no external library.\n";
        return 1;
    }
    string mode = argv[1];
    if (mode == "generate") {
        if (argc < 4) { cerr << "generate needs: n_start n_end [mr_rounds] [--sorted] [--verify]\n"; return 1; }
        int rounds = 20;
        bool sorted_output = false, self_verify = false;
        for (int a = 4; a < argc; a++) {
            string arg = argv[a];
            if (arg == "--sorted") sorted_output = true;
            else if (arg == "--verify") self_verify = true;
            else rounds = stoi(arg);
        }
        mode_generate(argv[2], argv[3], rounds, sorted_output, self_verify);
    } else if (mode == "verify") {
        if (argc < 7) { cerr << "verify needs: N i n_i j n_j\n"; return 1; }
        mode_verify(argv[2], stoi(argv[3]), argv[4], stoi(argv[5]), argv[6]);
    } else {
        cerr << "Unknown mode '" << mode << "'. Use 'generate' or 'verify'.\n";
        return 1;
    }
    return 0;
}