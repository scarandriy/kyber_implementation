/**************************************************************
 *
 * This single C++ file demonstrates a simplified version of
 * CRYSTALS-Kyber. It contains implementations of the main 
 * reference algorithms:
 *
 *   1) CBD (noise generation)
 *   2) NTT (Number Theoretic Transform)
 *   3) Inverse NTT
 *   4) PolyCompress/PolyDecompress
 *   5) IndCPA KeyGen
 *   6) IndCPA Enc
 *   7) IndCPA Dec
 *   8) KEM Encaps
 *   9) KEM Decaps
 *
 * IMPORTANT NOTES (Semester Project):
 *   - This code was written as part of a Bachelor's semester
 *     project by a second-year CS student, so it's mainly 
 *     for educational exploration.
 *   - It's not secure for real-world use because it lacks 
 *     constant-time operations, advanced random generation,
 *     and other crucial security features.
 *   - For real applications, you must rely on official or
 *     formally verified implementations of Kyber.
 ***************************************************************/

#include <bits/stdc++.h>
using namespace std;

/************************************************
* (1) Kyber512-like Parameters
*    These values help define the polynomial 
*    dimensions, modulus, etc.
************************************************/
static const int KYBER_N         = 256;
static const int KYBER_Q         = 3329;
static const int KYBER_K         = 2;     // Matrix dimension
static const int KYBER_ETA       = 2;     // Controls noise generation
static const int KYBER_POLYBYTES = 384;   // Not strictly used here
static const int SEEDBYTES       = 32;    // Size for seeds
static const int NOISESEEDBYTES  = 32;    // Size for noise seeds
static const int SYMBYTES        = 32;    // Typically 256-bit security
static const int KEYBYTES        = 32;    // 256-bit shared key

// These define how many bits are used in the compression
// for different parts of the ciphertext.
static const int COMP_U_BITS = 10;
static const int COMP_V_BITS = 4;

// Constants used in Montgomery and Barrett reductions.
// These were taken from official Kyber reference code.
static const int16_t MONT = 2285;  // 2^16 mod Q
static const int32_t QINV = 62209; // -inverse(Q) mod 2^16

/************************************************
* A struct for one polynomial (N=256 coefficients)
************************************************/
struct poly {
    int16_t coeffs[KYBER_N];
};

/************************************************
* (2) Basic modular arithmetic functions
*    These help reduce numbers modulo Q.
************************************************/
static inline int16_t montgomery_reduce(int32_t a) {
    // This function reduces the number 'a' using
    // Montgomery arithmetic. 
    int32_t m = (int32_t)((int64_t)a * QINV >> 16);
    int32_t r = a - m * KYBER_Q;
    return (int16_t)r;
}

static inline int16_t barrett_reduce(int16_t a) {
    // This function performs Barrett reduction. It's a
    // faster way to bring 'a' into the range [0, Q).
    const int32_t v = ((1U << 26) + (KYBER_Q/2))/KYBER_Q;
    int32_t t = ((int32_t) a * v) >> 26;
    t *= KYBER_Q;
    return (int16_t)(a - t);
}

static inline int16_t csubq(int16_t a) {
    // Ensures the result is in [0, Q).
    a -= (a >> 15) & KYBER_Q;
    if(a >= KYBER_Q) a -= KYBER_Q;
    return a;
}

/************************************************
* (3) Forward and Inverse NTT
*    The NTT helps with polynomial multiplication.
************************************************/

// Precomputed "zetas" array used in NTT. 
// These values come from the official Round 3 code.
static const int16_t zetas[128] = {
  2285, 3181, 1018, 313,  2049,  1401,  3225,  1551,
  3301, 2674, 1950, 1599,  3099,  2227, 1741,  806,
  2682, 2018, 288,  3193,  911,   2040, 1356,  2057,
  2675, 342,  1478, 184,   2521,  2499, 1275,  1789,
  287,  1517, 400,  2371,  1453,  3022, 697,   450,
  2341, 1441, 2892, 904,   489,   3293, 1025,  1771,
  1328, 217,  1440, 1671,  106,   1907, 2265,  1640,
  2780, 233,  116,  1037,  2939,  1660, 2541,  1151,
  2334, 1808, 2710, 219,   1184,  2657, 1223,  1373,
  179,  2207, 1397, 2686,  2975,  800,  1081,  2591,
  3235, 2648, 1841, 2483,  2735,  3305, 1070,  2801,
  1235, 1988, 1174, 697,   3085,  2773, 2038,  340,
  2085, 129,  230,  2211,  516,   1271, 2770,  1901,
  1784, 2245, 3030, 2367,  1237,  137,  2854,  3162,
  2369, 166,  250,  1425,  1166,  2476, 1904,  3381,
  2331, 3027, 1026, 247,   709,   575,  3205
};

// Basic multiplication in the Montgomery domain
static inline int16_t montmul(int16_t a, int16_t b) {
    return montgomery_reduce((int32_t)a * b);
}

/* Forward NTT: transforms a polynomial from normal domain 
   to the NTT domain for faster multiplication. */
static void ntt(int16_t *a) {
    for(int level=0; level<7; level++){
        int distance = (1 << level);
        for(int j=0; j<distance; j++){
            int16_t zeta = zetas[distance - 1 + j];
            for(int i=j; i<KYBER_N; i+=(distance<<1)){
                int16_t t = montmul(a[i+distance], zeta);
                a[i+distance] = barrett_reduce(a[i] - t);
                a[i]          = barrett_reduce(a[i] + t);
            }
        }
    }
}

/* Inverse NTT: transforms data back from the NTT domain 
   to the normal polynomial domain. */
static void invntt(int16_t *a) {
    for(int level=6; level>=0; level--){
        int distance = (1 << level);
        for(int j=0; j<distance; j++){
            int16_t zeta = zetas[distance - 1 + j];
            for(int i=j; i<KYBER_N; i+=(distance<<1)){
                int16_t t = a[i];
                a[i] = barrett_reduce(t + a[i+distance]);
                a[i+distance] = barrett_reduce(t - a[i+distance]);
                a[i+distance] = montmul(a[i+distance], zeta);
            }
        }
    }
    // We multiply by the modular inverse of 256 mod Q.
    // That inverse is 62209 in this setting.
    for(int i=0; i<KYBER_N; i++){
        a[i] = montmul(a[i], 62209);
    }
}

/************************************************
* (4) Polynomial Compression and Decompression
*    Compress coefficients to fewer bits to save space.
************************************************/
static vector<uint8_t> poly_compress(const poly &p, int dbits){
    /* Each coefficient is squeezed into 'dbits' bits 
       so the size is smaller. */
    int totalBits  = dbits * KYBER_N;
    int totalBytes = (totalBits + 7)/8;
    vector<uint8_t> out(totalBytes, 0);
    uint32_t bitpos=0;
    for(int i=0; i<KYBER_N; i++){
        int16_t c = p.coeffs[i];
        c = barrett_reduce(c);
        c = csubq(c);
        // Scale from [0, Q) down to [0, 2^dbits).
        uint32_t val = ( ((uint32_t)c << dbits ) + (KYBER_Q >> 1) ) / KYBER_Q;
        val &= ( (1U << dbits) -1U );
        for(int b=0; b<dbits; b++){
            if(val & (1U<<b)){
                out[bitpos>>3] |= (1U<<(bitpos&7));
            }
            bitpos++;
        }
    }
    return out;
}

static void poly_decompress(poly &r, const vector<uint8_t> &in, int dbits){
    // Rebuild the polynomial coefficients from dbits representation.
    memset(r.coeffs, 0, sizeof(r.coeffs));
    uint32_t bitpos=0;
    for(int i=0; i<KYBER_N; i++){
        uint32_t val=0;
        for(int b=0; b<dbits; b++){
            uint32_t bit = ( in[bitpos>>3] >> (bitpos & 7) ) &1U;
            val |= (bit << b);
            bitpos++;
        }
        // Scale it back up to the modulo Q domain.
        uint32_t tmp = (uint32_t)(
            ( (uint64_t)val * KYBER_Q ) + ( (1ULL<<(dbits-1)) )
            ) >> dbits ;
        r.coeffs[i] = csubq(barrett_reduce((int16_t)tmp));
    }
}

/************************************************
* (Helper) Pointwise multiply two polynomials
* in NTT domain, then reduce.
************************************************/
static void poly_pointwise(poly &r, const poly &a, const poly &b){
    for(int i=0; i<KYBER_N; i++){
        r.coeffs[i] = montmul(a.coeffs[i], b.coeffs[i]);
    }
}

/************************************************
* (1) CBD: Generates polynomial noise from seed 
*    (Also labeled as #1 in the initial summary).
************************************************/
static void cbd(poly &r, const uint8_t *buf, int eta){
    // Here, we implement the simpler case for eta=2.
    // We split bits of the input to form small random
    // differences in the range [-1, 1].
    for(int i=0; i<KYBER_N/8; i++){
        uint16_t t = (buf[2*i] | ( (uint16_t)buf[2*i+1]<<8 ));
        uint16_t d0 = t & 0x5555;
        uint16_t d1 = (t >> 1) & 0x5555;
        d0 = (uint16_t)__builtin_popcount(d0);
        d1 = (uint16_t)__builtin_popcount(d1);
        for(int j=0; j<8; j++){
            int16_t a = ( (d0 >> j) & 1 );
            int16_t b = ( (d1 >> j) & 1 );
            r.coeffs[8*i + j] = a - b;
        }
    }
}

/************************************************
* (Utility) Randombytes and a simple Shake 
*    (NOT secure! Just for demonstration).
************************************************/
static void randombytes(uint8_t *out, size_t len){
    // This is just a quick Mersenne Twister approach.
    // Real code should use a cryptographic RNG.
    static mt19937 rng(0x12345678);
    for(size_t i=0;i<len;i++){
        out[i] = (uint8_t)(rng() & 0xFF);
    }
}

static void shake128(uint8_t *out, size_t outlen, 
                     const uint8_t *in, size_t inlen){
    // This is just a placeholder for demonstration.
    // Real code should use official SHAKE or other 
    // cryptographic hash function.
    static mt19937 rng(0xABCDEF);
    for(size_t i=0; i<inlen; i++){
        rng.seed(rng() ^ in[i]);
    }
    for(size_t i=0; i<outlen; i++){
        out[i] = (uint8_t)(rng() &0xFF);
    }
}

/************************************************
* Expand the matrix A from a seed
* A has size k x k (k=2 here) of polynomials.
************************************************/
static void gen_matrix(vector<poly> &A, const uint8_t *seed){
    // For Kyber512, we have a 2x2 matrix of polynomials.
    // We generate each polynomial by hashing the seed
    // with indices (i, j).
    A.resize(KYBER_K*KYBER_K);
    for(int i=0; i<KYBER_K; i++){
        for(int j=0; j<KYBER_K; j++){
            uint8_t extseed[SEEDBYTES+2];
            memcpy(extseed, seed, SEEDBYTES);
            extseed[SEEDBYTES]   = (uint8_t)i;
            extseed[SEEDBYTES+1] = (uint8_t)j;

            // For eta=2, we need some random bytes for polynomial 
            // generation via CBD.
            vector<uint8_t> buf( (KYBER_N*KYBER_ETA*2)/8 + 2, 0);
            shake128(buf.data(), buf.size(), extseed, SEEDBYTES+2);

            // Make the polynomial with CBD and then convert 
            // into NTT domain.
            poly temp;
            cbd(temp, buf.data(), KYBER_ETA);
            ntt(temp.coeffs);
            A[i*KYBER_K + j] = temp;
        }
    }
}

/************************************************
* IndCPA KeyGen (Algorithm 5 in summary)
************************************************/
struct PublicKey {
    uint8_t seed[SEEDBYTES];
    vector<uint8_t> tbytes;
};

struct SecretKey {
    vector<uint8_t> sbytes;
    uint8_t hpk[32];
};

static void indcpa_keypair(PublicKey &pk, SecretKey &sk){
    // Step 1: Generate 64 random bytes, split into 
    // (rho, sigma).
    uint8_t buf[64];
    randombytes(buf,64);
    memcpy(pk.seed, buf, SEEDBYTES);
    uint8_t sigma[SEEDBYTES];
    memcpy(sigma, buf+32, SEEDBYTES);

    // Step 2: Create matrix A from rho.
    vector<poly> A;
    gen_matrix(A, pk.seed);

    // Step 3: Sample s and e using sigma with CBD,
    // then convert them to NTT form.
    vector<poly> s(KYBER_K), e(KYBER_K), t(KYBER_K);
    vector<uint8_t> noiseseed(KYBER_K * (KYBER_N/8) * 2 * 2);
    shake128(noiseseed.data(), noiseseed.size(), sigma, SEEDBYTES);

    int offset=0;
    for(int i=0;i<KYBER_K;i++){
        cbd(s[i], &noiseseed[offset], KYBER_ETA);
        offset += (KYBER_N/8)*2;
        ntt(s[i].coeffs);
    }
    for(int i=0;i<KYBER_K;i++){
        cbd(e[i], &noiseseed[offset], KYBER_ETA);
        offset += (KYBER_N/8)*2;
        ntt(e[i].coeffs);
    }

    // Step 4: Compute t[i] = sum of A[i][j]*s[j] + e[i] (in NTT).
    // For a smaller k=2, we basically do 2 polynomials for i.
    for(int i=0;i<KYBER_K;i++){
        // We'll do a naive approach of iNTT e[i], add partial 
        // sums, then re-NTT. In official code, it can be done 
        // more efficiently.
        t[i] = e[i];
        invntt(t[i].coeffs);
        for(int j=0;j<KYBER_K;j++){
            poly temp;
            for(int x=0;x<KYBER_N;x++) temp.coeffs[x]=0;
            poly_pointwise(temp, A[i*KYBER_K + j], s[j]);
            invntt(temp.coeffs);
            for(int x=0;x<KYBER_N;x++){
                t[i].coeffs[x] = barrett_reduce(t[i].coeffs[x] + temp.coeffs[x]);
            }
        }
        ntt(t[i].coeffs);
    }

    // Step 5: Compress t and put into pk.
    pk.tbytes.clear();
    for(int i=0;i<KYBER_K;i++){
        auto comp = poly_compress(t[i], COMP_U_BITS);
        pk.tbytes.insert(pk.tbytes.end(), comp.begin(), comp.end());
    }

    // Step 6: Compress s and store it in sk.
    sk.sbytes.clear();
    for(int i=0;i<KYBER_K;i++){
        auto comp = poly_compress(s[i], COMP_U_BITS);
        sk.sbytes.insert(sk.sbytes.end(), comp.begin(), comp.end());
    }

    // Step 7: Hash the entire pk into sk.hpk (for KEM usage).
    vector<uint8_t> pkraw;
    pkraw.insert(pkraw.end(), pk.seed, pk.seed+SEEDBYTES);
    pkraw.insert(pkraw.end(), pk.tbytes.begin(), pk.tbytes.end());
    vector<uint8_t> hashpk(32,0);
    shake128(hashpk.data(), 32, pkraw.data(), pkraw.size());
    memcpy(sk.hpk, hashpk.data(), 32);
}

/************************************************
* IndCPA Encryption (Algorithm 6)
************************************************/
struct Ciphertext {
    vector<uint8_t> c; // c = compressed(u) || compressed(v)
};

static void indcpa_enc(Ciphertext &ct, 
                       const uint8_t *msg, // 32-byte message or bit-packed
                       const PublicKey &pk, 
                       const uint8_t *coins) 
{
    // 1) Recreate matrix A from pk.seed,
    //    and decompress pk.t (which is in NTT form).
    vector<poly> A;
    gen_matrix(A, pk.seed);

    vector<poly> t(KYBER_K);
    {
        size_t offset=0;
        for(int i=0; i<KYBER_K; i++){
            vector<uint8_t> sub(pk.tbytes.begin()+offset,
                                pk.tbytes.begin()+offset + (COMP_U_BITS*KYBER_N+7)/8);
            poly_decompress(t[i], sub, COMP_U_BITS);
            offset += (COMP_U_BITS*KYBER_N+7)/8;
        }
    }

    // 2) Sample r, e1, e2 from 'coins' and convert them to NTT domain.
    vector<poly> r(KYBER_K), e1(KYBER_K);
    poly e2, mp;
    vector<uint8_t> buf(320);
    shake128(buf.data(), buf.size(), coins, 32);

    int offset=0;
    for(int i=0;i<KYBER_K;i++){
        cbd(r[i], &buf[offset], KYBER_ETA);
        offset += (KYBER_N/8)*2;
        ntt(r[i].coeffs);
    }
    for(int i=0;i<KYBER_K;i++){
        cbd(e1[i], &buf[offset], KYBER_ETA);
        offset += (KYBER_N/8)*2;
        ntt(e1[i].coeffs);
    }
    cbd(e2, &buf[offset], KYBER_ETA);
    offset += (KYBER_N/8)*2;
    ntt(e2.coeffs);

    // 3) Encode msg into a polynomial m, then NTT it.
    memset(mp.coeffs,0,sizeof(mp.coeffs));
    // We'll assume msg is 32 bytes, but only up to 256 bits might be used.
    for(int i=0; i<KYBER_N/8 && i<32; i++){
        for(int b=0;b<8;b++){
            int bit= (msg[i]>>b)&1;
            mp.coeffs[8*i + b] = bit*(KYBER_Q/2);
        }
    }
    ntt(mp.coeffs);

    // 4) Compute u = A*r + e1 (polynomial vector).
    //    Each u[i] = sum over j(A[i][j]*r[j]) + e1[i].
    vector<poly> u(KYBER_K);
    for(int i=0;i<KYBER_K;i++){
        u[i] = e1[i];
        for(int j=0;j<KYBER_K;j++){
            poly temp;
            for(int x=0;x<KYBER_N;x++) temp.coeffs[x]=0;
            poly_pointwise(temp, A[i*KYBER_K + j], r[j]);
            for(int x=0;x<KYBER_N;x++){
                u[i].coeffs[x] = barrett_reduce(u[i].coeffs[x] + temp.coeffs[x]);
            }
        }
    }

    // 5) Compute v = t*r + e2 + m.
    poly v;
    memset(v.coeffs,0,sizeof(v.coeffs));
    for(int x=0;x<KYBER_N;x++){
        v.coeffs[x] = e2.coeffs[x];
    }
    for(int j=0;j<KYBER_K;j++){
        poly temp;
        memset(temp.coeffs,0,sizeof(temp.coeffs));
        poly_pointwise(temp, t[j], r[j]);
        for(int x=0;x<KYBER_N;x++){
            v.coeffs[x] = barrett_reduce(v.coeffs[x] + temp.coeffs[x]);
        }
    }
    // Add the message polynomial
    for(int x=0;x<KYBER_N;x++){
        v.coeffs[x] = barrett_reduce(v.coeffs[x] + mp.coeffs[x]);
    }

    // 6) Compress u and v into the ciphertext.
    vector<uint8_t> c;
    for(int i=0;i<KYBER_K;i++){
        auto cu = poly_compress(u[i], COMP_U_BITS);
        c.insert(c.end(), cu.begin(), cu.end());
    }
    auto cv = poly_compress(v, COMP_V_BITS);
    c.insert(c.end(), cv.begin(), cv.end());
    ct.c = std::move(c);
}

/************************************************
* IndCPA Dec (Algorithm 7)
************************************************/
static void indcpa_dec(uint8_t *msg, 
                       const Ciphertext &ct,
                       const SecretKey &sk)
{
    // 1) Decompress the secret key polynomials from sk.sbytes
    vector<poly> s(KYBER_K);
    {
        int offset=0;
        for(int i=0;i<KYBER_K;i++){
            int compSize = (COMP_U_BITS*KYBER_N+7)/8;
            vector<uint8_t> sub(sk.sbytes.begin()+offset,
                                 sk.sbytes.begin()+offset + compSize);
            poly_decompress(s[i], sub, COMP_U_BITS);
            offset+=compSize;
        }
    }

    // 2) Decompress the ciphertext polynomials (u and v)
    vector<poly> u(KYBER_K);
    poly v;
    {
        int offset=0;
        for(int i=0;i<KYBER_K;i++){
            int compSize = (COMP_U_BITS*KYBER_N+7)/8;
            vector<uint8_t> sub(ct.c.begin()+offset,
                                ct.c.begin()+offset + compSize);
            poly_decompress(u[i], sub, COMP_U_BITS);
            offset+=compSize;
        }
        int compSizeV= (COMP_V_BITS*KYBER_N+7)/8;
        vector<uint8_t> sub(ct.c.begin()+offset,
                            ct.c.begin()+offset + compSizeV);
        poly_decompress(v, sub, COMP_V_BITS);
    }

    // 3) Compute the polynomial v' = v - sum(u[i]*s[i]) in normal domain.
    for(int i=0;i<KYBER_K;i++){
        ntt(s[i].coeffs);
    }
    for(int i=0;i<KYBER_K;i++){
        ntt(u[i].coeffs);
    }

    poly sumPoly;
    memset(sumPoly.coeffs, 0, sizeof(sumPoly.coeffs));
    for(int i=0;i<KYBER_K;i++){
        poly temp;
        memset(temp.coeffs,0,sizeof(temp.coeffs));
        poly_pointwise(temp, u[i], s[i]);
        for(int x=0;x<KYBER_N;x++){
            sumPoly.coeffs[x] = barrett_reduce(sumPoly.coeffs[x] + temp.coeffs[x]);
        }
    }
    invntt(sumPoly.coeffs);

    invntt(v.coeffs);
    for(int i=0;i<KYBER_N;i++){
        v.coeffs[i] = barrett_reduce(v.coeffs[i] - sumPoly.coeffs[i]);
    }

    // 4) Decode the message from v's coefficients.
    memset(msg, 0, KYBER_N/8);
    for(int i=0;i<KYBER_N;i++){
        int16_t val= barrett_reduce(v.coeffs[i]);
        val= csubq(val);
        int bit= (val > (KYBER_Q/2));
        msg[i>>3] |= (bit << (i & 7));
    }
}

/************************************************
* (Helper) Hash function for FO transformations
*    We use 64 bytes of output from the input.
************************************************/
static void hash_g(uint8_t *out, const uint8_t *in, size_t inlen){
    // Real code should do a proper cryptographic hash 
    // like SHAKE256 or similar. This is just for demo.
    shake128(out, 64, in, inlen);
}

/************************************************
* KEM.Encaps (Algorithm 8)
************************************************/
struct KEMCiphertext {
    Ciphertext ct;
    uint8_t key[KEYBYTES];
};

static void kem_encaps(KEMCiphertext &out, const PublicKey &pk){
    // 1. Generate a random 32-byte message M.
    uint8_t M[32];
    randombytes(M, 32);

    // 2. Hash M and pk together to get (K, r).
    vector<uint8_t> cat;
    cat.insert(cat.end(), M, M+32);
    cat.insert(cat.end(), pk.seed, pk.seed+SEEDBYTES);
    cat.insert(cat.end(), pk.tbytes.begin(), pk.tbytes.end());
    uint8_t kr[64];
    hash_g(kr, cat.data(), cat.size());

    uint8_t K[32], r[32];
    memcpy(K, kr, 32);
    memcpy(r, kr+32, 32);

    // 3. Encrypt M with IndCPA using 'r' for random coins.
    Ciphertext c;
    indcpa_enc(c, M, pk, r);

    // 4. Output the ciphertext and the key K.
    out.ct = c;
    memcpy(out.key, K, 32);
}

/************************************************
* KEM.Decaps (Algorithm 9)
************************************************/
static void kem_decaps(uint8_t *sharedkey, 
                       const KEMCiphertext &in_ct, 
                       const PublicKey &pk, 
                       const SecretKey &sk) 
{
    // 1. Decrypt the ciphertext to get M'.
    uint8_t Mprime[KYBER_N/8];
    indcpa_dec(Mprime, in_ct.ct, sk);

    // 2. Hash M' and pk the same way as in Encaps.
    vector<uint8_t> cat;
    cat.insert(cat.end(), Mprime, Mprime+(KYBER_N/8));
    cat.insert(cat.end(), pk.seed, pk.seed+SEEDBYTES);
    cat.insert(cat.end(), pk.tbytes.begin(), pk.tbytes.end());
    uint8_t kr[64];
    hash_g(kr, cat.data(), cat.size());

    uint8_t Kprime[32], rprime[32];
    memcpy(Kprime, kr, 32);
    memcpy(rprime, kr+32, 32);

    // 3. Re-encrypt M' to get c' and compare with the received ciphertext.
    Ciphertext cprime;
    indcpa_enc(cprime, Mprime, pk, rprime);

    // 4. If there's a mismatch, produce a random key. Otherwise, use K'.
    bool mismatch=false;
    if(cprime.c.size()!= in_ct.ct.c.size()) {
        mismatch=true;
    } else {
        if(!equal(cprime.c.begin(), cprime.c.end(), in_ct.ct.c.begin())) {
            mismatch=true;
        }
    }
    if(mismatch){
        uint8_t tmp[32];
        randombytes(tmp,32);
        memcpy(sharedkey, tmp, 32);
    } else {
        memcpy(sharedkey, Kprime, 32);
    }
}

/************************************************
* A simple main() function to show usage
************************************************/
int main(){
    cout << "=== Kyber-Like DEMO (Semester Project) ===\n";

    // Generate Key Pair (IndCPA-based)
    PublicKey pk;
    SecretKey sk;
    indcpa_keypair(pk, sk);
    cout << "[KeyGen] Done.\n";

    // IndCPA Encryption/Decryption
    uint8_t message[32];
    memset(message, 0x77, 32);
    Ciphertext c;
    uint8_t coins[32];
    memset(coins, 0xAA, 32); // Example ephemeral randomness

    indcpa_enc(c, message, pk, coins);
    cout << "[CPA Encrypt] Ciphertext size = " << c.c.size() << "\n";

    uint8_t decrypted[32];
    memset(decrypted,0,sizeof(decrypted));
    indcpa_dec(decrypted, c, sk);
    cout << "[CPA Decrypt] First 8 bytes of decrypted msg: ";
    for(int i=0;i<8;i++){
        cout << (int)decrypted[i] << " ";
    }
    cout << "\n";

    // KEM Encapsulation
    KEMCiphertext kemct;
    kem_encaps(kemct, pk);
    cout << "[KEM Encaps] Key: ";
    for(int i=0;i<32;i++){
        cout << hex << (int)kemct.key[i] << " ";
    }
    cout << dec << "\n";

    // KEM Decapsulation
    uint8_t sharedkey[32];
    kem_decaps(sharedkey, kemct, pk, sk);
    cout << "[KEM Decaps] Key: ";
    for(int i=0;i<32;i++){
        cout << hex << (int)sharedkey[i] << " ";
    }
    cout << dec << "\n";

    bool match = true;
    for(int i=0;i<32;i++){
        if(sharedkey[i] != kemct.key[i]) {
            match = false; 
            break;
        }
    }
    if(match) cout << "KEM Keys match!\n";
    else      cout << "KEM Keys mismatch!\n";

    return 0;
}

