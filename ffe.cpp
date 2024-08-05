#include "emp-tool/emp-tool.h"
#include "emp-zk/emp-zk-arith/emp-zk-arith.h"

#define HIGH64(x) _mm_extract_epi64((block)x, 1)


struct ffe {
#ifndef FFE_SIMPLE
    constexpr static u64 mod = 0x1fffffffffffffff; // Prime for the finite field
    constexpr static u64 mod_pow = 61; // mod = 2**mod_pow - 1
#else
    constexpr static u64 mod = 7;
    constexpr static u64 mod_pow = 3;
#endif
    u64 x;
    constexpr ffe(): x{0} {}
    constexpr ffe(s32 x_): x{x_ < 0 ? x_ + mod : x_} {}
    constexpr ffe(u64 x_): x{x_} {x %= mod;}
    // constexpr ffe(s64 x_): x{0} {x_ %= (s64)mod; x = x_ < 0 ? x_+mod : x_;}

    static constexpr ffe make_invalid() { ffe x; x.x = -1; return x; }
    bool is_invalid() { return x == (u64)-1; }

    //Implementing addition and substraction and multiplication in the finite field
    ffe& operator+= (ffe y) {
        // if (x/2 + y.x/2 >= 1<<63) x -= mod;
        u64 gap = mod - x;
        if (y.x >= gap) x = y.x - gap;
        else x += y.x;
        if (x >= mod) x -= mod;
        return *this;
    }
    ffe& operator-= (ffe y) { y.x > x? x = mod - y.x + x: x -= y.x; return *this; }
    ffe operator+ (ffe y) const { ffe z {*this}; z += y; return z; }
    ffe operator- (ffe y) const { ffe z {*this}; z -= y; return z; }
    
    ffe operator* (ffe y) const {
#ifndef FFE_SIMPLE
        u128 z = (u128)x * y.x;
        while (z > (u128)mod) z -= (u128)mod;
        return (u64)z;
#else
        return (x * y.x) % mod;
#endif
    }
    ffe& operator*= (ffe y) { x = (*this * y).x; return *this; }

    bool operator== (ffe y) const { return x == y.x; }
    bool operator!= (ffe y) const { return x != y.x; }

    //Computing the inverse and division
    ffe inv() const {
        u64 t = 0, t_new = 1, r = mod, r_new = x;
        while (r_new) {
            u64 q = r / r_new, tmp;
            tmp = t_new; t_new = t - q * t_new; t = tmp;
            tmp = r_new; r_new = r - q * r_new; r = tmp;
        }
        return t > mod ? t + mod : t;
    }
    ffe operator/ (ffe y) const { return *this * y.inv(); }
    ffe& operator/= (ffe y) { *this *= y.inv(); return *this; }

    static ffe pow2(s64 exp) {
        exp %= mod_pow;
        if (exp < 0) exp += mod_pow;
        ffe r;
        r.x = 1ull << exp;
        return r;

    }
};
ffe operator+ (s32 x, ffe y) { return ffe{x} + y; }
ffe operator- (s32 x, ffe y) { return ffe{x} - y; }
ffe operator* (s32 x, ffe y) { return ffe{x} * y; }
ffe operator/ (s32 x, ffe y) { return ffe{x} / y; }

struct Polynomial { // Defining the Ring F[X]/(X^3)
    ffe a,b,c; // a * x**2 + b * x + c

    //Ring Operations on Polynomials
    Polynomial& operator+= (Polynomial y) { a += y.a; b += y.b; c += y.c; return *this; }
    Polynomial& operator-= (Polynomial y) { a -= y.a; b -= y.b; c -= y.c; return *this; }
    Polynomial operator+ (Polynomial y) const { Polynomial z {*this}; z += y; return z; }
    Polynomial operator- (Polynomial y) const { Polynomial z {*this}; z -= y; return z; }
    
    Polynomial operator* (Polynomial y) const {
        assert(not (a.x and y.b.x) and not (y.a.x and b.x) and not (a.x and y.a.x));
        return {a*y.c + b*y.b + c*y.a, b*y.c + c*y.b, c*y.c};
    }
    Polynomial& operator*= (Polynomial y) { *this = (*this * y); return *this; }
    Polynomial& operator*= (ffe y) { a *= y; b *= y; c *= y; return *this; }

    bool operator== (Polynomial y) const { return a == y.a and b == y.b and c == y.c; }
    bool operator!= (Polynomial y) const { return a != y.a or  b != y.b or  c != y.c; }
    
    // Evaluation on the polynomial in finite field
    ffe operator() (ffe x) const { return (a * x + b) * x + c; }
    // Degree reduction
    Polynomial degree_reduced() const { return {0, a + b, c}; }

    bool is_linear() { return a.x == 0; }
    bool is_constant() { return a.x == 0 and b.x == 0; }
};

class VOLECommitment;

class Commitment{
public:
    enum Commit_Type: u8 {
        VOLE, PEDERSEN
    };
    virtual void CommitEqual(Commitment* x) = 0;
    virtual void CommitEqual(uint64_t x) = 0;
    virtual Commitment* add(Commitment* x) = 0;
    virtual Commitment* mult(Commitment* x) = 0;
    virtual Commitment* mult(const uint64_t x) = 0;
    virtual uint64_t reveal() = 0;
    virtual uint64_t revealALICE() = 0;
    virtual void check_zero() = 0;
    virtual Commitment* negate() = 0;
    virtual ~Commitment() {}
};

class VOLECommitment: public Commitment {
public:

    IntFp intfp;

    VOLECommitment(): intfp() {}

    VOLECommitment(uint64_t value, int party = PUBLIC) {this->intfp = IntFp(value, party);}

    VOLECommitment(s8 value, int party = PUBLIC) {
        if (value < 0) this->intfp = IntFp((uint64_t)(-value), party).negate();
        else this->intfp = IntFp((uint64_t)value, party);
    }

    void CommitEqual(Commitment* x) override {
        (this->intfp + (((VOLECommitment*)x)->intfp.negate())).reveal_zero();
    }

    void CommitEqual(uint64_t x) override {
        (this->intfp + (IntFp(x).negate())).reveal_zero();
    }

    Commitment* add (Commitment* x) override {
        VOLECommitment* ret = new VOLECommitment;
        ret->intfp = this->intfp + ((VOLECommitment*)x)->intfp;
        return ret;
    }

    Commitment* mult(Commitment* x) override {
        VOLECommitment* ret = new VOLECommitment;
        ret->intfp = this->intfp * ((VOLECommitment*)x)->intfp;
        return ret;
    }

    Commitment* mult(uint64_t x) override {
        VOLECommitment* ret = new VOLECommitment;
        ret->intfp = this->intfp * x;
        return ret;
    }

    uint64_t reveal() override {return this->intfp.reveal();}

    uint64_t revealALICE() override {return HIGH64(this->intfp.value);}

    Commitment* negate() override {
        VOLECommitment* ret = new VOLECommitment;
        ret->intfp = this->intfp.negate();
        return ret;
    }

    void check_zero() override {this->intfp.reveal_zero();}
};

class PedersenCommitment: public Commitment {
public:

    BIGNUM *c_PUBLIC;
    BIGNUM *r_ALICE;
    BIGNUM *m_ALICE;

    // void CommitEqual(Commitment* x) override {
    //     (this->intfp + (((VOLECommitment*)x)->intfp.negate())).reveal_zero();
    // }

    // void CommitEqual(uint64_t x) override {
    //     (this->intfp + (IntFp(x).negate())).reveal_zero();
    // }

    // Commitment* add (Commitment* x) override {
    //     VOLECommitment* ret = new VOLECommitment;
    //     ret->intfp = this->intfp + ((VOLECommitment*)x)->intfp;
    //     return ret;
    // }

    // Commitment* mult(Commitment* x) override {
    //     VOLECommitment* ret = new VOLECommitment;
    //     ret->intfp = this->intfp * ((VOLECommitment*)x)->intfp;
    //     return ret;
    // }

    // Commitment* mult(uint64_t x) override {
    //     VOLECommitment* ret = new VOLECommitment;
    //     ret->intfp = this->intfp * x;
    //     return ret;
    // }

    // uint64_t reveal() override {return this->intfp.reveal();}

    // uint64_t revealALICE() override {return HIGH64(this->intfp.value);}

    // Commitment* negate() override {
    //     VOLECommitment* ret = new VOLECommitment;
    //     ret->intfp = this->intfp.negate();
    //     return ret;
    // }

    // void check_zero() override {this->intfp.reveal_zero();}
};

Commitment* Commit(uint64_t value, int party = PUBLIC, u8 type = Commitment::VOLE){
    if (type == Commitment::VOLE) {
        VOLECommitment* ret = new VOLECommitment;
        ret->intfp = IntFp(value, party);
        return ret;
    } else {
        // PedersenCommitment* ret = new PedersenCommitment;
        // BN_set_u64(ret->m_ALICE, value);
        
    }
}


void polynomial_print(Polynomial p) {
    bool first = true;
    if (p.a.x) {
        first = false;
        if (p.a.x != 1) {
            printf("%llx ", p.a.x);
        }
        printf(u8"x²");
    }
    if (p.b.x) {
        if (not first) printf(" + ");
        first = false;
        if (p.b.x != 1) {
            printf("%llx ", p.b.x);
        }
        printf(u8"x");
    }
    if (first or p.c.x) {
        if (not first) printf(" + ");
        printf("%llx", p.c.x);
    }
};

void CommittedPoly_print(vector<Commitment*> p) {
    bool first = true;
    auto a = p[0]->reveal();
    auto b = p[1]->reveal();
    auto c = p[2]->reveal();
    if (a) {
        first = false;
        if (a != 1) {
            printf("%llx ", a);
        }
        printf(u8"x²");
    }
    if (b) {
        if (not first) printf(" + ");
        first = false;
        if (b != 1) {
            printf("%llx ", b);
        }
        printf(u8"x");
    }
    if (first or c) {
        if (not first) printf(" + ");
        printf("%llx", c);
    }
}