
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
    constexpr ffe(s64 x_): x{0} {x_ %= (s64)mod; x = x_ < 0 ? x_+mod : x_;}

    static constexpr ffe make_invalid() { ffe x; x.x = -1; return x; }
    bool is_invalid() { return x == (u64)-1; }

    //Implementing addition and substraction and multiplication in the finite field
    ffe& operator+= (ffe y) { x += y.x; if (x >= mod) x -= mod; return *this; }
    ffe& operator-= (ffe y) { x -= y.x; if (x >  mod) x += mod; return *this; }
    ffe operator+ (ffe y) const { ffe z {*this}; z += y; return z; }
    ffe operator- (ffe y) const { ffe z {*this}; z -= y; return z; }
    
    ffe operator* (ffe y) const {
#ifndef FFE_SIMPLE
        u128 z = (u128)x * y.x;
        u64 w = (z & mod) + (z >> mod_pow);
        if (w > mod) w -= mod;
        return w;
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
ffe operator+ (s64 x, ffe y) { return ffe{x} + y; }
ffe operator- (s64 x, ffe y) { return ffe{x} - y; }
ffe operator* (s64 x, ffe y) { return ffe{x} * y; }
ffe operator/ (s64 x, ffe y) { return ffe{x} / y; }

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
    Polynomial degree_reduced() const { return {0, a+b, c}; }

    bool is_linear() { return a.x == 0; }
    bool is_constant() { return a.x == 0 and b.x == 0; }
};

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
}
