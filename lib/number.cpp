
//#import <math.h>

Array_t<u8> _number_error(u8 code) {
    switch (code) {
    case 1: return "String is empty"_arr;
    case 2: return "Invalid character"_arr;
    case 3: return "Out of range (too low)"_arr;
    case 4: return "Out of range (too high)"_arr;
    case 5: return "Unexpected end of input"_arr;
    case 6: return "Value too close to zero"_arr;
    case 7: return "Extra characters"_arr;
    case 8: return "Expected an integer"_arr;
    default: assert_false;
    };
}

struct Number_scientific {
    enum Type: u8 {
        NORMAL, T_INFINITY, T_NAN
    };
    
    u8 type;
    bool sign;
    u64 m; // mantissa
    s32 e; // exponent
};

struct Number_parse_args {
    enum Flags: u8 {
        ALLOW_INFINITY = 1,
        ALLOW_NAN = 2,
        INTEGER = 4,
        UNSIGNED = 8,
    };
    u8 flags;
    u8 type = -1;

    template <typename T> void settype();
};
template <> void Number_parse_args::settype<u8 >() { flags |= UNSIGNED | INTEGER; type = 0; }
template <> void Number_parse_args::settype<s8 >() { flags |=            INTEGER; type = 1; }
template <> void Number_parse_args::settype<u16>() { flags |= UNSIGNED | INTEGER; type = 2; }
template <> void Number_parse_args::settype<s16>() { flags |=            INTEGER; type = 3; }
template <> void Number_parse_args::settype<u32>() { flags |= UNSIGNED | INTEGER; type = 4; }
template <> void Number_parse_args::settype<s32>() { flags |=            INTEGER; type = 5; }
template <> void Number_parse_args::settype<u64>() { flags |= UNSIGNED | INTEGER; type = 6; }
template <> void Number_parse_args::settype<s64>() { flags |=            INTEGER; type = 7; }
template <> void Number_parse_args::settype<float>()  { type = 8; }
template <> void Number_parse_args::settype<double>() { type = 9; }

// Converts a string into a number. This function returns imprecise results!
u8 _number_parse_helper(Array_t<u8> str, Number_scientific* into, u8 flags) {
    assert(into);
    if (str.size == 0) return 1;

    bool sign = false;
    s64 i = 0;
    while (i < str.size and (str[i] == '-' or str[i] == '+')) {
        sign ^= str[i] == '-';
        ++i;
    }
    if (i == str.size) return 5;

    auto cmp_ci = [&str, &i](Array_t<u8> s) {
        if (i + s.size > str.size) return false;
        for (s64 j = 0; j < s.size; ++j) {
            if (str[i + j] != s[j] and str[i+j] != s[j] + 'A' - 'a') return false;
        }
        i += s.size;
        return true;
    };

    if (flags & Number_parse_args::ALLOW_INFINITY) {
        if (cmp_ci("infty"_arr) or cmp_ci("infinity"_arr) or cmp_ci("inf"_arr)) {
            if (i < str.size) return 7;
            *into = {Number_scientific::T_INFINITY, sign, 0, 0};
            return 0;
        }
    }
    if (flags & Number_parse_args::ALLOW_NAN) {
        if (cmp_ci("nan"_arr)) {
            if (i < str.size) return 7;
            *into = {Number_scientific::T_NAN, sign, 0, 0};
            return 0;
        }
    }
    
    u64 base = 10;
    if (str[i] == '0' and i + 1 < str.size) {
        ++i;
        if (str[i] == 'x' or str[i] == 'X') {
            base = 16; ++i;
        } else if (str[i] == 'b' or str[i] == 'B') {
            base = 2; ++i;
        } else if ('0' <= str[i] and str[i] <= '9') {
            base = 8;
        } else {
            // nothing
        }
    }
    if (i == str.size) return 5;

    double base_log2;
    switch (base) {
    case 10: base_log2 = 3.3219280948873626; break;
    case  2: base_log2 = 1.0; break;
    case  8: base_log2 = 3.0; break;
    case 16: base_log2 = 4.0; break;
    default: assert_false;
    }

    u64 m = 0;
    int exp = 0;
    bool overflow = false;
    bool do_exp = false;
    bool do_frac = false;
    for (; i < str.size; ++i) {
        char c = str[i];
        u64 val = 0;
        if ('0' <= c and c <= '9') {
            val = c - '0';
        } else if (base == 16 and 'a' <= c and c <= 'z') {
            val = c - 'a' + 10;
        } else if (base == 16 and 'A' <= c and c <= 'Z') {
            val = c - 'A' + 10;
        } else if (base == 10 and (c == 'e' or c == 'E')) {
            do_exp = true; ++i; break;
        } else if (c == '.') {
            do_frac = true; ++i; break;
        } else {
            return 2;
        }
        if (val >= base) { return 2; }

        if (not overflow) {
            u64 tmp;
            if (__builtin_mul_overflow(m, base, &tmp)) {
                overflow = true;
            } else if (__builtin_add_overflow(tmp, val, &tmp)) {
                overflow = true;
            } else {
                m = tmp;
            }
        }
        
        if (overflow) {
            // If we are doing integers, this does not fit
            if (flags & Number_parse_args::INTEGER) return sign ? 3 : 4;

            // For floats, ignore the other digits
            if (__builtin_add_overflow(exp, 1, &exp)) {
                return sign ? 3 : 4;
            }
        }
    }
    overflow = false;

    if (do_frac) {
        for (; i < str.size; ++i) {
            char c = str[i];
            u64 val = 0;
            if ('0' <= c and c <= '9') {
                val = c - '0';
            } else if (base == 16 and 'a' <= c and c <= 'z') {
                val = c - 'a' + 10;
            } else if (base == 16 and 'A' <= c and c <= 'Z') {
                val = c - 'A' + 10;
            } else if (base == 10 and (c == 'e' or c == 'E')) {
                do_exp = true; ++i; break;
            } else {
                return 2;
            }
            if (val >= base) { return 2; }

            if (not overflow) {
                u64 tmp_m;
                int tmp_exp;
                overflow |= __builtin_mul_overflow(m, base, &tmp_m);
                overflow |= __builtin_add_overflow(tmp_m, val, &tmp_m);
                overflow |= __builtin_sub_overflow(exp, 1, &tmp_exp);
                if (not overflow) {
                    m = tmp_m;
                    exp = tmp_exp;
                }
            }
            
            if (overflow) {
                // Unless we are parsing an integer, any leftover fractional part can be ignored. If
                // we are, we should still accept a long fractional part of 0.
                if (val != 0 and (flags & Number_parse_args::INTEGER)) {
                    return 8;
                }
            }
        }
    }
    overflow = false;
    
    if (do_exp) {
        bool exp_sign = false;
        u64 exp_val = 0;
        while (i < str.size and (str[i] == '-' or str[i] == '+')) {
            exp_sign ^= str[i] == '-';
            ++i;
        }
        if (i == str.size) return 5;
    
        for (; i < str.size; ++i) {
            char c = str[i];
            u64 val = 0;
            if ('0' <= c and c <= '9') {
                val = c - '0';
            } else {
                return 2;
            }

            if (__builtin_mul_overflow(exp_val, 10, &exp_val)) {
                overflow = true; break;
            } else if (__builtin_add_overflow(exp_val, val, &exp_val)) {
                overflow = true; break;
            }
        }

        if (exp_sign) {
            if (__builtin_sub_overflow(exp, exp_val, &exp)) overflow = true;    
        } else {
            if (__builtin_add_overflow(exp, exp_val, &exp)) overflow = true;    
        }

        if (overflow) return exp_sign ? (sign ? 3 : 4) : 6;
    }

    // Convert exponent into base 2
    // TODO: Implement correct rounding
    s32 exp_;
    if (m == 0 or exp == 0) {
        exp_ = 0;
    } else if (exp > 0 and base_log2 * (double)exp < __builtin_clzll(m)) {
        // If the number is a 64-bit integer, represent it directly
        for (s32 i = 0; i < exp; ++i) {
            m *= 10;
        }
        exp_ = 0;
    } else if (base == 10) {
        u64 shift = __builtin_clzll(m);
        m <<= shift;
        // roughly exp * base_log2 > S32_MAX or exp * base_log2 < S32_MIN
        if (exp > 646456991 or exp < -646456992) {
            return exp < 0 ? 6 : (sign ? 3: 4);
        }
        long double base_log2_l = 3.3219280948873623478l;
        exp_ = (s32)(ceill(exp * base_log2_l));

        long double m_ld = (long double)m;
        if (exp > 0) {
            long double d = 10.l;
            u64 i = (u64)exp;
            while (i) {
                if (i & 1) m_ld *= d;
                d *= d;
                i >>= 1;
            }
        } else {
            long double d = 10.l;
            u64 i = (u64)-exp;
            while (i) {
                if (i & 1) m_ld /= d;
                d *= d;
                i >>= 1;
            }
        }
        if (m_ld == INFINITY or m_ld == -INFINITY or m_ld == 0) {
            return exp < 0 ? 6 : (sign ? 3: 4);
        }

        m = (u64)(ldexpl(m_ld, -exp_));
        exp_ -= shift;
    
    } else {
        switch (base) {
        case 2: exp_ = exp; break;
        case 8: exp_ = exp * 3; break;
        case 16: exp_ = exp * 4; break;
        default: assert_false;
        }
    }

    // Shift mantissa to the right
    if (m != 0) {
        exp_ += __builtin_ctzll(m);
        m >>= __builtin_ctzll(m);
    }
    
    if (flags & Number_parse_args::INTEGER) {
        if (exp_ != 0) {
            assert(m != 0);
            if (exp_ > 0 and __builtin_clzll(m) >= exp_) {
                m <<= exp_;
                exp_ = 0;
            } else {
                return 8;
            }
        }
    }

    *into = {Number_scientific::NORMAL, sign, m, exp_};
    return 0;
}

u8 _number_pack_float(Number_scientific n, float* into) {
    // Shift to the left
    if (n.m != 0) {
        n.e -=  __builtin_clzll(n.m);
        n.m <<= __builtin_clzll(n.m);
    }
    
    // We interpret n.m as a real in [0, 2)
    n.e += 63;
    assert(n.m == 0 or (n.m & (1ull << 63)));

    union {
        u32 d = 0;
        float result;
    };

    // sign
    d ^= ((u32)n.sign << 31);
    
    if (n.type == Number_scientific::T_NAN) {
        d = 0x7fc00000ull;
    } else if (n.type == Number_scientific::T_INFINITY) {
        d |= 0x7f800000ull;
    } else if (n.type == Number_scientific::NORMAL)  {
        // Take care of the normal-denormal cutoff
        if (n.e == -127) {
            if (n.m >= 0xffffff0000000000ull) {
                n.m = 1ull << 63;
                n.e += 1;
            }
        } else if (n.e <= -150) {
            if (n.e == -150 and n.m > (1ull << 63)) {
                n.m = 1ull << 63;
                n.e += 1;
            } else {
                n.m = 0;
                n.e = 0;
            }
        }
        
        if (n.m == 0) {
            // nothing, mantissa and exponent are already zero
        } else if ((n.e > -127 and n.e < 127) or (n.e == 127 and n.m < 0xffffff7000000000ull)) {
            // normalized
            u64 m_ = n.m >> 40;
            s64 exp_ = n.e;
            u64 round = n.m & 0xffffffffffull;

            if (not (round & 0x8000000000ull)) {
                // round down
            } else if (round & 0x7fffffffffull) {
                // round up
                m_ += 1;
            } else {
                assert(round == 0x8000000000ull);
                // round towards even
                m_ += m_ & 1;
            }
            if (m_ & (1ull << 24)) {
                m_ >>= 1;
                exp_ += 1;
            }

            assert(m_ < (1ull << 25) and exp_ >= -126 and exp_ <= 1027);
            d |= (m_ & ~(1ull << 23));
            d |= (u64)(exp_ + 127) << 23;
        } else if (n.e >= -149 and n.e <= -127) {
            // denormalized
            u64 shift = 41 - (127 + n.e);
            u64 m_ = n.m >> shift;
            u64 round = (n.m >> (shift - 41)) & 0xffffffffffull;

            if (not (round & 0x8000000000ull)) {
                // round down
            } else if (round & 0x7fffffffffull) {
                // round up
                m_ += 1;
            } else {
                assert(round == 0x8000000000ull);
                // round towards even
                m_ += m_ & 1;
            }
            
            assert(m_ < (1ull << 24));
            d |= m_;
            // exponent already 0
        } else {
            return n.e < 0 ? 6 : (n.sign ? 3 : 4);
        }
    } else {
        assert_false;
    }

    *into = result;
    return 0;
}

u8 _number_pack_double(Number_scientific n, double* into) {
    // Shift to the left
    if (n.m != 0) {
        n.e -=  __builtin_clzll(n.m);
        n.m <<= __builtin_clzll(n.m);
    }
    
    // We interpret n.m as a real in [0, 2)
    n.e += 63;
    assert(n.m == 0 or (n.m & (1ull << 63)));

    union {
        u64 d = 0;
        double result;
    };

    // sign
    d ^= ((u64)n.sign << 63);
    
    if (n.type == Number_scientific::T_NAN) {
        d = 0x7ff8000000000000ull;
    } else if (n.type == Number_scientific::T_INFINITY) {
        d |= 0x7ff0000000000000ull;
    } else if (n.type == Number_scientific::NORMAL)  {
        // Take care of the normal-denormal cutoff
        if (n.e == -1023) {
            if (n.m >= 0xfffffffffffff800ull) {
                n.m = 1ull << 63;
                n.e += 1;
            }
        } else if (n.e <= -1075) {
            if (n.e == -1075 and n.m > (1ull << 63)) {
                n.m = 1ull << 63;
                n.e += 1;
            } else {
                n.m = 0;
                n.e = 0;
            }
        }
        
        if (n.m == 0) {
            // nothing, mantissa and exponent are already zero
        } else if ((n.e > -1023 and n.e < 1023) or (n.e == 1023 and n.m < 0xfffffffffffffc00ull)) {
            // normalized
            u64 m_ = n.m >> 11;
            s64 exp_ = n.e;
            u64 round = n.m & 0x7ffull;

            if (not (round & 0x400)) {
                // round down
            } else if (round & 0x3ff) {
                // round up
                m_ += 1;
            } else {
                assert(round == 0x400);
                // round towards even
                m_ += m_ & 1;
            }

            if (m_ & (1ull << 53ull)) {
                m_ >>= 1;
                exp_ += 1;
            }

            assert(m_ < (1ull << 54) and exp_ >= -1022 and exp_ <= 1023);
            d |= (m_ & ~(1ull << 52));
            d |= (u64)(exp_ + 1023) << 52;
        } else if (n.e >= -1074 and n.e <= -1023) {
            // denormalized
            u64 shift = 12 - (1023 + n.e);
            u64 m_ = n.m >> shift;
            u64 round = (n.m >> (shift - 12)) & 0xfffull;

            if (not (round & 0x800)) {
                // round down
            } else if (round & 0x7ff) {
                // round up
                m_ += 1;
            } else {
                assert(round == 0x800);
                // round towards even
                m_ += m_ & 1;
            }

            assert(m_ < (1ull << 53));
            d |= m_;
            // exponent already 0
        } else {
            return n.e < 0 ? 6 : (n.sign ? 3 : 4);
        }
    } else {
        assert_false;
    }

    *into = result;
    return 0;
}

u8 _number_pack_int(Number_scientific n, Number_parse_args args, void* into) {
    u8 bits[] = {8, 8, 16, 16, 32, 32, 64, 64};

    if ((args.flags & Number_parse_args::UNSIGNED) and n.sign and n.m) {
        return 3;
    }
    
    if (not n.sign) {
        u64 max = (u64)-1 >> (64 - bits[args.type]);
        if (~args.flags & Number_parse_args::UNSIGNED) {
            max >>= 1;
        }
        max >>= n.e;
        if (max < n.m) return 4;
    } else {
        u64 max = 1ull << (bits[args.type] - 1);
        max >>= n.e;
        if (max < n.m) return 3;
    }

    u64 x = n.m << n.e;
    if (n.sign) x = -x;
    u8 bytes[] = {1, 1, 2, 2, 4, 4, 8, 8};
    memcpy(into, &x, bytes[args.type]);
        
    return 0;
}

constexpr static u64 NUMBER_ERR_BASE = 221205000;

void _number_parse_ex(Array_t<u8> str, Status* status, Number_parse_args args, void* into) {
    Number_scientific n;
    u8 code = _number_parse_helper(str, &n, args.flags);

    if (code) {
        // nothing
    } else if (args.type < 8) {
        code = _number_pack_int(n, args, into);
    } else if (args.type == 8) {
        code = _number_pack_float(n, (float*)into);
    } else if (args.type == 9) {
        code = _number_pack_double(n, (double*)into);
    }
    
    if (code) {
        status->code = NUMBER_ERR_BASE + code;
        array_printa(&status->error_buf, "%\nwhile parsing '%'\n", _number_error(code), str);
    }
}

/**
 * General number parsing routine. The string str is parsed (specifics depend on the value of
 * flags) and the result is returned. If an error occured, status is updated accordingly.
 *
 * The currently supported data types are 8/16/32/64-bit signed/unsigned integers and 32/64-bit
 * IEEE-754 floating point numbers.
 *
 * When parsing integers, currently no flags may be specified. The value will be represented
 * exactly, if possible, else an error will be raised. Only the value must be an integer, it may be
 * written in a form usually used for floating point numbers (e.g. 3.14159e5 is a valid).
 * 
 * When parsing floating point numbers, the flags ALLOW_INFINITY and ALLOW_NAN are allowed. The
 * enable parsing of the special values infinity and NaN, respectively. Parsing a floating point
 * number is not exact, of course. However, THIS FUNCTION IS NOT GUARATEED TO ROUND CORRECTLY in
 * general. This means that it is possible for the result to be off-by-one.  Empirically,
 * round-trips (converting the number to a string with enough digits and then back) work without
 * fault, and parsing of random strings is wrong only ~0.00067% of the time for 64-bit floats, and
 * ~0.00023% for 32-bit floats.
 *
 * The following formats are supported (all matching is case-insensitive):
 *   [+-]*(?=.)[0-9]*(\.[0-9]*)?(e[+-]*[0-9]+)?
 *     Base-10 number with optional fractional part and optional exponent.
 *   [+-]*0b(?=.)[01]*(\.[01]*)?
 *     Base-2 number with optional fractional part
 *   [+-]*0(?=.)[0-7]*(\.[0-7]*)?
 *     Base-8 number with optional fractional part
 *   [+-]*0x(?=.)[0-9a-f]*(\.[0-9a-f]*)?
 *     Base-16 number with optional fractional part
 *   [+-]*(inf|infty|infinity)
 *     Infinity (for floating point values only, ALLOW_INFINITY flag must be set)
 *   [+-]*nan
 *     (quiet) NaN (for floating point values only, ALLOW_NAN flag must be set)
 *
 * Note that the (?=.) matches everything that is followed by at least one character, i.e. that is
 * not at the end of the string. To put it differently, the base specifier, either ("", "0b", "0" or
 * "0x") must not be followed by the end of the string.
 */
template <typename T>
T number_parse(Array_t<u8> str, Status* status=nullptr, u8 flags=0) {
    if (os_status_initp(&status)) return {};
    
    Number_parse_args args {flags};
    args.settype<T>();
    T result {};
    _number_parse_ex(str, status, args, &result);
    return result;
}
