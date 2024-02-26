
static inline u64 rotate_left(u64 x, int k) {
	return (x << k) | (x >> (64 - k));
}

struct Rng {
    u64 s[4] = {0x3769f2291d29a0dfull, 0x5bd9e4c279984390ull, 0x7c963c6debfd83e0ull, 0xf208cb4874fc1399ull};

    u64 u64_uni() {
        u64 result = rotate_left(s[1] * 5, 7) * 9;
        u64 t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1];
        s[1] ^= s[2]; s[0] ^= s[3];
        s[2] ^= t;
        s[3] = rotate_left(s[3], 45);
        return result;
    }

    float float_uni() {
        return u64_uni() / 18446744073709551616.f;
    }
    float float_normal() {
        // Ok, this is cheating.
        return float_uni() + float_uni() + float_uni() + float_uni()
             + float_uni() + float_uni() + float_uni() + float_uni()
             + float_uni() + float_uni() + float_uni() + float_uni() - 6.f;
    }
    u8 u8_normal() {
        u64 x = u64_uni();
        u64 r = 8;
        for (s64 i = 0; i < 16; ++i) {
            r += x & 0xf; x >>= 4;
        }
        return r;
    }

};
