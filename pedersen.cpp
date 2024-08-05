#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rand.h>

#define SEEDSIZE 16
#define SEC_PARA 61

BN_CTX *ctx_setup;
BIGNUM *p_param, *q_param, *g_param, *h_param, *s_param;

static int _seed_prng() {
	static int _prng_seeded = 0;
	if (_prng_seeded) return 0;
	if (RAND_load_file("/dev/random", SEEDSIZE)) {
		_prng_seeded = 1;
		return 0;
	}
	return 1;
}

// void setup_perdersen(BoolIO<NetIO> *ios, int party) {
// 	ctx_setup = BN_CTX_new();

// 	p_param = BN_new();
// 	BN_generate_prime_ex(p_param, SEC_PARA, 1);

// 	q_param = BN_new();
// 	BN_lshift1(q_param, p_param);

// 	g_param = BN_new();
// 	h_param = BN_new();
// 	BN_rand_range(g_param, q_param);

// 	if (party == BOB) {
// 		s_param = BN_new();
// 		BN_rand_range(s_param, q_param);
// 		BN_mod_exp(h_param, g_param, s_param, p_param, ctx);

// 		uint64_t *out = new uint64_t;
// 		BN_get_u64(h_param, out);
// 		ios->send_data(out, sizeof(uint64_t));
// 	} else {
// 		// uint64_t *in = new uint64_t;
// 		// ios->rec_data(in, sizeof(uint64_t));
// 		// BN_set_u64(h_param, in);
// 	}
// }

static void _commitment_calculate_c(BIGNUM*p, BIGNUM *g, BIGNUM *r, BIGNUM *h, BIGNUM *m, BIGNUM *c) {
	BN_CTX *ctx = BN_CTX_new();

	BIGNUM *gr = BN_new();
	BN_mod_exp(gr, g, r, p, ctx);	// gr = g^r (mod p)

	BIGNUM *hm = BN_new();
	BN_mod_exp(hm, h, m, p, ctx);	// hm = h^m (mod p)

	BN_mod_mul(c, gr, hm, p, ctx);	// c = g^r * h^m (mod p)

	// cleanup
	BN_free(gr);
	BN_free(hm);
	BN_CTX_free(ctx);
}

void commit(// BIGNUM *p, BIGNUM *q, BIGNUM *g, BIGNUM *h, // in: p, q, g, h - parameters given by Receiver
	BIGNUM *m,		// in: m - secret value/message
	BIGNUM *r, BIGNUM *c) {	// out: r, c - Receiver will store c, sender will store r for decomittment

	_seed_prng();

	BN_rand_range(r, q_param);		// r = random[0,q[

	_commitment_calculate_c(p_param, g_param, r, h_param, m, c);	// c = g^r * h^m (mod p)
}

/* returns 1 if c==c', 0 otherwise */
int decommit(BIGNUM *c,		 	//in: stored committed value
	// BIGNUM *p, BIGNUM *g, BIGNUM *h,//in: p, g, h - phase 1 parameters
	BIGNUM *r, BIGNUM *m,		//in: r, m - r and original value
	BIGNUM *cbis) {			//out: c', if needed outside -  ignored if NULL
	
	BIGNUM *c2 = BN_new();
	_commitment_calculate_c(p_param, g_param, r, h_param, m, c2);	// c2 = g^r * h^m (mod p)

	int checkPassed = BN_cmp(c,c2)==0;	// c == c' ?

	// if c2 value needed outside
	if (cbis!=NULL) BN_copy(cbis, c2);

	// cleanup
	BN_free(c2);

	return checkPassed;
}