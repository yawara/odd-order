/* BG App.C Problem 1 — trace-obstruction certificate search in GF(3^N).
 *
 * Companion to notes/meta/gap/verify_trace_obstruction.g.  The GAP script settles
 * q <= 31; for q = 41 the birthday search needs ~10^9 evaluations of
 *
 *     D(p) = p^E - (p-1)^E ,   p in T = { p : p and p-1 both nonzero squares },
 *
 * which GAP cannot reach (it runs at ~1 ms/sample).  This is the same search in C.
 *
 * WHAT IT LOOKS FOR (see notes/bg/appC_problem1_partial_resolution.md):
 *   a collision D(p) = D(r), p != r in T, whose difference delta = p^E - r^E is a
 *   square, and whose S-value S = ((r-1)^{E^2} - r^{E^2}) * (delta^{-1})^E has
 *   non-zero absolute trace.  ONE such collision refutes hypothesis (B) for that q
 *   (Lean: OddOrder.BG.AppC.Problem1.false_of_collisionPair_trace_ne_zero).
 *
 * FIELD MODEL.  GF(3^N) = GF(3)[x]/(x^N + 2x^K + 1) with the Conway polynomial
 * (GAP: ConwayPolynomial(3,N)); all three N we need give trinomials, so
 * x^N = -2x^K - 1 = x^K + 2 and reduction is one shift-and-add pass.  The model is
 * irrelevant to the *answer* (isomorphic fields), so no cross-model matching with
 * GAP is needed — only model-independent invariants are compared in the self-test.
 *
 * REPRESENTATION.  Bit-sliced GF(3): a field element is two 64-bit planes (m, s)
 * holding N trits, with 0 -> (0,0), 1 -> (1,0), 2 -> (1,1) per bit position
 * (m = "non-zero", s = "equals two"; s is kept 0 wherever m is 0).
 *
 * Build:  cc -O3 -march=native -pthread -o gf3_collision gf3_collision.c
 * Usage:  ./gf3_collision selftest
 *         ./gf3_collision search <N> <K> <E-hi> <E-lo> <threads> <seconds> <dpbits>
 *           E = E-hi * 2^64 + E-lo is the *odd* representative of the exotic exponent
 *           (GAP prints it as "Eodd").  <dpbits> sets the distinguished-point density
 *           theta = 2^-dpbits; it must be about half of log2 of the search space
 *           |D(T)|/q ~ 3^N/(4N), i.e. ~7 for N=13, ~13 for N=19, ~29 for N=41.
 *           Too large and walks never reach a distinguished point.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

typedef unsigned __int128 u128;

/* ------------------------------------------------------------------ field */

static int N;              /* extension degree */
static int K;              /* middle exponent of the trinomial x^N + 2x^K + 1 */
static uint64_t FMASK;     /* mask of the N low bits */

typedef struct { uint64_t m, s; } fe;
typedef struct { u128 m, s; } fe2;

static inline fe fe_zero(void) { fe z = {0, 0}; return z; }

static inline fe fe_add(fe a, fe b) {
  uint64_t both = a.m & b.m;
  uint64_t d = a.s ^ b.s;
  uint64_t m = (a.m ^ b.m) | (both & ~d);
  uint64_t base = a.s | b.s;
  fe z = {m, m & (base ^ both)};
  return z;
}

static inline fe fe_neg(fe a) { fe z = {a.m, a.s ^ a.m}; return z; }
static inline fe fe_sub(fe a, fe b) { return fe_add(a, fe_neg(b)); }
static inline int fe_eq(fe a, fe b) { return a.m == b.m && a.s == b.s; }
static inline int fe_is_zero(fe a) { return a.m == 0; }

static inline fe2 fe2_add(fe2 a, fe2 b) {
  u128 both = a.m & b.m;
  u128 d = a.s ^ b.s;
  u128 m = (a.m ^ b.m) | (both & ~d);
  u128 base = a.s | b.s;
  fe2 z = {m, m & (base ^ both)};
  return z;
}

/* reduce a product of degree <= 2N-2 modulo x^N + 2x^K + 1, i.e. x^N = x^K + 2 */
static fe fe_reduce(fe2 p) {
  for (;;) {
    u128 hi_m = p.m >> N, hi_s = p.s >> N;
    if (hi_m == 0) break;
    fe2 lo = {p.m & (((u128)1 << N) - 1), p.s & (((u128)1 << N) - 1)};
    /* hi * (x^K + 2) = (hi << K) + 2*hi ; 2*hi = -hi */
    fe2 t1 = {hi_m << K, hi_s << K};
    fe2 t2 = {hi_m, hi_s ^ hi_m};
    p = fe2_add(lo, fe2_add(t1, t2));
  }
  fe z = {(uint64_t)p.m, (uint64_t)p.s};
  return z;
}

static fe fe_mul(fe a, fe b) {
  fe2 acc = {0, 0};
  u128 am = a.m, as = a.s;
  for (int i = 0; i < N; i++) {
    uint64_t bm = (b.m >> i) & 1u;
    if (bm) {
      uint64_t bs = (b.s >> i) & 1u;
      u128 sm = bs ? (as ^ am) : as; /* multiply a by 1 or by 2 (= negate) */
      fe2 t = {am << i, sm << i};
      acc = fe2_add(acc, t);
    }
  }
  return fe_reduce(acc);
}

/* x^{3i} mod f for i < N, used to cube by table lookup (cubing is GF(3)-linear) */
static fe cube_tab[64];

static fe fe_cube_slow(fe a) { return fe_mul(fe_mul(a, a), a); }

static void build_cube_table(void) {
  fe x = {2, 0}; /* x */
  for (int i = 0; i < N; i++) {
    fe e = {1, 0}; /* 1 */
    for (int j = 0; j < 3 * i; j++) e = fe_mul(e, x);
    cube_tab[i] = e;
  }
}

static inline fe fe_cube(fe a) {
  fe acc = fe_zero();
  for (int i = 0; i < N; i++) {
    if ((a.m >> i) & 1u) {
      fe t = cube_tab[i];
      if ((a.s >> i) & 1u) t = fe_neg(t);
      acc = fe_add(acc, t);
    }
  }
  return acc;
}

static fe fe_pow_u128(fe a, u128 e) {
  fe r = {1, 0};
  while (e) {
    if (e & 1) r = fe_mul(r, a);
    a = fe_mul(a, a);
    e >>= 1;
  }
  return r;
}

static fe fe_inv(fe a) { /* a^{3^N - 2} */
  u128 q = 1;
  for (int i = 0; i < N; i++) q *= 3;
  return fe_pow_u128(a, q - 2);
}

static fe fe_trace(fe a) { /* sum of the N Frobenius conjugates */
  fe acc = fe_zero(), y = a;
  for (int i = 0; i < N; i++) { acc = fe_add(acc, y); y = fe_cube(y); }
  return acc;
}

static int fe_is_square(fe a) { /* a^{(3^N-1)/2} == 1 */
  u128 q = 1;
  for (int i = 0; i < N; i++) q *= 3;
  fe r = fe_pow_u128(a, (q - 1) / 2);
  return r.m == 1 && r.s == 0;
}

/* canonical representative of the Frobenius orbit: lexicographic minimum */
static inline fe fe_canon(fe a) {
  fe best = a, y = a;
  for (int i = 1; i < N; i++) {
    y = fe_cube(y);
    if (y.m < best.m || (y.m == best.m && y.s < best.s)) best = y;
  }
  return best;
}

/* --------------------------------------------------------------- problem */

static u128 EXP_E;   /* odd representative of the exotic exponent */
static u128 EXP_E2;  /* E^2 mod (3^N - 1) */

/* p = (u + u^{-1})^2 lies in T with p - 1 = (u - u^{-1})^2, for u^2 != 1 */
static int paley_point(fe u, fe *p, fe *pm1) {
  if (fe_is_zero(u)) return 0;
  fe ui = fe_inv(u);
  fe a = fe_add(u, ui), b = fe_sub(u, ui);
  if (fe_is_zero(a) || fe_is_zero(b)) return 0;
  *p = fe_mul(a, a);
  *pm1 = fe_mul(b, b);
  return 1;
}

/* D(p) = p^E - (p-1)^E */
static fe Dval(fe p, fe pm1) {
  return fe_sub(fe_pow_u128(p, EXP_E), fe_pow_u128(pm1, EXP_E));
}

/* ------------------------------------------------------------- self test */

static void set_field(int n, int k) {
  N = n; K = k; FMASK = (n == 64) ? ~0ull : ((1ull << n) - 1);
  build_cube_table();
}

static uint64_t rng_state;
static inline uint64_t rng(void) {
  rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
  return rng_state;
}

static fe fe_random(void) {
  uint64_t m = rng() & FMASK;
  uint64_t s = rng() & m;
  fe z = {m, s};
  return z;
}

static int selftest_field(int n, int k) {
  set_field(n, k);
  u128 q = 1; for (int i = 0; i < N; i++) q *= 3;
  int fails = 0;
  rng_state = 0x1234567 + n;
  for (int t = 0; t < 2000; t++) {
    fe a = fe_random(), b = fe_random(), c = fe_random();
    /* ring axioms */
    if (!fe_eq(fe_add(a, b), fe_add(b, a))) { fails++; break; }
    if (!fe_eq(fe_mul(a, b), fe_mul(b, a))) { fails++; break; }
    if (!fe_eq(fe_mul(a, fe_add(b, c)), fe_add(fe_mul(a, b), fe_mul(a, c)))) { fails++; break; }
    if (!fe_eq(fe_add(a, fe_neg(a)), fe_zero())) { fails++; break; }
    /* Frobenius */
    if (!fe_eq(fe_cube(a), fe_cube_slow(a))) { fails++; break; }
    if (!fe_eq(fe_cube(fe_add(a, b)), fe_add(fe_cube(a), fe_cube(b)))) { fails++; break; }
    /* field: a^{3^N} = a, and a != 0 has an inverse */
    if (!fe_eq(fe_pow_u128(a, q), a)) { fails++; break; }
    if (!fe_is_zero(a)) {
      fe o = {1, 0};
      if (!fe_eq(fe_mul(a, fe_inv(a)), o)) { fails++; break; }
    }
    /* trace lands in the prime field: Tr(a)^3 = Tr(a) */
    fe tr = fe_trace(a);
    if (!fe_eq(fe_cube(tr), tr)) { fails++; break; }
  }
  printf("  GF(3^%d) (x^%d + 2x^%d + 1): %s\n", n, n, k, fails ? "FAIL" : "ok");
  return fails;
}

/* exhaustive fibre census of D on T; only meaningful for tiny N */
static void census(int n, int k, u128 e) {
  set_field(n, k);
  EXP_E = e;
  u128 q = 1; for (int i = 0; i < N; i++) q *= 3;
  long qq = (long)q;
  fe *Tp = malloc(sizeof(fe) * qq), *Tm = malloc(sizeof(fe) * qq);
  fe *Dv = malloc(sizeof(fe) * qq);
  long nt = 0;
  for (long idx = 0; idx < qq; idx++) {
    /* enumerate field elements by base-3 digits of idx */
    fe u = fe_zero();
    long r = idx;
    for (int i = 0; i < N; i++) {
      int d = r % 3; r /= 3;
      if (d) { u.m |= 1ull << i; if (d == 2) u.s |= 1ull << i; }
    }
    if (fe_is_zero(u) || !fe_is_square(u) || !fe_is_square(fe_sub(u, (fe){1, 0}))) continue;
    Tp[nt] = u; Tm[nt] = fe_sub(u, (fe){1, 0});
    Dv[nt] = Dval(Tp[nt], Tm[nt]);
    nt++;
  }
  /* fibre sizes */
  long *cnt = calloc(nt, sizeof(long));
  long pairs = 0;
  for (long i = 0; i < nt; i++)
    for (long j = i + 1; j < nt; j++)
      if (fe_eq(Dv[i], Dv[j])) { cnt[i]++; cnt[j]++; pairs++; }
  long f2 = 0, f3 = 0, f4 = 0;
  for (long i = 0; i < nt; i++) { if (cnt[i] == 1) f2++; else if (cnt[i] == 2) f3++; else if (cnt[i] >= 3) f4++; }
  printf("  N=%d e=%llu : |T|=%ld  collision pairs=%ld  (members of fibres of size 2/3/>=4: %ld/%ld/%ld)\n",
         n, (unsigned long long)e, nt, pairs, f2, f3, f4);
  free(Tp); free(Tm); free(Dv); free(cnt);
}

/* --------------------------------------------------------------- search */

/* Distinguished-point parallel collision search (van Oorschot-Wiener).
 * Walk:  u  ->  H(canon(D(p(u))))  on F^x, with H a cheap bijection-ish map.
 * A collision of the walk gives canon(D(p(u1))) = canon(D(p(u2))); rotating one
 * side by Frobenius turns it into an exact collision D(p1) = D(p2).           */

static int DP_BITS = 20;
#define TAB_BITS 22
#define TAB_SIZE (1u << TAB_BITS)

typedef struct { fe dp; fe start; uint64_t len; int used; } dprec;

static dprec *table;
static pthread_mutex_t tab_lock = PTHREAD_MUTEX_INITIALIZER;
static volatile int found_decisive = 0;
static volatile long total_steps = 0;
static double deadline;

static double now(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline uint64_t mix(uint64_t z) {
  z += 0x9e3779b97f4a7c15ull;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}

/* one walk step: u -> next u, and report the canonical D-value */
static inline int walk(fe u, fe *next, fe *cval) {
  fe p, pm1;
  if (!paley_point(u, &p, &pm1)) return 0;
  fe d = Dval(p, pm1);
  if (fe_is_zero(d)) return 0;
  *cval = fe_canon(d);
  uint64_t h = mix(cval->m ^ (cval->s * 0x9e3779b97f4a7c15ull));
  fe nu = {h & FMASK, 0};
  nu.s = mix(h) & nu.m;
  if (fe_is_zero(nu)) nu.m = 1;
  *next = nu;
  return 1;
}

/* Given two starts whose walks meet, back up to the exact colliding pair. */
static int retrace(fe s1, uint64_t l1, fe s2, uint64_t l2, fe *u1, fe *u2) {
  fe a = s1, b = s2, na, nb, ca, cb;
  while (l1 > l2) { if (!walk(a, &na, &ca)) return 0; a = na; l1--; }
  while (l2 > l1) { if (!walk(b, &nb, &cb)) return 0; b = nb; l2--; }
  for (uint64_t i = 0; i < l1; i++) {
    if (!walk(a, &na, &ca)) return 0;
    if (!walk(b, &nb, &cb)) return 0;
    if (fe_eq(na, nb)) { *u1 = a; *u2 = b; return !fe_eq(a, b); }
    a = na; b = nb;
  }
  return 0;
}

/* Test the collision candidate (u1,u2): rotate by Frobenius to align the
 * D-values exactly, require delta = p1^E - p2^E to be a square, and report the
 * trace of the S-value. */
static int test_pair(fe u1, fe u2) {
  fe p1, m1, p2, m2;
  if (!paley_point(u1, &p1, &m1) || !paley_point(u2, &p2, &m2)) return 0;
  fe d1 = Dval(p1, m1), d2 = Dval(p2, m2);
  int rot;
  for (rot = 0; rot < N; rot++) {
    if (fe_eq(d1, d2)) break;
    d2 = fe_cube(d2); p2 = fe_cube(p2); m2 = fe_cube(m2);
  }
  if (rot == N || fe_eq(p1, p2)) return 0;
  fe delta = fe_sub(fe_pow_u128(p1, EXP_E), fe_pow_u128(p2, EXP_E));
  if (fe_is_zero(delta) || !fe_is_square(delta)) return 0;
  fe Kp = fe_sub(fe_pow_u128(m2, EXP_E2), fe_pow_u128(p2, EXP_E2));
  fe S = fe_mul(Kp, fe_pow_u128(fe_inv(delta), EXP_E));
  fe tr = fe_trace(S);
  printf("COLLISION  delta square, Tr(S) = %s\n",
         fe_is_zero(tr) ? "0" : (tr.s & 1 ? "-1" : "+1"));
  fflush(stdout);
  return !fe_is_zero(tr);
}

typedef struct { int id; } targ;

static void *worker(void *v) {
  targ *t = (targ *)v;
  uint64_t local = 0x243F6A8885A308D3ull * (t->id + 1) + 0x13198A2E03707344ull;
  fe start, u, next, cval;
  uint64_t len = 0;
  const uint64_t maxlen = 20ull << DP_BITS;
  (void)maxlen;
  /* fresh start */
  local = mix(local); start.m = local & FMASK; local = mix(local);
  start.s = local & start.m; if (fe_is_zero(start)) start.m = 1;
  u = start;
  while (!found_decisive && now() < deadline) {
    for (int burst = 0; burst < 4096; burst++) {
      if (!walk(u, &next, &cval)) {
        local = mix(local); start.m = local & FMASK; local = mix(local);
        start.s = local & start.m; if (fe_is_zero(start)) start.m = 1;
        u = start; len = 0; continue;
      }
      u = next; len++;
      if ((mix(u.m ^ u.s) & ((1ull << DP_BITS) - 1)) == 0 || len > maxlen) {
        if (len <= maxlen) {
          uint64_t idx = mix(u.m * 3 + u.s) & (TAB_SIZE - 1);
          pthread_mutex_lock(&tab_lock);
          if (table[idx].used && fe_eq(table[idx].dp, u) &&
              !fe_eq(table[idx].start, start)) {
            fe s1 = table[idx].start; uint64_t l1 = table[idx].len;
            pthread_mutex_unlock(&tab_lock);
            fe a, b;
            if (retrace(s1, l1, start, len, &a, &b)) {
              if (test_pair(a, b)) found_decisive = 1;
            }
          } else {
            table[idx].used = 1; table[idx].dp = u;
            table[idx].start = start; table[idx].len = len;
            pthread_mutex_unlock(&tab_lock);
          }
        }
        local = mix(local); start.m = local & FMASK; local = mix(local);
        start.s = local & start.m; if (fe_is_zero(start)) start.m = 1;
        u = start; len = 0;
      }
    }
    __sync_fetch_and_add(&total_steps, 4096);
  }
  return NULL;
}

int main(int argc, char **argv) {
  if (argc >= 2 && strcmp(argv[1], "selftest") == 0) {
    printf("field self-test\n");
    int f = 0;
    f += selftest_field(7, 2);
    f += selftest_field(13, 1);
    f += selftest_field(41, 1);
    printf("exhaustive collision census on T (model-independent invariants)\n");
    census(7, 2, 151);
    census(7, 2, 941);
    return f ? 1 : 0;
  }
  if (argc < 9) {
    fprintf(stderr,
            "usage: %s search <N> <K> <E-hi> <E-lo> <threads> <seconds> <dpbits>\n", argv[0]);
    return 2;
  }
  int n = atoi(argv[2]), k = atoi(argv[3]);
  u128 ehi = (u128)strtoull(argv[4], NULL, 10);
  u128 elo = (u128)strtoull(argv[5], NULL, 10);
  int nthreads = atoi(argv[6]);
  double secs = atof(argv[7]);
  DP_BITS = atoi(argv[8]);
  set_field(n, k);
  EXP_E = (ehi << 64) | elo;
  u128 qm1 = 1; for (int i = 0; i < N; i++) qm1 *= 3; qm1 -= 1;
  EXP_E2 = (EXP_E % qm1) * (EXP_E % qm1) % qm1;
  table = calloc(TAB_SIZE, sizeof(dprec));
  deadline = now() + secs;
  double t0 = now();
  pthread_t *th = malloc(sizeof(pthread_t) * nthreads);
  targ *ta = malloc(sizeof(targ) * nthreads);
  for (int i = 0; i < nthreads; i++) { ta[i].id = i; pthread_create(&th[i], NULL, worker, &ta[i]); }
  for (int i = 0; i < nthreads; i++) pthread_join(th[i], NULL);
  double dt = now() - t0;
  printf("%s  steps=%ld  time=%.1fs  rate=%.3g steps/s\n",
         found_decisive ? "DECISIVE" : "no decisive collision found",
         total_steps, dt, total_steps / dt);
  return found_decisive ? 0 : 1;
}
