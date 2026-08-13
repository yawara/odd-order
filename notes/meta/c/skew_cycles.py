#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
skew_cycles.py -- census of the collision-free skew-pair calculus on GF(3^7).

Every p in T (p, p-1 both nonzero squares) satisfies, for all z in U:
    a(z) = b(-p^e z^e) d(K(p) z^{e^2}) b((p-1)^e z^e),   K(p) = (p-1)^{e^2} - p^{e^2}.
Hence every ordered pair (p, r) in T^2, p != r, gives the SKEW relation
    b(d0 z^e) d(K(p) z^{e^2}) b(-d1 z^e) = d(K(r) z^{e^2}),
    d0 = r^e - p^e,  d1 = (r-1)^e - (p-1)^e     (both nonzero).
Composition of skew relations (with the z -> t z rescaling freedom, t in U)
closes into a genuine two-layer conjugation relation (a "loop") iff the
product condition prod(d1_i) = prod(d0_i) holds, PLUS per-step sign
conditions chi(d1_i / d0_{i+1}) = 1 for the chaining rescalers.

k = 2 census: a 2-cycle needs rho_2 = rho_1^{-1} where rho := d1/d0, with
step conditions t2^e = d1_1/d0_2 in U and closing t1-free; the loop weights
are  X_tot = K(p1) + K(p2) * w,  Y_tot = K(r1) + K(r2) * w,  w = t2^{e^2},
after which the loop reads  b(d0_1 z^e) d(X_tot z^{e^2}) b(-d0_1 z^e)
= d(Y_tot z^{e^2}): a ConjPair in layers (1,2) with delta = d0_1.

We measure, for q = 7, both exotic e:
  1. the rho-distribution over all |T|(|T|-1) edges;
  2. #edges whose rho-inverse class is nonempty (2-cycle partner exists);
  3. among sampled valid 2-cycles (sign conditions checked), the fraction
     with (X_tot, Y_tot) != (0,0)  [the kill condition];
  4. cross-check: rho = 1 edges = collisions (delta0 = delta1 <=> D(p)=D(r)
     ... actually rho = 1 <=> d0 = d1 <=> collision in the D-sense).
"""
import os
import sys
import random
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, os.pardir, 'collision_impact')))
import collision_impact as ci

Q = 3 ** 7
N1 = Q - 1
HALF = N1 // 2
F7POLY = [1, 0, 2, 0, 0, 0, 0, 1]
E2OF = {151: 941, 941: 151}


def main():
    rng = random.Random(20260813)
    F = ci.Field(7, F7POLY)
    exp, log, add = F.exp, F.log, F.add_enc

    def is_sq(enc):
        return enc != 0 and log[enc] % 2 == 0

    def neg(enc):
        return add(enc, enc)

    def sub(x, y):
        return add(x, neg(y))

    one = 1
    # T = {p : p, p-1 both nonzero squares}
    T = [p for p in range(Q) if is_sq(p) and is_sq(sub(p, one))]
    print("q=7  |T| = %d" % len(T))
    assert len(T) == (Q - 3) // 4

    for E in [151, 941]:
        E2 = E2OF[E]
        pw = {}
        for enc in range(1, Q):
            pw[enc] = exp[log[enc] * E % N1]

        def powE(enc):
            return pw[enc]

        def powE2(enc):
            return exp[log[enc] * E2 % N1] if enc else 0

        # per point: p^e, (p-1)^e, K(p)
        pe = {}
        pme = {}
        K = {}
        for p in T:
            pe[p] = powE(p)
            pme[p] = powE(sub(p, one))
            K[p] = sub(powE2(sub(p, one)), powE2(p))
            assert K[p] != 0
        # edges: (p, r) ordered, p != r
        # rho(p,r) = d1/d0, log-form
        rho_ct = Counter()
        edges_by_rho = defaultdict(list)
        nedge = 0
        ncoll = 0
        for i, p in enumerate(T):
            for r in T:
                if r == p:
                    continue
                d0 = sub(pe[r], pe[p])
                d1 = sub(pme[r], pme[p])
                assert d0 != 0 and d1 != 0
                lrho = (log[d1] - log[d0]) % N1
                rho_ct[lrho] += 1
                if lrho == 0:
                    ncoll += 1
                nedge += 1
                if len(edges_by_rho[lrho]) < 400:
                    edges_by_rho[lrho].append((p, r, d0, d1))
        print("E=%d: edges %d, distinct rho %d (of %d possible), "
              "rho=1 edges (=collisions x2) %d" %
              (E, nedge, len(rho_ct), N1, ncoll))
        # 2-cycle partner availability
        have_inv = sum(1 for lr in rho_ct if (N1 - lr) % N1 in rho_ct)
        print("  rho classes with inverse class nonempty: %d / %d" %
              (have_inv, len(rho_ct)))
        # sample valid 2-cycles and test sign conditions + weights
        tried = 0
        signfail = 0
        ok = 0
        w_zero_both = 0
        w_zero_one = 0
        kills = 0
        seen_pairs = 0
        for lrho in list(rho_ct):
            linv = (N1 - lrho) % N1
            if linv not in edges_by_rho or not edges_by_rho[lrho]:
                continue
            # sample a few cross pairs
            for _ in range(3):
                p1, r1, d0a, d1a = edges_by_rho[lrho][rng.randrange(
                    len(edges_by_rho[lrho]))]
                p2, r2, d0b, d1b = edges_by_rho[linv][rng.randrange(
                    len(edges_by_rho[linv]))]
                # skip the degenerate exact-reversal loop (same unordered pair)
                if {p1, r1} == {p2, r2}:
                    continue
                seen_pairs += 1
                # chaining condition: t2^e = d1a/d0b must be a square (t2 in U);
                # closing: d1b * t2^e = d0a  <=> log identity (holds by rho)
                lt2e = (log[d1a] - log[d0b]) % N1
                tried += 1
                if lt2e % 2 != 0:
                    signfail += 1
                    continue
                # closing check
                assert (log[d1b] + lt2e) % N1 == log[d0a] % N1
                ok += 1
                # weights: w = t2^{e^2}; t2^e known -> t2 = (t2^e)^{e^2} since
                # e^3 = 1; so t2^{e^2} = (t2^e)^{e^2 * e^2} = (t2^e)^{e}
                # (e^4 = e). Check: (t2^e)^(e) has log lt2e * E.
                lw = lt2e * E % N1
                w = exp[lw]
                Xt = add(K[p1], (0 if K[p2] == 0 else
                                 exp[(log[K[p2]] + lw) % N1]))
                Yt = add(K[r1], (0 if K[r2] == 0 else
                                 exp[(log[K[r2]] + lw) % N1]))
                if Xt == 0 and Yt == 0:
                    w_zero_both += 1
                elif Xt == 0 or Yt == 0:
                    w_zero_one += 1   # K2-type kill (0 vs nonzero)
                    kills += 1
                else:
                    kills += 1
        print("  sampled cross 2-cycles: %d (tried %d, sign-blocked %d, "
              "valid %d)" % (seen_pairs, tried, signfail, ok))
        print("  weights: both-zero %d, one-zero %d, kills (any nonzero) "
              "%d / %d valid" % (w_zero_both, w_zero_one, kills, ok))


if __name__ == '__main__':
    main()
