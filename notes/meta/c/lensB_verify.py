#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
lensB_verify.py -- adversarial verification of the endgame BRANCH KILLS and
Frobenius quantization (Lens B) for the skew-pair calculus, GF(3^7).

Strategy: build SYNTHETIC kappa data that satisfies the master formula
    M(p,r) := lam_{chi(d0)} d0^e - lam_{chi(d1)} d1^e        (playing K(p))
for arbitrary (lam+, lam-), and check that every identity the note derives
FROM the master formula actually holds for this data.  This validates the
derivation chain independent of the conspiracy being false at q=7.

Checks:
  S0  basics: chi(-1) = -1, e odd, gcd(3e, Q-1) = 1, |T| = (Q-3)/4,
      T Frobenius-stable, d_i(p^3, r^3) = d_i(p,r)^3, K(p^3) = K(p)^3,
      chi cube-invariant, swap flips both components, swap preserves rho.
  S1  (EX)-consistency: master kappa-hat satisfies the exchange relation
      khat(rho,c) - khat(sig,c) = sig^e khat(rho, chi(sig)c)
                                  - rho^e khat(sig, chi(rho)c)
      for random realized (rho, sigma) and both c  (this is (EX) after
      multiplying by rho^e resp. dividing; also = the 4-term commutator
      weight vanishing).
  S2  branch (a) Delta = 0: with lam+ = lam- = lam, M(p,r) = lam(d0^e - d1^e)
      and M(r,p) = -M(p,r)  (e odd).  [3-point step is char-3 trivia.]
  S3  branch (b) difference identity: for ARBITRARY (lam+, lam-),
      M(p,r) - M(r,p) = (lam+ + lam-) (d0^e - d1^e); in particular
      Sigma-bar = 0 (lam- = -lam+) gives M(p,r) = M(r,p) exactly.
  S4  branch (c) quantization: M(p^3, r^3) - M(p,r)^3
      = mu_{chi(d0)} d0^{3e} - mu_{chi(d1)} d1^{3e},  mu_c := lam_c - lam_c^3;
      and lam in F_3 (9 pairs) gives M(p^3,r^3) = M(p,r)^3 exactly.
  S5  confinement collapse ingredients (verifier's sharpening):
      - x -> x^{3e} is a bijection, so rho^{3e} in {1,-1} <=> rho in {1,-1};
      - all-mixed rho = -1 world forces M = Sigma-bar * d0^e (checked on
        synthetic edges constructed with d1 = -d0);
      - real q=7 populations: same-sign (chi rho = +1) edges DO exist
        (so the lam^3 != lam branch dies at q=7 through the same-sign kill),
        rho = -1 edge count, and (+,-) out-degrees >> 2 for sampled p
        (F_3-candidate counting kill has huge slack).
  S6  F_3 candidate kill conditions on synthetic patterns: for
      (lam+,lam-) = (1,0): a (-,-) edge gives M = 0; a (+,-) edge pins
      d0^e = M; a (-,+) edge pins d1^e = -M  (checked by construction).
"""
import os
import sys
import math
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, os.pardir, 'collision_impact')))
import collision_impact as ci

Q = 3 ** 7
N1 = Q - 1
E2OF = {151: 941, 941: 151}
F7POLY = [1, 0, 2, 0, 0, 0, 0, 1]


def main():
    rng = random.Random(20260815)
    F = ci.Field(7, F7POLY)
    exp, log, add = F.exp, F.log, F.add_enc

    def neg(x):
        return add(x, x)

    def sub(x, y):
        return add(x, neg(y))

    def mul(x, y):
        if x == 0 or y == 0:
            return 0
        return exp[(log[x] + log[y]) % N1]

    def inv(x):
        return exp[(N1 - log[x]) % N1]

    def chi(x):
        return 1 if log[x] % 2 == 0 else -1

    def powg(x, k):
        return exp[(log[x] * k) % N1] if x else 0

    def cube(x):
        return powg(x, 3)

    T = [p for p in range(Q) if p and log[p] % 2 == 0
         and sub(p, 1) and log[sub(p, 1)] % 2 == 0]
    assert len(T) == (Q - 3) // 4 == 546, len(T)
    Tset = set(T)

    fails = []

    def ck(name, ok):
        tag = "OK " if ok else "FAIL"
        print("  [%s] %s" % (tag, name))
        if not ok:
            fails.append(name)

    # S0 basics (E-independent parts)
    print("S0 basics")
    ck("chi(-1) = -1", chi(neg(1)) == -1)
    ck("T Frobenius-stable", all(cube(p) in Tset for p in T))
    ck("chi cube-invariant", all(chi(cube(x)) == chi(x)
                                 for x in rng.sample(range(1, Q), 200)))

    for E in [151, 941]:
        E2 = E2OF[E]
        print("== E = %d (e^2 = %d) ==" % (E, E2))
        ck("e odd", E % 2 == 1)
        ck("e^3 = 1 mod Q-1", (E * E * E) % N1 == 1)
        ck("gcd(3e, Q-1) = 1", math.gcd(3 * E, N1) == 1)

        def powE(x):
            return powg(x, E)

        K = {p: sub(powg(sub(p, 1), E2), powg(p, E2)) for p in T}
        ck("K nonzero on T", all(K[p] for p in T))

        def edge(p, r):
            return (sub(powE(r), powE(p)),
                    sub(powg(sub(r, 1), E), sub(powg(sub(p, 1), E), 0)))

        def edge2(p, r):  # cleaner
            d0 = sub(powE(r), powE(p))
            d1 = sub(powE(sub(r, 1)), powE(sub(p, 1)))
            return d0, d1

        # S0 edge-level Frobenius facts
        ok_frob = True
        ok_swap = True
        for _ in range(300):
            p, r = rng.sample(T, 2)
            d0, d1 = edge2(p, r)
            d0c, d1c = edge2(cube(p), cube(r))
            if d0c != cube(d0) or d1c != cube(d1):
                ok_frob = False
            if K[cube(p)] != cube(K[p]):
                ok_frob = False
            d0s, d1s = edge2(r, p)
            if d0s != neg(d0) or d1s != neg(d1):
                ok_swap = False
            if chi(d0s) != -chi(d0) or chi(d1s) != -chi(d1):
                ok_swap = False
            # rho preserved under swap
            if (log[d1s] - log[d0s]) % N1 != (log[d1] - log[d0]) % N1:
                ok_swap = False
        ck("d_i(p^3,r^3) = d_i^3 and K(p^3) = K(p)^3", ok_frob)
        ck("swap: (d0,d1) -> (-d0,-d1), components flip, rho fixed", ok_swap)

        # ---- synthetic master data ----
        def make_M(lp, lm):
            lam = {1: lp, -1: lm}

            def M(p, r):
                d0, d1 = edge2(p, r)
                return sub(mul(lam[chi(d0)], powE(d0)),
                           mul(lam[chi(d1)], powE(d1)))
            return lam, M

        # S1: (EX) consistency of the master khat
        print("S1 (EX)-consistency of master form")
        for draw in range(3):
            lp = rng.randrange(1, Q)
            lm = rng.randrange(1, Q)
            lam = {1: lp, -1: lm}

            def khat(rho, c):
                return sub(lam[c], mul(lam[chi(rho) * c], powE(rho)))
            ok_ex = True
            ok_4t = True
            for _ in range(300):
                p1, r1 = rng.sample(T, 2)
                p2, r2 = rng.sample(T, 2)
                d0a, d1a = edge2(p1, r1)
                d0b, d1b = edge2(p2, r2)
                rho = mul(d1a, inv(d0a))
                sig = mul(d1b, inv(d0b))
                for c in (1, -1):
                    lhs = sub(khat(rho, c), khat(sig, c))
                    rhs = sub(mul(powE(sig), khat(rho, chi(sig) * c)),
                              mul(powE(rho), khat(sig, chi(rho) * c)))
                    if lhs != rhs:
                        ok_ex = False
                    # 4-term commutator-weight vanishing (X_tot/v^e = 0)
                    four = khat(rho, c)
                    four = add(four, mul(powE(rho), khat(sig, chi(rho) * c)))
                    four = sub(four, mul(powE(sig), khat(rho, chi(sig) * c)))
                    four = sub(four, khat(sig, c))
                    if four != 0:
                        ok_4t = False
            ck("draw %d: khat(rho,c)-khat(sig,c) = sig^e khat(rho,Xsig c)"
               " - rho^e khat(sig,Xrho c)" % draw, ok_ex)
            ck("draw %d: 4-term commutator weight vanishes under master"
               % draw, ok_4t)

        # S2: branch (a)
        print("S2 branch (a): Delta = 0")
        for draw in range(3):
            lamv = rng.randrange(1, Q)
            _, M = make_M(lamv, lamv)
            ok_form = True
            ok_anti = True
            for _ in range(300):
                p, r = rng.sample(T, 2)
                d0, d1 = edge2(p, r)
                if M(p, r) != mul(lamv, sub(powE(d0), powE(d1))):
                    ok_form = False
                if M(r, p) != neg(M(p, r)):
                    ok_anti = False
            ck("draw %d: M = lam (d0^e - d1^e) sign-free" % draw, ok_form)
            ck("draw %d: swap antisymmetry M(r,p) = -M(p,r)" % draw, ok_anti)
        # char-3 step: K = -K => K = 0
        ck("char 3: x = -x has only x = 0",
           all(add(x, x) != 0 or x == 0 for x in range(Q))
           and all(not (x == neg(x)) for x in range(1, Q)))

        # S3: branch (b) difference identity, arbitrary lam
        print("S3 branch (b): difference identity")
        for draw in range(3):
            lp = rng.randrange(1, Q)
            lm = rng.randrange(1, Q)
            _, M = make_M(lp, lm)
            sbar = add(lp, lm)
            ok_diff = True
            for _ in range(300):
                p, r = rng.sample(T, 2)
                d0, d1 = edge2(p, r)
                if sub(M(p, r), M(r, p)) != mul(sbar, sub(powE(d0), powE(d1))):
                    ok_diff = False
            ck("draw %d: M(p,r)-M(r,p) = (lam+ + lam-)(d0^e - d1^e)"
               % draw, ok_diff)
        # Sigma-bar = 0 draw
        lp = rng.randrange(1, Q)
        _, M = make_M(lp, neg(lp))
        ok0 = all(M(p, r) == M(r, p)
                  for p, r in (rng.sample(T, 2) for _ in range(300)))
        ck("Sigma-bar = 0: M(p,r) = M(r,p) exactly (K constant shape)", ok0)

        # S4: branch (c) quantization
        print("S4 branch (c): Frobenius quantization")
        for draw in range(3):
            lp = rng.randrange(1, Q)
            lm = rng.randrange(1, Q)
            lam, M = make_M(lp, lm)
            mu = {c: sub(lam[c], cube(lam[c])) for c in (1, -1)}
            ok_q = True
            for _ in range(300):
                p, r = rng.sample(T, 2)
                d0, d1 = edge2(p, r)
                lhs = sub(M(cube(p), cube(r)), cube(M(p, r)))
                rhs = sub(mul(mu[chi(d0)], powg(d0, 3 * E)),
                          mul(mu[chi(d1)], powg(d1, 3 * E)))
                if lhs != rhs:
                    ok_q = False
            ck("draw %d: M(p^3,r^3) - M^3 = mu_c d0^{3e} - mu_c' d1^{3e}"
               % draw, ok_q)
        # F_3 pairs: exact Frobenius equivariance
        f3 = [0, 1, neg(1)]
        ok_f3 = True
        for lp in f3:
            for lm in f3:
                _, M = make_M(lp, lm)
                for _ in range(60):
                    p, r = rng.sample(T, 2)
                    if M(cube(p), cube(r)) != cube(M(p, r)):
                        ok_f3 = False
        ck("all 9 F_3 pairs: M(p^3,r^3) = M(p,r)^3 exactly", ok_f3)

        # S5: confinement collapse ingredients
        print("S5 confinement collapse ingredients")
        # bijectivity of x -> x^{3e}: injective on a sample + gcd check above
        seen = set()
        for x in range(1, 2000):
            seen.add(powg(x, 3 * E))
        ck("x -> x^{3e} injective (sample 1999 distinct images)",
           len(seen) == 1999)
        ck("(-1)^{3e} = -1", powg(neg(1), 3 * E) == neg(1))
        # only x = +-1 solve x^{3e} = +-1
        sols = [x for x in range(1, Q)
                if powg(x, 3 * E) in (1, neg(1))]
        ck("x^{3e} in {1,-1} <=> x in {1,-1}", sorted(sols) == sorted([1, neg(1)]))
        # all-mixed rho=-1 world: M collapses to Sigma-bar d0^e.
        # (synthetic: for arbitrary d0 != 0 with d1 := -d0)
        lp = rng.randrange(1, Q)
        lm = rng.randrange(1, Q)
        lam = {1: lp, -1: lm}
        sbar = add(lp, lm)
        ok_mx = True
        for _ in range(300):
            d0 = rng.randrange(1, Q)
            d1 = neg(d0)
            val = sub(mul(lam[chi(d0)], powE(d0)), mul(lam[chi(d1)], powE(d1)))
            if val != mul(sbar, powE(d0)):
                ok_mx = False
        ck("rho = -1 edge: master value = (lam+ + lam-) d0^e", ok_mx)
        # d0 -> d0^e injective (so K(p) = Sbar d0^e pins r per p)
        ck("gcd(e, Q-1) = 1 (d -> d^e injective)", math.gcd(E, N1) == 1)

        # real q=7 populations (full census)
        pe = {p: powE(p) for p in T}
        pme = {p: powE(sub(p, 1)) for p in T}
        n_edge = n_same = n_rho1 = n_rhom1 = 0
        for p in T:
            for r in T:
                if r == p:
                    continue
                d0 = sub(pe[r], pe[p])
                d1 = sub(pme[r], pme[p])
                n_edge += 1
                lr = (log[d1] - log[d0]) % N1
                if lr % 2 == 0:
                    n_same += 1
                if lr == 0:
                    n_rho1 += 1
                if d1 == neg(d0):
                    n_rhom1 += 1
        print("  edges %d: same-sign(chi rho=+1) %d, rho=1 %d, rho=-1 %d"
              % (n_edge, n_same, n_rho1, n_rhom1))
        ck("same-sign edges exist (kills lam^3 != lam at q=7)", n_same > 0)
        ck("not all edges rho = -1", n_rhom1 < n_edge)
        # (+,-) out-degree census for 20 random p
        mindeg = 10 ** 9
        for p in rng.sample(T, 20):
            deg_pm = deg_mp = 0
            for r in T:
                if r == p:
                    continue
                d0 = sub(pe[r], pe[p])
                d1 = sub(pme[r], pme[p])
                if chi(d0) == 1 and chi(d1) == -1:
                    deg_pm += 1
                if chi(d0) == -1 and chi(d1) == 1:
                    deg_mp += 1
            mindeg = min(mindeg, deg_pm, deg_mp)
        print("  min mixed out-degree over 20 sampled p: %d" % mindeg)
        ck("mixed out-degrees >> 2 (counting kill has huge slack)",
           mindeg > 2)

        # S6: F_3 candidate (1,0) wrong-pattern kills on synthetic patterns
        print("S6 F_3 candidate (1,0) pattern kills")
        lam, M = make_M(1, 0)
        ok_mm = ok_pm = ok_mp = ok_pp = True
        cnt = {(1, 1): 0, (1, -1): 0, (-1, 1): 0, (-1, -1): 0}
        for _ in range(2000):
            p, r = rng.sample(T, 2)
            d0, d1 = edge2(p, r)
            pat = (chi(d0), chi(d1))
            cnt[pat] += 1
            v = M(p, r)
            if pat == (-1, -1) and v != 0:
                ok_mm = False
            if pat == (1, -1) and v != powE(d0):
                ok_pm = False
            if pat == (-1, 1) and v != neg(powE(d1)):
                ok_mp = False
            if pat == (1, 1) and v != sub(powE(d0), powE(d1)):
                ok_pp = False
        print("  sampled pattern counts: %s" % cnt)
        ck("(-,-) => M = 0 (kills K != 0)", ok_mm and cnt[(-1, -1)] > 0)
        ck("(+,-) => M = d0^e (pins r via injectivity)",
           ok_pm and cnt[(1, -1)] > 0)
        ck("(-,+) => M = -d1^e (pins r via injectivity)",
           ok_mp and cnt[(-1, 1)] > 0)
        ck("(+,+) => M = d0^e - d1^e (swap edge is (-,-))",
           ok_pp and cnt[(1, 1)] > 0)

    print()
    if fails:
        print("FAILURES: %d" % len(fails))
        for f in fails:
            print("  - " + f)
    else:
        print("ALL CHECKS PASSED")


if __name__ == '__main__':
    main()
