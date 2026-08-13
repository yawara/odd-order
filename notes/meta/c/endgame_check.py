#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
endgame_check.py -- verify the endgame algebra of the skew calculus on GF(3^7).

1. Commutator-loop weight formula: for edges e (class rho, comp c1) and f
   (class sigma, comp chi(rho)c1), the 4-leg loop e, f, rev(e'), rev(f')
   with e' in slot (rho, chi(sigma)c1), f' in slot (sigma, c1) has
   X_tot/v^e = kh(e) + kh(f) rho^e - k(e') (sigma rho)^e - k(f') sigma^e
   where kh(g) = K(p_g) delta0(g)^{-e}, k(g) = K(p_g) delta1(g)^{-e}.
   We verify this against the literal chain composer (t-recursion), and that
   under slot-constancy it reduces to the exchange relation (EX).

2. Master-formula fit: the conspiracy requires
   K(p) = lam[chi(d0)] d0^e - lam[chi(d1)] d1^e for all (p,r).
   At q=7 we solve for (lam+, lam-) from two edges and count how many other
   edges satisfy it (expected: essentially none -- conspiracy false).

3. The identity delta0^e - delta1^e = K(p) - K(r) + defect: measure defect
   (dream-world check: it should be NONZERO generically, else (1,1)-conspiracy
   would trivially hold).
"""
import os
import sys
import random
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, os.pardir, 'collision_impact')))
import collision_impact as ci

Q = 3 ** 7
N1 = Q - 1
E2OF = {151: 941, 941: 151}
F7POLY = [1, 0, 2, 0, 0, 0, 0, 1]


def main():
    rng = random.Random(20260814)
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

    T = [p for p in range(Q) if p and log[p] % 2 == 0
         and sub(p, 1) and log[sub(p, 1)] % 2 == 0]
    assert len(T) == 546

    for E in [151, 941]:
        def powE(x):
            return exp[log[x] * E % N1] if x else 0

        def powE2(x):
            return exp[log[x] * E2OF[E] % N1] if x else 0

        K = {p: sub(powE2(sub(p, 1)), powE2(p)) for p in T}

        def edge(p, r):
            d0 = sub(powE(r), powE(p))
            d1 = sub(powE(sub(r, 1)), powE(sub(p, 1)))
            return d0, d1

        # ---- 1. commutator loop vs chain composer ----
        # chain composer: edges as (A,B,X,Y); step: t_{i+1}^e = B_i t_i^e / A_{i+1}
        def run_chain(legs):
            # legs: list of (A,B,X,Y) already oriented (rev applied if needed)
            lte = 0  # log of t_1^e = 0 (t1 = 1)
            Xtot = 0
            Ytot = 0
            for i, (A, B, X, Y) in enumerate(legs):
                if i > 0:
                    Ap, Bp = legs[i - 1][0], legs[i - 1][1]
                    lte = (lte + log[Bp] - log[A]) % N1
                    if lte % 2:
                        return None  # sign-blocked
                u = exp[(lte * E) % N1]  # t_i^{e^2} = (t_i^e)^e
                Xtot = add(Xtot, mul(X, u))
                Ytot = add(Ytot, mul(Y, u))
            # closing
            A1, B1 = legs[0][0], legs[0][1]
            Ak, Bk = legs[-1][0], legs[-1][1]
            lclose = (lte + log[Bk]) % N1
            if lclose != log[A1] % N1:
                return None  # not closed
            return Xtot, Ytot

        nloops = 0
        nmatch = 0
        for _ in range(4000):
            p1, r1 = rng.sample(T, 2)
            p2, r2 = rng.sample(T, 2)
            d0a, d1a = edge(p1, r1)
            d0b, d1b = edge(p2, r2)
            # commutator: e fwd, f fwd, rev(e3) with e3 same class as e,
            # rev(f4) with f4 same class as f.  Use e3 = e, f4 = f (reuse).
            legs = [
                (d0a, d1a, K[p1], K[r1]),
                (d0b, d1b, K[p2], K[r2]),
                (d1a, d0a, neg(K[p1]), neg(K[r1])),   # rev(e)
                (d1b, d0b, neg(K[p2]), neg(K[r2])),   # rev(f)
            ]
            out = run_chain(legs)
            if out is None:
                continue
            nloops += 1
            Xt, Yt = out
            # predicted: v0 = d0a (t1=1); X/v^e with v = d0a:
            # kh(e) + kh(f) rho^e - k(e)(sig rho)^e - k(f) sig^e, scaled v0^e
            lrho = (log[d1a] - log[d0a]) % N1
            lsig = (log[d1b] - log[d0b]) % N1
            v0e = exp[(log[d0a] * E) % N1]
            kh_e = mul(K[p1], inv(exp[(log[d0a] * E) % N1]))
            kh_f = mul(K[p2], inv(exp[(log[d0b] * E) % N1]))
            k_e = mul(K[p1], inv(exp[(log[d1a] * E) % N1]))
            k_f = mul(K[p2], inv(exp[(log[d1b] * E) % N1]))
            rhoe = exp[(lrho * E) % N1]
            sige = exp[(lsig * E) % N1]
            pred = mul(kh_e, 1)
            pred = add(pred, mul(kh_f, rhoe))
            pred = add(pred, neg(mul(k_e, mul(sige, rhoe))))
            pred = add(pred, neg(mul(k_f, sige)))
            pred = mul(pred, v0e)
            if pred == Xt:
                nmatch += 1
        print("E=%d: commutator loops sampled %d, X_tot formula match %d/%d"
              % (E, nloops, nmatch, nloops))

        # ---- 2. master-formula fit ----
        # pick 2 random edges, solve lam[c0], lam[c1] when patterns allow,
        # then count satisfaction rate over 20000 random edges.
        def master_ok(lp, lm, p, r):
            d0, d1 = edge(p, r)
            l0 = lp if chi(d0) == 1 else lm
            l1 = lp if chi(d1) == 1 else lm
            rhs = sub(mul(l0, exp[(log[d0] * E) % N1]),
                      mul(l1, exp[(log[d1] * E) % N1]))
            return rhs == K[p]
        # solve from two edges with patterns (+,-) and (-,+) if found
        best = 0
        for trial in range(30):
            # gather equations: K[p] = lam_c0 * d0^e - lam_c1 * d1^e
            # linear in (lam+, lam-): coeff matrix over F
            eqs = []
            while len(eqs) < 2:
                p, r = rng.sample(T, 2)
                d0, d1 = edge(p, r)
                a_p = 0
                a_m = 0
                t0 = exp[(log[d0] * E) % N1]
                t1 = neg(exp[(log[d1] * E) % N1])
                if chi(d0) == 1:
                    a_p = add(a_p, t0)
                else:
                    a_m = add(a_m, t0)
                if chi(d1) == 1:
                    a_p = add(a_p, t1)
                else:
                    a_m = add(a_m, t1)
                eqs.append((a_p, a_m, K[p]))
            (a1, b1, c1), (a2, b2, c2) = eqs
            det = sub(mul(a1, b2), mul(a2, b1))
            if det == 0:
                continue
            di = inv(det)
            lp = mul(di, sub(mul(c1, b2), mul(c2, b1)))
            lm = mul(di, sub(mul(a1, c2), mul(a2, c1)))
            cnt = 0
            for _ in range(2000):
                p, r = rng.sample(T, 2)
                if master_ok(lp, lm, p, r):
                    cnt += 1
            best = max(best, cnt)
        print("  master-formula best satisfaction over random (lam) fits: "
              "%d/2000" % best)
        # also the 9 F_3 candidates
        f3 = [0, 1, neg(1)]
        for lp in f3:
            for lm in f3:
                cnt = sum(1 for _ in range(500)
                          if master_ok(lp, lm, *rng.sample(T, 2)))
                if cnt > 5:
                    print("  F_3 candidate (%s,%s): %d/500 !!" % (lp, lm, cnt))
        print("  (all F_3 candidates <= 5/500 unless printed)")

        # ---- 3. dream-world defect ----
        nz = 0
        for _ in range(500):
            p, r = rng.sample(T, 2)
            d0, d1 = edge(p, r)
            lhs = sub(exp[(log[d0] * E) % N1], exp[(log[d1] * E) % N1])
            rhs = sub(K[p], K[r])
            if lhs != rhs:
                nz += 1
        print("  defect (d0^e - d1^e != K(p)-K(r)): %d/500 nonzero" % nz)


if __name__ == '__main__':
    main()
