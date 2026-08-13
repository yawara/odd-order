#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""lensA_commutator_verify.py -- adversarial verification of the commutator
loop / (EX) endgame step (issue 0180, note section 6.1).

Checks, on GF(3^7), both exotic exponents:

  (0) The ORIGINAL endgame_check.py sampler reuses g3=g1, g4=g2; show that
      every ACCEPTED reuse loop has chi(rho)=chi(sigma)=+1, i.e. the
      1010/1010 verification only covered the (+,+) sector.
  (1) LEGALITY: for all four sign cases (chi rho, chi sigma) and both c1,
      the component-correct 4-leg commutator loop
        g1 fwd in (rho,c1), g2 fwd in (sigma, chi(rho)c1),
        rev(g3), g3 in (rho, chi(sigma)c1), rev(g4), g4 in (sigma, c1)
      is NEVER sign-blocked and always closes (chain composer accepts).
  (2) WEIGHT FORMULA in every sector:
        X_tot = v^e [ kh(g1) + kh(g2) rho^e - k(g3) (sig rho)^e - k(g4) sig^e ]
      and the (EX)-shaped rearrangement
        X_tot = v^e [ k(g1) rho^e - k(g4) sig^e - sig^e rho^e (k(g3)-k(g2)) ]
      plus the Y-side analogue with K(r)-based kappa's.
  (3) NEGATIVE CONTROL: putting g3 in the WRONG component always
      sign-blocks the chain.
  (4) MASTER SOLVES (EX): random lam+/lam-, random class pairs of all four
      parities: khat(rho,c) = lam_c - lam_{chi(rho)c} rho^e satisfies
      (EX'): khat(r,c) - khat(s,c) = s^e khat(r, chi(s)c) - r^e khat(s, chi(r)c).
  (5) UNIQUENESS (rank): the (EX) linear system on sampled realized class
      sets has solution space of dimension exactly 2 (= the master family):
      mixed parities, all-plus, all-minus, all-minus including rho=-1;
      and exhibits the singleton {rho=-1} exception (dim 2 > master dim 1).
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
    rng = random.Random(20260813)
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

    T = [p for p in range(Q) if p and log[p] % 2 == 0
         and sub(p, 1) and log[sub(p, 1)] % 2 == 0]
    assert len(T) == 546
    # chi(-1) = -1 (Q = 3 mod 4): sanity
    assert log[neg(1)] % 2 == 1, "chi(-1) must be -1 for swap component flip"

    grand_fail = 0

    for E in (151, 941):
        E2 = E2OF[E]

        def powE(x):
            return exp[log[x] * E % N1] if x else 0

        def powE2(x):
            return exp[log[x] * E2 % N1] if x else 0

        K = {p: sub(powE2(sub(p, 1)), powE2(p)) for p in T}

        # ---- index all edges by slot (lrho, comp) ----
        slots = {}
        classes_by_par = {0: set(), 1: set()}
        for p in T:
            for r in T:
                if r == p:
                    continue
                d0 = sub(powE(r), powE(p))
                d1 = sub(powE(sub(r, 1)), powE(sub(p, 1)))
                lrho = (log[d1] - log[d0]) % N1
                if lrho == 0:
                    continue  # rho = 1 (collision) handled by a separate branch
                c = 1 if log[d0] % 2 == 0 else -1
                key = (lrho, c)
                lst = slots.get(key)
                if lst is None:
                    slots[key] = lst = []
                if len(lst) < 30:
                    lst.append((p, r, d0, d1))
                classes_by_par[lrho % 2].add(lrho)
        # swap-population check: every realized (class, comp) has the other comp
        miss = sum(1 for (lr, c) in slots if (lr, -c) not in slots)
        even_cls = sorted(classes_by_par[0])
        odd_cls = sorted(classes_by_par[1])
        print("E=%d: classes chi=+1: %d, chi=-1: %d; slots missing swap comp: %d"
              % (E, len(even_cls), len(odd_cls), miss))
        if miss:
            grand_fail += 1
        assert 1093 in odd_cls, "rho=-1 class expected realized at q=7"

        # ---- chain composer (identical semantics to endgame_check.py) ----
        def run_chain(legs):
            lte = 0
            Xtot = 0
            Ytot = 0
            for i, (A, B, X, Y) in enumerate(legs):
                if i > 0:
                    Bp = legs[i - 1][1]
                    lte = (lte + log[Bp] - log[A]) % N1
                    if lte % 2:
                        return None
                u = exp[(lte * E) % N1]
                Xtot = add(Xtot, mul(X, u))
                Ytot = add(Ytot, mul(Y, u))
            A1 = legs[0][0]
            Bk = legs[-1][1]
            if (lte + log[Bk]) % N1 != log[A1] % N1:
                return None
            return Xtot, Ytot

        def fwd(e):
            return (e[2], e[3], K[e[0]], K[e[1]])

        def rev(e):
            return (e[3], e[2], neg(K[e[0]]), neg(K[e[1]]))

        # ---- (0) original reuse sampler: which sectors does it reach? ----
        sector_ct = defaultdict(int)
        for _ in range(4000):
            p1, r1 = rng.sample(T, 2)
            p2, r2 = rng.sample(T, 2)
            d0a = sub(powE(r1), powE(p1))
            d1a = sub(powE(sub(r1, 1)), powE(sub(p1, 1)))
            d0b = sub(powE(r2), powE(p2))
            d1b = sub(powE(sub(r2, 1)), powE(sub(p2, 1)))
            e1 = (p1, r1, d0a, d1a)
            e2 = (p2, r2, d0b, d1b)
            out = run_chain([fwd(e1), fwd(e2), rev(e1), rev(e2)])
            if out is None:
                continue
            srho = 1 if (log[d1a] - log[d0a]) % 2 == 0 else -1
            ssig = 1 if (log[d1b] - log[d0b]) % 2 == 0 else -1
            sector_ct[(srho, ssig)] += 1
        print("  (0) reuse-sampler accepted loops by sector: %s"
              % dict(sector_ct))
        if any(k != (1, 1) for k in sector_ct):
            print("      !! reuse sampler reached a non-(+,+) sector")
            grand_fail += 1

        # ---- (1)-(3) component-correct loops in all four sectors ----
        pools = {1: even_cls, -1: odd_cls}
        for srho in (1, -1):
            for ssig in (1, -1):
                for c1 in (1, -1):
                    tried = 0
                    blocked = 0
                    mX = 0
                    mEX = 0
                    mY = 0
                    ctl_tot = 0
                    ctl_blk = 0
                    while tried < 250:
                        lr = rng.choice(pools[srho])
                        ls = rng.choice(pools[ssig])
                        if lr == ls:
                            continue
                        g1s = slots.get((lr, c1))
                        g2s = slots.get((ls, srho * c1))
                        g3s = slots.get((lr, ssig * c1))
                        g4s = slots.get((ls, c1))
                        if not (g1s and g2s and g3s and g4s):
                            print("      !! unpopulated slot for classes "
                                  "(%d,%d) sector (%d,%d)" % (lr, ls, srho, ssig))
                            grand_fail += 1
                            continue
                        e1 = rng.choice(g1s)
                        e2 = rng.choice(g2s)
                        e3 = rng.choice(g3s)
                        e4 = rng.choice(g4s)
                        tried += 1
                        out = run_chain([fwd(e1), fwd(e2), rev(e3), rev(e4)])
                        if out is None:
                            blocked += 1
                            continue
                        Xt, Yt = out
                        rhoe = exp[(lr * E) % N1]
                        sige = exp[(ls * E) % N1]
                        v0e = exp[(log[e1[2]] * E) % N1]

                        def kh(e, side):
                            return mul(K[e[side]], inv(exp[(log[e[2]] * E) % N1]))

                        def kp(e, side):
                            return mul(K[e[side]], inv(exp[(log[e[3]] * E) % N1]))

                        # X-side: p-based kappas
                        pred = add(add(kh(e1, 0), mul(kh(e2, 0), rhoe)),
                                   neg(add(mul(kp(e3, 0), mul(sige, rhoe)),
                                           mul(kp(e4, 0), sige))))
                        if mul(pred, v0e) == Xt:
                            mX += 1
                        # (EX)-shape rearrangement
                        exsh = sub(sub(mul(kp(e1, 0), rhoe), mul(kp(e4, 0), sige)),
                                   mul(mul(sige, rhoe),
                                       sub(kp(e3, 0), kp(e2, 0))))
                        if mul(exsh, v0e) == Xt:
                            mEX += 1
                        # Y-side: r-based kappas
                        predy = add(add(kh(e1, 1), mul(kh(e2, 1), rhoe)),
                                    neg(add(mul(kp(e3, 1), mul(sige, rhoe)),
                                            mul(kp(e4, 1), sige))))
                        if mul(predy, v0e) == Yt:
                            mY += 1
                        # (3) negative control: g3 from the WRONG component
                        g3w = slots.get((lr, -ssig * c1))
                        if g3w:
                            e3w = rng.choice(g3w)
                            ctl_tot += 1
                            if run_chain([fwd(e1), fwd(e2), rev(e3w),
                                          rev(e4)]) is None:
                                ctl_blk += 1
                    ok = tried - blocked
                    tag = "OK"
                    if blocked or mX != ok or mEX != ok or mY != ok \
                            or ctl_blk != ctl_tot:
                        tag = "FAIL"
                        grand_fail += 1
                    print("  (1-3) sector (chi_rho=%+d, chi_sig=%+d, c1=%+d): "
                          "%d loops, blocked %d, X-match %d, EX-shape %d, "
                          "Y-match %d, wrong-comp blocked %d/%d  [%s]"
                          % (srho, ssig, c1, tried, blocked, mX, mEX, mY,
                             ctl_blk, ctl_tot, tag))

        # ---- (4) master formula solves (EX') for random lam, all parities ----
        def khat_master(lp, lm, lcls, c):
            lam_c = lp if c == 1 else lm
            s = 1 if lcls % 2 == 0 else -1
            lam_sc = lp if s * c == 1 else lm
            return sub(lam_c, mul(lam_sc, exp[(lcls * E) % N1]))

        bad = 0
        tot = 0
        for _ in range(2000):
            lp = rng.randrange(Q)
            lm = rng.randrange(Q)
            lr = rng.choice(even_cls if rng.random() < 0.5 else odd_cls)
            ls = rng.choice(even_cls if rng.random() < 0.5 else odd_cls)
            if lr == ls:
                continue
            sr = 1 if lr % 2 == 0 else -1
            ss = 1 if ls % 2 == 0 else -1
            for c in (1, -1):
                lhs = sub(khat_master(lp, lm, lr, c), khat_master(lp, lm, ls, c))
                rhs = sub(mul(exp[(ls * E) % N1], khat_master(lp, lm, lr, ss * c)),
                          mul(exp[(lr * E) % N1], khat_master(lp, lm, ls, sr * c)))
                tot += 1
                if lhs != rhs:
                    bad += 1
        print("  (4) master satisfies (EX'): %d/%d (violations %d)"
              % (tot - bad, tot, bad))
        if bad:
            grand_fail += 1

        # ---- (5) rank of the (EX) linear system on sampled class sets ----
        def ex_rank(cls):
            n = 2 * len(cls)
            rows = []

            def idx(k, cc):
                return 2 * k + (0 if cc == 1 else 1)

            for i, lr in enumerate(cls):
                for j, ls in enumerate(cls):
                    if i == j:
                        continue
                    sr = 1 if lr % 2 == 0 else -1
                    ss = 1 if ls % 2 == 0 else -1
                    rhoe = exp[(lr * E) % N1]
                    sige = exp[(ls * E) % N1]
                    for c in (1, -1):
                        row = [0] * n
                        row[idx(i, c)] = add(row[idx(i, c)], 1)
                        row[idx(j, c)] = add(row[idx(j, c)], neg(1))
                        row[idx(i, ss * c)] = add(row[idx(i, ss * c)], neg(sige))
                        row[idx(j, sr * c)] = add(row[idx(j, sr * c)], rhoe)
                        rows.append(row)
            # gaussian elimination over F
            rank = 0
            for col in range(n):
                piv = None
                for k in range(rank, len(rows)):
                    if rows[k][col] != 0:
                        piv = k
                        break
                if piv is None:
                    continue
                rows[rank], rows[piv] = rows[piv], rows[rank]
                pv = inv(rows[rank][col])
                rows[rank] = [mul(x, pv) for x in rows[rank]]
                for k in range(len(rows)):
                    if k != rank and rows[k][col] != 0:
                        f = rows[k][col]
                        rows[k] = [sub(x, mul(f, y))
                                   for x, y in zip(rows[k], rows[rank])]
                rank += 1
            return rank, n

        def report_rank(name, cls, expect_dim):
            rank, n = ex_rank(cls)
            dim = n - rank
            tag = "OK" if dim == expect_dim else "FAIL"
            print("  (5) rank check %-34s n=%2d rank=%2d dim=%d (expect %d) [%s]"
                  % (name, n, rank, dim, expect_dim, tag))
            return dim == expect_dim

        e_s = rng.sample(even_cls, 3)
        o_s = rng.sample([x for x in odd_cls if x != 1093], 3)
        allok = True
        allok &= report_rank("mixed 3+/3-", e_s + o_s, 2)
        allok &= report_rank("all-plus 4", rng.sample(even_cls, 4), 2)
        allok &= report_rank("all-minus 4 (no -1)",
                             rng.sample([x for x in odd_cls if x != 1093], 4), 2)
        allok &= report_rank("all-minus 4 incl rho=-1",
                             [1093] + rng.sample(
                                 [x for x in odd_cls if x != 1093], 3), 2)
        allok &= report_rank("pair {-1, odd}", [1093, o_s[0]], 2)
        allok &= report_rank("singleton {rho=-1} (EXCEPTION)", [1093], 2)
        # master image dim on singleton {-1}: khat(+)=lam+ + lam-, khat(-)=lam- + lam+
        # (rho^e = -1) -> image is the diagonal, dim 1 < solution dim 2.
        v1 = khat_master(rng.randrange(1, Q), rng.randrange(1, Q), 1093, 1)
        v2 = khat_master(0, 0, 1093, 1)  # not needed; just structural print
        _ = (v1, v2)
        lp0, lm0 = rng.randrange(Q), rng.randrange(Q)
        diag = khat_master(lp0, lm0, 1093, 1) == khat_master(lp0, lm0, 1093, -1)
        print("  (5) singleton {-1}: master forces khat(+)=khat(-): %s "
              "(master image dim 1 < EX-solution dim 2 -> genuine exception)"
              % diag)
        if not diag:
            grand_fail += 1
        if not allok:
            grand_fail += 1

        # e-power injectivity: rho^e = sigma^e -> rho = sigma (no coincidences)
        assert all((lr * E) % N1 != 0 for lr in odd_cls + even_cls if lr)
        # 1 - rho^e != 0 for rho != 1; 1 + rho^e = 0 iff rho = -1
        bad1 = sum(1 for lr in even_cls + odd_cls
                   if exp[(lr * E) % N1] == 1)
        badm1 = [lr for lr in even_cls + odd_cls
                 if add(1, exp[(lr * E) % N1]) == 0]
        print("  (5) classes with rho^e=1: %d (expect 0); rho^e=-1: %s "
              "(expect [1093])" % (bad1, badm1))
        if bad1 or badm1 != [1093]:
            grand_fail += 1

    print()
    print("GRAND RESULT: %s (fail count %d)"
          % ("ALL CHECKS PASSED" if grand_fail == 0 else "FAILURES", grand_fail))


if __name__ == '__main__':
    main()
