#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""assembly_spotcheck.py -- FINAL-ASSEMBLY audit spot checks, GF(3^7).

Independent of the three lens scripts.  Checks:
  A. standing facts: |T|=(Q-3)/4, K!=0 on T, chi(-1)=-1, gcd(3e,Q-1)=1,
     x^3=x <=> x in F_3, T Frobenius-stable, e-power bijective.
  B. translations for the e^2-collision endpoint:
     p in T <=> p-1 in paleySet;  K(p) = -powDiff_{E^2}(p-1);
     D_E(p) = powDiff_E(p-1).
  C. bridge end-to-end on a REAL e^2-collision: powDiffConj/Neg at exponent
     E^2 maps it to a genuine e-collision of Paley points; then the
     CollisionPair packaging conditions (delta != 0, exactly one ordering
     square) hold.
  D. fwd-fwd swap 2-loop composer semantics: accepted iff rho=-1 (with the
     chi rho=-1 junction), weight (K(p)+K(r), K(r)+K(p)).
  E. assembled-kill walkthrough: for each of the 4 F_3 candidates, a random
     generic lambda, (lam,lam) and (lam,-lam): identify the tree step that
     fires and verify its concrete absurdity in the field.
"""
import os, sys, math, random

sys.path.insert(0, '/home/ywr/odd-order/notes/meta/c')
import collision_impact as ci

Q = 3 ** 7
N1 = Q - 1
E2OF = {151: 941, 941: 151}
F7POLY = [1, 0, 2, 0, 0, 0, 0, 1]

rng = random.Random(99720813)
F = ci.Field(7, F7POLY)
exp, log, add = F.exp, F.log, F.add_enc

def neg(x): return add(x, x)
def sub(x, y): return add(x, neg(y))
def mul(x, y):
    if x == 0 or y == 0: return 0
    return exp[(log[x] + log[y]) % N1]
def inv(x): return exp[(N1 - log[x]) % N1]
def chi(x): return 1 if log[x] % 2 == 0 else -1
def powg(x, k): return exp[(log[x] * (k % N1)) % N1] if x else 0

fails = []
def ck(name, ok):
    print("  [%s] %s" % ("OK " if ok else "FAIL", name))
    if not ok: fails.append(name)

one = 1
m1 = neg(1)

T = [p for p in range(Q) if p and log[p] % 2 == 0 and sub(p, 1)
     and log[sub(p, 1)] % 2 == 0]
Tset = set(T)

print("A. standing facts")
ck("|T| = (Q-3)/4 = 546", len(T) == (Q - 3) // 4 == 546)
ck("chi(-1) = -1", chi(m1) == -1)
ck("x^3 = x <=> x in F_3 (3 elements)",
   sorted(x for x in range(Q) if powg(x, 3) == x or x == 0) == sorted([0, 1, m1]))
ck("T Frobenius-stable", all(powg(p, 3) in Tset for p in T))

for E in (151, 941):
    E2 = E2OF[E]
    print("== E = %d ==" % E)
    ck("gcd(3E, Q-1) = 1", math.gcd(3 * E, N1) == 1)
    ck("E odd, E^3 = 1 mod Q-1", E % 2 == 1 and (E ** 3) % N1 == 1)

    def powE(x): return powg(x, E)
    def powE2(x): return powg(x, E2)  # E2 = E*E mod N1

    ck("E2 == E*E mod N1", (E * E) % N1 == E2)

    K = {p: sub(powE2(sub(p, 1)), powE2(p)) for p in T}
    D = {p: sub(powE(p), powE(sub(p, 1))) for p in T}
    D2 = {p: sub(powE2(p), powE2(sub(p, 1))) for p in T}
    ck("K nonzero on all of T", all(K[p] for p in T))

    # --- B. translations ---
    print(" B. endpoint translations")
    def in_paley(a):
        return a != 0 and chi(a) == 1 and add(a, 1) != 0 and chi(add(a, 1)) == 1
    ck("p in T <=> p-1 in paleySet (all p in T + 300 random non-T)",
       all(in_paley(sub(p, 1)) for p in T) and
       all((x in Tset) == in_paley(sub(x, 1))
           for x in rng.sample(range(1, Q), 300)))
    def powDiff(EE, a):  # (a+1)^EE - a^EE
        return sub(powg(add(a, 1), EE), powg(a, EE))
    ck("K(p) = -powDiff_{E^2}(p-1)",
       all(K[p] == neg(powDiff(E * E, sub(p, 1))) for p in rng.sample(T, 100)))
    ck("D_E(p) = powDiff_E(p-1)",
       all(D[p] == powDiff(E, sub(p, 1)) for p in rng.sample(T, 100)))

    # --- C. bridge end-to-end on a REAL e^2 collision ---
    print(" C. downward bridge on a real e^2-collision")
    fib = {}
    coll2 = None
    for p in T:
        w = D2[p]
        if w in fib:
            coll2 = (fib[w], p); break
        fib[w] = p
    ck("an e^2-collision exists at q=7", coll2 is not None)
    p1, p2 = coll2
    a, b = sub(p1, 1), sub(p2, 1)
    ck("K(p1) = K(p2) for it (K-collision form)", K[p1] == K[p2])
    EE = E * E
    w = powDiff(EE, a)
    ck("collision value w nonzero", w != 0)
    wsq = (chi(w) == 1)
    def conj_map(x):
        if wsq:
            return mul(powg(x, EE), inv(powDiff(EE, x)))
        return mul(neg(powg(add(x, 1), EE)), inv(powDiff(EE, x)))
    c, d = conj_map(a), conj_map(b)
    ck("images distinct", c != d)
    ck("images in paleySet", in_paley(c) and in_paley(d))
    # powDiff_{E^4} = powDiff_E pointwise; verify collision at E via E^4
    ck("powDiff_{E^4}(x) = powDiff_E(x) pointwise (200 samples)",
       all(powDiff(EE * EE, x) == powDiff(E, x)
           for x in rng.sample(range(Q), 200)))
    ck("bridge output collides for E", powDiff(E, c) == powDiff(E, d))
    # CollisionPair packaging: delta != 0, exactly one ordering square
    delta = sub(powg(add(d, 1), E), powg(add(c, 1), E))
    ck("delta = (d+1)^E - (c+1)^E != 0", delta != 0)
    ck("exactly one of delta, -delta is a square",
       (chi(delta) == 1) != (chi(neg(delta)) == 1))

    # --- D. fwd-fwd swap 2-loop composer semantics ---
    print(" D. fwd-fwd swap 2-loop")
    def edge(p, r):
        return (sub(powE(r), powE(p)),
                sub(powE(sub(r, 1)), powE(sub(p, 1))))
    def run_chain(legs):
        lte, Xt, Yt = 0, 0, 0
        for i, (A, B, X, Y) in enumerate(legs):
            if i > 0:
                Bp = legs[i - 1][1]
                lte = (lte + log[Bp] - log[A]) % N1
                if lte % 2: return None
            u = exp[(lte * E) % N1]
            Xt = add(Xt, mul(X, u)); Yt = add(Yt, mul(Y, u))
        if (lte + log[legs[-1][1]]) % N1 != log[legs[0][0]] % N1: return None
        return Xt, Yt
    em1 = None; eother = None; eplus = None
    for p in T:
        for r in T:
            if r == p: continue
            d0, d1 = edge(p, r)
            if d1 == neg(d0) and em1 is None: em1 = (p, r, d0, d1)
            lr = (log[d1] - log[d0]) % N1
            if lr % 2 == 1 and d1 != neg(d0) and eother is None:
                eother = (p, r, d0, d1)
            if lr % 2 == 0 and lr != 0 and eplus is None:
                eplus = (p, r, d0, d1)
        if em1 and eother and eplus: break
    p, r, d0, d1 = em1
    out = run_chain([(d0, d1, K[p], K[r]), (neg(d0), neg(d1), K[r], K[p])])
    ck("rho=-1 edge: fwd-fwd accepted", out is not None)
    ck("weight = (K(p)+K(r), K(r)+K(p))",
       out == (add(K[p], K[r]), add(K[r], K[p])))
    ck("K(p)+K(r) != 0 on this edge (conspiracy consequence concretely false)",
       add(K[p], K[r]) != 0)
    pp, rr, dd0, dd1 = eother
    ck("chi rho=-1, rho!=-1 edge: fwd-fwd rejected (closure)",
       run_chain([(dd0, dd1, K[pp], K[rr]),
                  (neg(dd0), neg(dd1), K[rr], K[pp])]) is None)
    pp, rr, dd0, dd1 = eplus
    ck("chi rho=+1 edge: fwd-fwd sign-blocked",
       run_chain([(dd0, dd1, K[pp], K[rr]),
                  (neg(dd0), neg(dd1), K[rr], K[pp])]) is None)

    # --- E. assembled-kill walkthrough ---
    print(" E. assembled-kill walkthrough")
    lam_cases = [("(1,0)", one, 0), ("(0,1)", 0, one),
                 ("(-1,0)", m1, 0), ("(0,-1)", 0, m1)]
    # find, for each same-sign pattern, one concrete edge
    edge_cc = {}
    edge_mixed = {}
    for p in T:
        for r in T:
            if r == p: continue
            d0, d1 = edge(p, r)
            pat = (chi(d0), chi(d1))
            if pat not in edge_cc and pat[0] == pat[1] and d0 != d1:
                edge_cc[pat] = (p, r, d0, d1)
            if pat[0] != pat[1] and pat not in edge_mixed:
                edge_mixed[pat] = (p, r, d0, d1)
        if len(edge_cc) == 2 and len(edge_mixed) == 2: break
    ck("both same-sign patterns realized (non-collision edges)",
       (1, 1) in edge_cc and (-1, -1) in edge_cc)
    for name, lp, lm in lam_cases:
        lam = {1: lp, -1: lm}
        Delta = sub(lp, lm); Sbar = add(lp, lm)
        mu = {c: sub(lam[c], powg(lam[c], 3)) for c in (1, -1)}
        assert Delta != 0 and Sbar != 0 and mu[1] == 0 and mu[-1] == 0
        # step 7 fires: the pattern with lam_c = 0 forces K(p) = 0
        cdead = 1 if lp == 0 else -1   # component whose lambda is 0
        p, r, d0, d1 = edge_cc[(cdead, cdead)]
        forced = sub(mul(lam[chi(d0)], powE(d0)), mul(lam[chi(d1)], powE(d1)))
        ck("cand %s: step-7 same-sign kill fires (forced K=0, actual K!=0)"
           % name, forced == 0 and K[p] != 0)
        # step 7 out-degree variant: 3 mixed-pattern rs from one p pin
        # pairwise-distinct forced values -> at most one r can satisfy master
        p0 = None
        for p in T:
            rs = []
            for r in T:
                if r == p: continue
                d0, d1 = edge(p, r)
                if chi(d0) != chi(d1): rs.append((r, d0, d1))
                if len(rs) == 3: break
            if len(rs) == 3: p0 = (p, rs); break
        p, rs = p0
        forced_vals = [sub(mul(lam[chi(d0)], powE(d0)),
                           mul(lam[chi(d1)], powE(d1))) for (r, d0, d1) in rs]
        ck("cand %s: 3 mixed edges from one p give pairwise-distinct pins"
           % name, len(set(forced_vals)) == 3)

    # random generic lambda -> step 6 fires
    lp = rng.randrange(1, Q); lm = rng.randrange(1, Q)
    lam = {1: lp, -1: lm}
    mu = {c: sub(lam[c], powg(lam[c], 3)) for c in (1, -1)}
    while mu[1] == 0 and mu[-1] == 0:
        lp = rng.randrange(1, Q); lam = {1: lp, -1: lm}
        mu = {c: sub(lam[c], powg(lam[c], 3)) for c in (1, -1)}
    cstar = 1 if mu[1] != 0 else -1
    p, r, d0, d1 = edge_cc[(cstar, cstar)]
    defect = sub(mul(mu[chi(d0)], powg(d0, 3 * E)),
                 mul(mu[chi(d1)], powg(d1, 3 * E)))
    ck("random lam (mu!=0): step-6 quantization defect nonzero on a "
       "same-sign edge in the mu!=0 component", defect != 0)
    ck("  (mechanism: rho^{3e} != 1 on that edge)",
       powg(mul(d1, inv(d0)), 3 * E) != 1)

    # (lam,lam): Delta=0 -> step 5; concrete absurdity of K(p) = -K(r)
    lamv = rng.randrange(1, Q)
    p, r = rng.sample(T, 2)
    d0, d1 = edge(p, r)
    Mpr = mul(lamv, sub(powE(d0), powE(d1)))
    d0s, d1s = edge(r, p)
    Mrp = mul(lamv, sub(powE(d0s), powE(d1s)))
    ck("(lam,lam): master antisymmetry M(r,p) = -M(p,r) (the forced law)",
       Mrp == neg(Mpr))
    s = next(x for x in T if x not in (p, r))
    # char-3 3-point algebra: x=-y, x=-z, y=-z => all zero
    ck("(lam,lam): step-5 3-point algebra kills (2 invertible in char 3)",
       add(one, one) != 0)
    ck("(lam,lam): actual K(p) != -K(r) for a concrete pair (world absurd)",
       any(add(K[a1], K[a2]) != 0 for a1 in (p, r, s) for a2 in (p, r, s)
           if a1 != a2))

    # (lam,-lam): Sigma-bar=0 -> step 5 K-constant -> bridge (checked in C)
    lamv = rng.randrange(1, Q)
    lam = {1: lamv, -1: neg(lamv)}
    p, r = rng.sample(T, 2)
    d0, d1 = edge(p, r)
    Mpr = sub(mul(lam[chi(d0)], powE(d0)), mul(lam[chi(d1)], powE(d1)))
    d0s, d1s = edge(r, p)
    Mrp = sub(mul(lam[chi(d0s)], powE(d0s)), mul(lam[chi(d1s)], powE(d1s)))
    ck("(lam,-lam): master symmetry M(p,r) = M(r,p) (K-constant law)",
       Mpr == Mrp)
    ck("(lam,-lam): actual K not constant at q=7 (world absurd; and if it "
       "were constant, bridge C fires)", len(set(K.values())) > 1)

    # realized-class census: real q=7 world is none of the degenerate ones
    n_m1 = n_rho1 = n_edge = 0
    cls_par = set()
    for p in rng.sample(T, 60):
        for r in T:
            if r == p: continue
            d0, d1 = edge(p, r)
            n_edge += 1
            lr = (log[d1] - log[d0]) % N1
            if lr == 0: n_rho1 += 1
            if d1 == neg(d0): n_m1 += 1
            cls_par.add(lr % 2)
    ck("sampled census: both parities realized, not singleton {-1}",
       cls_par == {0, 1} and n_m1 < n_edge)

print()
print("RESULT: %s (%d failures)" % ("ALL OK" if not fails else "FAILURES", len(fails)))
for f in fails:
    print("  - " + f)
