#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
chain_closure.py — phase 2: composition-closure saturation for the 21 escape
collisions of GF(3^7) (BG App.C Problem 1, attack on (B2)).

Per collision (S, S') (oriented as in phase 1) the hypothetical group witness
forces the "ConjPair graph"
    V = F_3-span{ (S^(3^j), S'^(3^j)) : j = 0..6 }  subset  F^2 = F_3^14,
closed under F_3-linear combinations and under the two composition operations
(elements (s,s'), (t,t') of V with all four components nonzero):

  C1 (straight, always defined):
      c in {1,-1} with chi(c*s'/t) = 1  (exactly one works);
      eta = (c*s'/t)^(E^2)  [E^2 taken mod Q-1];  tau = 1 + eta  (never 0);
      r = s'*t'/(t*s);
      chi(tau) =  1  ->  new pair (m, r*m),  m = s*tau^(-E)
      chi(tau) = -1  ->  new pair (r*m, m),  m = s*(-tau)^(-E)
  C2 (flip, defined iff t' not in {s', -s'}):
      c in {1,-1} with chi(c*s'/t') = 1;  etah = (c*s'/t')^(E^2);
      tauh = 1 - etah  (nonzero given the guard; 0 would be an ANOMALY);
      rh = s'*t/(t'*s);  same normalisation with tauh in place of tau.

Kill conditions (pure linear algebra on V; witness dies => valid certificate):
  K1: V ∩ diagonal != 0          (nonzero fixed point (m,m))
  K2: V contains (0,x), x != 0   (graph violation)   <=> rank(Dom V) < dim V
  K3: rank(Dom V) = 7            (A normalises the whole layer; existing thm)

Saturation loop: enumerate ALL elements of V (it is tiny, |V| <= 3^7), apply
C1 and C2 to all ordered pairs, span-update, kill-check after every span
growth, iterate to fixed point or kill; caps: 6 rounds, dim 7.
NOTE dim(V) = 7 provably forces K2 or K3: rank(Dom V) <= 7, and either it is
7 (K3) or it is < dim V (K2).  So the dim cap is self-enforcing.

Efficiency note (verified empirically in 'full' mode for one escape per E):
composition results are invariant under negating (t,t') and negated under
negating (s,s'), for both C1 and C2, so sweeping one representative per
+-class of V generates the same span.  Default sweep uses +-classes.

Field arithmetic (exp/log/Zech tables for GF(3^7), modulus X^7+2X^2+1,
generator g = X) is reused from phase 1: ../collision_impact/collision_impact.py.
Escape data is recomputed with the same code AND cross-checked against the
parsed phase-1 results.txt (both the ESCAPE blocks and the 70-row per-E
detail tables).
"""

import os
import re
import sys
import time
from collections import Counter, defaultdict
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
P1DIR = os.path.normpath(os.path.join(HERE, os.pardir, 'collision_impact'))
sys.path.insert(0, P1DIR)
import collision_impact as ci

Q7 = 3 ** 7                  # 2187
MAX_ROUNDS = 6
F7POLY = [1, 0, 2, 0, 0, 0, 0, 1]   # X^7 + 2X^2 + 1 (same as phase 1)


# ------------------------------------------------------------------
# GF(3)^14 pair-vector helpers.  A pair (m, m') of field elements
# (encodings < 3^7) is packed as enc = m + 3^7 * m'; digitwise base-3
# integer addition realises addition in F^2.
# ------------------------------------------------------------------

def add14(x, y):
    r = 0
    m = 1
    for _ in range(14):
        r += ((x % 3 + y % 3) % 3) * m
        x //= 3
        y //= 3
        m *= 3
    return r


def neg14(x):
    return add14(x, x)          # 2v = -v in char 3


def enc_to_vec14(enc):
    v = []
    for _ in range(14):
        v.append(enc % 3)
        enc //= 3
    return v


def vec14_to_enc(v):
    e = 0
    for c in reversed(v):
        e = e * 3 + c
    return e


def gf3_rank(vecs, width):
    rows = {}
    for v0 in vecs:
        v = list(v0)
        for p in sorted(rows, reverse=True):
            c = v[p]
            if c:
                row = rows[p]
                for i in range(width):
                    if row[i]:
                        v[i] = (v[i] - c * row[i]) % 3
        piv = -1
        for i in range(width - 1, -1, -1):
            if v[i]:
                piv = i
                break
        if piv >= 0:
            if v[piv] == 2:
                v = [(2 * x) % 3 for x in v]
            rows[piv] = v
    return len(rows)


class Span(object):
    """F_3-span of 14-digit pair vectors, echelon rows keyed by top pivot."""

    def __init__(self):
        self.rows = {}

    def dim(self):
        return len(self.rows)

    def reduce_vec(self, v):
        v = list(v)
        for p in sorted(self.rows, reverse=True):
            c = v[p]
            if c:
                row = self.rows[p]
                for i in range(14):
                    if row[i]:
                        v[i] = (v[i] - c * row[i]) % 3
        return v

    def insert_enc(self, enc):
        """Insert; return True iff the span grew."""
        v = self.reduce_vec(enc_to_vec14(enc))
        piv = -1
        for i in range(13, -1, -1):
            if v[i]:
                piv = i
                break
        if piv < 0:
            return False
        if v[piv] == 2:
            v = [(2 * x) % 3 for x in v]
        self.rows[piv] = v
        return True

    def basis_encs(self):
        return [vec14_to_enc(v) for v in self.rows.values()]


def span_set(basis_encs):
    elems = set([0])
    for b in basis_encs:
        b2 = add14(b, b)
        for e in list(elems):
            elems.add(add14(e, b))
            elems.add(add14(e, b2))
    assert len(elems) == 3 ** len(basis_encs), "basis not independent"
    return elems


def kill_status(span):
    """-> (conds, dim, dom_rank, dim(V∩Δ), dim(V∩(Fx0)))"""
    rows = list(span.rows.values())
    dim = len(rows)
    dom = gf3_rank([r[:7] for r in rows], 7)
    ran = gf3_rank([r[7:] for r in rows], 7)
    diff = gf3_rank([[(r[7 + i] - r[i]) % 3 for i in range(7)] for r in rows], 7)
    dimD = dim - diff
    conds = []
    if dimD > 0:
        conds.append('K1')
    if dom < dim:
        conds.append('K2')
    if dom == 7:
        conds.append('K3')
    return conds, dim, dom, dimD, dim - ran


# ------------------------------------------------------------------
# composition operations, log-space (fast path)
# ------------------------------------------------------------------

def compose_C1(F, E, E2, ls, lsp, lt, ltp, stats):
    n1, half = F.n1, F.half
    stats['C1'] += 1
    lr0 = (lsp - lt) % n1                       # log(s'/t)
    ok1 = (lr0 % 2 == 0)
    ok2 = (((lr0 + half) % n1) % 2 == 0)
    if ok1 == ok2:
        stats['ANOMALY_c_choice'] += 1          # must be exactly one
    lcst = lr0 if ok1 else (lr0 + half) % n1    # log(c*s'/t), a square
    leta = lcst * E2 % n1
    if leta % 2:
        stats['ANOMALY_eta_nonsquare'] += 1
    ltau = F.add_log(leta, 0)                   # log(1 + eta)
    if ltau < 0:
        stats['ANOMALY_tau_zero_C1'] += 1
        return None
    lr = (lsp + ltp - lt - ls) % n1             # log(s't'/(ts))
    if ltau % 2 == 0:                           # tau square
        lm = (ls - ltau * E) % n1               # m = s * tau^(-E)
        return (lm, (lr + lm) % n1)
    lmt = (ltau + half) % n1                    # log(-tau), even now
    lm = (ls - lmt * E) % n1                    # m = s * (-tau)^(-E)
    return ((lr + lm) % n1, lm)


def compose_C2(F, E, E2, ls, lsp, lt, ltp, stats):
    """Caller must have checked the guard t' not in {s', -s'}."""
    n1, half = F.n1, F.half
    stats['C2'] += 1
    lr0 = (lsp - ltp) % n1                      # log(s'/t')
    ok1 = (lr0 % 2 == 0)
    ok2 = (((lr0 + half) % n1) % 2 == 0)
    if ok1 == ok2:
        stats['ANOMALY_c_choice'] += 1
    lcst = lr0 if ok1 else (lr0 + half) % n1
    leta = lcst * E2 % n1
    if leta % 2:
        stats['ANOMALY_eta_nonsquare'] += 1
    ltau = F.sub_log(0, leta)                   # log(1 - etah)
    if ltau < 0:
        stats['ANOMALY_tauhat_zero_C2'] += 1    # should be impossible w/ guard
        return None
    lr = (lsp + lt - ltp - ls) % n1             # log(s't/(t's))
    if ltau % 2 == 0:
        lm = (ls - ltau * E) % n1
        return (lm, (lr + lm) % n1)
    lmt = (ltau + half) % n1
    lm = (ls - lmt * E) % n1
    return ((lr + lm) % n1, lm)


# ------------------------------------------------------------------
# independent slow verification of compositions via polynomial arithmetic
# ------------------------------------------------------------------

def poly_pow_enc(F, enc, e):
    assert enc != 0
    return F.enc_of_poly(ci.ppowmod(F.poly_of_enc(enc), e, F.f))


def poly_mul_enc(F, a, b):
    return F.enc_of_poly(ci.pmod(ci.pmul(F.poly_of_enc(a), F.poly_of_enc(b)), F.f))


def poly_inv_enc(F, a):
    return poly_pow_enc(F, a, F.n1 - 1)


def poly_check(F, E, E2, ls, lsp, lt, ltp, out, flip):
    """Recompute C1 (flip=False) / C2 (flip=True) with ppowmod and compare."""
    n1, half = F.n1, F.half
    s, sp, t, tp = F.exp[ls], F.exp[lsp], F.exp[lt], F.exp[ltp]
    den = tp if flip else t
    ratio = poly_mul_enc(F, sp, poly_inv_enc(F, den))
    sq_p = (poly_pow_enc(F, ratio, half) == 1)
    nratio = F.add_enc(ratio, ratio)
    sq_n = (poly_pow_enc(F, nratio, half) == 1)
    assert sq_p != sq_n, "poly check: exactly-one-c violated"
    cst = ratio if sq_p else nratio
    eta = poly_pow_enc(F, cst, E2)
    assert poly_pow_enc(F, eta, half) == 1, "poly check: eta not a square"
    if flip:
        tau = F.add_enc(1, F.add_enc(eta, eta))     # 1 - etah
        num = poly_mul_enc(F, sp, t)
        dnm = poly_mul_enc(F, tp, s)
    else:
        tau = F.add_enc(1, eta)                     # 1 + eta
        num = poly_mul_enc(F, sp, tp)
        dnm = poly_mul_enc(F, t, s)
    assert tau != 0, "poly check: tau = 0"
    r = poly_mul_enc(F, num, poly_inv_enc(F, dnm))
    if poly_pow_enc(F, tau, half) == 1:
        m = poly_mul_enc(F, s, poly_inv_enc(F, poly_pow_enc(F, tau, E)))
        pair = (m, poly_mul_enc(F, r, m))
    else:
        ntau = F.add_enc(tau, tau)
        m = poly_mul_enc(F, s, poly_inv_enc(F, poly_pow_enc(F, ntau, E)))
        pair = (poly_mul_enc(F, r, m), m)
    got = (F.exp[out[0]], F.exp[out[1]])
    assert got == pair, "poly check: mismatch log-space vs polynomial"


# ------------------------------------------------------------------
# saturation loop
# ------------------------------------------------------------------

def build_reps(Vset, F, mode):
    """Elements of V with both components nonzero, as (log m, log m') pairs.
    mode 'half': one representative per {v,-v}; 'full': all nonzero."""
    out = []
    for enc in sorted(Vset):
        if enc == 0:
            continue
        if mode == 'half' and neg14(enc) < enc:
            continue
        m = enc % Q7
        mp = enc // Q7
        if m and mp:
            out.append((F.log[m], F.log[mp]))
    out.sort()
    return out


def init_span(F, rec):
    """Span of the 7 Frobenius-twist generator pairs."""
    n1 = F.n1
    span = Span()
    for j in range(7):
        pw = pow(3, j, n1)
        ls = rec['lS'] * pw % n1
        lsp = rec['lSp'] * pw % n1
        assert ls != lsp, "generator has S^(3^j) = S'^(3^j)"
        span.insert_enc(F.exp[ls] + Q7 * F.exp[lsp])
    return span


def saturate(F, E, rec, mode='half', poly_verify=3, max_rounds=MAX_ROUNDS,
             ops=('C1', 'C2')):
    n1, half = F.n1, F.half
    E2 = E * E % n1
    exp = F.exp
    stats = Counter()
    kill_cert = None
    t0 = time.time()

    span = init_span(F, rec)
    Vset = span_set(span.basis_encs())
    conds, dim, dom, dimD, anti = kill_status(span)
    init = (dim, dom, dimD, anti)
    dims = [dim]
    killed = bool(conds)
    kround = 0 if killed else None
    kconds = list(conds)
    rounds = 0
    fixed = False
    pv = poly_verify

    while not killed and rounds < max_rounds:
        rounds += 1
        reps = build_reps(Vset, F, mode)
        stats['reps_r%d' % rounds] = len(reps)
        grew = False
        for ls, lsp in reps:
            for lt, ltp in reps:
                outs = []
                if 'C1' in ops:
                    o1 = compose_C1(F, E, E2, ls, lsp, lt, ltp, stats)
                    if o1 is not None:
                        outs.append(('C1', o1))
                        if pv > 0:
                            poly_check(F, E, E2, ls, lsp, lt, ltp, o1, False)
                            stats['poly_checked'] += 1
                if 'C2' in ops:
                    if ltp != lsp and ltp != (lsp + half) % n1:
                        o2 = compose_C2(F, E, E2, ls, lsp, lt, ltp, stats)
                        if o2 is not None:
                            outs.append(('C2', o2))
                            if pv > 0:
                                poly_check(F, E, E2, ls, lsp, lt, ltp, o2, True)
                                stats['poly_checked'] += 1
                    else:
                        stats['C2_skipped_guard'] += 1
                if pv > 0:
                    pv -= 1
                for op, (l0, l1) in outs:
                    enc = exp[l0] + Q7 * exp[l1]
                    if enc in Vset:
                        stats['in_V'] += 1
                        continue
                    stats['new_pairs'] += 1
                    grew = True
                    assert span.insert_enc(enc)
                    Vset = span_set(span.basis_encs())
                    conds, dim, dom, dimD, anti = kill_status(span)
                    if conds:
                        killed = True
                        kround = rounds
                        kconds = list(conds)
                        kill_cert = {'op': op, 'in': (ls, lsp, lt, ltp),
                                     'out': (l0, l1), 'conds': list(conds)}
                        break
                    assert dim < 7, "dim 7 must trigger K2 or K3"
                if killed:
                    break
            if killed:
                break
        dims.append(span.dim())
        if killed:
            break
        if not grew:
            fixed = True
            break

    return {'killed': killed, 'round': kround, 'conds': kconds,
            'init': init, 'dims': dims, 'fixed': fixed, 'rounds': rounds,
            'final_dim': span.dim(), 'dom': dom, 'dimD': dimD, 'anti': anti,
            'span': span, 'Vset': Vset, 'stats': stats, 'kill_cert': kill_cert,
            'secs': time.time() - t0, 'mode': mode, 'ops': ops}


def rref_canonical(vec14s):
    """Canonical RREF basis (order-independent fingerprint of a span)."""
    rows = {}
    for v0 in vec14s:
        v = list(v0)
        for p in sorted(rows, reverse=True):
            c = v[p]
            if c:
                r = rows[p]
                for i in range(14):
                    if r[i]:
                        v[i] = (v[i] - c * r[i]) % 3
        piv = -1
        for i in range(13, -1, -1):
            if v[i]:
                piv = i
                break
        if piv >= 0:
            if v[piv] == 2:
                v = [(2 * x) % 3 for x in v]
            rows[piv] = v
    for p in sorted(rows):
        for p2 in sorted(rows):
            if p2 <= p:
                continue
            c = rows[p2][p]
            if c:
                r = rows[p]
                rows[p2] = [(rows[p2][i] - c * r[i]) % 3 for i in range(14)]
    return tuple(sorted(tuple(r) for r in rows.values()))


def one_round_results(F, E, rec, mode):
    """All C1/C2 results of one full sweep of the INITIAL V, no early stop."""
    n1, half = F.n1, F.half
    E2 = E * E % n1
    exp = F.exp
    span = init_span(F, rec)
    Vset = span_set(span.basis_encs())
    reps = build_reps(Vset, F, mode)
    stats = Counter()
    out = set()
    for ls, lsp in reps:
        for lt, ltp in reps:
            o1 = compose_C1(F, E, E2, ls, lsp, lt, ltp, stats)
            if o1 is not None:
                out.add(exp[o1[0]] + Q7 * exp[o1[1]])
            if ltp != lsp and ltp != (lsp + half) % n1:
                o2 = compose_C2(F, E, E2, ls, lsp, lt, ltp, stats)
                if o2 is not None:
                    out.add(exp[o2[0]] + Q7 * exp[o2[1]])
    anomalies = sum(v for k, v in stats.items() if k.startswith('ANOMALY'))
    return out, stats, anomalies


def neg_pair_log(F, pair):
    return ((pair[0] + F.half) % F.n1, (pair[1] + F.half) % F.n1)


def verify_sign_invariance(F, E, rec, nsample):
    """Direct check of the +-class reduction identities:
       C1(s,s';-t,-t') = C1(s,s';t,t')      C1(-s,-s';t,t') = -C1(s,s';t,t')
       C2(s,s';-t,-t') = C2(s,s';t,t')      C2(-s,-s';t,t') = -C2(s,s';t,t')
    on the first nsample +-class reps of the initial V."""
    n1, half = F.n1, F.half
    E2 = E * E % n1
    span = init_span(F, rec)
    Vset = span_set(span.basis_encs())
    reps = build_reps(Vset, F, 'half')[:nsample]
    stats = Counter()
    checks = 0
    for ls, lsp in reps:
        for lt, ltp in reps:
            b = compose_C1(F, E, E2, ls, lsp, lt, ltp, stats)
            assert compose_C1(F, E, E2, ls, lsp,
                              (lt + half) % n1, (ltp + half) % n1, stats) == b
            assert compose_C1(F, E, E2, (ls + half) % n1, (lsp + half) % n1,
                              lt, ltp, stats) == neg_pair_log(F, b)
            checks += 2
            if ltp != lsp and ltp != (lsp + half) % n1:
                b2 = compose_C2(F, E, E2, ls, lsp, lt, ltp, stats)
                assert compose_C2(F, E, E2, ls, lsp, (lt + half) % n1,
                                  (ltp + half) % n1, stats) == b2
                assert compose_C2(F, E, E2, (ls + half) % n1,
                                  (lsp + half) % n1, lt, ltp,
                                  stats) == neg_pair_log(F, b2)
                checks += 2
    assert sum(v for k, v in stats.items() if k.startswith('ANOMALY')) == 0
    return checks


def verify_kill_bruteforce(res):
    """Independent recomputation of K1/K2/K3 on the final V by enumerating
    all its elements (no echelon algebra): returns the set of conditions."""
    Vset = res['Vset']
    doms = set()
    k1 = k2 = False
    for enc in Vset:
        m = enc % Q7
        mp = enc // Q7
        doms.add(m)
        if enc != 0 and m == mp:
            k1 = True
        if m == 0 and mp != 0:
            k2 = True
    conds = set()
    if k1:
        conds.add('K1')
    if k2:
        conds.add('K2')
    if len(doms) == Q7:
        conds.add('K3')
    return conds


# ------------------------------------------------------------------
# collision recomputation (same scan as phase-1 analyze_E) + sanity
# ------------------------------------------------------------------

def collision_records(F, E):
    n1, half = F.n1, F.half
    exp, log, Z = F.exp, F.log, F.Z
    E2 = E * E % n1
    first = {}
    multi = {}
    for k in range(0, n1, 2):
        p = exp[k]
        d0 = p % 3
        p1e = p - d0 + (d0 + 2) % 3
        if p1e == 0:
            continue
        a1 = log[p1e]
        if a1 & 1:
            continue
        la = k * E % n1
        lb = (a1 * E + half) % n1
        z = Z[(la - lb) % n1]
        assert z >= 0
        Dl = (lb + z) % n1
        if Dl in multi:
            multi[Dl].append(k)
        elif Dl in first:
            multi[Dl] = [first.pop(Dl), k]
        else:
            first[Dl] = k
    recs = []
    for Dl, ms in multi.items():
        L = len(ms)
        for i in range(L):
            for j in range(i + 1, L):
                recs.append(ci.pair_record(F, E, E2, ms[i], ms[j]))
    return recs


def killed_sets(F, recs):
    half = F.half
    ka = set(i for i, r in enumerate(recs) if r['trS'] != 0 or r['trSp'] != 0)
    kb = set(i for i, r in enumerate(recs) if r['lrho'] == half)
    kc = set(i for i, r in enumerate(recs) if r['lrho'] == 0)
    kF = ci.f_criterion(F, recs)
    return ka, kb, kc, kF


def check_collision_direct(F, E, rec):
    """Sanity (i): both points in T, D(p) = D(r), S != S', S,S' nonzero."""
    n1, half = F.n1, F.half

    def logD(k):
        a1 = ci.a1_of(F, k)
        assert k % 2 == 0 and a1 % 2 == 0, "point not in T"
        la = k * E % n1
        lb = (a1 * E + half) % n1
        z = F.Z[(la - lb) % n1]
        assert z >= 0
        return (lb + z) % n1

    assert logD(rec['a0p']) == logD(rec['a0r']), "not a D-collision"
    assert rec['lS'] != rec['lSp'], "S = S'"
    # lS, lSp are logs, hence S, S' automatically nonzero; assert table sanity
    assert 0 <= rec['lS'] < n1 and 0 <= rec['lSp'] < n1


def verify_twists(F, E, rec):
    """All 7 Frobenius twists are themselves collision-derived pairs with
    S -> S^(3^j), S' -> S'^(3^j) (same orientation)."""
    n1 = F.n1
    E2 = E * E % n1
    for j in range(1, 7):
        pw = pow(3, j, n1)
        r2 = ci.pair_record(F, E, E2, rec['a0p'] * pw % n1, rec['a0r'] * pw % n1)
        assert r2['lS'] == rec['lS'] * pw % n1, "twist S mismatch"
        assert r2['lSp'] == rec['lSp'] * pw % n1, "twist S' mismatch"


def orbit_partition(F, recs, idxs):
    n1 = F.n1
    groups = defaultdict(list)
    for i in idxs:
        key = min((recs[i]['lS'] * pow(3, j, n1) % n1,
                   recs[i]['lSp'] * pow(3, j, n1) % n1) for j in range(7))
        groups[key].append(i)
    return dict(groups)


# ------------------------------------------------------------------
# phase-1 results.txt parsing (recovery cross-check)
# ------------------------------------------------------------------

def parse_phase1(path):
    data = {}
    cur_E = None
    pending = None
    intable = False
    sec_re = re.compile(r'^--- q=(\d+), E = (\d+)')
    esc_re = re.compile(r'^\s+ESCAPE #(\d+):')
    s_re = re.compile(r"S=g\^(\d+)=.*S'=g\^(\d+)=")
    rho_re = re.compile(r"rho=g\^(\d+)=")
    with open(path) as fh:
        for ln in fh:
            ln = ln.rstrip('\n')
            m = sec_re.match(ln)
            if m:
                q, E = int(m.group(1)), int(m.group(2))
                cur_E = E if q == 7 else None
                if cur_E is not None:
                    data[cur_E] = {'escapes': {}, 'table': {}}
                intable = False
                continue
            if cur_E is None:
                continue
            m = esc_re.match(ln)
            if m:
                pending = int(m.group(1))
                continue
            if pending is not None:
                m = s_re.search(ln)
                if m:
                    data[cur_E]['escapes'][pending] = [int(m.group(1)),
                                                       int(m.group(2)), None]
                    continue
                m = rho_re.search(ln)
                if m:
                    data[cur_E]['escapes'][pending][2] = int(m.group(1))
                    pending = None
                    continue
                continue
            if ln.startswith(' idx |'):
                intable = True
                continue
            if intable:
                parts = ln.split('|')
                if len(parts) == 6:
                    try:
                        idx = int(parts[0])
                    except ValueError:
                        intable = False
                        continue
                    p0, r0 = map(int, parts[1].split())
                    dlog = int(parts[2])
                    lS, lSp, lrho = map(int, parts[3].split())
                    trS, trSp = map(int, parts[4].split())
                    flags = tuple(parts[5].split())
                    data[cur_E]['table'][idx] = (p0, r0, dlog, lS, lSp, lrho,
                                                 trS, trSp, flags)
                else:
                    intable = False
    return data


# ------------------------------------------------------------------
# survivor characterisation
# ------------------------------------------------------------------

def characterize(F, res, emit):
    n1 = F.n1
    Vset = res['Vset']
    span = res['span']
    frob_ok = True
    for enc in span.basis_encs():
        m = enc % Q7
        mp = enc // Q7
        fm = F.exp[F.log[m] * 3 % n1] if m else 0
        fmp = F.exp[F.log[mp] * 3 % n1] if mp else 0
        if fm + Q7 * fmp not in Vset:
            frob_ok = False
    both = [(enc % Q7, enc // Q7) for enc in sorted(Vset)
            if enc % Q7 and enc // Q7]
    spec = sorted(set((F.log[mp] - F.log[m]) % n1 for m, mp in both))
    sset = set(spec)
    inv_closed = all((n1 - l) % n1 in sset for l in spec)
    frob_spec = all(l * 3 % n1 in sset for l in spec)
    prod_closed = all((l1 + l2) % n1 in sset for l1 in spec for l2 in spec)
    orders = Counter(n1 // gcd(n1, l) for l in spec)
    parity = Counter(l % 2 for l in spec)
    emit("    |V| = %d, elements with both comps nonzero = %d, dim = %d" %
         (len(Vset), len(both), span.dim()))
    emit("    V Frobenius-stable (x->x^3 both comps): %s" % frob_ok)
    emit("    ratio spectrum {m'/m}: size %d; 1 in spectrum: %s; "
         "inverse-closed: %s; product-closed(subgroup coset test): %s; "
         "Frobenius-closed (l->3l): %s" %
         (len(spec), 0 in sset, inv_closed, prod_closed, frob_spec))
    emit("    multiplicative orders of ratios: %s; square(even log)/nonsquare: %s" %
         (dict(sorted(orders.items())), dict(sorted(parity.items()))))
    lines = []
    for i in range(0, len(spec), 16):
        lines.append("      " + " ".join("%4d" % l for l in spec[i:i + 16]))
    emit("    spectrum logs (g^l):")
    for l in lines:
        emit(l)
    return {'frob_ok': frob_ok, 'spec': spec}


# ------------------------------------------------------------------
# main
# ------------------------------------------------------------------

def main():
    t_start = time.time()
    out_lines = []

    def emit(s=""):
        print(s, flush=True)
        out_lines.append(s)

    emit("Chain-closure saturation (phase 2), BG App.C Problem 1 (B2) attack")
    emit("python %s; field code reused from %s" %
         (sys.version.split()[0], os.path.join(P1DIR, 'collision_impact.py')))
    emit("")

    q = 7
    n1 = 3 ** q - 1
    half = n1 // 2
    F = ci.Field(q, F7POLY)
    emit("field: GF(3^7), modulus %s, generator g = X "
         "(tables cross-checked by Field ctor)" % ci.poly_str(F7POLY))
    Es, _ = ci.exotic_exponents(q)
    assert Es == [151, 941], Es
    emit("exotic exponents: %s (E^2 mod %d: %s)" %
         (Es, n1, [E * E % n1 for E in Es]))

    parsed = parse_phase1(os.path.join(P1DIR, 'results.txt'))
    assert set(parsed) == {151, 941}

    studied = []          # (E, idx, rec, tag, orbit_label)
    orbit_of = {}
    expected_escapes = {151: 14, 941: 7}
    controls_per_E = {151: 3, 941: 2}

    for E in Es:
        emit("")
        emit("=" * 72)
        emit("E = %d  (E^2 mod %d = %d)" % (E, n1, E * E % n1))
        recs = collision_records(F, E)
        assert len(recs) == 70, len(recs)
        ka, kb, kc, kF = killed_sets(F, recs)
        union = ka | kb | kc | kF
        escapes = [i for i in range(70) if i not in union]
        emit("collisions recomputed: %d; trace-killed %d, escapes %d "
             "(expected %d)" % (len(recs), len(ka), len(escapes),
                                expected_escapes[E]))
        assert len(escapes) == expected_escapes[E]

        # --- recovery cross-check vs phase-1 results.txt ---
        tab = parsed[E]['table']
        assert set(tab) == set(range(70))
        nfield = 0
        for i, r in enumerate(recs):
            p0, r0, dlog, lS, lSp, lrho, trS, trSp, flags = tab[i]
            assert (p0, r0, dlog) == (r['a0p'], r['a0r'], r['dlog']), i
            assert (lS, lSp, lrho) == (r['lS'], r['lSp'], r['lrho']), i
            assert (trS, trSp) == (r['trS'], r['trSp']), i
            myflags = ('x' if i in ka else '.', 'x' if i in kb else '.',
                       'x' if i in kc else '.', 'x' if i in kF else '.')
            assert flags == myflags, i
            nfield += 8
        esc_parsed = parsed[E]['escapes']
        assert set(esc_parsed) == set(escapes), (set(esc_parsed), set(escapes))
        for i in escapes:
            assert esc_parsed[i] == [recs[i]['lS'], recs[i]['lSp'],
                                     recs[i]['lrho']], i
        emit("cross-check vs phase-1 results.txt: 70-row table MATCH "
             "(%d fields) + escape blocks MATCH (%d escapes x lS,lS',lrho)" %
             (nfield, len(escapes)))

        # --- orbits ---
        orbs = orbit_partition(F, recs, escapes)
        sizes = sorted(len(v) for v in orbs.values())
        emit("escape Frobenius orbits: %d, sizes %s" % (len(orbs), sizes))
        if E == 151:
            assert len(orbs) == 2 and sizes == [7, 7]
        else:
            assert len(orbs) == 1 and sizes == [7]
        for oi, key in enumerate(sorted(orbs)):
            label = "%d/%s" % (E, chr(ord('A') + oi))
            for i in orbs[key]:
                orbit_of[(E, i)] = label
            emit("  orbit %s: escapes %s  (canonical (lS,lS') = %s)" %
                 (label, sorted(orbs[key]), key))

        # --- sanity (i) on every studied collision ---
        ctrl = sorted(ka)[:controls_per_E[E]]
        for i in escapes:
            check_collision_direct(F, E, recs[i])
            verify_twists(F, E, recs[i])
            studied.append((E, i, recs[i], 'ESC', orbit_of[(E, i)]))
        for i in ctrl:
            check_collision_direct(F, E, recs[i])
            verify_twists(F, E, recs[i])
            orbit_of[(E, i)] = '-'
            studied.append((E, i, recs[i], 'CTRL', '-'))
        emit("sanity (i): all %d studied collisions re-verified directly "
             "(T-membership, D(p)=D(r), S'!=S, S,S' nonzero) and all 7 "
             "Frobenius twists confirmed as oriented collision pairs" %
             (len(escapes) + len(ctrl)))
        emit("controls (trace-killed) chosen: %s (Tr(S),Tr(S') = %s)" %
             (ctrl, [(recs[i]['trS'], recs[i]['trSp']) for i in ctrl]))

    # ---------------- saturation runs ----------------
    emit("")
    emit("=" * 72)
    emit("SATURATION (caps: %d rounds, dim 7; sweep over +-classes; "
         "first 3 composition sites of each run verified by direct "
         "polynomial arithmetic)" % MAX_ROUNDS)
    emit("")
    results = {}
    total_stats = Counter()
    hdr = (" q    E  idx orbit  tag  |   lS   lS'  lrho | d0 dom0 dD0 a0 |"
           " result       rnd conds  | dim trace | fdom fdD fa |"
           " C1+C2 calls | newV | secs")
    emit(hdr)
    emit("-" * len(hdr))
    for E, i, rec, tag, orb in studied:
        res = saturate(F, E, rec)
        results[(E, i)] = res
        bf = verify_kill_bruteforce(res)
        assert bf == set(res['conds']), \
            "kill-condition brute-force mismatch at (E=%d, idx=%d): %s vs %s" \
            % (E, i, bf, res['conds'])
        st = res['stats']
        total_stats.update({k: v for k, v in st.items()
                            if k.startswith('ANOMALY') or k in
                            ('C1', 'C2', 'in_V', 'new_pairs', 'poly_checked',
                             'C2_skipped_guard')})
        d0, dom0, dD0, a0 = res['init']
        outcome = ("KILLED" if res['killed'] else
                   ("SURVIVE(fp)" if res['fixed'] else "SURVIVE(cap)"))
        emit(" %d %4d  %3d  %-5s %-4s | %4d  %4d  %4d |  %d   %d    %d  %d |"
             " %-12s %3s %-6s | %-9s |  %d    %d   %d |"
             " %5d+%-5d | %4d | %.2f" %
             (q, E, i, orb, tag, rec['lS'], rec['lSp'], rec['lrho'],
              d0, dom0, dD0, a0, outcome,
              str(res['round']) if res['round'] is not None else '-',
              '+'.join(res['conds']) if res['conds'] else '-',
              ','.join(map(str, res['dims'])),
              res['dom'], res['dimD'], res['anti'],
              st['C1'], st['C2'], st['new_pairs'], res['secs']))
    anomalies = sum(v for k, v in total_stats.items() if k.startswith('ANOMALY'))
    emit("-" * len(hdr))
    emit("totals: C1 = %d, C2 = %d, C2 skipped by guard = %d, "
         "results already in V = %d, new pairs = %d, poly-verified = %d" %
         (total_stats['C1'], total_stats['C2'], total_stats['C2_skipped_guard'],
          total_stats['in_V'], total_stats['new_pairs'],
          total_stats['poly_checked']))
    emit("ANOMALIES (exactly-one-c / eta nonsquare / tau=0 in C1 / "
         "tauhat=0 in C2 despite guard): %d %s" %
         (anomalies, "" if anomalies == 0 else "*** ANOMALY ***"))
    assert anomalies == 0

    # ---------------- orbit consistency ----------------
    emit("")
    by_orbit = defaultdict(list)
    for E, i, rec, tag, orb in studied:
        if tag == 'ESC':
            by_orbit[orb].append((E, i))
    for orb in sorted(by_orbit):
        sigs = set()
        for E, i in by_orbit[orb]:
            r = results[(E, i)]
            cert = r['kill_cert']
            sigs.add((r['killed'], r['round'], tuple(r['conds']),
                      tuple(r['dims']), frozenset(r['Vset']),
                      None if cert is None else
                      (cert['op'], cert['in'], cert['out'])))
        assert len(sigs) == 1, "orbit %s members disagree" % orb
        emit("orbit %s: all %d members give identical (outcome, round, conds, "
             "dims, final V, kill certificate) -- consistent (same initial V, "
             "deterministic sweep)" % (orb, len(by_orbit[orb])))

    # ---------------- kill certificates ----------------
    emit("")
    emit("one-point kill certificates (first composition that leaves the "
         "initial 6-dim module; logs base g):")
    done_orb = set()
    for E, i, rec, tag, orb in studied:
        res = results[(E, i)]
        cert = res['kill_cert']
        if cert is None:
            continue
        if tag == 'ESC':
            if orb in done_orb:
                continue
            done_orb.add(orb)
            who = "orbit %-5s (rep E=%d idx=%d)" % (orb, E, i)
        else:
            who = "CTRL  E=%d idx=%d" % (E, i)
        ls, lsp, lt, ltp = cert['in']
        l0, l1 = cert['out']
        emit("  %s: %s[(s,s')=(g^%d,g^%d), (t,t')=(g^%d,g^%d)] -> "
             "(g^%d, g^%d); + 7 twists => dim 7 => %s" %
             (who, cert['op'], ls, lsp, lt, ltp, l0, l1,
              '+'.join(cert['conds'])))

    # ---------------- C2-only diagnostic ----------------
    emit("")
    emit("C2-only diagnostic (main runs kill on the first C1 site, so C2 is "
         "never reached there; rerun each escape orbit rep with C1 disabled):")
    for E, i, rec, tag, orb in studied:
        if tag != 'ESC':
            continue
        if not (orb.endswith('/A') or orb.endswith('/B')):
            continue
        if (E, i) != min((E2_, i2) for (E2_, i2, r2, t2, o2) in studied
                         if t2 == 'ESC' and o2 == orb):
            continue
        r2only = saturate(F, E, rec, ops=('C2',))
        bf = verify_kill_bruteforce(r2only)
        assert bf == set(r2only['conds'])
        cert = r2only['kill_cert']
        emit("  orbit %-5s rep idx %2d: killed=%s round=%s conds=%s dims=%s "
             "C2 calls=%d anomalies=%d%s" %
             (orb, i, r2only['killed'], r2only['round'],
              '+'.join(r2only['conds']) if r2only['conds'] else '-',
              ','.join(map(str, r2only['dims'])), r2only['stats']['C2'],
              sum(v for k, v in r2only['stats'].items()
                  if k.startswith('ANOMALY')),
              "" if cert is None else
              "; cert C2[(g^%d,g^%d),(g^%d,g^%d)] -> (g^%d,g^%d)" %
              (cert['in'] + cert['out'])))

    # ---------------- +-class reduction verification ----------------
    emit("")
    emit("+-class reduction verification (per E, on its first escape):")
    for E in Es:
        i = min(i2 for (E2_, i2, rec, tag, orb) in studied
                if E2_ == E and tag == 'ESC')
        rec = next(r for (E2_, i2, r, tag, orb) in studied
                   if E2_ == E and i2 == i)
        # (a) exact sign-invariance identities on sample sites
        nchk = verify_sign_invariance(F, E, rec, nsample=25)
        emit("  (a) E=%d idx=%d: sign-invariance identities "
             "C(s,s';-t,-t')=C(s,s';t,t') and C(-s,-s';t,t')=-C(s,s';t,t') "
             "hold for C1 and C2 at all sampled sites: %d checks, 0 failures"
             % (E, i, nchk))
        # (b) one full round, no early stop: span(V + results) identical
        out_f, st_f, an_f = one_round_results(F, E, rec, 'full')
        out_h, st_h, an_h = one_round_results(F, E, rec, 'half')
        assert an_f == 0 and an_h == 0
        span_f = init_span(F, rec)
        for enc in sorted(out_f):
            span_f.insert_enc(enc)
        span_h = init_span(F, rec)
        for enc in sorted(out_h):
            span_h.insert_enc(enc)
        cf = rref_canonical(list(span_f.rows.values()))
        ch = rref_canonical(list(span_h.rows.values()))
        emit("  (b) E=%d idx=%d: one full no-early-stop round: full sweep "
             "%d C1 + %d C2 -> %d distinct pairs, span dim %d; +-class sweep "
             "%d C1 + %d C2 -> %d distinct pairs, span dim %d; RREF spans "
             "identical: %s" %
             (E, i, st_f['C1'], st_f['C2'], len(out_f), len(cf),
              st_h['C1'], st_h['C2'], len(out_h), len(ch), cf == ch))
        assert cf == ch
        # (c) full-mode saturate reaches the same verdict
        rh = results[(E, i)]
        rf = saturate(F, E, rec, mode='full', poly_verify=0)
        bf = verify_kill_bruteforce(rf)
        assert bf == set(rf['conds'])
        emit("  (c) E=%d idx=%d: full-enumeration saturate: killed=%s "
             "round=%s conds=%s dims=%s (half-mode: killed=%s round=%s "
             "conds=%s); killed/round agree: %s (final V/conds may differ "
             "for killed runs -- sweep order picks a different first "
             "out-of-module pair)" %
             (E, i, rf['killed'], rf['round'],
              '+'.join(rf['conds']) if rf['conds'] else '-', rf['dims'],
              rh['killed'], rh['round'],
              '+'.join(rh['conds']) if rh['conds'] else '-',
              (rf['killed'], rf['round']) == (rh['killed'], rh['round'])))
        assert (rf['killed'], rf['round']) == (rh['killed'], rh['round'])

    # ---------------- survivor characterisation ----------------
    emit("")
    emit("=" * 72)
    survivors = [(E, i) for (E, i, rec, tag, orb) in studied
                 if tag == 'ESC' and not results[(E, i)]['killed']]
    esc_killed = [(E, i) for (E, i, rec, tag, orb) in studied
                  if tag == 'ESC' and results[(E, i)]['killed']]
    if survivors:
        emit("SURVIVING escape collisions: %d of 21 -- characterisation "
             "(one block per orbit; members identical):" % len(survivors))
        done = set()
        for E, i in survivors:
            orb = orbit_of[(E, i)]
            if orb in done:
                continue
            done.add(orb)
            res = results[(E, i)]
            rec = next(r for (E2_, i2, r, tag, o) in studied
                       if E2_ == E and i2 == i)
            emit("")
            emit("  orbit %s (rep: E=%d idx=%d, lS=%d lS'=%d lrho=%d, "
                 "ord(rho)=%d):" % (orb, E, i, rec['lS'], rec['lSp'],
                                    rec['lrho'],
                                    n1 // gcd(n1, rec['lrho'])))
            emit("    fixed point reached in round %d (no new pairs in a full "
                 "sweep); killed: no; final dim = %d; dim(V ∩ Δ) = %d; "
                 "dom rank = %d; dim(V ∩ (Fx0)) = %d" %
                 (res['rounds'], res['final_dim'], res['dimD'], res['dom'],
                  res['anti']))
            characterize(F, res, emit)
    else:
        emit("SURVIVING escape collisions: none")

    # ---------------- verdict ----------------
    emit("")
    emit("=" * 72)
    rounds_hist = Counter()
    conds_hist = Counter()
    for E, i in esc_killed:
        rounds_hist[results[(E, i)]['round']] += 1
        conds_hist['+'.join(results[(E, i)]['conds'])] += 1
    emit("VERDICT")
    emit("  escapes killed: %d / 21;  kill rounds histogram: %s;  "
         "kill conditions: %s" %
         (len(esc_killed), dict(sorted(rounds_hist.items())),
          dict(sorted(conds_hist.items()))))
    emit("  escapes surviving at depth-%d fixed point: %d / 21" %
         (MAX_ROUNDS, len(survivors)))
    if not survivors:
        emit("  => depth-<=%d composition closure kills ALL 21 escape "
             "collisions: (B2) eliminated by the calculus on GF(3^7) "
             "(both exotic exponents)." % MAX_ROUNDS)
    else:
        emit("  => depth-<=%d composition closure does NOT kill all escapes; "
             "surviving V characterised above." % MAX_ROUNDS)
    ctrl_res = [(E, i) for (E, i, rec, tag, orb) in studied if tag == 'CTRL']
    emit("  controls (trace-killed): %d run, killed %d / %d, rounds: %s, "
         "conds: %s" %
         (len(ctrl_res),
          sum(1 for k in ctrl_res if results[k]['killed']), len(ctrl_res),
          [results[k]['round'] for k in ctrl_res],
          ['+'.join(results[k]['conds']) for k in ctrl_res]))
    emit("total wall time: %.1fs" % (time.time() - t_start))

    outpath = os.path.join(HERE, 'results.txt')
    with open(outpath, 'w') as fh:
        fh.write("\n".join(out_lines) + "\n")
    emit("results written to %s" % outpath)


if __name__ == '__main__':
    main()
