#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Collision-impact measurement for BG App.C Problem 1 certificates.

Field: F = GF(3^q), q in {7, 13}.  U = nonzero squares.
T = {p : p and p-1 both in U}  (Paley points).
Exotic exponents: E in [1, Q-1), odd, E^3 = 1 mod (Q-1), E not a power of 3.
D(p) = p^E - (p-1)^E ; collisions = unordered {p,r} in T, p != r, D(p) = D(r).
Per collision, oriented so that delta = r^E - p^E is a nonzero square
(exactly one orientation works since -1 is a nonsquare):
  E2 = E*E mod (Q-1)
  K_p = (p-1)^E2 - p^E2 ,  K_r = (r-1)^E2 - r^E2
  S  = K_p * (delta^E)^{-1} ,  S' = K_r * (delta^E)^{-1} ,  rho = S'/S.
Criteria (a collision is "killed" when the criterion fires):
  (a) OLD trace:   Tr(S) != 0 or Tr(S') != 0
  (b) NEW A3:      S' = -S           (rho = -1)
  (c) same-coset:  rho = 1           (S' = S, Theorem B)
  (F) Theorem F:   exists another collision j and 0 <= k < q with
                   rho_i = rho_j^(3^k)  and  S_j^(3^k) not in {S_i, -S_i}.
      A collision is F-killed if it belongs to at least one F-firing pair.

Implementation: pure Python 3, no external deps.  GF(3^q) is realised as
GF(3)[X]/(f) with f irreducible (verified by trial division) and X primitive
(verified); all multiplicative arithmetic via exp/log tables, additive
arithmetic via Zech logarithms (hot loop) and digitwise base-3 addition
(everywhere else).  Independent cross-checks against direct polynomial
arithmetic (ppowmod) are built in.
"""

import os
import random
import sys
import time
from array import array
from collections import Counter, defaultdict

# ------------------------------------------------------------------
# GF(3)[X] helpers; polynomials = little-endian coefficient lists
# ------------------------------------------------------------------

def pstrip(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[i + j] = (r[i + j] + ai * bj) % 3
    return pstrip(r)


def pmod(a, f):
    """a mod f, f monic."""
    a = list(a)
    df = len(f) - 1
    for i in range(len(a) - 1, df - 1, -1):
        c = a[i]
        if c:
            a[i] = 0
            base = i - df
            for j in range(df):
                if f[j]:
                    a[base + j] = (a[base + j] - c * f[j]) % 3
    return pstrip(a)


def ppowmod(a, e, f):
    r = [1]
    a = pmod(a, f)
    while e:
        if e & 1:
            r = pmod(pmul(r, a), f)
        a = pmod(pmul(a, a), f)
        e >>= 1
    return r


def poly_from_counter(c, d):
    """monic degree-d poly whose low coefficients are the base-3 digits of c."""
    out = []
    for _ in range(d):
        out.append(c % 3)
        c //= 3
    out.append(1)
    return out


def is_irreducible(f):
    """Trial division by every monic poly of degree 1..deg(f)//2."""
    d = len(f) - 1
    # quick root check first
    for x in (0, 1, 2):
        v = 0
        for c in reversed(f):
            v = (v * x + c) % 3
        if v == 0:
            return False
    for dd in range(1, d // 2 + 1):
        for c in range(3 ** dd):
            g = poly_from_counter(c, dd)
            if not pmod(f, g):
                return False
    return True


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def poly_str(f):
    terms = []
    for i in range(len(f) - 1, -1, -1):
        c = f[i]
        if not c:
            continue
        if i == 0:
            terms.append(str(c))
        elif i == 1:
            terms.append(("" if c == 1 else str(c) + "*") + "X")
        else:
            terms.append(("" if c == 1 else str(c) + "*") + "X^%d" % i)
    return " + ".join(terms)


def elt_order_full(a_poly, f, q, m):
    """True iff a has full order 3^q-1, given 3^q-1 = 2*m with m prime."""
    if ppowmod(a_poly, 2, f) == [1]:
        return False
    if ppowmod(a_poly, m, f) == [1]:
        return False
    return True


def find_generator(f, q, m):
    for enc in range(3, 3 ** q):
        a = []
        e = enc
        while e:
            a.append(e % 3)
            e //= 3
        if elt_order_full(a, f, q, m):
            return enc
    raise RuntimeError("no generator found")


def find_modulus(q):
    """Irreducible monic degree-q poly over GF(3) with X primitive."""
    m = (3 ** q - 1) // 2
    assert is_prime(m)
    X = [0, 1]
    # trinomials first (fast reduction later)
    for k in range(1, q):
        for a in (1, 2):
            for b in (1, 2):
                f = [0] * (q + 1)
                f[q] = 1
                f[k] = a
                f[0] = b
                if is_irreducible(f) and elt_order_full(X, f, q, m):
                    return f
    # generic small-coefficient scan
    for c in range(1, 3 ** q):
        if c % 3 == 0:
            continue
        f = poly_from_counter(c, q)
        if is_irreducible(f) and elt_order_full(X, f, q, m):
            return f
    raise RuntimeError("no primitive modulus found")


# ------------------------------------------------------------------
# The field GF(3^q): exp/log tables, Zech logs, trace
# elements are encoded as base-3 integers (digit i = coeff of X^i)
# ------------------------------------------------------------------

class Field:
    def __init__(self, q, f, slow_gen_enc=None):
        self.q = q
        self.Q = Q = 3 ** q
        self.n1 = n1 = Q - 1
        self.half = half = n1 // 2
        assert half % 2 == 1, "need Q = 3 mod 4 so that -1 is a nonsquare"
        self.f = f
        exp = array('l', [0]) * n1
        log = array('l', [-1]) * Q
        if slow_gen_enc is None:
            # generator g = X; multiply-by-X stepping on integer encodings
            red = [(-f[j]) % 3 for j in range(q)]
            Rterms = [(3 ** j, red[j]) for j in range(q) if red[j]]
            cur = 1
            for k in range(n1):
                exp[k] = cur
                log[cur] = k
                cur *= 3
                if cur >= Q:
                    d, cur = divmod(cur, Q)
                    for pw, r in Rterms:
                        c0 = (cur // pw) % 3
                        c1 = (c0 + d * r) % 3
                        if c1 != c0:
                            cur += (c1 - c0) * pw
            assert cur == 1, "X not primitive under given modulus"
        else:
            g = self.poly_of_enc(slow_gen_enc)
            curp = [1]
            for k in range(n1):
                enc = self.enc_of_poly(curp)
                exp[k] = enc
                log[enc] = k
                curp = pmod(pmul(curp, g), f)
            assert self.enc_of_poly(curp) == 1, "generator order wrong"
        assert log[1] == 0
        assert log.count(-1) == 1 and log[0] == -1, "exp not a bijection onto F*"
        self.exp = exp
        self.log = log
        # Zech logarithms: Z[c] = log(1 + g^c), -1 when 1 + g^c = 0
        Zt = array('l', [-1]) * n1
        for k in range(n1):
            e = exp[k]
            d0 = e % 3
            e1 = e - d0 + (d0 + 1) % 3
            if e1:
                Zt[k] = log[e1]
        assert Zt[half] == -1, "1 + g^half must be 0 (g^half = -1)"
        self.Z = Zt
        # trace basis: Tr is GF(3)-linear; trb[i] = Tr(X^i) in {0,1,2}
        trb = []
        for i in range(q):
            lx = log[3 ** i]
            t = 0
            for j in range(q):
                t = self.add_enc(t, exp[lx * (3 ** j) % n1])
            assert t in (0, 1, 2)
            trb.append(t)
        self.trb = trb
        assert self.trace_enc(1) == q % 3, "Tr(1) must equal q mod 3"
        # cross-checks: trace linearity, Zech vs digitwise addition,
        # exp/log powering vs direct polynomial powering
        rng = random.Random(12345 + q)
        for _ in range(20):
            l = rng.randrange(n1)
            x = exp[l]
            t = 0
            for j in range(q):
                t = self.add_enc(t, exp[l * (3 ** j) % n1])
            assert t == self.trace_enc(x)
        for _ in range(20):
            a = rng.randrange(n1)
            b = rng.randrange(n1)
            s = self.add_enc(exp[a], exp[b])
            ls = self.add_log(a, b)
            assert (s == 0 and ls == -1) or (s != 0 and log[s] == ls)
        for _ in range(5):
            k = rng.randrange(n1)
            e = rng.randrange(1, n1)
            direct = ppowmod(self.poly_of_enc(exp[k]), e, f)
            assert self.enc_of_poly(direct) == exp[k * e % n1]
        # -1 = 1 + 1 = g^half
        assert log[self.add_enc(1, 1)] == half

    # --- representation helpers ---
    def poly_of_enc(self, e):
        out = []
        for _ in range(self.q):
            out.append(e % 3)
            e //= 3
        return pstrip(out)

    def enc_of_poly(self, p):
        e = 0
        for c in reversed(p):
            e = e * 3 + c
        return e

    def digits_of_enc(self, e):
        out = []
        for _ in range(self.q):
            out.append(e % 3)
            e //= 3
        return out

    # --- additive arithmetic on encodings ---
    def add_enc(self, x, y):
        r = 0
        m = 1
        for _ in range(self.q):
            r += ((x % 3 + y % 3) % 3) * m
            x //= 3
            y //= 3
            m *= 3
        return r

    def trace_enc(self, x):
        t = 0
        for i in range(self.q):
            d = x % 3
            x //= 3
            if d:
                t = (t + d * self.trb[i]) % 3
        return t

    # --- log-space arithmetic ---
    def add_log(self, a, b):
        """log(g^a + g^b); -1 if the sum is zero."""
        z = self.Z[(a - b) % self.n1]
        return -1 if z < 0 else (b + z) % self.n1

    def sub_log(self, a, b):
        """log(g^a - g^b); -1 if zero."""
        return self.add_log(a, (b + self.half) % self.n1)


# ------------------------------------------------------------------
# exotic exponents
# ------------------------------------------------------------------

def exotic_exponents(q):
    n1 = 3 ** q - 1
    pows3 = set()
    v = 1
    for _ in range(q):
        pows3.add(v)
        v = v * 3 % n1
    out = [x for x in range(1, n1)
           if x * x % n1 * x % n1 == 1 and x not in pows3]
    for E in out:
        assert E % 2 == 1, "cube roots of 1 mod even n1 must be odd"
    return out, pows3


# ------------------------------------------------------------------
# sanity checks (item 6)
# ------------------------------------------------------------------

def sanity_checks(F, E, rng, emit):
    n1, half = F.n1, F.half
    for _ in range(200):
        lx = rng.randrange(n1)
        x = F.exp[lx]
        nx = F.add_enc(x, x)                    # -x = 2x in char 3
        lnx = F.log[nx]
        assert lnx == (lx + half) % n1
        assert (lx % 2 == 0) != (lnx % 2 == 0)  # exactly one of x, -x square
    for _ in range(50):
        lz = rng.randrange(n1)
        assert lz * E % n1 * E % n1 * E % n1 == lz
        z = F.exp[lz]
        w = F.exp[lz * E % n1]
        w = F.exp[F.log[w] * E % n1]
        w = F.exp[F.log[w] * E % n1]
        assert w == z                            # z^(E^3) = z, field-level
    assert E * E % n1 * E % n1 == 1
    emit("sanity(E=%d): 200x exactly-one-of{x,-x}-is-square OK; "
         "50x z^(E*E*E)=z OK; E^3=1 mod %d OK" % (E, n1))


# ------------------------------------------------------------------
# per-collision record
# ------------------------------------------------------------------

def a1_of(F, a0):
    p = F.exp[a0]
    d0 = p % 3
    return F.log[p - d0 + (d0 + 2) % 3]          # log(p - 1)


def pair_record(F, E, E2, k_p, k_r):
    n1, half = F.n1, F.half
    a0p, a0r = k_p, k_r
    # oriented ordering: delta = r^E - p^E must be a nonzero square
    d_pr = F.sub_log(a0r * E % n1, a0p * E % n1)
    assert d_pr >= 0, "delta = 0 impossible (x -> x^E injective)"
    if d_pr & 1:
        a0p, a0r = a0r, a0p
        dlog = (d_pr + half) % n1
        chk = F.sub_log(a0r * E % n1, a0p * E % n1)
        assert chk == dlog
    else:
        dlog = d_pr
    # exactly one orientation is a square (half odd => parity flips)
    assert dlog % 2 == 0 and ((dlog + half) % n1) % 2 == 1
    a1p = a1_of(F, a0p)
    a1r = a1_of(F, a0r)
    # collision consistency: r1^E - p1^E = delta as well
    d_side1 = F.sub_log(a1r * E % n1, a1p * E % n1)
    assert d_side1 == dlog, "D(p) = D(r) must give r1^E - p1^E = delta"
    lKp = F.sub_log(a1p * E2 % n1, a0p * E2 % n1)
    lKr = F.sub_log(a1r * E2 % n1, a0r * E2 % n1)
    assert lKp >= 0 and lKr >= 0
    ldE = dlog * E % n1
    lS = (lKp - ldE) % n1
    lSp = (lKr - ldE) % n1
    lrho = (lSp - lS) % n1
    trS = F.trace_enc(F.exp[lS])
    trSp = F.trace_enc(F.exp[lSp])
    return {'a0p': a0p, 'a0r': a0r, 'dlog': dlog, 'lS': lS, 'lSp': lSp,
            'lrho': lrho, 'trS': trS, 'trSp': trSp}


# ------------------------------------------------------------------
# Theorem F criterion
# ------------------------------------------------------------------

def f_criterion(F, recs):
    """Exact bucket algorithm.

    Fire(i,j) <=> ex. k: rho_i = rho_j^(3^k) and S_j^(3^k) not in {S_i,-S_i}.
    Bucket collisions by the Frobenius orbit of rho.  q is prime, so orbits
    have length 1 (rho in GF(3)*, i.e. rho = 1 or rho = -1) or length q.

    Length-q bucket: unique matching k per pair; normalising each member by
    its argmin twist k* (V = S^(3^k*), W = class of V mod +-1), fire(i,j)
    <=> W_i != W_j.  So all members are killed iff the bucket carries >= 2
    distinct W classes.

    rho = +-1 bucket: every k matches; fire(i,j) fails only when S_i and S_j
    are both in GF(3)* (Frobenius-fixed scalars, orbit inside {S_i,-S_i}).
    So if the bucket has >= 2 members and at least one non-scalar S, every
    member is killed; otherwise none.
    """
    q, n1, half = F.q, F.n1, F.half
    pow3 = [3 ** k for k in range(q)]
    buckets = defaultdict(list)
    Wval = {}
    for idx, r in enumerate(recs):
        lr = r['lrho']
        if lr == 0:
            buckets[(0, 0)].append(idx)          # rho = 1
        elif lr == half:
            buckets[(0, 1)].append(idx)          # rho = -1
        else:
            orb = [lr * pw % n1 for pw in pow3]
            assert len(set(orb)) == q            # full orbit (q prime)
            rep = min(orb)
            kstar = orb.index(rep)
            lV = r['lS'] * pow3[kstar] % n1
            Wval[idx] = min(lV, (lV + half) % n1)
            buckets[(1, rep)].append(idx)
    killed = set()
    for key, mem in buckets.items():
        if key[0] == 1:
            if len({Wval[i] for i in mem}) >= 2:
                killed.update(mem)
        else:
            if len(mem) >= 2 and any(recs[i]['lS'] not in (0, half) for i in mem):
                killed.update(mem)
    return killed


def f_bruteforce(F, recs):
    """O(C^2 q) direct check; returns (killed_both_members, killed_i_only)."""
    q, n1, half = F.q, F.n1, F.half
    pow3 = [3 ** k for k in range(q)]
    C = len(recs)
    lr = [r['lrho'] for r in recs]
    lS = [r['lS'] for r in recs]
    killed = set()
    killed_i = set()
    for i in range(C):
        for j in range(C):
            if i == j:
                continue
            fired = False
            for k in range(q):
                if lr[i] == lr[j] * pow3[k] % n1:
                    sjk = lS[j] * pow3[k] % n1
                    if sjk != lS[i] and sjk != (lS[i] + half) % n1:
                        fired = True
                        break
            if fired:
                killed.add(i)
                killed.add(j)
                killed_i.add(i)
    return killed, killed_i


# ------------------------------------------------------------------
# main per-E analysis
# ------------------------------------------------------------------

def elt_line(F, l):
    return "g^%d=%s" % (l, F.digits_of_enc(F.exp[l]))


def analyze_E(F, E, emit, expect_fibers=None, expect_collisions=None,
              detail_table=False, escape_cap=40):
    q, n1, half, Q = F.q, F.n1, F.half, F.Q
    exp, log, Z = F.exp, F.log, F.Z
    E2 = E * E % n1
    t0 = time.time()
    emit("")
    emit("--- q=%d, E = %d   (E mod (Q-1)/2 = %d, E^2 mod (Q-1) = %d) ---"
         % (q, E, E % half, E2))
    # ---- T scan + fibers of D ----
    first = {}
    multi = {}
    for k in range(0, n1, 2):                    # p = g^k runs over U
        p = exp[k]
        d0 = p % 3
        p1e = p - d0 + (d0 + 2) % 3              # p - 1
        if p1e == 0:
            continue
        a1 = log[p1e]
        if a1 & 1:                               # p-1 must be a square
            continue
        la = k * E % n1                          # log p^E
        lb = (a1 * E + half) % n1                # log(-(p-1)^E)
        z = Z[(la - lb) % n1]
        if z < 0:
            raise AssertionError("D(p) = 0 impossible")
        Dl = (lb + z) % n1                       # log D(p)
        if Dl in multi:
            multi[Dl].append(k)
        elif Dl in first:
            multi[Dl] = [first.pop(Dl), k]
        else:
            first[Dl] = k
    Tsize = len(first) + sum(len(v) for v in multi.values())
    emit("|T| = %d (expected (Q-3)/4 = %d)" % (Tsize, (Q - 3) // 4))
    assert Tsize == (Q - 3) // 4
    sizes = Counter(len(v) for v in multi.values())
    sizes[1] = len(first)
    del first
    emit("fiber size distribution of D on T: %s" % dict(sorted(sizes.items())))
    if expect_fibers is not None:
        mism = {s: (sizes.get(s, 0), c) for s, c in expect_fibers.items()
                if sizes.get(s, 0) != c}
        extra = {s: c for s, c in sizes.items() if s >= 2 and s not in expect_fibers}
        ok = not mism and not extra
        emit("expected multi-fiber sizes %s: %s" %
             (expect_fibers, "MATCH" if ok else
              "*** MISMATCH *** got_vs_expected=%s extra=%s" % (mism, extra)))
    ncoll = sum(s * (s - 1) // 2 * c for s, c in sizes.items())
    # ---- collision records ----
    recs = []
    for Dl, ms in multi.items():
        L = len(ms)
        for i in range(L):
            for j in range(i + 1, L):
                recs.append(pair_record(F, E, E2, ms[i], ms[j]))
    del multi
    C = len(recs)
    assert C == ncoll
    msg = "collisions (unordered pairs {p,r} with D(p)=D(r)): %d" % C
    if expect_collisions is not None:
        msg += "  (expected %d: %s)" % (expect_collisions,
                                        "MATCH" if C == expect_collisions
                                        else "*** MISMATCH ***")
    emit(msg)
    # ---- criteria ----
    killed_a = {i for i, r in enumerate(recs) if r['trS'] != 0 or r['trSp'] != 0}
    killed_b = {i for i, r in enumerate(recs) if r['lrho'] == half}
    killed_c = {i for i, r in enumerate(recs) if r['lrho'] == 0}
    killed_F = f_criterion(F, recs)
    if C <= 400:
        bf, bf_i = f_bruteforce(F, recs)
        emit("F cross-check (brute force O(C^2 q)): %s; "
             "i-only vs both-members interpretation identical: %s" %
             ("MATCH" if bf == killed_F else "*** MISMATCH ***", bf == bf_i))
        assert bf == killed_F
    union = killed_a | killed_b | killed_c | killed_F
    escapes = [i for i in range(C) if i not in union]
    emit("killed by (a) Tr(S)!=0 or Tr(S')!=0 : %d" % len(killed_a))
    emit("killed by (b) S' = -S  (rho = -1)   : %d" % len(killed_b))
    emit("killed by (c) rho = 1  (S' = S)     : %d" % len(killed_c))
    emit("killed by (F) equal-ratio Frobenius : %d" % len(killed_F))
    emit("killed by union (a|b|c|F)           : %d" % len(union))
    emit("ESCAPES (killed by none)            : %d" % len(escapes))
    emit("overlaps: a&b=%d a&c=%d a&F=%d b&c=%d b&F=%d c&F=%d" %
         (len(killed_a & killed_b), len(killed_a & killed_c),
          len(killed_a & killed_F), len(killed_b & killed_c),
          len(killed_b & killed_F), len(killed_c & killed_F)))
    for i in escapes[:escape_cap]:
        r = recs[i]
        emit("  ESCAPE #%d:" % i)
        emit("    p0=%s  r0=%s" % (elt_line(F, r['a0p']), elt_line(F, r['a0r'])))
        emit("    delta=g^%d  S=%s  S'=%s" %
             (r['dlog'], elt_line(F, r['lS']), elt_line(F, r['lSp'])))
        emit("    rho=%s  Tr(S)=%d Tr(S')=%d" %
             (elt_line(F, r['lrho']), r['trS'], r['trSp']))
    if len(escapes) > escape_cap:
        emit("  ... and %d more escapes (suppressed)" % (len(escapes) - escape_cap))
    if detail_table:
        emit("per-collision table (logs; flags: a=trace b=S'=-S c=rho=1 F):")
        emit(" idx | p0_log r0_log |  dlog |    lS   lS'   lrho | TrS TrS' | a b c F")
        for i, r in enumerate(recs):
            emit(" %3d | %6d %6d | %5d | %5d %5d %6d | %3d %4d | %s %s %s %s" %
                 (i, r['a0p'], r['a0r'], r['dlog'], r['lS'], r['lSp'],
                  r['lrho'], r['trS'], r['trSp'],
                  'x' if i in killed_a else '.',
                  'x' if i in killed_b else '.',
                  'x' if i in killed_c else '.',
                  'x' if i in killed_F else '.'))
    emit("(analysis time %.1fs)" % (time.time() - t0))
    return {'C': C, 'a': len(killed_a), 'b': len(killed_b), 'c': len(killed_c),
            'F': len(killed_F), 'union': len(union), 'escapes': len(escapes)}


# ------------------------------------------------------------------
# main
# ------------------------------------------------------------------

def main():
    t_start = time.time()
    lines = []

    def emit(s=""):
        print(s, flush=True)
        lines.append(s)

    rng = random.Random(20260812)
    summary = []

    emit("Collision-impact measurement, BG App.C Problem 1 (exotic exponents)")
    emit("python %s" % sys.version.split()[0])

    # ================= q = 7 =================
    emit("")
    emit("=" * 72)
    q = 7
    Q = 3 ** q
    n1 = Q - 1
    m = n1 // 2
    emit("q = 7 : Q = %d, Q-1 = %d, (Q-1)/2 = %d (prime: %s)"
         % (Q, n1, m, is_prime(m)))
    assert is_prime(m)
    f7 = [1, 0, 2, 0, 0, 0, 0, 1]                 # X^7 + 2X^2 + 1
    irr7 = is_irreducible(f7)
    emit("modulus f = %s : irreducible over GF(3) "
         "(trial division by all monic polys of degree <= 3): %s"
         % (poly_str(f7), irr7))
    assert irr7
    prim7 = elt_order_full([0, 1], f7, q, m)
    emit("X primitive mod f: %s" % prim7)
    if prim7:
        F7 = Field(q, f7)
        emit("generator g = X; exp/log/Zech/trace tables built and cross-checked")
    else:
        gen = find_generator(f7, q, m)
        emit("X NOT primitive; using generator enc=%d (slow build)" % gen)
        F7 = Field(q, f7, slow_gen_enc=gen)
    emit("-1 = g^%d = g^half, half odd => -1 is a nonsquare: verified"
         % F7.log[F7.add_enc(1, 1)])
    Es7, _ = exotic_exponents(q)
    emit("exotic exponents (odd E, E^3=1 mod %d, E not a power of 3): %s"
         % (n1, Es7))
    ok = set(Es7) == {151, 941}
    emit("matches expected {151, 941}: %s%s"
         % (ok, "" if ok else "   *** ANOMALY ***"))
    emit("check: 151^2 mod %d = %d, 151*941 mod %d = %d "
         "(mutual squares = mutual inverses)"
         % (n1, 151 * 151 % n1, n1, 151 * 941 % n1))
    for E in Es7:
        sanity_checks(F7, E, rng, emit)
        st = analyze_E(F7, E, emit, expect_fibers={2: 49, 3: 7},
                       expect_collisions=70, detail_table=True)
        summary.append((7, E, st))

    # ================= q = 13 =================
    emit("")
    emit("=" * 72)
    q = 13
    Q = 3 ** q
    n1 = Q - 1
    m = n1 // 2
    emit("q = 13 : Q = %d, Q-1 = %d, (Q-1)/2 = %d (prime: %s)"
         % (Q, n1, m, is_prime(m)))
    assert is_prime(m)
    t = time.time()
    f13 = find_modulus(q)
    emit("modulus f = %s : irreducible (trial division deg <= 6), "
         "X primitive (found in %.1fs)" % (poly_str(f13), time.time() - t))
    t = time.time()
    F13 = Field(q, f13)
    emit("exp/log/Zech/trace tables built and cross-checked in %.1fs"
         % (time.time() - t))
    t = time.time()
    Es13, _ = exotic_exponents(q)
    emit("exotic exponents (E^3=1 mod %d, not a power of 3, found in %.1fs): %s"
         % (n1, time.time() - t, Es13))
    emit("count = %d (expected 2)%s"
         % (len(Es13), "" if len(Es13) == 2 else "   *** ANOMALY ***"))
    if len(Es13) == 2:
        emit("check: E0^2 mod (Q-1) = %d (= E1: %s); E mod (Q-1)/2: %s"
             % (Es13[0] * Es13[0] % n1,
                Es13[0] * Es13[0] % n1 == Es13[1],
                [E % m for E in Es13]))
    emit("note: full T enumeration used (|T| = %d); the 20000-point sampling"
         % ((Q - 3) // 4))
    emit("fallback from the task brief was not needed.")
    for E in Es13:
        sanity_checks(F13, E, rng, emit)
        st = analyze_E(F13, E, emit, escape_cap=40)
        summary.append((13, E, st))

    # ================= summary =================
    emit("")
    emit("=" * 72)
    emit("SUMMARY   q        E       C    (a)    (b)    (c)     (F)  union  escapes")
    for (qq, E, st) in summary:
        emit("        %2d %8d %7d %6d %6d %6d %7d %6d %8d"
             % (qq, E, st['C'], st['a'], st['b'], st['c'],
                st['F'], st['union'], st['escapes']))
    emit("total wall time: %.1fs" % (time.time() - t_start))

    outdir = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(outdir, "results.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    emit("results written to %s" % os.path.join(outdir, "results.txt"))


if __name__ == "__main__":
    main()
