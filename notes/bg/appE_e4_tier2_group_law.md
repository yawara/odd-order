# BG E.4 Tier 2: Q₆ Lazard 群法則の導出記録 (issue 3027, 2026-07-21)

`OddOrder/BG/AppE_FiliformGroup.lean` の `gmul` (scaled 整数係数 BCH 法則) の導出・検証
スクリプトと、WP3 以降で使う commutator 座標公式の永続記録。session scratchpad は揮発性
なのでここに保存する。

## 使い方

`python3` で下の 2 つのコードブロックを順に (同一ディレクトリで `derive_group_law.py`,
`emit_scaled.py` として) 実行すると、全記号検証 (Friedrichs / assoc / unit / inv / power /
grading / 整数性) を再実行し、Lean 転記用の多項式を再出力する。sympy 1.14 で確認済。

## WP3 で使う commutator 座標公式 (scaled、mod 197 の整数係数)

`gcomm x y := gmul (gmul (gmul x y) (-x)) (-y)` (= ⁅x,y⁆ = x y x⁻¹ y⁻¹ の座標)。

| 式 | 座標 (0..5) |
|---|---|
| `gcomm x eA` | `(0, 0, -2x₁, -6x₁², -4x₁³, -30x₀x₁³ - 60x₁³ - 60x₁²x₂ + 30x₁x₃ - 30x₄)` |
| `gcomm x eB` | `(0, 0, 2x₀, 6x₀x₁ + 6x₀ - 6x₂, 4x₀x₁² + 6x₀x₁ + 4x₀ - 6x₁x₂ - 6x₂ - 2x₃, 30x₀²x₁² + 60x₀² - 60x₀x₃ - 90x₂²)` |
| `gcomm x e4` | `(0, 0, 0, 0, 0, 30x₀)` |
| `gcomm x e5` | `(0, 0, 0, 0, 0, 0)` (e₅ 中心的) |
| `gcomm x (0,0,0,0,s,t)` | `(0, 0, 0, 0, 0, 30·s·x₀)` (Z₂ 平面の中心化 ⟺ x₀ = 0) |
| `gmul x v − gmul v x` | `(0, 0, 2x₀-2x₁, -6x₂, -2x₀x₁+2x₁²-2x₃, 30x₁x₂-30x₄)` (三角 solve → C(v) = {c•v + t•e₅}) |
| `gcomm eB e2` | `(0, 0, 0, 6, 6, 90)` (≠ 0 = T 非可換 witness) |

Z₁/Z₂ 上界の三角 solve (WP3):
- **Z₁ ≤ e₅-line**: eA から x₁=0, x₄=0 (c2, c5); eB から x₀=0, x₂=0, x₃=0 (c2, c3, c4)。
- **Z₂ ≤ {x₀=x₁=x₂=x₃=0}**: ⁅x,y⁆ ∈ Z₁ (座標 2..4 = 0) を eA (→x₁=0)・eB (→x₀=0, 次いで
  c3→x₂=0, c4→x₃=0) に適用。
- **C(Z₂ 平面) = {x₀=0} = T**、`bg, e2g ∈ T`、`gcomm eB e2 ≠ 0` ⟹ T 非可換。

係数の可逆性: 2, 4, 6, 30, 60, 90 は全て 197 と互いに素。

## script 1: `derive_group_law.py` (PBW straightening + BCH + 全検証)

```python
#!/usr/bin/env python3
"""WP1 (issue 3027): derive the Lazard group law of Q6 over Q, verify everything
symbolically, and emit Lean-ready polynomials mod 197.

Method: truncated universal enveloping algebra U(L)/(weight > 5), PBW basis with
order a < b < e2 < e3 < e4 < e5.  Group law z = log(exp(x) * exp(y)) (BCH,
coordinates of the first kind).  Friedrichs check: log lands exactly on the
6 single-generator monomials.
"""
import sympy as sp
from functools import lru_cache
from fractions import Fraction

W = [1, 1, 2, 3, 4, 5]          # weights of a, b, e2, e3, e4, e5
MAXW = 5
NGEN = 6

# bracket table for g < h:  [g,h] = sum coeff * generator
BR = {(0, 1): {2: 1}, (1, 2): {3: 1}, (1, 3): {4: 1}, (0, 4): {5: 1}, (2, 3): {5: 1}}

def wt_word(word):
    return sum(W[g] for g in word)

@lru_cache(maxsize=None)
def straighten(word):
    """word: tuple of generator indices -> dict {exponent-tuple: Fraction coeff}"""
    if wt_word(word) > MAXW:
        return {}
    # find first descent
    for i in range(len(word) - 1):
        u, v = word[i], word[i + 1]
        if u > v:
            out = {}
            # u v = v u + [u,v],  [u,v] = -[v,u]
            for mono, c in straighten(word[:i] + (v, u) + word[i + 2:]).items():
                out[mono] = out.get(mono, Fraction(0)) + c
            br = BR.get((v, u), {})
            for g, cg in br.items():
                for mono, c in straighten(word[:i] + (g,) + word[i + 2:]).items():
                    out[mono] = out.get(mono, Fraction(0)) - cg * c
            return {m: c for m, c in out.items() if c != 0}
    # sorted word -> exponent tuple
    exp = [0] * NGEN
    for g in word:
        exp[g] += 1
    return {tuple(exp): Fraction(1)}

def mono_to_word(mono):
    w = []
    for g in range(NGEN):
        w.extend([g] * mono[g])
    return tuple(w)

def wt_mono(mono):
    return sum(W[g] * mono[g] for g in range(NGEN))

# ---- element arithmetic: dict {mono: sympy expr} ----
def eadd(a, b, s=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = sp.expand(out.get(m, 0) + s * c)
        if out[m] == 0:
            del out[m]
    return out

def escale(a, s):
    return {m: sp.expand(s * c) for m, c in a.items() if sp.expand(s * c) != 0}

def emul(a, b):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            if wt_mono(m1) + wt_mono(m2) > MAXW:
                continue
            for m, c in straighten(mono_to_word(m1) + mono_to_word(m2)).items():
                out[m] = out.get(m, 0) + c1 * c2 * sp.Rational(c.numerator, c.denominator)
    return {m: sp.expand(c) for m, c in out.items() if sp.expand(c) != 0}

ONE = {tuple([0] * NGEN): sp.Integer(1)}

def eexp(x):  # x with zero constant term
    out = dict(ONE)
    p = dict(ONE)
    for k in range(1, MAXW + 1):
        p = emul(p, x)
        out = eadd(out, p, sp.Rational(1, sp.factorial(k)))
    return out

def elog(P):  # P with constant term 1
    u = eadd(P, ONE, -1)
    out = {}
    p = dict(ONE)
    for k in range(1, MAXW + 1):
        p = emul(p, u)
        out = eadd(out, p, sp.Rational((-1) ** (k + 1), k))
    return out

def gen_elt(coeffs):
    """coeffs: list of 6 sympy exprs -> element sum coeffs[i] * gen_i"""
    out = {}
    for i in range(NGEN):
        if coeffs[i] != 0:
            m = tuple(1 if j == i else 0 for j in range(NGEN))
            out[m] = coeffs[i]
    return out

def extract_law(z):
    """z must be supported on single-generator monomials; return list of 6 coords."""
    coords = [sp.Integer(0)] * NGEN
    for m, c in z.items():
        tot = sum(m)
        if tot == 0:
            assert sp.expand(c) == 0, f"constant term {c}"
            continue
        if tot == 1:
            coords[m.index(1)] = sp.expand(c)
        else:
            assert sp.expand(c) == 0, f"FRIEDRICHS FAIL on {m}: {c}"
    return coords

xs = sp.symbols('x0:6')
ys = sp.symbols('y0:6')
zs = sp.symbols('z0:6')

X = gen_elt(list(xs))
Y = gen_elt(list(ys))
Zlaw = elog(emul(eexp(X), eexp(Y)))
phi = extract_law(Zlaw)
print("== Friedrichs check PASS (law is a Lie element) ==")
for i in range(NGEN):
    print(f"phi[{i}] =", sp.expand(phi[i]))

def apply_phi(a, b):
    sub = {}
    for i in range(NGEN):
        sub[xs[i]] = a[i]
        sub[ys[i]] = b[i]
    return [sp.expand(p.subs(sub, simultaneous=True)) for p in phi]

# unit, inverse, powers
ZERO6 = [sp.Integer(0)] * 6
assert apply_phi(list(xs), ZERO6) == [sp.expand(v) for v in xs], "right unit FAIL"
assert apply_phi(ZERO6, list(ys)) == [sp.expand(v) for v in ys], "left unit FAIL"
assert all(sp.expand(v) == 0 for v in apply_phi(list(xs), [-v for v in xs])), "inverse FAIL"
c = sp.Symbol('c')
pw = apply_phi(list(xs), [c * v for v in xs])
assert all(sp.expand(pw[i] - (1 + c) * xs[i]) == 0 for i in range(6)), "power FAIL"
print("== unit / inverse / phi(x,cx)=(1+c)x PASS ==")

# associativity
lhs = apply_phi(apply_phi(list(xs), list(ys)), list(zs))
rhs = apply_phi(list(xs), apply_phi(list(ys), list(zs)))
for i in range(6):
    assert sp.expand(lhs[i] - rhs[i]) == 0, f"ASSOC FAIL coord {i}"
print("== associativity PASS ==")

# grading check (=> beta-equivariance for exact additive weights)
VW = {xs[i]: W[i] for i in range(6)} | {ys[i]: W[i] for i in range(6)}
for i in range(6):
    for mono in sp.Poly(phi[i], *xs, *ys).monoms():
        wsum = 0
        for v, e in zip(list(xs) + list(ys), mono):
            wsum += VW[v] * e
        assert wsum == W[i], f"GRADING FAIL coord {i} mono {mono}"
print("== grading (beta-equivariance) PASS ==")

# group commutator
def neg(a):
    return [-v for v in a]
comm = apply_phi(apply_phi(apply_phi(list(xs), list(ys)), neg(list(xs))), neg(list(ys)))
print("== group commutator ==")
for i in range(6):
    print(f"comm[{i}] =", sp.expand(comm[i]))

# specific values for the Lean proofs
def basis(i):
    return [sp.Integer(1) if j == i else sp.Integer(0) for j in range(6)]
vvec = [sp.Integer(1), sp.Integer(1), 0, 0, 0, 0]

def show(name, coords):
    print(name, "=", [sp.expand(v) for v in coords])

show("comm(x, eA)", apply_phi(apply_phi(apply_phi(list(xs), basis(0)), neg(list(xs))), neg(basis(0))))
show("comm(x, eB)", apply_phi(apply_phi(apply_phi(list(xs), basis(1)), neg(list(xs))), neg(basis(1))))
show("comm(x, e4)", apply_phi(apply_phi(apply_phi(list(xs), basis(4)), neg(list(xs))), neg(basis(4))))
show("phi(x,v)-phi(v,x)", [sp.expand(u - w) for u, w in
                           zip(apply_phi(list(xs), vvec), apply_phi(vvec, list(xs)))])
show("comm(eB, e2)", apply_phi(apply_phi(apply_phi(basis(1), basis(2)), neg(basis(1))), neg(basis(2))))

# ---- numeric spot checks mod 197 ----
P = 197
import random
random.seed(11)
def phi_num(a, b):
    sub = {xs[i]: a[i] for i in range(6)} | {ys[i]: b[i] for i in range(6)}
    out = []
    for p in phi:
        r = sp.Rational(sp.expand(p.subs(sub, simultaneous=True)))
        out.append((r.p * pow(r.q, P - 2, P)) % P)
    return out
for _ in range(3):
    a = [random.randrange(P) for _ in range(6)]
    # x^197 = 1 via x^k = k x (proved symbolically above), but check by repeated mult:
    acc = a[:]
    for _ in range(P - 1):
        acc = phi_num(acc, a)
    assert acc == [0] * 6, "exponent-p FAIL"
print("== exponent 197 numeric PASS ==")

# ---- Lean output mod 197 ----
def lean_poly(expr, vmap):
    expr = sp.expand(expr)
    poly = sp.Poly(expr, *sorted(vmap.keys(), key=str))
    terms = []
    for mono, coeff in zip(poly.monoms(), poly.coeffs()):
        q = Fraction(sp.Rational(coeff).p, sp.Rational(coeff).q)
        cm = (q.numerator * pow(q.denominator, P - 2, P)) % P
        if cm == 0:
            continue
        factors = []
        for v, e in zip(sorted(vmap.keys(), key=str), mono):
            for _ in range(e):
                factors.append(vmap[v])
        if not factors:
            terms.append(f"{cm}")
        elif cm == 1:
            terms.append(" * ".join(factors))
        else:
            terms.append(f"{cm} * " + " * ".join(factors))
    return " + ".join(terms) if terms else "0"

vmap = {xs[i]: f"x {i}" for i in range(6)} | {ys[i]: f"y {i}" for i in range(6)}
print("\n== LEAN group law (coefficients mod 197) ==")
for i in range(6):
    print(f"  coord {i}: {lean_poly(phi[i], vmap)}")
print("\n== LEAN group commutator (mod 197) ==")
for i in range(6):
    print(f"  coord {i}: {lean_poly(comm[i], vmap)}")
```

## script 2: `emit_scaled.py` (rescale diag(1,1,2,12,24,720) → 整数係数化 + 再検証)

```python
import sympy as sp
from fractions import Fraction
exec(open('derive_group_law.py').read().split("# ---- numeric spot checks")[0])

MU = [1, 1, 2, 12, 24, 720]   # z_i' = MU[i] * z_i  (basis e_i' = e_i / MU[i])

def scale_law(coords, invars):
    """coords: exprs in xs/ys (unscaled). Return scaled: mu_k * coords[k](x->x/mu, y->y/mu)."""
    sub = {}
    for i in range(6):
        for v in invars:
            sub[v[i]] = v[i] / MU[i]
    return [sp.expand(MU[k] * coords[k].subs(sub, simultaneous=True)) for k in range(6)]

phiS = scale_law(phi, [xs, ys])

# integrality + re-verify everything for the scaled law
def apply_phiS(a, b):
    sub = {xs[i]: a[i] for i in range(6)} | {ys[i]: b[i] for i in range(6)}
    return [sp.expand(p.subs(sub, simultaneous=True)) for p in phiS]

for k in range(6):
    for c in sp.Poly(phiS[k], *xs, *ys).coeffs():
        assert sp.Rational(c).q == 1, f"NOT INTEGER coord {k}: {c}"
print("== scaled law has INTEGER coefficients ==")

lhs = apply_phiS(apply_phiS(list(xs), list(ys)), list(zs))
rhs = apply_phiS(list(xs), apply_phiS(list(ys), list(zs)))
assert all(sp.expand(lhs[i] - rhs[i]) == 0 for i in range(6)), "scaled assoc FAIL"
assert apply_phiS(list(xs), [sp.Integer(0)]*6) == [sp.expand(v) for v in xs]
assert apply_phiS([sp.Integer(0)]*6, list(ys)) == [sp.expand(v) for v in ys]
assert all(sp.expand(v) == 0 for v in apply_phiS([-v for v in xs], list(xs))), "neg-left FAIL"
c = sp.Symbol('c')
pw = apply_phiS([c * v for v in xs], list(xs))
assert all(sp.expand(pw[i] - (c + 1) * xs[i]) == 0 for i in range(6)), "power FAIL"
print("== scaled: assoc/unit/neg-left/power PASS ==")

# grading still exact
VW = {xs[i]: W[i] for i in range(6)} | {ys[i]: W[i] for i in range(6)}
for i in range(6):
    for mono in sp.Poly(phiS[i], *xs, *ys).monoms():
        wsum = sum(VW[v] * e for v, e in zip(list(xs) + list(ys), mono))
        assert wsum == W[i], f"GRADING FAIL {i}"
print("== scaled grading PASS ==")

def neg(a): return [-v for v in a]
commS = apply_phiS(apply_phiS(apply_phiS(list(xs), list(ys)), neg(list(xs))), neg(list(ys)))
for k in range(6):
    if commS[k] != 0:
        for co in sp.Poly(commS[k], *xs, *ys).coeffs():
            assert sp.Rational(co).q == 1, f"comm NOT INT coord {k}"
print("== scaled commutator INTEGER ==")

def basis(i): return [sp.Integer(1) if j == i else sp.Integer(0) for j in range(6)]
vvec = [sp.Integer(1), sp.Integer(1), 0, 0, 0, 0]
def commS_at(a, b):
    return apply_phiS(apply_phiS(apply_phiS(a, b), neg(a)), neg(b))

def show(name, coords):
    print(name, "=", [sp.expand(v) for v in coords])
show("comm(x,eA)", commS_at(list(xs), basis(0)))
show("comm(x,eB)", commS_at(list(xs), basis(1)))
show("comm(x,e4)", commS_at(list(xs), basis(4)))
show("comm(x,e5)", commS_at(list(xs), basis(5)))
show("phi(x,v)-phi(v,x)", [sp.expand(u - w) for u, w in zip(apply_phiS(list(xs), vvec), apply_phiS(vvec, list(xs)))])
show("comm(eB,e2)", commS_at(basis(1), basis(2)))
# generic z in e4-e5 plane commutes-check data
zz = [sp.Integer(0), sp.Integer(0), sp.Integer(0), sp.Integer(0), sp.Symbol('s'), sp.Symbol('t')]
show("comm(x, (0,0,0,0,s,t))", commS_at(list(xs), zz))
# beta^7-scalar sanity is weight-based, unchanged.

def lean_int_poly(expr, vmap):
    expr = sp.expand(expr)
    vs = sorted(vmap.keys(), key=str)
    poly = sp.Poly(expr, *vs)
    terms = []
    for mono, coeff in zip(poly.monoms(), poly.coeffs()):
        n = int(coeff)
        if n == 0: continue
        factors = []
        for v, e in zip(vs, mono):
            factors.extend([vmap[v]] * e)
        mstr = " * ".join(factors) if factors else ""
        sgn = "-" if n < 0 else "+"
        an = abs(n)
        if not factors: t = f"{an}"
        elif an == 1: t = mstr
        else: t = f"{an} * {mstr}"
        terms.append((sgn, t))
    if not terms: return "0"
    out = ""
    for i, (sgn, t) in enumerate(terms):
        out = (("-" + t) if sgn == "-" else t) if i == 0 else out + f" {sgn} {t}"
    return out

vmap = {xs[i]: f"x {i}" for i in range(6)} | {ys[i]: f"y {i}" for i in range(6)}
print("\n== LEAN scaled INTEGER law ==")
for i in range(6):
    print(f"COORD{i}: {lean_int_poly(phiS[i], vmap)}")
print("\n== LEAN scaled commutator ==")
for i in range(6):
    print(f"CCOORD{i}: {lean_int_poly(commS[i], vmap)}")
```
