# Keystone build plan — `dim E₀ = dim E_m + 1` (BG (2.11), the SOLE remaining input for Thm 2.5)

**Status (2026-06-07, `bg-reptower`).** Everything in Thm 2.5 EXCEPT this keystone is done +
axiom-clean (see `s03_extraspecial_blocker.md`): full Prop 2.4 (a,c,d,g,h,j,k), `prop24j_fin`/
`prop24k_fin`, and BOTH Thm 2.5 conclusions conditional on the keystone (`ExtraspecialThm25.lean`).
Keystone scaffolding done: `isInternal_cyclicEndConjEigenspaceFin` (`End V = ⊕_m E_m`).

The keystone says: for the Thm 2.5 setup (`G = P ⋊ ⟨x⟩`, `P` extraspecial order `q^{1+2n}`,
`ρ : G → GL(V)` faithful, `C_P(xᵏ) = Z(P)` for `xᵏ ≠ 1`, `char F ∤ |G|`, `F` alg-closed),
the conjugation `εᵐ`-eigenspaces `E_m` on `End V` satisfy `dim E₀ = dim E_m + 1` for `m ≢ 0`.

## Three pieces (each substantial new infrastructure — NOT quick)

### (P1) Diagonalized-trace formula — `tr(c_{xᵏ}) = ∑_m εᵐᵏ · dim E_m`
- Have `End V = ⊕_m E_m` (`isInternal_cyclicEndConjEigenspaceFin`); `c_{xᵏ} = (cyclicEndConj g)^k`
  acts as the SCALAR `εᵐᵏ` on `E_m`.
- mathlib gap: NO `trace`-over-`IsInternal` lemma. Building block available: `LinearMap.IsProj.trace`
  (`tr(proj onto p) = finrank p`, needs `Module.Free` on `p` + `ker`, both auto over a field).
- Route: write `c_{xᵏ} = ∑_m εᵐᵏ • projₘ` (spectral form over the internal sum), then
  `tr = ∑_m εᵐᵏ · tr(projₘ) = ∑_m εᵐᵏ · dim E_m`. Build a GENERAL reusable lemma
  `trace_eq_sum_smul_finrank_of_isInternal` (IsInternal `E` + `f|_{Eᵢ} = cᵢ • id` ⟹
  `tr f = ∑ᵢ cᵢ • finrank Eᵢ`). ~60-100 LOC.
- NOTE: this is a FIELD equation in `F`.

### (P2) THE deep core — `tr(c_{xᵏ}) = 1` for `xᵏ ≠ 1` (and `= q²` for `k=0`)
- Needs the **`P ⋊ ⟨x⟩` extraspecial Burnside-basis framework** (the large lift; not yet present —
  the generic machinery above is stated for an abstract `g : GL(V)`).
- Burnside basis: `{ρ(t) : t ∈ transversal of Z in P}` is a basis of `End V`. Spanning from
  Prop 2.1 (`asAlgebraHom_surjective_of_isAlgClosed`, DONE) + `center_isScalar` (DONE,
  `ρ(gz)=λ(z)ρ(g)`); cardinality `|P/Z| = (dim V)²` from `sq_finrank_eq_card_quotient_center`
  (DONE, Gor 5.5.5a). A spanning family of size `finrank` is a basis
  (`basisOfTopLeSpanOfCardEqFinrank` or similar).
- Monomial action: `c_x ρ(t) = ρ(xtx⁻¹) = λ·ρ(t')` (`t'` = rep of `xtx⁻¹ Z`); `c_x` is a monomial
  matrix on the basis. `tr(c_{xᵏ}) = ∑_{t : xᵏ-fixed in P/Z} (scalar)`. `C_{P/Z}(xᵏ)=1`
  (from `C_P(xᵏ)=Z`) ⟹ only `t=1` fixed, `ρ(1)=id`, scalar `=1` ⟹ `tr=1`.
- Needs: the `G = P⋊H` rep setup, `x` acting on `P` (`MulAut` / semidirect), `IsExtraspecial P`,
  the transversal/central-character, the monomial-matrix trace. **Largest, deepest piece.**

### (P3) DFT descent — `(P1)+(P2) ⟹ dim E₀ − dim E_m = 1`
- `∑_k ε^{-mk} tr(c_{xᵏ}) = h · dim E_m` (char-orthogonality `∑_k ε^{lk} = h·[l≡0]`, needs ε primitive).
- Sub `(P2)` values: `h·dim E_m = q² + (h·[m=0] − 1)` (FIELD). For `m=0`: `h dim E₀ = q²+h−1`;
  `m≠0`: `h dim E_m = q²−1`. Subtract: `h(dim E₀ − dim E_m) = h` ⟹ `dim E₀ − dim E_m = 1`.
- **char-p subtlety**: this is a FIELD equation; descending to the ℕ/ℤ equation
  `dim E₀ = dim E_m+1` needs `char ∤ h` + the values being integers. Reuse the Gram-matrix /
  `(dim:F)≠0` descent trick from Gor 5.5.5a (`ExtraspecialFaithful.lean`) if needed, OR note that
  `dim E_m = ∑ nᵢnᵢ₊ₘ` (Prop 2.4(g), already an ℕ equation) sidesteps part of it: combine the
  field identity `h(∑nᵢ² − ∑nᵢnᵢ₊ₘ) = h` with `(dim:F)≠0`-style cancellation.

## Recommended order
P1 (general trace lemma — concrete, reusable, no group theory) → P3 wiring (char-orthogonality DFT,
isolating `tr(c_{xᵏ})` values as hypothesis) → P2 (the `P⋊H` Burnside-basis framework, the deep lift)
→ assemble keystone → discharge `ExtraspecialThm25` hypotheses → Prop 2.2 Clifford → Thm 3.4.

This is a LARGE remaining build (the original blocker's "rep-theory keystone"); each of P1/P2/P3 is
multiple leaves. P2 in particular is a substantial new framework interfacing `IsExtraspecial` +
semidirect products + the representation.

## ⚠ IMPORTANT REDIRECT (iter 29): the P3 DFT route hits a char-p descent obstacle

**Done so far** (`EigenspaceBlockDecomp.lean`, axiom-clean): `End = ⊕_m E_m`
(`isInternal_cyclicEndConjEigenspaceFin`), P1 core `trace_eq_sum_finrank_smul_of_isInternal`, and
P1 instantiated `trace_pow_cyclicEndConj_eq` (`tr((cyclicEndConj g)^k) = ∑_m εᵐᵏ·(dim E_m : F)`).

**The obstacle.** The DFT inversion `(dim E_m : F) = (1/h)∑_k ε^{-mk} tr(c_{xᵏ})` is a FIELD equation.
Descending `(dim E₀ : F) − (dim E_m : F) = 1` to the ℕ equation `dim E₀ = dim E_m + 1` needs the
cast `ℕ → F` injective on `[0, q²]`, i.e. `char > q²` — NOT available (`r ∤ |G|` can be small).
Worse, `(q²−1)/h ∈ ℤ` (the value the DFT spits out) is EQUIVALENT to `h ∣ q²−1`, which is part of the
very conclusion (`q ≡ ±1`). So the trace/DFT route is **circular / blocked at the ℕ-descent** for
small char. `trace_pow_cyclicEndConj_eq` is still valid + reusable (it IS the H-character of E(P)),
but it does not by itself reach the ℕ keystone.

**The resolution = the F[H]-module ISOMORPHISM** (the real BG (2.11)): `E(P) ≅ 1 ⊕ ((q²−1)/h)·F[H]`
as `F[H]`-modules (`H = ⟨x⟩`, char `r ∤ h` ⟹ Maschke-semisimple; `F` alg-closed ⟹ `H` has `h`
distinct 1-dim chars `εᵐ`). Then `dim E_m = mult(εᵐ in E(P))` is an ℕ multiplicity, and the iso gives
`mult(εᵐ) = (q²−1)/h + [m=0]` DIRECTLY as ℕ (no descent): the trivial summand contributes `+1` to
`m=0`; each regular `F[H]` contributes each char exactly once. So `dim E₀ = dim E_m + 1`.

The iso comes from the **Burnside basis being a monomial `F[H]`-module**: `H` permutes `{ρ(t)}`
(`t ∈ P/Z`) up to roots-of-unity scalars; `C_{P/Z}(x)=1` ⟹ identity coset fixed (→ trivial summand),
all other orbits free of size `h`; each free monomial orbit ≅ `F[H]` (regular) since char `∤ h` and
the orbit-product scalar is a root of unity. **This is the deep P2 + module theory — the large lift.**
Net: build P2 as the module iso (not the trace/DFT). P1/`trace_pow…` support the multiplicity bookkeeping.
