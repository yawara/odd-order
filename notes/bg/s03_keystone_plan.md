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

## Lane A progress (2026-06-07, branch `a-keystone`) + refined Lean plan

**✅ Leaf 1 — Burnside basis** (`BurnsideBasis.lean`, sorry-free, axiom-clean, commit `97412db`):
`burnsideBasis ρ hf hcl : Basis (P ⧸ Z(P)) F (End F V)`, `b c = ρ(out c)`, via `Basis.mk`
(`linearIndependent_representation_quotientOut` [lifted from the Gram-matrix `hindep` previously
buried in `card_quotient_center_le_sq_finrank`] + the already-public spanning
`span_range_quotient_out_eq_top`). `burnsideBasis_apply` simp lemma.

**✅ Leaf 2 — monomial action** (`ExtraspecialMonomial.lean`, sorry-free, axiom-clean, commit `5053a7e`):
abstract data = automorphism `φ : P ≃* P` + intertwiner `T : GL(V)` with `T·ρ p = ρ(φ p)·T`.
- `center_map_eq_of_mulEquiv` (φ maps Z(P) onto Z(P));
- `quotientCenterCongr φ : (P/Z) ≃* (P/Z)` = the induced `σ`, `quotientCenterCongr_mk` simp;
- `cyclicEndConj_representation : c_x (ρ p) = ρ(φ p)` (conjugation by the intertwiner = ρ∘φ);
- `cyclicEndConj_burnsideBasis : ∃ a, c_x (b c) = a • b (σ c)` — the **monomial identity**.

**▶ Leaf 3 (the deep core, NOT yet done) — abstract monomial-operator eigenspace count.**
Goal: `finrank (cyclicEndConjEigenspaceFin ε T m) = N + (if m=0 then 1 else 0)` (N = #free orbits),
hence the keystone `dim E₀ = dim E_m + 1`. Confirmed NO mathlib shortcut: free-action→free-module,
regular-rep eigenspace dims, cyclic group-algebra split are all ABSENT; every trace/rank/charpoly
route is `F`-valued ⟹ circular for the ℕ count (re-verified this session). The integer count
genuinely needs the orbit/basis combinatorics. mathlib tools available: `MulAction.selfEquivSigmaOrbits`,
`orbitRel.Quotient`, `DirectSum.IsInternal` (style as in `EigenspaceBlockDecomp.lean`),
`finrank_eigenspace_le … charpoly.rootMultiplicity` + semisimple equality.

**KEY SIMPLIFICATION found this session (de-risks Leaf 3): use a φ-EQUIVARIANT transversal ⟹ the
twist `μ` vanishes ⟹ `T` is a PURE permutation of the basis.** Because `φ^h = conj(x^h) = id`, one
can choose the transversal `t : P/Z → P` orbit-by-orbit via `t(σ^j c₀) := φ^j(t c₀)`; then
`φ(t c) = t(σ c)` EXACTLY (the wrap `φ^h(t c₀)=t c₀` closes since `σ^h=id`), so `c_x (b c) = b (σ c)`
with NO scalar. (Any section gives a Burnside basis — spanning+Gram independence work for any `t`,
not just `Quotient.out`; generalize `burnsideBasis`/`linearIndependent_representation_quotientOut`
to an arbitrary section `t` with `⟦t c⟧ = c`.) Then per **pure** cycle the eigenvectors are clean:
for a free orbit `{c₀,σc₀,…,σ^{h-1}c₀}`, `v_m = ∑_j ε^{-mj} b_{σʲc₀}` is an `εᵐ`-eigenvector (no
partial products), and `{v_m}_{m}` is a basis of `W_O` (distinct eigenvalues) ⟹ `dim(E_m ∩ W_O)=1`
for every `m`. Fixed point `s₀` (identity coset): `b s₀ = ρ(1) = id`, `c_x(id)=id` ⟹ contributes to
`E₀` only. So `dim E_m = N + [m=0]`.

**✅ Leaf 3 technical core DONE** (`CyclicShiftEigenspace.lean`, sorry-free, axiom-clean, commit
`7b2663b`): `finrank_cyclicEigenspaceFin_cyclicShift` — for the pure shift `T (b j) = b (j+1)` on
`b : Basis (ZMod h) F W`, each `T.eigenspace (εⁱ)` is **1-dimensional** (`ε` primitive `h`-th root).
Helpers: `pow_eq_pow_of_modEq` (general), `cyclicShift_hasEigenvector` (explicit eigenvector
`∑_j (εⁱ)⁻¹^{j.val} • b j`). Proof = dimension squeeze (h independent nonzero eigenspaces in an
h-dim space) reusing `cyclicEigenspaceFin_iSupIndep` + `finrank_iSup_of_iSupIndep` — NO full
diagonalization. **Route-independent** (works for any orbit once it's reduced to a pure cycle).

**▶ Remaining Leaf 3 = the ORBIT ASSEMBLY (the bulk that's left).** Refined plan — a **GLOBAL SQUEEZE**
that AVOIDS the orbit `DirectSum.IsInternal` and the "block-eigenspace = ∑" lemma:
1. ✅ DONE (`BurnsideBasis.lean`, commit `22384c0`): `burnsideBasisOfSection ρ hf hcl t ht`
   for any section `t` (+ `linearIndependent_representation_section`, `span_range_section_eq_top`,
   `burnsideBasisOfSection_apply`). `Quotient.out` versions now delegate to these (DRY).
2. ▶ Construct the **φ-equivariant section** `t` (orbit-rep choice + `φ^j` propagation; `σ`-orbits of
   `P/Z` are free for `c ≠ ⟦1⟧` from `C_{P/Z}(xᵏ)=1`, fixed only at `⟦1⟧`). Get `φ(t c) = t(σ c)`
   ⟹ via `cyclicEndConj_representation`, `c_x (b c) = b (σ c)` — a **PURE permutation** (twist gone).
3. **Per free orbit**, the orbit submodule `W_O = span{b_s : s∈O}` has `Basis (ZMod h) F W_O`
   (torsor `j ↦ σʲc_O`) and `c_x|_{W_O}` = pure shift ⟹ apply `finrank_cyclicEigenspaceFin_cyclicShift`
   to get an explicit `εᵐ`-eigenvector `v_{O,m} ∈ E_m` (it lies in the global `E_m` since `W_O` is
   `c_x`-invariant). Fixed point `⟦1⟧`: `b_{⟦1⟧} = ρ(1) = id ∈ E₀`.
4. **Squeeze (global, no DirectSum):** `{v_{O,m} : O free} ∪ ({b_{⟦1⟧}} if m=0) ⊆ E_m` are independent
   (disjoint orbit support) ⟹ `dim E_m ≥ N + [m=0]` (`N` = #free orbits). And `∑_m dim E_m = q²`
   (`isInternal_cyclicEndConjEigenspaceFin`) `= N·h + 1 = ∑_m (N+[m=0])`. Each `≥` + equal totals ⟹
   `dim E_m = N + [m=0]` ⟹ `dim E₀ = dim E_m + 1`. (Same squeeze pattern as the single-cycle proof.)
   Needs: σ-orbit count `|P/Z| = N·h + 1` (orbit sizes from `C_{P/Z}(xᵏ)=1`; `MulAction`/`Equiv.Perm`
   orbit tools), and cross-orbit independence (disjoint basis support).
5. Discharge `hEdim` of `sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace`
   (`ExtraspecialThm25.lean`). Leaf 4.

Then **Leaf 5 = Thm 2.5/3.4 assembly** (Prop 2.2(a) alg-closed Clifford `V_P=M`, base-change (2.9),
produce `(P,φ,T)` from the `G=P⋊⟨x⟩` rep, Maschke→faithful irred, Gor 5.3.7 → contradiction).

## ✅✅ KEYSTONE COMPLETE (2026-06-07, Lane A `a-keystone`) — Leaf 3 + Leaf 4 done, sorry-free + axiom-clean

The keystone `dim E₀ = dim E_m + 1` (BG (2.11)) is **fully discharged** in terms of the BG Thm 2.5
setup data. Full build green (3599 jobs), AxiomsCheck OK. Three commits:
`2b6617c` (orbit infra) → `f2af3c8` (abstract keystone) → `6cfa8d8` (extraspecial discharge).

**Two new leaf files** (nothing imports them yet — they are the producers for Leaf 5):
- `CyclicPermEigenCount.lean` — the **abstract** orbit-count keystone, pure linear algebra +
  finite combinatorics over a bare basis index `κ`:
  `CyclicPermEigen.finrank_eigenspace_fixed_succ` — for a monomial permutation operator
  `T` on `b : Basis κ F W` (`T^k (b c) = a • b (σ^k c)`, `σ : Equiv.Perm κ`) with `σ^h = T^h = 1`,
  `ε` primitive `h`-th root, `char ∤ h`, a `σ`-fixed `c₀` with `T (b c₀) = b c₀` whose orbit is the
  **only** non-free one, gives `dim (T.eigenspace ε^0) = dim (T.eigenspace ε^m) + 1` for `ε^m ≠ 1`.
- `ExtraspecialKeystone.lean` — the **bridge** `finrank_cyclicEndConjEigenspaceFin_succ`:
  instantiates the abstract keystone at `b = burnsideBasis`, `T_op = cyclicEndConj T`,
  `σ = quotientCenterCongr φ`, producing the exact `hEdim` of
  `sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace`. **Verified end-to-end**: composing
  the two yields BG Thm 2.5's `q = h·v₀ ± 1` from `(ρ, φ, T, hint, φ^h=1, ε primitive, char∤h,
  C_{P/Z}(xᵏ)=1)`.

### ⚠ The realised plan DEVIATED from "Remaining Leaf 3" above (both deviations are improvements — do not revert)

1. **No φ-equivariant section** (Step 2 above was AVOIDED). The recent commits `range_sum_pow_eq_eigenspace`
   (range of the Fourier projection `proj_m = ∑_k (ε^m)⁻¹^{k} T^k` = the eigenspace `E_m`) and
   `sum_pow_smul_pow_comm` (proportionality `proj_m (T^n w) = (ε^m)^n proj_m w`) make the *monomial*
   (twisted) action suffice — no need to kill the twist. Reason: independence (`hoff`/`hdiag`) only
   needs the **support** of `proj_m (b c)` (⊆ the orbit of `c`) plus the `k=0` diagonal term `= 1`;
   the twist scalars `μ_k` are always killed by the Kronecker `[σ^k c = c']`. So the **done** Leaf 2
   `cyclicEndConj_pow_burnsideBasisOfSection` is reused directly. The fixed point `⟦1⟧` lands in `E₀`
   for **any** section because `b ⟦1⟧ = ρ(out ⟦1⟧)` is central ⟹ scalar ⟹ `c_x`-fixed (conjugation
   fixes scalars) — no need for `t ⟦1⟧ = 1`.
2. **No GLOBAL SQUEEZE / no `|P/Z| = N·h+1`** (Step 4 above was REPLACED). Because `range proj_m = E_m`
   gives **spanning** of `E_m` by `{proj_m (b c) : c}` for free, and proportionality collapses the span
   onto orbit reps, `dim E_m = #{contributing orbits}` is an **exact per-`m` basis count** (via
   `finrank_span_eq_card`), not a squeeze. The total orbit count `N` cancels between `E₀` (all orbits)
   and `E_m` (all but the `c₀`-orbit, which projects to 0 for `ε^m ≠ 1`), so the keystone needs neither
   `∑_m dim E_m` nor `(dim V)² = |P/Z|`. Orbit reps come from a hand-built `orbitSetoid` (`Quotient`,
   reps via `Quotient.out`), counted by a `Finset` filter; no `MulAction`/`DirectSum.IsInternal`.

## ✅ Leaf 5 progress (2026-06-08, `a-keystone`): group-level Thm 2.5 divisibility wired

`ExtraspecialThm25Group.lean` (commit `788b670`, sorry-free + axiom-clean, full build green):
**`finrank_modEq_of_faithful_irreducible`** — for finite `G`, `P ⊴ G` of class `≤ 2`
(`commutator P ≤ Z(P)`), faithful `ρ` over alg-closed `F` (`char ∤ |P|`), `x ∈ G` with `x^h = 1`,
`h ≥ 2`, `char ∤ h`, `ε` primitive `h`-th root, **IF** `Representation.IsIrreducible (ρ.comp P.subtype)`
(= Prop 2.2(a), `V_P` irreducible) **and** `hcent` (`x` fixed-point-free on `P/Z`, = Prop 1.5),
**THEN** `(dim V : ℤ) = h·v₀ + δ` with `δ = ±1` (i.e. `dim V ≡ ±1 mod h`).

Group-theoretic setup wiring built (all grounded): `conjAutOfNormal P x : P ≃* P` (conj aut of normal
`P`, via `MulEquiv.subgroupMap` + `Subgroup.Normal.conj_smul_eq_self`) + `_pow_apply_coe`/`_pow_eq_one`;
`T = ρ.asGroupHom x : GL(V)` with `(T:End) = ρ x` (`MonoidHom.coe_toHomUnits`); `hint`; `φ^h=1`,
`T^h=1`; `hV` (`cyclicEigenspaceFin_isInternal_of_pow_eq_one`); then composes
`finrank_cyclicEndConjEigenspaceFin_succ` (keystone) + `sum_eigenspaceFinDim_eq_…` (Prop 2.4) +
`∑ dim Vᵢ = dim V`. **GOTCHA**: `(ρ.comp P.subtype).IsIrreducible` dot-notation resolves to
`MonoidHom.IsIrreducible` (fails) — use explicit `Representation.IsIrreducible (ρ.comp P.subtype)`
(both are `abbrev`; Clifford.lean does the same at L101).

### ▶ Remaining = Leaf 5 (Thm 2.5/3.4 assembly) — the keystone is no longer the blocker

The keystone now consumes three inputs that the **BG Thm 2.5 setup** must supply (assembled separately,
from the `G = P ⋊ ⟨x⟩` representation):
- `hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily ε (T:End) h)` (eigenspace decomposition of `End V`);
- `hcent : C_{P/Z}(xᵏ) = 1` for `xᵏ ≠ 1` (stated as: only the identity coset is fixed by a nontrivial
  `σ`-power) — this is the BG hypothesis that `x` acts fixed-point-freely on `P/Z`;
- the `(ρ, φ, T, hint)` data itself: a faithful irreducible `F[P⋊⟨x⟩]`-module restricting to `(P,φ,T)`.

So **Leaf 5** = Prop 2.2(a) alg-closed Clifford (`V_P = M`), base-change (2.9), produce `(P,φ,T)` +
`hV` + `hcent` from the `G`-rep (Maschke → faithful irred), then Gor 5.3.7 (=`S04e_GorThm37`) →
contradiction. This opens BG §10–§16.

### ▶▶ Precise next steps (2026-06-08) — `finrank_modEq_of_faithful_irreducible` reduced Thm 2.5
### divisibility to TWO open hypotheses; **`hcent` now DISCHARGED**, so the frontier = `hVP` alone:

1. **✅ `hcent` (Prop 1.5) DONE** (commit `0af0f90`, sorry-free + axiom-clean, full build 3608 green):
   `quotientCenter_fixedFree_of_centralizer_le_center` (`ExtraspecialThm25Group.lean`) derives
   `∀ k≠0, ∀ c, (quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c = c → c = 1` from `(h, |P|) = 1`
   + the BG-faithful `hCP : ∀ k≠0, ∀ p, (conjAutOfNormal P x ^ k.val) p = p → p ∈ center P` (= `C_P(xᵏ) ⊆ Z`).
   Proof exactly as planned: `A = Subgroup.zpowers (φ₀^k.val) ≤ MulAut P`, `coprime_fixedPoints_quotient_of_coprime_normal`
   (Isaacs Cor 3.28) lifts the fixed coset `⟦g⟧` to a genuine fixed point `w` of `φ₀^k`, `hCP` puts
   `w ∈ Z`, coset rep `g = w·n⁻¹ ∈ Z` ⟹ `⟦g⟧ = c = 1`. Coprimality `|A|=orderOf(φ₀^k.val) ∣ h`
   (`(φ₀^k.val)^h=(φ₀^h)^k.val=1`) + `|Z| ∣ |P|` + `(h,|P|)=1`. `hg_fix` (coset A-invariance) via
   nat-power reduction `mem_powers_iff_mem_zpowers` + `quotientCenterCongr_pow_mk` + fixed-point iterate.
   Center `IsSolvable` via `isSolvable_of_comm` + `mem_center_iff`. **Convenience corollary**
   `finrank_modEq_of_faithful_irreducible_of_centralizer` = Thm 2.5 divisibility with `hcent` swapped
   for `(h,|P|)=1` + `hCP` (calls the producer internally). **`hcop`/`hCP` will be supplied by the
   §2 setup** (`h` rel. prime `p` is a hypothesis of BG Thm 2.5, mmd L716; `C_P(x)=Z` likewise).

2. **▶ `hVP` (Prop 2.2(a) alg-closed Clifford, the BIG piece) — NOW THE SOLE FRONTIER for divisibility** —
   `Representation.IsIrreducible (ρ.comp P.subtype)`
   from: `ρ` faithful irreducible `F[G]`-module, `P ⊴ G`, `G/P` cyclic, `F` alg-closed, and `M ≅ M^g`
   ∀g (all `P`-conjugates of an irred submodule `M` isomorphic — from "faithful irred of extraspecial
   determined by center", Gor 5.5.4). BG mmd L614-647: build `L` extending `M`, `τ`-cocycle, `τx`
   generates `Hom_FG(L,L) = F` (Prop 2.1 ✅), so `V_P` irreducible. `Clifford.lean` is **ℂ-pinned**
   (no destructive edit) ⟹ NEW file `CliffordAlgClosed.lean` (or alg-closed section). Multi-session.
   Needs Gor 5.5.4 ("faithful irred determined by central char") too — `ExtraspecialFaithful.lean` has
   `center_isScalar` + `sq_finrank_eq_card_quotient_center`; 5.5.4 = "two faithful irreds with equal
   central char are isomorphic" is a separate sub-piece.

After hVP: both Thm 2.5 conclusions are genuine grounded (divisibility + C_V(H)). Then:
3. **✅ C_V(H) half DONE** (commit `e7db278`, 2026-06-08, sorry-free + axiom-clean, full build 3608):
   `finrank_eq_sub_one_of_faithful_irreducible` (`ExtraspecialThm25Group.lean`) — same setup as
   `finrank_modEq…` + `dim V ≥ 2` + `C_V(x)=0` (`cyclicEigenspaceFinDim ε (ρ x) 0 = 0`) ⟹ `dim V = h-1`
   (= `h = dim V + 1`); contrapositive = BG's `h ≠ pⁿ+1 ⟹ C_V(H) ≠ 0`. Calls
   `sum_eigenspaceFinDim_eq_sub_one_of_finrank_cyclicEndConjEigenspace` (Prop 2.4(k), ✅). Shared setup
   (φ,T,hint,hV,hEdim,∑=dim V) factored into private `cyclicEndConj_keystoneData_of_faithful_irreducible`
   (both divisibility + C_V(H) consume it; divisibility rewritten to use it, sig unchanged). centralizer
   corollary `finrank_eq_sub_one_of_faithful_irreducible_of_centralizer` parallels the divisibility one.
   **⟹ group-level Thm 2.5 は両結論とも wired, 残仮説 = hVP 単独。**
4. **Thm 3.4** (`S03d_Thm34.lean`, new): Maschke → faithful irred → Gor 5.3.7 → special case = Thm 2.5
   → parity contradiction (`h = pⁿ+1` even vs `|G|` odd). Then Thm 3.5 → Thm 3.6 → §10.6 → §10/§11.

### ▶▶▶ hVP (Prop 2.2(a)) の精密プラン (mmd L614-653 精読, 2026-06-08)

**Prop 2.2(a)**: `G` group, `H ⊴ G`, `G/H` cyclic, `F` alg-closed, `M` irred `F[H]`-module with
`M ≅ M^x ∀x∈G`. IF `L` irred `F[G]`-module & `M ≅` submodule of `L_H`, THEN `L_H ≅ M` (= `L_H` irred).
**hVP 適用**: `H=P`, `L=V` (faithful irred `F[G]`), `M`=irred `F[P]`-submodule of `V_P` ⟹ `V_P=M` irred。
証明 (mmd L619-651):
1. Clifford (Gor 3.4.1): `L_H = M_1⊕…⊕M_k`, `M≅M_i`。`G` faithful on `L` ⟹ `H` faithful on `M`。
2. `F` alg-closed ⟹ `Hom_{FH}(M,M)=F` ⟹ (Prop 2.1✅) `E(H)=Hom_F(M,M)` (Burnside, M 上全行列環)。
3. `M≅M^{x⁻¹}` (hyp) ⟹ ∃ F-iso `τ∈E(H)` with `(mh)τ=(mτ)(xhx⁻¹)` (2.2)。`L` に lift (2.1+2.2 経由)、
   linear 拡張 ⟹ `(ℓθ)τ=(ℓτ)(xθx⁻¹) ∀θ∈E(H)⊆E(G)` (2.3 `(ℓθ)τx=(ℓτx)θ`)。
4. `τ⁻¹∈E(H)` ⟹ `ℓx=ℓτxτ⁻¹` ⟹ `(ℓx)τx=(ℓτx)x` (2.4)。(2.3)+(2.4)+`⟨H,x⟩=G` ⟹ `τx∈Hom_{FG}(L,L)`。
5. `F` alg-closed + `L` irred ⟹ (Prop 2.1✅) `Hom_{FG}(L,L)=F` ⟹ `τx` scalar。`τ∈E(H)` ⟹ `M_1τ=M_1`
   ⟹ `M_1=M_1τx=M_1x` ⟹ `M_1` は `G`-submodule ⟹ `L=M_1` (L irred)。∎
**要件**: (i) Clifford 分解 (mathlib に有? 要調査; repo `Clifford.lean` は ℂ-pin)。(ii) Prop 2.1✅
(`asAlgebraHom_surjective_of_isAlgClosed` 系)。(iii) Gor 5.5.4 (= `M≅M^g`, faithful irred extraspecial
は central char で決まる; `ExtraspecialFaithful.lean` の `center_isScalar`+`sq_finrank…` 部分被覆、
"等 central char ⟹ iso" は別 sub-piece)。新 `CliffordAlgClosed.lean` (ℂ-pin Clifford.lean は破壊禁止)。複数セッション。

**資産インベントリ (2026-06-08 精査, Explore agent; 再調査不要)**:
- ✅ **Prop 2.1 = `AbsolutelyIrreducible.lean` (一般 alg-closed F, NOT ℂ-pin)**: `asAlgebraHom_surjective_of_isAlgClosed`
  (L118, `F[G]→End_F V` 全射), `span_range_representation_eq_top` (L135, `{ρ g}` spans End), `center_isScalar`
  (L157, `z∈center ⟹ ρ z = c•id`), `toModuleEnd_surjective_of_isAlgClosed` (L67, module 版 Burnside)。
- ✅ **`Representation.IsIrreducible`** (mathlib `RepresentationTheory/Irreducible.lean:28`) `:= IsSimpleOrder (Subrepresentation ρ)`;
  `irreducible_iff_isSimpleModule_asModule` (L34) で `IsSimpleModule k[G] ρ.asModule` と往復。`restrictRep ρ H := ρ.comp H.subtype`
  (Clifford.lean:147)。`IsSimpleModule` API (mathlib `RingTheory/SimpleModule/Basic.lean`) 充実。
- ⚠️ **重大 ℂ-pin 障壁**: Clifford.lean の **module-level** 機構は全部 ℂ 固定 — `conjBySimpleRingHom g` (L156, `ℂ[H]` 環自己同型 `h↦ghg⁻¹`),
  `conjBySimpleSemilinear g` (L182, ρ g を H-intertwiner として実現する semilinear), **`isSimpleModule_map_conjBySimpleSemilinear`
  (L244, 証明済: N が `Res ρ` の simple `ℂ[H]`-部分加群 ⟹ `ρ g(N)` も simple — これが Clifford 分解の核ブロック)**。
  **⟹ 一般 F へ移植が hVP の最初の具体 sub-task** (これら 3 つを CliffordAlgClosed.lean で F 版に)。
- ❌ **mathlib に完全 module-level Clifford 分解は無い** (`L_H=⊕ conjugate simples`)。有るのは `IsSimpleModule`,
  `Rep.res` (`Rep/Res.lean`), `Representation.ind` (`Induced.lean`), Maschke `sumOfConjugates` (intertwiner レベルのみ)。
- ❌ **Gor 5.5.4 ("等 central char の faithful irred ⟹ iso" ⟹ `M≅M^g`) は未形式化** (ExtraspecialFaithful は mass formula
  止まり、iso 部分なし)。別 sub-piece。
- **着手順序案**: (1) `conjBySimpleSemilinear`+`isSimpleModule_map_conjBySimpleSemilinear` を一般 F に移植
  (CliffordAlgClosed.lean) → (2) Clifford 分解 `L_H=⊕M_i` (M≅M_i, M_1 が submodule) → (3) τ-intertwiner +
  `τx∈Hom_{FG}(L,L)=F` scalar → `L=M_1` (Prop 2.2(a) 本体) → (4) Gor 5.5.4 で `M≅M^g` 供給 → hVP discharge。

### ✅✅ hVP 進捗 (2026-06-08, `a-keystone`): CliffordAlgClosed.lean の両「端」着地 — 残 = τ-scalar crux

`CliffordAlgClosed.lean` (新規, **一般体 `k`**, sorry-free + axiom-clean, OddOrder root 配線済, full 3609):
- **✅ Step 1 (foundation) DONE** (commit `3aa611c`): ℂ-pin Clifford.lean の module-core を一般 `k` に移植:
  `conjNormalMulAut H g : H≃*H` (h↦ghg⁻¹), `conjMonoidAlgRingHom g : k[H]→+*k[H]` (誘導環自己同型, surj),
  `conjSemilinearEnd ρ g` (ρ g を `conjMonoidAlgRingHom g`-semilinear endo として; module-level normality
  `h•(ρg v)=ρg(ρ(g⁻¹hg)v)`), **`isSimpleModule_map_conjSemilinearEnd`** (simple `k[H]`-部分加群 N の像 `ρg(N)`
  も simple — conjugation が simple constituents を置換; 既約性/alg-closed 不要, ρg は常に bijection)。
  ℂ-pin Clifford.lean は無改変 (名前を別にして共存)。
- **✅ Step 末尾 (conclusion) DONE** (commit `1b24c0a`): **`eq_top_of_forall_map_conjSemilinearEnd_le`** —
  ρ 既約 + W (≠⊥) が `G`-不変 (∀g, `W.map (conjSemilinearEnd ρ g) ≤ W`) ⟹ `W=⊤`。証明: G-不変 `k[H]`-部分加群
  は `Subrepresentation ρ` の carrier (`toSubmodule := W.restrictScalars k`) ⟹ `IsSimpleOrder (Subrepresentation ρ)`
  (=既約) で ⊥/⊤、≠⊥ で ⊤。これが BG の「M_1 G-不変 ⟹ L=M_1」(mmd L651)。
- **✅ Clifford 構造 (W-isotypic) DONE** (commit `497fb1e`, 2026-06-08): mathlib `IsIsotypicOfType`
  (`RingTheory/SimpleModule/Isotypic.lean`) を使用。`map_conjSemilinearEnd_one`/`map_map_conjSemilinearEnd`
  (carrier 等式 `ρ(g₁g₂)=ρg₁∘ρg₂`, semilinear-comp 回避) → `iSup_map_conjSemilinearEnd_eq_top` (ρ 既約 ⟹
  `⨆_g (ρg)W = ⊤`, Clifford) → **`isIsotypicOfType_of_conjugates`** (∀ conjugate `(ρg)W ≅ W` ⟹
  `IsIsotypicOfType k[H] L_H W`)。`Submodule.linearEquiv_of_sSup_eq_top` 使用。**GOTCHA**: asModule の
  Module-instance diamond で `set_option backward.isDefEq.respectTransparency false in` 必須 (Clifford.lean 同様)。
- **▶ 残 = m=1 finish のみ** (`finrank V = finrank W` ⟹ `W=⊤`): `IsIsotypicOfType L_H W` + Maschke
  (mathlib instance `IsSemisimpleModule k[G] V` for `NeZero(card G:k)`) ⟹ `V ≅ Wᵐ` (`linearEquiv_fun`).
  **m=1 が唯一の残り。クリーン還元**: m=1 ⟺ `finrank V = finrank W` ⟹ `W` simple ≤ ⊤ で finrank 一致 ⟹ `W=⊤`
  (`eq_top` も使える)。m=1 の 2 ルート (どちらもハード, 単独 multi-session):
  - **(A) Skolem-Noether 経路**: `E:=End_{k[H]}(V)≅M_m(k)` (isotypic + `endVecAlgEquivMatrixEnd` + Schur
    `finrank_endomorphism_simple_eq_one`✅mathlib); θ:=Ad(ρx) auto, `End_{k[G]}(V)=E^θ=k` (Schur 既約 V); SN
    (θ=Ad u) + centralizer(u)=k ⟹ u scalar ⟹ θ=id ⟹ E=k ⟹ m=1。**⚠ SN は mathlib ABSENT** → M_m(k) 版を自前
    (θ-twist simple module ≅ standard ⟹ intertwiner u, ~50-100 行)。Wedderburn (`WedderburnArtin.lean`) 有。
  - **(B) BG-τ 経路** (mmd L619-650): Burnside (Prop2.1✅) で conjugate-iso を `τ=ρ(a)∈E(H)` 化, `ann(V)=ann(W)`
    (isotypic) で `L` へ extend, σ:=ρx∘τ⁻¹ が `End_{k[G]}=k` scalar ⟹ `(ρx)W=W`。⚠ τ の commutation/convention
    が微妙 (σ が ρx と可換になる cocycle 条件 = BG (2.4))。
- **▶ + bootstrap**: x-不変 + W は `k[H]`-部分加群 (H-不変) + `G/H=⟨xH⟩` ⟹ ∀g G-不変 — 小補題 (eq_top 前提)。
  ※ m=1 finish なら finrank 経由で直接 `W=⊤`, bootstrap 不要かも。
- **▶ + Gor 5.5.4** (`W≅W^g` 供給 = hconj 仮説, 別 sub-piece, 未着手)。
- **hVP 進捗 = 3/4** (foundation✅ + conclusion✅ + W-isotypic✅; 残 m=1 finish)。CliffordAlgClosed.lean 全 sorry-free。

### ✅ m=1 finish: REFINED ROUTE A (2026-06-08, mathlib 偵察完了 — Explore agent; 再調査不要)

**ルート A (Skolem-Noether) に確定。ルート B (BG-τ) は破棄** (τ cocycle が fiddly・非再利用)。偵察で
**A の hard piece は「行列 Skolem-Noether 自前構築」1 個のみ**と判明し、しかも **finish が劇的に簡単化** —
centralizer-dimension 補題が **不要**になった。

**mathlib 在庫 (PRESENT / ABSENT 確定)**:
- ✅ Wedderburn-Artin 一式 (`RingTheory/SimpleModule/WedderburnArtin.lean`): `isSimpleRing_isArtinianRing_iff`
  (L66, `IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R`),
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` (`SimpleModule/IsAlgClosed.lean:22`, `R≃ₐ[F]M_n(F)`)。
- ✅ **unique simple module** = `IsIsotypic.of_self [IsSemisimpleRing R] (h : IsIsotypic R R) : IsIsotypic R M`
  (`Isotypic.lean:80`)。`IsIsotypic R M` の def (L59) = 「M の任意 simple 部分加群が互いに ≅」。
- ✅ `Matrix.isSimpleRing [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A)` (`SimpleRing/Matrix.lean:21`);
  field は IsSimpleRing。transport = `IsSimpleRing.of_ringEquiv` / `of_surjective` (`SimpleRing/Congr.lean:23-28`)。
- ✅ twist module = `compHom.toLinearEquiv {R S} (g : R ≃+* S)` (`Module/Equiv/Basic.lean:175`) — θ:E≃ₐE を
  RingEquiv とみて `Module.compHom` で別 E-module 構造 (instance diamond 注意, 型シノニム or letI)。
- ✅ `IsIsotypicOfType.linearEquiv_fun [Module.Finite R M] : ∃ n, Nonempty (M ≃ₗ[R] Fin n → S)` (mult 抽出),
  `IsSemisimpleModule.endAlgEquiv`, `endVecAlgEquivMatrixEnd : End_A(ι→M)≃ₐMatrix ι ι (End_A M)` (`Matrix/ToLin.lean:1165`)。
- ✅ Schur: `finrank_endomorphism_simple_eq_one` (alg-closed, 既約 ⟹ `finrank End=1`),
  `isSimpleModule_iff_finrank_eq_one` (`SimpleModule/Rank.lean:17`), `Module.End.instDivisionRing`,
  `isField_center (A) [IsSimpleRing A]` (`SimpleRing/Field.lean:27`)。
- ✅ Maschke instance `IsSemisimpleModule k[G] V` for `[Finite G][NeZero (Nat.card G:k)]` (`Maschke.lean:168`)。
- ❌ **ABSENT**: Skolem-Noether 本体 / 「M_n aut は inner」/ centralizer finrank bound ≥ n。← A の唯一の自前構築。

**REFINED finish (centralizer-dim 不要・エレガント)**: SN で θ=Ad(u) (u∈E) を得たら、`u∈E` かつ
`u∈C_E(u)=E^θ=k` (u は自分と可換) ⟹ **u は scalar** ⟹ θ=Ad(scalar)=**id** ⟹ `E=E^θ=k` ⟹
`finrank_k E=1` ⟹ m=1。← 「centralizer(u)=k ⟹ m=1」(旧プラン, dim≥m 補題要) を回避。

**Leaf 分解 (bottom-up, 各 build-green)**:
- **✅ Leaf SN-core DONE** (2026-06-08, `SkolemNoether.lean` 新規, sorry-free + axiom-clean, full build
  3610 green): **`finrank_le_one_of_aut_fixedScalar`** — `W₀` f.d. over **任意体 `k`** (alg-closed 不要!),
  `θ : End_k(W₀) ≃ₐ[k] End_k(W₀)` の固定環 ⊆ scalars ⟹ `finrank_k W₀ ≤ 1`。+ foundation
  **`nonempty_linearEquiv_of_isSimpleModule`** (任意 simple artinian ring の simple module は同型, ~6 行,
  `IsSimpleRing.isIsotypic` + `exists_linearEquiv_ideal_of_isSimpleModule`)。
  - 実装ルート (計画どおり, deviation 小): (i) `EndTwist θ` 型シノニム + `Module.compHom θ.toRingEquiv.toRingHom`
    で twist module; simplicity 移送は **`LinearMap.isSimpleModule_iff_of_bijective`** (mathlib 既存! θ-semilinear
    恒等で) — orderIso 手構築不要。(ii) `IsSimpleRing (End k W₀)` は `algEquivMatrix` で `Matrix` へ transport
    (`Module.finBasis`, `Nonempty (Fin n)` from `finrank_pos`), `IsArtinianRing` は `IsArtinianRing.of_finite`。
    (iii) `nonempty_linearEquiv_of_isSimpleModule` で `W₀ ≃ₗ[End] EndTwist θ` → u∈GL(W₀)=End_k(W₀), `θ=u.conjAlgEquiv k`。
    (iv) θ が u 自身を固定 ⟹ u scalar (c•id, c≠0) ⟹ θ=id ⟹ 全 f scalar ⟹ `finrank(End)=n²≤1` (surj algebraMap)
    ⟹ n≤1。**alg-closed も Jacobson density も centralizer-dim も不要** (W₀=End_k(W₀) なので u∈E 自動)。
  - ⚠ diamond `set_option` は **不要**だった (compHom instance + `change` で defeq 解決)。`show`→`change` lint のみ。
  - **✅ 抽象ラッパー `finrank_eq_one_of_aut_fixedScalar` も追加** (alg-closed `k` の f.d. simple algebra `E`,
    `θ : E ≃ₐ[k] E` 固定環 ⊆ scalars ⟹ `finrank_k E = 1`): Wedderburn `exists_algEquiv_matrix_of_isAlgClosed`
    で `E ≅ₐ M_n(k) ≅ₐ End_k(Fin n→k)` (`algEquivMatrix'.symm`)、θ を transport、matrix 版適用 ⟹ n≤1、`NeZero n`
    ⟹ n=1 ⟹ `finrank E=n²=1`。**wire-E はこれを直接消費** (M_m transport を application で再実装不要)。両定理 commit `b4a88f9f`/次。
- **▶ Leaf wire-E** (次セッション, CliffordAlgClosed.lean に追記 or 新 section) — **SN-core 完成済なので残る山はこれ**:
  `E:=Module.End k[↥H] (resRep ρ H).asModule`。手順:
  1. **`IsSimpleRing E`**: V は W-isotypic (既 `isIsotypicOfType_of_conjugates`) + Maschke 半単純 ⟹
     `E ≅ₐ Matrix m m (End_{k[H]} W)` (`endVecAlgEquivMatrixEnd` + `linearEquiv_fun`), `End_{k[H]} W = k`
     (Schur, alg-closed + W simple — 補題名要確認: `finrank_endomorphism_simple_eq_one` 系) ⟹ `E ≅ₐ M_m(k)` simple。
     `[FiniteDimensional k E]` も (V f.d.)。
  2. **θ:=Ad(ρx) を `E ≃ₐ[k] E` に**: ρx ∈ GL(V) (k-線形) が E を共役で保つ (x が H 正規化 ⟹ k[H]-線形性保存)。
     mathlib 直球は無いかも (conjAlgEquiv は End_R の R-共役用; ここは End_{k[H]} を k-線形 ρx で共役 = subalgebra 共役)。
     `MulSemiringAction`/`Subalgebra` 共役 or 手構築 (`AlgEquiv` の toFun=f↦ρx∘f∘ρx⁻¹, well-def 証明)。
  3. **`E^θ = scalars`**: `θ f = f ⟺ ρx と可換 ⟺ f ∈ End_{k[G]}(V)` (G=⟨H,x⟩); `End_{k[G]}(V)=k` (Schur,
     V 既約 k[G]-加群, alg-closed) ⟹ 固定環 ⊆ scalars。⚠ `G=⟨H,x⟩` (= ⟨H, x⟩ 生成 = ⊤) を仮説に要する
     (§2 setup の `G = P ⋊ ⟨x⟩` が供給) — hVP/Prop2.2(a) の hypothesis に `Subgroup.closure (H ∪ {x}) = ⊤` 相当。
  4. **`finrank_eq_one_of_aut_fixedScalar` 適用** ⟹ `finrank_k E = 1` ⟹ m=1 (E≅M_m, m²=1) ⟹ `V_H` simple
     ⟹ W (simple 部分加群) `= ⊤` (finrank 一致 or simple ≤ ⊤)。これで Prop 2.2(a) = hVP discharge。
  + Gor 5.5.4 (hconj `W≅W^g`) は依然別 sub-piece (未着手, hVP の最終 hypothesis)。
  - **wire-E recon (2026-06-08, 再調査不要)**: (a) module-level Schur 「`End_{k[G]} V = scalars`」は
    **要組立** — mathlib の `finrank_endomorphism_simple_eq_one` は **category 版** (`CategoryTheory/Preadditive/Schur.lean:126`,
    `FDRep` 経由); module 直は `AlgebraRepresentation/Basic.lean` の alg-closed Schur か、`End` が division ring
    (`Module.End.instDivisionRing`, simple module) + f.d. division alg over alg-closed = k (`isSimpleModule_iff_finrank_eq_one`)
    で組む。`irreducible_iff_isSimpleModule_asModule` (`Irreducible.lean:34`) で `ρ.IsIrreducible ↔ IsSimpleModule k[G] ρ.asModule`。
    (b) `IsSimpleRing E` の直 instance **無し** → `V ≅ W^m` (`linearEquiv_fun`) ⟹ `E ≅ₐ Matrix m m (End_{k[H]}W)`
    (`endVecAlgEquivMatrixEnd`), `End_{k[H]}W` は division ring (Schur) ⟹ `Matrix.isSimpleRing` + transport (`Nonempty (Fin m)`, m≥1)。
    (c) θ=Ad(ρx) on E: `LinearEquiv.conjAlgEquiv (ρx)` は `End_k V` 全体の自己同型 → E (=`End_{k[H]}V`) を保つこと
    を示して手で `E ≃ₐ E` 構築 (`Subalgebra.equivOfEq`/`AlgEquiv.ofInjective` は部分的; 直球 restrict は無く手構築濃厚)。
- **✅ module-Schur LANDED** (2026-06-08, commit `1e4c9314`): `algebraMap_end_bijective_of_isSimpleModule`
  (`SkolemNoether.lean`) — `[Field k][IsAlgClosed k][Algebra k R]`, M simple R-加群 f.d. over k ⟹
  `algebraMap k (End R M)` bijective (= 全 endo が scalar)。**eigenvalue 論法で diamond 回避**: f は固有値 c∈k を持ち
  (`Module.End.exists_eigenvalue`, alg-closed+f.d.), `ker(f−c•id)` は simple M の非零 R-部分加群 ⟹ ⊤ ⟹ f=c•id。
  `Module.End.instDivisionRing` の **semiring diamond を完全回避** (note 旧推奨の FDRep ルートも不要だった)。
  ⟹ wire-E step 3 (`E^θ⊆scalars` for `End_{k[G]}V`) + step 1 (`End_{k[H]}W≅k` for IsSimpleRing E) の両方を供給。
- **🔑 θ construction の KEY INSIGHT (2026-06-08, 次セッション用)**: by-hand map_smul' を避ける道 —
  既存 `conjSemilinearEnd ρ x` (CliffordAlgClosed, σ_x:=conjMonoidAlgRingHom x-semilinear) を使い
  `θ(f) := conjSL(x) ∘ f ∘ conjSL(x⁻¹)`。**semilinear twist が相殺**: σ_x ∘ σ_{x⁻¹} = id (∵ conj_x∘conj_{x⁻¹}=id on H)
  ⟹ θ(f) は **k[H]-linear 自動** (RingHomCompTriple σ_{x⁻¹} σ_x id 要)。あるいは by-hand map_smul' (single h c で
  reduce, ρ の hom 性で計算; 既に worked out — `θ(f)(single h c•v)=single h c•θ(f)(v)` は ρ(hx)=ρ(h)ρ(x) 等で展開)。
  `asModule := V` は **defeq** (`Representation.asModule` は型シノニム, `asModuleEquiv` で橋) — ρx を asModule 上で使える。
  θ の AlgEquiv packaging (map_mul/map_add/commutes/bijective, θ⁻¹=conj by x⁻¹) が残工数の主 (~60-100 行)。
- **bridge finrank E=1 ⟹ V_H simple**: projection idempotent (W 補元 p∈E, finrank E=1 ⟹ E=k•id ⟹ p=c•id,
  idempotent ⟹ c∈{0,1}, range p=W ⟹ W=⊥/⊤) ‖ 「End=scalar ⟹ 非自明 idempotent 無 ⟹ indecomposable + semisimple ⟹ simple」。
- **Leaf hVP-assemble**: 最終結論は `Representation.IsIrreducible (resRep ρ H)` (= `IsSimpleModule k[↥H] (resRep ρ H).asModule`,
  `irreducible_iff_isSimpleModule_asModule`) — group-level Thm 2.5 (`finrank_modEq_of_faithful_irreducible`) が直消費。
  hconj (`W≅W^g`) は Gor 5.5.4 待ち (別 sub-piece, 未着手 — hVP の最終仮説)。
- **wire-E 残工数見積**: θ packaging (~60-100) + IsSimpleRing E (~30, module-Schur 利用) + bridge (~25) + assembly (~30)
  ≈ 1 セッション。SN core/wrapper/module-Schur (本セッション 3 commit) で **材料は出揃った**; 残は asModule 越しの組立。

### ✅✅ wire-E 進捗 (2026-06-08 続き, `a-keystone`): θ + hfix LANDED, 残 = IsSimpleRing E + assembly

`CliffordMultiplicityOne.lean` (新規, sorry-free + axiom-clean, full build 3611, OddOrder root 配線済,
commits `d54869a5` + `e1ac4947`):
- **✅ θ = `cliffordConj ρ x : End_{k[H]}V ≃ₐ[k] End_{k[H]}V`** (conjugation by ρx)。`cliffordConjMap`
  (toFun=`conjSL(x)∘f∘conjSL(x⁻¹)`, map_smul' は conjSL の semilinear smul × 3 + `σ_x∘σ_{x⁻¹}=id`)、
  helpers `conjNormalMulAut_conjNormalMulAut_inv`/`conjMonoidAlgRingHom_conj_inv`/`conjSemilinearEnd_conj_inv`/
  `_inv_conj`/`_one_apply`/`_mul_apply`/`conjMonoidAlgRingHom_algebraMap`/`conjSemilinearEnd_smul_k`、
  `cliffordConjMap_one`/`_mul`/`_smul`/`_apply`、AlgEquiv packaging (commutes' = `cliffordConjMap_smul`+`_one`)。
- **✅ hfix = `cliffordConj_fixed_imp_scalar`** (`[ρ.IsIrreducible][IsAlgClosed k][Module.Finite k V][Nontrivial V]`,
  `hgen : Subgroup.closure (↑H ∪ {x}) = ⊤`): θ-固定 f は scalar。証明 = `commute_conjSemilinearEnd_of_cliffordConj_fixed`
  (`Subgroup.closure_induction` で f が全 ρg と可換: H 上は k[H]-linearity, x 上は hf) → f の固有値 c (V 上で
  `Module.End.exists_eigenvalue (f.restrictScalars k)`) → `ker(fk−c•1)` が ρ(G)-不変 `Subrepresentation` ⟹
  既約で ⊤ ⟹ `f=c•id`。**全部 V 上で実行** (asModule の Module-k 検索回避)。
- **▶ 残 = (1) `IsSimpleRing E` + (2) finrank=1⟹V_H simple bridge + (3) assembly** (= 最終 `restriction_isSimpleModule`,
  group-level Thm 2.5 が消費)。
- **⚠⚠ KEY BLOCKER (次セッション最初に解く)**: **`Module k (resRep ρ H).asModule` が bare `inferInstance` で
  見つからない** (deriving 由来; type-ascription `(... : Module.End k …)` や `restrictScalars`/`asModuleEquiv`
  経由なら解決するが、`Module.End.exists_eigenvalue` / Maschke `IsSemisimpleModule k[↥H] asModule` /
  `linearEquiv_fun` の `Module.Finite k[↥H] asModule` は bare 検索 ⟹ 全部失敗)。smul 自体は V と **defeq**
  (確認済 `rfl`)。**回避策候補**: (a) section/proof 冒頭で derived instance を名前指定 `attribute [local instance]`
  (deriving 生成名を要特定) ‖ (b) `letI` で V 由来を consistent に注入 (Module.Finite と diamond 注意, smul defeq
  なので可能性あり) ‖ (c) IsSimpleRing E を `asModuleEquiv` で V の End へ全 transport してから組む。
  hfix では (V 上実行 + `f.restrictScalars k` ascription) でこの罠を回避できた — 同手法を IsSimpleRing E にも。
- **IsSimpleRing E の math**: V W-isotypic + Maschke ⟹ `V≅Fin m→W` (`linearEquiv_fun`) ⟹
  `E≅ₐ Matrix m m (End_{k[H]}W)` (`endVecAlgEquivMatrixEnd`+`e.conjAlgEquiv`), `End_{k[H]}W≅k`
  (module-Schur `algebraMap_end_bijective_of_isSimpleModule`), `Matrix.isSimpleRing` (m≥1) → transport
  (`IsSimpleRing.of_ringEquiv`)。**前提 instance (要 derive, 上記 blocker)**: `IsSemisimpleModule k[↥H] asModule`
  (Maschke, `[Finite ↥H][NeZero (Nat.card ↥H:k)]`), `Module.Finite k[↥H] asModule`。
- **bridge math**: `finrank E=1` ⟹ E=scalar。W の補元 (Maschke) の射影 p∈E は idempotent, scalar (c•id),
  c∈{0,1}, range p=W, W≠⊥ ⟹ W=⊤ ⟹ `IsSimpleModule k[↥H] asModule`。
- **assembly**: `restriction_isSimpleModule` — isotypic (`isIsotypicOfType_of_conjugates`) + IsSimpleRing E +
  `finrank_eq_one_of_aut_fixedScalar (cliffordConj ρ x) (cliffordConj_fixed_imp_scalar …)` ⟹ finrank E=1 ⟹ bridge
  ⟹ `IsSimpleModule k[↥H] (resRep ρ H).asModule` = `Representation.IsIrreducible (resRep ρ H)` (= hVP, group-level Thm2.5 消費)。

### ✅✅✅ wire-E COMPLETE (2026-06-08 続き, `a-keystone`): hVP = Prop 2.2(a) discharged (mod hconj=Gor5.5.4)

`CliffordMultiplicityOne.lean` 完成 — **`restriction_isSimpleModule` + `restriction_isIrreducible`**
(sorry-free + axiom-clean [propext/Choice/Quot のみ], full build **3611** green + AxiomsCheck OK)。
**新 commit (このセッション)**; main 未マージ (司令塔がマージ予定)。

- **`restriction_isSimpleModule`** (`[ρ.IsIrreducible][IsAlgClosed k][Module.Finite k V][Nontrivial V][Finite ↥H]
  [NeZero (Nat.card ↥H:k)]`, `x`, `hgen:closure(↑H∪{x})=⊤`, `W` 非零 simple `k[↥H]`-部分加群, `hconj`):
  `IsSimpleModule k[↥H] (resRep ρ H).asModule`。証明 = 計画どおり: isotypic → `linearEquiv_fun` で `V≅Fin n→W`
  → Schur `End_{k[H]}W≅k` (`AlgEquiv.ofBijective (Algebra.ofId k _) (algebraMap_end_bijective_of_isSimpleModule)`)
  → `Ψ : E ≃ₐ[k] Matrix (Fin n)(Fin n) k` (`e.conjAlgEquiv k` ▸ `endVecAlgEquivMatrixEnd ..` ▸ `schur.symm.mapMatrix`)
  → `IsSimpleRing E`+`FiniteDimensional E` を Ψ で transport → `finrank_eq_one_of_aut_fixedScalar (cliffordConj ρ x) hfix`
  ⟹ `finrank E=1` ⟹ `Module.finrank_matrix`+`Nat.dvd_one` で `n=1` ⟹ `V≅W` (`LinearEquiv.funUnique`) ⟹
  `IsSimpleModule.congr`。n≠0 は `e.toEquiv.subsingleton`+`not_subsingleton` で nontrivial 矛盾。
- **`restriction_isIrreducible`** = `(resRep ρ H).IsIrreducible` (= `Representation.IsIrreducible (ρ.comp H.subtype)`,
  group-level Thm 2.5 `finrank_modEq_of_faithful_irreducible` が直消費する形)。
  `Representation.irreducible_iff_isSimpleModule_asModule` でラップ。

- **🔑 KEY BLOCKER 解決法 (再調査不要)**: notes 旧「`Module k (resRep ρ H).asModule` bare inferInstance 失敗」=
  **`set_option backward.isDefEq.respectTransparency false in`** を定理頭に付ければ全解決 (CliffordAlgClosed/Irreducible/
  Semisimple と同じ; instance 名 `instModuleMonoidAlgebraAsModule`)。これで `Module k[↥H] asModule` / Maschke
  `IsSemisimpleModule` (via `← isSemisimpleRepresentation_iff_isSemisimpleModule_asModule; infer_instance`) /
  `IsScalarTower k k[↥H] asModule` / `Module.Finite k asModule` が解決。
- **diamond fix の確定レシピ**:
  - `Module.Finite k[↥H] asModule` = `Module.Finite.of_restrictScalars_finite k k[↥H] _` (k-finite + scalar tower)。
  - `Module.Finite k ↥W` (submodule) = `haveI : IsNoetherian k asModule := inferInstance` →
    `Module.Finite.of_injective ((W.subtype).restrictScalars k) Subtype.val_injective`。
  - `Nontrivial asModule` = `‹Nontrivial V›` (defeq ascription; bare inferInstance は不可)。
  - `endVecAlgEquivMatrixEnd` の明示引数順は `ι R A M` → **`..` で全推論**させる (mathlib WedderburnArtin と同様)。
- **▶▶ hVP は hconj (`W≅W^g`) を仮説に取った形で COMPLETE。残る = hconj 供給 + group-setup 配線。**

### 🔁 hconj は Gor 5.5.4 をゼロ形式化しない — char_orthonormal 経路 (2026-06-08 訂正, 再調査不要)

**重要な訂正**: 旧 notes は hconj (`W≅W^g`) を「Gor 5.5.4 = extraspecial faithful irred 一意性、mathlib 不在、
複数セッションの新規ピース」と記録していたが、これは**過大評価で誤り**。BG mmd **L756** が出所:
> "by **G** Thm 5.5.4 … a faithful irreducible rep of an extraspecial group is **determined by its center**.
> It follows that … M and M^g are isomorphic."

これは **既形式化の Gor 5.5.5 + mathlib 一般体指標直交性**で出る (Gor 5.5.4 本体不要):
- ✅ **`character_eq_zero_of_notMem_center`** (`ExtraspecialFaithful.lean`, **一般 alg-closed F**, 既証 = Gor 5.5.5):
  faithful irred + class≤2 ⟹ χ は Z(P) 外で 0。
- ✅ **mathlib `Representation.char_orthonormal`** (`RepresentationTheory/Character.lean:230`, **一般 alg-closed k +
  `Invertible (Nat.card G:k)`** — ℂ-pin でない!): `[IsIrreducible ρ][IsIrreducible σ]` ⟹
  `(card G)⁻¹·∑ ρ.char g · σ.char g⁻¹ = if Nonempty (σ.Equiv ρ) then 1 else 0`。
  + `card_inv_mul_sum_char_mul_char_eq_finrank` (= `⟨χ⟩ = finrank (IntertwiningMap ρ σ)`), `char_conj`
  (`ρ.char (hgh⁻¹)=ρ.char g`), `char_iso`, `Representation.character g := trace k V (ρ g)`, `Representation.Equiv`
  (`Intertwining.lean:232`)。
- **論法**: W faithful irred P-加群 (V_P の constituent, BG 2.10), g が Z(P) を中心化 (C_P(x)=Z(P) ⟹ x が Z 上自明,
  一般 g=p·xᵏ も Z 中心化) ⟹ **χ_{W^g}(h)=χ_W(g⁻¹hg)=χ_W(h)** (h∈Z は g 固定; h∉Z は両者 0 by χ-vanishing)
  ⟹ `⟨χ_W,χ_W⟩=1≠0` ⟹ `Nonempty (W^g.Equiv W)` ⟹ **W≅W^g = hconj**。
- **NeZero→Invertible**: 体上 `NeZero (Nat.card ↥H:k)` ⟹ `Invertible` (非零元は単元); `Fintype ↥H` from `Finite`.
- **残工数 (focused session 級, NOT multi-session)**: (1) 共役部分加群 `W.map (conjSemilinearEnd ρ g)` を
  `Representation k ↥H` として実現しその指標 = χ_W(g⁻¹·g) を示す plumbing (conjSemilinearEnd の twist 利用,
  CliffordAlgClosed と同系統) → (2) χ 等式 (χ-vanishing + g 中心化) → (3) char_orthonormal で `W≅W^g` → hconj。
- **group-setup 配線**: W = V_P の simple constituent (非零 f.d. semisimple から存在), W faithful (BG 2.10), hgen
  (`closure(↑P∪{x})=⊤`, = `G=P⋊⟨x⟩`) → `restriction_isIrreducible` 呼出 ⟹ hVP materialize。
  ⟹ Thm 2.5 → Thm 3.4 (parity 矛盾) → 3.5 → 3.6 → §10.6 が開く。
- **⚠ Isaacs FGT には無い** (S02 表確認済: FGT は character/Clifford 章なし); repo の `CharacterCompleteness`/
  `CharacterConjugate`/`CharacterRowOrthogonality` は **ℂ-pin** ゆえ一般 k に使えない — **mathlib `char_orthonormal`
  (一般体) が正解の経路**。

### ✅✅✅ character route to hconj COMPLETE (2026-06-08 cont., `CliffordConjugateChar.lean`, commits `836324bf`+`83cf1180`)

**hconj の指標論機械が完成** (sorry-free + axiom-clean, full build 3612 green)。hconj は今や**群入力だけ**に還元:
- ✅ `repEquiv ρ g`/`repEquiv_conj` (ρg を k-線形 auto 化 + 大域共役 `ρh∘ρg=ρg∘ρ(g⁻¹hg)`)。
- ✅ `subRep_coe_smul`/`subRepAsModuleEquiv`/`subRep_isIrreducible`/`equivAsModule` (一般体 subrep↔asModule 基盤;
  CharacterCompleteness の ℂ-pin `ofSubmodulePrime*` の一般 k 版。**⚠ ℂ 重複は後で統一すべき** — spawn task 候補)。
- ✅ `character_subRep_conj` : `χ_{(ρg)W}(h) = χ_W(g⁻¹hg)` (`char_iso` + `repEquiv` で共役表現の同型)。
- ✅ `character_subRep_conj_eq` : W faithful simple class≤2 + g が Z(H) 中心化 ⟹ `χ_{W^g}=χ_W`
  (共役指標 + `character_eq_zero_of_notMem_center` [Gor 5.5.5, 既証] + `mulEquiv_mem_center_iff`)。
- ✅ `submodule_iso_of_character_eq` : 等指標 ⟹ `W≅(ρg)W` (`Representation.char_orthonormal` 一般体 + Equiv→submodule)。
- ✅ `conjugate_submodule_iso` : **per-g hconj capstone** = `restriction_isIrreducible`/`isIsotypicOfType_of_conjugates`
  が消費する形 (`Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd ρ g)))`), 仮説 = `[IsSimpleModule k[↥H] ↥W]`
  + hf (faithful) + hcl (class≤2) + hgc (g が Z 中心化)。

**▶▶ 残 = 群入力のみ (group-wiring)**:
- ✅✅ **hgc/W存在/hgen/∀g hconj/assembly DONE** (2026-06-08 cont., commit `fed77d1b`, full 3612 green):
  - `conjNormalMulAut_center_eq_of_closure` (hgc): `C_G(z)` が P と x を含む ⟹ ⟨P,x⟩=⊤ ⟹ ∀g が Z(P) 中心化。
    仮説 = `hxZ` (x が Z(P) 中心化, = `C_P(x)=Z(P)` の ⊇ 方向) + hgen。
  - **`restriction_isIrreducible_of_faithful_constituents`** (materialization): ρ 既約/alg-closed/`char∤|H|`,
    `⟨H,x⟩=⊤`, class≤2, x が Z(H) 中心化, **∀ 非零 simple constituent が faithful (hf)** ⟹ `(resRep ρ H).IsIrreducible`。
    W 存在 (`exists_simple_submodule`) + ∀g hconj (`conjugate_submodule_iso`) + `restriction_isIrreducible` を組立。
- **▶▶▶ 残る唯一の入力 = hf = constituent faithful (BG 2.10) — ✅ TRACTABLE (多セッション級でない), 証明スケッチ確定**:
  **鍵 = `OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial`** (`Ch01_Sylow/Main.lean:357`, 既証:
  finite p-group の非自明正規 N ⟹ `N ⊓ Z(P)` nontrivial)。証明手順:
  1. **unique minimal normal** (新 helper, `IsExtraspecial.lean` 候補): `IsExtraspecial p ↥P` + `[Finite]` + N⊴P, N≠⊥ ⟹
     Z(P)≤N。`normal_inf_center_nontrivial` で N⊓Z≠⊥, `center_card=p` prime ⟹ N⊓Z=Z (prime-order subgroup は ⊥/⊤;
     card-dvd or `subgroupOf` + IsSimpleOrder ルート) ⟹ Z≤N。
  2. **faithfulness** (新 thm, hf を discharge): ρ_W=(ofSubmodule' W).toRepresentation の ker は ⊴↥P。ker≠⊥ なら
     Z(↥P)≤ker (上記) ⟹ Z(↥P) が W に自明作用。各共役 ρg(W) でも自明 (z 作用 = ρ(z), w'=ρg w で ρ(z)ρg w=ρ(zg)w=
     ρg ρ(g⁻¹zg)w, g⁻¹zg∈Z(P) 自明 ⟹ =w')。共役 span ⊤ (`iSup_map_conjSemilinearEnd_eq_top`, ρ既約) ⟹ Z(↥P) が V 自明 ⟹
     Z(↥P)⊆ker ρ=⊥ (ρ faithful) ⟹ |Z|=1, `center_card=p` と矛盾 ⟹ ker=⊥ ⟹ ρ_W injective。
  discharge ⟹ materialization → hVP → Thm 2.5 (`finrank_modEq_of_faithful_irreducible`) → 3.4 → 3.6 → §10.6 全開放。
  ※ hxZ (x が Z(P) 中心化) も group-level setup の `C_P(x)=Z(P)` 完全等号から供給要 (現状 finrank_modEq の hCP は ⊆ のみ)。
  ※ 要 `[Fact p.Prime]` + `IsExtraspecial p ↥P` を faithfulness thm の仮説に。CliffordConjugateChar が IsExtraspecial を import。
