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

### ▶▶ Precise next steps (2026-06-08) — `finrank_modEq_of_faithful_irreducible` reduces Thm 2.5
### divisibility to exactly TWO open hypotheses; discharge them:

1. **`hcent` (Prop 1.5, the smaller piece, tool IDENTIFIED)** — from the BG hypothesis `C_P(xᵏ) = Z(P)`
   (`xᵏ ≠ 1`) derive `∀ k≠0, ∀ c, (quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c = c → c = 1`.
   Use **`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal`** (ForwardFromCh03.lean:794):
   `{φ : A →* MulAut G} {N ⊴ G} (hCop : Coprime |A| |N|) (hSolv : Solvable A ∨ Solvable N)`
   `(hN_inv : IsAInvariant φ N) {g} (hg_fix : ∀ a, ∃ n∈N, φ a g = g*n) : ∃ c, (∀ a, φ a c = c) ∧ ∃ n∈N, c = g*n`.
   Setup: `A = Subgroup.zpowers (conjAutOfNormal P x ^ k.val)` ≤ `MulAut P`, `φ = A.subtype`, `G = P`,
   `N = center P` (abelian ⟹ `hSolv` right; characteristic ⟹ `hN_inv`); `Coprime |A| |Z|` from `|A| ∣ h`
   (`(conjAutOfNormal P x)^h = 1`) + `|Z| ∣ |P|` p-power + `gcd(h,p)=1`. `g = Quotient.out c`, `hg_fix`
   from `σ^{k·j} c = c` (iterate `σ^k c = c`). Lift gives `c'` conj(xᵏ)-fixed ⟹ `c' ∈ C_P(xᵏ) = Z = N`
   ⟹ `g = c'·n⁻¹ ∈ Z` ⟹ `⟦g⟧ = c = 1`. ~80-120 lines (A-action plumbing + coprimality + the bridges).
   `C_P(xᵏ)` (centralizer in P) = `{p : P | conj(xᵏ) p = p}` (fixed points of the conj aut) — same set.

2. **`hVP` (Prop 2.2(a) alg-closed Clifford, the BIG piece)** — `Representation.IsIrreducible (ρ.comp P.subtype)`
   from: `ρ` faithful irreducible `F[G]`-module, `P ⊴ G`, `G/P` cyclic, `F` alg-closed, and `M ≅ M^g`
   ∀g (all `P`-conjugates of an irred submodule `M` isomorphic — from "faithful irred of extraspecial
   determined by center", Gor 5.5.4). BG mmd L614-647: build `L` extending `M`, `τ`-cocycle, `τx`
   generates `Hom_FG(L,L) = F` (Prop 2.1 ✅), so `V_P` irreducible. `Clifford.lean` is **ℂ-pinned**
   (no destructive edit) ⟹ NEW file `CliffordAlgClosed.lean` (or alg-closed section). Multi-session.
   Needs Gor 5.5.4 ("faithful irred determined by central char") too — `ExtraspecialFaithful.lean` has
   `center_isScalar` + `sq_finrank_eq_card_quotient_center`; 5.5.4 = "two faithful irreds with equal
   central char are isomorphic" is a separate sub-piece.

After both: `finrank_modEq_of_faithful_irreducible` is a genuine grounded Thm 2.5 (divisibility). Then:
3. **C_V(H)=0 half** of Thm 2.5 (`h ≠ pⁿ+1 ⟹ C_V(H) ≠ 0`) — near-copy of `finrank_modEq…` using
   `sum_eigenspaceFinDim_eq_sub_one_of_finrank_cyclicEndConjEigenspace` (✅ in ExtraspecialThm25) +
   `dim V₀ = 0` hypothesis ⟹ `dim V = h − 1`. Low-risk wiring (extract shared setup to a private lemma).
4. **Thm 3.4** (`S03d_Thm34.lean`, new): Maschke → faithful irred → Gor 5.3.7 → special case = Thm 2.5
   → parity contradiction (`h = pⁿ+1` even vs `|G|` odd). Then Thm 3.5 → Thm 3.6 → §10.6 → §10/§11.
