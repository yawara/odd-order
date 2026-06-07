# Rep-theory lane handoff — alg-closed extraspecial rep theory (BG Thm 3.4) — 2026-06-07

**Status update (2026-06-07, loop iteration on `bg-reptower`): two earlier "blockers" turned out
to be NON-blockers — both keystones are already in mathlib.** This note supersedes the pessimistic
2026-06-07-AM version. The tower is much more tractable than first feared.

## ✅ DONE this iteration (do NOT redo) — all sorry-free, axiom-clean

- **Step 1 — Prop 2.1 / Burnside** (`AbsolutelyIrreducible.lean`):
  - `toModuleEnd_surjective_of_isAlgClosed` (module form): `M` fin-dim simple over `F`-algebra `A`,
    `F` alg-closed ⟹ `A → End_F M` surjective (enveloping algebra = `End_F M`).
  - `asAlgebraHom_surjective_of_isAlgClosed` (representation form): `ρ.asAlgebraHom : F[G] →ₐ End_F V`
    surjective for fin-dim irreducible `ρ` over alg-closed `F`. = BG `E(P) = Hom_F(V,V)`.
  - **KEY: the feared ~150-line Wedderburn gap ("semisimple + faithful simple ⟹ simple ring") is NOT
    needed.** Burnside = mathlib `Module.Finite.toModuleEnd_moduleEnd_surjective` (Jacobson density,
    `RingTheory/SimpleModule/Basic.lean:588`) + alg-closed Schur
    `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`
    (`RepresentationTheory/AlgebraRepresentation/Basic.lean:28`). Since the commutant `D = End_A M`
    is the scalars `F` (Schur), `End_D M = End_F M` and Jacobson IS Burnside. ~20 lines.
  - asModule-synonym instance trap (the prior blocker on the Schur leaf): solved by
    `set_option backward.isDefEq.respectTransparency false` (the idiom mathlib uses for the
    `IsScalarTower k k[G] ρ.asModule` instance). Then `toModuleEnd F ρ.asModule r ≡ ρ.asAlgebraHom r`
    by defeq, so the representation form is `exact ⟨r, hr⟩`.

- **Step 2 foundation — central character** (`AbsolutelyIrreducible.lean`, `center_isScalar`):
  fin-dim irreducible `ρ` over alg-closed `F`, `z ∈ Z(G)` ⟹ `∃ c, ρ z = c • id`. Via
  `ρ z` is a self-intertwiner (z central) + `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`
  (`RepresentationTheory/Irreducible.lean`). `IntertwiningMap` algebra/coe lemmas are all `rfl` so the
  scalar is extracted by defeq (NB: `IntertwiningMap.coe_smul`/`coe_one`/`algebraMap_apply` did NOT
  resolve by name in `simp only` — use the defeq `have hv : c • v = ρ z v := DFunLike.congr_fun hc v`).

- (banked earlier) base-change `BaseChange.lean` (`baseChangeRepresentation`, BG (2.9)); Gor 5.3.7
  (`S04e_GorThm37`); Lem 3.1, Lem 3.3 (`S03b_Lemma33`); Prop 2.4 (`EigenspaceUnderCyclicAction`).

## ▶ NEXT: Gor 5.5.5 (`ExtraspecialFaithful.lean`, still a skeleton) — NOW TRACTABLE

**KEY DISCOVERY: mathlib has FIELD-VALUED character orthogonality over general alg-closed `k`** (no
`star`/ℂ needed), AND at the **`Representation` level** (no FDRep bridging!) —
`Representation.char_orthonormal` (`RepresentationTheory/Character.lean:230`):
for `[Group G] [Field k] [IsAlgClosed k] [Fintype G] [Invertible (Nat.card G : k)]`,
`[IsIrreducible ρ] [IsIrreducible σ]`,
`(Nat.card G : k)⁻¹ * ∑ g, ρ.character g * σ.character g⁻¹ = if Nonempty (Equiv σ ρ) then 1 else 0`.
For `ρ = σ`: `∑ g, χ(g) χ(g⁻¹) = |G|` (`Equiv ρ ρ` nonempty via `refl`). Companions (all
`Representation`-level): `Representation.char_one : ρ.character 1 = finrank k V`,
`Representation.char_conj : ρ.character (h*g*h⁻¹) = ρ.character g`,
`Representation.character` (= `fun g => LinearMap.trace _ _ (ρ g)`).
**Use these `Representation.*` versions directly — no `FDRep.of`/`Simple`-bridge needed. The repo's
ℂ-pinned `RowOrthogonality`/`SecondOrthogonality` (`star`) are NOT needed.**

**Recommended split** (the "2n even" structure is isolated to a pure group-theory leaf):

**What Thm 2.5 actually needs (re-read of BG proof, mmd L756/L766):** the *integer* equation
**`(dim V)² = |P/Z|`** — it is used to say the `|P/Z|` images of `Z`-coset reps form a *basis* of
`E(P)` (BG (2.11)), needing `dim E(P) = (dim V)² = |P/Z|` exactly. So the deliverable is this **ℕ
equation**, not just an `F`-equation.

**⚠ char-p descent subtlety (the real point):** `Representation.char_orthonormal` lives in `F`. Over
`char r > 0` the cast `ℕ → F` is NOT injective, so the `F`-equation `(d:F)²·(|Z|:F) = (|P|:F)` does
**not** by itself give the ℕ equation. The clean fix is a **trace-form Gram-matrix** argument (no
Stone–von-Neumann, no "deg ∣ |G|" needed):

- **5.5.5a-i ✅ DONE** (`character_eq_zero_of_notMem_center`, commit `b3017ac`): faithful irreducible,
  `commutator P ≤ Z(P)` ⟹ `χ g = 0` for `g ∉ Z(P)`. (Uses `center_isScalar` + `char_conj` + the
  `x g x⁻¹ = ⁅x,g⁆ g` identity + faithfulness `c ≠ 1`.)
- **5.5.5a-ii (mass formula in F):** `char_orthonormal ρ ρ` ⟹ `∑_g χ(g)χ(g⁻¹) = (|P|:F)`; split off `Z`
  by (i); for `z ∈ Z`, `χ(z)χ(z⁻¹) = (d:F)²` (`ρ z = c•id`, `ρ z⁻¹ = c⁻¹•id`, `χ z = c·d`,
  `χ z⁻¹ = c⁻¹·d`, product `= d²`). Sum ⟹ `(|Z|:F)·(d:F)² = (|P|:F)`, i.e. `(d:F)² = (|P/Z|:F)`.
- **5.5.5a-iii `(d:F) ≠ 0`** — the KEY enabler: from `(d:F)² = (|P/Z|:F)` and `(|P/Z|:F) ≠ 0`
  (`|P/Z| ∣ |P|`, `char ∤ |P|`). So `char ∤ dim V` *without* needing degree-divides-order.
- **5.5.5a-iv spanning** `(dim V)² ≤ |P/Z|`: Burnside `E(P) = End_F V` (✅ `asAlgebraHom_surjective…`)
  + `Z` acts by scalars (`center_isScalar`) ⟹ `E(P) = ∑_{g∈R} F·g` (`R` = `Z`-coset reps), so
  `dim E ≤ |R| = |P/Z|`.
- **5.5.5a-v independence** `(dim V)² ≥ |P/Z|`: the Gram matrix `[trace(ρ gᵢ · ρ gⱼ⁻¹)]_{R×R}
  = [χ(gᵢ gⱼ⁻¹)]` is `(d:F)·I` (off-diag: `gᵢgⱼ⁻¹ ∉ Z` ⟹ `0` by (i); diag: `χ 1 = (d:F)`),
  nonsingular by (iii) ⟹ the `|P/Z|` images are `F`-independent in `E(P)`.
- **5.5.5a-vi assembly:** iv + v ⟹ **`(dim V)² = |P/Z|`** (ℕ). ∎
  Work at the `Representation` level (`Representation.char_orthonormal`, no FDRep bridge). The sum
  split is `Finset.sum_subset`/filter over `g ∈ center` (`DecidablePred`, classical).

- **5.5.5b (pure group theory):** extraspecial `P` of order `q^{1+2n}` ⟹ `|P| = q · q^{2n}` with the
  exponent `2n` even (nondegenerate symplectic form on `P/Z` from the commutator). Combined with
  5.5.5a (`d² q = |P| = q^{2n+1}`) ⟹ `d² = q^{2n}` ⟹ `d = qⁿ`. (`IsExtraspecial` gives `center_card`,
  `commutator_eq_center`; the even-rank fact may itself be a sub-leaf — check mathlib
  `GroupTheory`/symplectic for `extraspecial card`.)

## Then Steps 3-5 — the assembly phase (LARGER than "routine"; ~4 substantial leaves)
**Recon (2026-06-07, iter 6): Thm 2.5 needs TWO unbuilt pieces beyond the done core, plus assembly.**
- **Prop 2.4(j) — ✅ DONE** in new file `CyclicEndConjCount.lean` (`prop24j`, axiom-clean): under
  `∀ m≠0, ∑ᵢ(nᵢ−nᵢ₊ₘ)²=2` with `h≥2`, `∃ i₁ v₀ δ=±1, (∀ i≠i₁, nᵢ=v₀) ∧ n_{i₁}=v₀+δ ∧ ∑nᵢ=h·v₀+δ`
  (so `∑nᵢ ≡ ±1 mod h`). Proved by a **counting route** (NOT the textbook cyclic-arc geometry):
  sub-lemma 1 (`∑d=0,∑d²=2 ⟹ one +1/−1`) → per-shift count = 2 → total moved-pairs `2(h−1)` →
  `∑mult = (h−1)²+1` → max-multiplicity index has mult `h−1` (one outlier) → `(n_{i₁}−v₀)²=1`.
  Takes the `∑(nᵢ−nᵢ₊ₘ)²=2` hypothesis abstractly (`n : ZMod h → ℤ`); general, field-free.
- **(k) — ✅ DONE** (`prop24k`, CyclicEndConjCount.lean): `C_V(H)=0 ⟹ q=h−1`.
- **(c) — ✅ DONE** (`EigenspaceBlockDecomp.lean`, all axiom-clean): the `End V = ⊕_{i,t} E_{i,t}`
  block internal direct sum is built from scratch (no mathlib shortcut):
  `sum_cyclicEigenspaceFinDecomposition_eq` (reconstruction ∑ᵢ compᵢ v = v) →
  `sum_cyclicHomBlockFinProjection_eq` (every e = ∑ block-projections, via `Submodule.iSup_induction'`) →
  `iSup_cyclicHomBlockFin_eq_top` → `isInternal_cyclicHomBlockFin` (`DirectSum.IsInternal`, via
  coeLinearMap surjective + `∑ dim E_{i,t}=(dim V)²=dim End` ⟹ bijective by
  `injective_iff_surjective_of_finrank_eq_finrank`).
- **(g) — ✅ DONE** (`finrank_cyclicEndConjEigenspaceFin`, EigenspaceBlockDecomp.lean, axiom-clean):
  `dim E_m = ∑ᵢ nᵢ·nᵢ₊ₘ`. Built bottom-up: `finrank_iSup_of_iSupIndep` (general
  `dim(⨆ indep)=∑dim`) → `finrank_iSup_cyclicHomBlockFin_diagonal` (`dim(⨆ᵢ E_{i,i+m})=∑nᵢnᵢ₊ₘ`,
  m-diagonal sub-family of (c)) → `iSup_cyclicHomBlockFin_diagonal_le` (`⨆ᵢ E_{i,i+m} ≤ E_m`) →
  the dimension sandwich (E_m independent via `cyclicEigenspaceFin_iSupIndep` for the conj operator
  + ∑ₘ∑ᵢ = (dim V)² = dim End ⟹ termwise). Key hyps: `IsPrimitiveRoot epsilon h`, hV.
- **(h) — ✅ DONE** (`sum_sq_sub_finrank_cyclicEndConjEigenspaceFin`, axiom-clean):
  `∑ᵢ((nᵢ:ℤ)−nᵢ₊ₘ)² = 2(dim E_0 − dim E_m)`. Via (g) at m and 0 + `sum_sub_sq_of_sum_sq_eq`
  (elementary) + reindex `∑nᵢ₊ₘ²=∑nᵢ²`. **⟹ full BG Prop 2.4 chain (a)(c)(d)(g)(h)(j)(k) COMPLETE.**
  With the Thm 2.5 hyp `dim E_0 = dim E_m+1 ∀m≢0` this gives `∑(nᵢ−nᵢ₊ₘ)²=2` = the prop24j hypothesis.
- **NEXT — Thm 2.5 core** (the real remaining work): assemble `h | qⁿ±1` and `C_V(H)=0 ⟹ h=qⁿ+1`.
  Needs: (1) **E(P) = principal ⊕ (q²−1)/h · regular** as an `H = ⟨x⟩`-module under conjugation
  (from the Burnside basis E(P)=End_F V (Prop 2.1, done) + `C_{P/Z}(x)=1` ⟹ x acts freely off
  scalars), giving `dim E_0 = dim E_m + 1 ∀ m≢0` — substantial group-rep-theory; (2) the
  **Fin h ↔ ZMod h** transport to feed prop24j; (3) Prop 2.2(a) alg-closed Clifford (`V_P = M`);
  (4) base-change wiring (2.9, done) for `C_V(H)=0 ⟹ C_V̄(H)=0`. Then Thm 3.4 assembly.
- **Indexing bridge for prop24j**: `prop24j`/`prop24k` are over `ZMod h → ℤ`; eigenspace dims are
  `Fin h → ℕ`. `ZMod h ≃+ Fin h` (NeZero h) needed to transport the `∑(nᵢ−nᵢ₊ₘ)²=2` hypothesis.
- **(g)(h) bridge — leftover detail**:
    - **(g)** `dim E_m = ∑ᵢ nᵢ·nᵢ₊ₘ`. **Route fixed (iter 18)** — AVOID the eigenvalue-uniqueness
      refinement (`E_m = ⊕_{t−i≡m} E_{i,t}` ⊆-direction). Instead: (i) sub-family finrank
      `dim(⨆_{t−i≡m} E_{i,t}) = ∑_{t−i≡m} dim E_{i,t}` [sub-family of `isInternal_cyclicHomBlockFin`
      is `iSupIndep` via `iSupIndep.comp`; **mathlib lacks `finrank(⨆ independent)=∑finrank`** — build
      via sub-family coeLinearMap injective → equiv → `finrank_directSum`]; (ii) `⨆_{t−i≡m} E_{i,t} ≤ E_m`
      [inclusion `cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_modEq`, already in file] ⟹
      `dim E_m ≥ ∑_{t−i≡m} dim E_{i,t}`; (iii) `∑_m dim E_m = dim End` [need `End = ⊕_m E_m`, i.e.
      Prop 2.4(a) for the conj operator `cyclicEndConj g`]; (iv) `∑_m ∑_{t−i≡m} dim E_{i,t} = ∑_all = dim End`
      [(c) + partition]; (v) `dim E_m ≥ Σ_m` termwise with equal total sums ⟹ each `=`. **GOTCHA**:
      `E_m = cyclicEndConjEigenspace` needs `g : GeneralLinearGroup F V` (invertible), but the blocks/(c)
      use `g : Module.End F V` — instantiate (c) at `(g : End)` and carry the GL `g` + `hspan`/`hperiod`/
      ε-primitive hyps from the inclusion lemma's signature.
    - **(h)** `2 dim E_0 − 2 dim E_m = ∑ᵢ(nᵢ−nᵢ₊ₘ)²` from (g) + periodicity `∑ nᵢ² = ∑ nᵢ₊ₘ²`
      (`Equiv.addRight m` reindex on `Fin h`). Then `dim E_0 = dim E_m+1 ∀m≢0` (Thm 2.5 H-module hyp) ⟹
      `∑(nᵢ−nᵢ₊ₘ)²=2`, feeding `prop24j`.
- Larger Thm 2.5 assembly after (g)(h): E(P) = principal + (q²−1)/h regular H-module (Burnside basis
  (2.11) + `C_{P/Z}(x)=1`); Prop 2.2(a) alg-closed Clifford; base-change wiring — several leaves each.
- **Prop 2.2(a) alg-closed (Clifford `V_K = M`) — NOT built**; `Clifford.lean` is ℂ. Real Clifford
  theory over alg-closed F (M irred H-module, H◁G, M≅M^x, G/H cyclic ⟹ V_H irreducible = M).
- **Thm 2.5 assembly**: base-change (2.9 ✅) → reduce to alg-closed faithful irred → Prop 2.2(a) `V_P=M`
  → Gor 5.5.5a `(dim V)²=|P/Z|` (✅) + Burnside `E(P)=End` (✅) ⟹ coset reps are a basis (BG (2.11))
  → H-conjugation on `E(P)` is principal + `(q²−1)/h` regular (uses Prop 1.5 `C_{P/Z}(x)=1`) → Prop 2.4(j)(k)
  ⟹ `h | qⁿ±1` (with `q := dim V`). Big interconnected proof.
- **Thm 3.4** (`S03d_Thm34.lean`): Maschke → faithful irred → Gor 5.3.7 (✅ `S04e`) → elem-abelian case
  (Frobenius/Lem 3.1/3.3 ✅) / special case (Thm 2.5) → contradiction `h` even vs odd.
- Prop 1.5 (`C_{P/Z}(x)=1`): check `S01_Solvable` / Isaacs; small if present.

## Bottom line
The rep-theory tower is **NOT** the multi-session mathlib-gap build the AM blocker feared. Both hard
keystones (Burnside, character orthogonality over general alg-closed fields) are in mathlib. The one
real subtlety — that the `F`-valued character sum doesn't descend to the needed ℕ equation over
`char r` — is resolved by the trace-form Gram-matrix argument above (`(d:F) ≠ 0` bootstrapped from the
mass formula), avoiding Stone–von-Neumann and degree-divides-order entirely. Remaining work is real but
routine assembly.

**✅ 5.5.5a DONE** (`a6473bc` `sq_finrank_eq_card_quotient_center`: `(dim V)² = Nat.card (P ⧸ Z(P))`
for faithful irreducible, `commutator P ≤ Z(P)`, alg-closed, `char ∤ |P|`). All of i–vi landed
(`b3017ac` char-vanish, `e3cc34c` mass formula, `40ef1d2` `(dim V:F)≠0`, `ef6b560` independence ≥,
`a6473bc` spanning ≤ + assembly). The whole tower is sorry-free + axiom-clean.

**Important observation for Step 4 (Thm 2.5):** the deliverable `(dim V)² = |P/Z|` is exactly what BG
(2.11) uses (the `|P/Z|` coset-rep images are a *basis* of `E(P)`, since `|P/Z| = dim E(P)`). BG calls
`dim V = pⁿ` and `|P/Z| = p^{2n}`, but those equalities are just *naming* `q := dim V`; the divisibility
conclusion `h | pⁿ ± 1` is `h | dim V ± 1`. So **5.5.5b (extraspecial `|P| = q^{1+2n}`, the even-rank
symplectic group theory) is likely NOT needed for Thm 2.5** — use `dim V` directly as `q`. Confirm when
wiring Thm 2.5; only prove 5.5.5b if the final Thm 3.4 arithmetic genuinely needs `dim V = qⁿ` literally.
