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

- **5.5.5a (representation theory, the meat):** `P` finite, `Z := Z(P)`, `[P,P] = Z` (= extraspecial's
  `commutator_eq_center`), `|Z| = q` prime, `F` alg-closed with `char ∤ |P|`, `V` a faithful simple
  `FDRep F P`. Then **`(dim V)² · q = |P|`** (equivalently `(dim V)² = |P| / |Z|`). Lemma chain:
  1. `λ : Z → F` central character from `center_isScalar` (✅). Faithful ⟹ `λ z = 1 ↔ z = 1`
     (if `ρ z = id` then `z = 1`), so `z ≠ 1 ⟹ λ z ≠ 1`.
  2. `χ(g z) = λ(z) · χ(g)` for `z ∈ Z` (trace of `ρ g ∘ (λ z • id)`).
  3. **χ vanishes off Z:** `g ∉ Z ⟹ χ g = 0`. Group fact: `g ∉ Z(P) ⟹ ∃ x, [g,x] ≠ 1`; then
     `gˣ = g·[g,x]` with `z₀ := [g,x] ∈ [P,P] = Z` (extraspecial!), `z₀ ≠ 1`. So `g ~ g z₀`, giving
     `χ g = χ(g z₀) = λ(z₀) χ g` with `λ(z₀) ≠ 1` ⟹ `χ g = 0`.
  4. `char_orthonormal V V`: `∑_{g} χ(g)χ(g⁻¹) = |P|`. Split off Z (vanishing): `= ∑_{z∈Z} χ(z)χ(z⁻¹)`.
  5. `χ(z) = λ(z)·d`, `χ(z⁻¹) = λ(z)⁻¹·d` (d = dim V), product `= d²`. Sum over `z∈Z`: `= |Z|·d² = q d²`.
  6. `q d² = |P|`. ∎
  Risk: bridging "BG faithful irreducible" ⇝ `Simple (FDRep.of ...)`; the conjugacy-class sum split
  (`Finset` over `G \ Z`); `char` of `FDRep` vs `Representation` (use `FDRep.character`).

- **5.5.5b (pure group theory):** extraspecial `P` of order `q^{1+2n}` ⟹ `|P| = q · q^{2n}` with the
  exponent `2n` even (nondegenerate symplectic form on `P/Z` from the commutator). Combined with
  5.5.5a (`d² q = |P| = q^{2n+1}`) ⟹ `d² = q^{2n}` ⟹ `d = qⁿ`. (`IsExtraspecial` gives `center_card`,
  `commutator_eq_center`; the even-rank fact may itself be a sub-leaf — check mathlib
  `GroupTheory`/symplectic for `extraspecial card`.)

## Then Steps 3-5 (unchanged shape, see `s03_loop_task_extraspecial.md`)
- Step 3 Prop 2.2(a) alg-closed (Clifford `V_K = M`) — `Clifford.lean` is ℂ; build alg-closed facts new.
- Step 4 Thm 2.5 (`h | qⁿ ± 1`, `C_V(H)=0 ⟹ h = qⁿ+1`) via Prop 2.4(j)(k) + base-change (2.9).
- Step 5 Thm 3.4 body (`S03d_Thm34.lean`).

## Bottom line
The rep-theory tower is **NOT** the multi-session mathlib-gap build the AM blocker feared. Both hard
keystones (Burnside, character orthogonality over general alg-closed fields) are in mathlib. Remaining
work is real but routine assembly. Resume at **Gor 5.5.5a** (the character computation).
