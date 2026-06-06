# Peterfalvi (6.8) capstone — BLOCKER: producer requires central `Z`, formalization uses `Z = ⁅H,H⁆`

**Status (2026-06-07): the (6.8) capstone `sibleySetup_is_coherent` (S08:7582 sorry,
X-nonempty branch) is BLOCKED by a structural/design flaw, not by missing assembly.**
The X-coherence producer `hstepData` cannot be honestly built at the instantiation the
capstone needs. Filling it would require an unsatisfiable hypothesis (= scaffold, forbidden).

This contradicts the earlier optimistic handoffs ("all building blocks landed, only the
monolithic producer assembly remains"). Those handoffs never checked that the step-data field
`hθsq_le_qtot` is *satisfiable* at `Z = ⁅H,H⁆`. It is not. See [[scaffold-sorry-free-not-done]].

## The math (Peterfalvi source)

`references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd`:

- **(6.6)** (L74): *"Let `Z` be a normal subgroup of `L` such that `1 ≠ Z ⊆ Z(K)`* and let
  `X = S − S(Z)`. … Then `X` is coherent."* — **`Z` must be central in `K = H`.**
- **(6.6) proof** (L80): *"By [Is], Corollary 2.30, `θᵢ(1)² ≤ |K:Z|`, and so `θᵢ(1)²` divides
  `|L|−|L:Z|`."* — the degree bound is **Cor 2.30**, which needs **`Z ⊆ Z(K)`**.
- **(6.8) proof** (L156): *"Set `Z = Z(H) ∩ H′` in case (A) and `Z = W₂` in case (B). Let
  `X = S − S(Z)` and `Y = S(H′)`. As `Z ⊆ H′`, `X ∩ Y = ∅`."* — **`Z = Z(H)∩H′`, central; NOT
  `H′`.** Since `Z ⊊ H′` in general, **`X ∪ Y ⊊ S`** (gap `= S(Z) − S(H′)`), and Peterfalvi
  closes the gap separately in **(6.8.3)** by another (5.6) argument.

Cor 2.30 = `IsIrreducibleCharacter.exists_degree_sq_le_index`
(`OddOrder/GroupTheory/RepresentationTheory/SchurCenterBound.lean:193`):
`φ irreducible, Z ≤ center G ⟹ ∃ d, φ(1)=d ∧ d² ≤ |G:Z|`. **Hypothesis `Z ≤ center G` is essential.**

## Where the formalization diverges

- `Xset Z := S − S(Z)` (S08:3475). Its own docstring: *"for a normal `Z ⊆ Z(H)`"*.
- `Yset := S(⁅H,H⁆) = S(H′)` (S08:3480).
- Capstone routes through
  `coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner`
  → `Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
  which instantiates the general (6.6) consumer at **`Z := ⁅H,H⁆`** (S08:7456).
- This buys the clean partition `Xset ⁅H,H⁆ ∪ Yset = S` (S08:3607) and the tidy X-empty branch
  (`coherenceTarget_of_Xset_empty`), **but ⁅H,H⁆ ⊄ Z(H)** (class ≥ 3 p-groups), so (6.6)/Cor 2.30
  does not apply.

## Why the producer field is unfillable at `Z = ⁅H,H⁆`

Step-data `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (S08:7265) carries, per step:
`hθsq_le_qtot : θχ*θχ ≤ qtot`, `hqtot : qtot = p^mq`, `htotal : total = qtot*c`,
`hsum : ∑members² + ∑tail² = total`.

- `hsum` ⟹ `total = ∑_{χ∈X} χ(1)²` (members ⊔ tail = X, degree-sorted partition).
- `sum_re_sq_Xset_eq` + `index_mul_card_sub_factor`: `total = idx·(|H|−|H:Z|) = |H:Z|·(idx·(|Z|−1))`
  with `idx = |W₁|` coprime to `p`. So the **p-part of `total` is exactly `|H:Z| = |H:⁅H,H⁆| = |H^ab|`**.
- `qtot = p^mq` and `qtot ∣ total` ⟹ `qtot ≤ p-part = |H:⁅H,H⁆|`. With `θχ² ≤ qtot` this forces
  **`θχ² ≤ |H:⁅H,H⁆|`** for every `χ = Ind θ ∈ X` (θ nonlinear irreducible of `H`).

**Counterexample** `H = UT(4,p)` (unitriangular 4×4, an odd p-group for odd `p`, nilpotent ⟹ a
valid Frobenius-kernel candidate): `|H| = p⁶`, `H′ = ⁅H,H⁆` has order `p³` (entries (1,3),(1,4),(2,4)),
so `|H:H′| = p³`. `H` has an irreducible `θ` of degree `p²` (max degree of UT(4,·)); `θ` is
nonlinear ⟹ `Ind θ ∈ X`, and `θ(1)² = p⁴ > p³ = |H:⁅H,H⁆|`. So `hθsq_le_qtot` is **false** for this
`χ`. No `qtot` can satisfy both `θχ² ≤ qtot` and `qtot ∣ total`. ∎

Cor 2.30 only yields `θ² ≤ |H:Z(H)|`; concluding `θ² ≤ |H:⁅H,H⁆|` would need `⁅H,H⁆ ≤ Z(H)`
(class ≤ 2), false in general.

## The general (6.6) machinery is SOUND — only the (6.8) instantiation is wrong

`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X` (S08:7360) is
parameterized by a general normal `Z`; the bound is a *hypothesis* of the step data. At a **central**
`Z` (`Z ≤ Z(H)`) the field is fillable (Cor 2.30). So the (6.6) consumer is reusable as-is; the bug
is purely the §8 capstone-level choice `Z := ⁅H,H⁆` and the `X ⊔ Y = S` shortcut.

## Correct path (matches Peterfalvi; substantial redesign — NOT a sorry-fill)

1. Let **`Zc := (Z(H) ∩ ⁅H,H⁆)`** (case A) — normal in `L` (`Z(H)` char in `H ◁ L`; `⁅H,H⁆ ◁ L`),
   central in `H`, `≠ ⊥` (nonabelian nilpotent ⟹ `Z(H)∩H′ ≠ 1`), `⊆ ⁅H,H⁆`. (Case B: `Zc := W₂`.)
2. `X := Xset Zc = S − S(Zc)`. Apply the general (6.6) consumer at `Z := Zc` — now `hθsq_le_qtot`
   = `exists_degree_sq_le_index (Zc.subgroupOf H) (central proof)`, honestly fillable.
3. `Y := S(⁅H,H⁆)` (= S(H′), equal-degree `|W₁|`, already coherent: `coherentYset`).
4. Glue `X ∪ Y` coherent: **(6.8.1)** case A (mmd L158-176, the `τ₃` argument, uses (6.7)),
   **(6.8.2)** case B (mmd L178-224).
5. **(6.8.3)** (mmd L226-): if `S ⊋ X ∪ Y` (i.e. `Zc ⊊ H′`), extend `X∪Y`-coherence to all of `S`
   via Theorem (5.6) again (the `S₁`/`S₂` not-coherent contradiction). This is the piece the current
   `Xset ⁅H,H⁆ ∪ Yset = S` shortcut elided entirely.

### Concrete formalization deltas
- Replace, in the capstone X-nonempty branch, the `Z = ⁅H,H⁆` producer route by a `Z = Zc` route.
- `coherenceTarget_of_Xset_empty` / `Xset ⁅H,H⁆ ∪ Yset = S` (3607) are no longer the partition;
  introduce the central `Zc` decomposition + a (6.8.3) extension lemma.
- New prerequisites: `Zc` normal/central/nontrivial facts; (6.8.3) `coherentUnion`→`coherentAllS`
  extension (a new §7-engine application: `S₁` coherent, `S₁∪{ψ,ψ̄}` not ⟹ degree/`(5.6)` bound,
  contradiction). (6.8.1)/(6.8.2) case-A/B `τ₃`/`τ₂` glue (genuine character theory, uses (6.7)).
- The `(6.7)` congruence `ψ(z) ≡ ψ(1) (mod |P|)` (mmd L86-134) is itself **not yet formalized** and
  is a prerequisite of (6.8.1)/(6.8.2). Check whether it exists in S08/S07 before redesign.

## Layered redesign plan (dependency-audited 2026-06-07) — Frobenius / case (A)

Frobenius (c1) ⟹ `W₂ = 1 ⊆ Z(H)` ⟹ Peterfalvi **case (A)**, `Z = Z(H) ∩ H′` (central). The
(A)/(B) split (mmd L150) is orthogonal to c1/c2; the Frobenius producer machinery targets case A.

**L1 — central `Zc` facts** (clean, committable, independent of everything below).
`Zc := ((Subgroup.center ↥H).map H.subtype) ⊓ ⁅H,H⁆ : Subgroup ↥L`. Need:
`Zc ≤ ⁅H,H⁆` (inf_le_right); `Zc ≤ H`; `Zc.Normal` (center char in `H◁L` ⟹ its map ◁L; `⁅H,H⁆◁L`;
inf of normals); `Zc.subgroupOf H ≤ Subgroup.center ↥H` (via `map`/`subgroupOf` of `center ↥H` along
injective `H.subtype`); `Zc ≠ ⊥` when `H` nonabelian (use `isNilpotent_normal_inf_center_ne_bot`
@S08:645 with `N = ⁅H,H⁆ ≠ ⊥`, giving `⁅H,H⁆ ⊓ center ≠ ⊥`).

**L2 — `X = Xset Zc` coherence at central `Zc`.** REUSE the general consumer
`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X (Z := Zc)`
(S08:7360) — it is SOUND for any Z; the producer `hstepData` is now HONESTLY fillable because
`hθsq_le_qtot : θχ² ≤ qtot` = `exists_degree_sq_le_index (Zc.subgroupOf H) (L1 centrality)`. The
building blocks `sum_re_sq_Xset_eq` / `index_mul_card_sub_factor` are already stated for general Z, so
they apply verbatim at `Zc`. **This is still the ~300-line `hstepData` monolith** (member/tail
degree data + the `hsum` partition `∑members² + ∑tail² = total = ∑_{X(Zc)} deg²`), but now
mathematically valid. The hardest sub-piece is `hsum` (degree-sorted partition of `X(Zc)`).
Also needs `X(Zc) ⊆ Irr L` — at central `Zc`, `Ind θ` irreducible for `Zc ⊄ ker θ`: reuse/adapt
`isIrreducibleCharacter_of_mem_Xset_of_frobenius` (currently proven; check it is Z-generic or only
⁅H,H⁆).

**L3 — ν glue → `IsCoherent (Xset Zc ∪ Yset)`.** REUSE `coherentUnion_of_glued` (S07) — exactly what
`coherentS_of_Xset_commutator_Yset_glued` (S08:4212) wraps, EXCEPT do NOT apply the final
`simpa [Xset_union_Yset_eq_S]` (false at `Zc`); stop at the union coherence. The hypotheses
`hagreeX/hagreeY/himg_ortho/hgen` are the genuine **(6.8.1)** case-A `τ₃` content (mmd L160-176):
construct `ν` agreeing with `τ₁` on `Y` and `τ₂` on `X`, mutually orthogonal images. **This uses
(6.7)** (`η₁^{τ₁}` constant on `Z^#` ⟹ congruence ⟹ `b ≡ 0 mod a`). **(6.7) is NOT formalized as a
named theorem** (broad grep 2026-06-07). CANDIDATE: `OddOrder/GroupTheory/RepresentationTheory/
SylowTICongruence.lean` — (6.7) is a Sylow-TI congruence (`P^#` TI, ψ constant on `Z^# ⊆ P` ⟹
`ψ(z) ≡ ψ(1) mod |P|`). **First action of L3 = read SylowTICongruence.lean; if it is (6.7), wire it;
else formalize (6.7) (mmd L86-134, the class-algebra `ω`/`a_{ijs}` argument).**

**L4 — (6.8.3): `IsCoherent (Xset Zc ∪ Yset)` → `CoherenceTarget` (all of `S`).** mmd L226-: if
`S ⊋ X∪Y` (i.e. `Zc ⊊ H′`), suppose `S` not coherent; `exists_coherentBreakPair` (S08:572) gives
`S₁ ⊇ X∪Y` coherent with breaking pair `{ψ,ψ̄}`; `coherentDegreeSumBound_of_not_coherent` (S08:1996)
+ the (5.6) degree bound force a contradiction (`|L:H| ∣ ψ(1)`, the `Z⊄ker` degree argument). Both
tools EXIST. Substantial but unblocked.

### Reuse / rework map
- **Keep (Z-generic, sound):** `Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X`,
  `sum_re_sq_Xset_eq`, `index_mul_card_sub_factor`, `exists_degree_sq_le_index`, `coherentYset`,
  `coherentUnion_of_glued`, `exists_coherentBreakPair`, `coherentDegreeSumBound_of_not_coherent`,
  `exists_pairUnion_memberFamily_of_irreducible_X`, all the per-member degree blocks.
- **Rework / replace (hardwired to ⁅H,H⁆):** the capstone `sibleySetup_is_coherent` X-nonempty branch;
  `coherentS_of_Xset_commutator_Yset_glued` (drop final `simpa`); `coherentS_of_frobenius_…` capstone;
  `coherenceTarget_of_Xset_empty` / `Xset_union_Yset_eq_S` (no longer the partition).
- **New:** L1 Zc facts; L2 producer at Zc; L3 (6.8.1) ν construction (+ (6.7) wiring/formalization);
  L4 (6.8.3) extension.

### Order of attack
L1 → (read SylowTICongruence for 6.7) → L4 (unblocked, exercises the (5.6) tools) → L2 (monolith) →
L3 (hardest, needs 6.7). L1 and L4 are the cleanest committable starts; L3 is the gating risk.

### Progress
- **✅ L1 DONE (2026-06-07, commits `b501838` + `b70b430`, leaf-green, axiom-clean).** In namespace
  `SibleyDadeHypothesis`: `centralCommutator := (center ↥H).map H.subtype ⊓ ⁅H,H⁆`;
  `centralCommutator_le_commutator` / `centralCommutator_le` (≤ ⁅H,H⁆, ≤ H);
  `centralCommutator_subgroupOf_le_center` (**centrality** — the (6.6) bound enabler);
  `centralCommutator_normal` (instance, via `normal_of_characteristic_of_normal`);
  `centralCommutator_subgroupOf_eq` (`= center ↥H ⊓ commutator ↥H`);
  `centralCommutator_ne_bot` (H non-abelian ⟹ ≠ ⊥). Not yet registered in `AxiomsCheck.lean`
  (deferred until consumed; verified axiom-clean via temp `#print axioms`).
- **🔜 L4 IN PROGRESS (order chosen: L4 → L2 → L3).** Decomposition of the (6.8.3) case-(A) extension
  `IsCoherent (Xset Zc ∪ Yset) → ¬Nonempty CoherenceTarget → False`:
  - **✅ (a) arithmetic core** `false_of_centralCommutator_break_arith` (commit `0af1041`, axiom-clean):
    `w1,d,hZ,cZ`, `d²≤hZ`, `2w1≤cZ−1`, `w1·hZ·(cZ−1) < 2w1²d` ⟹ False.
  - (b) **break-pair**: `exists_coherentBreakPair` (S08:572) on `Sa = Xset Zc ∪ Yset`, `Sb = S` ⟹
    `S₁` (conj-closed, X∪Y ⊆ S₁ ⊆ S) coherent + `ψ` with `S₁∪{ψ,ψ̄}` not coherent. Needs `S` real-free
    (`S_hasNoRealCharacters`), `Xset Zc ∪ Yset ⊆ S`, and `Xset Zc ∪ Yset` coherent (= L3 output).
  - (c) **xSum bound** `∑_{χ∈X} χ(1)² < 2ψ(1)·|W₁|`: analogue of `sMember_index_le_two_psi` (S08:5485)
    but bounding the X-sum (`sum_re_sq_Xset_eq`, applies at central Zc) instead of `S(A)`; reuse
    `sMember_degreeSqReBound_of_not_coherent` over `S₁ ⊇ X`, anchor `χ₁ = η₁ ∈ Y` of degree `|W₁|`.
  - (d) **Cor 2.30** `d² ≤ |H:Z|`: `exists_degree_sq_le_index (Zc.subgroupOf H) centralCommutator_subgroupOf_le_center` (L1). Easy.
  - (e) **FPF bound** `|Z|−1 ≥ 2|W₁|`: W₁ acts FPF on the W₁-invariant `Z ≤ H` (Z char in H);
    `card_modEq_one` (`FrobeniusActionTI:146`) + `Z,W₁` odd + `two_mul_add_one_le_of_odd_dvd` (S08:2383)
    — mirrors `isPGroup_of_isFrobeniusGroup_of_card_le` (S08:2534) done for all of H. Sub-task: derive
    `IsFrobeniusAction W₁ Z` from `IsFrobeniusGroup L H W₁` + Z W₁-invariant.
  - (f) assemble (b)–(e)+(a). `∑_X = |W₁|·|H:Z|·(|Z|−1)` via `sum_re_sq_Xset_eq` + `index_mul_card_sub_factor`.
- **Then L2, L3.** Before L2, confirm `isIrreducibleCharacter_of_mem_Xset_of_frobenius`
  (S08:4348) is `Z`-generic (works at `centralCommutator`) or generalize it. Before L3, read
  `OddOrder/GroupTheory/RepresentationTheory/SylowTICongruence.lean` for (6.7).

## Recommendation

This is a multi-session redesign of the §8 capstone assembly (and possibly (6.7)), not an
autonomous "fill the sorry" loop. The earlier `autonomous_assembly_queue.md` recipe (build the
`Z=⁅H,H⁆` producer) is **invalid** and should not be executed. Pause the (6.8) capstone; the next
real work is the central-`Zc` redesign above, best done attended.
