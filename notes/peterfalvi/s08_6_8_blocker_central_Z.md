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

## Recommendation

This is a multi-session redesign of the §8 capstone assembly (and possibly (6.7)), not an
autonomous "fill the sorry" loop. The earlier `autonomous_assembly_queue.md` recipe (build the
`Z=⁅H,H⁆` producer) is **invalid** and should not be executed. Pause the (6.8) capstone; the next
real work is the central-`Zc` redesign above, best done attended.
