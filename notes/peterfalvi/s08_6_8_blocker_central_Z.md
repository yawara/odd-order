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
- The `(6.7)` congruence `ψ(z) ≡ ψ(1) (mod |P|)` (mmd L86-134) **IS formalized** (2026-06-07 finding)
  as `peterfalvi_67_of_odd` (`SylowTICongruence.lean:140`); it is a prerequisite of (6.8.1)/(6.8.2)
  and is available for wiring.

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
(6.7)** (`η₁^{τ₁}` constant on `Z^#` ⟹ congruence ⟹ `b ≡ 0 mod a`). **CORRECTION (2026-06-07): (6.7)
IS already formalized** as `peterfalvi_67_of_odd`
(`OddOrder/GroupTheory/RepresentationTheory/SylowTICongruence.lean:140`) — the earlier "NOT
formalized" claim was a grep miss (searched the string `6.7`, not the identifier). Its statement:
for `P` Sylow-`p`, `L = N_G(P)` odd, `P^#` TI, `Z ⊴ L`, `1 ≠ Z ≤ Z(P)`, `|C_L(·)|` const on `Z^#`,
and `ψ = χ_ρ ∈ Irr G` const on `Z^#`, then `ψ(z) ≡ ψ(1) [ALGMOD |P|]`. So **L3's gating prerequisite
exists**; L3 reduces to the (6.8.1) `τ₃` ν-construction *wiring* `peterfalvi_67_of_odd`, not a
from-scratch formalization of the class-algebra `ω`/`a_{ijs}` argument (that is already done inside
`ClassSumAlgebra.lean` / `SylowTICongruence.lean`).

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
L1 → L4 (unblocked, exercises the (5.6) tools) → L2 (monolith) → L3 (wires the already-formalized
(6.7) `peterfalvi_67_of_odd` into the (6.8.1) `τ₃` ν-construction). L1 and L4 are the cleanest
committable starts. **With (6.7) confirmed present, L3's residual risk is the `τ₃` ν-construction
itself, not a missing congruence theorem; L2 (the never-before-built StepData monolith) is now the
larger remaining lift.**

### Progress
- **✅ L1 DONE (2026-06-07, commits `b501838` + `b70b430`, leaf-green, axiom-clean).** In namespace
  `SibleyDadeHypothesis`: `centralCommutator := (center ↥H).map H.subtype ⊓ ⁅H,H⁆`;
  `centralCommutator_le_commutator` / `centralCommutator_le` (≤ ⁅H,H⁆, ≤ H);
  `centralCommutator_subgroupOf_le_center` (**centrality** — the (6.6) bound enabler);
  `centralCommutator_normal` (instance, via `normal_of_characteristic_of_normal`);
  `centralCommutator_subgroupOf_eq` (`= center ↥H ⊓ commutator ↥H`);
  `centralCommutator_ne_bot` (H non-abelian ⟹ ≠ ⊥). Not yet registered in `AxiomsCheck.lean`
  (deferred until consumed; verified axiom-clean via temp `#print axioms`).
- **✅ L4 COMPLETE (order L4 → L2 → L3).** The (6.8.3) case-(A) extension
  `false_of_coherentXunionYset_of_not_coherentS` (commit `c49ab3f`, axiom-clean): given
  `Nonempty (IsCoherent (Xset Zc ∪ Yset))` and `¬ Nonempty (IsCoherent S)`, derives `False`.
  Sub-pieces (all committed, leaf-green, axiom-clean):
  - **✅ (a) arithmetic core** `false_of_centralCommutator_break_arith` (commit `0af1041`; relaxed to
    non-strict `≤` + `2 ≤ hZ` in `c9ba639`): `d²≤hZ`, `2≤hZ`, `2w1≤cZ−1`, `w1·hZ·(cZ−1) ≤ 2w1²d` ⟹ False.
  - **✅ (e) FPF bound** `centralCommutator_card_subgroupOf_lower` (commit `395ceb2`): `2|W₁|+1 ≤ |Z|`.
  - **✅ (c) X-sum bound** `xSum_le_two_psi` (commit `c9ba639`): `∑_X χ(1)² ≤ 2ψ(1)χ₁(1)`.
  - **✅ (d)** inline in (f): Cor 2.30 `d²≤|H:Z|` via `exists_degree_sq_le_index` + L1 centrality.
  - **✅ (b)+(f)** the assembly (commit `c49ab3f`): break-pair + (c)+(d)+(e)+(a), with the
    `isIrreducibleCharacter_of_mem_S_of_frobenius` / `Yset_nonempty` / `induce_apply_one_eq_card_W1_of_degree_one`
    helpers (all pre-existing) and ℝ→ℕ casting via `index_mul_card_sub_factor`.
- **🔜 NEXT: L2 (the producer monolith), then L3, then capstone wiring.**
  - **L2**: `X = Xset Zc` coherence at central `Zc`. REUSE the general consumer
    `Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X (Z := Zc)`
    (S08:~7460). **✅ linchpin landed** (`exists_source_primePow_centralBound_of_mem_Xset`, commit
    `a119d9c`): for `χ∈X(Z)`, `χ(1)=|L:H|·p^k ∧ (p^k)²≤|H:Z|` — the `hθχ`/`hθsq_le_qtot` data, now
    fillable at central `Zc`. `isIrreducibleCharacter_of_mem_Xset_of_frobenius` confirmed Z-generic.
    **✅ hXne landed (2026-06-07, commit `264966a`)**: `Xset_centralCommutator_nonempty` (via Z-generic
    `Xset_nonempty_of_subgroupOf_ne_bot`, degree-sum positivity — no Clifford theory). **✅ outer shell
    landed (commit `a9054c4`)**: `Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
    — the Zc instantiation of the consumer, all prereqs discharged, `hstepData` confirmed to TYPECHECK
    at `Z := Zc` (so the producer goal is well-formed and satisfiable).
    **Sole remaining L2 hole = constructing the producer `hstepData` monolith** (single atomic
    `noncomputable def`, ~250 lines,
    not splittable — the StepData is consumed atomically). For each chain step `i`:
    1. enum: `exists_pairUnion_memberFamily_of_irreducible_X` → `k`, `χmem`, `hχinj`, `hrange`; anchor
       `i₁` = min-degree of `xBaseBlock Zc` (`Set.exists_min_image`, cf. `two_le_xBaseBlock_ncard`).
    2. numerics: `p`/`hp`(`three_le_prime_of_isPGroup_of_odd`)/`idx=H.index`(`hidx_p`=`coprimeIndexPrimePow`)/
       per-member `dmem,θmem,mmem` (`exists_memberDegreeData`); `χs i` degree via the linchpin
       (`θχ=p^mχ`, `θχ²≤|H:Z|=qtot`); `qtot=|H:Z|=p^mq` (`exists_primePow_card_quotient_of_isPGroup`);
       `c`/`total`/`htotal` via `index_mul_card_sub_factor`.
    3. **`hsum` (crux, ~80 lines)**: `tailSet := X(Zc)-Finset ∖ (accumulator image)`,
       `θtail j` = source p-degree of `j`; `∑_{Fin k} dmem² + ∑_{tailSet}(idx·θtail)² = ∑_{X(Zc)} = total`
       via `Finset.sum_sdiff` (accumulator ⊆ X) + `sum_re_sq_Xset_eq` (ℕ-cast); `htail_le` from the
       degree-sorted chain (`hmono`): tail degrees ≥ `dχ`.
    4. package `PairUnionBaseAnchorCommonIndexPrimePowerStepData ⟨…⟩`; feed the consumer.
    Also needs `H` a `p`-group (from `isPGroup_of_not_coherent`, capstone ¬-coherent branch) and
    `(Xset Zc).Nonempty`.
  - **L3**: ν glue → `Nonempty (IsCoherent (Xset Zc ∪ Yset))` via `coherentUnion_of_glued`; needs
    (6.8.1) case-A `τ₃`, which wires the **already-formalized** (6.7) `peterfalvi_67_of_odd`
    (`SylowTICongruence.lean:140`). The `τ₃` ν-construction is the residual content (no missing
    prerequisite theorem).
  - **capstone** `sibleySetup_is_coherent` (S08 X-nonempty sorry): `by_cases Nonempty CoherenceTarget`;
    `¬` branch → `isPGroup_of_not_coherent` (H p-group) → L2 → L3 → `false_of_coherentXunionYset_of_not_coherentS` (L4).

## 2026-06-07 deep-dive findings (reconnaissance, no Lean delta yet)

Re-verified the whole frontier against the live branch (`peterfalvi` @ `144c9c9`, baseline build
green, 1 sorry @ capstone S08:7919). New facts beyond the progress log above:

1. **(6.7) `peterfalvi_67_of_odd` is already formalized** (`SylowTICongruence.lean:140`,
   complete + clean). The note's L3 gating-risk analysis was wrong; corrected throughout above.
   L3 ⇒ "wire (6.7) into the (6.8.1) `τ₃` ν-construction", no missing prerequisite theorem.
2. **The `Z=⁅H,H⁆` blocker is independently re-confirmed.** Cor 2.30 needs centrality; `UT(4,p)`
   (class 3) is the counterexample; the redesign is genuinely necessary, not a detour.
3. **No `…StepData` value has ever been constructed anywhere** (grep: every occurrence is the
   `hstepData` *hypothesis*, incl. S09:1668). L2 builds the **first-ever** such term — the
   per-step machinery has never been exercised with concrete data. This is the larger remaining lift.
4. **`hXne` (`(Xset Zc).Nonempty`) is NOT a quick win.** `Xset Zc ⊆ Xset ⁅H,H⁆` (antitone,
   `Xset_mono`), so the X-nonempty branch hypothesis does NOT give it. It needs the
   separation argument: `Zc ≠ ⊥` (`centralCommutator_ne_bot`, needs `commutator ↥H ≠ ⊥`) ⟹
   ∃ `θ≠1`, `Zc ⊄ ker θ`, AND `Ind θ ∉ S(Zc)` — the latter needs `Zc` W₁-invariant (char in H) +
   `Ind` injective-up-to-W₁-conjugacy. Genuine character theory; budget a sub-lemma.
5. **The capstone needs BOTH branches of `hyp.cases`** (`IsFrobeniusGroup ∨ ∃ cert,
   CertainTypeHypothesis`). L1–L4 + L2/L3 close only the **Frobenius / case (A)** branch. The
   **CertainType / case (B)** branch (`Z = W₂`, (6.8.2) `τ₂` glue, mmd L178-224) is **unplanned**.
   Capstone skeleton: `by_cases hcoh : Nonempty CoherenceTarget` (`= IsCoherent … S …`); coherent →
   `hcoh.some`; ¬coherent → `exfalso`; `rcases hyp.cases`; Frobenius → L2+L3+L4
   (`false_of_coherentXunionYset_of_not_coherentS`, with `hHnonab` from X-nonempty); CertainType →
   case-(B) analogue (needs its own central-Z facts + (6.8.2) + a case-(B) L4).
6. **🛑 SECOND BLOCKER — the StepData producer contract is undischargeable as-is (the real reason
   #3's StepData was never built).** The per-step fields `htail_le`/`hsum`/`htotal` flow into
   `S07.sq_dvd_head_of_commonIndex_primePower_sums` (called @ S08:7402) to prove `dχ² ∣ D`
   (`D = ∑members²`). To supply them honestly the producer must take `tailSet = Xset Z ∖ members`
   with `total =` the full X degree-square sum `= |H:Z|·(|L:H|·(|Z|−1)) = qtot·c` (`qtot = |H:Z|`),
   and `htail_le` = "every non-member has degree ≥ dχ". **Both require Xset-cover completeness**
   (`∀ φ ∈ Xset Z, φ ∈ xBaseBlock Z ∨ ∃ j<N, φ ∈ pairSet pair j`). The chain engine
   `Xset_isCoherent_from_adjoinSteps_of_irreducible_X` (S08:6651) HAS this (`hcover` @ 6693, from
   `exists_conjugatePairCover`) but passes **only the 5 hypotheses** (hpair0/1, hpairs, hdisj, hmono)
   to its `hstep` callback (6703) — completeness is NOT exposed to the StepData producer. Verified no
   cooked-`tailSet` escape: setting `qtot = θχ²` (or padding with `dχ²` copies) makes `htotal` reduce
   to `θχ² ∣ D`, the very conclusion — circular. An incomplete-but-5-hyp-valid `pair` (covering half
   of `Xset Z`, sorted/disjoint) is a genuine counterexample to the producer goal.
   **Fix = thread `hcover` through the callback contract**: add it to `adjoinSteps`' `hstep` type +
   pass it (6703); thread into the base-anchor consumer's `hstepData`
   (`…BaseAnchorCommonIndexPrimePowerData_of_irreducible_X` @ S08:7697) and its callers (the ⁅H,H⁆
   wrapper @ 7850, the Zc shell `a9054c4`, the capstone glue `coherentS_of_frobenius_…BaseAnchor…`
   @ ~7951/7966, and **S09:1648** `indChainDecomposition_of_sibley_…`). The common-index consumer
   (@ 7660) + its wrapper can accept-and-ignore the new `hcover` (their path isn't being built).
   ~7 defs across S08+S09, mechanical (everyone threads one extra hypothesis; only the eventual
   monolith *uses* it). **Alternative**: a new completeness-aware consumer that re-runs
   `exists_conjugatePairCover` internally and absorbs the monolith, leaving existing signatures
   untouched (no S09 churn, but ~50 lines of engine duplication). Do the threading fix **before** the
   monolith; it is the true L2 unblock.

### L2 field map (for the eventual monolith — `xAdjoinStepInput_of_pairUnion_baseAnchor_…` @ S08:7464)
**⚠️ Requires the finding-#6 completeness fix first** (`htail_le`/`hsum` below are unprovable until
`hcover` is threaded to the producer).
- enum (`κ,tailSet,k,χmem,hχinj,hrange,i₁`): `exists_pairUnion_memberFamily_of_irreducible_X`
  (S08:6353, gives `k/χmem/hχinj/hrange`) + base-block min-degree anchor `i₁`.
- numerics: `p`(`3≤p`),`idx=H.index`(`hidx_p` coprime),`qtot=|H:Z|=p^mq`,`c=|L:H|·(|Z|−1)`,
  `total=|H:Z|·c`(`index_mul_card_sub_factor` @5560); `dχ/θχ/mχ`,`d₁/θ₁/m₁`,`dmem/θmem/mmem` via
  `exists_source_primePow_centralBound_of_mem_Xset` (5627, gives `hθsq_le_qtot`) /
  `exists_memberDegreeData` (5611).
- **crux `hsum`/`htail_le`/`htotal`** (needs finding-#6 `hcover`): `tailSet := Xfin ∖ members`,
  `θtail` = source p-degree (choose via linchpin over `Xfin`); `∑members² + ∑tail² = total` is
  `Finset.sum_sdiff` + per-char deg identification, ℝ-value pinned by `sum_re_sq_Xset_eq` (5511)
  cast to ℕ, with `htotal` from `index_mul_card_sub_factor`. `htail_le` (non-members have degree
  ≥ `dχ`) is the part that genuinely consumes `hcover` + `hmono`. ~80 lines of casts/plumbing
  **on top of** the threading fix.

## Recommendation

Multi-session redesign of the §8 capstone assembly (Frobenius L2/L3 **and** the unplanned
CertainType case (B)), not an autonomous "fill the sorry" loop. The earlier
`autonomous_assembly_queue.md` recipe (build the `Z=⁅H,H⁆` producer) is **invalid**. With (6.7)
confirmed present, no prerequisite *theorem* is missing — it is all assembly.

**Precise next-step ordering for L2** (2026-06-07): ✅ `hXne` (`264966a`) + ✅ Zc shell (`a9054c4`).
**✅ (1) finding-#6 contract fix DONE (`2e46520`, additive)**: three `…withCover…` defs expose
`hcover` to the StepData producer (engine `Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X`,
consumer `…BaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X`, Zc shell
`Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_frobenius`).
No existing signatures touched → S09 untouched, full build green. **✅ (2) the L2 producer monolith
DONE (`d21d788`, sorry-free + axiom-clean)**: `Xset_centralCommutator_isCoherent_of_frobenius` builds
the first-ever `…StepData` term for every chain step and feeds the `…withCover…` Zc shell →
`IsCoherent (Xset Zc)`. Sub-lemmas: anchor (`1f2148a`), htail_le core (`c8ddb62`), hsum-partition
(`natSum_partition_of_realSum`, `ab01c92`). The `StepData.κ : Type` (Type 0) constraint was met by
indexing the tail `XF∖members` via `Fin tailF.card` (`Finset.equivFin` + `Equiv.sum_comp` +
`Finset.sum_coe_sort`); ∃→data witnesses via the `choose` tactic (Type-valued goal).
**⟹ L2 (the X(Zc)-coherence) is complete.** Remaining for the (6.8) capstone: **L3** (ν-glue, wires
`peterfalvi_67_of_odd`), **CertainType case (B)**, **capstone wiring**.
