> ⚠️ **2026-06-17 STALE — central-Zc 経路は放棄済**: 本ファイルが記述する central-Zc (T=0 = `D.X=cTEμ`) 経路は session 48 で**厳密反駁・放棄**され、教科書 (6.8.2) τ₂ 経路に置換済（関連 handoff は削除済）。
> (6.8.3)/case-B の現状は [`s08_6_8_3_gap_resolution.md`](s08_6_8_3_gap_resolution.md) が正本（数学 gap=0、engine `S08_CoherenceWeighted` 既存、残務=case-B glue）。**Lane B はこの central-Zc 経路に戻らないこと**。本ファイルは history。

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
**⟹ L2 (the X(Zc)-coherence) is complete.**
**✅ (3a) L3 outer shell DONE (`13836f7`)**: `coherentXunionYset_centralCommutator_of_glued_of_frobenius`
— given the (6.8.1) `τ₃` glue data (`ν`, `hagreeX`/`hagreeY`/`hmixed`/`hgen`), produces
`IsCoherent (Xset Zc ∪ Yset)` (what L4 consumes), via `coherentUnion_of_glued` at `Zc`,
source-orthogonality discharged. **🔴 (3b) the genuine L3 content = CONSTRUCT `ν` (the (6.8.1) `τ₃`
argument)** — DEEP character theory, never before built (like the StepData, `ν` was always a
hypothesis). The mmd (6.8.1) proof (04.8 L160-176): set `τ₁`= Y-isometry (`coherentYset.extension`),
`τ₂`= X-isometry (L2 `.extension`); write `(χ₁−aη₁)^τ = X − a η₁^{τ₁} + b∑η_j^{τ₁}`; show
`η₁^{τ₁}` constant on `Z^#` (via the `Res η₁^{τ₁} = c∑d_iχ_i + χ′` decomposition =
`(c/a)(ρ_L − ρ_{L/Z})`), then **(6.7) `peterfalvi_67_of_odd`** ⟹ `−c|H|/a ≡ 0 mod |H|` ⟹ `b ≡ c ≡ 0
mod a`; norm bound `(x−1)²+(m−1)x² ≤ 1+1/a²` with `a>1` ⟹ `b=0`; then `X = χ₁^{τ₁}`, so `τ₃` (=`τ₁`
on Y, `τ₂` on X) is an isometry. Formalizing this faithfully is a multi-session piece (several
sub-lemmas: the regular-character decomposition, the (6.7) wiring to the SibleyDade TI/Sylow/odd
setup, the norm/inner computations). After `ν`: **CertainType case (B)** (mmd (6.8.2), `Z=W₂`, the
`τ₂`/`(6.8.2.1-3)` argument — separate, also deep), then **capstone wiring** (`by_cases Nonempty
CoherenceTarget`; `¬` → `rcases hyp.cases`; Frobenius → L2+L3+L4; CertainType → case-(B) analogue).

### L3 ν-construction analysis (2026-06-07, post-L3-shell)
`IntegralCharacterMap (↥L) G = ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ` (S07:301). `IsCoherent`
(S07:1557) carries `extension : IntegralCharacterMap` isometric **only on its lattice** `ℤ[S]`.
τ₁ := `coherentYset.extension`, τ₂ := `(Xset_centralCommutator_isCoherent_of_frobenius …).extension`.
**Key reduction:** the L3 shell wants `ν` with `hagreeX`(=τ₂ on X), `hagreeY`(=τ₁ on Y), `hmixed`
(`⟨νx,νy⟩=⟨x,y⟩` on X×Y). Take `ν` agreeing with τ₂ on X-irr and τ₁ on Y-irr (then hagreeX/hagreeY
hold by ℤ-linearity on `ℤ[X]`/`ℤ[Y]`); since `⟨x,y⟩=0` (source-ortho, X⊥Y disjoint irreducibles),
**`hmixed ⟺ himg_ortho : ⟨τ₂ x, τ₁ y⟩ = 0` = the image orthogonality `X^τ₂ ⊥ Y^τ₁`** — which IS the
deep (6.8.1) content (the `b≡c≡0 mod a` computation via (6.7)). So L3 = (a) *construct* `ν` (an
IntegralCharacterMap agreeing with τ₂/τ₁ — extensions are built via `retarget` @S07:2680, NOT
`Basis.constr`; a glue/combination constructor likely must be added) + (b) prove `himg_ortho` (the
(6.8.1) `b≡0` argument: `Res η₁^{τ₁} = c∑dᵢχᵢ+χ′ = (c/a)(ρ_L−ρ_{L/Z})` ⟹ `η₁^{τ₁}` const on `Z^#` ⟹
(6.7) ⟹ `c≡0 mod a`; norm bound ⟹ done). Both (a),(b) are genuinely deep / multi-session; (b) is the
gating character theory. The (6.7) wiring needs the SibleyDade TI/Sylow/odd setup matched to
`peterfalvi_67_of_odd`'s hypotheses (`P`, `L=N_G(P)`, `Z≤Z(P)`, `|C_L(·)|` const on `Z^#`).

## 2026-06-07 (session 2): regular-char ingredient landed + (6.7)-wiring feasibility resolved

**✅ (1) Regular-character decomposition off-identity value — DONE, committed `abbe578`.**
`sumNonInflatedDegreeMulChar_of_mem` (`InflationCharacter.lean`, sorry-free + axiom-clean): for
finite `G`, `N ⊴ G`, `z ∈ N^#`,
`∑_{χ ∈ Irr G, N ⊄ ker χ} χ(1)·χ(z) = -|G ⧸ N|`. The off-identity companion of the pre-existing
`sumNonInflatedDegreeSq` (z=1 value `|G|−|G⧸N|`); together they give `ρ_G − ρ_{G⧸N}` constant on
`N^#` (value `-|G⧸N|`) with `ψ_N(z)−ψ_N(1) = -|G|`. Proof = `column_orthogonality_not_conjugate`
(`∑_{Irr G} χ(1)χ(z)=0` at `z≁1`) minus the `N⊆ker` part (`χ(z)=χ(1)` on the kernel,
`sumInflatedDegreeSq`). This is the mmd 04.8 L168 `∑ dᵢχᵢ(z) = -|L:Z|/(a|W₁|)` ingredient of
"`η₁^{τ₁}` constant on `Z^#`". **NOT yet consumed** (the `Res η₁^{τ₁} = c∑dᵢχᵢ+χ′` decomposition that
feeds it is still to be built — task #3); committed as a standalone reusable rep-theory lemma.

**🟢 (2) The (6.7) wiring is FEASIBLE — the "structural risk" (is `H` Sylow-`p` of `G`?) is resolved.**
(6.7) `peterfalvi_67_of_odd` requires `P : Sylow p G` with `L = N_G(P)`; the (6.8.1) application
uses modulus `|H|`, so it needs **`H` = Sylow-`p` of `G`, `L = N_G(H)`**. Peterfalvi (6.8)(a)
(mmd L138) does **not** state this (only `H^#` TI with normalizer `L`, `H` nilpotent) — and it is
**not** implied by TI alone (counterexample `H=C_p ◁ G=C_p×C_p`, non-Frobenius). **But in the
Frobenius case (A) it IS provable**, hence no missing hypothesis field:
- `H ◁ L` (kernel, `H_normal`), `H` a `p`-group (post-(6.5), `hHp`), and Frobenius ⟹
  `gcd(|H|,|W₁|)=1` (`OddOrder.Isaacs.Ch06.coprime_card_kernel_complement hF`, FrobeniusGroup.lean:287)
  ⟹ `H` is the **unique normal** Sylow-`p` of `↥L` (`Sylow.unique_of_normal`) ⟹ every `p`-element
  of `↥L` lies in `H`.
- `Ĥ := H.map L.subtype : Subgroup G` (`sharpImage H = (Ĥ : Set G) \ {1}`, S08:1004),
  `N_G(Ĥ) = L` from `H_sharp_ti` (TI normalizer). If `Ĥ ⊊ P ∈ Syl_p(G)`: normalizer-growth gives
  `x ∈ N_P(Ĥ)∖Ĥ`; `x` normalizes `Ĥ` ⟹ `x ∈ N_G(Ĥ) = L`; `x` a `p`-element of `L` ⟹ `x ∈ Ĥ`,
  contradiction. ∴ `Ĥ ∈ Syl_p(G)`. (Even if one only had `H ⊆ P`, `mod |P| ⟹ mod |H|` since
  `|H| ∣ |P|` makes `-c|H|/(a|P|) ∈ ℤ ⟹ a ∣ c` anyway — but the `L=N_G(P)` hypothesis still forces
  `Ĥ=P`, so the Sylow lemma is the honest route.)

**(6.7)-wiring plan (task #2), de-risked, ~focused-session build:**
1. ✅ `Ĥ := H.map L.subtype : Subgroup G`; `IsPGroup p Ĥ` (`hHp.map L.subtype`).
2. **✅ DONE (commit `941e85e`, sorry-free + axiom-clean): `Ĥ ∈ Syl_p(G)`.** Realized as
   `SibleyDadeHypothesis.sylow_map_subtype_of_frobenius` (S08) + the reusable general lemma
   `OddOrder.GroupTheory.sylow_coe_eq_of_normalizer_inf_le` (SubgroupInAmbient.lean). The
   normalizer-growth was packaged via `NormalizerCondition` (`Q` nilpotent) + `subgroupOf_normalizer_eq`
   (self-normalizing ⟹ ⊤), avoiding the explicit `N_P(H)` argument. The "p-element of L in H" went
   through `Q.comap L.subtype ≤ H` (`comap_of_injective` + unique normal Sylow), and `N_G(Ĥ) ≤ L`
   from `H_sharp_ti`. **The handoff's structural risk is now not just resolved on paper but formalized.**
3. **✅ DONE (commit `2a10d44`): `normalizer_map_subtype_eq : normalizer (H.map L.subtype) = L`.**
   `≤` from `H_sharp_ti` (TI), `≥` from `H ◁ ↥L` (`H.normalizer = ⊤` mapped to `range L.subtype = L`,
   `le_normalizer_map`). Refactored step 2's `hNle` to reuse `.le`.
4. **✅ DONE (commits `023fbfb` + `abf9c05`): the centralizer constancy.**
   `centralizer_centralCommutator_eq : Subgroup.centralizer {z} = H` for `z ∈ Zc^#` (in `↥L`):
   `H ≤ C_L(z)` (`z ∈ Z(H)`, `centralCommutator_subgroupOf_le_center`) + `C_L(z) ≤ H`
   (`z ∈ H^#`, Frobenius `centralizer_kernel_le`). Its ambient-`G` form
   `inf_centralizer_centralCommutator_map : (L:Subgroup G) ⊓ C_G(↑z) = H.map L.subtype` gives the
   `|N_G(Ĥ) ⊓ C_G(·)| = |Ĥ|` constancy on `Zc^#`.
5. **✅ DONE (commit `9498451`): the adapter `peterfalvi_67_centralCommutator`.** For `ρ` irreducible
   with character const on `Zc^#`: `ρ.character z ≡ ρ.character 1 [ALGMOD |H|]` for `z ∈ Zc^#`.
   Discharges all of `peterfalvi_67_of_odd`'s hyps at `P:=Ĥ`, `Z:=Zc.map L.subtype` (hZP, hZnormal
   via `comap_map_eq_self`, hti/hodd via step 3, hPz + hconst-centralizer via step 4); modulus
   `|Ĥ|=|H|` via `card_map_of_injective`. S08 imports `SylowTICongruence`, opens `OddOrder.AlgInt`.

**⟹ (6.7) WIRING COMPLETE (task #2 closed).** All five steps sorry-free + axiom-clean, full build
green. The handoff's flagged structural risk is fully resolved and formalized. The adapter
`peterfalvi_67_centralCommutator` is ready for L3 (3b) to consume (`ρ` = the irreducible underlying
`η₁^{τ₁}`; the "character const on `Zc^#`" hypothesis is exactly what the `Res η₁^{τ₁}` decomposition
of task #3 supplies).

**🔴 REMAINING for the (6.8) capstone:**
- **✅ L3 (3a) construct `ν` — DONE (commits `9977399` + `1b72d39` + `015441a`, axiom-clean).**
  `IntegralCharacterMap.coherentImageMapGlue` (S07) = `coherentImageMap χX (τ₂∘χX) + coherentImageMap χY (τ₁∘χY)`
  (`coherentImageMapGlue_apply_left/right`); set form `exists_integralCharacterMap_glue_of_orthonormal`
  (enumerates X/Y via `Finset.equivFin`, set-orthonormality as hyps); S08 `ν`-free shell
  `coherentXunionYset_centralCommutator_of_himg_ortho` (derives orthonormality from
  `irreducibleCharacter_inner` + disjointness, `ν` via `Classical.choose`). **⟹ the (6.8.1)
  `X(Zc)∪Y`-coherence now has a SINGLE remaining obligation: `himg_ortho`.**
- **🔴 L3 (3b) prove `himg_ortho` — the deep `b≡c≡0 mod a` argument** (`Res η₁^{τ₁}` decomposition ⟹
  const on `Zc^#` ⟹ **adapter `peterfalvi_67_centralCommutator`** ⟹ `a∣c`, then norm bound ⟹ `b=0`).
  `himg_ortho : ∀ x ∈ X(Zc), ∀ y ∈ Y, ⟨τ₂ x, τ₁ y⟩ = 0` (`τ₂ = Xset_centralCommutator_isCoherent_of_frobenius.extension`,
  `τ₁ = coherentYset.extension`). **The gating character theory, attended.** Tasks #3/#4.
- capstone Frobenius-branch wiring (mechanical: `by_cases Nonempty CoherenceTarget`; `¬` →
  `isPGroup_of_not_coherent` → `coherentXunionYset_centralCommutator_of_himg_ortho` (needs 3b) wrapped
  `Nonempty` → L4 `false_of_coherentXunionYset_of_not_coherentS`); CertainType case (B) (unplanned).

**The entire autonomous-friendly runway is done** (6.7 wiring + L3 (3a) ν-construction). The sole
gating remainder is `himg_ortho` (3b), the subtle §13-style character theory — best attended. Every
prerequisite it needs is now in place: the reg-char decomposition (`abbe578`) and the (6.7) adapter
(`9498451`).

Order note: the adapter (step 5) and task #3 (`Res η₁^{τ₁}` decomposition ⟹ const on `Zc^#`) are both
prerequisites of #4 (`b≡0`). #3 is the genuinely deep character theory (entangled with
`coherentYset.extension` internals).

## 2026-06-07 (session 3): Peterfalvi (4.1) landed + two framing corrections (read carefully)

**✅ Peterfalvi (4.1) (mmd 04.6 L5) LANDED — general form, build-green + axiom-clean + AxiomsCheck-registered.**
In `S08_CoherenceTheorems.lean`, namespace `OddOrder.RepresentationTheory` (general `{Γ}`, reusable;
inserted just after the early `ClassFunction` section):
- `apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one` — a `±Irr` element has nonzero degree.
- `eq_inner_smul_of_inner_ne_zero` — two `±Irr` with `⟨φ,ψ⟩ ≠ 0` satisfy `ψ = ⟨φ,ψ⟩ • φ`.
- `inner_eq_zero_of_orthogonal_signedDifference` — (4.1) cross core: `(α,γ) = 0`.
- `pairwise_inner_eq_zero_of_orthogonal_signedDifference` — full (4.1): all four cross products
  `(α,γ),(α,δ),(β,γ),(β,δ)` vanish (core + 3 sign-flipped/swapped applications).

"±Irr Γ" = norm-`1` element of `ZIrr Γ` (`exists_zsmul_irreducibleCharacter_of_inner_self_one`).
All four `#print axioms` = `[propext, Classical.choice, Quot.sound]`. Issue `1002`.

### 🔶 Framing correction #1: `himg_ortho` IS the (4.1) step, NOT the deep `b≡0` argument.
The mmd (6.8.1) proof (04.8 **L166**) establishes `X^{τ₂} ⊥ Y^{τ₁}` (= the formalization's
`himg_ortho`, `⟨τ₂ χᵢ, τ₁ ηⱼ⟩ = 0`) **"by (4.1)"**, *before* and independent of the `b≡c≡0 mod a`
argument (L168-176). So `himg_ortho` reduces to **(4.1) + difference-orthogonality + degree setup +
`n ≥ 2`, `m ≥ 2`**, not the `(6.7)`/regular-character machinery. Concretely, apply
`pairwise_inner_eq_zero_of_orthogonal_signedDifference` with `α=τ₁ηⱼ, β=τ₁η₁, γ=τ₂χᵢ, δ=τ₂χ₁,
u=1, v=dᵢ` (`dᵢ` = degree ratio `χᵢ(1)/χ₁(1)`); the four conclusions cover all index combinations
(incl. boundaries `i=1`/`j=1`). Hypotheses discharge as:
- `(α,β)=(γ,δ)=0`: τ₁/τ₂ isometry on `ℤ[Y]`/`ℤ[X]` + distinct irreducibles (`extension_inner_eq`).
- difference-orthogonality `⟨τ₁(ηⱼ−η₁), τ₂(χᵢ−dᵢχ₁)⟩=0`: both diffs supported (vanish at 1) ⟹
  `τ₁=τ₂=τ` there (`extends_on_supported`) ⟹ `=⟨ηⱼ−η₁, χᵢ−dᵢχ₁⟩=0` by the Dade isometry +
  `X ⊥ Y` (disjoint irreducibles). **This is the next leaf to build** (needs the Dade
  supported-isometry lemma `dadeIntegralCharacterMap_inner_eq_on_supported_span` wired to τ₁/τ₂).
- degree-`0` conditions `(τ₁(ηⱼ−η₁))(1)=(τ₂(χᵢ−dᵢχ₁))(1)=0`: **`dadeIntegralCharacterMap_apply_one_eq_zero`**
  (S07:5107, "Dade base map sends supported class functions to functions vanishing at `1`"), since τ
  scales degree by `[G:L]`.

### ⚠️ Framing correction #2 (NEEDS VERIFICATION): `hgen` looks **false** for `X ∪ Y` — it, not
### `himg_ortho`, is where the deep `b≡0` argument lives.
The L3 shell hands `hgen : zSupportedSpan (X∪Y) A ⊆ span ℤ (zSupportedSpan X A ∪ zSupportedSpan Y A)`
to the capstone (`coherentUnion_of_glued`, S07). With `zSupportedSpan S A = {φ ∈ ℤ[S] | supp φ ⊆ A}`
(S07:44), this appears **FALSE**: `χ₁ − aη₁` (`a = χ₁(1)/|W₁| > 1`, so `χ₁(1) = aη₁(1)`) lies in
`zSupportedSpan (X∪Y) A` (it is in `ℤ[X∪Y]` and vanishes at `1`, supported on `H^#`), but **not** in
the RHS: any RHS element is `p + q` with `p` a *supported* `X`-combo (degree `0`, i.e.
`∑ pᵢdᵢ = 0`) and `q` a supported `Y`-combo; coefficient-matching forces `p`'s `X`-part `= χ₁`, which
has degree `a|W₁| ≠ 0` — contradiction. (Degree-counting: a supported `∑cᵢχᵢ + ∑eⱼηⱼ` has
`∑eⱼ = −a∑cᵢdᵢ`, and splits only when `∑cᵢdᵢ = 0`; `χ₁−aη₁` has `∑cᵢdᵢ = 1`.)
**Structural confirmation:** the *single-family* `XAdjoinStepInput.adjoin` derives its `hgen` "from
`hSgen` and the degree-matched support of `χ − aχ₁`" (S08:2296) — i.e. it explicitly **generates the
supported lattice with the diagonal difference `χ − aχ₁`**, which the union shell's `hgen` omits.
**⟹ Hypothesis:** the deep `b≡c≡0 mod a` / (6.7) argument (mmd L168-176, showing
`(χ₁−aη₁)^τ = χ₁^{τ₂} − aη₁^{τ₁}`) is what discharges the **cross-diagonal** generation, i.e. it
targets `extends_on_supported`/`hgen`, **not** `himg_ortho`. So `himg_ortho` alone is likely **not**
the sole remaining obligation — the union needs a `coherentUnion_of_glued` *variant* whose supported
generation includes the cross-diagonals `{χᵢ − aᵢη₁}`, discharged by the b≡0 argument (the already-
landed `peterfalvi_67_centralCommutator` + reg-char `sumNonInflatedDegreeMulChar_of_mem` feed exactly
this). **Verify before committing to "himg_ortho is the last step":** re-derive how the capstone is
meant to supply `hgen`; if the degree-counting above is right, plan a diagonal-aware union lemma.

### Recommended next steps (updated)
1. ✅ **DONE** (2026-06-07 session 3, same commit cluster): **difference-orthogonality leaf** —
   `inner_extension_eq_inner_of_supported` (S08 `OddOrder.Peterfalvi.S08`, axiom-clean, AxiomsCheck-
   registered): for two coherences `hX, hY` off the **same** Dade base map and supported
   `x∈ℤ[X,A]`, `y∈ℤ[Y,A]`, `⟨hX.extension x, hY.extension y⟩ = ⟨x,y⟩` (`extends_on_supported` to τ +
   `dadeIntegralCharacterMap_inner_eq_on_supported_span` on the pair `{x,y}`). Companion
   `extension_apply_one_eq_zero_of_supported` (`(hX.extension x)(1)=0` for supported `x`) supplies
   the (4.1) degree-`0` hypotheses. Both are the (4.1) `hdiff`/degree-`0` inputs — hgen-independent,
   reusable for the diagonal handling too.
2. **`himg_ortho` via (4.1)**: wire `pairwise_inner_eq_zero_of_orthogonal_signedDifference` + #1
   (`inner_extension_eq_inner_of_supported` for `hdiff`, `extension_apply_one_eq_zero_of_supported`
   for degree-`0`) + `n,m ≥ 2` (the B4 issue — needs a reference distinct from each member; the
   degree ratio is just `dᵢ = χᵢ(1)/χ₁(1) ∈ ℝ`, no p-group structure needed). **Blocked only on
   `n ≥ 2`/`m ≥ 2`** (existence of distinct references per member), itself a caller-supplied /
   §6.5-context fact.
3. **Resolve `hgen`**: confirm the counterexample, then build a diagonal-aware union variant (or fix
   the shell) and discharge the cross-diagonal via the b≡0 / (6.7) argument. **This is the real deep
   piece**, best attended.

### The b≡0 / cross-diagonal argument — spine mapped + 4 ingredients landed (2026-06-07 session 3 cont.)

The `hgen` fix (diagonal-aware union) reduces to the **cross-diagonal agreement**
`ν(χᵢ − aᵢη₁) = τ(χᵢ − aᵢη₁)`, i.e. `τ₂χᵢ − aᵢτ₁η₁ = τ(χᵢ − aᵢη₁)`, i.e. the **crux**
`t₁ := ⟨τ(χ₁ − aη₁), τ₁η₁⟩ = −a` (the b≡0 conclusion; parallels the X-chain `crux1` but forced by
(6.7)+norm-bound, **not** the (6.6) degree gap — so `lambda_eq_zero_and_Z_eq_zero` does NOT apply,
its `hD : 2a < ∑(rcᵢ)²mcᵢ` is the wrong forcing).  Spine + status:
- **cross-term** `⟨τ(χ₁−aη₁), τ(η_j−η₁)⟩ = ⟨χ₁−aη₁, η_j−η₁⟩ = a` (j>1): Dade isometry on supported
  (`dadeIntegralCharacterMap_inner_eq_on_supported_span` / `inner_extension_eq_inner_of_supported`) +
  `X⊥Y`.  Tractable.
- **(6.7) divisibility `a ∣ c ≡ b`**: needs "η₁^{τ₁} const on `Z^#`" ⟹ `peterfalvi_67_centralCommutator`
  (LANDED adapter).  The "const on `Z^#`" comes from the **Res-decomposition** `Res_L(η₁^{τ₁}) =
  c∑dᵢχᵢ + χ′` + the **reg-char identity** `∑dᵢχᵢ = (ρ_L − ρ_{L/Z})/(a|W₁|)` (LANDED:
  `sumNonInflatedDegreeMulChar_of_mem` gives `∑_{Z⊄ker χ}χ(1)χ(z) = −|L:Z|`, constant on `Z^#`).
- **norm-bound forcing** `b = 0 ∨ (b=a ∧ m=2)`: ✅ **LANDED** `eq_zero_or_edge_of_dvd_of_normBound`
  (S08, axiom-clean, registered).  The (6.8.1) L176 step.
- ✅ **the gateway = Dade reciprocity** `⟨τα, ψ⟩_G = ⟨α, Res_L ψ⟩_L` for supported `α` — **LANDED**
  (S08, axiom-clean, registered): `inner_dadeIntegralCharacterMap_eq_inner_restrict` (under
  `∀ a, hyp.H a = ⊥`, the TI condition) + the collapse `adjointAverageFun_eq_of_H_eq_bot`
  (`adjointAverageFun χ a = χ a` when `H(a) = ⊥`, the `H(a)=⊥` ⟹ `aH(a)={a}` single-term average,
  modelled on `adjointAverageFun_dadeMap_eq`).  Built from the (2.7) `adjoint_formula` (S04:3894) +
  `dadeIntegralCharacterMap_apply_of_support`.  **Sibley call-site wiring:** ✅ **DONE** — added the
  faithful (6.8.a)-level field `SibleyDadeHypothesis.dade_H_eq_bot : ∀ a, dade.H a = ⊥` (additive;
  nothing constructs the carrier, so safe + honest, since (6.8)'s Dade IS the TI one), and the
  Sibley wrapper `inner_tau_eq_inner_restrict : ⟨α^τ, ψ⟩_G = ⟨α, Res_L ψ⟩_L` (supported `α`).  Full
  build green (3557), registered.  **⟹ Dade reciprocity is now directly usable in the (6.8) context.**

So **5 of the ~6 b≡0 ingredient-classes are landed** ((4.1), diff-ortho, degree-0, norm-bound,
**Dade reciprocity** + its Sibley wrapper, + reg-char & (6.7) adapter).  Remaining = the
**Res-decomposition assembly** (attended): use `inner_tau_eq_inner_restrict`
`⟨η₁^{τ₁}, τ(χᵢ−dᵢχ₁)⟩ = ⟨Res_L(η₁^{τ₁}), χᵢ−dᵢχ₁⟩` + the himg-difference-orthogonality (`=0`, giving
`Res_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′`) → reg-char `∑dᵢχᵢ` const on `Z^#` → (6.7) `a∣c` → norm-bound `b=0`
→ crux `⟨τ(χ₁−aη₁), τ₁η₁⟩ = −a` → cross-diagonal `ν=τ` → diagonal-aware union → capstone.  All
ingredient-lemmas are now in hand; the remaining work is the **assembly + the m=2 relabel + the
diagonal-aware union lemma** (replacing the false-`hgen` shell).

## 2026-06-07 (session 4): framing #2 VERIFIED + diagonal-aware union machinery LANDED

**✅ Framing correction #2 is CONFIRMED — `hgen` is genuinely false, and the missing generators are
EXACTLY the cross-diagonals (one suffices).**  Precise degree-count: a supported (= degree-`0`)
element `∑cᵢχᵢ + ∑eⱼηⱼ ∈ ℤ[X∪Y]` satisfies `∑eⱼ = −a·∑cᵢdᵢ`; by linear independence of the disjoint
irreducibles it lies in `ℤ[zSupportedSpan X A ∪ zSupportedSpan Y A]` **iff** its `X`-part is itself
degree-`0` (`∑cᵢdᵢ = 0`) and its `Y`-part is degree-`0` (`∑eⱼ = 0`).  The cross-diagonal `χ₁−aη₁`
has `∑cᵢdᵢ = d₁ = 1 ≠ 0`, so it is **not** in the plain-`hgen` RHS.  Conversely the supported union
lattice (rank `|X|+|Y|−1`) is generated by `{χᵢ−dᵢχ₁} ∪ {ηⱼ−η₁} ∪ {χ₁−aη₁}`, i.e. by
`zSupportedSpan X A ∪ zSupportedSpan Y A ∪ {single cross-diagonal}`.

**✅ Diagonal-aware union machinery LANDED (build-green + axiom-clean via temp `#print axioms`; full
build 3599; NOT yet AxiomsCheck-registered — deferred until the capstone consumes it).**
- **S07** `coherentUnion_of_glued_withDiagonal` (just after `coherentUnion_of_glued`): generalizes
  the plain union lemma by a set `D` of supported cross-diagonals with `hDτ : ∀ d ∈ D, ν d = τ d`,
  enlarging `hgen` to `… ∪ D`.  `extension_inner_eq` (needs `himg_ortho`) and `extension_mem_ZIrr`
  are **unchanged** (they live on `ℤ[X∪Y]`, never see `D`); only `extends_on_supported` gains the
  `D`-generators, discharged by `hDτ`.  `D = ∅` recovers `coherentUnion_of_glued`.
- **S07** `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`: generator-level wrapper
  (caller checks `hagreeX`/`hagreeY`/`hmixed` on `X`,`Y` only), the diagonal analogue of
  `…_of_generator_mixed_inner_eq`.
- **S08** `SibleyDadeHypothesis.coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius`:
  the Sibley/`Zc` ν-explicit shell (parallel to `…_of_glued_of_frobenius`), routing through the
  generator-level S07 wrapper.  Inputs `ν`/`hagreeX`/`hagreeY`/`hmixed` (as before) + `D` + `hDτ` +
  the satisfiable `hgen` (with `D`) ⟹ `IsCoherent (Xset Zc ∪ Yset)`.

**⟹ The false-`hgen` shell `coherentXunionYset_centralCommutator_of_himg_ortho` (8699) is superseded**
(it is an unconsumed dead `def` with an unsatisfiable hypothesis; left in place, documented here).

### ✅ `himg_ortho` DONE (2026-06-07 session 4, commit `3f486cb`) — the shared bottleneck is resolved
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius` (S08, axiom-clean): for
`χ ∈ X(Zc)`, `η ∈ Y`, `⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  **Two findings correcting the prior pessimism:**
- **`n,m ≥ 2` ARE available** — NOT a missing §6.5 fact.  `2 ≤ |Y|` = `two_le_Yset_ncard`;
  `2 ≤ |X(Zc)|` from `two_le_xBaseBlock_ncard hF centralCommutator_le hXne` + `xBaseBlock_subset` +
  `Set.ncard_le_ncard`.  So distinct references `χ'≠χ`, `η'≠η` always exist
  (`Set.exists_ne_of_one_lt_ncard`).
- **The degree-coefficient trick kills the divisibility/minimality/4-case subtleties.**  Take the
  (4.1) coefficients to be the degrees themselves: `u = χ'(1)`, `v = χ(1)`.  Then
  `u•χ − v•χ' = χ'(1)•χ − χ(1)•χ'` is an *integer* `X`-combination that is degree-`0` **for free**
  (`χ'(1)·χ(1) − χ(1)·χ'(1) = 0`, `mul_comm`), hence supported
  (`sMember_smulDiffSupport_of_charValue_eq`, the new two-coefficient support helper — no `χ'(1) ∣ χ(1)`
  needed).  No need for `χ₁`-minimality or a 4-case reference split: *any* distinct `χ'`, `η'` work.
  `pairwise_inner_eq_zero_of_orthogonal_signedDifference` then yields `⟨α,γ⟩ = 0`, conjugate symmetry
  gives the claim.  Supporting helpers landed: `sMember_smulDiffSupport_of_charValue_eq`,
  `Yset_apply_one` (every `Y`-member has degree `|W₁|`).

### Remaining for the capstone Frobenius branch (`himg_ortho` ✅ landed)

**crux `hDτ` progress (2026-06-07 session 4 cont., commits `badd906` + `31b3b28`, axiom-clean):**
the deep b≡0 spine's first steps are now LANDED:
- **✅ spine steps 1–2 (Res-decomposition orthogonality)** `badd906`:
  `inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius` (span `himg_ortho`) +
  `inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius`
  (`⟨Res^G_L(η^{τ₁}), x⟩_L = 0` for supported `x ∈ ℤ[X(Zc)]`, via reciprocity + span-himg_ortho).
  ⟹ the X-components of `Res^G_L(η₁^{τ₁})` are all `∝ dᵢ`.
- **✅ spine step 5 (reg-char values over `X(Zc)`)** `31b3b28`: reindexing
  `sum_Xset_eq_sum_filter_irreducible_of_frobenius` (X(Z)↔Irr-filter via the (6.6) characterization
  `Xset_eq_irreducible_not_subset_characterKernel` + `sum_bij'`) ⟹ `∑_{χ∈X(Z)}χ(1)χ(z) = -|L⧸Z|`
  (`sum_degree_mul_charValue_Xset_eq_of_frobenius`), `∑χ(1)² = |L|-|L⧸Z|`
  (`sum_degree_sq_Xset_eq_of_frobenius`), combined `∑χ(1)(χ(z)-χ(1)) = -|L|`
  (`sum_degree_mul_charValue_sub_Xset_eq_of_frobenius`).

**🔴 remaining for `hDτ`** (the precise next steps):
1. **`η₁^{τ₁}` const on `Zc^#`** (the (6.7) input): Fourier-expand `Res^G_L(η₁^{τ₁}) ∈ ZIrr L`
   (`mem_ZIrr_repr` / `inner_eq_coeff_of_repr`); on `X(Zc)` the coefficients are `c·ψ(1)/χ₁(1)`
   (Res-orthogonality, with `c = ⟨Res,χ₁⟩`); the `Z⊆ker` part is const on `Z` (factors through
   `L/Z`).  Then `Res(z)−Res(1) = (c/χ₁(1))·(∑χ(1)(χ(z)−χ(1))) = (c/χ₁(1))(−|L|) = −c|H|/a` (reg-char
   combined value, `χ₁(1)=a|W₁|`), constant on `Zc^#`.  **The harder remaining sub-piece** (Fourier
   assembly + X/non-X split + non-X const-on-Z).
2. **`a ∣ c`**: `η₁^{τ₁}` const on `Zc^#` + `peterfalvi_67_centralCommutator` (η₁^{τ₁} = ±irreducible
   ⟹ `≡ mod |H|`) ⟹ `−c|H|/a ≡ 0 mod |H|` ⟹ `a ∣ c`.
3. **the Y-decomposition + `c ≡ b mod a`**: `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑η_j^{τ₁}` (X ⊥ Y^{τ₁};
   the `j>1` coefficients equal via `⟨(χ₁−aη₁)^τ,(η_j−η₁)^τ⟩ = a`); then `⟨Res(η₁^{τ₁}),χ₁−aη₁⟩ = b−a`
   (Dade reciprocity) gives `c ≡ b mod a` ⟹ with step 2, `b ≡ 0 mod a`.
4. **`b = 0`** via `eq_zero_or_edge_of_dvd_of_normBound` (`‖(χ₁−aη₁)^τ‖²=1+a²`, `a,m≥2`; m=2 relabel).
5. **`X = χ₁^{τ₂}`** (index argument, `⟨(χ₁−aη₁)^τ,(χ₂−χ₁)^τ⟩`, n≥3 / n=2 relabel) ⟹ the crux.
2. **`hgen'`** (the satisfiable generation): provable lattice fact — anchors `χ₁∈X(Zc)`, `η₁∈Yset`
   with `χ₁(1)=a|W₁|`, `η₁(1)=|W₁|`; the degree-`0` decomposition
   `φ = (∑cᵢχᵢ − s·χ₁) + (∑eⱼηⱼ + sa·η₁) + s·(χ₁−aη₁)` with `s = ∑cᵢdᵢ ∈ ℤ` (needs `dᵢ ∈ ℤ`, the
   p-power degree ratio, χ₁ minimal); `supp ⊆ A ⟺ degree 0` for the induced lattice (TI).
   `D := {χ₁−aη₁}`.  No deep character theory; focused lattice sub-lemma.
3. **construct `ν`** (`exists_integralCharacterMap_glue_of_orthonormal`, L3 3a — landed; `hmixed`
   reduces to the now-proven `himg_ortho`) + wire the capstone Frobenius branch through
   `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` + L4
   `false_of_coherentXunionYset_of_not_coherentS`.  (A ν-free diagonal shell — analogue of the old
   8699 shell constructing `ν` internally — packages this; with the internally-glued `ν`,
   `hDτ(χ₁−aη₁)` reads `τ₂χ₁ − a·τ₁η₁ = (χ₁−aη₁)^τ` = the crux.)

**Order:** `hDτ` (crux spine, now unblocked by `himg_ortho`) ‖ `hgen'` (independent lattice fact) →
ν-free diagonal shell + capstone wiring.  CertainType case (B) still unplanned.

## 2026-06-08 (session 5): crux `hDτ` spine steps 1–3 + step-4 foundation LANDED (5 commits, axiom-clean)

**All leaf-green (3467) + axiom-clean `[propext, Classical.choice, Quot.sound]`.**  The crux `hDτ`
divisibility spine (the deep `b≡c≡0 mod a` argument, mmd 04.8 L176) is now mostly assembled:

- **step 1 (`η₁^{τ₁}` const on `Zc^#`)** — already landed pre-session (`14ea0ae`/`d1c18ea`):
  `restrict_extension_Yset_degree_value_eq_of_frobenius` (`χ₁(1)·(R(z)−R(1)) = −c·|L|`,
  `R = Res^G_L(η^{τ₁})`, `c = ⟨R,χ₁⟩`) + `restrict_extension_Yset_const_on_centralCommutator_of_frobenius`.
- ✅ **step-2 input (the (6.7)-congruence)** `bb81ca1`:
  `restrict_extension_Yset_charValue_cong_of_frobenius` — `R(z) ≡ R(1) [ALGMOD |H|]` (write
  `η^{τ₁} = ε•ξ`, `ξ` irreducible from norm 1; const-on-`Zc^#` is the
  `peterfalvi_67_centralCommutator` hypothesis; scale by `ε` via `Cong.smul_left`).
- ✅ **step 2 (`a ∣ c`)** `f92617c`: `dvd_inner_restrict_extension_Yset_of_frobenius` — for
  `χ₁(1) = a·|W₁|` (`a>0`), `c = ⟨R,χ₁⟩ ∈ ℤ` and `a ∣ c`.  Value identity (with `χ₁(1)=a|W₁|`,
  `|L|=|H||W₁|` via `index_H_eq_card_W1` + `Subgroup.index_mul_card`) gives `(R(z)−R(1))/|H| = −c/a`;
  the congruence makes it an algebraic integer; rational alg-int ⟹ integer
  (`RepresentationTheory.isIntegral_rat_imp_int`).  `c∈ℤ` via `restrict_mem_ZIrr` + `mem_ZIrr_inner_int`.
- ✅ **step 3 (`a ∣ b`)** `cdb2ca8`: `dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius` — the
  `η₁^{τ₁}`-coefficient `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩` (= `b−a`) is an integer divisible by `a` (⟺ `a∣b`).
  **Direct route — bypasses the full (168) decomposition:** reciprocity `inner_tau_eq_inner_restrict`
  (`χ₁−aη₁` supported via `sMember_scaledDiffSupport_of_charValue_eq`) gives
  `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩ = c − a·e` (`inner_conj_symm` + reality of `c=⟨R,χ₁⟩`,
  `e=⟨R,η₁⟩`); `a∣c` (step 2) + `a∣a·e` ⟹ done.
- ✅ **step-4 foundation (the constancy isometry)** `4ceb421`:
  `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius` — `⟨(χ₁−aη₁)^τ, (η_j−η₁)^τ⟩ = a` (η_j≠η₁), via
  Dade isometry on the supported pair (`dadeIntegralCharacterMap_inner_eq_on_supported_span`) +
  `X⊥Y` + `Y`-orthonormality.  This is the `β_j − β₁ = a` (j>1) constancy of the `η_j^{τ₁}`-coefficients.

### 🔴 Remaining for `hDτ` (refined plan, session 5)
- **step 4 (`b = 0`)** — the next big unit, needs the **full (168) decomposition**
  `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑_j η_j^{τ₁}`, `X ⊥ Y^{τ₁}`: project `(χ₁−aη₁)^τ` (∈ ZIrr G) onto the
  orthonormal `{η_j^{τ₁}}_{j∈Y}` (coefficients `β_j = ⟨(χ₁−aη₁)^τ, η_j^{τ₁}⟩ ∈ ℤ`), define
  `X := (χ₁−aη₁)^τ − ∑_j β_j η_j^{τ₁}` (⊥ all η_j^{τ₁}); the constancy `4ceb421` gives `β_j = β_{j'}`
  (j,j'>1, since `⟨(χ₁−aη₁)^τ,(η_j−η_{j'})^τ⟩ = ⟨χ₁−aη₁, η_j−η_{j'}⟩ = 0`) and `β_j − β₁ = a` (j>1),
  so all-but-η₁ coefficients equal `b := β₁ + a` and η₁ coefficient is `b−a`.  Parseval +
  `‖(χ₁−aη₁)^τ‖² = ‖χ₁−aη₁‖² = ‖χ₁‖²+a²‖η₁‖² = 1+a²` (Dade isometry on the supported `χ₁−aη₁` +
  X⊥Y orthonormality) gives `1+a² = ‖X‖² + (b−a)² + (m−1)b²`, i.e. (with `b=ax`)
  `(x−1)²+(m−1)x² ≤ 1+1/a²`.  `eq_zero_or_edge_of_dvd_of_normBound` (**already landed**, takes `2≤a`,
  `2≤m`, `a∣b`, the norm ineq) ⟹ `b=0 ∨ (b=a ∧ m=2)`.  Need `2≤a` (from `X∩Y=∅`: `a=1` ⟹ χ₁ has
  degree `|W₁|` ⟹ χ₁∈Y, contra `disjoint_Xset…`), `2≤m` (`two_le_Yset_ncard`); the `b=a∧m=2` edge
  case reduces to `b=0` by relabelling `η₁^{τ₁},η₂^{τ₁} ↦ −η₂^{τ₁},−η₁^{τ₁}`.  **This is a sizable
  new development** (the Y-family projection + Parseval bookkeeping); best a fresh focused session.
- **step 5 (`X = χ₁^{τ₂}`)** ⟹ the crux `(χ₁−aη₁)^τ = χ₁^{τ₂} − aη₁^{τ₁}` = `hDτ`: with `b=0`,
  `(χ₁−aη₁)^τ = X − aη₁^{τ₁}`, `‖X‖²=1`; consider `⟨(χ₁−aη₁)^τ,(χ₂−χ₁)^τ⟩` (= `⟨χ₁−aη₁,χ₂−χ₁⟩` by
  isometry) ⟹ `X=χ₁^{τ₂} ∨ X=−χ₂^{τ₂}`; for `n≥3` pin via `⟨(χ₁−aη₁)^τ,(χ₃−d₃χ₁)^τ⟩`, `n=2` relabel.
- **then wiring:** `hgen'` (lattice fact, unchanged plan above) + ν-free diagonal shell through
  `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` + L4
  `false_of_coherentXunionYset_of_not_coherentS`.  CertainType case (B) still unplanned.

## 2026-06-08 (session 5 cont.): step-4 ingredient set COMPLETE (3 more commits, axiom-clean)

All leaf-green (3467) + axiom-clean.  The **complete ingredient set for the step-4 dichotomy
`b = 0 ∨ (b = a ∧ m = 2)`** is now landed:
- ✅ **norm `‖(χ₁−aη₁)^τ‖² = 1+a²`** `b97d2f9a`: `inner_self_tau_scaledDiff_of_frobenius` (Dade
  isometry on the supported singleton `{χ₁−aη₁}` + `χ₁/η₁`-orthonormality + `X⊥Y`).  Peterfalvi's
  norm-identity LHS.
- ✅ **Bessel's inequality (general, reusable)** `b2fe3bd7`:
  `OddOrder.RepresentationTheory.sum_sq_le_inner_self_re` — for an orthonormal Finset family `s`
  (`⟨a,b⟩=δ`) and `v` with integer coefficients `⟨v,a⟩=β a` on `s`,
  `(∑_{a∈s} (β a)² : ℝ) ≤ (⟨v,v⟩).re`.  Pythagoras on `v=(v−p)+p`, `p=∑β_a•a`
  (`inner_self_orthonormalSum_eq_sum_sq` + `inner_conj_symm` + `inner_self_re_nonneg`).
- ✅ **`a ≥ 2`** `066da126`: `two_le_degreeRatio_of_mem_Xset_of_frobenius` — `χ₁∈X(Zc)`,
  `χ₁(1)=a|W₁|` ⟹ `2≤a` (`a=1` ⟹ source `θ` linear nontrivial ⟹ `χ₁∈Y`, contra `X∩Y=∅`; uses
  `exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one` + `linearIrreducibleCharacter_eq_trivial_iff`
  + `mem_Yset_iff_exists_linear_source` + `IrreducibleCharacter.ext`).

### 🔴 Remaining for step 4 (the dichotomy ASSEMBLY — all ingredients in hand)
The next unit is purely **assembly** (lengthy Finset bookkeeping, no new math):
1. Build the **Y^{τ₁}-image Finset** `s := Yset.toFinset.image (coherentYset.extension)` with
   orthonormality `⟨ext η, ext η'⟩ = ⟨η,η'⟩ = δ` (`extension_inner_eq` + Y orthonormal; injectivity of
   `extension` on Y from orthonormality) — OR reuse the S07 `OrthonormalCharacterImageFamily` of the
   `coherentYset` if it exposes one.
2. Coefficient function `β ψ := ⟨v, ψ⟩` (`v = (χ₁−aη₁)^τ`), integer-valued (`v∈ZIrr G`,
   `mem_ZIrr_inner_int` — though here β is real/int via the constancy values).  Values:
   `β (ext η₁) = bb` (step 3 `dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius`),
   `β (ext η) = bb + a` for `η≠η₁` (constancy `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`:
   `⟨v,(η−η₁)^τ⟩ = a` and `(η−η₁)^τ = ext η − ext η₁` ⟹ `β(ext η) − β(ext η₁) = a`).
3. `∑_{ψ∈s} (β ψ)² = bb² + (m−1)(bb+a)²` (`m = |Y| = s.card`; one element `ext η₁` gets `bb`, the
   other `m−1` get `bb+a`) — `Finset.sum` with the `if`-coefficient.
4. **Bessel** (`sum_sq_le_inner_self_re`) + **norm** (`(⟨v,v⟩).re = 1+a²`, `.re` of `b97d2f9a`) ⟹
   `bb² + (m−1)(bb+a)² ≤ 1+a²`.
5. **`eq_zero_or_edge_of_dvd_of_normBound`** (already landed) with Peterfalvi `b := bb+a`, `a∣b`
   (⟺ `a∣bb`, step 3), `2≤a` (`066da126`), `2≤m` (`two_le_Yset_ncard`), hnorm = step 4 ⟹
   `b=0 ∨ (b=a∧m=2)`, i.e. **`bb=−a ∨ (bb=0 ∧ m=2)`**.
6. GOOD case `bb=−a`: the Y-projection of `v` is `−a·η₁^{τ₁}` (`β(ext η₁)=−a`, `β(ext η)=0` for
   η≠η₁), so `v = X − aη₁^{τ₁}` with `X ⊥ Y^{τ₁}`, `‖X‖²=1`.  EDGE case `m=2`: relabel
   `η₁^{τ₁},η₂^{τ₁} ↦ −η₂^{τ₁},−η₁^{τ₁}` (re-choose the `Y`-coherence isometry — structurally the
   hardest remaining piece) reduces to `bb=−a`.
- **then step 5 (`X=χ₁^{τ₂}`)** ⟹ crux `(χ₁−aη₁)^τ = χ₁^{τ₂}−aη₁^{τ₁}` = `hDτ`, then `hgen'` +
  ν-free diagonal shell + capstone wiring.  CertainType (B) still unplanned.

### Key API discovered this session (don't re-derive)
- **Rational alg-int ⟹ integer:** `OddOrder.RepresentationTheory.isIntegral_rat_imp_int {q:ℚ}
  (IsIntegral ℤ (q:ℂ)) : ∃ n:ℤ, (q:ℂ)=n` (ClassSumAlgebra.lean:1434).
- **ZIrr inner integrality:** `OddOrder.RepresentationTheory.mem_ZIrr_inner_int (χ:IrreducibleChar G)
  (hφ:φ∈ZIrr G) : ∃ m:ℤ, inner φ χ = m` (ZIrrFourier.lean:52) — **ZIrr first arg**, use
  `inner_conj_symm` to flip.  **Restriction preserves ZIrr:**
  `OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr (H:Subgroup G) (hφ:φ∈ZIrr G) :
  restrict H φ ∈ ZIrr ↥H` (InducedCharacter.lean:644, namespace `…ClassFunction`).
- **Inner conj symmetry:** `OddOrder.RepresentationTheory.inner_conj_symm (φ ψ) : inner ψ φ =
  star (inner φ ψ)` (ZIrrFourier.lean:147); `star_intCast` for `star (n:ℂ)=n`.  Inner is **linear in
  1st arg** (`ClassFunction.inner_smul_left c φ ψ : inner (c•φ) ψ = c*inner φ ψ`, `inner_sub_left`).
- **ALGMOD:** `OddOrder.AlgInt.Cong n α β := IsIntegral ℤ ((α−β)/n)`; `cong_def` unfolds it.
- **`hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)`** (abbrev);
  Dade isometry on supported: `S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade
  hyp.hconj (hS : ∀s∈S, supported) (hφ:φ∈zSpan S)(hζ:ζ∈zSpan S) : ⟨τφ,τζ⟩ = ⟨φ,ζ⟩`.  Reciprocity:
  `hyp.inner_tau_eq_inner_restrict (hαsupp) ψ : ⟨hyp.tau α, ψ⟩ = ⟨α, restrict L ψ⟩`.
- **Supports/degrees:** `sMember_scaledDiffSupport_of_charValue_eq (hχS)(hχ'S)(χ 1 = a*χ' 1) :
  (χ − a•χ').support ⊆ H^#`; `sMember_diffSupport_of_charValue_eq` (equal degree);
  `sMember_charValue_one_eq_mul_anchor (hχ∈S)(χ₁ 1=|W₁|) : ∃a:ℕ, 0<a ∧ χ 1=a*χ₁ 1` (the degree
  ratio `a`); `Yset_apply_one (hη) : η 1 = |W₁|`; `index_H_eq_card_W1 : H.index = |W₁|`;
  `Subgroup.index_mul_card H : H.index * |H| = |L|`.  `Xset_subset_S`, `Yset_subset_S`,
  `centralCommutator_ne_bot (hHnonab)` (+ `Subgroup.ne_bot_iff_exists_ne_one` for a `z∈Zc^#`).
- **(session 5 cont.):** `inner_self_re_nonneg (φ) : 0 ≤ (⟨φ,φ⟩).re` (ZIrrFourier:177);
  `inner_self_orthonormalSum_eq_sum_sq (horth) : ⟨∑c_a•a, ∑c_a•a⟩ = ∑(c_a)²` (Parseval,
  ZIrrFourier:352); `Complex.intCast_re`.  Degree-1↔linear:
  `IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one (hφ)(φ 1=1) :
  ∃ χ:G→*ℂˣ, (linearIrreducibleCharacter χ : CF)=φ` (LinearCharacter:169);
  `linearIrreducibleCharacter_eq_trivial_iff : linear χ = trivial ↔ χ=1` (LinearCharacter:84);
  `IrreducibleCharacter.ext (↑χ=↑ψ) : χ=ψ`; `S_eq : S = {φ | ∃θ:Irr H, θ≠trivial ∧ φ=induce H ↑θ}`;
  `ClassFunction.induce_apply_one : (induce H ψ) 1 = H.index * ψ 1`; `mem_Yset_iff_exists_linear_source`.
  ⚠ inner: linear in 1st arg (`ClassFunction.inner_smul_left`/`inner_sub_left`/`inner_sub_right`),
  conj-linear in 2nd (`OddOrder.RepresentationTheory.inner_smul_right : ⟨φ,c•ψ⟩=star c·⟨φ,ψ⟩` — NOT in
  `ClassFunction` namespace).

## 2026-06-08 (session 6): step 4 COMPLETE (dichotomy + good-case `X`-structure) + step-5 isometry value (3 commits, axiom-clean)

All leaf-green (3467) + axiom-clean `[propext, Classical.choice, Quot.sound]`.  The step-4
dichotomy ASSEMBLY (the lengthy Finset bookkeeping recipe of "session 5 cont.") was sitting
**uncommitted** in the worktree from a prior session; this session committed it and pushed the
crux spine forward two more units:

- ✅ **step-4 dichotomy** `eea00823`: `coeff_eq_neg_or_edge_of_frobenius` —
  `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a ∨ (|Y|=2 ∧ = 0)` (Peterfalvi's `b=0 ∨ (b=a∧m=2)`).  Builds the
  `Y^{τ₁}`-image Finset, coefficient values `bb`/`bb+a`, `∑β²=bb²+(m−1)(bb+a)²`, feeds `sum_sq_le_inner_self_re`
  (Bessel) + the `b97d2f9a` norm + `eq_zero_or_edge_of_dvd_of_normBound`.  (Exactly the recipe; no new math.)
- ✅ **step-4 good-case `X`-structure** `8709ee15`:
  `orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius` — in the good case
  `⟨v, η₁^{τ₁}⟩ = −a` (`v = (χ₁−aη₁)^τ`), the element **`X := v + a·η₁^{τ₁}`** is ⊥ the whole
  `Y^{τ₁}` family, has `‖X‖² = 1`, and lies in `ℤ[Irr G]`.  (Peterfalvi's `(χ₁−aη₁)^τ = X − aη₁^{τ₁}`,
  `‖X‖²=‖χ₁‖²=1`.)  Orthogonality from the constancy `4ceb421` + `⟨v,η₁^{τ₁}⟩=−a`; norm
  `(1+a²)−a²−a²+a²=1`; ZIrr from `dadeIntegralCharacterMap_mem_ZIrr_of_supported` + `extension_mem_ZIrr`.
- ✅ **step-5 `X`-difference isometry value** `a5df2a3a`:
  `inner_tau_scaledDiff_tau_Xset_diff_of_frobenius` — `⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1` for a second
  **equal-degree** `X`-member `χ₂ ∈ X(Zc)`, `χ₂≠χ₁`, `χ₂(1)=χ₁(1)`.  Dade isometry on the supported
  pair ⟹ source `⟨χ₁−aη₁,χ₂−χ₁⟩ = (0−a·0)−(1−a·0) = −1` (X-orthonormality + X⊥Y).  Mirror of the
  Yset-diff constancy lemma.

### 🔴 Remaining for the crux `hDτ` (refined, session 6)
The crux is `(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}` for the **fixed** `τ₁ = coherentYset`,
`τ₂ = Xset_centralCommutator_isCoherent`.  With `X := v + a·η₁^{τ₁}` (good case), the crux ⟺ `X = χ₁^{τ₂}`.

- **step 5 (`X = χ₁^{τ₂}`)** — the next focused unit.  **A `±Irr` lemma is NOT needed** (worked out
  this session): use `⟨X, χ₁^{τ₂}⟩ = 1` ⟹ `‖X − χ₁^{τ₂}‖² = ‖X‖² − 2·Re⟨X,χ₁^{τ₂}⟩ + ‖χ₁^{τ₂}‖² = 1−2+1 = 0`
  ⟹ `X = χ₁^{τ₂}`.  To get `⟨X,χ₁^{τ₂}⟩=1`:
  1. **translation** (relabel-free, ~60–80 lines): `⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1`.  From the
     isometry value `a5df2a3a`: `⟨v,(χ₂−χ₁)^τ⟩=−1`; `(χ₂−χ₁)^τ = χ₂^{τ₂}−χ₁^{τ₂}` (X-coherence
     `extends_on_supported` on the supported equal-degree diff χ₂−χ₁); `v = X − a·η₁^{τ₁}` and
     `η₁^{τ₁} ⊥ X^{τ₂}` (himg_ortho `inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`,
     conj-flip) ⟹ `⟨v,χ_j^{τ₂}⟩ = ⟨X,χ_j^{τ₂}⟩`.
  2. **Bessel pinning** (relabel-free for the generic case): `⟨X,χ_j^{τ₂}⟩ ∈ ℤ` (X, χ_j^{τ₂} ∈ ZIrr,
     `mem_ZIrr_inner_int`); `∑_{χ∈X(Zc)} ⟨X,χ^{τ₂}⟩² ≤ ‖X‖² = 1` (`sum_sq_le_inner_self_re` over the
     orthonormal `X^{τ₂}` family).  With the relation `⟨X,χ₁^{τ₂}⟩−⟨X,χ₂^{τ₂}⟩=1`, integer coeffs +
     ∑²≤1 force `(⟨X,χ₁^{τ₂}⟩,⟨X,χ₂^{τ₂}⟩) ∈ {(1,0),(0,−1)}`, i.e. `X=χ₁^{τ₂} ∨ X=−χ₂^{τ₂}`.  For
     `n=|xBaseBlock|≥3` a third anchor χ₃ pins `(1,0)`; for `n=2`, **relabel** (see below).
  - **inputs needed**: a second equal-degree anchor `χ₂` and `χ₁ ∈ xBaseBlock Zc` (the minimal-degree
    block; `xBaseBlock_degree_re_eq` = equal degree, `xBaseBlock_subset`).  `2 ≤ |xBaseBlock Zc|`
    (note's `two_le_xBaseBlock_ncard` — VERIFY it exists / is for Zc).  ⚠ the good-case χ₁ must be a
    **base-block** anchor (minimal degree) for `χ₂−χ₁` equal-degree-supported — re-derive the good
    case with `χ₁ ∈ xBaseBlock`, not a general X-anchor.

- **🛑 the relabels = the structural bottleneck** (both `m=2` step-4 edge and `n=2` step-5 edge).
  Worked out this session: the relabel `η₁^{τ₁},η₂^{τ₁} ↦ −η₂^{τ₁},−η₁^{τ₁}` (or the X-analogue) is a
  **different `IsCoherent` witness** with flipped signs.  It IS valid (preserves `extends_on_supported`:
  the difference `η₁−η₂ ↦ τ(η₁−η₂)` is unchanged under swap+negate — verified), but the FIXED
  `coherentYset`/`Xset_centralCommutator_isCoherent` are not it.  **The crux for the fixed maps is
  FALSE in the edge cases**, so the "ν-free diagonal shell over the fixed extensions" plan only works
  in the **generic `n,m ≥ 3` case**.  Two ways forward:
  (a) **land the generic case first** — prove the capstone Frobenius branch assuming `3 ≤ |xBaseBlock Zc|`
      and `3 ≤ |Y|` (no relabel), defer edge cases.  Lets `hDτ`+`hgen'`+ν-shell+wiring complete for
      generic, isolating the relabel as the sole remaining gap.
  (b) **build relabel infrastructure** — a constructor producing an `IsCoherent` witness for a 2-element
      sign-swap of an equal-degree coherent family (new `IntegralCharacterMap` with flipped values; prove
      the 4 `IsCoherent` fields).  Reusable for both edges.  Structurally hardest; the `retarget`
      machinery (S07:2987–3360, builds τ₂ from target pairs `{X,X̄}`) is the closest existing template.
  **Recommend (a) first** (concrete generic-case progress) then (b).

- **then**: `hgen'` (lattice fact — degree-0 decomp + supp↔deg-0 for the induced lattice, `D := {χ₁−aη₁}`,
  unchanged plan) + ν-free diagonal shell through
  `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` (S08:8928; needs
  `ν`/`hagreeX`/`hagreeY`/`hmixed`(=himg_ortho)/`D`/`hDτ`(=crux)/`hgen`) + L4
  `false_of_coherentXunionYset_of_not_coherentS`.  **CertainType case (B)** (mmd (6.8.2), `Z=W₂`,
  τ₂-glue, separate (6.8.2.1)/(6.8.2.2)/(6.8.2.3) lemmas) still **unplanned** — capstone needs BOTH
  `hyp.cases` branches.

### Key API (session 6, don't re-derive)
- **Step-4 dichotomy** `coeff_eq_neg_or_edge_of_frobenius (hyp)(hF)(hHnonab)(hp)(hp3)(hHp)(hη₁:η₁∈Yset)
  (hχ₁:χ₁∈Xset Zc)(ha_pos:0<a)(ha:χ₁ 1=a·|W₁|) : ⟨tau(χ₁−a•η₁), coherentYset.extension η₁⟩ = −a ∨
  (Yset.ncard=2 ∧ … = 0)`.
- **Good-case `X`** `orthogonal_normOne_tau_scaledDiff_add_extension_of_frobenius (hyp)(hF)(hη₁)(hχ₁)
  (ha:χ₁ 1=a·|W₁|)(hgood:⟨tau(χ₁−a•η₁),ext η₁⟩=−a)` : `(∀η∈Yset, ⟨v+a•ext η₁, ext η⟩=0) ∧
  ⟨v+a•ext η₁, v+a•ext η₁⟩=1 ∧ v+a•ext η₁ ∈ ZIrr G` (`v=tau(χ₁−a•η₁)`, `a•` = `(a:ℂ)•`).
- **Step-5 isometry value** `inner_tau_scaledDiff_tau_Xset_diff_of_frobenius (hyp)(hF)(hη₁)(hχ₁)
  (hχ₂)(hne:χ₂≠χ₁)(ha:χ₁ 1=a·|W₁|)(hdeg2:χ₂ 1=χ₁ 1) : ⟨tau(χ₁−a•η₁), tau(χ₂−χ₁)⟩ = −1`.
- `IsIrreducibleCharacter.mem_ZIrr (hφ) : φ ∈ ZIrr G` (ZIrr.lean:160).  `nsmul_mem (h:x∈S)(n) : n•x∈S`
  (submodule).  `Nat.cast_smul_eq_nsmul ℂ a x : (↑a)•x = a•x`.  `dadeIntegralCharacterMap_mem_ZIrr_of_supported
  hyp.dade hyp.hconj (hsupp)(hZIrr:φ∈ZIrr L) : tau φ ∈ ZIrr G` (S07:5196 — ⚠ needs the **ZIrr-L** arg).
- `xBaseBlock Z = {χ∈Xset Z | minimal re-degree}`; `xBaseBlock_subset`, `xBaseBlock_degree_re_eq`
  (S08:5449–5478).  himg_ortho landed = `inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.

## 2026-06-08 (session 6 cont.): crux `hDτ` COMPLETE in the generic `m,n ≥ 3` case (5 more Lean commits, axiom-clean)

The entire step-5 + crux spine landed.  All leaf-green (3467) + axiom-clean.  **The crux `hDτ`
`(χ₁−aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}` now holds UNCONDITIONALLY when `|Y| ≥ 3` and a third equal-degree
`X`-anchor exists** (`crux_of_frobenius`, `17b79c5a`).  Commits:

- ✅ **step-5 relation** `a453969e`: `inner_extension_Xset_sub_eq_neg_one_of_frobenius` —
  `⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1` for `X := (χ₁−aη₁)^τ + a·η₁^{τ₁}`.  Via himg_ortho
  (`η₁^{τ₁} ⊥ X^{τ₂}`, so `⟨X,χ_j^{τ₂}⟩ = ⟨(χ₁−aη₁)^τ,χ_j^{τ₂}⟩`) + X-coherence
  `(χ₂−χ₁)^τ = χ₂^{τ₂}−χ₁^{τ₂}` + the isometry value `a5df2a3a`.
- ✅ **step-5 dichotomy** `a6d88cf3`: `extension_eq_or_eq_neg_of_frobenius` —
  `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`.  Bessel `c₁²+c₂² ≤ ‖X‖²=1` via positive-definiteness
  (`inner_self_re_nonneg` of the residual `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`, integer coeffs
  `inner_mem_ZIrr_int` — **NO `±Irr` lemma**) + relation `c₂−c₁=−1` ⟹ `(c₁,c₂) ∈ {(1,0),(0,−1)}`;
  `⟨X,·⟩=1` + both norm 1 ⟹ equal by `eq_zero_of_inner_self_re_eq_zero`.
- ✅ **crux (n≥3 case)** `1c1f37cb`: `crux_of_third_anchor_of_frobenius` — a third equal-degree anchor
  `χ₃` excludes the right disjunct (`X=−χ₂^{τ₂}` ⟹ the χ₃ relation gives `0=−1`), so `X=χ₁^{τ₂}`,
  and `eq_sub_of_add_eq` gives the crux.
- ✅ **good-case discharge (m≥3)** + **generic crux** `17b79c5a`:
  `inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius` (`|Y|≥3` ⟹ step-4 edge `m=2` impossible
  ⟹ good case `⟨v,η₁^{τ₁}⟩=−a`) feeds `crux_of_frobenius` (`|Y|≥3` + third anchor ⟹ crux, no hgood).

### 🔴 Remaining for the capstone (refined, session 6 cont.)
1. **Relabels (m=2 / n=2 edge cases)** — still the structural bottleneck.  The generic crux needs
   `3 ≤ |xBaseBlock Zc|` (for the third anchor `χ₃`) AND `3 ≤ |Y|` (for hgood).  When either is 2,
   relabel.  Plan unchanged: build a 2-element sign-swap `IsCoherent` constructor (template = `retarget`
   S07:2987–3360), OR restructure the capstone to choose relabeled witnesses.  **Could also defer**:
   land the capstone Frobenius branch under the explicit `3 ≤ |xBaseBlock Zc| ∧ 3 ≤ |Y|` hypotheses
   first, isolate the relabel as the sole gap.
2. **`hgen'`** (the diagonal-aware generation, relabel-free): `zSupportedSpan (X∪Y) A ⊆ span(zSupp X ∪ zSupp Y ∪ {χ₁−aη₁})`.
   Degree-0 decomp `φ = (∑cᵢχᵢ − s·χ₁) + (∑eⱼηⱼ + sa·η₁) + s·(χ₁−aη₁)`, `s = ∑cᵢdᵢ ∈ ℤ` (needs
   `dᵢ ∈ ℤ` = p-power degree ratio, χ₁ minimal); supp↔deg-0 for the induced lattice (TI).  Focused
   lattice sub-lemma, no deep character theory.
3. **ν construction + ν-free diagonal shell**: build `ν = coherentImageMapGlue` (X^{τ₂} ⊕ Y^{τ₁}),
   discharge `hagreeX`/`hagreeY` (defn), `hmixed` (= himg_ortho), `hDτ` (= `crux_of_frobenius`), `hgen`
   (= hgen'); route through `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius`
   (S08:8928) + L4 `false_of_coherentXunionYset_of_not_coherentS`.
4. **CertainType case (B)** (mmd (6.8.2), `Z=W₂`, separate (6.8.2.1)/(6.8.2.2)/(6.8.2.3)) — unplanned.

**Recommended next session:** `hgen'` (relabel-free, focused) → ν-shell wiring under `3≤|xBaseBlock|, 3≤|Y|`
⟹ generic-case capstone Frobenius branch done; THEN relabels; THEN CertainType (B).

### Key API (session 6 cont.)
- **generic crux** `crux_of_frobenius (hyp)(hF)(hHnonab)(hp)(hp3)(hHp)(hη₁)(hχ₁)(hχ₂)(hne₂:χ₂≠χ₁)
  (hχ₃)(hne₃₁:χ₃≠χ₁)(hne₃₂:χ₃≠χ₂)(ha:χ₁ 1=a·|W₁|)(hdeg2:χ₂ 1=χ₁ 1)(hdeg3:χ₃ 1=χ₁ 1)(hm3:3≤|Y|)`
  : `tau(χ₁−a•η₁) = χ₁^{τ₂} − a·η₁^{τ₁}` (the equality form of `hDτ`).
- `extension_eq_or_eq_neg_of_frobenius (… hgood:⟨tau(χ₁−a•η₁),ext η₁⟩=−a)` : `X=χ₁^{τ₂} ∨ X=−χ₂^{τ₂}`
  (`X := tau(χ₁−a•η₁)+a•ext η₁`).
- `inner_extension_Xset_sub_eq_neg_one_of_frobenius (…)` : `⟨X,χ₂^{τ₂}⟩−⟨X,χ₁^{τ₂}⟩=−1`.
- `inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius (…)(hm3:3≤|Y|)` : `⟨tau(χ₁−a•η₁),ext η₁⟩=−a`.
- `OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int (hφ:φ∈ZIrr)(hψ:ψ∈ZIrr) : ∃m:ℤ, ⟨φ,ψ⟩=m`
  (InducedCharacter:716 — ⚠ full path `…ClassFunction.inner_mem_ZIrr_int`); `eq_zero_of_inner_self_re_eq_zero
  (h:(⟨φ,φ⟩).re=0) : φ=0` (ZIrrFourier:189); `Complex.intCast_re`, `star_intCast`, `Finset.sum_pair`.

## 2026-06-08 (session 6 cont.²): `hgen'` support side landed (`zSpan_S_support_subset_of_apply_one_eq_zero`)

✅ **support side of `hgen'`** (`aa6476a0`, axiom-clean): `zSpan_S_support_subset_of_apply_one_eq_zero`
— any `φ ∈ ℤ[S]` with `φ(1) = 0` is supported on `H^# = sharpImage H`.  `φ.support ⊆ H` by span
induction (each S-member is, `sMember_support_subset_H`; `+`/`zsmul`-closed — the `zsmul` case needs
`← Int.cast_smul_eq_zsmul ℂ` then `smul_apply`+`mul_zero`); `φ(1)=0` removes `1`.  The multi-term
generalisation of the 2-term `sMember_(scaled)diffSupport_of_charValue_eq` — usable for **both** the
`X`-part `∑cᵢχᵢ−sχ₁` and the `Y`-part `∑eⱼηⱼ+saη₁` of the `hgen'` decomposition (both degree-0).

### 🔴 Remaining for `hgen'` (degree side + decomposition)
- **degree-ratio integrality `dᵢ = χᵢ(1)/χ₁(1) ∈ ℕ`** (for `χ₁ ∈ xBaseBlock Zc` minimal): sources
  `θ,θ₁ ∈ Irr H` have p-power degrees (`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`,
  ZIrr.lean:254 — **available**); `χ₁` minimal (`natDegree_le_of_xBaseBlock_anchor` S08:5482) ⟹
  `θ₁(1) ≤ θ(1)` ⟹ `p^{k₁} | p^k` ⟹ `χ₁(1) | χᵢ(1)`.  ~50–80 lines (source extraction via `S_eq` +
  `induce_apply_one` + p-power comparison).
- **the decomposition itself**: `φ ∈ zSupportedSpan (X∪Y) A`, write `φ = ∑_{X} cᵢχᵢ + ∑_{Y} eⱼηⱼ`
  (Finsupp over X∪Y), `s := ∑cᵢdᵢ ∈ ℤ`; then `∑cᵢχᵢ−sχ₁ ∈ zSupportedSpan X A` (degree 0 via the new
  support lemma + `s·χ₁(1)=∑cᵢχᵢ(1)`) and `∑eⱼηⱼ+saη₁ ∈ zSupportedSpan Y A` (degree 0: `φ(1)=0` ⟹
  `∑eⱼ=−sa`), and `s·(χ₁−aη₁) ∈ span{χ₁−aη₁}`.  Finsupp split of `zSpan(X∪Y)` into `zSpan X ⊕ zSpan Y`
  (X,Y disjoint) is the bookkeeping.  Substantial (~150–250 lines).

**Then** ν-shell wiring (under `3≤|xBaseBlock Zc|, 3≤|Y|` ⟹ crux + hgen' both available) ⟹ generic
capstone Frobenius branch.  Then relabels; then CertainType (B).  **Next session: degree-ratio
integrality (small, p-power lemma available) → the Finsupp decomposition → ν-shell.**

## 2026-06-08 (session 6 cont.³): `hgen'` COMPLETE + generic capstone Frobenius branch ASSEMBLED (3 more commits, axiom-clean)

The entire (6.8.1) generic-case spine is now assembled end-to-end.  All leaf-green (3467) +
axiom-clean.  Commits:

- ✅ **degree-ratio integrality** `6f38d283`: `exists_charValue_one_eq_mul_xBaseBlock_anchor` —
  `χ∈X(Z)`, `χ₁∈xBaseBlock Z` ⟹ `∃ d:ℕ, 0<d ∧ χ(1)=d·χ₁(1)`.  Sources p-power
  (`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`) + minimality
  (`natDegree_le_of_xBaseBlock_anchor`) ⟹ `p^{k₁} | p^k`.  (hgen' degree side.)
- ✅ **`hgen'` assembly** `d2867ae3`: `hgen_withDiagonal_of_frobenius` —
  `ℤ[X(Zc)∪Y,A] ⊆ span(ℤ[X(Zc),A] ∪ ℤ[Y,A] ∪ {χ₁−a·η₁})`.  `φ=φ_X+φ_Y` (`span_union`/`mem_sup`),
  `s∈ℤ` via span induction + degree-ratio, three-piece decomposition (the `s·χ₁`/`s·(a·η₁)` cancel,
  `abel`), supports via `zSpan_S_support_subset_of_apply_one_eq_zero`.
- ✅✅ **generic capstone Frobenius branch** `021808e3`:
  `coherentXunionYset_centralCommutator_diagonal_of_frobenius` — given 3 distinct equal-degree
  anchors `χ₁∈xBaseBlock, χ₂, χ₃` (n≥3) + `η₁∈Y` + `3≤|Y|` (m≥3), **`X(Zc)∪Y` is coherent**.
  ν built internally (`exists_integralCharacterMap_glue_of_orthonormal`); hDτ=`crux_of_frobenius`
  (via `map_sub`/`map_nsmul` + glue), hgen=`hgen_withDiagonal_of_frobenius`, hmixed=himg_ortho;
  routed through `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` (S08:8928).

**⟹ the (6.8.1) generic (m,n≥3) case is COMPLETE end-to-end** (step 4 → step 5 → crux → hgen' →
ν-shell → X(Zc)∪Y coherent).  No `sorry`, axiom-clean.

### 🔴 Remaining for the full (6.8) capstone `sibleySetup_is_coherent`
1. **edge cases (m=2 / n=2) = the relabels** — the generic branch needs `3≤|xBaseBlock Zc|` (for
   χ₂,χ₃) and `3≤|Y|`.  When |xBaseBlock|=2 or |Y|=2, relabel (2-elt sign-swap `IsCoherent` ctor,
   template `retarget` S07:2987–3360).  Still the structural bottleneck; could also be handled by an
   honest case split if the FT groups always satisfy m,n≥3 (CHECK Peterfalvi — likely not, hence the
   relabel).
2. **the anchor/`a` existence + capstone wiring**: pick χ₁∈xBaseBlock, get `a` (χ₁(1)=a|W₁| from the
   source degree), χ₂,χ₃ distinct (needs `3≤|xBaseBlock|`), η₁∈Y; feed
   `coherentXunionYset_centralCommutator_diagonal_of_frobenius`; then **X(Zc)∪Y coherent + L4
   `false_of_coherentXunionYset_of_not_coherentS` ⟹ S coherent** (the (6.8.3) extension); wire into
   `sibleySetup_is_coherent` (the S08 sole sorry), with the case split (A)/(B).
3. **CertainType case (B)** (mmd (6.8.2), `Z=W₂`, (6.8.2.1)/(6.8.2.2)/(6.8.2.3)) — unplanned.

**Next session:** the anchor-existence + capstone wiring (2) under explicit `3≤|xBaseBlock|, 3≤|Y|`,
to connect the generic branch to `sibleySetup_is_coherent`; then the relabels (1); then (B).

### Key API (session 6 cont.³)
- `coherentXunionYset_centralCommutator_diagonal_of_frobenius (hyp)(hF)(hHnonab)(hp)(hp3)(hHp)
  (hη₁)(hχ₁base:χ₁∈xBaseBlock Zc)(hχ₂)(hne₂)(hχ₃)(hne₃₁)(hne₃₂)(ha:χ₁ 1=a·|W₁|)(hdeg2)(hdeg3)
  (hm3:3≤|Y|)` : `IsCoherent hyp.tau (Xset Zc ∪ Yset) A`.
- `hgen_withDiagonal_of_frobenius (hyp)(hF)(hp)(hHp)(hη₁)(hχ₁base)(ha)` : the hgen containment.
- `exists_charValue_one_eq_mul_xBaseBlock_anchor (hyp)(hF)(hp)(hHp)(hχX)(hχ₁base)` : `∃d:ℕ,0<d∧χ(1)=d·χ₁(1)`.
- `IntegralCharacterMap = ClassFunction →ₗ[ℤ] ClassFunction` (ℤ-linear; `map_sub`/`map_nsmul`).

## 2026-06-08 (session 6 cont.⁴): (6.8) capstone case A assembled to S-coherence (2 more commits, axiom-clean)

The generic Frobenius branch now reaches **S-coherence** end-to-end.  All leaf-green (3467) +
axiom-clean.  Commits:

- ✅ **case A with anchors** `9c90c508`: `nonempty_coherent_S_caseA_of_anchors_of_frobenius` —
  generic branch (`coherentXunionYset_centralCommutator_diagonal_of_frobenius`, X(Zc)∪Y coherent) +
  L4 `false_of_coherentXunionYset_of_not_coherentS` ((6.8.3) extension) ⟹ `Nonempty (IsCoherent S)`.
  (`by_contra hncoh; exact L4 ⟨generic branch⟩ hncoh`.)
- ✅✅ **case A from cardinality** `5a1331a4`: `nonempty_coherent_S_caseA_of_card_of_frobenius` —
  from `3≤|xBaseBlock Zc|` + `3≤|Y|`, **`S` is coherent**.  Discharges the anchors: 3 distinct
  base-block anchors (ncard_diff/ncard_pair + `exists_ne_of_one_lt_ncard`), equal degree
  (`xBaseBlock_degree_re_eq` + nat-degree reality), `χ₁(1)=a·|W₁|`
  (`sMember_charValue_one_eq_mul_anchor` vs a degree-|W₁| Y-anchor).

**⟹ the (6.8) Frobenius branch is COMPLETE from cardinality hypotheses to S-coherence** (generic
m,n≥3).  The L4 (6.8.3) bridge was already landed; this session connected it to the generic branch.

### 🔴 Remaining for the full (6.8) capstone `sibleySetup_is_coherent` (S08 sole sorry, ~10954)
1. **drop the `3≤|xBaseBlock|, 3≤|Y|` hypotheses (m=2/n=2 relabels)** — the structural bottleneck.
   The generic branch needs 3 anchors + 3 Y-members; when |xBaseBlock|=2 or |Y|=2, relabel (2-elt
   sign-swap `IsCoherent` ctor, template `retarget` S07:2987–3360).  ⚠ CHECK whether FT minimal-simple
   groups can have |xBaseBlock|=2 or |Y|=2 — if always ≥3, an honest cardinality lemma suffices and the
   relabels are unnecessary.  **This is the key open question for closing case A.**
2. **CertainType case (B)** (mmd (6.8.2), `Z=W₂`, (6.8.2.1)/(6.8.2.2)/(6.8.2.3)) — unplanned.
3. **wiring into `sibleySetup_is_coherent`**: restructure the capstone's `by_cases Xset ⁅H,H⁆ = ∅`
   into the `hyp.cases` split (Frobenius / CertainType); in the Frobenius case derive `hHnonab` (X
   nonempty ⟹ H non-abelian) + p-group data (hp/hp3/hHp from (6.5)) + the cardinality (1), then
   `nonempty_coherent_S_caseA_of_card_of_frobenius |>.some`.

**Next session:** resolve (1) — determine if |xBaseBlock|,|Y|≥3 always holds for FT groups (Peterfalvi
text / (6.5) p-group structure); if so, the cardinality lemma closes case A with no relabels.  Then (3)
wiring + (2) case B.

### Key API (session 6 cont.⁴)
- `nonempty_coherent_S_caseA_of_card_of_frobenius (hyp)(hF)(hHnonab)(hp)(hp3)(hHp)(h3X:3≤|xBaseBlock
  Zc|)(h3Y:3≤|Y|)` : `Nonempty (IsCoherent hyp.tau hyp.S A)`.
- `nonempty_coherent_S_caseA_of_anchors_of_frobenius (… anchors …)` : same, with explicit anchors.
- `false_of_coherentXunionYset_of_not_coherentS` (S08:6564, LANDED): X(cc)∪Y coh + ¬S coh ⟹ False.
- `Set.ncard_diff`/`Set.ncard_pair`/`Set.exists_ne_of_one_lt_ncard`/`Set.nonempty_of_ncard_ne_zero`
  (3-distinct selection); `characterDegree_def : characterDegree χ = χ 1`.

## 2026-06-08 (session 6 cont.⁵): cardinality question RESOLVED — relabels are genuinely needed (mmd-confirmed)

**KEY FINDING (resolves the session-6-cont.⁴ open question):** the `m = 2` / `n = 2` edge cases DO
occur in (6.8), so `3 ≤ |Y|` / `3 ≤ |xBaseBlock|` are **FALSE in general** — the relabels are
unavoidable.  Evidence:
- **mmd 04.8 (6.8.1)** explicitly contains both relabels: "_The second case reduces to the first on
  replacing `η₁^{τ₁}` and `η₂^{τ₁}` by `−η₂^{τ₁}` and `−η₁^{τ₁}`_" (`m = 2`), and "_If `n = 2`, we may
  assume `X = χ₁^{τ₂}`, possibly on replacing `χ₁^{τ₂}` and `χ₂^{τ₂}` by `−χ₂^{τ₂}` and `−χ₁^{τ₂}`_".
- **Arithmetic:** `Y = S(H′)` = degree-`|W₁|` members = `W₁`-orbits on nontrivial linear chars of `H`;
  `W₁` acts FPF ⟹ `|Y| = (|H/H′|−1)/|W₁|`, which can be `2` (e.g. `p=3`, `|H/H′|=3`, `|W₁|=1`).  Only
  `2 ≤ |Y|` (`two_le_Yset_ncard`) and `2 ≤ |xBaseBlock|` (`two_le_xBaseBlock_ncard`) hold in general.

**⟹ closing case A requires the relabels** (the `nonempty_coherent_S_caseA_of_card_of_frobenius`'s
`3≤` hypotheses cannot be discharged unconditionally).

### Relabel plan (the structural bottleneck — multi-piece refactor)
The relabel = choosing a **re-signed coherence witness**.  Concretely (mmd: `τ₁`/`τ₂` are "_an
isometry from ℤ[Y]/ℤ[X] coinciding with τ on ℤ[·,L^#]_"; the relabel flips signs on 2 members):
1. **relabeled witness via `coherentEqualDegree` (S07:3529)** — for `Y` (`m=2`): apply
   `coherentEqualDegree` with source `χ = ![η₁,η₂]` and **flipped target** `X' = ![−η₂^{τ₁},−η₁^{τ₁}]`
   (`η^{τ₁} = coherentYset.extension`).  `himg`: `τ(η₂−η₁) = X'₁−X'₀ = η₂^{τ₁}−η₁^{τ₁}` ✓ (same
   supported difference); `horthX'`/`hXZ'` ✓ (signs square out).  Gives `IsCoherent τ {η₁,η₂} A` =
   relabeled `Y`-coherence (`range ![η₁,η₂] = Yset` via `Set.ncard_eq_two`).  Analogue for `X` (`n=2`).
2. **parameterized diagonal shell** — the S07 shell
   `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07:4442) takes `hX, hY` as
   **arbitrary** `IsCoherent` witnesses + `ν` + agreement; the Sibley wrapper
   `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` (S08:8928) HARD-CODES
   `hyp.coherentYset` / `Xset_centralCommutator_isCoherent`.  ⟹ need a **cY/cX-parameterized** Sibley
   shell, and the crux/hgen'/himg_ortho re-proven (or generalized) for the relabeled witness.  ⚠ the
   crux's step-4/5 (`crux_of_frobenius`) is stated for the FIXED extensions — for the edge case the
   sign-flipped witness makes the bad disjunct (`X=−χ₂^{τ₂}`, `bb=0`) into the good one.
3. **edge-case crux variants** — `m=2`: re-run step 4 with the flipped `cY'` ⟹ `bb=−a` (good).
   `n=2`: flipped `cX'` ⟹ `X=χ₁^{τ₂'}`.  Then the diagonal shell with `cX'/cY'` ⟹ `X∪Y` coherent.

### Other remaining (unchanged)
- **capstone redesign + wiring** `sibleySetup_is_coherent` (S08 sole sorry ~10954): the current
  `by_cases Xset ⁅H,H⁆ = ∅` is the OLD `Z=⁅H,H⁆` design; must restructure to the `Z=centralCommutator`
  redesign + `hyp.cases` (A)/(B) split, then in case A invoke the (relabel-complete) case-A result.
- **CertainType case (B)** (mmd (6.8.2), `Z=W₂`, (6.8.2.1)/(6.8.2.2)/(6.8.2.3)) — unplanned.

**Recommended next phase (fresh multi-session):** (1) relabeled-witness lemma via `coherentEqualDegree`
(self-contained, ~80 lines each for Y/X); (2) cX/cY-parameterized Sibley diagonal shell; (3) edge-case
crux variants; (4) capstone redesign + wiring; (5) case B.  The generic (m,n≥3) spine
(`coherentXunionYset_centralCommutator_diagonal_of_frobenius` → `nonempty_coherent_S_caseA_of_card`)
is the template the edge cases mirror.

## 2026-06-08 (session 7): relabel step (1) DONE — sign-swap witness `coherentEqualDegree_swap_neg` (S07, 1 commit, full build 3599, axiom-clean)

The relabel foundation is landed in `S07_Coherence.lean` (right after `coherentEqualDegree`), all three
`[propext, Classical.choice, Quot.sound]`:
- ✅ **`coherentEqualDegree_swap_neg`** — given a coherence witness `c` for an orthonormal **equal-degree**
  pair `{φ₀, φ₁}` (`⟨φ₀,φ₁⟩=0`, `⟨φ₀,φ₀⟩=⟨φ₁,φ₁⟩=1`, `φ₁(1)=φ₀(1)≠0`, `(φ₁−φ₀).support ⊆ A`, `1∉A`),
  produces `c' : IsCoherent τ {φ₀,φ₁} A` with **`c'.ext φ₀ = −c.ext φ₁`**, **`c'.ext φ₁ = −c.ext φ₀`**.
  Built via `coherentEqualDegree` with source `![φ₀,φ₁]`, target `![−c.ext φ₁, −c.ext φ₀]`; the swapped
  images stay orthonormal + ZIrr (signs square), and the supported diff is preserved
  (`τ(φ₁−φ₀)=c.ext φ₁−c.ext φ₀`) so `extends_on_supported` survives.
- ✅ helpers: `coherentEqualDegree_extension` (`.extension = coherentImageMap χ X`, `rfl`);
  `IsCoherent.extension_eqRec` (transport `.extension` across set-equality `▸`, `subst;rfl`).
- API gotchas (don't re-derive): both live in ambient ns `OddOrder.Peterfalvi.S07` (NOT inside
  `namespace IntegralCharacterMap`, which closes @ S07:3233) → need **`open IntegralCharacterMap in`** to
  see `coherentImageMap`/`coherentImageMap_apply_eq`. `inner_neg_left/right` are in **`ClassFunction`** ns.
  Fin-2 `∀ i j` orthonormality: **`Fin.forall_fin_two.mpr ⟨…⟩`** (NOT `fin_cases`, which leaves indices as
  `⟨1,⋯⟩` so `Matrix.cons_val_one` won't fire) + `simp only [Matrix.cons_val_zero/one, Fin.isValue,
  Fin.reduceEq, ↓reduceIte]`.

### 🔴 Remaining for the edge cases (the real work = relabel steps (2)/(3) = crux-spine parameterization)
**`coherentEqualDegree_swap_neg` alone does NOT close the edge** — the crux spine is hard-coded to the
FIXED witnesses, so the swapped `cY'`/`cX'` need their OWN crux.  mmd + code re-confirmed this session:
- **both edges are 2-elt equal-degree-WHOLE-SET swaps**: `Y=S(H′)` is all degree-`|W₁|` ⟹ `m=2` ⟹
  `Y={η₁,η₂}`; for `n=2`, `X=S−S(Z)` is conj-closed + no real char (|L| odd) ⟹ `|X|` even ⟹ `|X|=2` is a
  **conjugate pair** `{χ,χ̄}`, EQUAL degree.  So `coherentEqualDegree_swap_neg` applies to BOTH (each is
  the whole equal-degree set).  ⚠ swap preserves `extends_on_supported` ONLY at equal degree (`d=1`); fine
  here since both edges are equal-degree pairs.
- **crux spine is cY/cX-parameterizable (verified by reading `coeff_eq_neg_or_edge_of_frobenius` S08:10187)**:
  its cY-use is ONLY via generic `IsCoherent` fields (`extension_inner_eq`/`extends_on_supported` ⟹
  injectivity/orthonormality of `cY.ext` on `Y`) + **witness-INDEPENDENT** τ-lemmas
  (`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius` = `⟨v,(η−η₁)^τ⟩=a`, `inner_self_tau_scaledDiff` =
  `‖v‖²=1+a²`; `v=hyp.tau(χ₁−aη₁)` is τ, not cY) + Bessel/arith.  The deepest cY-dep is **step-3 `a∣bb`**
  (`dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius`, the (6.7)/reg-char `b≡0` argument): applied to
  `cY.ext η₁` "const on Z^#"; for `cY'`, `cY'.ext η₁ = −cY.ext η₂` is also const on Z^# (same arg), so it
  generalizes — but the lemma is stated for `coherentYset`, so threading cY through is required.
- **m=2 mechanics**: step-4 dichotomy gives `⟨v,cY.ext η₁⟩=−a (good) ∨ (m=2 ∧ =0 (bad))`.  In bad,
  `⟨v,cY.ext η₂⟩=a` (the η-part is `a·cY.ext η₂`), so `cY'.ext η₁=−cY.ext η₂` ⟹ `⟨v,cY'.ext η₁⟩=−a` (good).
  So: case-split; good→existing `crux_of_third_anchor` (needs n≥3 only, NOT |Y|≥3 — it takes hgood as hyp);
  bad→re-run with cY'.  **n=2 mechanics**: step-5 dichotomy `X=cX.ext χ₁ ∨ X=−cX.ext χ₂` lacks the 3rd
  anchor; `cX'.ext χ₁=−cX.ext χ₂` flips it to good.
- **PLAN for steps (2)/(3)** (the multi-lemma parameterization, ~6-7 lemmas, mechanical-but-large): thread
  `(cY : IsCoherent τ Yset A) (cX : IsCoherent τ (Xset Zc) A)` through `coeff_eq_neg_or_edge`,
  `orthogonal_normOne_tau_scaledDiff_add_extension`, `inner_extension_Xset_sub_eq_neg_one`,
  `extension_eq_or_eq_neg`, `crux_of_third_anchor`, `inner_extension_Xset_centralCommutator_Yset_eq_zero`
  (himg_ortho), replacing `hyp.coherentYset`/`Xset_centralCommutator_isCoherent` by cY/cX.  Generic case
  re-plugs the fixed witnesses; edges plug swapped witnesses.  Then a cX/cY-param diagonal capstone
  (`coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` S08:9018 hard-codes them) +
  case-split on `2≤|xBaseBlock|`/`2≤|Y|` into generic (≥3) + edge (=2, swap).  Step-5 isometry value
  `inner_tau_scaledDiff_tau_Xset_diff` (S08:10427) is already witness-independent — no change.

## 2026-06-08 (session 7 cont.): spine parameterization + general diagonal capstone DONE; KEY degree-ratio finding (3 more commits, full build 3557 + AxiomsCheck OK, all axiom-clean)

Relabel steps (1)+(2) of the plan are now LANDED.  Commits on `b-peterfalvi`:
- ✅ **swap witness** `7108ab59` (session 7 above): `coherentEqualDegree_swap_neg` (S07).
- ✅ **spine parameterization** `e63822ec`: 6 `_general` lemmas over `cX : IsCoherent τ (Xset Zc) A`,
  `cY : IsCoherent τ Yset A` (the SHALLOW spine — NOT the deep step-3/step-4): himg_ortho
  (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general`), good-case-X
  (`orthogonal_normOne_tau_scaledDiff_add_extension_general`), step-5 relation
  (`inner_extension_Xset_sub_eq_neg_one_general`), dichotomy (`extension_eq_or_eq_neg_general`),
  crux (`crux_of_third_anchor_general`), L3 shell
  (`coherentXunionYset_centralCommutator_of_glued_withDiagonal_general`).  Each fixed `_of_frobenius`
  is now a thin specialization (passes fixed witnesses) → generic chain + S09 UNCHANGED.  Mechanism:
  `set hXc := cX` alias / replace `hyp.coherentYset → cY` (proofs use only generic IsCoherent fields +
  witness-independent τ-lemmas, so they transfer verbatim).
- ✅ **general diagonal capstone** `35e55bc8`: `coherentXunionYset_centralCommutator_diagonal_general
  (hyp)(hF)(hp)(hHp)(cX)(cY)(hη₁)(hχ₁base)(ha)(hcrux : τ(χ₁−aη₁) = cX χ₁ − a·cY η₁)` ⟹ `X(Zc)∪Y`
  coherent.  **This is the SHARED interface** for the generic case AND both edges — they differ only
  in how `hcrux` is produced for the chosen (possibly swapped) witnesses.  Generic
  `..._diagonal_of_frobenius` now delegates to it (fixed witnesses + `crux_of_frobenius`).

### 🔑 KEY FINDING (don't re-derive): the X-relabel needs a DEGREE-RATIO exclusion, not just a swap
The session-6-cont.⁵ relabel plan was INCOMPLETE.  Re-examined the swap's validity:
- **The 2-element sign-swap `cX'` is a valid `IsCoherent` witness ONLY when `|X(Zc)| = 2`** (the whole
  set).  Proof: `cX'` differs from `cX` on `χ₁,χ₂` (the swapped pair); for a supported
  `φ = ∑cᵢχᵢ ∈ ℤ[X,A]`, `cX' φ − cX φ = −(c₁+c₂)(cX χ₁ + cX χ₂)`, which is `0` (so `extends_on_supported`
  survives) **iff `c₁+c₂ = 0`**.  With higher-degree members present, a supported combo like
  `χ₁+χ₂−χ'` (`χ'(1)=2·χ₁(1)`) has `c₁+c₂=2≠0` → swap BREAKS `extends_on_supported`.  So the X-swap
  is invalid once `|X(Zc)|>2`.  (Y-swap is fine: `Y` is all equal degree, `|Y|=2` ⟹ whole set.)
- ⟹ the boundary is **`|X(Zc)|` (not `|xBaseBlock|`)**: `|X(Zc)|=2` ⟹ `X={χ,χ̄}` conj pair (|L| odd,
  no real char ⟹ |X| even) ⟹ equal degree ⟹ swap OK.  But **`|xBaseBlock|=2 ∧ |X(Zc)|≥4` is a real
  case** (one min-degree pair + a higher pair) where NEITHER the equal-degree generic (needs
  `|xBaseBlock|≥3`) NOR the swap (needs `|X|=2`) applies.
- **Fix = Peterfalvi's actual argument: a DEGREE-RATIO third anchor.**  His `n` is `|X|`, and the
  exclusion uses `(χ₃−d₃χ₁)^τ` for ANY third member `χ₃` (`d₃ = χ₃(1)/χ₁(1) ∈ ℕ`), needing only
  `|X(Zc)|≥3`.  In the right disjunct `X=−cX χ₂`: the relation
  `⟨X,cX χ₃⟩ − d₃·⟨X,cX χ₁⟩ = −d₃` becomes `0 − d₃·0 = −d₃` ⟹ `d₃=0`, contra (`d₃>0`).  So a
  degree-ratio exclusion covers `|X(Zc)|≥3` uniformly; the swap is needed ONLY for `|X(Zc)|=2`.

### 🔴 Remaining edge logic (precise, all feeding `coherentXunionYset_centralCommutator_diagonal_general`)
- **E1 — degree-ratio crux `crux_general_of_higher_anchor (cX,cY,χ₁∈xBaseBlock,χ₂ equal,χ₃ ANY,hgood)`
  ⟹ crux** (closes `|xBaseBlock|=2 ∧ |X|≥3`).  Needs: (a) degree-ratio isometry value
  `⟨τ(χ₁−aη₁), τ(χ₃−d₃•χ₁)⟩ = −d₃` (mirror `inner_tau_scaledDiff_tau_Xset_diff_of_frobenius` S08:10492
  with `d₃` from `exists_charValue_one_eq_mul_xBaseBlock_anchor`, `χ₃−d₃•χ₁` supported via
  `sMember_scaledDiffSupport_of_charValue_eq`); (b) degree-ratio relation
  `⟨X,cX χ₃⟩ − d₃·⟨X,cX χ₁⟩ = −d₃` (mirror `inner_extension_Xset_sub_eq_neg_one_general`); (c) the
  exclusion + `extension_eq_or_eq_neg_general` dichotomy.  ~3 lemmas, ~150 lines.
- **E2 — m=2 hgood selection.**  Step-4 dichotomy `coeff_eq_neg_or_edge_of_frobenius` (FIXED cY, S08
  ~10232): `⟨v,cY η₁⟩=−a (good) ∨ (|Y|=2 ∧ =0 (bad))`.  good ⟹ `cY*=coherentYset`, hgood.  bad ⟹
  `|Y|=2` ⟹ `Y={η₁,η₂}`, `cY'=coherentEqualDegree_swap_neg` (transport `{η₁,η₂}→Yset`), hgood for cY'
  via `⟨v,cY' η₁⟩=⟨v,−cY η₂⟩=−(⟨v,cY η₁⟩+a)=−a` (the `⟨v,cY η₂⟩=⟨v,cY η₁⟩+a` from
  `inner_tau_scaledDiff_tau_Yset_diff` + extends_on_supported).
- **E3 — |X(Zc)|=2 relabel.**  `X={χ₁,χ₂}` conj pair; `extension_eq_or_eq_neg_general (cX,cY*)`:
  left ⟹ crux for `cX`; right (`X=−cX χ₂`) ⟹ `cX'=swap` (valid, |X|=2 whole set), `cX' χ₁=−cX χ₂=X` ⟹
  crux for `cX'`.
- **E4 — master edge lemma** under `2≤|xBaseBlock|`, `2≤|Y|` (always true): pick χ₁,χ₂∈xBaseBlock, η₁;
  E2 → (cY*,hgood); then `by_cases |X(Zc)|≥3`: E1 (cX*=cX) ‖ E3 (|X|=2, cX*∈{cX,cX'}); feed
  `..._diagonal_general (cX*,cY*,hcrux)` ⟹ X∪Y coherent → L4 → S coherent.
- **wiring** into `sibleySetup_is_coherent` (S08 sole sorry): restructure `by_cases Xset⁅H,H⁆=∅` →
  `hyp.cases` (A)/(B); case A derive hHnonab(X≠∅)+p-data((6.5))+`2≤` cards, invoke E4; case B = (6.8.2)
  unplanned.

**Recommended next session:** E1 (degree-ratio crux, the gating piece — mirror the equal-degree
isometry/relation lemmas with `d₃`), then E2/E3 (relabel selections, consume
`coherentEqualDegree_swap_neg`), then E4 + wiring.  ALL feed the landed
`coherentXunionYset_centralCommutator_diagonal_general`.  **Don't re-grind the spine
parameterization or the swap witness — landed + axiom-clean.**

## 2026-06-08 (session 7 cont.²): edge logic E1–E4 COMPLETE — (6.8) Frobenius case (A) UNCONDITIONAL (4 more commits, full AxiomsCheck 3557 green, all axiom-clean)

The entire edge-case relabel programme is landed; **`nonempty_coherent_S_caseA_of_frobenius` proves
`S` coherent in the Frobenius / case-(A) branch with NO `3 ≤` cardinality hypotheses** (the `m = 2`
/ `n = 2` edge relabels are handled internally).  Commits on `b-peterfalvi`, each axiom-clean
`[propext, Classical.choice, Quot.sound]`:

- ✅ **E1** `143ce5b7` — degree-ratio crux closing the `|xBaseBlock| = 2 ∧ |X(Zc)| ≥ 3` gap:
  `inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius` (`⟨(χ₁−aη₁)^τ,(χ₃−d·χ₁)^τ⟩ = −d`) +
  `inner_extension_Xset_scaledSub_eq_neg_general` (relation) + `crux_general_of_higher_anchor`
  (good case + dichotomy + degree-ratio exclusion of the right disjunct by ANY third member χ₃:
  `X = −cX χ₂ ⟹ 0 = −d`, impossible since `d > 0`).  Covers `|X(Zc)| ≥ 3` uniformly.
- ✅ **E2** `bed633a0` — `exists_Ycoherence_hgood_of_frobenius`: `∃ cY, ⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a`
  (good `cY`).  `|Y| ≥ 3` → coherentYset; `|Y| = 2` bad → `cY'` = `coherentEqualDegree_swap_neg`
  (η₁ ↦ −η₂^{τ₁}), hgood via `⟨v, cY η₂⟩ = ⟨v, cY η₁⟩ + a = a`.
- ✅ **E3** `36c184c4` — `exists_Xcoherence_crux_of_card_two_of_frobenius`: when `X(Zc) = {χ₁,χ₂}`,
  `∃ cX,` crux.  Dichotomy left → `cX = cX₀`; right (`X = −cX₀ χ₂`) → `cX'` = swap (valid since
  `|X| = 2` whole set), `cX' χ₁ = −cX₀ χ₂ = X`.
- ✅✅ **E4** `fd10b360` — `nonempty_coherent_S_caseA_of_frobenius` (UNCONDITIONAL).  `2≤|xBaseBlock|`
  (`two_le_xBaseBlock_ncard`) + `2≤|Y|` (`two_le_Yset_ncard`) → 2 base-block anchors + a + η₁ + hdeg2;
  E2 → (cY, hgood); `by_cases 3≤|X(Zc)|` → E1 (third anchor) ‖ E3 (`|X|=2`); crux →
  `coherentXunionYset_centralCommutator_diagonal_general` (X(Zc)∪Y coherent) → L4
  `false_of_coherentXunionYset_of_not_coherentS` → `S` coherent.  ⚠ Type-data from the E2/E3
  existentials extracted via **`.choose`** (`Exists` over `IsCoherent` cannot eliminate into the
  Type-valued assembly — `obtain` fails with `Exists.casesOn can only eliminate into Prop`).

**⟹ (6.8) case (A) is fully discharged, sorry-free + axiom-clean.**

### 🔴 Remaining for the full (6.8) capstone `sibleySetup_is_coherent` (S08 sole sorry)
1. **CertainType case (B)** (mmd (6.8.2): `Z = W₂`, (6.8.2.1) `η^{τ₁}` const on `Z^#` /
   (6.8.2.2) `Ind_Z φ` decomposition / (6.8.2.3) per-χ `X₁ − aY`) — **UNPLANNED**, separate deep
   character theory (the `w₂`-prime / `(4.6)` machinery).  This is the sole remaining blocker.
2. **final wiring** into `sibleySetup_is_coherent` (currently the OLD `by_cases Xset ⁅H,H⁆ = ∅`
   design): restructure to `hyp.cases` (A)/(B); case A = `nonempty_coherent_S_caseA_of_frobenius
   |>.some` (DONE), case B from (1).  Deferred until (1) is ready (else it commits a case-B sorry).
   Also derive `hHnonab` (X-nonempty ⟹ H non-abelian) + p-group data (hp/hp3/hHp from (6.5)) at the
   wiring site.

**Recommended next phase:** CertainType case (B) — a fresh multi-session piece (plan from scratch,
mmd (6.8.2)).  Case (A) is the template (Z central, glue via diagonal shell), but (B) uses `Z = W₂`
and the `w₂`-prime structure.  Then the trivial final wiring.  **Don't re-grind case A / the edge
relabels — landed + axiom-clean.**

## 2026-06-08 (session 8): CertainType (c2) branch — RECON + dependency-audited PLAN + CB1 foundation

Resumed the B lane.  (c1) Frobenius / case-(A) is fully discharged (`nonempty_coherent_S_caseA_of_frobenius`,
session 7 cont.²).  This session reconnoiters and PLANS the remaining `hyp.cases.inr` (CertainType /
(c2)) branch — the note's "sole remaining blocker" — and lands the foundational leaf CB1.

### 🔑 KEY FINDINGS (don't re-derive)

**F1. The (c2) branch math-splits on `Z(H) ⊓ W₂`; `|W₂|` prime makes it a clean dichotomy.**
`cases.inr` gives `cert : S06.CertainTypeHypothesis (sharpImage H) L` with `cert.K = H`,
`cert.W2 ≤ ⁅H,H⁆`, `(Nat.card cert.W2).Prime`, `Nat.Coprime |H| |W₁|`.  The mmd (A)/(B) split
(04.8 L152-154) is `Z(H) ⊓ W₂ =? 1`:
- math-(A) `Z(H)∩W₂ = 1`: `Z := centralCommutator = Z(H)∩H'`; uses (6.8.1).
- math-(B) `Z(H)∩W₂ ≠ 1` ⟹ (prime) `W₂ ⊆ Z(H)`: `Z := W₂ = cert.W2`; uses (6.8.2).
`W₂.subgroupOf H` has prime card, so `center ⊓ W₂sub ∈ {⊥, W₂sub}` (`eq_bot_or_eq_of_le_of_card_prime`).

**F2. Prerequisites MOSTLY EXIST (the note's "unplanned/deep" framing was too pessimistic).**
- (6.8.2.1) `Z^#`-constancy: ✅ `IsCoherent.extension_constant_on_sharp_of_prime` (S07_CoherenceGalois:424),
  GENERIC for prime-order Z, (1.9) produced internally — just needs wiring.
- [Is] 2.27 central restriction: ✅ `IsIrreducibleCharacter.exists_central_linear_restriction`
  (SchurCenterBound:241) — docstring literally says "behind (6.8.2.3)".
- (4.1): ✅ `pairwise_inner_eq_zero_of_orthogonal_signedDifference` (S08:204).
- (5.9.a): ✅ `IsCoherent.extension_mapRingEquiv_comm` (S07_CoherenceGalois:109).
- (6.7): ✅ `peterfalvi_67_of_odd` (SylowTICongruence:140); the S08 adapter (9797) is
  centralCommutator+Frobenius-hardcoded → needs a W₂ analogue.
- (5.6): ✅ `coherentDegreeSumBound_of_not_coherent` (S08:2419) + `exists_coherentBreakPair` (S08:995).
- [Is] 2.30: ✅ `exists_degree_sq_le_index` (SchurCenterBound:193).
- (4.5) "S, S(Z) have w₂−1 reducible chars": NOT formalized, but **BYPASSED** — the formalization
  proves `X⊆Irr` per-member via `inertia_eq_H_of_c2_caseA` (S08:3716), not the global count.

**F3. The case-A/c1 machinery's TRUE hypothesis is "W₁ FPF on Z" + coprimality, NOT "Frobenius".**
In c2+math(A), `W₁` DOES act FPF on `Zc=Z(H)∩H'`: `C_{Zc}(w) = Zc ∩ C_H(w) = Zc ∩ W₂ ⊆ Z(H)∩W₂ = 1`.
So (c1) ∪ (c2+math-A) UNIFY under FPF-on-Z.  **Low-level case-A pieces are ALREADY FPF-generic**:
`isIrreducibleCharacter_of_mem_Xset_caseA` (5177, takes hZcentral/hZnorm/hZfpf), `inertia_eq_H_of_c2_caseA`
(3716), `xBaseBlock_isCoherent_caseA` (7074).  **High-level assembly is Frobenius-wired** (needs
generalization to FPF): `Xset_centralCommutator_isCoherent_of_frobenius` (8764), the diagonal shell
`coherentXunionYset_centralCommutator_diagonal_general` (11287), L4
`false_of_coherentXunionYset_of_not_coherentS` (6564), `peterfalvi_67_centralCommutator` (9797),
`centralCommutator_card_subgroupOf_lower` (4043), capstones (11380/11405/11472).
Z-generic reusables: (6.6) consumer `...withCover_of_irreducible_X` (8583),
`false_of_centralCommutator_break_arith` (6286, pure arith), `xSum_le_two_psi` (6421, Z-param).

**F4. ⚠️ math-(B) does NOT reuse the case-A coherence architecture.**  In case B the X-members are NOT
all irreducible — `W₁` is NOT FPF on `W₂` (`C_L(w)⊓W₂ = W₂` via `cert.centralizer_W2`), so the inertia
`I_L(θ)` can exceed `H` and `Ind θ` can be reducible.  Hence "X coherent via (6.6) + Y coherent +
diagonal glue" FAILS.  (6.8.2) instead builds the `X∪Y` isometry τ₂ DIRECTLY via the §5 reflection
machinery `R(χ)` / Hypothesis (5.2) / (5.3)/(5.4.a,b)/(5.5) (mmd L214-222).  **OPEN RISK (investigate
at CB4 start): is the `R(χ)` reflection machinery formalized in S05/S07?** If not, CB4 is large.

### Layered plan (CertainType branch)
- **CB1 (foundation — ✅ THIS SESSION)**: `eq_bot_or_eq_of_le_of_card_prime` (general group theory) +
  `W2_subgroupOf_le_center_of_caseB` (the (6.6) centrality enabler at `Z=W₂`, analogue of
  `centralCommutator_subgroupOf_le_center`).  axiom-clean.
- **CB2a (c2+math-A FPF/irreducibility — ✅ THIS SESSION)**:
  `centralizer_inf_centralCommutator_eq_bot_of_c2_caseA` (`W₁` FPF on `Zc`: `C_L(w)⊓Zc=⊥` from the
  math-(A) hyp `Z(H)⊓W₂=1` + `cert.centralizer_W2`, lifted ↥H→↥L) +
  `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (the (c2) mirror of
  `isIrreducibleCharacter_of_mem_Xset_of_frobenius`: discharges hZH/hZcentral/hZnorm/hZfpf into the
  FPF-generic `isIrreducibleCharacter_of_mem_Xset_caseA`).  axiom-clean.
- **CB2b**: case-B `W₂ ◁ L` (H centralizes W₂ via centrality; W₁ normalizes via `centralizer_W2` +
  W₁ abelian/conjugation) — needed for `Xset W₂` in math-(B) (CB4).  Pending.
- **CB3 (c2+math-A)**: GENERALIZE the high-level case-A assembly (L2/L3/L4 + capstone) from `hF` to the
  FPF-on-Z hypotheses (`hZcentral`/`hZnorm`/`hZfpf` + coprimality).  Then both (c1) and (c2+math-A)
  instantiate it.  Largest "refactor" milestone; F3 low-level pieces already support it.
- **CB4 (math-B / 6.8.2)**: the §5-reflection construction of τ₂ (6.8.2.1 wire `extension_constant_on_sharp_of_prime`
  + 6.8.2.2 `Ind_Z φ` decomp via (6.7)+(1.5.b)+fpf-on-`H/Z` + 6.8.2.3 per-χ via [Is]2.27 + (5.4)).
  **🛑 VERDICT (session 8 CB4-feasibility investigation): BLOCKED on Peterfalvi §4 (certain-type
  structure theory), NOT near-term feasible.** The §5/§7 reflection machinery `R(χ)` itself IS
  formalized and 0-sorry — `OrthonormalCharacterImageFamily` (S07_Coherence:759), (5.4.a)/(5.4.b)
  norm bounds, (5.5), and the Dade producer `dadeOrthonormalCharacterImageFamily` (S07:5387).  BUT
  that producer **requires `χ : IrreducibleCharacter`**.  In case B the X-members `χ = Ind θ` can be
  **reducible** (W₁ is NOT FPF on `W₂` ⟹ `I_L(θ)` can exceed `H`), and `R(χ)` for reducible induced
  χ comes from **Peterfalvi (4.9)** (the `μ_j = ±δ_j ∑ ω_{ij}^σ` certain-type structure).  Per
  `notes/peterfalvi/s06_dade_certain_subgroup.md`: **(4.3)/(4.4)/(4.5)/(4.7)/(4.9)/(4.10) are ALL
  unformalized** (only the (4.6) `CertainTypeHypothesis` bundle exists), and (4.5) is itself blocked
  on **Brauer's permutation lemma** ([Is] 6.32, also unformalized → needs new `BrauerPermutation.lean`).
  Estimated ~18–22h of independent §4 work.  **⟹ CB4 is gated on the full §4 certain-type project**
  (which also unblocks §12/§13/§15 downstream).
  **⚠️ SUPERSEDED (2026-06-08 session 9, see `s06_dade_certain_subgroup.md` "session 9")**: this
  verdict is WRONG about Brauer — [Is] 6.32 IS fully formalized & 0-sorry (`BrauerPermutation.lean` /
  `BrauerPermutationUnconditional.lean` / `ConjugationBrauer.lean`). The real (and larger) bottleneck
  the verdict MISSED is **§5 (3.x) σ-isometry**, esp. the (3.5) χ_ij combinatorial construction —
  the §7 per-pair R(χ) producer (`dadeOrthonormalCharacterImageFamily`) does NOT subsume the global
  (3.2) σ. Corrected scope = §5 (3.x) + §6 (4.x) theorem bodies, ~30-40h, hard cores (3.5) & (4.3),
  Brauer-free. Dependency-ordered leaf plan + first leaf (3.3) in the s06 note.
- **CB5 (6.8.3 shared)**: generalize L4 `false_of_coherentXunionYset_of_not_coherentS` over Z; apply at
  `W₂`.  (5.6)-based; `xSum_le_two_psi`/`false_of_centralCommutator_break_arith` are already Z-param.
- **CB6 (wiring)**: restructure `sibleySetup_is_coherent` to `hyp.cases`; `inl`→case-A-frobenius (done);
  `inr`→`by_cases center⊓W₂sub=⊥` → CB3 (math-A) / CB4+CB5 (math-B).

### Scope honesty + CB4-feasibility VERDICT (session 8 conclusion)
The (c2) branch is comparable in size to the entire case-A effort (~7 sessions).  CB3 (FPF
generalization) is tractable and well-supported (F3).  **But CB4 (math-B) is confirmed BLOCKED on the
unformalized Peterfalvi §4 certain-type structure theory ((4.3)/(4.4)/(4.5)/(4.7)/(4.9)/(4.10) +
Brauer's permutation lemma [Is] 6.32; ~18–22h, see the CB4 verdict above and
`s06_dade_certain_subgroup.md`).**  Because the `inr`/CertainType branch of the capstone needs BOTH
math-A (CB3) AND math-B (CB4), **doing CB3 alone CANNOT close `sibleySetup_is_coherent`** — the
capstone stays blocked on §4 regardless.  This is full-Pf-scope completionism, **off the FT critical
path** (per the FT master roadmap — (6.8)/(7.10) are genuine but orphaned).

**⟹ Strategic fork (user's call):** (A) take on the Peterfalvi §4 certain-type project (unblocks CB4
*and* §12/§13/§15) — large but the true gate; (B) do CB3 (math-A) as partial, capstone-still-blocked
progress; (C) pause the (6.8) capstone (record blocked-on-§4) and redirect to the FT critical path
(BG §7–16 / the rep-theory keystone).  Recommendation: (A) if full-Pf completion is the goal and the
§4 investment is acceptable; (C) if FT-shortest-path progress is the priority.  CB1/CB2a stand as
landed, axiom-clean foundation either way.

## 2026-06-11 (session 27, b-peterfalvi): 経路逆算 RECON — case-A 完全 landed判明 + (4.9) 要否の真の crux 特定

監視レーンの一押し(「経路逆算せよ — (4.7)-(4.9) off-path なら skip して case-B 直行」)を受け、
capstone `sibleySetup_is_coherent` から逆算して全フロンティアを精査。**この note の上部 (2026-06-07
deep-dive) は stale** — その後 case-A は大幅前進していた。

### ✅ 判明: case-A (6.8.1 / Frobenius) は L1-L4 すべて sorry-free で landed
S08_CoherenceCore.lean は **sorry 0**。case-A の全 brick が存在:
- L1 `centralCommutator_*` (Zc=Z(H)∩H′ central facts) ✅
- L2 monolith `Xset_centralCommutator_isCoherent_of_frobenius` (S08:8691, **inline で hstepData 構築済**、
  hcover threading は `..._withCover_of_frobenius` variant で**既に解決**) ✅
- L3 ν-glue `coherentXunionYset_centralCommutator_of_glued_of_frobenius` (S08:8902) ✅
- L4 `false_of_coherentXunionYset_of_not_coherentS` (S08:6491) ✅
- `isPGroup_of_not_coherent` ✅ / `Xset_centralCommutator_nonempty` ✅
⟹ **capstone の Frobenius branch は landed lemma から組立可能**。唯一の sorry = S08_CoherenceTheorems:59
(`sibleySetup_is_coherent` の X-nonempty branch)、残ギャップ = **CertainType (case-B/6.8.2) branch のみ**。

### ✅ 判明: case-B が要する §1/§6 prerequisite は全て済 — (4.7)-(4.9) は教科書証明に非出現
mmd 04.8 (6.8.1)/(6.8.2) 全証明精読:
- **X⊆Irr L** (case c2): 「(1.6)+Theorem (4.5) で S,S(Z) 各 w₂−1 個 reducible ⟹ X⊆Irr L」。
  (4.5)=✅完了、(1.6) needed direction=`not_subsetCharacterKernel_of_not_induce`(S03:636)=✅完了。
  **X-members は全て既約** (reducible は S(Z) に入り X=S−S(Z) で相殺)。
- W₂ centrality `W2_subgroupOf_le_center_of_caseB` (S08:3850) ✅、inertia `inertia_eq_H_of_c2` ✅。
- (6.8.2.1)→(1.9)/(5.9.a)=T4✅; (6.8.2.2)→(6.7)=T3✅+(1.5.b); (6.8.2.3)→[Is]2.27=T5✅+R(χ)+(5.3/5.4/5.5)。

### 🔑🔑 真の crux (session 8 CB4 verdict と session 26 RECON の矛盾の決着)
**(6.8.2.3) は `R(χ_i)` を χ_i=Ind_H^L θ_i ∈ S に適用するが、これらは reducible になりうる**
(case B では W₁ が W₂ に FPF とは限らず I_L(θ_i)>H)。一方、形式化された §7 producer
`dadeOrthonormalCharacterImageFamily` (S07:5389) は **`χ : IrreducibleCharacter` 専用**。
⟹ **矛盾の真相**: 教科書 (6.8.2) は (4.9) を明示引用しない (session 26 RECON 正) が、**reducible
χ∈S の R(χ) を形式化するには「一般 R(reducible χ∈S)」か「(4.9) (certain-type structure
T(μ_j)=δ_k∑ω_ij^σ)」が要る** (session 8 CB4 の懸念は形式化レベルで妥当)。
**∴ 精査の結論: (6.8.2.3) の χ_i は実は既約 ⟹ (4.9) 不要 (RECON 正・CB4 誤)**:
(6.8.2.3) の χ_i=Ind_H^L θ_i は `Res_Z θ_i = a_i φ` (φ≠1_Z, [Is]2.27) ゆえ **Z⊄Ker θ_i** ⟹
([Is]2.21 = 1.6.a 逆で) Z⊄Ker(Ind θ_i) ⟹ **Ind θ_i ∈ X = {χ∈Irr L | Z⊄Ker χ} ⊆ Irr L ⟹ χ_i 既約**。
∴ R(χ_i) は既約専用 producer `dadeOrthonormalCharacterImageFamily` で供給でき、**(4.9) は不要**。
**session-8 CB4 verdict の「X-members χ=Ind θ は reducible ⟹ R に (4.9) 要」は誤り** — Z⊄Ker θ_i が
Ind θ_i を X(⊆Irr L) に押し込んで既約化する点を見落としていた。

### ▶▶ case-B 完遂の残務 (mirror case-A; (4.9) 不要・[Is]2.21 不要 = §1/§6 prerequisite 皆無)
**✅ [Is]2.21 は不要と確定 (前 entry の「prerequisite」claim を撤回)**: S08:265
`characterKernel_subset_of_isCharacter_of_inner_ne_zero` (genuine ψ の既約 constituent χ
[⟨ψ,χ⟩≠0] は g∈Ker ψ ⟹ g∈Ker χ) が**既に landed**で、X⊆Irr L はこれ経由でルート。S08:186-191
docstring が明示: 「両方向 (Res_H φ / Ind_K^L θ) は genuine character 経由ゆえ **[Is] Lemma 2.21 は
不要**」。⟹ **case-B 閉鎖に §1/§6 の新規 prerequisite は皆無、純粋に §8 Zc 機構のみ**。
- math-A/math-B split (CertainType 内): **math-A** (Z(H)⊓W₂=⊥) は **Zc=Z(H)∩H' で case-A 機構を再利用**
  (FPF 入力 `centralizer_inf_centralCommutator_eq_bot_of_c2_caseA` landed)、ただし case-A monolith
  `Xset_centralCommutator_isCoherent_of_frobenius` の `hF:IsFrobeniusGroup` を「W₁ FPF on Zc」へ一般化要
  (CB3); **math-B** (W₂⊆Z(H)) は **Z=W₂ 機構** (CB4, `W2_subgroupOf_le_center_of_caseB` landed)。
1. **CB3 (math-A)**: ✅✅ **次数平方和の c2 reworking 完了** (session 27 cont.³, 2 commits):
   `sum_re_sq_Xset_eq_of_irreducible_X` (33a1b7f6, B2 orbit-counting `sum_div_normSq_induce_kernelFilter_eq`
   [χ(1)²/‖χ‖² 形=reducible OK] + sum_sdiff + X-irr で X 側のみ (χ(1).re)² 変換) +
   `Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X` (6ec05402)。**⟹ monolith の全 hF 依存に c2/generic 版
   が揃った**: X⊆Irr=`isIrreducibleCharacter_of_mem_Xset_c2_caseA`/two_le=`two_le_xBaseBlock_ncard_of_irreducible_X`/
   degree-sum=`sum_re_sq_Xset_eq_of_irreducible_X`/nonempty=`..._of_irreducible_X`/index=`index_H_eq_card_W1`[generic]/
   coprime=`cert.card_coprime`/consumer=`Xset_isCoherent_from_..._withCover_of_irreducible_X`[generic, S08:8532]。
   **残 = monolith assembly のみ (機械的)**: `Xset_centralCommutator_isCoherent_of_frobenius` (S08:8861, ~200行)
   を copy → 署名を math-A hyps (cert/hK/hW1/hA: Z(H)⊓W₂=⊥) へ → `hX := isIrreducibleCharacter_of_mem_Xset_c2_caseA`
   を冒頭で確立 → 5 つの hF-use を上記 c2 版へ差し替え → consumer を generic 版へ。
2. **CB4 (math-B)**: Z=W₂ の monolith + 支持 lemma。⚠ W₂ の L-normality (Xset Z が要する Z⊴L) は
   要解決 (W₂=C_K(x) は一般に L-正規でない)。
3. case-B L3 τ₂ glue + L4 ((6.8.2)/(6.8.3))。
4. capstone assembly (`hyp.cases` split: Frobenius=landed brick / CertainType=math-A∧math-B)。

**⟹ 確定: case-B closure は genuine multi-session §8 work** (CB3 の hard core [次数平方和] は解除済み;
残 = CB3 monolith 機械的 assembly + CB4 [W₂-normality] + L3/L4 + capstone)。case-A が ~7
session を要した規模。**次セッション第一手 = CB3 monolith assembly** (上記 recipe; 全 piece landed)
※旧記述「X(Z) 次数平方和 c2 版」は session 27 cont.³ で完了 (reducible S-members
を分離して Irr 部分のみ (χ(1).re)² 化、reducible 部分は ⟨χ,χ⟩ 重み付き)。

**正本 = 本 session 27 entry (上部 2026-06-07 deep-dive は stale: case-A は landed)。**
**(4.7)-(4.9) は case-B 完全 off-path 確定 (監視レーン裁可と一致); §6 (4.x) は full-Pf scope の正当成果。**
**case-B の真の残務 = §8 Zc=W₂ branch (monolith+τ₂+L4, case-A mirror) + [Is]2.21。multi-session §8 work。**

## 2026-06-11 (session 28, b-peterfalvi): CB3 の L2 monolith COMPLETE — X(Zc) coherence for c2/math-A (1 commit, full build 3774 + AxiomsCheck 3622 緑、axiom-clean)

session 27 cont.³ の recipe「CB3 monolith assembly」を実施。**copy でなく generic core 化**で着地
(両 case が 1 つの core を instantiate; CB3 の「generalize して両者が instantiate」哲学に合致)。commit `1b7cd80a`:

### ✅ 着地 (S08_CoherenceCore、全 axiom-clean allowlist 3、AxiomsCheck 登録)
- **`mem_xSetFinset_iff_mem_Xset`** (bridge): `X=S−S(Z)` の Finset 形 (filter bot-ker `.image Ind` `\`
  filter Z-ker `.image Ind`) ↔ Set 形 `Xset Z`。monolith inline の hmemXF を generic Z で抽出。
  c2 の Set 形 irreducibility を Finset 形 nonempty 補題へ橋渡しするため。
- **`Xset_centralCommutator_isCoherent_of_irreducible_X`** (generic L2 core): Frobenius monolith
  (旧 8861) を `hX`/`hXne`/`hidxp` パラメトリック化。6 つの hF-use を差し替え (consumer→generic
  `…withCover_of_irreducible_X`、irr→hX、two_le→`…_of_irreducible_X`、nonempty→hXne param、
  degree-sum→`sum_re_sq_Xset_eq_of_irreducible_X` + bridge、hidxp→param)。**Z=Zc は両 case 共通**
  (math-A も Zc=Z(H)∩H′ central を使う; W₁ FPF on Zc は math-A 仮説 Z(H)⊓W₂=⊥ から)。
- **`Xset_centralCommutator_isCoherent_of_frobenius`**: 上記 generic への薄い delegate へ refactor
  (hX←`isIrreducibleCharacter_of_mem_Xset_of_frobenius`、hidxp←`hF.coprime_card_kernel_complement`)。
  **downstream defeq 保存を full build で検証** (consumer は同一引数で呼ばれ `.extension` 不変; S09 等緑)。
- **`Xset_centralCommutator_isCoherent_of_c2_caseA`** (CB3 deliverable): math-A `Z(H)⊓W₂=⊥` で
  hX←`isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA`、hXne←`Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X`
  (hZbot は hHnonab→`centralCommutator_ne_bot`; Form-A は bridge 経由)、hidxp←`cert.card_coprime`
  (`rw [hK] at hcop`) + `index_H_eq_card_W1`。署名 = `{cert}(hK:cert.K=H)(hW1:cert.W1=hyp.W1)(hA)(hHnonab){p}(hp)(hp3)(hHp)`。

### 🔑 罠 (再調査しない)
- delegate に `haveI : Fact p.Prime := ⟨hp⟩` 必須 (`hHp.exists_card_eq` が要求; 削ると instance 不足)。
- `hK ▸ cert.card_coprime` は motive 計算失敗 → `have hcop := cert.card_coprime; rw [hK] at hcop` で回避。
- 巨大 body の prefix-replace 後の残骸は `sed -i '<start>,<end>d'` で line-range 削除 (string-match は generic と
  body 重複で曖昧化)。

### ▶▶ 次 = CB3 の L3/L4 一般化 → CB4 (math-B) → CB6 wiring
- **CB3 残 (math-A 上位 assembly)**: L2 (X(Zc) coherence) は landed。**L3 glue
  `coherentXunionYset_centralCommutator_of_glued_of_frobenius` (S08:9176) + L4
  `false_of_coherentXunionYset_of_not_coherentS` (S08:6661) + capstone
  `nonempty_coherent_S_caseA_of_frobenius` (S08:11673) は全て hF 固有**で要一般化。
  **🛑 L4 は機械的でない (session 28 survey 結果)**: L4 は break-pair `ψ∈S` の**既約性**を実質使用
  (`isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS` @ ~6703 で ψ を Ind θ と分解)。だが **c2 では
  W₁ は H 全体に FPF でない** (`cert.centralizer_W2`: w∈W₁^# で C_L(w)⊓H=W₂≠1) ⟹ **S-members は既約とは
  限らない** (reducible Ind θ は I_L(θ)>H 由来; これらは S(Z) に入り X=S−S(Z) からは除かれるが、L4 の
  break-pair ψ は S 全体から来るので reducible でありうる)。∴ c2 L4 は **reducible ψ を扱う別論法**が要る
  (X-members だけで break するか、(5.6) 評価を reducible ψ へ拡張するか — 要設計)。他の hF-use
  (`S_hasNoRealCharacters hF` @ ~6691 [|L| 奇 ⟹ no real char; hF 非依存化可能か?] / `xSum_le_two_psi hF` @ ~6715 /
  `centralCommutator_card_subgroupOf_lower hF hHnonab` @ ~6750) も要 c2 版。`_general` diagonal 変種 (9219/11488) は既存。
- **CB4 (math-B, Z=W₂)**: ⚠ 当 generic core は **Z=Zc 固定** (math-B の Z=W₂ には非適用; かつ math-B では
  W₁ が W₂ に FPF でない ⟹ X(W₂)⊆Irr は (4.5)/(1.6) 経由・FPF 不可)。math-B は X(Z) coherence でなく
  **§5/§7 reflection で τ₂ を直接構成** (session 27 RECON: χ_i 既約 ⟹ `dadeOrthonormalCharacterImageFamily`
  供給可・(4.9) 不要)。W₂ の L-normality も要解決。CB4 は CB3 と別構造。
- **CB6 (wiring)**: `sibleySetup_is_coherent` (S08_CoherenceTheorems:59 sole sorry) を `hyp.cases` split へ
  (inl=Frobenius landed brick / inr=`by_cases center⊓W₂sub=⊥` → math-A (CB3) / math-B (CB4))。

**正本 = 本 session 28 entry。CB3-L2 done; 残 = CB3-L3/L4 一般化 (hF→c2) + CB4 (math-B τ₂, 別構造) + CB6 wiring。**

## 2026-06-11 (session 28 cont.²): CB5 (6.8.3) の真相精査 + break-pair foundation landed (1 commit, axiom-clean)

**🔑🔑 教科書 (6.8.3) 精読 (mmd 04.8 L226-244) で L4 障害の本質を確定**: (6.8.3) は case (A)/(B)
**共有**の S-coherence 最終ステップ。証明は **norm-weighted sum `∑_{χ∈S₁} χ(1)²/‖χ‖²`** を使い
(L230)、ψ は「源 θ∈Irr H から induce される」だけで十分 (L236 "induced from an irreducible
character of H" = **源 θ の既約性 = S の定義から自動**; ψ 自身の既約性は不要)。最終算術のみ case 差:
case(A) `|Z|−1≥2|W₁|` (W₁ FPF on Z), case(B) `|H:Z|≥(2|W₁|+1)²` (W₁ FPF on H/H' & H'/Z)。

### ✅ landed (commit `6994ad08`, CB5 combinatorial foundation)
formalization の障害 = break-pair 機構の **irreducibility 仮説のみ** (教科書には無い over-strong)。除去:
- **`exists_conjugatePairCover_general`**: `hXirr` 除去。survey 結果 = irreducibility は **line 737 の
  `hpairχ` (IrreducibleCharacter packaging) 1 箇所のみ**で使用、conjugate involution `cidx`/cover/
  disjoint/monotone は `hXreal`+`hXconj` のみ。出力を ClassFunction pair + `(pair i).2=(pair i).1.conj` 直接出力に。
- **`exists_coherentBreakPair_general`**: `hSbirr` 除去 (上記 cover 上に mirror)。ψ∈Sb は reducible OK。

### 🔴 CB5 残 = norm-weighted degree-sum 解析 (deep analytical core)
break-pair の **combinatorial** 部は済。残る **analytical** 部 (degree-sum bound chain) は全て
`IrreducibleCharacter` orthonormal family ベースで、reducible S₁ に未対応:
- (5.6) `coherentDegreeSumBound_of_not_coherent` (S08:2450): 抽象 `χmem : ι → IrreducibleCharacter ↥L`
  orthonormal family でパラメタ化。
- `sMember_degreeSumBound_of_not_coherent` (S08:6065): `exists_sMemberOrthonormalFamily hF` で **S₁ を
  IrreducibleCharacter 列挙** (S₁⊆S 既約前提) → `∑ deg² ≤ 2a`。
- `sMember_degreeSqReBound` (6153) / `xSum_le_two_psi` (6451) → `false_of_coherentXunionYset` (6661)。
- **gap**: reducible S₁ では `∑_{χ∈S₁} χ(1)²/‖χ‖²` (norm-weighted) を扱う。X-sum 部 (`∑_X χ(1)²`, X⊆Irr)
  は既存 (`sum_re_sq_Xset_eq_of_irreducible_X`)、`∑_X ≤ ∑_{S₁}` (norm-weighted, X⊆S₁, 正項) は易。
  ⚠ S₁ の既約 sub-family (例 X) を (5.6) に渡すのは**不可** — (5.6) は family が S₁ の span を**生成**要
  (`hSgen`/`hgen` via `hcover`)、reducible S₁ では既約 member family で代替できない。

### ✅✅ DE-RISK (session 28 cont.²、再調査するな): norm-weighted 機構は **S07 に既存** — CB5 は再導出でなくルーティング
S08 `xAdjoinStep` (2261)/`coherentDegreeSumBound` (2450) は orthonormal (mc=1) 特殊化を使うが、**底層 S07
は完全 norm-weighted** (`mc i = ‖χ_i‖²`, member は reducible 可):
- **`S07.lambda_eq_zero_and_Z_eq_zero`** (S07:2184): (5.6.2) capstone、`mc i = ‖χ_i‖²` (line 2175 明記)、
  `hD : 2a < ∑ (rc i)²·mc i` (rc i = a_i/‖χ_i‖²)。Pythagoras + arith は mc 一般で成立。
- **`S07.dade_Y_collapse_of_family`** (S07:5769): Dade 版 collapse、`hdeg_c : 2a < ∑ (B.ratio i/mc i)²·mc i`。
- **`S07.CharacterPsiDecomposition.Y_collapse_of_family`** (S07:5059): `mc` パラメトリック、`hmc : ⟨B.chiFam i,
  B.chiFam i⟩ = mc i`。
- **`S07.DadeChainStep`** (S07:6237): S₁ を `famS` (**`famPairwise` = pairwise orthogonal、orthonormal 不要 →
  reducible member OK**) として扱う構造 + `advance` (6329)。
- **次手 (CB5 routing、multi-lemma だが re-derivation 不要)**: (1) S08 `xAdjoinStep_general`/(5.6)`_general`
  を `mc i = ‖χ_i‖²` で上記 S07 norm-weighted 経由に (mc=1 を一般 mc へ; ‖·‖² gram を hmemortho の代わりに) →
  (2) `sMember_degreeSumBound` の norm-weighted 版 (S₁ を `DadeChainStep.famS` pairwise-orthogonal で列挙、
  `exists_sMemberOrthonormalFamily` の代替) → (3) `xSum_le_two_psi_general` (X-sum は既存、∑_X≤∑_{S₁}) →
  (4) `false_of_coherentXunionYset_general` (break-pair = `exists_coherentBreakPair_general` [済] + FPF-on-Z arith)。

⚠ **精度補正 (DadeChainStep 精読後)**: S07 norm-weighted は **S₁ メンバー (famS) の reducible 対応は確証**
(`famPairwise` = pairwise orthogonal、‖·‖²=mc)。だが **adjoined break character χ は `DadeChainStep.hχχ:‖χ‖²=1`
で既約前提**。(6.8.3) の break ψ は reducible でありうる (S∖S₁ で constituent が S₁ に未収なら break しうる) ので、
routing (1) の前に **「c2 break ψ は既約か、reducible-adjoined を S07 が別途扱うか」を要確認**
(候補: ψ の既約 constituent を adjoin する / ψ 既約性を break 構造から導く)。これが CB5 の残る precise 未解決点。

**正本 = 本 session 28 cont.² entry。CB5 = break-pair foundation done (combinatorial) + analytical 機構の
大半 (reducible S₁ メンバー = famPairwise) は S07 に既存 (再導出不要)。残 precise 未解決 = reducible-adjoined-ψ
の扱い + S08 norm-weighted (5.6) chain 配線 + L4 FPF-arith。CB3-L3 (X∪Y glue) と CB4 (math-B τ₂) は別途。**

## 2026-06-11 (session 28 cont.³): reducible-adjoined-ψ の真の深さ = R(reducible) ⟹ (4.9) 再浮上の可能性 (調査のみ、Lean 変更なし)

(5.6) 原文 (mmd 04.7 L59-79) + S07 内部精読で reducible-adjoined-ψ の正確な障害を確定:

### (5.6) 原文 = norm-weighted、adjoined χ 既約性要求なし
**(5.6) Theorem** 条件: (a) S₁ coherent (b) χ₁(1)|χ(1) (c) `2χ(1)χ₁(1) < ∑ᵢ χᵢ(1)²/‖χᵢ‖²`
⟹ S₁∪{χ,χ̄} coherent。**χᵢ も χ も reducible 可** (‖·‖² で正規化)。proof (5.6.1) は
`(χ−aχ₁)^τ = X−Y, X∈ℤ[R(χ)]`、Y⊥R(χ) で R(χ) = adjoined χ の反射族 (Hypothesis (5.2) が
全 S に与える、reducible 含む)。

### 形式化の精査: 2 段階に分かれる
- ✅ **Dade image step は reducible ψ で OK**: `scaledDiff_dadeImage_mem_ZIrr` (S08:6006) は
  `χ.mem_ZIrr` のみ使用 (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。**reducible ψ=Ind θ も
  ψ∈ZIrr** (非負整数結合) ゆえ `τ(ψ−aχ₁)∈ZIrr` は成立。R(ψ) 不要。
- 🛑 **(5.6.1) 分解は R(ψ) を要する**: `DadeChainStep` (S07:6237) は adjoined の反射族
  `dadeOrthonormalCharacterImageFamilyOfDiff` を持ち、`hχχ:‖χ‖²=1`/`hχbarχbar:‖χ̄‖²=1` を**必須 field**。
  reducible ψ (‖ψ‖²>1) では不成立。R(reducible ψ) = §5 (5.2)-reflection-for-reducible は
  形式化に無い (`dadeOrthonormalCharacterImageFamily` = `χ:IrreducibleCharacter` 専用)。

### 🚨 含意: (6.8.3) reducible break ψ は (4.9) 級を要しうる (session-27 RECON の盲点)
- (6.8.3) の break ψ∈S∖S₁ (S₁⊇X∪Y)。reducible は S(Z)∖Y に w₂−1 個 (Y は既約 deg|W₁|)。
  ψ がその一つなら **R(reducible ψ) = (4.9) certain-type 反射構造** (μ_j=±δ∑ω^σ がまさに reducible 反射)。
- **session-27 RECON「(4.9) 不要」は (6.8.2.3) [χ_i 既約] には正しいが、(6.8.3) の break ψ を見落とし**。
  ⟹ c2 (6.8.3) は (4.9) 級に再接続しうる (off-path・full §6)。
- **escape 候補 (要検討、未解決)**: break を既約に confine — もし **S(Z) coherent** (reducibles を
  S₁ に full 収容、break は X 既約メンバーで起きる) なら reducible-adjoined 回避。S(Z) は H/Z-characters
  由来の induced で sub-(6.8) 的構造 (inductive?) — 設定は非自明だが (4.9) 回避の最有望路。

**∴ CB5 真の障害 = reducible break ψ の R(ψ)**。(a) S(Z) coherence で break を既約 confine (有望、要設計) /
(b) R(reducible) = (4.9) 形式化 (off-path)。**combinatorial foundation (exists_*_general) と S07
famPairwise [reducible S₁ メンバー] は landed/確認済で無駄でない** — full norm-weighted (5.6) 配線で再利用。
**正本 = 本 session 28 cont.³。次手 = S(Z) coherence の inductive 構造を精査 (4.9 回避可否の判定)。**

## 2026-06-11 (session 29, Fable 5): (5.3) 原文精読で経路 100% 確定 — R(reducible) = (5.3.b) = (4.9) 引用、「(4.7)-(4.9) off-path」撤回

### FT-critical 再確認 (repo 実配線で検証済)
- `field_normalizer_structure` (Pf 14.2, S16_NonExistenceG:6846) = **sorry** — `nonexistence_of_G` →
  BG.AppC final contradiction の唯一の carrier 供給源。S16.Hypothesis は S15.Hypothesis を base に持つ。
- (7.10) `card_G0_lower_bound` (S09:6479) = sorry (issue 0044)、(6.8) (issue 0046) が block。
- ⟹ **FT 経路の Pf 側 = S15/S16 scaffold 充足、数学的供給源 = §3-§8 → (6.8) → (7.10) → §9+ 連鎖。
  (6.8) 完遂が Lane B の FT-critical 第一任務** (「orphaned」は現 import 配線の話で数学的には必須)。

### 🔑🔑🔑 (5.3) 原文 (mmd 04.7 L15-29) — R(χ) producer の全貌
- **(5.3.a)**: S ⊆ Irr L なら (5.2.a)+(5.2.b) だけで Hyp (5.2) 成立 (‖(χ−χ̄)^τ‖²=2 ⟹ |R(χ)|=2;
  (5.2.e) は (4.1))。= 形式化済みの既約 producer。
- **(5.3.b)**: **Hypothesis (4.6)** + (5.2.a) + S ⊆ {Ind_K^L θ | θ∈Irr K, H⊄Ker θ} ⟹ Hyp (5.2) 成立:
  - (4.7) で ℤ[S,L^#] = ℤ[S,A] (τ の定義域)。pairwise ⊥ は (1.5.c)。
  - (5.2.d): χ 既約 → (a) 同様。**χ reducible → (4.4)+Thm(4.5) で χ = μ_j (0<j<w₂)、Thm (4.9) で
    R(μ_j) = {δ_j ω_ij^σ, −δ_j ω_ik^σ | 0≤i<w₁}** (k: μ̄_j=μ_k)。
  - (5.2.e): 既約×既約 = (4.1); reducible×reducible = R(μ_j) の形から; **既約 φ × reducible μ_j =
    (4.7) Supp(φ−φ̄)⊂A → (φ−φ̄)^τ は V で消滅 → NC((φ−φ̄)^τ) ≤ 2 → (3.8) で R(φ)⊥ω^σ 全 ω∈Irr W**。
- ⟹ **session 28 cont.³ の「(4.9) 級」評価は教科書的に正確** ((5.3.b) が文字通り (4.9) を引用)。
  **session 27 RECON の「(4.7)-(4.9) は case-B 経路外」は撤回** — (6.8.2.3) の直接引用としては正しいが、
  **(6.8.3) reducible break ψ の R(ψ) が (5.3.b) 経由で (4.7)/(4.8)/(4.9) を要求**。S(Z)-confine escape は
  不要 (教科書の正攻法が (4.9) ルート)。

### ▶▶ 確定経路 (case-B (6.8) 完遂 = FT-critical):
1. **(4.7) j≥1 part** (Supp μ_j ⊆ A∪{1}; recipe = s06 note session 27 末尾の ω_{0j} 論法) ← 今ここ
2. **(4.8)** (`sigmaCoeff_trichotomy` [landed] 消費)
3. **(4.9)** (= (4.8)+(3.9)+(4.3)+(4.7)、R(μ_j) の certain-type reflection)
4. **(5.3.b)** general R-producer (§7; OrthonormalCharacterImageFamily for reducible μ_j)
5. norm-weighted (5.6) chain (S07 機構既存 [famPairwise/mc]、S08 配線; DadeChainStep の hχχ=1 を ‖χ‖²=m 化)
6. CB5 L4-general (break-pair `exists_*_general` landed) → CB3-L3 → CB4 → CB6 capstone。
依存 landed 済: Hyp(4.6)/(4.1)/(4.3)/(4.4)/(4.5)/(4.7)core+induced/(3.8)trichotomy/(3.9)/(1.5.c)。
**正本 = 本 session 29 entry。これは s06 note「次 = (4.7) j≥1 → (4.8)/(4.9)」と完全一致 — 一本道。**
