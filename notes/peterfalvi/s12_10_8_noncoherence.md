# Peterfalvi (10.8) `S_not_coherent` — the §10 non-coherence keystone (lane-b W3)

> ⚠ 2026-07-02: lane 表記は 2026-06-2x era (現 = **lane a**, 正本 [`ft_lane_reallocation_2026_06_28.md`](../meta/ft_lane_reallocation_2026_06_28.md)); (10.8) `S_not_coherent` は **landed**; 本 note の S12 行番号は 07-02 prefix-split (95fc7ade) 前; live = [`s13_11_8_orthogonality.md`](s13_11_8_orthogonality.md)。

> repo `S12_MaximalIII_IV_V.lean` = **Pf §10**. (10.8) is the keystone cited by **both**
> (11.3) `S13.S_H0C_not_coherent` and (10.10) `S12.no_typeV_maximal`, hence the most upstream
> FT-path char obligation in W3 (issue 2020). FT consumer chain:
> `card_kappaHall_lt_of_isTypeIIIorIV` → (11.9.b) → (11.8) → (11.3) → **(10.8)**;
> and `no_typeV_maximal` (10.10) → **(10.8)**.

## (10.8) statement and faithful decomposition (landed 2026-06-26)

`S_not_coherent`: under Hypothesis (10.1), the induced family `S = inducedFamily M` is **not**
coherent for the Dade map `τ`.

Peterfalvi's proof (04.12 p.61, lines 77–97) is a `False` from the coherence assumption, assembled
from three pieces — **the keystone is now a sorry-free assembly** citing them:

1. **arithmetic closer** `typeII_noncoherence_arithmetic` — **PROVEN** (pure ℚ). Given `w₁ ≥ 3`,
   `|U| ≥ 7`, `|M'| ≥ (2w₁+1)w₂`, and `1 − 1/w₁ − 1/|U| < w₁w₂/|M'|`, derives `False`
   (the bound's RHS exceeds `1 − 1/3 − 1/7 > 1/2`, forcing `|M'| < 2w₁w₂`, contradicting
   `|M'| ≥ (2w₁+1)w₂ = 2w₁w₂ + w₂`).

2. **structural lower bound** `Hypothesis.card_derived_ge` — `(2w₁+1)·w₂ ≤ |M'|`. Pure group
   theory (the `hMp` input). **Status: PROVEN** (2026-06-26, commit below; sorryAx only via the
   shared upstream `typePData_W1_hall_coprime`). The proof, working on the group `H = M'.subgroupOf M`
   (`≅ ↥M'`):
   - `derivedInG K = ⁅K,K⁆` (helper `hderiv`); `H = commutator ↥M`, `H.map subtype = M'`,
     `⁅H,H⁆.map subtype = M''` (`Subgroup.subgroupOf_map_subtype`, `Subgroup.map_commutator`);
   - `W₁` acts on `↥H` by conjugation fixed-point-freely: a fixed `x` has `(x:G) ∈ C_{M'}(a) = W₂`
     (`TypePData.centralizer_W1`) `⊆ M'' = ⁅H,H⁆.map subtype`, so `x ∈ commutator ↥H`
     (`commutator_subgroupOf_self` + `Subgroup.mem_map_iff_mem`); hence `w₁ ∣ |H:⁅H,H⁆| − 1` by
     **`S08.caseB_W1_dvd_index_of_centralizer_le`** (axiom-clean), with `hcop` from
     `typePData_W1_hall_coprime`;
   - `↥M' ` solvable (`hG.solvable_of_mem_maximalSubgroups` + `solvable_of_solvable_injective`) and
     nontrivial (`|H| ≥ |W₂| > 1`), so `⁅H,H⁆ < ⊤` (`IsSolvable.commutator_lt_top_of_nontrivial`),
     giving `|H:⁅H,H⁆| > 1`; all orders odd ⟹ `|H:⁅H,H⁆| ≥ 2w₁+1` (`S08.two_mul_add_one_le_of_odd_dvd`);
   - `|⁅H,H⁆| = |M''| ≥ |W₂| = w₂` (`Subgroup.card_le_of_le`, `W₂ ⊆ M''`); then
     `|M'| = |H| = |H:⁅H,H⁆|·|⁅H,H⁆| ≥ (2w₁+1)·w₂` (`Subgroup.index_mul_card`).
   - **import**: added `OddOrder.Peterfalvi.S08_CaseBEndgame` to S12 (acyclic; §8 < §10).

3. **norm-counting estimate** `typeII_coherence_contradiction_estimate` — the §7 analytic heart
   (the `hbound` input, with `|U| ≥ 7` bundled). **Status: the single remaining genuine
   character-theoretic gate of (10.8).** `∃ u ≥ 7, 1 − 1/w₁ − 1/u < w₁w₂/|M'|`. Peterfalvi's
   derivation (under coherence):
   - the Type-II partner `S` (Theorem (8.8), `exists_typeII_maximal_with_w2`) with `|U| ≥ 2w₂+1 ≥ 7`
     (as `UW₂` is Frobenius, from (10.7) `typeII_derived_frobenius`);
   - the family inequality (7.5) `S09.family_inequality` over `G₀ ∪ G₁`;
   - (10.6.b) `tau1_values_and_norm_bound` (**proven**: off `Ã(M)`, `ζ^{τ₁}(g)` is an odd integer,
     so `|ζ^{τ₁}(g)| ≥ 1`);
   - (7.8.b) giving `‖χ^ρ‖² ≥ 1 − ŵ₁/|M'|`;
   - the TI-counting `G₁ ⊆ (H#)^G ∪ V^G` (using (8.6.a)/(8.11)/(10.7)).

## Significance (progress is decomposition + wiring, not sorry count)

The keystone (10.8) went from **one opaque `sorry`** to **Peterfalvi's faithful 3-part
decomposition** with the arithmetic closer + the `(10.3)`-parameter/`CoherentHypothesis`
construction + the `w₁ ≥ 3` / `w₂ ≥ 1` structural facts **all genuinely wired**, and the two
remaining gates **precisely isolated**: a pure-group-theory bound (`card_derived_ge`) and the
single genuine §7 character estimate (`typeII_coherence_contradiction_estimate`). This sharpens
the W3 frontier from "(10.8) is a black box" to "(10.8) needs only the §7 norm-counting estimate
(+ a routine FPF index bound)". `no_typeV_maximal` and `S_H0C_not_coherent` are unchanged
(they cite (10.8) by signature).

## 2026-06-27 — estimate decomposed: analytic chain + `V^G` TI-counting landed (genuine)

The single remaining gate `typeII_coherence_contradiction_estimate` is **Peterfalvi's chain
(10.8) lines 79--99**, not one opaque step.  Two genuinely-provable pieces of that chain are now
**proven, sorry-free, full-build green** (all in `S12_MaximalIII_IV_V.lean`):

1. **`typeII_coherence_estimate_chain`** — the pure-`ℚ` analytic combination (lines 87--99): from
   the §7 output `hA` (line 87, `w₁/|M'| > 1 − |G₁|/|G| − 1/w₁`), the TI-counting bound `hB`
   (`|G₁|/|G| ≤ (|H|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)`), and `|S| = |H|·|U|·w₂`, derives
   `1 − 1/w₁ − 1/u < w₁w₂/|M'|` (the `hbound` that `typeII_noncoherence_arithmetic` then closes).
2. **the `V^G` TI-counting** (the `(w₁w₂−w₁−w₂+1)/(w₁w₂)` numerator of `hB`):
   - `typePData_card_W` : `|W| = w₁·w₂` (type-`P` torus order, `card_sup_eq_card_mul_card_of_disjoint_normal` in `↥W`);
   - `typePData_typePV_ncard` : `|V| = w₁w₂ − w₁ − w₂ + 1`;
   - `typePData_W_normalizes_typePV` : `l ∈ W ⟹ conj l • V = V` (`normalizer_V` with `X = V`);
   - `typePData_conjClassSet_typePV_ncard` : **`|V^G| = |G:W|·(w₁w₂−w₁−w₂+1)`** via
     `ncard_conjClassSet_of_isTISubset` + `typePData_V_ti` (the `V`-TI fact already in S12).
   These are fundamental, reusable type-`P` torus facts (the `ω`-grid lives on `W = W₁ × W₂`, the
   (4.5) reducible characters, the Dade support `A_0(M) ⊇ V^G`), not estimate-only scaffolding.

**Remaining gates of the estimate (precise, after this decomposition)** — the estimate stays
sorried, but now reduces to exactly:
- **(A) the §7 output (line 87)** = `family_inequality` (7.5) + `Hypothesis78.NormEstimates` (7.8.b)
  + (10.6.b), for `(L, A) = (M, A(M))`.
  - **✅ `Hypothesis.toHypothesis71` LANDED** (2026-06-27, sorry-free): the §7 (7.1) ρ-machinery data
    `S09.Hypothesis71 G (typePA M) M`, built by restricting the §10 `A_0(M)` Dade isometry
    (`hyp.dadeData`/`hyp.hconj`) to `A(M) = typePA ⊆ typePA0` via `FullDadeIsometryData.restrict`
    (Dade map + `IsDadeMap`) and `S04.HConjInvariant.restrict` (equivariance).  Takes
    `hN : N_G(A(M)) = M` (Pf (8.16), `S10.dadeSupportHypotheses_typeP`) as a parameter, so the
    construction itself is sorry-free.  Uses the `FiniteInduce` scope for the canonical
    `Fintype`/`Invertible` instances (avoids the instance-desync of explicit ones).
  - **✅ `Hypothesis.toFamilyHypothesis71` LANDED** (2026-06-27, sorry-free): the `(7.4)` one-member
    family `S09.FamilyHypothesis71 G 1` for `{(M, A(M))}`, built from `toHypothesis71` (its single
    member), with `IsDadeIsometry` from the restricted fdi's `toDadeIsometryData.isDadeIsometry`
    (supplied by `exact`, defeq through proof-irrelevance of the `hnorm` argument) and vacuous
    `pairwise_disjoint` over `Fin 1`.  **The entire input side of (7.5) for `M` is now built**:
    `S09.family_inequality (hyp.toFamilyHypothesis71 hN) χ hχ` gives line 81 directly.
  - **✅ `card_le_sum_normSq_of_forall_eq_odd_intCast` LANDED** (2026-06-27, sorry-free, general):
    the analytic core of line 83 — if `χ : ι → ℂ` takes **odd integer** values on a finite `S`, then
    `|S| ≤ Σ_{S} ‖χ‖²` (per element, `‖(m:ℂ)‖² = |m|² ≥ 1` via `Complex.norm_intCast`; `Σ_S 1 = |S|`).
    General/reusable (no §10 hyps).  In (10.8) it is applied to `χ = ζ^{τ₁}` on
    `G₀ = {g | g ∉ Ã(M), (ord g).Coprime w₁}` with the per-`g` bound (10.6.b) `zeta_tau1_norm_ge_one`,
    dropping the `G₀`-part of the (7.5) sum.
  - **Remaining for (A)**: (i) apply `family_inequality` (7.5) [one-liner on `toFamilyHypothesis71`];
    (ii) the `Hypothesis78` (7.8.b) instance for `M`; (iii) **the deep norm-connection assembly** —
    instantiate `card_le_sum_…` for `ζ^{τ₁}` on `G₀` via (10.6.b) `tau1_values_and_norm_bound`,
    combine with (7.5) [`famG₀ = G − Ã(M)` sum, `G₀ ⊆ famG₀` via `A(M)-support ⊆ A_0(M)-support`]
    → line 83; then `|A(M)|/|M| < 1/w₁` + (7.8.b) → line 87.
  - **✅ `Hypothesis.muColumnSign_eq_one_or_neg_one` LANDED** (2026-06-27, sorry-free): the (10.3)
    fact `δ_j = muColumnSign j ∈ {±1}` (from the §6 `columnFamily`'s `.sign_eq`).  With `hδj`
    (`muColumnSign j = δ`, returned by `exists_charParamArith`) this gives **`hδpm` (δ = ±1)** — one
    of the 3 not-yet-exposed (10.6.b) conditions now established.  Still open: `hzconj` (ζ non-real).
  - **⚠ signature-threading finding (2026-06-27)**: `tau1_values_and_norm_bound` / `zeta_tau1_norm_ge_one`
    (10.6.b) require **7 parameter conditions** `hmu : params.mu = hyp.muGrid`, `hos`, `hzS`, `hz1`,
    `hzconj`, `hδpm`, `hδj` that are **NOT fields of `CharacterParameters`** (which has a *free* `mu`
    field) — they hold only for the specific params from `Hypothesis.exists_charParameters`
    (`hmu`/`hos` are `rfl`; `hzS`/`hz1` and `hδj`/`hδpm` are now establishable per above; the lone
    deep gap is **`hzconj` (ζ non-real)**, which S12 currently *assumes* everywhere).
  - **✅✅ `hzconj` PROVEN (2026-06-27) — `Hypothesis.zeta_conj_ne`, sorry-free.**  The route is
    **direct via Peterfalvi (1.1)** (`OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'`):
    `ζ` is a *nontrivial* (degree `w₁ > 1`, from `hz1`) irreducible character of the *odd-order* `M`,
    so it is not real, i.e. `ζ.conj ≠ ζ`.  **No induced-character / orbit argument is needed** — the
    long argument below was unnecessary (kept for the record).  ⟹ **all 7 (10.6.b) conditions are now
    establishable** (`hmu`/`hos` = rfl, `hzS`/`hz1`/`hδj` supplied, `hδpm` from
    `muColumnSign_eq_one_or_neg_one`, **`hzconj` = `zeta_conj_ne`**).
  - **✅ `Hypothesis.exists_charParameters_full` LANDED** (2026-06-27, sorry-free): the single producer
    of `params` **with all 7 (10.6.b) conditions** (`mu=muGrid`, `omegaSigma=alignedΩΣ`, `ζ∈S`,
    `ζ(1)=w₁`, `ζ̄≠ζ`, `δ=±1`, `δ_j=δ`).  The (10.8) line-83 step consumes this (re-wrapping the
    coherence `⟨coh.coherent⟩` for the produced `params`).
  - **✅ `Hypothesis.sum_zeta_tau1_normSq_ge_card` LANDED** (2026-06-27, sorry-free): the `(10.6.b)`-
    summed bound `|G₀| ≤ Σ_{g∈G₀} ‖ζ^{τ₁}(g)‖²` over `G₀ = {g | g∉Ã(M), (ord g).Coprime w₁}`, via
    `card_le_sum_normSq_of_forall_eq_odd_intCast ∘ tau1_values_and_norm_bound`.  This is the `G₀`-drop
    term for line 83.  **Remaining line-83 wiring**: `G₀ ⊆ famG₀` (restricted `A(M)`-support ⊆
    `A_0`-support — derive), the (7.5)-combination (family_inequality + this bound + sum monotonicity
    + `|famG₀| = |G₀| + |G₁|`).
  - (superseded, kept for record) `hzconj` via the orbit argument — every degree-`w₁` `ζ` is non-real
    (de-risks `hzconj` from "deep unknown" to a concrete formalization task).  `ζ = Ind_{M'}^M θ`
    (`θ` nontrivial linear on `M' = [M,M]`, `θ` in general position so `ζ` irreducible of degree
    `w₁ = [M:M']`); `ζ̄ = Ind θ̄` (`induce_conj`, as in `inducedFamily_closedUnderConjugate`).  By the
    Clifford correspondence for the normal `M' ◁ M`, `ζ = ζ̄ ⟺ θ̄ = θ^{w}` for some `w ∈ W₁`
    (`M`-conjugate = `W₁`-conjugate).  **Key: `w₁ = |W₁|` is odd.**  Suppose `θ̄ = θ^{w₀^k}`
    (`W₁ = ⟨w₀⟩`); since `θ̄ = θ⁻¹`, applying inversion again gives `θ = θ^{w₀^{2k}}`, and `W₁` acts
    fixed-point-freely on the regular orbit, so `w₀^{2k} = 1`, i.e. `2k ≡ 0 (mod w₁)`; `w₁` odd ⟹
    `k ≡ 0` ⟹ `θ⁻¹ = θ` ⟹ `θ² = 1` ⟹ `θ = 1` (|`M'/M''`| odd), contradicting `θ` nontrivial.  Hence
    `ζ̄ ≠ ζ` for **all** such `ζ` (no special choice needed).  **Formalization — FEASIBLE**: the Clifford
    correspondence `Ind θ = Ind θ' ⟺ θ' is conjugate to θ` is **already in the repo** —
    `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean:192` ("Induced irreducibles
    coincide iff the sources are `G`-conjugate", for `θ, ψ ∈ Irr H`).  So `hzconj` is a well-scoped
    task: apply that correspondence to `ζ = Ind θ`, `ζ̄ = Ind θ̄`, then the odd-order orbit argument
    above (`θ̄ = θ^{w} ⟹ θ = 1`).  The remaining investigation is connecting `(10.2)`'s `θ` (its
    `M'`-conjugation / `W₁`-action / regular-orbit setup) to the correspondence's conjugation
    hypothesis.  With `hzconj` done, **all 7 (10.6.b) conditions are available** and the line-83
    assembly (thread the 7 conditions `exists_charParameters → … → estimate` + the `card_le_sum`
    sum-drop) can proceed; then line 83 → 87 needs `|A(M)|/|M| < 1/w₁` + (7.8.b), and the estimate
    still bottoms out on the §9-blocked (B1)/(10.7).  The
    estimate's signature takes an **arbitrary implicit `{params}`** (the one `coh` is for), so to
    invoke (10.6.b) inside it these 7 conditions must be **threaded** `exists_charParameters →
    `w2_prime_and_parameter_independence` → `S_not_coherent` → the estimate (add them as hypotheses,
    have `exists_charParameters` expose them).  This is a design+proof step spanning 3 declarations,
    the real entry cost of (iii).
  - **deepest W3 root**: even with all of (A) done, the estimate needs **(B1)** = (10.7), which is
    **§9-blocked** (`S11.Section11CharacterData` carrier, shared with (11.8)).  The §7 foundation
    above is genuine reusable infrastructure for the honest (10.8) proof, but the headline estimate
    will not close until the §9 carrier is materialised.
- **(B1) the inclusion `G₁ ⊆ (H#)^G ∪ V^G`** (lines 89): needs **(10.7) `typeII_derived_frobenius`**
  (the `x ∈ HU ⟹ x ∈ H` step) + (8.6.a)/(8.11)/(2.1).  `(10.7)` is the §9-blocked piece (its
  Peterfalvi proof cites the §9 Clifford counts `(9.8.b)/(9.9.b)/(9.10)`, which are stated against
  the **opaque, never-constructed** carrier `S11.Section11CharacterData` — same root blockage as
  (11.8)).  No structural shortcut: `TypeFData.frobenius_HU0` only gives `H ⊔ U₀` Frobenius
  (`U₀` an exponent-proxy), not the full `[S,S] = H ⋊ U` Frobenius that (10.7) asserts.
- **(B2) the `(H#)^G` count** `|(H#)^G| = |G:S|·(|H|−1)`: the partner analogue of the `V^G` count
  above, once the Type-II partner `S`'s `H# = S_F#` TI-ness (8.6.a) and `N_G(H#) = S` are available
  (partner structure, from a richer (8.8) than the proven `exists_typeII_maximal_with_w2`).

**Upstream-first priority for the next session**: (A) [§7 `Hypothesis71` construction for `(M,A(M))`,
feasible] is the cleanest genuine next step; (10.7)/(B1) bottoms out on the §9 `Section11CharacterData`
carrier (deep, shared with (11.8)).

## 2026-06-27 (cont.) — (8.16) `N_G(A(M)) = M` proven; the §7 family input is now self-contained

The upstream prerequisite of the §7 input (A) — the `M`-stability `hN : N_G(A(M)) = M` that
`toHypothesis71` / `toFamilyHypothesis71` took as a *free parameter* — is now **proven**
(`S12.Hypothesis.normalizer_typePA_eq`, axiom-clean, full build 3884 green, commit on lane-b).

- **Statement** = Peterfalvi (8.16) for the type-`P` support `A(M) = typePA M`: for the genuine (10.1)
  `Hypothesis M`, `Subgroup.normalizer (typePA M hyp.typeP) = M`.
- **Proof** (pure group theory, no character data): the carried (8.15) datum gives
  `N_G(A_0(M)) = M` (`hyp.dadeData.normalizer_eq`), where `A_0(M) = A(M) ∪ V^G`
  (`typePA0 = typePA ∪ conjClassSet (typePV)`).
  * `⊆`: `V^G = 𝒞_G(V)` is invariant under conjugation by **every** `g ∈ G` (new reusable
    `OddOrder.GroupTheory.mem_conjClassSet_conj_iff`, `N_G(𝒞_G(T)) = G`), so an element normalizing
    `A(M)` automatically normalizes the union `A_0(M)`, hence `N_G(A(M)) ⊆ N_G(A_0(M)) = M`.
  * `⊇`: `A(M) = centralizerSupport (M#) M'` is `M`-invariant (`M` normalizes `M' = derivedInG M` by
    `derivedInG_pointwise_smul` + `Subgroup.conj_smul_eq_self_of_mem`, permutes `M# = sharpSubgroup M`
    by `image_sharpSubgroup`, and conjugates the `C_G({x})` condition elementwise).
- **Effect**: `toHypothesis71` / `toFamilyHypothesis71` no longer take `hN`; they derive it internally
  from `normalizer_typePA_eq`.  So **`hyp.toFamilyHypothesis71 : S09.FamilyHypothesis71 G 1` is now a
  closed term from the genuine `Hypothesis`**, and `S09.family_inequality (hyp.toFamilyHypothesis71) χ hχ`
  (Peterfalvi (10.8) line 81, the (7.5) family inequality for `(M, A(M))`) is directly applicable with
  no external hypothesis.

**Remaining for (A), after this** (unchanged otherwise): (ii) the `S09.Hypothesis78` (7.8.b) instance
for `M` (the coherent extension `ν` from `coh` + the (7.8.c.i) `chiRho_eq_inner_beta` certificate),
and (iii) the line-83 norm assembly [`family_inequality` (now applicable) + the landed `G₀`-drop
`sum_zeta_tau1_normSq_ge_card` + `dadeSupport_restrict_subset` for `G₀ ⊆ famG₀` + sum monotonicity],
then line 83 → 87 via `|A(M)|/|M| < 1/w₁` + (7.8.b).  (B1)/(10.7) remain §9-blocked
(`S11.Section11CharacterData` carrier, shared with (11.8)).

**Next**: the cleanest genuine next step is the `Hypothesis78` (7.8.b) instance for `M` (ii) — the
last §7-input piece before the line-83 assembly; the deep `Section11CharacterData` carrier (the shared
root of (10.7)/(11.8)) remains the W3 keystone.

### ⚠ design finding for the next §7 step (ii) — the (7.8.b) `A = H#` requirement

`S09.Hypothesis78` (and its base `Hypothesis76` (7.6)) requires `A = H \ {1}` for a **normal subgroup
`H ⊴ L`** (`Hypothesis76.A_eq_H_sharp` / `H_normal_in_L`).  But `A(M) = typePA M =
centralizerSupport (M#) M'` is a *centralizer-support* set, **not** `H#` for any single normal
subgroup, so (7.8.b) does **not** apply to `(M, A(M))` directly — unlike (7.5), which needs only the
(7.1)/(7.4) Dade data and so *does* apply to `(M, A(M))` (now enabled by `normalizer_typePA_eq`).

In Peterfalvi (10.8) the (7.8.b) coherence bound `‖χ^ρ‖² ≥ 1 − ŵ₁/|M'|` is therefore applied to a
**different normal-subgroup configuration** (the `ŵ₁/|M'|` form points at `H = M'` / the
`(M'/M'')⋊W₁` Frobenius section, an `(M')#`-style `A`), not the type-`P` support `A(M)`.  ⟹ **before
building (ii)**, read Pf (10.8) 04.12 lines 81–87 to fix *which* `(A, L)` / normal `H` the (7.8.b)
instance is for; the "`Hypothesis78` for `M`" phrasing in earlier notes is imprecise on this point.
The `(7.5)`-for-`(M, A(M))` side (line 81) is exactly the part `normalizer_typePA_eq` unblocks.

### ✅ CORRECTION (2026-06-27, supersedes the design finding above): `A(M) = (M')#` IS `H#`

The "design finding" above (that `A(M)` is centralizer-support, **not** `H#`, so (7.8.b) applies to a
different config) is **WRONG** and is hereby corrected.  Reading Peterfalvi (10.8) 04.12 line 79
confirms `ρ` is defined with `L = M, A = A(M)`, and **both** (7.5) (line 81) and (7.8.b) (line 85) use
this *same* `ρ` — so (7.8.b) is for `(M, A(M))`, exactly as (7.5).

The resolution: **`typePA M = sharpSubgroup (derivedInG M) = (M')#`** (proven:
`GroupTheory.typePA_eq_sharpSubgroup_derivedInG`).  The `centralizerSupport (M#) M'` definition's
centralizer condition is *vacuous* on `(M')#` — every `y ∈ (M')# ⊆ M#` self-centralizes (`x = y`).
So `A(M)` **is** the sharp of the **normal** subgroup `M' = derivedInG M ⊴ M`; the `Hypothesis78`
(7.8.b) `A = H#` requirement is satisfied with `H = M'`, `L = M`.  No alternative config is needed.

⟹ the (7.8.b) instance for `(M, A(M))` is the `H = M'` Hypothesis78 (the family `T = inducedFamily M
= S`, the coherent extension `ν = coh.tau1`, the (7.7.a)/(7.8.c.i) certificates) — this is the genuine
remaining §7 piece (ii).  `|A(M)| = |M'| − 1` (sharp of `M'`), so the line-87 arithmetic
`|A(M)|/|M| < 1/w₁` follows from `[M : M'] = w₁` (`TypePData.card_W1_eq_derived_index`):
`(|M'|−1)/(|M'|·w₁) < 1/w₁`.

## 2026-06-27 (cont.²) — §7-estimate inputs rounded out; remaining (10.8) §7 = the (7.8.b) instance

Status of the (10.8) §7 estimate `typeII_coherence_contradiction_estimate` (still one `sorry`, but its
genuine inputs are being proven ahead of the assembly, mirroring `card_derived_ge`):

**Proven this session (all axiom-clean, full build 3884 green)**:
- `Hypothesis.normalizer_typePA_eq` (8.16) `N_G(A(M)) = M` ⟹ `toFamilyHypothesis71` self-contained ⟹
  **(7.5) for `(M, A(M))` (line 81) is applicable** with no external hypothesis.
- `typePA_eq_sharpSubgroup_derivedInG`: `A(M) = (M')#` ⟹ `A = H#` with `H = M'` normal (the (7.8.b)
  config; corrects the earlier wrong "A ≠ H#" finding).
- `Hypothesis.card_typePA_div_card_lt_inv_w1` (line 87): `|A(M)|/|M| < 1/w₁`.
- (earlier) `card_derived_ge`: `(2w₁+1)w₂ ≤ |M'|`; `sum_zeta_tau1_normSq_ge_card` (G₀-drop);
  `dadeSupport_restrict_subset` (`G₀ ⊆ famG₀`); `typeII_coherence_estimate_chain` (the ℚ chain);
  `typeII_noncoherence_arithmetic` (the closer).

**Remaining for `hA` (line 87) — the one genuine §7 piece left**:
- **(7.8.b) `‖χ^ρ‖² ≥ 1 − ŵ₁/|M'|`** = an `S09.Hypothesis78` instance for `(A, L) = (A(M), M)` with
  `H = M'`.  Its `Hypothesis76` (7.6) data: `hyp71 = toHypothesis71` (have it), `H = M' = derivedInG M`
  (normal in `M` ✓), `A = A(M) = (M')# ` ✓ (`typePA_eq_sharpSubgroup_derivedInG`), the family
  `T = inducedFamily M = S` (the `ζ_i`), the (7.7.a) certificate; then `ν = coh.tau1` and the
  (7.8.c.i) `chiRho_eq_inner_beta` certificate.  **The two certificates are the deep content** (the
  coherence-based reduction); this is the next genuine multi-step piece.

**Then line 81 → 83 → 87** (mechanical given the above): (7.5) [line 81] + `sum_zeta_tau1_normSq_ge_card`
+ `Σ_{G₁}|χ|² ≥ 0` ⟹ line 83; + (7.8.b) + `card_typePA_div_card_lt_inv_w1` ⟹ `hA` (line 87).  The
final contradiction still needs `hB` (TI-counting, lines 89–99) which is **§9-blocked via (10.7)**
(the `S11.Section11CharacterData` carrier, shared with (11.8) — the W3 keystone).

**Next session**: build the (7.8.b) `Hypothesis78` instance for `(M, A(M))`, `H = M'` (the family is
`inducedFamily M`, `ν = coh.tau1`; the (7.7.a)/(7.8.c.i) certificates are the work).  After that, the
line 81→87 assembly is mechanical, leaving only the §9-gated `hB`/(10.7)/(11.8) keystone.

## 2026-06-27 (cont.³) — §7 input prerequisites COMPLETE; line-83 assembly fully scoped

`Hypothesis.inner_tau1_zeta_self_eq_one` (`‖ζ^{τ₁}‖² = 1`) landed (axiom-clean).  **The entire §7
*input* side of (10.8) is now proven** — the only remaining §7 piece is the (7.8.b) `‖χ^ρ‖²` bound
(deep certificate).  Proven inputs (all axiom-clean):

| input | lemma | rôle in (10.8) lines 81-99 |
|---|---|---|
| (7.5) applicable to `(M,A(M))` | `normalizer_typePA_eq` (8.16) ⟹ `toFamilyHypothesis71` self-contained | line 81 |
| `‖ζ^{τ₁}‖² = 1` | `inner_tau1_zeta_self_eq_one` | (7.5)'s norm-one arg |
| `A(M) = (M')#` | `typePA_eq_sharpSubgroup_derivedInG` | `A=H#` for (7.8.b), `\|A\|=\|M'\|−1` |
| G₀-drop | `sum_zeta_tau1_normSq_ge_card` ((10.6.b)) | line 83 |
| `G₀ ⊆ famG₀` | `dadeSupport_restrict_subset` | line 83 |
| `\|A(M)\|/\|M\| < 1/w₁` | `card_typePA_div_card_lt_inv_w1` | line 87 |
| `(2w₁+1)w₂ ≤ \|M'\|` | `card_derived_ge` | the closer's `hMp` |
| ℚ chain (87→bound) | `typeII_coherence_estimate_chain` | line 99 |
| closer | `typeII_noncoherence_arithmetic` | `False` |

**Precise line-83 assembly plan** (mechanical, all inputs ready; the remaining work is Finset
bookkeeping, not new mathematics).  For `F = hyp.toFamilyHypothesis71` (`k = 1`),
`χ = coh.tau1 params.zeta`, `hχ = inner_tau1_zeta_self_eq_one`:
1. `family_inequality F χ hχ` gives line 81:
   `|G|⁻¹·(Σ_{F.G0}‖χ‖² − |F.G0|) + (F.chiRhoNormSq χ 0 − |A(M)|/|M|) ≤ 0`.
2. `G₀set := filter (g ∉ hyp.dadeData.dade.dadeSupport ∧ (ord g).Coprime w₁) ⊆ F.G0`
   (`dadeSupport_restrict_subset`: `(F.hyp71 0).hyp.dadeSupport ⊆ hyp.dadeData.dade.dadeSupport`).
3. `Σ_{F.G0}‖χ‖² ≥ Σ_{G₀set}‖χ‖²` (`Finset.sum_le_sum_of_subset_of_nonneg`, `‖·‖²≥0`)
   `≥ |G₀set|` (`sum_zeta_tau1_normSq_ge_card`).
4. ⟹ `Σ_{F.G0}‖χ‖² − |F.G0| ≥ |G₀set| − |F.G0| = −(|F.G0|−|G₀set|)`, so line 83:
   `F.chiRhoNormSq χ 0 − |A(M)|/|M| ≤ (|F.G0| − |G₀set|)/|G|`  (with `|G₁| := |F.G0| − |G₀set|`).
5. line 87 = line 83 + (7.8.b) `F.chiRhoNormSq χ 0 ≥ 1 − ŵ₁/|M'|` + `card_typePA_div_card_lt_inv_w1`.
6. then `typeII_coherence_estimate_chain` + the `|U| ≥ 7` Frobenius bound on the partner.

**The two genuine gates that remain** (both deep, both already isolated):
- **(7.8.b)** `F.chiRhoNormSq χ 0 ≥ 1 − ŵ₁/|M'|` = an `S09.Hypothesis78` instance for `(M, A(M))`,
  `H = M'` (family `inducedFamily M`, `ν = coh.tau1`; the (7.7.a)/(7.8.c.i) certificates are the deep
  content).  This is the cleanest next genuine target.
- **`|G₁| = |F.G0| − |G₀set|` TI-counting** (lines 89-99) = `hB`, **§9-blocked** via (10.7)
  (`S11.Section11CharacterData` carrier, shared with (11.8) — the W3 keystone).

The natural way to land the estimate is a **faithful de-opacification** of
`typeII_coherence_contradiction_estimate`: write its body as [family_inequality → line 83 (steps 1-4,
mechanical)] + [(7.8.b) named obligation] + [line 87 + chain] + [hB named obligation], isolating the
two deep gates as named `sorry`s.  All the non-gate steps are now backed by proven lemmas.

## 2026-06-27 (cont.⁴) — line 83 PROVEN (the mechanical (7.5)+G₀-drop step)

`Hypothesis.chiRhoNormSq_zeta_le_line83` landed (full build 3884 green): Peterfalvi (10.8) 04.12
lines 81→83, `‖ζ^{τ₁,ρ}‖² ≤ |A(M)|/|M| + (|famG₀|−|G₀|)/|G|`.  This is the "mechanical, all inputs
ready" step from cont.³ — now actually proven:
- `S09.family_inequality` (7.5) on the self-contained `toFamilyHypothesis71` (norm-one =
  `inner_tau1_zeta_self_eq_one`) → line 81;
- `G₀ ⊆ famG₀` (`dadeSupport_restrict_subset`) + `‖·‖²≥0` lift `sum_zeta_tau1_normSq_ge_card`
  ((10.6.b)) to `famG₀` → line 83; `mul_sub`+`linarith` close.
- **Not AxiomsCheck-registered**: inherits the existing §10 `Hypothesis`-carrier `sorryAx` taint via
  `sum_zeta_tau1_normSq_ge_card`/`tau1_values_and_norm_bound` (same status as (10.9)); no new sorry.

**(10.8) progress map now**:
- lines 79-83: **proven** (`chiRhoNormSq_zeta_le_line83`).
- line 87 = line 83 + (7.8.b) [`‖ζ^{τ₁,ρ}‖² ≥ 1−ŵ₁/|M'|`, deep] + `card_typePA_div_card_lt_inv_w1`
  [proven] + `card_derived_ge` [proven].  **Blocked only on (7.8.b).**
- lines 89-99: the `|G₁| = |famG₀|−|G₀|` TI-counting (`hB`) + partner `|U|≥7`/`|S|=|H||U|w₂`
  (from (10.7)) → `typeII_coherence_estimate_chain` → `typeII_noncoherence_arithmetic` → `False`.
  **§9-blocked** (the `S11.Section11CharacterData` carrier, shared with (11.8)).

So the *entire* mechanical/arithmetic spine of (10.8) is now proven; the two remaining gates are
exactly **(7.8.b)** (the `Hypothesis78` instance for `(M, A(M))`, `H=M'`) and the **§9 carrier**
(`hB`/(10.7), shared with (11.8)).  Next genuine target: (7.8.b) — its config (`H=M'`,
`family=inducedFamily M`, `ν=coh.tau1`) is fixed; the (7.7.a)/(7.8.c.i) certificates are the content.

## 2026-06-27 (cont.⁵) — W3 keystone precisely scoped (issue 2030)

With the (10.8) mechanical spine done, the **single remaining keystone** for all of W3 is the §9
Clifford character theory.  Finding: `S11.Section11CharacterData` is **scaffold-by-design** (free
character fields `S/X/SOf/XOf/tau/quotientSemidirectFrobenius`), and (9.8)/(9.9)/(9.10) are all
`sorry` (S11:2505/2516/2532) — *unprovable* against the current carrier.  Both W3 obligations
((10.8)`hB`/(10.7) and (11.8)), **and** the last §7 gate (7.8.b) (whose `Hypothesis78` family
enumeration is §9-governed), converge here.

The genuine fix = **redesign the carrier** (genuine `S(HC)` etc. with property fields, or define
against the producer-backed `S12.Hypothesis`+`ChiefFactorData`) + **prove (9.8)/(9.9)/(9.10)** (the
(9.7)(a)/(b) Clifford dichotomy; case (b) Singer model has reusable infra `chiefFactor_caseB_image_*`).
Research-grade, multi-session.  **Full scoping + decomposition (sub-tasks A-D) = issue 2030.**

This session (cont.¹-⁵) took W3 from "(10.8) is a black-box estimate" to "(10.8)/(11.8) need only the
§9 keystone (issue 2030)", proving the entire §7-input + line-83 + arithmetic spine en route.

## 2026-06-27 (cont.⁶) — §9 keystone: character families genuinized (issue 2030, commit 9c41978a)

First brick of the §9 keystone (issue 2030, the convergence point of (10.8)`hB`/(10.7) and (11.8)).
`S11.Section11CharacterData`'s formerly free, scaffold-by-design character fields are now **genuine**:
new sorry-free defs `xiSet` (𝒳={χ∈Irr(HU)|H⊄Ker χ}), `xiOf` (𝒳(Y)), `induceHU`/`induceHU_apply_one`
(Ind_{HU}^M + degree), `sSet` (𝒮), `sOf` (𝒮(Y)) + foundational API; the carrier's `X`/`S`/`XOf`/`SOf`
are replaced by namespace defs pinned to these (`S=sSet data` etc.).  ⟹ (9.8)/(9.9)/(9.10) counts and
the (9.11) coherence consumer now reference Peterfalvi's **honest families** (previously unprovable
against free fields).  Full build 3884 green; consumers (S12 `typeII_section11_coherence`,
`sibleyTarget_H0C`) unaffected (signature-stable, no producer to break).  **Remaining §9** (issue 2030):
genuinize carrier subgroups `C=C_U(H̄)`/`U'=[U,U]`/`C'=[C,C]` (fiddly prerequisite, doesn't unlock a
proof; best bundled with the counts) + the deep Clifford/Dade proofs of (9.8)/(9.9)/(9.10).

## 2026-07-06 — SCOPE re-audit of `typeII_coherence_contradiction_estimate` (S12:445, sorry :453): the estimate is blocked on the type-II PARTNER Frobenius structure (10.7), which genuinely needs the ABSENT prime-TI-reducible coherence apparatus. NOT built (no clean ungated path); minimal missing piece named below.

Re-read the **full** Coq `FTtype345_noncoherence_main` (10.8, `coq/theories/PFsection10.v:670-791`) and
`Frob_der1_type2` (10.7, `PFsection10.v:549-666`) and re-inventoried the repo.  Findings (corroborated
two independent sub-agents + direct reads):

**Which facts the (10.8) FINAL numeric inequality needs, and their repo status**
(via the proven ℚ chain `typeII_coherence_estimate_chain` (S12:389), whose inputs are `hA`/`hB`/`hS`):
- **`hA` (line 87)** `1 − |G₁|/|G| − 1/w₁ < w₁/|M'|` = line-83 **upper** bound (`chiRhoNormSq_zeta_le_line83`,
  S12:329, **PROVEN**) + (7.8.b) **lower** bound `chiRhoNormSq ≥ 1 − w₁/|M'|` + `card_typePA_div_card_lt_inv_w1`
  (S12:204, PROVEN).  ⟹ `hA` reduces to **(7.8.b) for `(M,M')`**.
  - **KEY POSITIVE FINDING**: `inducedFamily M = S` (S12_Core:79) is **exactly** `{Ind_{M'}^M θ | θ∈Irr(M'), θ≠1}`
    = the Coq `calS = seqIndD … M`, so the coherence datum `coh.coherent : IsCoherent hyp.tau hyp.Sset hyp.A0`
    **IS** the `cohS` that the Coq (7.8.b) `Dade_Ind1_sub_lin` (`PFsection7.v:345`, part (b)) consumes.
    That lemma is **GENERIC coherence-theory — NO prime-TI, NO Frobenius-on-`L` requirement** (only
    `coherent_with calS L^# (Dade ddA) ν`, `1 < size calS`, `ζ∈irr∩calS`, `ζ(1)=e`, and the `e≤(h−1)/2`
    guard = `smallIndex 2w₁+1 ≤ |M'|`, which `card_derived_ge` gives).  Lean engine EXISTS + PROVEN:
    `zetaNuRhoNormSqGeOfDade` (`S09_CertificateDischarge.lean:2406`), and the **exact wiring template is
    already realised for the §14 case** in S16: `MHypothesis.rhoNormSq_ge_lower` (`S16_NonExistenceG.lean:2851`)
    with its posited `h78 : Hypothesis78` field (S16:1643) + `psi_tau1_eq` (S16:1672).  So a `Hypothesis78`-for-`M`
    (`H=M'`, `ν=coh.tau1`) carrier + the `θ`-family/`hagree`/`hnu_isometry` certificates would give `hA` — a
    **genuine, ungated, feasible** (if deep, multi-step) build.  **BUT `hA` alone does not close the estimate** (below).
- **`hB` (lines 89-91)** `|G₁|/|G| ≤ (|S_F|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)`:
  - `V^G` numerator half **PROVEN** (`typePData_conjClassSet_typePV_ncard`, S12_Core:772).
  - `(S_F#)^G` count + the inclusion `G₁ ⊆ (S_F#)^G ∪ V^G` **ABSENT**; both need the type-II **partner** `S`'s
    Frobenius structure (Coq `Frob_der1_type2` at line 721 + Hall covering `sG1_HVG` 724-755).
- **`hS`/`hu`** `|S| = |S_F|·|U|·w₂` and `|U| ≥ 2w₂+1 ≥ 7` **ABSENT**; from the partner `S = (S_F⋊U)⋊W₂`
  decomposition + `Ptype_compl_Frobenius`+`ltn_odd_Frobenius_ker` (Coq lines 783-785).  The estimate's goal
  `∃ u, 7 ≤ u ∧ …` **existentially bundles `u = |U|`**, so the `7 ≤ u` witness AND the `hB` term (via `cardS`)
  are inseparable from the partner — a `hA`-only build **cannot** produce them.

**The single choke point** = the type-II partner Frobenius structure, i.e. **(10.7) `typeII_derived_frobenius`
(S12:47, bare `sorry`, 0 downstream consumers, `DerivedFrobeniusData` fully opaque)**.  Its faithful proof
(the entire Coq `Frob_der1_type2`) drives a coherence contradiction on the 4-member reducible family
`T2 = [λ; λ*; νr; (νr)*]` and essentially uses **`primeTIred pddS`** (Coq 576), **`FTtypeP_subcoherent`/
`subcoherent`/`subset_subcoherent`** (603-616), **`uniform_degree_coherence`** (618), **`FTtypeP_coherent_TIred`**
(629,656), **`cyclicTIiso`** (631) + `cfdot_cycTIiso`/`coherent_ortho_cycTIiso`.

**Minimal missing foundation (named)**: the **prime-TI-reducible character apparatus** — `primeTIred`,
`FTtypeP_subcoherent`, `FTtypeP_coherent_TIred`, `cyclicTIiso` (Coq PFsection3/4).  **VERIFIED ABSENT from
the Lean repo** (grep over `OddOrder/**` = 0 real identifiers; the lone hit is a *comment* in
`S06_CertainHypothesis46.lean:50` referencing Coq's unrelated `cyclicTIset`).  NB `uniform_degree_coherence`
alone **IS** present (= `coherent_of_constant_degree`, `S07_CoherenceConstantDegree.lean:551`, sorry-free) — but
(10.7) needs the *whole* subcoherent/`TIred`/`cyclicTIiso` chain to even set up the `T2` family it feeds to it.
This apparatus is the same root that (11.8) / the §9 keystone (`S11.Section11CharacterData`, issue 2030) bottom
out on — a multi-session foundation build, not a one-shot leaf.

**Decision (this session)**: did **NOT** modify `typeII_coherence_contradiction_estimate` — building only the
ungated `hA` half would leave the `∃ u` goal unclosable and would tempt a hoist-into-false-hypotheses
non-proof (forbidden).  The honest next genuine step, if one wants forward motion on THIS estimate
independently of (10.7), is the **(7.8.b)-for-`(M,M')` `Hypothesis78` instance** (the S16 `MHypothesis.h78`/
`rhoNormSq_ge_lower` pattern ported to the type-`P` `M`, `H=M'`, `ν=coh.tau1`) — a real reusable §7 brick that
proves `hA`'s lower-bound half — but it does not on its own discharge the estimate.  The estimate's closure is
gated on (10.7) ⟹ the prime-TI-reducible apparatus (issue 2030 territory).

## 2026-07-11 (lane a /loop、13 ticks) — ★★★★ (10.8) 無条件版 COMPLETE

**`S12_Noncoherence.S_not_coherent_unconditional` = [propext, Classical.choice, Quot.sound]**
(無条件・sorryAx ゼロ)。本 note の 2026-07-06 audit の「choke point = (10.7) → prime-TI 必須」
は 9079 pair route + issue 1020 の 3 phase で完全 supersede:
- hB: 被覆 (V-capture + Hall 共役 + Frobenius 捕捉) + union-bound 計数 + 支持制限
  (Ã₀∩cop ⊆ Ã) + ℚ 算術を全て実証明 (g1_div_le_of_partner)。
- (13.2.a) 論理循環 ((10.8)→(10.7)→13.2.a→(10.10)→(10.8)) を発見し、
  Section16MaximalPairCore split で切断 → (10.7)' も axiom-clean 化。
- 供給組立 = M-seeded Core pair + reconcile + K = W₂ 同定 + (8.11)[本日閉鎖]。
正本 = issue 1020。旧 S_not_coherent/estimate/hB-sorry は superseded (警告注記済)、
consumer migration が残 (1020 cascade)。

**次の genuine frontier (この cluster)**: `typeV_forces_coherence` (S12_MaximalIII_IV_V、
bare sorry) = (10.10.1)-(10.10.4) の §6-trichotomy ((6.8)/(5.7)/(6.5.c) + (8.7) cases)。
S14 の (12.6) assembly (frobenius_typeI_coherent_of_cyclicQuotient 系、sorry-free) が
type-I 側の同型 template。

---

## 2026-07-11 update (issue 1020 close): (10.8)/(10.10)/(13.2.a) の書籍 DAG 復元・完了

上記「次の genuine frontier = typeV_forces_coherence」は**完了・supersede** (issue 1021:
`typeV_forces_coherence_v2`、S12_Noncoherence)。現アーキテクチャ (正本 = closed issue 1020):

- **`S12_Noncoherence.lean`** (pair leaf 下流) = 無条件 (10.8) `S_not_coherent_unconditional`
  (axiom-clean) + (10.10) `typeV_forces_coherence_v2`/`no_typeV_maximal_unconditional`
  (残 sorry = (6.5) gates ×3、issue 2022 lane b)。
- **`S13_TypeDetermination.lean`** (Noncoherence 下流、issue 1020 Phase 3 新設) =
  (13.2.a)-trio (`card_kappaHall_lt_of_isTypeIIIorIV`/`…_isTypeP1`/`isTypeP2_of_typeP_kappaHall_lt`、
  FTS から移設) + canonical pair producer + κ-ordered M-seeded pair + (11.3)/(11.9.b) の
  unconditional heir (`S_H0C_not_coherent_unconditional`/`w2_lt_w1_of_hypothesis_H0C_unconditional`)。
  spine (13.2.a) 経路の residual = §14 Sibley glue (6.7)/(5.8) + (9.11) caseA refuter +
  (6.5) gates。**旧 (10.8) hB・legacy (10.10) bare sorry は spine 経路から消滅**。
- **legacy 残置** (削除しない): 旧 `S_not_coherent`/`no_typeV_maximal`/`S_H0C_not_coherent` は
  上流 S13-world (`isTypeIIIorIV` S13_SixTwoBridge / `coherent_quotient_bound`) の
  forward-cite 用 (import 位相上 heir を cite 不能)。各 docstring に **Legacy** 注記済。
- followup: lane c TTypeII repoint = issue 1022 (任意 hygiene)。
