# Peterfalvi (10.8) `S_not_coherent` — the §10 non-coherence keystone (lane-b W3)

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
  + (10.6.b), for `(L, A) = (M, A(M))`.  This needs a `S09.Hypothesis71`/`FamilyHypothesis71`/
  `Hypothesis78` **instance for `(M, A(M))`**.  Investigation findings (this session): the §7
  machinery `(7.1)`--`(7.8)` is sorry-free in `S09_NonexistenceCertain.lean`; the §10 `Hypothesis M`
  carries a genuine Dade map for **`A_0(M)`** (`Hypothesis.tau`, via `dadeData`/`hconj`), and
  `S10.dadeSupportHypotheses_typeP` (sorried but signature-correct) supplies a
  `DadeSupportHypothesisData M (typePA M)` for **`A(M)` directly**.  The `HConjInvariant`-for-`A(M)`
  snag is **resolvable** via `S04.HConjInvariant.restrict` (`A(M) ⊆ A_0(M)`).  So building the
  `Hypothesis71` for `(M, A(M))` is feasible (S04/S07 Dade-map plumbing), and is the right next
  upstream target for closing the §7 half.
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
