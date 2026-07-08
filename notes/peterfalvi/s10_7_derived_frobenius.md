# Peterfalvi (10.7) `typeII_derived_frobenius` — honest-proof decomposition (lane a)

> Frontier note for the single residual `sorry` (`conj_frobenius`) of
> `typeII_derived_frobenius` (`OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean:66`).
> The datum is de-scaffolded 5/6 (commit 3907291e); this note pins the honest route
> for the last field. Coq mirror = `Frob_der1_type2` (`coq/theories/PFsection10.v:549-658`).
> Companion: issue 1017 (§5/prime-TI prereq map), s13_11_8_orthogonality.md update³⁸.

## Spine position (verified 2026-07-08)

On the FT spine — NOT off-path:
```
feitThompson → card_kappaHall_lt_of_isTypeIIIorIV (unique bare sorry, FeitThompson:426)
  → exists_zeta_residual_not_orthogonal (S12:4473, structurally complete)
  → [contradiction via] S12.S_not_coherent (10.8, S12:525; PROVEN modulo its one input)
  → typeII_coherence_contradiction_estimate (10.8 estimate, BARE sorry S12:514)
  → [TI-counting G₁ ⊆ (H#)^G ∪ V^G uses] (10.7) typeII_derived_frobenius
```
So `S_not_coherent` (S12:525) itself does NOT cite (10.7) directly; the dependency is via the
(10.8) *estimate*. Both the estimate (S12:514, bare) and (10.7)'s `conj_frobenius` are genuine
on-spine sorries; (10.7) is upstream (document order + the estimate consumes it) ⟹ correct target.

## `conj_frobenius` obligation

`IsFrobeniusGroup.conj_frobenius : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ N, n ≠ 1 → a*n*a⁻¹ ≠ n`
with `N = S_F.subgroupOf [S,S]`, `A = U.subgroupOf [S,S]`. Repackageable (no shortcut) via
`Ch06.IsFrobeniusGroup.of_centralizer_kernel_le` to: **`∀ h ∈ S_F, h ≠ 1 → C_{[S,S]}(h) ≤ S_F`**
(i.e. `HU` acts Frobenius-ly on `S_F`). The type-F structure only gives the *sub-complement*
`U₀`-Frobenius (`frobenius_HU0`); `U` is non-cyclic in type II so this does not transport —
genuine char-theoretic content is required.

## Coq `Frob_der1_type2` decomposition (the honest route)

Pivot = **`typeP_reducible_core_cases`** (`PFsection9:1439`), a dichotomy:
- **RIGHT branch**: `[/\ typeP_Galois, Frobenius(HU/H0), cyclic U, |U|=(p^q-1)/(p-1),
  & (FTtype M == 2 → [Frobenius HU = H ><| U])]`. The last conjunct **directly closes** the
  type-II goal. ⟹ in the Galois/regular case (10.7) is immediate.
- **LEFT branch**: `∃ t, chi_t ∈ S_H0C' ∧ chi_t 1 = q·u ∧ chi_t = Ind_HC(linear)` — a reducible
  core. This case is shown **impossible** by:
  1. `lambda := chi_t` irreducible in `calT = seqIndD HU S H 1`; and (via
     `typeP_reducible_core_Ind`, `PFsection9:1423`) a reducible `nu_r = primeTIred` with
     `nu_r 1 = lambda 1` (**equal degree**).
  2. `T2 := [lambda; lambda*; nu_r; nu_r*]`. `subcoherent calT` via `FTtypeP_subcoherent`
     (Coq PFsection8:819); `subset_subcoherent` restricts to `T2`; then
     **`uniform_degree_coherence`** gives `coherent T2 S^#` (all four have degree `q·u`).
  3. `oST` orthogonality: `phi ∈ Z[calS,M^#], psi ∈ Z[calT,S^#] ⟹ ⟨phi^τ, tauS psi⟩ = 0`,
     from **disjointness of the FT-Dade supports** `'A1~(M)` and `'A~(S)` (needs
     `FT_Dade0`/`FT_Dade` + `notMtype2`/`typePF_exclusion` + `FT_Dade_support_disjoint`).
  4. Contradiction: `alpha = mu_s − d·zeta ∈ Z[calS,M^#]`, `beta = nu_r − lambda ∈ Z[T2,S^#]`;
     `oST alpha beta = 0` but expanding via the coherent isometries + **`FTtypeP_coherent_TIred`**
     (the `primeTIred`→signed-sum-of-`cyclicTIiso`-`eta_` formula) + `cfdot_cycTIiso` +
     `coherent_ortho_cycTIiso` gives a nonzero value (a `±1` from the `(r',s')` diagonal term).

## Missing-piece candidates (repo state = pending Explore map, 2026-07-08)

Prime-TI foundation (Coq PFsection3 = 130 lemmas `cyclicTIiso`@1421; PFsection4 `primeTIred`) is
LARGE, **partially** in-repo under `certainType`/`columnFamily` names (S06; issue 1017 updates #1/#2:
`certainType_isCoherent` S06:505, `certainTypeR` S06:639). Coherence pieces exist:
`coherent_of_constant_degree` (= `uniform_degree_coherence`, S07_CoherenceConstantDegree:551),
`coherent_subset_of_constant_degree` + `subset_subcoherent` (S07_Subcoherent:256/…). Genuinely-
unknown-state (agent mapping): `typeP_reducible_core_cases` dichotomy, `FTtypeP_coherent_TIred`
signed-sum, `cyclicTIiso`/`eta_` dot-products, the `oST` FT-Dade-support disjointness.

**Most-upstream build target** (pending confirmation): whichever of
{`typeP_reducible_core_cases`, `cyclicTIiso`/`eta_` dot-product slice, `oST` Dade-disjointness}
is genuinely absent. `uniform_degree_coherence`/`subcoherent` are DONE ⟹ do not rebuild.
claim-before-build (9000-series) if the piece is shared prime-TI infra.

## 2026-07-08 update — infra map RESOLVED + (10.7)→(10.8) PIVOT + |U|≥7 landed (lane-a /loop)

### Explore map result (agent, verified)
- **SORRY-FREE, citable now**: `primeTIred`/`prTIred_not_irr` (PrimeTIResidue:197/273), `subset_subcoherent`
  + `coherent_subset_of_constant_degree` (S07_Subcoherent), `cyclicTIiso`/`sigma`/`eta` grid (S05/S16),
  `sixTwoDecompositionData` (=`FTtypeP_subcoherent` content, S13:814), Dade core (S04), disjoint-support
  cross-orthogonality `hypothesis79_zetaImage_cross_eq_zero` (S09:525), abstract contradiction
  `eta_cross_expansion_ne_zero` (S15:2430).
- **Missing/sorried, CROSS-LANE**: `FTtypeP_coh_base` (type-P Dade base) = genuinely absent, **assigned to
  lane C** (issue 9072, `of_typeP`-generic, via `dadeSupportHypothesisData_of_subset_sigmaSharp` S10:2160
  + `irrSubcoherent` S07:148); `character_degree_analysis` (13.3, S15:2406) = **lane b** (produces items 7/9
  `mu_col_tau1_eta_col_one`/`tau1S_induce_inner_eta`). Sibling `exceptional_case_frobenius_realization`
  (S11:14184) = SAME type-II HU-Frobenius content, also gated.

### ⟹ (10.7) core is cross-lane-gated; its ungated lane-a parts are DONE
`conj_frobenius` bottoms out on `FTtypeP_coh_base` (C's, **no repo signature to cite** — creating one overlaps
9072) + (13.3) (b's). The ungated (10.7) pieces are already proven in the lane-a S11 sibling
(`caseB_character_counts` S11:14128, `chiefFactor_caseB_action_fpf`, `caseB_no_irreducible_u_formula`). So
lane-a's honest ungated (10.7) math is largely exhausted (mirrors update³⁸'s (11.8) conclusion).

### PIVOT: (10.8) estimate `typeII_coherence_contradiction_estimate` (S12:514) — lane-a ungated, C-collision-free
Cites (10.7)'s *conclusion* (existing sorried theorem), NOT the Dade base ⟹ no C overlap. Reduces (via PROVEN
`typeII_coherence_estimate_chain` S12:450 + `chiRhoNormSq_zeta_le_line83` S12:390) to: `hS` (|S|=|H||U|w₂),
`hA` (line-87, from line-83 + (7.8.b) `zetaNuRhoNormSqGeOfDade`), `hB` (TI-counting `G₁⊆(H#)^G∪V^G`, cites
(10.7)), and `∃u≥7`.

**LANDED (commit a4217ba2, sorry-free, axioms = 3 standard only)**: `Hypothesis.exists_typeII_partner_card_U_ge_seven`
(S12:503) = the `∃u≥7` witness (`|U|≥7` via `typeP_uW1_frobenius` + `card_kernel_modEq_one` + odd-forcing
`two_mul_add_one_le_of_odd_dvd` + `w2_prime`), partner TypeIIData exposed for `hS`/`hB`.

### 2026-07-08 update² — both partner inputs LANDED + hA REDUCED to a single (7.8.b) gate

**LANDED (2 commits, sorry-free, axiom-clean)**: `exists_typeII_partner_card_U_ge_seven` (S12:503, `|U|≥7`,
a4217ba2) + `typePData_card_eq_H_mul_U_mul_W1` (S12, `|M|=|H|·|U|·|W₁|`, a9a6471c). ⟹ the chain's `hS`
(|S|=|H|·|U|·w₂, via card lemma + |W₁(S)|=w₂) and `∃u≥7` inputs are both established.

**★ hA REDUCED to ONE gate.** The estimate `hA` = `1 − g1g − 1/w₁ < w₁/|M'|` needs only the **(7.8.b) lower
bound** `chiRhoNormSq(ζ^{τ₁}) 0 ≥ 1 − w₁/|M'|`; everything else is PROVEN:
- line-83 upper bound `chiRhoNormSq ≤ |A(M)|/|M| + g1g` = `Hypothesis.chiRhoNormSq_zeta_le_line83` (S12:390);
- strict `|A(M)|/|M| < 1/w₁` = `Hypothesis.card_typePA_div_card_lt_inv_w1` (S12:265);
- norm-one `‖ζ^{τ₁}‖²=1` = `inner_tau1_zeta_self_eq_one`.
Combine: `1−w₁/|M'| ≤ chiRhoNormSq ≤ |A(M)|/|M|+g1g`, rearrange + strict ⟹ hA (a `linarith`).
**g1g is concrete M-side** = `(|famG0| − |{g∉dadeSupport ∧ coprime w₁}|)/|G|` (the line-83 middle term,
`famG0 = (hyp.toFamilyHypothesis71).G0`) — no M↔partner identification needed for hA; `hB` bounds this same g1g.
⚠ line-83 is ℝ-valued, chain is ℚ — g1g:ℚ from ℕ cards + cast bridge.

**(7.8.b) bridge machinery**: `exists_chiRhoNormSq_ge` (S09_FrobeniusEstimate:415),
`chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero` (S09_FrobeniusEstimate:51); S16 has the analogous M-side bridge
`MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq` (S16:4755) + `chiRhoNormSq_psi_le_line83` (S16:4690) as the
pattern (couples chiRhoNormSq to the (7.8.b) `zetaNuRhoNormSqGeOfDade` S09:2406). Build the lane-a Hypothesis-M
analogue: `chiRhoNormSq(ζ^{τ₁}) ≥ 1 − w₁/|M'|` for the coherent ζ.

**Next lane-a steps**: (A) build the M-side (7.8.b) bridge `chiRhoNormSq(ζ^{τ₁}) 0 ≥ 1 − w₁/|M'|` (couple to
`zetaNuRhoNormSqGeOfDade` via the S16 `chiRhoNormSq_eq_zetaNuRhoNormSq` pattern); (B) then hA = pure arithmetic
(line-83 + strict, proven); (C) de-scaffold the estimate: chain + hS(done) + hA + hB, isolating **hB
(TI-counting `G₁⊆(H#)^G∪V^G`, cites (10.7))** as the last genuine gate; (D) build hB (§8/§9 orbit counting).
