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

### ★ params-provenance RESOLVED — de-scaffold fully specified (no more investigation needed)
The line-83 lemma needs `hmu/hos/hzS/hz1/hzconj/hδpm/hδj` (grid/zeta props). `CharacterParameters` carries `mu`/
`omegaSigma` as FREE fields, so the estimate's generic `params` does NOT supply them — **but**
`CoherentHypothesis.coherent : IsCoherent hyp.tau hyp.Sset hyp.A0` is **params-INDEPENDENT**, and
`Hypothesis.exists_charParameters_full` (S12_Core:3156) delivers a `params'` satisfying **exactly** those 7
props. ⟹ estimate reconstructs internally. **Concrete de-scaffold skeleton** (build this directly):
```
obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
obtain ⟨S, dII, hSmax, hSidx, hU7⟩ := hyp.exists_typeII_partner_card_U_ge_seven hG
refine ⟨Nat.card dII.typeP.U, hU7, ?_⟩
have hW1card : Nat.card dII.typeP.W1 = hyp.w2 := by rw [dII.typeP.card_W1_eq_derived_index]; exact hSidx
have hS_struct : Nat.card S = Nat.card dII.typeP.H * Nat.card dII.typeP.U * hyp.w2 := by
  rw [typePData_card_eq_H_mul_U_mul_W1 dII.typeP, hW1card]
have h83 := hyp.chiRhoNormSq_zeta_le_line83 hG coh' hmu hos hzS hz1 hzconj hδpm hδj  -- PROVEN
set g1g : ℚ := ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
  - ((Finset.univ.filter (fun g:G => g ∉ hyp.dadeData.dade.dadeSupport ∧ (orderOf g).Coprime hyp.w1)).card : ℚ))
  / (Nat.card G : ℚ)   -- concrete, matches line-83 middle term
have hA : (1:ℚ) - g1g - 1/hyp.w1 < hyp.w1 / Nat.card ↥(derivedInG M) := ... -- h83 + h78(GATE) + card_typePA_div_card_lt_inv_w1(PROVEN); ⚠ ℝ→ℚ cast
have hB : g1g ≤ (Nat.card dII.typeP.H - 1)/Nat.card S + (w₁w₂-w₁-w₂+1)/(w₁w₂) := ... -- GATE (TI-counting)
exact typeII_coherence_estimate_chain (Nat.card_pos) ... hS_struct hA hB
```
Remaining GENUINE gates: `h78` (7.8.b `chiRhoNormSq ≥ 1−w₁/|M'|`) inside hA, and `hB` (TI-counting). Everything
else is proven.

### ⚠⚠ Fintype-instance TRAP — the real de-scaffold blocker (attempt reverted, build kept green)
The minimal de-scaffold (partner + hS + chain + concrete g1g, hA/hB sorried) BUILD-FAILED on the
[[lean-instance-defeq-traps]] scoped-vs-explicit `Fintype G` clash:
- `chiRhoNormSq_zeta_le_line83` (S12:390) + `toFamilyHypothesis71` live under **`open scoped FiniteInduce in`**
  → their `Fintype G` is the FiniteInduce-scoped instance (derived from `Finite G`).
- The estimate `typeII_coherence_contradiction_estimate` has an **explicit `[Fintype G]`** binder (REQUIRED —
  `CoherentHypothesis` needs `[Fintype G]` in its signature, S12_Core:2852).
- ⟹ hand-writing g1g's `Finset.univ.filter` (or calling line-83) inside the estimate synthesizes the explicit
  `Fintype G`, which is not defeq to line-83's scoped one ("synthesized instance not defeq" at the `let g1g`).
**Fix direction (next iteration, focused)**: align the `Fintype G` provenance across the call chain
`S_not_coherent → estimate → line-83`. Options: (i) put the estimate body under `open scoped FiniteInduce in`
and obtain a matching-instance `h83`, extracting g1g from `h83`'s RHS (avoids hand-writing the filter); (ii)
`letI` the FiniteInduce Fintype locally before the line-83 call; (iii) provide an explicit-`Fintype` variant of
line-83 / `toFamilyHypothesis71`. Study how the (11.8) capstones (S12:4165+) call scoped-FiniteInduce lemmas
from explicit-Fintype contexts — that pattern is the template. **This instance-alignment is the concrete next
task; once solved the de-scaffold + hA(→h78) + hB follow from the skeleton above.**

## 2026-07-08 update³ — (10.8) estimate DE-SCAFFOLDED (build-green) + Invertible discipline unified (lane-a /loop)

The `typeII_coherence_contradiction_estimate` (S12) bare `sorry` is **replaced by the full honest
de-scaffold** (arithmetic spine proven sorry-free); two named genuine gates remain:

- **`h78` = `Hypothesis.chiRhoNormSq_zeta_ge_line78`** (S12, new named lemma, body `sorry`): the (7.8.b)
  ρ-norm **lower** bound `‖ζ^{τ₁,ρ}‖² ≥ 1 − ŵ₁/|M'|`.  **Ungated lane-a**, C-collision-free.
- **`hB`** (inline in the estimate, `sorry`): the TI-counting `|G₁|/|G| ≤ (|S_F|−1)/|S| + …`, cites (10.7)
  ⟹ cross-lane-gated (partner Frobenius structure).

Everything else is PROVEN: params reconstruction (`exists_charParameters_full`), partner `S`+`|U|≥7`
(`exists_typeII_partner_card_U_ge_seven`), `hS` (`typePData_card_eq_H_mul_U_mul_W1`), `hA` = line-83
(`chiRhoNormSq_zeta_le_line83`) + `h78` + `card_typePA_div_card_lt_inv_w1` with the ℝ→ℚ cast bridge
(`Rat.cast_lt` + `push_cast` + `linarith`), and the chain (`typeII_coherence_estimate_chain`).

### ⚠ Invertible-instance discipline (the analogue of the Fintype trap, now RESOLVED)
line-83/`sum_zeta_tau1_normSq_ge_card` are **rigid `FiniteInduce`-scoped** lemmas (no explicit
`[Invertible …]` binders ⟹ their `CoherentHypothesis` bakes the scoped `natCardInvC`/`natCardInvCG`).
The estimate + `S_not_coherent` formerly had **explicit `[Invertible …]` binders** ⟹ their `coh` carried
abstract binder instances, not defeq to the scoped ones, and `IsCoherent`'s **every** field depends on
both `Invertible` args (so neither `⟨coh.coherent⟩`+`letI`, `convert`, nor field-by-field re-wrap works —
all fail "synthesized instance not defeq").  **Fix = drop the explicit `[Invertible …]` binders from
`typeII_coherence_contradiction_estimate` and `S_not_coherent`** so their `coh` synthesizes the scoped
instances directly (matching line-83/h78).  All callers (`S_H0C_not_coherent` S13:1528, `no_typeV_maximal`
S12, `S12:coherent_Sset` path) are already binder-free under `FiniteInduce` scope ⟹ unaffected; S12+S13
build green.  **Lesson: never mix explicit `[Invertible …]` binders with scoped-FiniteInduce consumers on
the same `CoherentHypothesis` value — pick scoped.** ([[lean-instance-defeq-traps]])

### h78 build recipe (map-verified, no new deep sorry)
Construct `h78P : S09.Hypothesis78 G (typePA M hyp.typeP) M` with `H = derivedInG M`, then call
`zetaNuRhoNormSqGeOfDade` (S09_CertificateDischarge:2406) + bridge `chiRhoNormSq = zetaNuRhoNormSq` via
`chiRhoCF_congr_hyp` (S16:4738).  Port of `exists_M_hypothesis78` (S16:7988) to **type-P** producers.
Inputs (all proven/generic except one): `hAH`=`typePA_eq_sharpSubgroup_derivedInG`; H71/`hτ`=`toHypothesis71`
(S12_Core:555/580); placed family θ/ind1H/Ind(θ₀)=`params.zeta`=`exists_placed_induced_family` (S09:607,
K=`(derivedInG M).subgroupOf M`); `hnu_isometry`=`coherence_extension_inner_eq_on_family` (S09:2645);
`hzeta0nu`=`coherence_extension_orthogonal_constOne` (S09:2719) + `inducedFamily_closedUnderConjugate` +
`inducedFamily_degree_w1_conj_ne`/`inducedFamily_hasNoRealCharacters` + `inner_induce_constOne_eq_zero` +
Dade ⊥1_G transport (pattern `witness_L_hzeta0nu` S14:6818); `a,ha`=`exists_betaDecomp_a` (S09:1727);
`hsmall`=`card_derived_ge`.  **The ONE new shallow lemma**: `hagree` **Dade support-restriction bridge** —
`toHypothesis71.τ` (restricted to `typePA`=A(M)) agrees with `coh.coherent`'s extension of `hyp.tau` (full,
over `typePA0`=A₀(M)) on `typePA`-supported differences; analogous to `dadeSupport_restrict_subset`
(S12:367).  S16 never needs it (type-I has A(M)=Dade support, `h78_hyp_eq := rfl`).

## 2026-07-08 update⁴ — h78 (7.8.b) M-side bridge PROVEN (sorry-free, axiom-clean) (lane-a /loop)

`Hypothesis.chiRhoNormSq_zeta_ge_line78` (S12) is **closed** — the (7.8.b) ρ-norm lower bound
`‖ζ^{τ₁,ρ}‖² ≥ 1 − ŵ₁/|M'|` is now a real theorem. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`); full build 3941 green.

Faithful type-P port of `exists_M_hypothesis78` (S16:7988): assemble `S09.Hypothesis78 G (typePA M) M`
(`H = M' = derivedInG M`, `K = M'.subgroupOf M`, `ζ_0 = Ind_K θ_0 = params.zeta` via
`exists_placed_induced_family`, `ν = coh.tau1`) and feed `zetaNuRhoNormSqGeOfDade`.  Resolved pieces:
- **`hagree`**: the anticipated "new bridge" was NOT needed as a standalone lemma —
  `S04.FullDadeIsometryData.restrict_apply` already gives `(τ.restrict …).toDadeMap α =
  τ.toDadeMap (inclusion α)`, inlined (`rw [restrict_apply]; exact congrArg _ (Subtype.ext rfl)`) and
  composed with `coherence_hagree_dadeMap` (full-map agreement).  No thin wrapper added (repo convention).
- **`hzeta0nu`** (`ζ_0^ν ⊥ 1_G`): `coherence_extension_orthogonal_constOne` using the conjugate member
  `ζ̄_0 = Ind_K θ̄_0 ∈ S`; the key `⟨ζ_0, ζ̄_0⟩ = 0` uses **`hzconj`** (`params.zeta.conj ≠ params.zeta`)
  via `irreducibleCharacter_inner_eq_ite` + `if_neg`.  `htau1` (Dade ⊥ 1_G on `A_0`-supported) built from an
  inline full `Hypothesis71 G (typePA0 M) M` + `inner_tau_supported_constOne`.
- **`hsmall`** (`2e+1 ≤ h`): `card_derived_ge` (`(2w₁+1)w₂ ≤ |M'|`, `w₂ ≥ 1`); `e = complementIndex = w₁`
  (`hcardM : |M| = w₁·|M'|`, `complementIndex = |M|/|H|`), `h = kernelOrder = |M'|` (both `rfl`).
- **norm bridge** `chiRhoNormSq = zetaNuRhoNormSq`: `H78.hyp76.hyp71 = hyp.toHypothesis71 := rfl` +
  `hpsi : coh.tau1 params.zeta = ν(zeta zetaDistinct)` + `simp [chiRhoNormSq, zetaNuRhoNormSq]; congr 1`
  (avoids `chiRhoCF_congr_hyp`, which is downstream in S16).
- **import added**: `OddOrder.Peterfalvi.S09_CertificateDischarge` (§7 engine; DAG-upstream of §10, no cycle).

⟹ the (10.8) estimate's `hA` is now **fully proven** (line-83 upper + h78 lower + card_typePA).  The estimate's
sole remaining gate is **`hB`** (TI-counting `G₁ ⊆ (S_F#)^G ∪ V^G`, cites (10.7) — cross-lane-gated).

## 2026-07-09 update⁵ — ★ (10.7) dichotomy assembly LANDED (commit 2a458dbc): exceptional 枝 honest close、左枝 = 単一 named gate

新 leaf `OddOrder/Peterfalvi/S12_TypeIIFrobenius.lean` で **(10.7) の骨格が完成**。
`typeII_derived_frobenius` の bare `conj_frobenius` sorry は消滅し、残 sorry は
named producer `exists_typeIICrossIsometryData` 1 本 (census 81 不変、bare→named)。

### 構造 (全て PROVEN、producer のみ sorried)
- `typeII_HU_frobenius_of_coherent(_aux)`: S に `TypesIIIIIIVSetup` 直接構築
  (type_alt=Or.inl、`Section11CharacterData` は inert-tau で counts のみ消費) →
  `clifford_dichotomy`:
  - **caseA**: (9.8.c) 既約 + (9.8.b) 可約 (deg qu) → 左枝矛盾。
  - **caseB exceptional**: (9.10) `exceptional_case_frobenius_realization` conjunct 3 →
    `derivedInG_eq_fitting_sup_U` transport で **sorry-free に HU-Frobenius**。
  - **caseB 非 exceptional**: 既約 λ ∈ 𝒮(H₀C′) + (9.9.c) 可約 → 左枝矛盾。
- `TypeIICrossIsometryData.elim`: 左枝矛盾の計算 (proven)。M-side は proven
  `muColumn_tau1_pin` + `alignedOmegaSigmaGrid_inner`; 双線形展開で共有 grid entry
  ±1 のみ残す (S15 `eta_cross_expansion_ne_zero` の inline mirror — S15 は下流ゆえ
  cite 不可; 将来 upstream hoist で dedup 候補)。

### 残 = `exists_typeIICrossIsometryData` の 3 obligations (docstring 精密化済)
1. **T2 coherence (5.7)** — `S07.uniform_degree_coherence_of_families` (norm-general、
   sorry-free) を T2={λ,λ̄,ν,ν̄} に適用。R(ν) = `S06.certainTypeR`/`certainTypeRImage`
   (可約列、landed)、R(λ) = `dadeCharacterDifferenceImageOfDiff` (landed)、
   τ_S = honest type-P₂ Dade (`dadeSupportHypothesisData_honestTypeP2ASet`、landed、
   type-II S に直接適用可)。**hRorth (R(λ)⊥R(ν) = (5.3.b) base-ortho) の discharge は
   `S13.caseB_coherent_sOf_H0Cprime` (a 所有、sorry-free) の
   `caseB_sOf_memberRFamily(_orthogonal)` dispatch が worked template** —
   ただし S13 版は S13.Hypothesis (M-instance) locked ゆえ、S の (data,chief,chars_honest)
   への**再 instantiation** が必要 (§6/§9-generic 部品は再利用可; maxHeartbeats 1600000
   級の重 elaboration に注意)。chars_honest = tau := honest Dade / H0CprimeSupport :=
   honest support の manual 構築 (lane-b の `mkSection11CharacterDataS_honest` が
   S15-instance の template)。T2 (4-elt) 直接 route は caseA/caseB 一様に効く
   (ν は列ゆえ case 非依存、家族全体の uniform degree 不要)。
2. **S-side (5.8) + shared grid** — τ₂(ν) = ±Σ_j ω^{M-aligned}_{r'j}。2 段:
   (a) τ₂(ν) が **S-side** certainType grid の ±列和 (Coq `coherent_prDade_TIred`;
   subcoherent (5.5) 分解 `mem_coherent_sum_subseq` 相当 + (3.7) 係数 rigidity +
   (3.2.d) V-vanishing — S12 M-side の `exists_muColumn_tau1_eq_sum_R` →
   `muColumn_tau1_pin` chain が同型の worked template、S-side へ mirror)。
   (b) **S-grid = M-grid transpose** ((8.8) pair `S∩M=W` + (3.2) σ-uniqueness) —
   typeP_pair 圏 (issue 0098 item 1、未 claim・未 build)。⚠ (b) が真の新規 deep。
   M-side の同型 gate = S13_Orthogonality:316 `hbridge_τ` (narrow coherence の
   μ-column pin) — (a) の機構が landed すれば両方閉じる公算。
3. **(8.18.b) support disjointness** — `Disjoint Ã₁(M) Ã(S)` (8.13.c4 経由、
   M not-Frobenius ← Hyp (10.1))。既存 (8.17.c)/(8.18) lemma 群は type-I pair 限定
   (`ftThickenedSupport_A1_disjoint_of_nonconjugate` 等) — type-P₁ M × type-II S 版は
   **新規 statement**。engine は landed: `disjoint_conjugatesIntoSet_of_centralizer`
   (Machinery135:254、type-agnostic) + `inner_eq_zero_of_disjoint_support` +
   Dade 側は restrict (`S04.FullDadeIsometryData.restrict_apply`、h78 と同 pattern)。
   `escapingCentralizers_control` (8.13、S10:519) が sorried であることに注意
   (c4 の一意性がそこに依存するなら sorried-cite)。

### 次 iteration 開始点
上流優先: **obligation 1 (T2/caseB-engine の S-instantiation)** から。場所 =
S12_TypeIIFrobenius (a 所有)。その後 2(a) の S-side (5.8) 機構 mirror →
2(b)/3 は §8/pair 圏で claim-before-build 判断 (0098 item 1 は lane c 名義・未着手;
c は temporary-hold 中 — 必要になった時点で 9000 claim を検討)。

### update⁵ 補遺 — obligation 1 の S-side Dade は (8.16) TI-route が軽い
- **II→P2 dictionary は未形式化** (`isTypeII_of_isTypeP2` の逆は TaxonomyOutput の仮説
  としてのみ存在) ⟹ honest-P₂ Dade (`dadeSupportHypothesisData_honestTypeP2ASet`、
  要 `IsTypeP2 S`) を type-II S に使うには dictionary が先に要る。
- **代替 (Coq 準拠・軽い)**: type-II では (8.16) `FTtypeII_ker_TI` = A₀(S)/A(S)/A₁(S)
  が normedTI (normalizer S)。repo に **`S04.Hypothesis.of_isTISubset`**
  (S04_DadeIsometryBasic:273、TI subset → Dade Hypothesis、signalizer 自明) が landed、
  (8.16) core = `typeII_centralizer_le_of_mem_mainSubgroup` (S14_MaximalI/
  WitnessSylowCyclic:929、commit 51a7cbba で proven)。⟹ **P1 の τ_S は
  of_isTISubset route で構築するのが正** (II→P2 も escaping-σ-sharp engine も不要)。
  必要 glue = 「A(S) (= (8.10) の type-II A-set) が TI」を (8.16) core から
  `IsTISubset` 形に整形する補題。

## 2026-07-10 update⁶ — ★ (8.16) type-II S-side Dade base LANDED (c844ccb0、sorry-free/axiom-clean)

補遺²の判断は解決、obligation 1 の τ_S 基盤が **sorried-cite すら無しで** 閉じた
(S12_TypeIIFrobenius に新 section DadeBase、#print axioms = 3 standard のみ):

- **support 判断**: 差分 ν−λ の support は full A(S) (witness d ∈ S_F^# が w を中心化するだけで
  w 自身は C_{S'}(d) の U-part に居てよい ⟹ A₁ に絞れない)。よって honest A(S) =
  `centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)` (= S15 `honestTypeP2ASet` と
  定義一致、ただし S15 は下流ゆえ本 leaf では raw composite で表記)。
- **`typeII_centralizerSupport_isTISubset`**: Pf (8.16) TI part。原文の (8.15) signalizer 経由でなく 3-case 分解:
  A₁×A₁ = kernel-TI (`TypePNontrivialCore.hTI` + N_G(S_F)=S を maximality+simplicity で inline) /
  (A−A₁)² = **proven** BG Thm B(5) `theoremB_A_minus_Msigma_isTISubset`
  (A(S) ⊆ ASet S U は `typeP_exists_hall_derived_eq` の S' = U ⊔ S_σ; IsTypeP は
  `isTypeP_of_isTypeNonI (Or.inl hSII)` — **II→P₂ dictionary 不要**) /
  cross = σ-element order 不変 (`mem_Msigma_iff_isPiElement_sigma` + `isPiElement_conj`) で不可能。
  旧 `typeII_A_sets_TI` の false-as-stated 問題 (S10:524 RETIRED) は honest 集合 + type-II 限定で回避。
- **`typeIIDadeHypothesis`**: `S04.Hypothesis G (A(S)) S` (of_isTISubset、全 signalizer ⊥、
  scoped FiniteInduce)。**`typeII_centralizer_le_of_mem_centralizerSupport`**: (12.10) 用
  containment 形。**`centralizerSupport_sharpMsigma_conj_mem`**: S-共役安定性。
- 教科書 (8.14)-(8.17) ページは mmd MISSING → PDF p.48 直読で復元済 ((8.16) 証明 =
  「全 R(a)=1 + (2.3)」、(8.15) = Hypothesis (2.2)/(4.6)/(5.2) 供給、(8.17) = Thm E citation)。

### 次 iteration (obligation 1 続き) — τ_S packaging → (4.7) support → T2 家族
1. ~~**τ_S packaging**~~ **DONE (31f31a56)**: `typeIITau` = `S07.dadeIntegralCharacterMap`
   (typeIIDadeHypothesis + generic (2.6) `fullDadeIsometryData`、hconj = H≡⊥ 自明)。
   isometry/ZIrr/1-vanish は S07 generic
   (`dadeIntegralCharacterMap_inner_eq_on_supported_span` / `_mem_ZIrr_of_supported` /
   `_apply_one_eq_zero`) がこの hyp+hconj で直接効く — wrapper 不要。axiom-clean。
2. ~~**(4.7) support lemma**~~ **DONE (31f31a56)**: `typeII_sSet_member_support_subset`
   (member ⊆ A(S)∪{1}、TypesIIIIIIVSetup-generic) + `typeII_sSet_diff_support_subset`
   (等次数差、engine hsuppdiff 形) + `typeII_sSet_member_diffsupp` ((5.3.a) 共役差、
   irreducible R-datum 用)。
3. **T2 = {λ,λ̄,ν,ν̄} 家族の R-data + engine 適用 (次 iteration)**:
   - **irreducible 側 (λ,λ̄)**: `S07.dadeOrthonormalCharacterImageFamily` (generic、
     hyp+hconj+irr+non-real+supported) or `dadeCharacterDifferenceImageOfDiff` — 入力は
     landed (diffsupp ✓)。non-real は `inducedKernelFamily_hasNoRealCharacters`-analog
     (S11 に sOf 版があるか要確認; M-odd から)。
   - **reducible 側 (ν,ν̄) が本丸**: R(ν) = `S06.certainTypeR`/`certainTypeRImage` は
     **S-side Hypothesis46 instance** (S の (4.5) W-pair grid) を要する。M-side は
     `hyp.base.toHypothesis46 hG hG.odd` が持つが S 版は未構築 — S13 caseB dispatch
     (`caseB_sOf_memberRFamily(_orthogonal)`) の S-再instantiation とセット。
     「reducible sOf member = column μ_j」の同定 ((9.8.b)/(9.9.c) 分類) も同所。
     ⚠ maxHeartbeats 1600000 級の重 elaboration 注意 (S13:1466 前例)。
   - hRorth: S13 `caseB_sOf_memberRFamily_orthogonal` template の S-mirror。
   - **精査済 crumb (2026-07-10 iteration 3 冒頭)**: `S06.Hypothesis46` (S06_CertainHypothesis46:40)
     の Dade fields は instantiator 供給 — `dade0 : S04.Hypothesis G (A ∪ conjClassSetIn L tic.V) L`
     (= **A₀ = A ∪ V^L level**) + `tau : FullDadeIsometryData dade0`。⟹ S-side instance には
     landed の A(S)-level `typeIIDadeHypothesis` を **A₀(S) = A(S) ∪ V^S に拡張**する必要
     ((8.16) は A₀ も TI と主張 — V-part の cross case は W cyclic TI (3.1) 経由; typePA0 の
     conjClassSetIn 形 (8.10) と定義整合)。他 fields: CertainTypeHypothesis ((4.2) L-side) +
     tic (3.1 TICyclicHypothesis) + W₁/W₂ image 同定 + subH (W₂ ≤ H ≤ K, normal) + A_covers。
     M-side 前例 = `S12_Core.Hypothesis.toHypothesis46` (Hypothesis.lean:1057)。
   - 代替検討: T2 は 4 元のみゆえ、家族全体 dispatch でなく **per-member 直接構築**
     (λ: Dade R-datum ✓ / ν: column 同定 → certainTypeR) が軽い可能性。まず
     「ν が column である」ことの S11-level 供給源 (`caseA/caseB_character_counts` の
     hbred が ν の deg=qu しか言わない — column 性は §6 経由) を精査してから設計。

## 2026-07-10 update⁷ — ★ S-side Hypothesis46 instance LANDED (f0772198、sorry-free/axiom-clean)

update⁶ 手順 3 の本丸 infra が閉じた。S12_TypeIIFrobenius に新 section Hypothesis46Instance:

- **`typePV_orderOf_not_dvd_card_derived`** (TypePData-generic): V-元の位数 ∤ |M'|。
  W = W₁⊔W₂ 分解 + Lagrange + (4.2.a) Hall coprime → v ∈ ⟨v^{w₁}⟩ ⊆ W₂ 矛盾。
  Coq `FTsupport0` (BGsection16:194) の order 特徴付け ('A0 = 'A ∪ {非π(M')-elt かつ 非π(M')'-elt})
  の type-data 形 — **mixed case の共役不変分離子**。
- **`typeII_A0_isTISubset`**: (8.16) A₀(S) = A(S) ∪ V^S の TI。4-case:
  (A,A) = landed / (V,V) = `typePData_V_ti` (normalizer W ≤ S) / mixed = orderOf 分離。
  ⚠ Coq (8.16) は (8.15) Dade hyp + signalizer 自明化経由 (逆順: A₀ 先、A/A₁ は normedTI_S subset) —
  repo は (8.15) 一般機構を持たないので直接 TI (方針は landed A(S)-TI と同じ 3-case 拡張)。
- **`typeIIDadeHypothesis0`**: A₀(S)-level S04.Hypothesis (of_isTISubset)。
- **`typeIIHypothesis46`**: `S06.Hypothesis46 (A(S)) S` 完全 instance。
  **subH = S_F.subgroupOf S** ((8.15) type-II の H = M_s = S_F; M-side の H = K と異なる) →
  A_covers は honest A(S) の定義でほぼ自明 (S_F = S_σ via maxNilpotentNormalHall_eq_Msigma)。
  dade = landed typeIIDadeHypothesis / dade0+tau = 新 A₀ 構築 / tic 系 = M-side と同 pattern。
  パラメータは `data : TypePData S` (consumer は data.typeP を渡す)。

### 残 = update⁶ 手順 3 の T2 R-data 続き (次 iteration)
1. ~~**reducible→column 分類の S-side mirror**~~ **DONE (c8528167)**:
   `typeII_sOf_subset_inducedKernelFamily` (𝒮(Y) ⊆ IKF S' (Y∩S)、S13 sOf_subset_SOf の
   generic mirror — ⚠ S13 import は cycle 不可ゆえ leaf 内再掲、upstream hoist で dedup) +
   `typeII_reducible_inducedKernelFamily_eq_columnSum` (可約 → columnSum h46 χ₂、raw form)。
2. R(ν) = `S06.certainTypeR (typeIIHypothesis46 …)` + R(λ) = Dade 2-elt 族 + hRorth (S13 dispatch mirror)。
   - certainTypeR の入力 = hχ₂ (≠1、分類が供給) + hdeg (χ₂ vs χ₂⁻¹ の deg 一致 —
     `columnSum_inv_apply_one` が S13 で使った形; conj deg 相等から)。
   - R(λ) = `dadeOrthonormalCharacterImageFamilyOfDiff h46.dade0 hconj ⟨λ,hirr⟩ hreal hdiffsupp`:
     hreal = `S08.inducedKernelFamily_hasNoRealCharacters` (IKF bridge 経由) /
     hdiffsupp = landed `typeII_sSet_member_diffsupp` を **A₀-support へ拡張** (A ⊆ A₀ ∪-left)。
   - hRorth: (λ,ν)/(λ,ν̄) 型のみ要 (conj pair は engine の precondition で除外)。
     irr×col = S06 の certainTypeR cross lemma (S06_CertainTypeCoherence 後半、要確認) +
     dadeOfDiff×certainTypeR。col×col (ν,ν̄) は precondition 除外 ✓。
3. T2 = {λ,λ̄,ν,ν̄} 家族で (5.7) engine (`uniform_degree_coherence_of_families`)。
   ⚠ engine の τ は **A₀-level** `dadeIntegralCharacterMap h46.dade0 h46.tau`
   (certainTypeR の image family の τ; 確認済) — landed A(S)-level typeIITau でなく
   h46 側で組む (support lemmas は A ⊆ A₀ で通る)。engine 入力の残り:
   pairwise ortho = `IKF_pairwise_orthogonal` / no-real = `IKF_hasNoRealCharacters` /
   hN (pivot norm) = λ irreducible norm 1 / hiso+hZdiff = S07 generic (h46.dade0+hconj)。
   ⚠ S13:1466 前例の maxHeartbeats 1600000 級 elaboration 注意。

### 2026-07-10 update¹⁰ — obligation 2(a) の (5.8) route 完全マップ (調査完了、実装は次 iteration)

★ **(5.8) endgame は既に formalize 済み**: `eq_smul_chiFam_column_of_vanishOnV`
(S05_SigmaTrichotomy:456) が「X|_V = 0 + σ-coeff 2 列支持 ({0,δ}/{0,−δ}) + ‖X‖² = w₁ +
Parseval ⟹ **X = δ·Σ_p χ_{(p,kcol)} ∨ X = −δ·Σ_p χ_{(p,jcol)}**」の dichotomy を供給。
★ **Coq (5.8) (`coherent_prDade_TIred`, PFsection5:1371) の結論も dichotomy** (±sign × k/k̄ 列)
— `TypeIICrossIsometryData` の (r', δ') は存在的 packaging ゆえ **dichotomy で十分**
(M-side 流の exact pin 不要、α_{ij}/ζ 機構の mirror 不要)。

**X := τ₂(ν) への適用に要る glue** (Coq proof 精読済、逐一対応):
1. **(5.5)-for-ν**: τ₂(ν) = Σ_{α∈E} α、E ⊆ certainTypeR.imageSet、|E| = w₁。
   M-side `exists_muColumn_tau1_eq_sum_R` (DadeCalculations:211-280) の mirror:
   `CharacterPsiDecomposition.ofProjection` + `eq_sum_of_psi_eq_zero`。
   ⟨ν,ν̄⟩ = 0 は `columnFamily_mu_sum_inner` + `column_inv_ne_self`;
   extends_on_supported の zSupportedSpan T2 A₀ 入力は landed hsuppdiff で。
2. **hψV: τ₂(ν)|_V = 0** — Coq の zeta1-trick: zeta1 := λ(1)·ν − ν(1)·λ (A(S)-supported、
   deg 相殺 — landed diff-helper の smul 版 1 本要)。τ₂(zeta1) = τ_S(zeta1) (supported) の
   V-値 = 0 (**landed anchor** `typeII_tau_apply_eq_zero_of_mem_ticVdiffV`) →
   τ₂(ν)(v) = (ν1/λ1)·τ₂(λ)(v) → **τ₂(λ)|_V = 0 が残り**:
   (5.5)-for-λ (card 1 → τ₂λ = ± 単一 Dade 成分) + R(λ)-member ⊥ 全 ω 列
   (landed cross lemma の `key` brick は既に ∀χ₂'-general — standalone 抽出) +
   「⊥ 全 σ-image → V-vanish」glue (W-side は `vanishOnV_of_inner_alphaCF`
   S05_SigmaIsometry:268; G-side 版の有無要確認 — 無ければ index 全射性経由)。
3. **σ-coeff 計算**: `sigmaCoeff := ⟨ψ, chiFam pq⟩` (S05_SigmaIsometry:501) — τ₂ν = ΣE +
   chiFam 直交性から直接。2 列支持: E ⊆ ±δω_{χ₂/χ₂⁻¹} + **index 翻訳**
   `certainTypeOmegaSigma_eq_chiFam` (S06_CertainTypeIsometry:165、
   ω_{χ₂,i} = chiFam (omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)))。
   ⚠ q-成分の i-独立性 + (χ₂,i) ↦ pq の単射/全射 bookkeeping — S06 (4.8) 機構
   (`certainType_diff_dade_eq` の NC≤4 計算) に既存 lemma がある可能性大、先に精査。
4. **hXnorm** = extension_inner_eq (ν ∈ zSpan T2) + columnFamily_mu_sum_inner (w₁)。
   **hParseval** = ΣE 直交形から (coeff = [α∈E]·±δ、Σ|coeff|² = |E| = w₁ = ‖X‖²)。
5. **hyp/app**: ticVdiff (typeIIHypothesis46 …) + rfl + ticVdiffFullDadeApplication
   (全て landed cross lemma と同じ instances)。結論の chiFam-form → certainTypeOmegaSigma
   逆翻訳で `typeII_nu_tau2_dichotomy` に整形。

実装順 (次 iteration): 3 の index bookkeeping 精査 → (5.5)-for-ν/λ → 2 の V-vanish 組立 →
S05 endgame 適用 → dichotomy 整形。その後 obligation 2(b) (S↔M grid transpose) と 3。

**進捗 (2026-07-10 続き)**: ~~(5.5)-for-ν/λ~~ **DONE (c6d4b780)** — 新 leaf
`S12_TypeIIColumnPin.lean` に `typeII_T2_extension_columnSum_eq_sum` (τ₂ν = ΣE、|E|=w₁) +
`typeII_T2_extension_lam_eq_single` (τ₂λ = 単一 Dade 成分)。sorry-free/axiom-clean。
S06 (4.8) index bookkeeping も精査済: `sigmaCoeff_psi_eq` pattern (chiFam_spec .2.2.1 で
ite 化) + `omegaProdCharTic_ne`/`omegaProdEquiv_symm_omegaProdCharTic_ne` (列単射) が既存 —
2 列支持の hsupp には **q-成分の i-独立性** (omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) の
第 2 成分が i に依らない) が追加で要る (S05 `omegaProdEquiv_symm_omegaProdChar` :
symm (omegaProdChar p q) = (p,q) 経由で omegaProdCharTic = omegaProdChar (transport i)
(transport χ₂) 形の分解 lemma を書く)。
⚠ Lean 知見: 識別子に λ 不可 (予約語) / proof 内 `set` は theorem binder を再束縛して
shadow 事故 (c✝) → subst + full-term 直書き。
残 = step 2 (V-vanishing: R(λ)-member ⊥ 全 ω の standalone 抽出 → τ₂λ|_V = 0 →
zeta1-trick で τ₂ν|_V = 0) → step 3 (S05 endgame + dichotomy 整形)。

**進捗²**: ~~key-brick standalone~~ **DONE (156e3906)**:
`typeII_dadeOfDiff_member_inner_omegaSigma_eq_zero` (R(λ)-member ⊥ 全 grid 列)。
**残る glue = (3.2.e) 「⊥ 全 σ-image → V-vanish」の G-side 版** — 設計確定済:
- σ = Ind on CF(W,V) 橋 (`sigma_eq_induce_of_supportedOnV`): 両者 conjugatesOfSet V 支持
  (`full_map_eq_zero_of_not_mem_conjugatesOfSet_V` / induce 版) + V 上一致
  (`full_map_eq_of_mem_V` S05_TICyclic:215 vs TI-induction 値 — V-TI で g v g⁻¹ ∈ V →
  g ∈ N(V) = W → 全項 = α(v)) + class-fn は V^G-支持なら V-値で決定。
- reciprocity = `ClassFunction.inner_induce_eq_inner_restrict` (既存 ✓、
  CliffordCorrespondence:71 の証明内で使用) で ⟨σα, ψ⟩ = ⟨α, Res_W ψ⟩。
- W-side 完結: `vanishOnV_of_inner_alphaCF` (S05_SigmaIsometry:268) に
  f := ClassFunction.restrict hyp.W ψ を食わせ f|_V = 0 = ψ|_V。
  alphaCF は ω-組合せ ⊆ CF(W,V) → σ(alphaCF) は χFam-組合せ → ⊥ 仮定から 0。
その後: τ₂λ|_V = 0 ((5.5) singleton + key-brick + glue) → zeta1-trick (λ1·ν − ν1·λ の
smul-diff support helper 1 本) → τ₂ν|_V = 0 → S05 endgame。

**進捗³**: ~~(3.2.e) glue~~ **DONE (7b02ae31)**: `ticyclic_full_map_eq_induce` (σ=Ind on
CF(W,V)、TI-counting) + `ticyclic_apply_eq_zero_of_forall_inner_chiFam` (Coq
ortho_cycTIiso_vanish — repo に無かった (3.2.e) gap を S05-generic に閉じた。upstream hoist
候補)。**残 = 純組立**: (a) τ₂λ|_V = 0 — (5.5) singleton (τ₂λ = α ∈ R(λ)) + 156e3906
(α ⊥ 全 ω) + glue (⚠ glue の仮定は ∀pq の chiFam-form — ω→chiFam は
certainTypeOmegaSigma_eq_chiFam、**全 pq への到達** = (χ₂',i) ↦ pq の全射が要 —
omegaProdEquiv.symm 全射 ✓ × omegaProdCharTic の (χ₂,i)-range = 全 Ŵ の確認 1 lemma,
S05 `omegaProdEquiv_symm_omegaProdChar` + w1CharEquiv/ticW₂-transport 全射で)。
(b) zeta1 = λ1•ν − ν1•λ: supported (smul-diff helper) → τ₂zeta1 = τ_S zeta1 (extends) →
V-値 0 (landed anchor) → λ1·τ₂ν(v) = ν1·τ₂λ(v) = 0 → τ₂ν|_V = 0 (λ1 ≠ 0)。
(c) S05 endgame 適用 (update¹⁰ の 3-5) → typeII_nu_tau2_dichotomy。

**進捗⁴ (741109f0)**: ~~(a) τ₂λ|_V = 0~~ ~~(b) τ₂ν|_V = 0~~ **step 2 完全 DONE**。
発見 2 点: (i) `inner_smul_chiFam_...` は既に ∀pq-chiFam 形 → **全射 lemma 不要**
(156e3906 を chiFam-primary に refactor)。(ii) **λ, ν 等次数ゆえ scaled zeta1 不要** —
ν − λ が直接 A(S)-supported で anchor が効く。⚠ λ-in-identifier 3 度目 (hλv 等) —
**識別子には lam/nu を使う** (λ は予約語、ν は可だが混在回避)。
**残 = step 3 (最終 assembly) のみ**: `typeII_nu_tau2_dichotomy` =
S05 `eq_smul_chiFam_column_of_vanishOnV` ((ticVdiff h46) rfl (ticVdiffFullDadeApplication…)) を
X := c.extension (columnSum χ₂) に適用。入力チェックリスト:
- hψV ✓ (741109f0 の nu-side、typePV↔ticVdiff.V defeq)
- σ-coeff 2 列支持 + {0,δ}/{0,−δ}: (5.5) E-形 (c6d4b780) から。τ₂ν = Σ_{α∈E}α、
  E ⊆ certainTypeRImage の像 → sigmaCoeff pq = ⟨Σ E, chiFam pq⟩ = Σ_{α∈E}⟨α, chiFam pq⟩ —
  各 α = ±δ_j ω_{χ₂/χ₂⁻¹, i} = ±δ_j chiFam P_i (certainTypeOmegaSigma_eq_chiFam) +
  chiFam 直交性 ((ticVdiff).chiFam_spec .2.2.1) → coeff = ±δ_j·[P ∈ E-index]。
  2 列条件の jcol/kcol := omegaProdEquiv.symm (omegaProdCharTic h χ₂/χ₂⁻¹ i).2 —
  **q-成分の i-独立性 lemma がここで必要** (omegaProdCharTic の分解、
  S05 omegaProdEquiv_symm_omegaProdChar + tic_W₂-transport; sigmaCoeff_psi_eq (S06:515) の
  pattern 参照)。row-条件 hk/hj: ∀p 形 — p ∉ P-image の行は coeff 0 (支持)。
- hδ = (columnFamily χ₂).sign (sign_eq) / hXnorm ✓ (extension_inner_eq + mu_sum_inner) /
- hParseval: ⟨X,X⟩ = w₁ = |E| = Σ_pq |coeff|² (coeff = ±δ on E-indices、0 else;
  E-index 単射 = certainTypeRImage_injective + omegaProdEquiv_symm_omegaProdCharTic_ne)。
- 結論整形: chiFam-form → certainTypeOmegaSigma 逆翻訳 (eq_chiFam.symm) で
  τ₂ν = δ·Σ_i ω_{χ₂,i} ∨ τ₂ν = −δ·Σ_i ω_{χ₂⁻¹,i}。

**進捗⁵ — q-成分 lemma の実装設計確定 (API 発見済、次 iteration で実装)**:
`omegaProdCharTic h χ₂ i := (sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂).comp
(ticWEquivSdiffW h)` (S06_CertainTypeIsometry:125、クリーンな合成形)。成分 lemma:
- **(L1) snd の i-独立性**: `(ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) |>.2`
  は i に依らない。証明: `omegaProdEquiv_symm_eq` (S05_SigmaIsometry:133、
  symm ξ = (ξ|_{W₁}, ξ|_{W₂})) で .2 = restriction; MonoidHom.ext w (w ∈ tic-W₂-of-W);
  値 = omegaProdChar (w1CharEquiv i) χ₂ (e w) — e w の sdiff-W₂ 帰属
  (`coe_ticWEquivSdiffW` S06:112 + tic_W2 = W2.map subtype) → `wFst_eq_one_of_mem_W2` で
  W₁-因子 = 1 → 値 = χ₂(wSnd (e w)) i-free ✓。
- **(L1') fst の χ₂-独立性**: 対称 (wSnd_eq_one_of_mem_W1、値 = w1CharEquiv i (wFst…))。
- **(L2) 列単射 (snd)**: χ₂ ≠ χ₂' → snd 成分相異。
  `omegaProdEquiv_symm_omegaProdCharTic_ne` (S06:既存、pair-ne) + (L1') fst 一致 → snd 相異 ✓。
⚠ ticVdiff h の W₁/W₂ は h.tic の fields (ticVdiff は tic の W-系を再利用) — subgroupOf の
基準が (ticVdiff h).W = h.tic.W で一致することを確認しつつ書く。
**進捗⁶ (df0cc78a)**: ~~L1/L1'/L2~~ **DONE** (+ 橋像帰属 helper 2 本、Hypothesis46-generic)。
⚠ (ticVdiff h).W ≡ h.tic.W の型 spelling 差 → **erw** 必須。
**残 = endgame 適用本体 1 本** (`typeII_nu_tau2_dichotomy`): kcol/jcol := 成分 (L1 で
well-defined)、σ-coeff 計算、S05 endgame 呼び出し、逆翻訳。
endgame 適用の残り組立は本 note 直上のチェックリスト通り
(E-Finset → T := 添字 preimage、coeff 計算 = sigmaCoeff_psi_eq (S06:515) の
chiFam_spec .2.2.1 pattern、hδ = (columnFamily χ₂).sign + sign_eq)。
その後 = obligation 2(b) (S↔M grid transpose、0098 item 1 → 9000 claim) + obligation 3
((8.18.b) disjointness) — dichotomy が landed すれば `exists_typeIICrossIsometryData` の
残 gap はこの 2 つ。

### 2026-07-10 update⁹ — ★★ typeII_T2_coherent LANDED (408e9650) — obligation 1 完成

**T2 = {λ,λ̄,ν,ν̄} の (5.7) coherence が sorry-free/axiom-clean で閉じた** (τ₂ の存在 =
`exists_typeIICrossIsometryData` obligation 1 の実体)。update⁸ checklist 全項目実行済:
家族 bookkeeping 5 本 + R-dispatch (`typeII_T2_memberRFamily` + imageSet 抽出 2 本) +
hRorth (`typeII_T2_memberRFamily_orthogonal`、2×2) + engine 呼び出し (`typeII_T2_coherent`)。
file hygiene: 1799 行 > 1500 → (8.16) DadeBase を `S12_TypeIIDadeBase.lean` へ prefix-split
(a882fc09、下流不変、full build 4132 green)。

⚠ Lean 知見 (再発防止): S08 の `{x : IrreducibleCharacter}` implicit に plain な
ClassFunction を関連付ける呼び出しは `↑?x ≡ φ` 非 pattern unification で whnf 1.6M 爆発 —
**bundled 引数は named-arg で explicit 渡し** `(x := ⟨φ, hφirr⟩)`。dispatch def の
choice-extract は `let χ₂ := hex.choose` + have 束縛 (rw motive 依存切り、S13 pattern)。

**残 obligations (update⁵ の 2-3、いずれも genuine 新規)**:
2. **(5.8) S-side pin + shared grid**: τ₂(ν) = ±Σ_j ω^{aligned}_{r'j}。
   (a) τ₂ と τ_S の supported-agreement + (3.7) 係数 rigidity で τ₂(ν) を S-grid 列和に pin
   (M-side template = 自レーン既証明の `exists_muColumn_tau1_eq_sum_R` → `muColumn_tau1_pin`
   chain、S12_Core)。**T2-coherence が landed した今、certainTypeR.image_eq が
   τ_S(ν−ν̄) = Σ R(ν) を既に供給**している点が M-side との差 (入口が軽い)。
   (b) S-grid = M-grid transpose ((8.8) pair S∩M=W + (3.2) σ-uniqueness) — 真の deep、
   typeP_pair 圏 (0098 item 1 未 claim → 着手時 9000 claim)。
3. **(8.18.b) disjointness**: Disjoint Ã₁(M) Ã(S) → cross_zero/zeta_lam_ortho。
   engine 部品 landed (`disjoint_conjugatesIntoSet_of_centralizer` 等、update⁵ 参照)。
上流優先: 2(a) → 2(b)/3。

### 2026-07-10 update⁸ — hRorth core LANDED (bfb1c48d) + T2 assembly checklist (次 iteration)

**LANDED (sorry-free/axiom-clean)**: `typeII_tau_apply_eq_zero_of_mem_ticVdiffV` (V-vanishing
anchor、(2.5) base-point 評価 + `typePData_typePV_not_mem_derived`) +
`typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff` (R(μ_j)⊥R(χ)、S13 _typeP 版 mirror) +
`typeIIHypothesis46_dade0_hConjInvariant`。
⚠ Lean 技術 crumb: proof 内 `set h46 := typeIIHypothesis46 …` は goal の occurrence を fold
できず後続 rw が全滅 — S13 同様 **full term 通貫**が正 (python \bh46\b 展開で解決)。

**残 = T2 assembly 一本** (`typeII_T2_coherent`、engine 呼び出し)。checklist:
- **hRorth dispatch**: 対象 pair は irr×col / col×irr のみ (conj-pair は precondition
  `inner φ ξ = 0 ∧ inner φ ξ.conj = 0` で自動除外 — (λ,λ̄): ⟨λ,λ̄.conj⟩=⟨λ,λ⟩=1≠0 /
  (ν,ν̄) 同様)。col×irr は landed lemma の swap (inner_conj_symm + star_zero)。
- **R-dispatch def**: 4-case dite (Classical、η = lam / lam.conj / nu / nu.conj) +
  eq-transport。imageSet 抽出 lemma を dif_pos/dif_neg で 4 本 (S13 の rebuild pattern 参照;
  ▸ の imageSet は subst で処理可)。R(λ/λ̄) = `dadeOrthonormalCharacterImageFamilyOfDiff
  h46.dade0 (typeIIHypothesis46_dade0_hConjInvariant …)` / R(ν) = 分類
  (`typeII_reducible_inducedKernelFamily_eq_columnSum` choice-extract) → `certainTypeR`
  (hdeg = `columnSum_inv_apply_one`) / R(ν̄) = χ₂⁻¹ 版 (ν̄ = columnSum χ₂⁻¹ via
  `columnSum_conj_eq`; (χ₂⁻¹)⁻¹ = χ₂ は inv_inv)。
- **T2 ⊆ IKF**: λ,ν = `typeII_sOf_subset_inducedKernelFamily` (landed)、bars =
  `S08.inducedKernelFamily_closedUnderConjugate` (名要確認)。
- **horth** = `S08.inducedKernelFamily_pairwise_orthogonal` / **hnr** =
  `S08.inducedKernelFamily_hasNoRealCharacters` (Odd |S| = hG.odd.of_dvd_nat) / bars は
  conj_conj + symm で還元。
- **hsuppdiff**: 汎用 helper 1 本 (`ha : a.supp ⊆ A∪{1} → hb → a1=b1 → (a−b).supp ⊆ A` —
  landed `typeII_sSet_diff_support_subset` の proof を抽象化) + member-support 4 本
  (λ,ν = landed `typeII_sSet_member_support_subset`、bars = conj は support 不変
  (`conj_apply`+`star_eq_zero` — landed `typeII_sSet_member_diffsupp` の hsupp_eq pattern))
  + A(S)→A₀ mono。degree: bars の deg = star(deg) = deg
  (`irreducibleCharacter_apply_one_eq_pos_natCast` for source ξ + `induceHU_apply_one_eq_q_mul`
  + star_natCast — landed member_diffsupp と同 pattern)。
- **hN** = ⟨1, irreducibleCharacter_inner_eq_ite…⟩ / **hdeg0** = q·ξ(1) natCast ≠ 0 /
  **h1A**: 1 ∉ supportInSubgroup A₀ S (mem_supportInSubgroup + A₀ 各部の ≠1) /
  **hη₂** = ν (≠ λ: irr vs red)。
- **hiso** = `S07.dadeIntegralCharacterMap_inner_eq_on_supported_span` +
  `S07.support_subset_of_mem_zSupportedSpan` / **hZdiff** =
  `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` + `S08.inducedKernelFamily_mem_ZIrr`
  (S13:1534-1542 の mirror)。
- statement: `Nonempty (S07.IsCoherent (S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
  {lam, lam.conj, nu, nu.conj} (S04.supportInSubgroup (A(S) ∪ conjClassSetIn S (typePV S
  data.typeP)) S))` + [NeZero (Nat.card h46.W1)] binder (consumer 供給は one_lt_card_W1)。
  ⚠ full term 通貫 (set 禁止)。⚠ maxHeartbeats 前例 S13:1466。

### update⁵ 補遺² — S-side Dade の support-set 選定 (次 iteration の最初の判断)
- **A₁(S) = S_F^# の TI は即座に取れる**: `TypePNontrivialCore` が kernel-sharp TI を
  field で保持 (`typeP_core_centralizer_le_of_mem_fitting` の hTI destructure) +
  `maximalSubgroup_eq_normalizer_maxNilpotentNormalHall` ⟹ `IsTISubset (S_F^#) S` は
  数行。`of_isTISubset` (H(a)=⊥) で `S04.Hypothesis G (S_F^#) S` が立つ。
- **⚠ full A(S)/A₀(S) の TI は旧 `typeII_A_sets_TI` が FALSE-as-stated で撤去済み**
  (S10_StructureSetup:524 コメント、faithful content = BG
  `theoremB_A_minus_Msigma_isTISubset`)。A(S)-level が要るなら BG 側 statement 経由。
- **先に決めるべきこと = T2-差分の support**: Peterfalvi (8.15) は
  Supp(ℤ[𝒯,S^#]) ⊆ A(S) (full)。差分 λ−ν が A₁(S)=S_F^# に落ちるかは非自明
  (Ind の U-part 値)。lane-b の §13-S instance は `sSet_member_support_subset_A`
  (support ⊆ honestTypeP2ASet ∪ {1}) を証明済 — その証明が一般 type-II S に
  instantiate できるか (S15.Hypothesis 依存部の除去) を最初に確認し、
  (a) A₁-TI Dade で足りる形に支持集合を絞れるなら最軽、
  (b) 足りなければ honest A(S) + BG theoremB-TI 経由。
