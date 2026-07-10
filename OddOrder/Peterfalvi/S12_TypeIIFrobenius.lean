/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_Section9Counts
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S04_DadeIsometryBasic
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TheoremsAE
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TaxonomyOutput
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeBridges
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting.Basics

/-!
# Peterfalvi (10.7): the Type-II `HU`-Frobenius dichotomy assembly

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 10, pp. 58--59, Theorem (10.7); Coq mirror `Frob_der1_type2`
(`coq/theories/PFsection10.v:549-658`).

Under Hypothesis (10.4) (the type-`P₁` maximal `M` with its coherent extension `τ₁`),
every Type-II maximal subgroup `S` of `G` has `[S,S] = S_F ⋊ U` a **Frobenius group with
kernel `S_F`**.  The proof splits on the `S`-side §9 Clifford dichotomy
(Coq `typeP_reducible_core_cases`):

* **Exceptional (right) branch** — `𝒮(H₀C')` has no irreducible of degree `q·u`: then
  `C = ⊥`, `U` is cyclic, and the type-II `HU`-Frobenius conclusion is immediate
  (`S11.exceptional_case_frobenius_realization`, proven).
* **Reducible-core (left) branch** — an irreducible `λ ∈ 𝒮(H₀)` and a reducible
  `ν ∈ 𝒮(H₀)` of equal degree `q·u` exist: this is **refuted** by the cross-isometry
  computation of (10.7): the 4-element family `T2 = {λ, λ̄, ν, ν̄}` is coherent by (5.7)
  with an extension `τ₂`; (5.8) pins `ν^{τ₂}` to a signed `ω^σ`-row-sum of the grid
  **shared** with `M` (the (8.8) pair structure `S ∩ M = W`); the Dade supports
  `Ã₁(M)` and `Ã(S)` are disjoint ((8.18.b) via (8.13.c4), since `M` is not Frobenius
  with kernel `M_F`), so `⟨α^τ, β^{τ_S}⟩ = 0` for `α = μ_s − d·ζ`, `β = ν − λ`; expanding
  through the proven `M`-side (10.6.a) pin `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`
  (`Hypothesis.muColumn_tau1_pin`) leaves the single shared grid entry
  `±⟨ω_{r's}^σ, ω_{r's}^σ⟩ = ±1 ≠ 0` — contradiction.

The left-branch cross facts (τ₂-coherence of `T2`, the `S`-side (5.8) row identity against
the shared grid, the (4.1)/(5.3.b) orthogonality of `λ^{τ₂}`, `ζ^{τ₁}` to the grid and to
each other, and the (8.18.b)-based `⟨α^τ, β^{τ_S}⟩ = 0`) are bundled as the explicit
carrier `TypeIICrossIsometryData`, produced by the (sorried) named gate
`exists_typeIICrossIsometryData` — see its docstring for the precise provenance of each
obligation.  The contradiction consumer (`TypeIICrossIsometryData.elim`) and the dichotomy
assembly (`typeII_HU_frobenius_of_coherent`) are proven.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-! ## Peterfalvi (8.16): the `S`-side Dade base for a Type-II maximal

The (10.7) left branch needs the Dade isometry `τ_S` of the pair `(A(S), S)` for the Type-II
maximal `S`, where `A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#` is the honest (8.10) type-`P` support
(`centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)`; the §9 family differences are
`A(S)`-supported by (8.15)/(4.7), and the equal-degree difference `ν − λ` vanishes at `1`).

Peterfalvi proves (8.16) — `A₀(S), A(S), A₁(S)` are TI-subsets of `G` with normalizer `S` — by
checking that every (8.14) signalizer `R(a)` is trivial and citing (2.3).  We instead assemble
the TI property of `A(S)` directly from three proven ingredients, avoiding the (8.15) signalizer
machinery altogether (all signalizers being trivial, Hypothesis (2.2) is `of_isTISubset`):

* on `A₁(S) = S_F^#` the (8.6.a) kernel TI-property (`TypePNontrivialCore`, with
  `N_G(S_F) = S` by maximality and simplicity);
* on `A(S) − A₁(S)` the BG Theorem B(5) TI-subset `A(M) − M_σ`
  (`theoremB_A_minus_Msigma_isTISubset`, transported through `A(S) ⊆ ASet S U` for a
  `(κ∪σ)'`-Hall `U` with `S' = U ⊔ S_σ`, BG Lemma 15.1(b) via `typeP_exists_hall_derived_eq`);
* no cross fusion: `S_σ`-membership of an element of `S` is determined by its order
  (`mem_Msigma_iff_isPiElement_sigma` + `isPiElement_conj`), so a `G`-conjugation cannot move a
  point between `A₁(S)` and `A(S) − A₁(S)`.

The type-II specialization enters through `S_F = S_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`) and `IsTypeP S` (`isTypeP_of_isTypeNonI`);
no `II → P₂` taxonomy bridge is needed. -/

section DadeBase

open OddOrder.BG.Ch3.S10

/-- **Peterfalvi (8.16), TI part, for the honest type-II `A(S)`**: for a Type-II maximal
subgroup `S`, the (8.10) support `A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#` is a TI-subset of `G` with
normalizer bound `S`.

The proof splits a conjugation `g·a·g⁻¹ = b` with `a, b ∈ A(S)` by `S_σ`-membership: both in
`A₁(S) = S_σ^# = S_F^#` is the (8.6.a) kernel TI-property; both outside is BG Theorem B(5)
(`A(S) − S_σ ⊆ ASet S U − S_σ`, a TI-subset); and the mixed cases are impossible because
`S_σ`-membership inside `S` depends only on the element's order. -/
theorem typeII_centralizerSupport_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    OddOrder.GroupTheory.IsTISubset
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
  classical
  obtain ⟨iiData⟩ := id hSII
  obtain ⟨-, -, hTI⟩ := iiData.common
  -- `S_F = S_σ` (type II) and `S_F ≠ ⊥`.
  have hMσF : maxNilpotentNormalHall S = Msigma S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hSmax
      (Or.inr hSII)
  have hFne : maxNilpotentNormalHall S ≠ ⊥ := by
    rw [hMσF]; exact Msigma_ne_bot hG hSmax
  -- `N_G(S_F) = S`: `S` normalizes its normal Hall core, the normalizer is proper (simplicity),
  -- and `S` is a coatom.
  have hNS : Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) = S := by
    have hle : S ≤ Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) := by
      intro s hs
      rw [hMσF, Msigma]
      exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (sigma S) S hs
    by_contra hne
    have hNtop : Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) = ⊤ :=
      hSmax.2 _ (lt_of_le_of_ne hle fun h => hne h.symm)
    haveI hHnormal : (maxNilpotentNormalHall S).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall S) hHnormal with hb | ht
    · exact hFne hb
    · exact hSmax.1
        (top_le_iff.mp (ht ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le S))
  -- `IsTypeP S` and a `(κ∪σ)'`-Hall `U` with `S' = U ⊔ S_σ` (BG Lemma 15.1(b)), plus a
  -- `κ(S)`-Hall `K` (Hall's theorem in the solvable `S`), feeding Theorem B(5).
  have hP : OddOrder.BG.Ch4.S14.IsTypeP S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)
  obtain ⟨U, hU, hder⟩ := OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hSmax hP
  have hUM : U ≤ S :=
    (le_sup_left.trans hder.ge).trans (Subgroup.map_subtype_le _)
  haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hSmax
  obtain ⟨K', hK'⟩ :=
    OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
  have hKM : K'.map S.subtype ≤ S := Subgroup.map_subtype_le K'
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S)
      ((K'.map S.subtype).subgroupOf S) := by
    have hKeq : (K'.map S.subtype).subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    rw [hKeq]; exact hK'
  have hTIB := OddOrder.BG.Ch4.S16.theoremB_A_minus_Msigma_isTISubset hG hSmax hKM hUM hK hU
  -- the conjugation `g·a·g⁻¹ ∈ A(S)` for `a ∈ A(S)`, split by `S_σ`-membership.
  rintro g ⟨a, ha, hga⟩
  obtain ⟨haM', ha1, z, hzσ, hzC⟩ := ha
  obtain ⟨hgaM', hga1, w, hwσ, hwC⟩ := hga
  have haS : a ∈ S := Subgroup.map_subtype_le _ haM'
  have hgaS : g * a * g⁻¹ ∈ S := Subgroup.map_subtype_le _ hgaM'
  by_cases haσ : a ∈ Msigma S
  · by_cases hgaσ : g * a * g⁻¹ ∈ Msigma S
    · -- both in `A₁(S) = S_F^#`: the (8.6.a) kernel TI-property.
      have hg := hTI g ⟨a,
        ⟨by rw [hMσF]; exact SetLike.mem_coe.mpr haσ, by simpa using ha1⟩,
        ⟨by rw [hMσF]; exact SetLike.mem_coe.mpr hgaσ, by simpa using hga1⟩⟩
      rwa [hNS] at hg
    · -- `a ∈ S_σ`, `g·a·g⁻¹ ∉ S_σ`: impossible, `S_σ`-membership is order-determined.
      exact absurd
        ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax hgaS).mpr
          (OddOrder.BG.Ch4.S14.isPiElement_conj g
            ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax haS).mp haσ)))
        hgaσ
  · by_cases hgaσ : g * a * g⁻¹ ∈ Msigma S
    · -- `a ∉ S_σ`, `g·a·g⁻¹ ∈ S_σ`: the same order argument along `g⁻¹`.
      refine absurd ?_ haσ
      have hπ := OddOrder.BG.Ch4.S14.isPiElement_conj g⁻¹
        ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax hgaS).mp hgaσ)
      rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at hπ
      exact (OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax haS).mpr hπ
    · -- both in `A(S) − S_σ ⊆ ASet S U − S_σ`: BG Theorem B(5).
      have hmem : ∀ {y : G}, y ∈ S → y ∈ derivedInG S →
          ∀ {x : G}, x ∈ sharpSubgroup (Msigma S) → y ∈ Subgroup.centralizer ({x} : Set G) →
          y ∉ Msigma S →
          y ∈ OddOrder.BG.Ch4.S16.ASet S U \ ((Msigma S : Subgroup G) : Set G) := by
        intro y hyS hyM' x hxσ hxC hyσ
        refine ⟨⟨⟨hyS, fun hbot => ?_⟩, ?_⟩, fun h => hyσ (SetLike.mem_coe.mp h)⟩
        · have hxmem : x ∈ Msigma S ⊓ Subgroup.centralizer ({y} : Set G) :=
            Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hxσ.1, by
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm⟩
          rw [hbot, Subgroup.mem_bot] at hxmem
          exact hxσ.2 (Set.mem_singleton_iff.mpr hxmem)
        · exact SetLike.mem_coe.mpr (hder ▸ hyM')
      exact hTIB g ⟨a, hmem haS haM' hzσ hzC haσ, hmem hgaS hgaM' hwσ hwC hgaσ⟩

/-- The honest type-II support `A(S)` is `S`-conjugation stable (both `S' = derivedInG S` and
`S_σ = Msigma S` are normalized by `S`); the `hL_norm` input of Hypothesis (2.2). -/
theorem centralizerSupport_sharpMsigma_conj_mem [Finite G] {S : Subgroup G} {m : G}
    (hm : m ∈ S) {y : G}
    (hy : y ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) :
    m * y * m⁻¹ ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := by
  obtain ⟨hyM', hy1, x, hxσ, hyC⟩ := hy
  have hmM' : m ∈ Subgroup.normalizer ((derivedInG S : Subgroup G) : Set G) :=
    OddOrder.BG.Ch3.S10.le_normalizer_derivedInG S hm
  have hmMσ : m ∈ Subgroup.normalizer ((Msigma S : Subgroup G) : Set G) := by
    rw [Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (sigma S) S hm
  refine ⟨(Subgroup.mem_normalizer_iff.mp hmM' y).mp hyM',
    fun h => hy1 (by
      have hyeq : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hyeq, h]; group),
    m * x * m⁻¹, OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem hmMσ hxσ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
  calc m * y * m⁻¹ * (m * x * m⁻¹) = m * (y * x) * m⁻¹ := by group
    _ = m * (x * y) * m⁻¹ := by rw [hyC]
    _ = m * x * m⁻¹ * (m * y * m⁻¹) := by group

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.16) ⇒ Hypothesis (2.2) for `(A(S), S)`, Type II**: the honest type-II Dade
base.  All (8.14) signalizers are trivial — `A(S)` is a TI-subset
(`typeII_centralizerSupport_isTISubset`) — so Hypothesis (2.2) is `of_isTISubset` with
`H(a) = ⊥`.  This is the `τ_S` foundation of the (10.7) left branch: the coherence engine
(5.7) runs over the Dade isometry of this hypothesis. -/
noncomputable def typeIIDadeHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    OddOrder.Peterfalvi.S04.Hypothesis G
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    (fun _y hy => OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, hy.2.1⟩)
    (fun _y hy => Subgroup.map_subtype_le _ hy.1)
    (fun l _a ha => centralizerSupport_sharpMsigma_conj_mem l.2 ha)
    (typeII_centralizerSupport_isTISubset hG hSmax hSII)

/-- **Peterfalvi (8.16), centralizer containment**: `C_G(y) ≤ S` for every point of the
type-II support `A(S)` (the "(8.16): `C_G(y) ⊆ S` for all `y ∈ A(S)`" form that (12.10)
cites).  Immediate from the TI property: any `c ∈ C_G(y)` fixes `y ∈ A(S) ∩ A(S)^c`. -/
theorem typeII_centralizer_le_of_mem_centralizerSupport [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) {y : G}
    (hy : y ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) :
    Subgroup.centralizer ({y} : Set G) ≤ S := by
  intro c hc
  refine typeII_centralizerSupport_isTISubset hG hSmax hSII c ⟨y, hy, ?_⟩
  have hcy : c * y * c⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  rw [hcy]; exact hy

open scoped Classical FiniteInduce in
/-- The (8.16) Dade hypothesis has every signalizer `H(a) = ⊥` (by construction,
`of_isTISubset`), so the kernel assignment is trivially `S`-conjugation invariant — the
`hconj` input of the §4 full Dade isometry (2.6). -/
theorem typeIIDadeHypothesis_hConjInvariant [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    (typeIIDadeHypothesis hG hSmax hSII).HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped Classical FiniteInduce in
/-- **The (10.7) `S`-side Dade base map `τ_S`**: the §4 Dade isometry of the (8.16) hypothesis
`(A(S), S)`, lifted to a total `IntegralCharacterMap ↥S G`.  On `A(S)`-supported class
functions it is the honest (2.5) Dade map (`S07.dadeIntegralCharacterMap_apply_of_support`);
its (2.6.a) isometry and (2.6.b) `ℤ[Irr]`-preservation on the supported sublattice are supplied
by the generic `S07.dadeIntegralCharacterMap_inner_eq_on_supported_span` /
`S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` at the hypothesis
`typeIIDadeHypothesis hG hSmax hSII` with `hconj = typeIIDadeHypothesis_hConjInvariant …`.
This is the map the (5.7) engine (`S07.uniform_degree_coherence_of_families`) runs over in the
(10.7) left branch. -/
noncomputable def typeIITau [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIDadeHypothesis hG hSmax hSII)
    ((typeIIDadeHypothesis hG hSmax hSII).fullDadeIsometryData
      (typeIIDadeHypothesis_hConjInvariant hG hSmax hSII))

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **Peterfalvi (4.7)/(8.15), §9-family induced support, type-II instance**:
`Supp (Ind_{HU}^S ξ) ⊆ A(S) ∪ {1}` for every `ξ ∈ 𝒳` (the (9.5) family, `H ⊄ Ker ξ`), with
`A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#` the honest (8.10) type-II support.

Generic (`TypesIIIIIIVSetup`-level) mirror of the `S15.Hypothesis`-locked
`sSet_member_support_subset_A` (whose proof this replays; the S15 instance is downstream of
this file):

* `support_induce_subset_conjugatesIntoSet`: a nonvanishing point of `Ind_{HU}^S ξ` is
  `S`-conjugate to a nonvanishing point `w ∈ HU` of `ξ`;
* the (1.2) core (`irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`,
  contrapositive) forces a nontrivial `d ∈ H` centralizing `w`; the chain
  `H = S_F = S_σ` (`TypePData.H_eq` + `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`)
  makes `d` an `S_σ^#`-witness, so `w ∈ A(S)` (`w ∈ HU = S'` by
  `huSub_eq_derivedInG_subgroupOf`);
* `A(S)` is `S`-conjugation invariant (`centralizerSupport_sharpMsigma_conj_mem`), so the
  original point lies in `A(S) ∪ {1}` too. -/
theorem typeII_sSet_member_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : TypesIIIIIIVSetup S)
    {ξ : IrreducibleCharacter ↥(huSub data)} (hξ : ξ ∈ xiSet data) :
    (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S ∪ {1} := by
  classical
  -- `H = S_F = S_σ` (type II).
  have hHσ : data.H = Msigma S := by
    show data.typeP.H = Msigma S
    rw [data.typeP.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG
      hSmax (Or.inr hSII)
  -- the (1.2) core: a nonvanishing `w ∈ HU` with `(w:S:G) ≠ 1` lies in `A(S)`.
  have hcore : ∀ w : ↥(huSub data),
      (ξ : ClassFunction ↥(huSub data) ℂ) w ≠ 0 → ((w : ↥S) : G) ≠ 1 →
      ((w : ↥S) : G) ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := by
    intro w hwval hwne
    haveI := hInHu_normal data
    have hCne : OddOrder.Peterfalvi.S03.centralizerInSubgroup (hInHu data) w ≠ ⊥ := fun hbot =>
      hwval
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
          ξ hξ hbot)
    obtain ⟨d, hd_mem, hd_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
    rw [OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup] at hd_mem
    obtain ⟨hd_H, hd_comm⟩ := hd_mem
    -- `d`'s ambient image lies in `H = S_σ`, is nontrivial, and commutes with `w`.
    have hdS_H : (d : ↥S) ∈ data.H.subgroupOf S := (Subgroup.mem_subgroupOf).mp hd_H
    have hdH_G : ((d : ↥S) : G) ∈ data.H := (Subgroup.mem_subgroupOf).mp hdS_H
    have hdG_ne : ((d : ↥S) : G) ≠ 1 := fun he => hd_ne (by
      apply Subtype.ext; apply Subtype.ext; exact he)
    have hcommG : ((d : ↥S) : G) * ((w : ↥S) : G) = ((w : ↥S) : G) * ((d : ↥S) : G) := by
      have := congrArg (fun t : ↥S => (t : G)) (Subtype.ext_iff.mp hd_comm)
      simpa using this
    -- assemble the `A(S)`-membership with witness `d ∈ S_σ^#`.
    refine ⟨?_, hwne, ((d : ↥S) : G), ?_, ?_⟩
    · have hwHU : (w : ↥S) ∈ (derivedInG S).subgroupOf S := by
        rw [← huSub_eq_derivedInG_subgroupOf]; exact w.2
      exact (Subgroup.mem_subgroupOf).mp hwHU
    · refine (Set.mem_sdiff _).mpr ⟨?_, fun he => hdG_ne (Set.mem_singleton_iff.mp he)⟩
      exact SetLike.mem_coe.mpr (hHσ ▸ hdH_G)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommG.symm
  -- assemble via `support_induce_subset_conjugatesIntoSet` + conjugation invariance.
  intro x hx
  rw [Set.mem_union, Set.mem_singleton_iff]
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  have hxsupp : (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx_conj : x ∈ ClassFunction.conjugatesIntoSet (huSub data)
      ((ξ : ClassFunction ↥(huSub data) ℂ)).support := by
    have hind : induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ξ : ClassFunction ↥(huSub data) ℂ) := rfl
    refine ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) ?_
    rw [← hind]; exact hxsupp
  rw [ClassFunction.mem_conjugatesIntoSet] at hx_conj
  obtain ⟨c, hc, hcsupp⟩ := hx_conj
  set w : ↥(huSub data) := ⟨c⁻¹ * x * c, hc⟩ with hw_def
  have hw_val : (ξ : ClassFunction ↥(huSub data) ℂ) w ≠ 0 := ClassFunction.mem_support.mp hcsupp
  have hxeq : (x : G) = (c : G) * ((w : ↥S) : G) * (c : G)⁻¹ := by
    show (x : G) = (c : G) * ((c : G)⁻¹ * (x : G) * (c : G)) * (c : G)⁻¹
    group
  have hwne : ((w : ↥S) : G) ≠ 1 := by
    intro he
    apply hx1
    have hxG : (x : G) = 1 := by rw [hxeq, he]; group
    exact Subtype.ext hxG
  have hwA : ((w : ↥S) : G) ∈
      centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := hcore w hw_val hwne
  refine Or.inl ?_
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hxeq]
  exact centralizerSupport_sharpMsigma_conj_mem c.2 hwA

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **Equal-degree §9-family differences are `A(S)`-supported** (the (5.7) engine's
`hsuppdiff` input for the (10.7) `T2`-family): for `ξ, η ∈ 𝒳` whose inductions share a degree,
`Supp (Ind ξ − Ind η) ⊆ A(S)` as an `↥S`-support.  Each member's support lies in
`A(S) ∪ {1}` (`typeII_sSet_member_support_subset`) and the equal degrees kill the `1`-point. -/
theorem typeII_sSet_diff_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : TypesIIIIIIVSetup S)
    {ξ η : IrreducibleCharacter ↥(huSub data)}
    (hξ : ξ ∈ xiSet data) (hη : η ∈ xiSet data)
    (hdeg : induceHU data (ξ : ClassFunction ↥(huSub data) ℂ) 1
      = induceHU data (η : ClassFunction ↥(huSub data) ℂ) 1) :
    ((induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
        - induceHU data (η : ClassFunction ↥(huSub data) ℂ)).support)
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
  intro x hx
  have hx0 : (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
      - induceHU data (η : ClassFunction ↥(huSub data) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx1 : x ≠ 1 := by
    intro he
    apply hx0
    rw [he, ClassFunction.sub_apply, hdeg, sub_self]
  have hmem : x ∈ (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)).support ∪
      (induceHU data (η : ClassFunction ↥(huSub data) ℂ)).support :=
    ClassFunction.support_sub_subset _ _ hx
  rcases hmem with h | h
  · rcases typeII_sSet_member_support_subset hG hSmax hSII data hξ h with h' | h'
    · exact h'
    · exact absurd (Set.mem_singleton_iff.mp h') hx1
  · rcases typeII_sSet_member_support_subset hG hSmax hSII data hη h with h' | h'
    · exact h'
    · exact absurd (Set.mem_singleton_iff.mp h') hx1

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **(5.3.a) conjugate-difference support, type-II instance**: `Supp ((Ind ξ)̄ − Ind ξ) ⊆ A(S)`
as an `↥S`-support — the `hdiffsupp` input of the irreducible members' `R`-data
(`S07.dadeCharacterDifferenceImageOfDiff`).  The conjugate has the same support, and the
difference vanishes at `1` (the degree `q·ξ(1)` is a positive natural, self-conjugate). -/
theorem typeII_sSet_member_diffsupp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : TypesIIIIIIVSetup S)
    {ξ : IrreducibleCharacter ↥(huSub data)} (hξ : ξ ∈ xiSet data) :
    ((induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)).conj
        - induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
  set φ : ClassFunction ↥S ℂ :=
    induceHU data (ξ : ClassFunction ↥(huSub data) ℂ) with hφ
  have hsupp_eq : φ.conj.support = φ.support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : (φ.conj - φ) x ≠ 0 := hx
  have hxsupp : x ∈ φ.support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases typeII_sSet_member_support_subset hG hSmax hSII data hξ (hφ ▸ hxsupp) with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ :=
      OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
    apply hx0
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hφ, induceHU_apply_one_eq_q_mul, hd,
      star_mul', star_natCast, star_natCast, sub_self]

end DadeBase

/-! ## Peterfalvi (8.16) ⇒ Hypothesis (4.6) for `(A(S), S)`: the `S`-side certain-type instance

The (10.7) left branch runs the (5.7) engine over the reducible column family `R(ν)`
(`S06.certainTypeR`), which consumes an `S06.Hypothesis46 (A(S)) S` — Peterfalvi's "(8.15):
Hypothesis (4.6) holds with `L = S`, `K = S'`, `A = A(S)`, `A₀ = A₀(S)`, `H = S_F`" for the
Type-II maximal `S`.  The `M`-side precedent (`Hypothesis.toHypothesis46`) receives its
`A₀`-level Dade datum as a hoisted §10 field; here we *construct* it: Peterfalvi (8.16) claims
`A₀(S) = A(S) ∪ V^S` is also a TI-subset, and the three-case extension of the landed `A(S)`
argument proves it —

* `(A, A)`: the landed `typeII_centralizerSupport_isTISubset`;
* `(V^S, V^S)`: the (3.1)/(4.3.a) ambient TI property of `V` (`typePData_V_ti`, normalizer
  bound `W ≤ S`);
* mixed: **impossible** — `orderOf` separates the two parts.  `A(S) ⊆ (S')^#` consists of
  `π(S')`-elements, while an exceptional `v ∈ V` has a nontrivial `W₁`-component whose order
  is coprime to `|S'|` (the (4.2.a) Hall coprimality `typePData_W1_hall_coprime`), so
  `orderOf v ∤ |S'|` (`typePV_orderOf_not_dvd_card_derived`); conjugation preserves orders.

This mirrors the Coq `FTsupport0` definition (`BGsection16.v:194`), whose exceptional part is
the *order-characterized* set `{x ∈ M | x` neither a `π(M')`- nor a `π(M')'`-element`}` —
`FTsupp0_typeP` (`PFsection8.v:772`) identifies it with `V^M` for type-`P` maximals. -/

section Hypothesis46Instance

open OddOrder.BG.Ch3.S10

/-- **Type-`P` exceptional elements have order outside `π(M')`**: for `v ∈ V = W − (W₁ ∪ W₂)`,
`orderOf v ∤ |M'|`.

Decompose `v = a·b` along the cyclic (hence abelian) `W = W₁ ⊔ W₂`.  If `orderOf v` divided
`|M'|` it would be coprime to `w₁ = |W₁|` (the (4.2.a) Hall coprimality `hHall`), so
`v ∈ ⟨v^{w₁}⟩` (the power map by a coprime exponent preserves the cyclic subgroup); but
`v^{w₁} = a^{w₁}·b^{w₁} = b^{w₁} ∈ W₂` (Lagrange kills the `W₁`-component), forcing `v ∈ W₂` —
contradicting `v ∉ W₁ ∪ W₂`.

This is the conjugation-invariant separator between `A(S) ⊆ (S')^#` (whose elements are
`π(S')`-elements) and the exceptional part `V^S` of `A₀(S)` in the (8.16) TI argument; it is
the type-data form of the Coq `FTsupport0` order characterization (`BGsection16.v:194`). -/
theorem typePV_orderOf_not_dvd_card_derived [Finite G] {M : Subgroup G} (data : TypePData M)
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    {v : G} (hv : v ∈ typePV M data) :
    ¬ orderOf v ∣ Nat.card ↥(derivedInG M) := by
  intro hdvd
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, -, hvnW2⟩ := hv
  -- decompose `v = a·b` along `W = W₁ ⊔ W₂` (the cyclic `W` is abelian)
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab
    simpa using this
  -- `v^{w₁} = b^{w₁} ∈ W₂`: the `W₁`-part dies by Lagrange, the factors commute in `W`
  set w₁ := Nat.card ↥data.W1 with hw₁def
  have hcomm : Commute ((a : ↥data.W) : G) ((b : ↥data.W) : G) :=
    OddOrder.Peterfalvi.S06.commute_of_mem_of_isCyclic data.W_cyclic (hW1le haW1) (hW2le hbW2)
  have hapow : ((a : ↥data.W) : G) ^ w₁ = 1 := by
    have h1 : (⟨((a : ↥data.W) : G), haW1⟩ : ↥data.W1) ^ w₁ = 1 := pow_card_eq_one'
    have := congrArg (Subtype.val) h1
    simpa using this
  have hvpow : v ^ w₁ ∈ data.W2 := by
    rw [← habG, hcomm.mul_pow, hapow, one_mul]
    exact pow_mem hbW2 w₁
  -- coprimality: `orderOf v` is coprime to `w₁`, so `⟨v^{w₁}⟩ = ⟨v⟩ ∋ v`
  have hcop : (orderOf v).Coprime w₁ := hHall.coprime_dvd_left hdvd
  have hord : orderOf (v ^ w₁) = orderOf v := by
    rw [orderOf_pow, hcop.gcd_eq_one, Nat.div_one]
  have hzle : Subgroup.zpowers (v ^ w₁) ≤ Subgroup.zpowers v :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers v).pow_mem (Subgroup.mem_zpowers v) w₁)
  have hzeq : Subgroup.zpowers (v ^ w₁) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge hzle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzeq ▸ Subgroup.mem_zpowers v)
  exact hvnW2 (hk ▸ zpow_mem hvpow k)

/-- **Peterfalvi (8.16), TI part, for the full `A₀(S) = A(S) ∪ V^S`** of a Type-II maximal:
the (8.10) enlarged support `A₀(S) = A(S) ∪ conjClassSetIn S V` is a TI-subset of `G` with
normalizer bound `S`.

Four cases for `a, g·a·g⁻¹ ∈ A₀(S)`: both in `A(S)` is the landed
`typeII_centralizerSupport_isTISubset`; both in `V^S` reduces (conjugating the `S`-parts away)
to the ambient (3.1) TI property `V ∩ V^h ≠ ∅ → h ∈ W` (`typePData_V_ti`) with `W ≤ S`; and
the mixed cases are impossible because conjugation preserves element orders while `orderOf`
separates `A(S)` from `V^S` (`typePV_orderOf_not_dvd_card_derived`). -/
theorem typeII_A0_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.GroupTheory.IsTISubset
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S := by
  classical
  have hP : OddOrder.BG.Ch4.S14.IsTypeP S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)
  have hHall := typePData_W1_hall_coprime hG hSmax hP data
  have hWle : data.W ≤ S := typePData_W_le_self data
  -- the order separator: `A(S)`-elements have order dividing `|S'|`, `V^S`-elements do not
  have hAord : ∀ {x : G}, x ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) →
      orderOf x ∣ Nat.card ↥(derivedInG S) := by
    intro x hx
    have h1 := orderOf_dvd_natCard (⟨x, hx.1⟩ : ↥(derivedInG S))
    rwa [← Subgroup.orderOf_coe] at h1
  have hVord : ∀ {x : G}, x ∈ conjClassSetIn S (typePV S data) →
      ¬ orderOf x ∣ Nat.card ↥(derivedInG S) := by
    rintro x ⟨t, htV, h, -, rfl⟩
    have hoeq : orderOf (h * t * h⁻¹) = orderOf t := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulEquiv.injective _) t
      simpa [MulAut.conj_apply] using this
    rw [hoeq]
    exact typePV_orderOf_not_dvd_card_derived data hHall htV
  have horder : ∀ (g x : G), orderOf (g * x * g⁻¹) = orderOf x := by
    intro g x
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) x
    simpa [MulAut.conj_apply] using this
  rintro g ⟨a, ha, hga⟩
  rcases ha with haA | haV
  · rcases hga with hgaA | hgaV
    · -- `(A, A)`: the landed (8.16) `A(S)`-TI
      exact typeII_centralizerSupport_isTISubset hG hSmax hSII g ⟨a, haA, hgaA⟩
    · -- `(A, V^S)`: impossible by the order separator
      exact absurd (horder g a ▸ hAord haA) (hVord hgaV)
  · rcases hga with hgaA | hgaV
    · -- `(V^S, A)`: impossible by the order separator
      exact absurd (horder g a ▸ hAord hgaA) (hVord haV)
    · -- `(V^S, V^S)`: the ambient (3.1) `V`-TI, then `W ≤ S`
      obtain ⟨t, htV, s, hsS, rfl⟩ := haV
      obtain ⟨t', ht'V, s', hs'S, heq⟩ := hgaV
      have hconj : (s'⁻¹ * g * s) * t * (s'⁻¹ * g * s)⁻¹ = t' := by
        have h3 : s' * ((s'⁻¹ * g * s) * t * (s'⁻¹ * g * s)⁻¹) * s'⁻¹
            = s' * t' * s'⁻¹ := by
          rw [heq]; group
        exact mul_left_cancel (mul_right_cancel h3)
      have hmemW : s'⁻¹ * g * s ∈ data.W :=
        OddOrder.Peterfalvi.S10.typePData_V_ti data (s'⁻¹ * g * s)
          ⟨t, htV, hconj ▸ ht'V⟩
      have hgeq : g = s' * (s'⁻¹ * g * s) * s⁻¹ := by group
      rw [hgeq]
      exact S.mul_mem (S.mul_mem hs'S (hWle hmemW)) (S.inv_mem hsS)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.16) ⇒ Hypothesis (2.2) for `(A₀(S), S)`, Type II**: the honest type-II Dade
base on the *enlarged* support `A₀(S) = A(S) ∪ V^S`.  All (8.14) signalizers are trivial —
`A₀(S)` is a TI-subset (`typeII_A0_isTISubset`) — so Hypothesis (2.2) is `of_isTISubset` with
`H(a) = ⊥`.  This is the `dade0` datum of the `S`-side Hypothesis (4.6)
(`typeIIHypothesis46`), over which the reducible-column `R`-family `S06.certainTypeR` and its
Dade identities run. -/
noncomputable def typeIIDadeHypothesis0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.Peterfalvi.S04.Hypothesis G
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    (by
      rintro y (hy | ⟨t, htV, h, -, rfl⟩)
      · exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, hy.2.1⟩
      · refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, fun h1 => htV.2 ?_⟩
        have ht1 : t = 1 := by
          have hteq : t = h⁻¹ * (h * t * h⁻¹) * h := by group
          rw [hteq, h1]; group
        exact (Set.mem_union _ _ _).mpr (Or.inl (by
          rw [ht1]; exact SetLike.mem_coe.mpr data.W1.one_mem)))
    (by
      rintro y (hy | ⟨t, htV, h, hhS, rfl⟩)
      · exact Subgroup.map_subtype_le _ hy.1
      · exact S.mul_mem (S.mul_mem hhS (typePData_W_le_self data htV.1)) (S.inv_mem hhS))
    (by
      rintro l a (ha | ⟨t, htV, h, hhS, rfl⟩)
      · exact Or.inl (centralizerSupport_sharpMsigma_conj_mem l.2 ha)
      · exact Or.inr ⟨t, htV, (l : G) * h, S.mul_mem l.2 hhS, by group⟩)
    (typeII_A0_isTISubset hG hSmax hSII data)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.15) for Type II / the (10.7) sentence "Hypothesis (4.6) holds with `L = S`,
`K = S'`, `A = A(S)`, `A₀ = A₀(S)`, `H = S_F`"**: a Type-II maximal subgroup `S` instantiates
the §4/§6 Hypothesis (4.6) carrier `S06.Hypothesis46 (A(S)) S`, with the honest (8.10) support
`A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#`.

Field sources (mirroring the `M`-side `Hypothesis.toHypothesis46`, but with every Dade datum
*constructed* rather than hoisted):

* the (4.2) structural part: `typePData_toS06Hypothesis` (Hall coprimality from
  `typePData_W1_hall_coprime`, BG `IsTypeP` from `isTypeP_of_isTypeNonI`);
* the `A`-side Dade datum: the landed (8.16) `typeIIDadeHypothesis`;
* the ambient (3.1) TI-cyclic data (4.6.b): `typePData_toTICyclicHypothesis`, with the same
  `subgroupOf`-vs-ambient matching as the `M`-side (`Subgroup.map_subgroupOf_eq_of_le`, `rfl`);
* (4.6.c): `H := S_F` — the (10.7)/(8.15) choice for type II (`M`-side types III–V take
  `H = K`); `W₂ ≤ S_F` and `S_F ≤ S'` are the `TypePData` fields, normality is
  `S ≤ N_G(S_F)`;
* (4.6.d): the covering `⋃_{h∈S_F^#} C_{S'}(h)^# ⊆ A(S)` holds *by definition* of the honest
  `A(S)`: `S_F = S_σ` for type II (`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`), so
  every such element carries an `S_σ^#`-witness;
* (4.6.d)/(4.6.e): the `A₀`-side Dade datum and isometry are the (8.16) TI construction
  `typeIIDadeHypothesis0` (with the trivial-signalizer `hconj`), on
  `A(S) ∪ conjClassSetIn S V` — definitionally the required `A ∪ V^L` shape. -/
noncomputable def typeIIHypothesis46 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    OddOrder.Peterfalvi.S06.Hypothesis46
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
  { toHypothesis := typePData_toS06Hypothesis data hG.odd
      (typePData_W1_hall_coprime hG hSmax
        (OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)) data)
    dade := typeIIDadeHypothesis hG hSmax hSII
    tic := typePData_toTICyclicHypothesis data hG.odd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le data.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self data)).symm
    tic_V := rfl
    subH := data.H.subgroupOf S
    subH_normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer
        (data.H_le.trans (Subgroup.map_subtype_le _))).mpr ?_
      rw [data.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer S
    W2_le_subH := Subgroup.comap_mono (data.W2_le.trans inf_le_left)
    subH_le_K := Subgroup.comap_mono data.H_le
    A_covers := by
      intro hh hhH hhne x hx hxne
      -- the witness `z = (hh : G) ∈ S_σ^#`: `S_F = S_σ` for type II
      have hhσ : (hh : G) ∈ Msigma S := by
        rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
          hG hSmax (Or.inr hSII), ← data.H_eq]
        exact Subgroup.mem_subgroupOf.mp hhH
      obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
      refine ⟨Subgroup.mem_subgroupOf.mp hxK, fun h1 => hxne (Subtype.ext h1),
        (hh : G), (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr hhσ,
          fun he => hhne (Subtype.ext (Set.mem_singleton_iff.mp he))⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    dade0 := typeIIDadeHypothesis0 hG hSmax hSII data
    tau := (typeIIDadeHypothesis0 hG hSmax hSII data).fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)) }

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **World-bridge, `S`-side subset direction**: the §9 induced family `𝒮(Y)` of a
Types-II/III/IV setup lands in the §6/§8 kernel-filtered family
`S(Y) = inducedKernelFamily S' (Y ∩ S)`.  Both families induce from `HU = S'`
(`huSub_eq_derivedInG_subgroupOf`), and the `H ⊄ Ker` condition of `xiSet` supplies the
`θ ≠ 1` of `inducedKernelFamily`.

Setup-generic mirror of the `S13.Hypothesis`-locked `sOf_subset_SOf` (S13 is downstream of
this leaf, so it cannot be cited here; dedup candidate on a future upstream hoist).  Feeds the
`(9.8)` reducible classification and the `inducedKernelFamily_*` support/orthogonality/no-real
facts to the (10.7) `T2`-family. -/
theorem typeII_sOf_subset_inducedKernelFamily [Finite G] {S : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S) (Y : Subgroup G) :
    OddOrder.Peterfalvi.S11.sOf data Y ⊆
      OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG S).subgroupOf S) (Y.subgroupOf S) := by
  classical
  have hHU : huSub data = (derivedInG S).subgroupOf S :=
    huSub_eq_derivedInG_subgroupOf data
  rintro _ ⟨χ, hχ, rfl⟩
  rw [← hHU, OddOrder.Peterfalvi.S08.mem_inducedKernelFamily]
  refine ⟨χ, ?_, hχ.2, induceHU_eq_induce data χ⟩
  intro htriv
  exact hχ.1 (by rw [htriv]; simp [OddOrder.Peterfalvi.S03.characterKernel])

open scoped Classical FiniteInduce in
/-- **Peterfalvi (9.8)-classification at the type-II `S`-side bridge family**: a *reducible*
member of `inducedKernelFamily S' B` (any kernel filter `B`) is a nontrivial certain-type
column sum `μ_j = columnSum χ₂` of the `S`-side Hypothesis (4.6) instance
(`typeIIHypothesis46`).

Setup-generic mirror of the `M`-side
`Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (S12_HcBound), stopping at
the raw column form (no `Fin w₂` re-indexing): the reducible source is a Clifford restriction
`θ = χ_j = chiRestrict χ₂` (Peterfalvi (4.5.b), `induce_not_isIrreducible_iff`), the trivial
column is excluded by the family's `θ ≠ 1` (`chiRestrict_one_eq_trivial`), and the (4.5.a)
induction identity `induce_restrict_certainType_eq` rewrites `Ind_{S'}^S θ` as the column sum.
This is the "`ν` is a column" input of the (10.7) reducible `R(ν)`-datum
(`S06.certainTypeR`). -/
theorem typeII_reducible_inducedKernelFamily_eq_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    {B : Subgroup ↥S} {ψ : ClassFunction ↥S ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) B)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ χ₂ : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ,
      χ₂ ≠ 1 ∧
        ψ = OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data) χ₂ := by
  classical
  obtain ⟨θ, hθne, -, rfl⟩ := hψ
  set h : OddOrder.Peterfalvi.S06.Hypothesis ↥S :=
    (typeIIHypothesis46 hG hSmax hSII data).toHypothesis with hh
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  -- the reducible source is a §6 column `χ_j`
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [h.chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨χ₂', hχ₂'ne, ?_⟩
  rw [← hχ₂', h.coe_chiRestrict]
  exact h.induce_restrict_certainType_eq χ₂'

open scoped Classical FiniteInduce in
/-- The (8.16) `A₀(S)` Dade base has conjugation-invariant (trivial) signalizers: every
`H(a) = ⊥` by the `of_isTISubset` construction.  The `hconj` input of the §4 full Dade
isometry (2.6) at `typeIIHypothesis46 … |>.dade0`; since `HConjInvariant` is a proposition,
this is definitionally interchangeable with the proof baked into `typeIIHypothesis46 … |>.tau`. -/
theorem typeIIHypothesis46_dade0_hConjInvariant [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S) :
    (typeIIHypothesis46 hG hSmax hSII data).dade0.HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped Classical FiniteInduce in
/-- **The `S`-side Dade image of an `A(S)`-supported function vanishes on the exceptional set
`V`** (type-II mirror of the §12 `S13.tau_apply_eq_zero_of_mem_typePV`, over the (8.16)
`A₀(S)`-Dade base): for `α` supported on `A(S)` and `v ∈ (ticVdiff h46).V = W ∖ (W₁ ∪ W₂) =
typePV S`, the image `α^{τ_S}` vanishes at `v`.

`V^S ⊆ A₀(S)`, so `v` **is** a Dade base point: the explicit (2.5) evaluation
(`dadeValue_eq` with witness `a = v`, `h = 1`) gives `α^{τ_S}(v) = α(v)`, which vanishes
because `v ∉ S'` (`typePData_typePV_not_mem_derived`) while `α` is supported on
`A(S) ⊆ S'`.  This is the anchor of the `S`-side cross-orthogonality `R(μ_j) ⊥ R(χ)`
(`typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff`). -/
theorem typeII_tau_apply_eq_zero_of_mem_ticVdiffV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    {α : ClassFunction ↥S ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      (typeIIHypothesis46 hG hSmax hSII data).tau α v = 0 := by
  classical
  -- `v ∈ typePV S` (the `ticVdiff` exceptional set is definitionally `W ∖ (W₁ ∪ W₂)`)
  have hvPV : v ∈ typePV S data := hv
  -- `v ∈ A₀(S)` (the `V^S`-part, conjugator `1`)
  have hvA0 : v ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
      ∪ conjClassSetIn S (typePV S data) :=
    Or.inr ⟨v, hvPV, 1, S.one_mem, by group⟩
  -- `α` is `A₀`-supported (monotone from `A(S)`-supported)
  have hαA0 : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data)) S :=
    hαsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- evaluate the explicit (2.5) Dade map at the base point `a = v`, `h = 1`
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      (typeIIHypothesis46 hG hSmax hSII data).dade0 _ hαA0,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    (typeIIHypothesis46 hG hSmax hSII data).dade0.dadeValue_eq _ (a := ⟨v, hvA0⟩)
      (Subgroup.one_mem _) (by rw [mul_one])]
  -- `α(v) = 0`: `v ∉ S'` while `α` is `A(S) ⊆ S'`-supported
  by_contra hne
  have hmem := hαsupp (ClassFunction.mem_support.mpr hne)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
  exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived data hvPV hmem.1

open scoped Classical FiniteInduce in
/-- **(5.2.e) certain-type column vs irreducible break cross-orthogonality, type-II `S`-side**
`R(μ_j) ⊥ R(χ)` — the (10.7) analogue of the §12
`S13.certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (which is downstream of this leaf), over
the (8.16) `A₀(S)`-Dade base `typeIIHypothesis46 … |>.dade0`.

The proof is the same mirror of the Sibley `certainTypeR_imageSet_orthogonal_dadeOfDiff`: the
disjointness machine (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` on `ticVdiff h46`) and the
two-element `R(χ)` capture are `h46`-generic; the single anchor — vanishing of `(χ − χ̄)^{τ_S}`
on the exceptional `V` — is `typeII_tau_apply_eq_zero_of_mem_ticVdiffV` (base-point evaluation,
`V^S ⊆ A₀(S)`).  The conjugate difference is `A(S)`-supported (`hdiffsuppχA`, feeding the
anchor) and `A₀(S)`-supported (`hdiffsuppχ`, defining the Dade image family `R(χ)`).  This is
the irr × column case of the (10.7) `T2`-family `hRorth`. -/
theorem typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    {χ₂ : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf
      ((typeIIHypothesis46 hG hSmax hSII data).W1
        ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, (((typeIIHypothesis46 hG hSmax hSII data).columnFamily χ₂).mu i
        : ClassFunction ↥S ℂ) 1)
      = (∑ i, (((typeIIHypothesis46 hG hSmax hSII data).columnFamily χ₂⁻¹).mu i
        : ClassFunction ↥S ℂ) 1))
    (χ : IrreducibleCharacter ↥S)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥S ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    (hdiffsuppχ : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data)) S) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR (typeIIHypothesis46 hG hSmax hSII data)
        hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)
        χ hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W2
    omega
  -- core disjointness brick (mirror of the Sibley/§12 `key`)
  have key : ∀ (χ₂' : ((typeIIHypothesis46 hG hSmax hSII data).W2.subgroupOf ((typeIIHypothesis46 hG hSmax hSII data).W1 ⊔ (typeIIHypothesis46 hG hSmax hSII data).W2)) →* ℂˣ)
      (i : Fin (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)) {c c' : ℂ}
      {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G →
      ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V, (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (typeIIHypothesis46 hG hSmax hSII data) χ₂' i) = 0 := by
    intro χ₂' i c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact OddOrder.Peterfalvi.S08.inner_smul_chiFam_eq_zero_of_diff_vanishOnV
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (typeIIHypothesis46 hG hSmax hSII data))
      hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish hmin _
  -- `(χ − χ̄)^{τ_S}` vanishes on `V` (the type-II anchor, base-point evaluation)
  have hsuppsub : (((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
    rw [show (χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj =
        -((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  have htauvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIHypothesis46 hG hSmax hSII data).dade0 (typeIIHypothesis46 hG hSmax hSII data).tau
        ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data hsuppsub hv
  -- capture the two-element `R(χ)` abstractly
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIHypothesis46 hG hSmax hSII data).dade0
          ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data)))
        (χ : ClassFunction ↥S ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (typeIIHypothesis46 hG hSmax hSII data).dade0
            (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data) χ hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (typeIIHypothesis46 hG hSmax hSII data).dade0
      ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData
        (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data))
      ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  intro α hα β hβ
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  simp only [OddOrder.Peterfalvi.S06.certainTypeR, Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, -, rfl⟩ := hα
  have hvanishμν : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  have hμcast : cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction :=
    (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm
  have hνcast : (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction := by
    rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]
  rcases hβ with rfl | rfl <;> cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]

end Hypothesis46Instance

/-! ## The (10.7) cross-isometry package -/

/-- **Peterfalvi (10.7), left-branch cross-isometry data** for a Type-II maximal `S`
against the type-`P₁` `M` of Hypothesis (10.1)/(10.4).

Bundles, for an irreducible `lam` and a reducible `nu` of equal degree in the `S`-side
induced family `𝒮(H₀)(S)`, the five character-theoretic facts that Peterfalvi's (10.7)
contradiction consumes.  Each field cites its book source:

* `tau2` — the coherent extension `τ₂` of the `S`-side Dade isometry to
  `ℤ[{λ, λ̄, ν, ν̄}]` (Peterfalvi (5.7): the 4-element family is uniform-degree coherent).
* `r'`, `delta'`, `nu_tau2_eq` — Peterfalvi (5.8) for `τ₂` against the **shared** `ω^σ`-grid:
  `ν^{τ₂} = δ'·∑_{j<w₂} ω_{r'j}^σ` for some row `r'` and sign `δ'`.  The grid here is `M`'s
  aligned `σ`-grid: the (8.8) pair structure (`S ∩ M = W`, `W₁/W₂` roles swapped) and the
  (3.2)-uniqueness of the cyclic-TI isometry `σ` identify `S`'s grid with the transpose of
  `M`'s, so the `S`-side (4.5)-column sum is an `M`-side row sum.
* `lam_ortho_grid` — `λ^{τ₂} ⊥ ω_{ij}^σ` (Peterfalvi (5.3.b): the coherent image of an
  irreducible family member is orthogonal to the `σ`-image; Coq `coherent_ortho_cycTIiso`).
* `zeta_ortho_grid` — `ζ^{τ₁} ⊥ ω_{ij}^σ` (same source, `M`-side).
* `zeta_lam_ortho` — `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0` (from `⟨(ζ−ζ̄)^τ, (λ−λ̄)^{τ_S}⟩ = 0` — the
  (8.18.b) support disjointness — and orthonormality of the conjugate pairs;
  Coq `orthonormal_vchar_diff_ortho` step of `Frob_der1_type2`).
* `cross_zero` — Peterfalvi's `(α^τ, β^τ) = 0` for `α = μ_s − d·ζ ∈ ℤ[𝒮, M^#]` and
  `β = ν − λ ∈ ℤ[T2, S^#]`: `Supp(α) ⊆ A₁(M)` by (8.10), `Supp(β) ⊆ A(S)` by (8.15)+(4.7),
  and `Ã₁(M) ∩ Ã(S) = ∅` by (8.18.b) (using (8.13.c4): no conjugate of `S` supports `M`,
  because `M` is not Frobenius with kernel `M_F` under Hypothesis (10.1)).  On these
  supports `τ = τ₁` and `τ_S = τ₂` (coherence agreement), giving the stated form. -/
structure TypeIICrossIsometryData [Finite G] [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (lam nu : ClassFunction ↥S ℂ) where
  /-- The (5.7) coherent extension `τ₂` of the `S`-side Dade isometry to the 4-element
  uniform-degree family `{λ, λ̄, ν, ν̄}`. -/
  tau2 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  /-- The `M`-grid row index of the (5.8) image of `ν`. -/
  r' : Fin hyp.w1
  /-- The (5.8) sign of the image of `ν`. -/
  delta' : ℤ
  delta'_pm : delta' = 1 ∨ delta' = -1
  /-- **Peterfalvi (5.8)** for `τ₂` against the shared grid: `ν^{τ₂} = δ'·∑_j ω_{r'j}^σ`. -/
  nu_tau2_eq : tau2 nu
    = (delta' : ℂ) • ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hG.odd r' j
  /-- **Peterfalvi (5.3.b)** (`S`-side): `λ^{τ₂}` is orthogonal to the `σ`-grid. -/
  lam_ortho_grid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j) (tau2 lam) = 0
  /-- **Peterfalvi (5.3.b)** (`M`-side): `ζ^{τ₁}` is orthogonal to the `σ`-grid. -/
  zeta_ortho_grid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
    ClassFunction.inner (coh.tau1 params.zeta) (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0
  /-- `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0` (cross-side orthogonality of the two coherent images). -/
  zeta_lam_ortho : ClassFunction.inner (coh.tau1 params.zeta) (tau2 lam) = 0
  /-- **Peterfalvi's `(α^τ, β^τ) = 0`** for `α = μ_s − d·ζ` and `β = ν − λ`
  ((8.10)+(8.15)+(4.7) supports and the (8.18.b) disjointness). -/
  cross_zero : ∀ s : Fin hyp.w2, s ≠ 0 →
    ClassFunction.inner
      (coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta))
      (tau2 nu - tau2 lam) = 0

open scoped Classical FiniteInduce in
/-- **The (10.7) left-branch gate** (Coq `Frob_der1_type2`, `PFsection10.v:568-658` tail):
for a Type-II maximal `S` whose `S`-side §9 family `𝒮(H₀)` contains an irreducible `lam`
and a reducible `nu` of equal degree, the (10.7) cross-isometry package exists.

The honest production decomposes into (tracking: the (10.7) frontier note
`notes/peterfalvi/s10_7_derived_frobenius.md`):

1. **`τ₂` = T2-coherence** (Peterfalvi (5.7)): the norm-general uniform-degree engine
   `S07.uniform_degree_coherence_of_families` applied to `{λ, λ̄, ν, ν̄}` over the honest
   type-`P₂` `S`-side Dade datum (`dadeSupportHypothesisData_honestTypeP2ASet`), with the
   reducible column `R(ν)`-family `S06.certainTypeRImage` and the irreducible 2-element
   `R(λ)` (`dadeCharacterDifferenceImageOfDiff`).
2. **The shared grid** ((8.8) pair + (3.2) σ-uniqueness): `S ∩ M = W` with the `W₁/W₂`
   roles swapped identifies the `S`-side `certainTypeOmegaSigma` grid with the transpose of
   `M`'s `alignedOmegaSigmaGrid`; then (5.8) (Coq `coherent_prDade_TIred`, via (3.7)
   coefficient rigidity and the `V`-vanishing (3.2.d)) pins `ν^{τ₂}` to a signed row sum.
3. **Support disjointness** ((8.18.b) via (8.13.c4)): `Ã₁(M) ∩ Ã(S) = ∅` because `M` is
   not Frobenius with kernel `M_F` (Hypothesis (10.1)), so no conjugate of `S` supports
   `M`; with (8.10)/(8.15)/(4.7) this gives `cross_zero` and (with the conjugate-pair
   difference trick) `zeta_lam_ortho`.

Each numbered item is genuine unformalized mathematics (none is `M`-side §10 material,
which is fully proven); item 2 is in the `typeP_pair` sphere (issue 0098 item 1), item 3
in the §8 support geometry (S10).  Consumed by `TypeIICrossIsometryData.elim` /
`typeII_HU_frobenius_of_coherent` below. -/
theorem exists_typeIICrossIsometryData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (hSII : IsTypeII S)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (TypeIICrossIsometryData hG coh lam nu) := by
  sorry

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7), left-branch contradiction** (the tail computation of Coq
`Frob_der1_type2`): the cross-isometry package is contradictory.

Choose any nontrivial column `s ≠ 0`.  The proven `M`-side (10.6.a) pin
(`Hypothesis.muColumn_tau1_pin`) gives `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`, so
`(μ_s − d·ζ)^{τ₁} = δ·∑_i ω_{is}^σ − d·ζ^{τ₁}`; the package's (5.8) identity gives
`(ν − λ)^{τ₂} = δ'·∑_j ω_{r'j}^σ − λ^{τ₂}`.  The bilinear expansion of `cross_zero`
against the orthonormal grid (`alignedOmegaSigmaGrid_inner`) kills every term except the
shared entry `⟨ω_{r's}^σ, ω_{r's}^σ⟩`, leaving `0 = δ·δ' = ±1` — absurd.  (This inlines
the abstract bookkeeping of `S15.eta_cross_expansion_ne_zero`, which lives downstream of
this file.) -/
theorem TypeIICrossIsometryData.elim [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    {coh : CoherentHypothesis hyp params}
    {S : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (pkg : TypeIICrossIsometryData hG coh lam nu)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    False := by
  haveI := hyp.finiteG
  classical
  haveI : NeZero hyp.w2 := ⟨params.w2_prime.pos.ne'⟩
  -- the nontrivial-column degree fact `μ_{0j}(1) = d ≠ 1` feeding the pin.
  have hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1 := by
    intro jj hjj h1
    rw [← hmu, params.degree_independent 0 jj hjj] at h1
    have hd := params.d_gt_one
    have : params.d = 1 := Nat.cast_eq_one.mp h1
    omega
  -- choose the column `s = 1 ≠ 0` (`w₂ ≥ 2` since it is prime).
  have hw2 : 1 < hyp.w2 := params.w2_prime.one_lt
  set s : Fin hyp.w2 := ⟨1, hw2⟩ with hs_def
  have hs0 : s ≠ 0 := Fin.ne_of_val_ne (by simp [hs_def])
  -- the proven `M`-side (10.6.a) pin: `μ_s^{τ₁} = δ·∑_i ω_{is}^σ`.
  have hpin := hyp.muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hs0
  -- shorthands (folded into the pin and the package projections).
  set eta : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ :=
    hyp.alignedOmegaSigmaGrid hG hG.odd with heta_def
  set Z : ClassFunction G ℂ := coh.tau1 params.zeta with hZ_def
  set L : ClassFunction G ℂ := pkg.tau2 lam with hL_def
  -- `τ₁(μ_s − d·ζ) = δ·∑_i ω_{is}^σ − d·ζ^{τ₁}` (ℤ-linearity through the ℕ-cast scalar).
  have hτlin : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta)
      = (params.delta : ℂ) • (∑ i : Fin hyp.w1, eta i s) - (params.d : ℂ) • Z := by
    rw [Nat.cast_smul_eq_nsmul ℂ params.d params.zeta, map_sub, map_nsmul, hpin,
      ← Nat.cast_smul_eq_nsmul ℂ params.d Z]
  -- the cross-orthogonality, rewritten through the two (5.8)-type identities.
  have h0 := pkg.cross_zero s hs0
  rw [hτlin, pkg.nu_tau2_eq, ← heta_def, ← hL_def] at h0
  -- the surviving grid entry and the three vanishing cross terms.
  have hgrid : ClassFunction.inner (∑ i : Fin hyp.w1, eta i s)
      (∑ j : Fin hyp.w2, eta pkg.r' j) = 1 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    have hrow : ∀ i : Fin hyp.w1,
        ClassFunction.inner (eta i s) (∑ j : Fin hyp.w2, eta pkg.r' j)
          = if i = pkg.r' then (1 : ℂ) else 0 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      by_cases hir : i = pkg.r'
      · subst hir
        rw [if_pos rfl, Finset.sum_eq_single s]
        · rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]; simp
        · intro j _ hjs
          rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]
          simp [Ne.symm hjs]
        · intro h; exact absurd (Finset.mem_univ s) h
      · rw [if_neg hir]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [heta_def, hyp.alignedOmegaSigmaGrid_inner]
        simp [hir]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp
  have hZsum : ClassFunction.inner Z (∑ j : Fin hyp.w2, eta pkg.r' j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun j _ => pkg.zeta_ortho_grid pkg.r' j
  have hsumL : ClassFunction.inner (∑ i : Fin hyp.w1, eta i s) L = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_eq_zero fun i _ => pkg.lam_ortho_grid i s
  have hZL : ClassFunction.inner Z L = 0 := pkg.zeta_lam_ortho
  -- expand the bilinear form; only the shared grid entry survives: `0 = δ·δ'`.
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right] at h0
  rw [hgrid, hZsum, hsumL, hZL] at h0
  simp only [star_intCast, mul_one, mul_zero, sub_zero] at h0
  rcases hδpm with hδ | hδ <;> rcases pkg.delta'_pm with hδ' | hδ' <;>
    rw [hδ, hδ'] at h0 <;> norm_num at h0

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7), dichotomy assembly** (setup form): under Hypothesis (10.4) for
`M`, a maximal `S` with a Types-II/III/IV setup that is actually of Type II has
`[S,S] = S_F ⋊ U` Frobenius with kernel `S_F` (on the `derivedInG S` carrier).

Splits on the `S`-side §9 Clifford dichotomy (`S11.clifford_dichotomy`):

* **Case A** (imprimitive `Ū`-action): (9.8.c) supplies an irreducible of degree `q·u` in
  `𝒮(H₀C)` and (9.8.a,b) a reducible of the same degree — the left-branch package
  (`exists_typeIICrossIsometryData`) is contradictory (`TypeIICrossIsometryData.elim`).
* **Case B, exceptional** (no irreducible of degree `q·u` in `𝒮(H₀C')`): Peterfalvi (9.10)
  = `S11.exceptional_case_frobenius_realization` yields the `H ⊔ U` Frobenius structure
  directly (its Type-II conjunct), transported to `derivedInG S` by
  `M' = H ⊔ U` (`TypePData.derivedInG_eq_fitting_sup_U`).
* **Case B, non-exceptional**: the degree-`q·u` irreducible exists in `𝒮(H₀C')`, and
  (9.9.b,c) supply the equal-degree reducible — again the left-branch contradiction. -/
theorem typeII_HU_frobenius_of_coherent_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    (hSII : IsTypeII S) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (data.typeP.H.subgroupOf (derivedInG S))
      (data.typeP.U.subgroupOf (derivedInG S)) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the (10.3) parameters carrying the grid/`ζ` pins (the coherence datum is
  -- params-independent), as in `typeII_coherence_contradiction_estimate`.
  obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- §9 character data: only the genuine `u`/`u_eq` pair is consumed by the counts; the
  -- coherence-only fields are inert placeholders (cf. `Hypothesis.mkSection11CharacterData`).
  let chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief :=
    { u := Nat.card ↥(((OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
          (N := chief.N) chief.N_aInvariant).comp
          (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
      u_eq_card_quotient := rfl
      H0CprimeSupport := ∅
      tau := 0
      quotientSemidirectFrobenius := True }
  -- the reducible `ν ∈ 𝒮(H₀)`: the (9.8.a)/(9.9.b) count `p − 1 ≥ 1`.
  have hred_ne : {φ ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 |
      ¬ IsIrreducibleCharacter φ}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [OddOrder.Peterfalvi.S11.reducible_count_sOf_H0 hG chief]
    have := chief.p_prime.two_le
    omega
  obtain ⟨nu, hnu_mem, hnu_red⟩ := hred_ne
  -- the left-branch refutation, shared by Case A and the non-exceptional Case B.
  have hleft : ∀ lam : ClassFunction ↥S ℂ,
      lam ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 → IsIrreducibleCharacter lam →
      lam 1 = nu 1 → False := fun lam hlam_mem hlam_irr hdeg =>
    (exists_typeIICrossIsometryData hG coh' hSII chars
      hlam_mem hlam_irr hnu_mem hnu_red hdeg).elim fun pkg =>
      pkg.elim hG hmu hos hzS hz1 hzconj hδpm hδj
  -- the §9 Clifford dichotomy.
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · -- **Case A**: (9.8.c) irreducible + (9.8.b) reducible degree — contradiction.
    exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, hbred, ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    have hnu_deg := (hbred nu hnu_mem hnu_red).1
    exact hleft lam
      (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
      hlam_irr (by rw [hlam_deg, hnu_deg])
  · -- **Case B**: split on the exceptional condition.
    obtain ⟨caseB⟩ := hB
    by_cases hex : ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)
    · -- non-exceptional: the degree-`q·u` irreducible exists — contradiction.
      exfalso
      obtain ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩ := hex
      obtain ⟨-, -, hbred, -⟩ :=
        OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB
      have hnu_deg := (hbred nu hnu_mem hnu_red).1
      exact hleft lam
        (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
        hlam_irr (by rw [hlam_deg, hnu_deg])
    · -- exceptional: (9.10) gives the `H ⊔ U` Frobenius, transported to `M' = derivedInG S`.
      have hfrobHU := (OddOrder.Peterfalvi.S11.exceptional_case_frobenius_realization
        hG chars caseB hex).2.2 hSII
      have hM'eq : derivedInG S = data.typeP.H ⊔ data.typeP.U := by
        rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]
      rw [hM'eq]
      exact hfrobHU

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7)** (Type-II datum form): under Hypothesis (10.4) for `M`, every
Type-II maximal subgroup `S` has `[S,S] = S_F ⋊ U` Frobenius with kernel `S_F`, on the
`derivedInG S` carrier with the type-`P` factors of the given `TypeIIData`. -/
theorem typeII_HU_frobenius_of_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (hSmax : S ∈ maximalSubgroups G) (dII : TypeIIData S) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (dII.typeP.H.subgroupOf (derivedInG S))
      (dII.typeP.U.subgroupOf (derivedInG S)) :=
  typeII_HU_frobenius_of_coherent_aux hG coh
    { maximal := hSmax
      typeP := dII.typeP
      nontrivial := dII.common
      type_alt := Or.inl ⟨dII⟩ } ⟨dII⟩

end OddOrder.Peterfalvi.S12
