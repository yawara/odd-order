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

end DadeBase

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
