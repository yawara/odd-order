/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.Peterfalvi.S08_GeneralAdjoin

/-!
# Peterfalvi (6.2)/(6.3) from the Hypothesis (5.2) image families — the oracle-free book form

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §5 (5.2)/(5.3),
§6 (6.1)-(6.3), pp. 25, 30-31.

## What this leaf removes

`S08_Theorem62_63_Standalone` states (6.2)/(6.3) with an explicit **break-member oracle** `h56`
("`𝒮(A)` coherent and `𝒮(B)` not ⟹ some `θ ∈ Irr K` trivial on `B` has
`|K:A| − 1 ≤ 2·(Ind_K^L θ)(1)`"), which is (6.2) itself minus the `√`-arithmetic.  That is *not*
a hypothesis of the book: Hypothesis (6.1) reads "**Assume that Hypothesis (5.2) holds.**  We
assume that `K` is a solvable normal subgroup of `L` and that `𝒮 = {Ind_K^L θ | θ ∈ Irr K,
θ ≠ 1_K}`" (p. 30).  The genuine data the book assumes is (5.2.d)/(5.2.e):

* **(5.2.d)** for `χ ∈ 𝒮`, `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α` for some orthonormal `R(χ) ⊆ ℤ[Irr G]`;
* **(5.2.e)** if `φ ∈ 𝒮` is orthogonal to `{χ, χ̄}`, then `R(φ)` is orthogonal to `R(χ)`.

`InducedFamilyImageData` bundles exactly those two for the general induced family
`𝒮 = S(⊥) = inducedKernelFamily K ⊥`, and `InducedFamilyImageData.datum` turns them into the
`hdatum` clause of the h56 producer `exists_source_index_le_two_psi_of_break`
(`S08_SixTwoGeneral`).  Composing gives `six_two_of_imageData` / `six_three_of_imageData`: the
book's (6.2)/(6.3) with **no oracle**, only Hypothesis (5.2)-data plus solvability of `K`.

⚠ The book's (5.2.d) is *not* automatic for the general family — for a **reducible** member the
two-element Dade `R(χ)` (`dadeOrthonormalCharacterImageFamilyOfDiff`, which demands
`χ ∈ Irr L`) does not apply.  Peterfalvi (5.3.b) discharges (5.2.d)/(5.2.e) under Hypothesis (4.6),
where the reducible members are exactly the certain-type columns `μ_j` and
`R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ | 0 ≤ i < w₁}` comes from Theorem (4.9) (repo:
`S06.certainTypeR`, `S06.certainTypeR_imageSet_orthogonal_certainTypeR`; the §9/§11 dispatch is
`S11.sOf_memberRFamily`, the §11/§13 discharge `S12.Hypothesis.sixTwoDecompositionData`).  So the
Feit–Thompson consumer supplies `InducedFamilyImageData`, and this leaf is the faithful statement
of what (6.1) actually assumes.

## Specialization debt

`τ` here is the Feit–Thompson Dade map `dadeIntegralCharacterMap` and the supported set is
`supportInSubgroup A L`, whereas Hypothesis (5.2.b) allows any linear isometry
`ℤ[𝒮, L^#] → ℤ[Irr G, G^#]`.  The adjoin engine is already `τ`-general
(`S07.adjoinPairCoherent_general`, `S08_GeneralAdjoin`); the *norm-weighted* engine
(`coherentDegreeSqNormBound_of_not_coherentW_k`) is still stated for the Dade map, so the abstract
form of (6.2)/(6.3) waits on generalizing that.  See issue 0153.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

/-- **Transport an image family along an equality of characters.**  Only `image_eq` mentions `χ`,
so `imageSet`/`mem_ZIrr`/`orthonormal` carry over verbatim and `(R.congrChi h).imageSet` is
*definitionally* `R.imageSet` — which is what lets orthogonality proved for the source family apply
to the transported one.

The use is the (5.2.d) dispatch on a general induced family: a **reducible** member is a
certain-type column `μ_j`, so its `R(·)` is produced for the *column* `∑ᵢ μ_{ij}`, while the family
datum is indexed by the member `χ` itself; the two are equal but not syntactically so.  (Companion
of `congrTau`, which transports along an equality of integral character maps.) -/
def OrthonormalCharacterImageFamily.congrChi {L G : Type*} [Group L] [Group G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] {τ : IntegralCharacterMap L G}
    {χ χ' : ClassFunction L ℂ} (h : χ = χ')
    (R : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ') :
    OrthonormalCharacterImageFamily (L := L) (G := G) τ χ where
  imageSet := R.imageSet
  mem_ZIrr := R.mem_ZIrr
  orthonormal := R.orthonormal
  image_eq := by rw [h]; exact R.image_eq

@[simp] theorem OrthonormalCharacterImageFamily.congrChi_imageSet {L G : Type*} [Group L] [Group G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] {τ : IntegralCharacterMap L G}
    {χ χ' : ClassFunction L ℂ} (h : χ = χ')
    (R : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ') :
    (R.congrChi h).imageSet = R.imageSet := rfl

end OddOrder.Peterfalvi.S07

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-! ### Hypothesis (5.2.d)/(5.2.e) for the general induced family -/

/-- **Peterfalvi Hypothesis (5.2.d)/(5.2.e) for `𝒮 = S(⊥) = inducedKernelFamily K ⊥`.**

The two pieces of Hypothesis (5.2) that are genuinely *data* rather than consequences of the
family's shape: a difference-image family `R(χ)` per member (5.2.d), and the disjoint-pair
orthogonality (5.2.e).  Everything else in (5.2) is proved for this family in
`S08_SixTwoGeneral`: (5.2.a) conjugation closure and non-reality
(`inducedKernelFamily_closedUnderConjugate`, `inducedKernelFamily_hasNoRealCharacters` for `L` of
odd order), (5.2.b) the isometry (the Dade map on the supported lattice), (5.2.c) pairwise
orthogonality (`inducedKernelFamily_pairwise_orthogonal`).

For an **irreducible** member `R(χ)` is the two-element Dade family
(`dadeOrthonormalCharacterImageFamilyOfDiff`); for a reducible one it is the certain-type
`R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ}` of Peterfalvi (5.3.b)/(4.9) (`S06.certainTypeR`). -/
structure InducedFamilyImageData {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)] where
  /-- **(5.2.d)**: the orthonormal difference-image family `R(χ)` of each member `χ ∈ 𝒮`. -/
  R : ∀ χ ∈ inducedKernelFamily K ⊥,
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) χ
  /-- **(5.2.e)**: `φ ⊥ {χ, χ̄}` forces `R(φ) ⊥ R(χ)`. -/
  orthogonal : ∀ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ inducedKernelFamily K ⊥)
      (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ inducedKernelFamily K ⊥),
    ClassFunction.inner φ χ = 0 → ClassFunction.inner φ χ.conj = 0 →
      (R φ hφ).Orthogonal (R χ hχ)

/-! ### From (5.2.d)/(5.2.e) to the `hdatum` clause of the h56 producer -/

section Datum

variable {A : Set G} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **The Dade map is an isometry on every supported sublattice of `ℤ[𝒮]`** — the `hisom` input
of `S07.decompositionDaFromDiff_general`, packaged for the ambient family `Samb = S(⊥)`.  Pure
repackaging of `dadeIntegralCharacterMap_inner_eq_on_supported_span`: membership in
`zSupportedSpan Samb A₀` gives the `A₀`-support of every generator, which is all that lemma
needs. -/
theorem dade_hisom_of_zSupportedSpan (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (Samb : Set (ClassFunction ↥L ℂ)) :
    ∀ (T : Set (ClassFunction ↥L ℂ)),
      (∀ s ∈ T, s ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) Samb
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) →
      ∀ φ ζ : ClassFunction ↥L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) φ)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) ζ)
          = ClassFunction.inner φ ζ :=
  fun _T hT _φ _ζ hφ hζ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
      (fun s hs => (hT s hs).2) hφ hζ

/-- **The break decomposition `Da` from (5.2.d)** — general in the break's norm, so a
**reducible** break `ψ` is allowed (Peterfalvi (5.6) puts no irreducibility on the adjoined
`χ ∈ 𝒮`).  Feeds `S07.decompositionDaFromDiff_general` the family `R(ψ)` supplied by (5.2.d);
the auxiliary isometry is `τ` itself, so `Da.tau1 = τ` holds definitionally. -/
noncomputable def InducedFamilyImageData.breakDa
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (RD : InducedFamilyImageData hyp K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      ψ (a • χ₁) := by
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  have hχ₁fam : χ₁ ∈ inducedKernelFamily K ⊥ := hS₁sub hχ₁S₁
  have hreal : ¬ ClassFunction.IsReal ψ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hψfam
  -- the two supported differences `ψ − ψ̄` and `ψ − a·χ₁`
  have hdiffsupp : (ψ.conj - ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    inducedKernelFamily_conjDiff_support hKsupp hψfam
  have hdiffasupp : (ψ - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    inducedKernelFamily_scaledDiff_support hKsupp hψB hχ₁fam (d := a) hψdeg
  have hdiffmem : ψ - ψ.conj ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam) (Submodule.subset_span hψcfam), by
        rw [show ψ - ψ.conj = -(ψ.conj - ψ) from by abel, ClassFunction.support_neg]
        exact hdiffsupp⟩
  have hadiffmem : ψ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam)
        (nsmul_mem (Submodule.subset_span hχ₁fam) a), hdiffasupp⟩
  have htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData) (ψ - a • χ₁) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp
      hdiffasupp ?_
    exact Submodule.sub_mem _ (inducedKernelFamily_mem_ZIrr hψfam)
      (nsmul_mem (inducedKernelFamily_mem_ZIrr hχ₁fam) a)
  -- the (5.4) orthogonality scalars `ψ, ψ̄ ⊥ a·χ₁` and `ψ ⊥ ψ̄`
  have hψχ₁ : ClassFunction.inner ψ χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hχ₁fam (fun h => hψnotS1 (h ▸ hχ₁S₁))
  have hψbarχ₁ : ClassFunction.inner ψ.conj χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψcfam hχ₁fam (fun h => hψcnotS1 (h ▸ hχ₁S₁))
  have hψaχ₁ : ClassFunction.inner ψ (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψχ₁, mul_zero]
  have hψbaraχ₁ : ClassFunction.inner ψ.conj (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψbarχ₁, mul_zero]
  have hψψbar : ClassFunction.inner ψ ψ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hψcfam (fun h => hreal h.symm)
  exact OddOrder.Peterfalvi.S07.decompositionDaFromDiff_general
    (Samb := inducedKernelFamily K ⊥) (RD.R ψ hψfam)
    (dade_hisom_of_zSupportedSpan hyp (inducedKernelFamily K ⊥))
    hdiffmem hadiffmem htau1_mema hψaχ₁ hψbaraχ₁ hψψbar

@[simp] theorem InducedFamilyImageData.breakDa_tau1
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (RD : InducedFamilyImageData hyp K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    (RD.breakDa hodd hKsupp hS₁sub hψB hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).tau1
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) :=
  rfl

@[simp] theorem InducedFamilyImageData.breakDa_imageFamily
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (RD : InducedFamilyImageData hyp K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    (RD.breakDa hodd hKsupp hS₁sub hψB hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).imageFamily
      = RD.R ψ (inducedKernelFamily_subset_bot B hψB) :=
  rfl

/-- **(5.2.d)/(5.2.e) ⟹ the `hdatum` clause of the h56 producer.**

The decomposition data `exists_source_index_le_two_psi_of_break` asks for, built from the image
families alone:

* the break side is `InducedFamilyImageData.breakDa` (auxiliary isometry `τ`, `R(ψ)` from
  (5.2.d)), with `Da.tau1 = τ` by `rfl`;
* the member side is `S07.memberExtensionDecomposition_general` at `R(χ)` (auxiliary isometry the
  **running extension** `ν = hS₁coh.extension`, which is integral on `S₁` where `τχ` need not be),
  so `D.tau1 χ = ν χ` by `rfl`;
* their cross-orthogonality `R(χ) ⊥ R(ψ)` is exactly (5.2.e), applicable because `χ ∈ S₁` while
  `ψ, ψ̄ ∉ S₁`, so `χ ⊥ {ψ, ψ̄}` by the family's pairwise orthogonality (5.2.c).

Note that the break `ψ` and the members `χ` may both be **reducible**: nothing here consumes
`‖·‖² = 1`. -/
theorem InducedFamilyImageData.datum
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (RD : InducedFamilyImageData hyp K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (A' B : Subgroup ↥L) :
    ∀ (S₁ : Set (ClassFunction ↥L ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ inducedKernelFamily K A' ∪ inducedKernelFamily K B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      ∀ (ψ : ClassFunction ↥L ℂ), ψ ∈ inducedKernelFamily K B → ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥L ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (S₁ ∪ {ψ, ψ.conj}) (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
            (hyp.fullDadeIsometryData)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
          (hyp.fullDadeIsometryData) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ := by
  intro S₁ hS₁conj hS₁un hS₁coh ψ hψB hψnotS₁ hψcnotS₁ χ₁ hχ₁S₁ a hψdeg _hnc
  have hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥ := fun χ hχ => by
    rcases hS₁un hχ with h | h
    · exact inducedKernelFamily_subset_bot A' h
    · exact inducedKernelFamily_subset_bot B h
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  refine ⟨RD.breakDa hodd hKsupp hS₁sub hψB hψnotS₁ hψcnotS₁ hχ₁S₁ hψdeg, rfl, ?_⟩
  intro χ hχS₁
  have hχfam : χ ∈ inducedKernelFamily K ⊥ := hS₁sub hχS₁
  have hχcfam : χ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hχfam
  have hχreal : ¬ ClassFunction.IsReal χ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hχfam
  have hχχbar : ClassFunction.inner χ χ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχfam hχcfam (fun h => hχreal h.symm)
  have hνZ : hS₁coh.extension χ ∈ ZIrr G :=
    hS₁coh.extension_mem_ZIrr χ (Submodule.subset_span hχS₁)
  refine ⟨OddOrder.Peterfalvi.S07.memberExtensionDecomposition_general hS₁coh (RD.R χ hχfam)
    (inducedKernelFamily_conjDiff_support hKsupp hχfam) hχS₁ (hS₁conj hχS₁) hνZ hχχbar, ?_, rfl⟩
  -- (5.2.e): `χ ∈ S₁` is orthogonal to `ψ, ψ̄ ∉ S₁`, so `R(χ) ⊥ R(ψ)`.
  exact RD.orthogonal ψ hψfam χ hχfam
    (inducedKernelFamily_pairwise_orthogonal hχfam hψfam (fun h => hψnotS₁ (h ▸ hχS₁)))
    (inducedKernelFamily_pairwise_orthogonal hχfam hψcfam (fun h => hψcnotS₁ (h ▸ hχS₁)))

end Datum

/-! ### The (6.2)/(6.3) theorems with no oracle -/

section BookForm

variable {A : Set G} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] in
/-- **`K/X` has proper commutator subgroup** whenever `X < K` and `K` is solvable — the input of
both the (6.2) degree-`|L:K|` anchor (`exists_inducedKernelFamily_member_degree_index`) and the
`S(X) ≠ ∅` witness (`inducedKernelFamily_nonempty_of_commutator_ne_top`).  Peterfalvi's
"Since `K` is solvable, `K/A` has a non-trivial irreducible character of degree 1" (p. 30). -/
theorem commutator_quotient_ne_top_of_lt [IsSolvable ↥K] {X : Subgroup ↥L} [X.Normal]
    (hXK : X < K) :
    _root_.commutator (↥K ⧸ X.subgroupOf K) ≠ ⊤ := by
  haveI : (X.subgroupOf K).Normal := (‹X.Normal›).subgroupOf K
  haveI : Nontrivial (↥K ⧸ X.subgroupOf K) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hXK.ne' (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hXK.le)
  exact (IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ X.subgroupOf K)).ne

/-- **The (6.2) break-member bound `|K:A'| − 1 ≤ 2ψ(1)` from Hypothesis (5.2) data alone** — the
`h56` of `six_two_general`/`six_three_of_six_two_oracle`, now a *theorem*.

Peterfalvi's (6.2) proof opening, verbatim: from the coherence dichotomy `S(A')` coherent /
`S(B)` not, the first-obstruction chain (`exists_coherentBreakPair_union`) produces a break pair
`{ψ, ψ̄} ⊆ S(B)` over a maximal coherent conjugation-closed `S₁ ⊆ S(A') ∪ S(B)`; the (5.6)
norm-weighted contrapositive then bounds the `S(A')` degree-square sum, and the (B2) identity
`∑_{χ ∈ S(A')} χ(1)²/‖χ‖² = |L:K|(|K:A'| − 1)` converts it into the index bound.  The anchor
`χ₁ ∈ S(A')` of degree `|L:K|` and the nonemptiness of `S(B)` both come from solvability of `K`
via `commutator_quotient_ne_top_of_lt`. -/
theorem exists_source_index_le_two_psi_of_imageData
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} [IsSolvable ↥K]
    (RD : InducedFamilyImageData hyp K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {A' B : Subgroup ↥L} [A'.Normal] [B.Normal] (hA'K : A' < K) (hBK : B < K)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K A') (OddOrder.Peterfalvi.S04.supportInSubgroup A L)))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K B) (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∃ θ : IrreducibleCharacter ↥K,
      (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥K ℂ) ∧
      (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
        2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re := by
  haveI : (A'.subgroupOf K).Normal := (‹A'.Normal›).subgroupOf K
  haveI : (B.subgroupOf K).Normal := (‹B.Normal›).subgroupOf K
  exact exists_source_index_le_two_psi_of_break hyp hodd hKsupp h1A
    (exists_inducedKernelFamily_member_degree_index (commutator_quotient_ne_top_of_lt hA'K))
    (inducedKernelFamily_nonempty_of_commutator_ne_top
      (commutator_quotient_ne_top_of_lt hBK))
    (RD.datum hodd hKsupp A' B) hAcoh hBncoh

/-- **Peterfalvi (6.2)** — no oracle.

*Assume Hypothesis (6.1).  Let `A, B, C, D` be normal subgroups of `L` such that*
*(a) `A ⊊ K`, `B ⊆ D ⊆ C ⊆ K` and `D/B ⊆ Z(C/B)`, (b) `S(A)` is coherent but `S(B)` is not.*
*Then `2|L:C|√|C:D| ≥ |K:A| − 1`.*  (p. 30; here `A' = A` to avoid clashing with the Dade
support set `A`.)

Hypothesis (6.1) is realized by: `hyp` (the Feit–Thompson Dade data, giving the (5.2.b) isometry),
`RD` (the (5.2.d)/(5.2.e) image families), `hodd` (so `𝒮` has no real members, (5.2.a)),
`hKsupp`/`h1A` (the family's differences are `A₀`-supported), `K` solvable normal, and
`𝒮(X) = inducedKernelFamily K X`.  `B < K` is part of (6.2.a) (`B ⊆ D ⊆ C ⊆ K` with `A ⊊ K`
forcing a proper section; it is what makes `S(B)` nonempty). -/
theorem six_two_of_imageData
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} [IsSolvable ↥K]
    (RD : InducedFamilyImageData hyp K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {A' B C D : Subgroup ↥L} [A'.Normal] [B.Normal]
    (hA'K : A' < K) (hBK : B < K) (hBD : B ≤ D) (hCK : C ≤ K)
    (hcentral : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (↥C ⧸ B.subgroupOf C))
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K A') (OddOrder.Peterfalvi.S04.supportInSubgroup A L)))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K B) (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
      2 * (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) :=
  six_two_general hBD hCK hcentral
    (exists_source_index_le_two_psi_of_imageData RD hodd hKsupp h1A hA'K hBK hAcoh hBncoh)

/-- **Peterfalvi (6.3)** — no oracle.

*Assume Hypothesis (6.1).  Let `M, H, H₁` be normal subgroups of `L` such that*
*`M ⊆ H₁ ⊆ H ⊆ K`.  Assume further that (a) `H/M` is nilpotent, (b) `S(H₁)` is coherent,*
*(c) `|H:H₁| > 4|L:K|² + 1`.  Then `S(M)` is coherent.*  (p. 30.)

⚠ **Specialization**: the repo takes `H` nilpotent where the book takes `H/M` nilpotent (the §11
consumer has `M = 1`, so the two agree there); this is inherited from `six_three_descent`.

Everything is discharged: the minimal-`A` descent and maximal-`B` step (`six_three_descent`), the
`√`-arithmetic (`six_three_index_bound_general`), and the (6.2) break bound
(`exists_source_index_le_two_psi_of_imageData`).  The per-section `A' < K`, `B < K` needed by the
anchor come from `A' ≤ H₁ < H ≤ K`. -/
theorem six_three_of_imageData
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} [IsSolvable ↥K]
    (RD : InducedFamilyImageData hyp K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {H M H₁ : Subgroup ↥L} [Group.IsNilpotent ↥H] [M.Normal] [H₁.Normal]
    (hHnorm : H.Normal) (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H) (hHK : H ≤ K)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K H₁) (OddOrder.Peterfalvi.S04.supportInSubgroup A L)))
    (hbound : 4 * K.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K M) (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) := by
  refine six_three_of_six_two_oracle hHnorm hMH₁ hH₁H hHK _ _ (inducedKernelFamily K)
    ?_ hcoh hbound
  intro A' B _ _ hBA' hA'H₁ _hcentral hA'coh hBncoh
  have hA'K : A' < K := lt_of_le_of_lt hA'H₁ (lt_of_lt_of_le hH₁H hHK)
  exact exists_source_index_le_two_psi_of_imageData RD hodd hKsupp h1A hA'K
    (lt_of_le_of_lt hBA' hA'K) hA'coh hBncoh

end BookForm

end OddOrder.Peterfalvi.S08
