/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_YsetInner

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S08_CoherenceCorePart1` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]


/-- **(5.6.1) member coefficient `⟨Da.Y, ν χⱼ⟩` — the heart of the λ-form.**

The (5.6.1) projection coefficient (mmd 04.7 L79): for a member `χⱼ` with degree-matched difference
`χⱼ − aⱼ·χ₁` (the value enters via `hfound`, `inner_dade_extension_of_supported` applied to the
supported `δ = χⱼ − aⱼ·χ₁`),

`⟨Y, ν χⱼ⟩ = a·⟨χ₁, χⱼ⟩ − (a + μ)·aⱼ`,    where `Y = X − τ(χ − a·χ₁)`, `μ = ⟨τ(χ − a·χ₁), ν χ₁⟩`.

The computation: `⟨Y, νχⱼ⟩ = −⟨τ(χ−a·χ₁), νχⱼ⟩` (since `⟨X, νχⱼ⟩ = 0`, the member R-orthogonality);
split `νχⱼ = ν(χⱼ − aⱼ·χ₁) + aⱼ·νχ₁` (ν is `ℤ`-linear); the first part is `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩`
(`hfound`), which expands via `χ ⊥ χⱼ, χ₁` and `‖χ₁‖² = 1` to `−a·⟨χ₁, χⱼ⟩ + a·aⱼ`; the second is
`aⱼ·μ`.  With `λ := a + μ` this is `a·⟨χ₁,χⱼ⟩ − λ·aⱼ`, the `lambda_eq_zero_and_Z_eq_zero`
coefficient (`χ₁,χⱼ` orthonormal ⟹ `⟨χ₁,χⱼ⟩ = δ`, giving `a·[j=1] − λ·aⱼ`). -/
theorem inner_Y_extension_member_eq
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ) {chi1 cj : ClassFunction ↥L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj) ((χ : ClassFunction ↥L ℂ) - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner (χ : ClassFunction ↥L ℂ) cj = 0)
    (hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1)) * (aj : ℂ) := by
  -- `ν cj = ν(cj − aⱼ·χ₁) + aⱼ·ν χ₁` (ν is ℤ-linear).
  have hνcj : hS₁.extension cj
      = hS₁.extension (cj - aj • chi1) + aj • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul]; abel
  -- The source-side expansion `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩ = −a·⟨χ₁, χⱼ⟩ + a·aⱼ`.
  have hsrc : ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1)
      = -(a : ℂ) * ClassFunction.inner chi1 cj + (a : ℂ) * (aj : ℂ) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ aj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  -- The χ₁-side `⟨τ(χ − a·χ₁), aⱼ·ν χ₁⟩ = aⱼ·μ`.
  have hsmul : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (aj • hS₁.extension chi1) =
      (aj : ℂ) * ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ aj (hS₁.extension chi1),
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub, hνcj,
    ClassFunction.inner_add_right, hfound, hsrc, hsmul]
  ring

open scoped Classical in
/-- **Indexed integral orthogonal projection onto a ZIrr-orthonormal family.**

The `ι`-indexed form of `exists_intProjection_of_orthonormal_ZIrr`, the shape the (5.6.2)
integer-forcing `lambda_eq_zero_and_Z_eq_zero` consumes: for `φ ∈ ZIrr G` and an **injective**
orthonormal family `vc : ι → CF G` over `s : Finset ι` (each `vc i ∈ ZIrr G`), there are integer
coefficients `c i = ⟨φ, vc i⟩` and an orthogonal residual `Z` with

`φ = (∑_{i ∈ s} c i • vc i) + Z`    and    `⟨Z, vc i⟩ = 0`.

Reindexes the image-indexed primitive (`R = s.image vc`, `Finset.sum_image` with `hvcinj`). -/
theorem exists_indexed_intProjection_of_orthonormal_ZIrr
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G)
    (hvcinj : ∀ i ∈ s, ∀ j ∈ s, vc i = vc j → i = j)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (1 : ℂ) else 0) :
    ∃ (c : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (c i : ℂ)) ∧
      φ = (∑ i ∈ s, (c i : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hZR : ∀ α ∈ s.image vc, α ∈ ZIrr G := by
    intro α hα; rw [Finset.mem_image] at hα; obtain ⟨i, hi, rfl⟩ := hα; exact hvcZ i hi
  have horthR : ∀ α ∈ s.image vc, ∀ β ∈ s.image vc,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0 := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨i, hi, rfl⟩ := hα; obtain ⟨j, hj, rfl⟩ := hβ
    rw [horth i hi j hj]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (hvcinj i hi j hj h))]
  obtain ⟨c, Y, hcoeff, hsum, hY⟩ :=
    ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZR horthR
  refine ⟨fun i => c (vc i), Y, fun i hi => hcoeff (vc i) (Finset.mem_image_of_mem vc hi), ?_,
    fun i hi => hY (vc i) (Finset.mem_image_of_mem vc hi)⟩
  rw [hsum, Finset.sum_image hvcinj]

open scoped Classical in
/-- **(5.6.1)/(5.6.2) crux1 from the member family: `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.**

The capstone of the crux1 discharge — the genuine (5.6.1)/(5.6.2) `Y`-collapse for the induced
X-family, producing crux1 directly.  Given the finite orthonormal member family `{χᵢ = χmem i}` (all
in `S₁`, `‖χᵢ‖² = 1` — the case-A `X ⊆ Irr L`), the per-member (5.6.1) coefficient values
`hcoeffval` (from `inner_Y_extension_member_eq`), `a₁ = 1`, and the (6.6) degree inequality
`2a < ∑ aᵢ²`:

* the indexed projection (`exists_indexed_intProjection_of_orthonormal_ZIrr`) writes
  `Da.Y = ∑ᵢ (cᵢ:ℂ)·νχᵢ + Z` with integer `cᵢ = ⟨Da.Y, νχᵢ⟩`;
* `hcoeffval` identifies `cᵢ = a·[i=i₁] − λ·aᵢ` with the integer `λ = a + μ`, `μ = ⟨τ(χ−a·χ₁), νχ₁⟩`
  (an integer since both are virtual characters);
* the (5.6.2) integer-forcing `lambda_eq_zero_and_Z_eq_zero` then forces `λ = 0` (`Z = 0`), i.e.
  `μ = −a` — which **is** crux1.

`μ ∈ ℤ` is the load-bearing fact making `λ = a + μ` an integer; the degree inequality (6.6) is what
forces it to vanish. -/
theorem crux1_of_memberFamily
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  -- `hνZ` is derived (route A): `χmem i ∈ S₁ ⊆ ℤ[S₁]`, so `ν (χmem i) ∈ ℤ[Irr G]` by the
  -- `IsCoherent.extension_mem_ZIrr` field — it need not be injected as a hypothesis.
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- Orthonormality of the family `vc i = ν χᵢ` (ν isometry on `ℤ[S₁]` + member orthonormality).
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  have hvcinj : ∀ i ∈ s, ∀ j ∈ s,
      hS₁.extension (χmem i) = hS₁.extension (χmem j) → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h0 := horth i hi j hj
    rw [if_neg hne, hij, horth j hj j hj, if_pos rfl] at h0
    exact one_ne_zero h0
  obtain ⟨c, Z, hc_coeff, hYsum, hZortho⟩ :=
    exists_indexed_intProjection_of_orthonormal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) hνZ hvcinj horth
  -- Coefficient identification `(c i : ℂ) = a·[i=i₁] − (a+μ)·aᵢ`.
  have hcoeff_eq : ∀ i ∈ s, (c i : ℂ) =
      (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ) := by
    intro i hi
    rw [← hc_coeff i hi, hcoeffval i hi, hμeq]
    by_cases h : i = i₁
    · simp only [if_pos h]; push_cast; ring
    · simp only [if_neg h]; push_cast; ring
  -- The (5.6.1) λ-form and the (5.6.2) integer-forcing.
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ)
        • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hcoeff_eq i hi]
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction ↥L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast, mul_one,
      show (a : ℂ) * (a : ℂ) = (((a : ℝ) ^ 2 * 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) ((a : ℤ) + μ) Z
    (fun i => hS₁.extension (χmem i)) (fun _ => 1) (fun i => (deg i : ℝ))
    hY horth hZortho hψ (by simp [ha1]) (by positivity)
    (by simp only [mul_one]; exact hDeg)
  -- `λ = a + μ = 0 ⟹ μ = −a`, which is crux1.
  have hμval : μ = -(a : ℤ) := by omega
  rw [hμeq, hμval]; push_cast; ring

/-- **(T8.11 surgery, option A) coherence from the corrected extension image.**

The (5.6) adjoining step for the *induced (unsupported)* X-family.  Instead of mapping the new pair
`{χ, χ̄}` to a supported `ψ = 0` decomposition image (which needs `τχ ∈ ZIrr`, false for the
unsupported `χ = Ind θ`), `χ` is mapped to the **corrected extension image**
`X := τ(χ − a·χ₁) + a·νχ₁` (both terms integral).  This makes the (5.6.2) image equation `himg`
definitional, **bypassing** the `htau1_chi1` requirement `τχ₁ = νχ₁` that fails for unsupported `χ₁`.

Every remaining obligation of `retarget_isCoherent` is discharged from the source/Dade/ν isometries
plus the two crux inner products `hcrux1 : ⟨τ(χ−a·χ₁), νχ₁⟩ = −a` and `hcrux2 : ⟨τ(χ−χ̄), νχ₁⟩ = 0`
(the genuine (5.6) Feit–Sibley content, to be discharged separately via the degree inequality).  The
lattice orthogonality `hX_ortho`/`hXbar_ortho` is a span induction over
`ℤ[S₁] ⊆ span(ℤ[S₁,A] ∪ {χ₁})` (`hSgen`): clean on a supported `ξ` (`νξ = τξ` + Dade isometry) and
on `χ₁` via `hcrux1`/`hcrux2`. -/
noncomputable def retarget_isCoherent_of_extensionImage
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {chi1 : ClassFunction ↥L ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • chi1).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) = -(a : ℂ))
    (hcrux2 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • chi1})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      τ
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- `χ₁ ⊥ χ, χ̄` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ).conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference lattice `{χ−χ̄, χ−a·χ₁}` and the Dade isometry on it.
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
          -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  have hmemu : (χ : ClassFunction ↥L ℂ) - a • chi1 ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ψ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := fun φ ψ hφ hψ => by
    rw [hτ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
      hSdiff hφ hψ
  -- Dade-image inner products (Dade isometry + source orthonormality).
  have huu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 + (a : ℂ) ^ 2 := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 1 := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχχbar, hchi1χ, hchi1χbar, star_natCast]
    ring
  have hdd : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 2 := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hχχ, hχχbar, hχbarχ, hχbarχbar]
    ring
  have hdu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `hS₁.extension χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = 1 := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ :=
    τ ((χ : ClassFunction ↥L ℂ) - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
    with hXbar
  -- `X, X̄ ∈ ℤ[Irr G]`: the supported Dade images `(χ−a·χ₁)^τ`, `(χ−χ̄)^τ` are virtual (hypotheses),
  -- and `ν χ₁ ∈ ZIrr` is now recorded by the coherence's `extension_mem_ZIrr` field (`χ₁ ∈ S₁`).
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  -- `‖X‖² = 1`.
  have hXX : ClassFunction.inner X X = 1 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  -- `‖X̄‖² = 1`.
  have hXbarXbar : ClassFunction.inner Xbar Xbar = 1 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X, X̄⟩ = 0`.
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X̄, X⟩ = 0`.
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ντ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - a • chi1} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · exact hdiffasupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)),
            ← Nat.cast_smul_eq_nsmul ℂ a chi1]
          simp only [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
            hyχ, star_natCast]
          ring
        · rw [Set.mem_singleton_iff.mp hy1, hvu, hchi1chi1, mul_one]
    | zero => simp
    | add y z _ _ ihy ihz =>
        rw [map_add, ClassFunction.inner_add_left, ihy, ihz, ClassFunction.inner_add_left]; ring
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          ← Int.cast_smul_eq_zsmul ℂ c y, ClassFunction.inner_smul_left]; ring
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0 := by
    intro ξ hξ
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1), ClassFunction.inner_add_right,
      OddOrder.RepresentationTheory.inner_smul_right, hkey ξ (hSgen hξ),
      hS₁.extension_inner_eq ξ chi1 hξ (Submodule.subset_span hchi1)]
    simp only [star_natCast]; ring
  -- `⟨hS₁.extension ξ, τ(χ−χ̄)⟩ = 0` on `ℤ[S₁]` (similar span induction; clean — no `χ₁` term).
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ)
        (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y (χ : ClassFunction ↥L ℂ).conj = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
                  -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
                ClassFunction.support_neg]
              exact hdiffsupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) = X - a • hS₁.extension chi1 := by
    rw [hX]; abel
  exact OddOrder.Peterfalvi.S07.retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
/-- **(T-A1) Per-step X-family coherence adjoin from a member family.** (`noncomputable def`: the
conclusion `IsCoherent` lives in `Type`, carrying the new extension `ν`.)

The (5.6)/(6.6) per-step adjoining of a new induced X-pair `{χ, χ̄}` to a coherent set `S₁`, packaged
as a function of the member-family enumeration data.  This wires the landed crux1 chain (the genuine
(5.6.1)/(5.6.2) `Y`-collapse, `crux1_of_memberFamily`) into the adjoining bridge
(`retarget_isCoherent_of_extensionImage`).

Inputs: `IsCoherent τ S₁ A` for the Dade map `τ`, a non-real irreducible `χ` orthogonal to all of
`S₁` (with `χ̄` likewise), and a finite orthonormal member family `{χmem i}ᵢ∈ₛ ⊆ S₁` with degree
ratios `deg i` (base member `i₁` of ratio `1`), the degree-matched supported differences
`χmem i − deg i·χmem i₁` and `χ − a·χmem i₁`, and the supported Dade-image ZIrr fact
`(χ − a·χmem i₁)^τ ∈ ZIrr`.  The members' ZIrr-codomain `ν χmem i ∈ ZIrr` is read off the
`IsCoherent.extension_mem_ZIrr` field (route A: `χmem i ∈ S₁ ⊆ ℤ[S₁]`), not passed as a hypothesis.
The construction:

* `Da := decompositionDaFromDadeOfDiff …` (the χ-decomposition for `χ − a·χ₁`), with `Da.Y ∈ ZIrr`
  derived from `Da.X ∈ ℤ[R(χ)]` and `(χ − a·χ₁)^τ ∈ ZIrr`;
* per member `i`, the (5.2.e) orthogonality `⟨Da.X, ν χᵢ⟩ = 0`
  (`inner_decomposition_X_extension_member_eq_zero`) and the (5.6.1) cross-term `hfound`
  (`inner_dade_extension_of_supported`) assemble the coefficient `⟨Da.Y, ν χᵢ⟩`
  (`inner_Y_extension_member_eq`);
* `crux1_of_memberFamily` collapses the λ-form (degree inequality `2a < ∑ aᵢ²`) into
  crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`;
* crux2 `⟨τ(χ − χ̄), ν χ₁⟩ = 0` is clean from `R(χ) ⊥ R(χ₁)`;
* the bridge concludes `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`.

The lattice-generation conditions `hSgen`/`hgen` (structural facts about the accumulator `S₁`) are
threaded to the bridge; the chain fold (`xChainCoherent`) discharges them from the X-family
enumeration. -/
noncomputable def xAdjoinStep
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The ZIrr-codomain of each member is now recorded by the coherence's `extension_mem_ZIrr` field
  -- (`χmem i ∈ S₁ ⊆ ℤ[S₁]`), so it need not be passed as a hypothesis (route A).
  have hmemνZ : ∀ i ∈ s, hS₁.extension (χmem i : ClassFunction ↥L ℂ) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 i hi))
  -- The trivially-derived orthogonalities `χ, χ̄ ⊥ a·χ₁` for the χ-decomposition `Da`.
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ)
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The χ-decomposition for the degree-matched difference `χ − a·χ₁`.
  -- (`let`, not `have`/`set`, so `Da.tau1 = τ` / `Da.imageFamily = R(χ)` reduce definitionally.)
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by rw [hmemortho i₁ hi₁ i₁ hi₁]; simp
  -- The four `χmem i ⊥ {χ, χ̄}` orthogonalities (conjugate symmetry of `hχ_S1`/`hχbar_S1`).
  have hmemχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmemS1 i hi), star_zero]
  have hmemχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmemS1 i hi), star_zero]
  have hmembarχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmembarS1 i hi), star_zero]
  have hmembarχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmembarS1 i hi), star_zero]
  -- Per-member ν-aux decomposition `D'` and the (5.2.e) family orthogonality `R(χᵢ) ⊥ R(χ)`.
  -- (`let`, not `have`, so `(Dmem i hi).tau1 = ν` reduces definitionally for the `rfl` arguments.)
  let Dmem : ∀ i, i ∈ s → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i : ClassFunction ↥L ℂ) 0 := fun i hi =>
    memberExtensionDecomposition hyp hconj hS₁ (χmem i) (hmemreal i hi) (hmemdiffsupp i hi)
      (hmemS1 i hi) (hmembarS1 i hi) (hmemνZ i hi) (hmemconjortho i hi)
  have hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily :=
    fun i hi =>
      dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hconj (hmemreal i hi)
        (hmemdiffsupp i hi) hrealχ hdiffsuppχ (hmemχ i hi) (hmemχbar i hi) (hmembarχ i hi)
        (hmembarχbar i hi)
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) = 0 :=
    fun i hi => inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi) rfl
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hconj hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hconj hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamily hyp hconj
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) rfl hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp hconj
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

open scoped Classical in
/-- **Peterfalvi (5.6)** — quantitative coherence, contrapositive form ("B1").

The converse of the forward adjoining engine `xAdjoinStep`: under the same Dade /
member-family hypotheses, if `S₁ ∪ {χ, χ̄}` fails to be coherent then the degree
sum is bounded by `∑ᵢ (deg i)² ≤ 2 a`.  Writing `a = ψ(1)/χ₁(1)` and
`deg i = χᵢ(1)/χ₁(1)` this is Peterfalvi's non-coherence bound
`∑_{χ∈S₁} χ(1)² ≤ 2 ψ(1) χ₁(1)`, the quantitative input consumed by (6.2) on the
way to the degree bound (6.3)/(6.5).  Proof: contrapose `xAdjoinStep` over its
degree hypothesis `hDeg : 2 a < ∑ᵢ (deg i)²`. -/
theorem coherentDegreeSumBound_of_not_coherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStep hyp hconj hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemreal hmemdiffsupp hmemdegdiffsupp hmemS1 hmembarS1
    hmemconjortho hmemortho hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Peterfalvi (6.2), step (ii) — the `S(A)` degree-sum (B2 assembled).**
For `H ⊴ G`, `A ⊴ G`, `A ≤ H`, the induced family
`S(A) = {Ind_H^G θ | θ ∈ Irr H, A ⊆ Ker θ, θ ≠ 1}` satisfies
`∑_{χ ∈ S(A)} χ(1)²/‖χ‖² = [G:H]·(|H : A| − 1)`.

This assembles the orbit-counted identity `sum_div_normSq_induce_image_eq`
(`∑ = [G:H]·∑_{θ∈T}θ(1)²`, fibres of `θ ↦ Ind θ` are `G`-conjugacy orbits) with the inflation
degree-sum `sumInflatedDegreeSq_ntrivial` (`∑_{θ∈T}θ(1)² = |H ⧸ A| − 1`, Burnside on `H ⧸ A`).
The index set `T = {θ ∈ Irr H | A ⊆ Ker θ, θ ≠ 1}` is `G`-conjugation-invariant because `A ⊴ G`:
`Ker(θ^g) = g·(Ker θ)·g⁻¹ ⊇ g·A·g⁻¹ = A`.  This is the (6.2) input "step (ii)" that, with the
(5.6) bound B1 and the θ-bound, yields `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sum_div_normSq_induce_kernelFilter_eq {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    {A : Subgroup G} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        χ 1 ^ 2 / ClassFunction.inner χ χ
      = (H.index : ℂ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℂ) - 1) := by
  classical
  have hconj : ∀ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H),
      ∀ g : G, IrreducibleCharacter.conjBy g θ ∈ Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H) := by
    intro θ hθ g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    obtain ⟨hker, hne⟩ := hθ
    refine ⟨?_, ?_⟩
    · -- `A ⊆ Ker(θ^g)`: each `a ∈ A` has `g·a·g⁻¹ ∈ A ⊆ Ker θ`.
      intro a ha
      have hmemA : (⟨g * (a : G) * g⁻¹, ‹H.Normal›.conj_mem (a : G) a.2 g⟩ : ↥H)
          ∈ A.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact ‹A.Normal›.conj_mem (a : G) (Subgroup.mem_subgroupOf.mp ha) g
      have hk := hker hmemA
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hk
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def, conjBy_apply_one,
        IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply, hk,
        OddOrder.Peterfalvi.S03.characterDegree_def]
    · -- `θ^g ≠ 1`: conjugation is injective and fixes the trivial character.
      intro hc
      apply hne
      have h1 : IrreducibleCharacter.conjBy g⁻¹ (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one]
      rw [← h1, hc, IrreducibleCharacter.ext_iff]
      ext h
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      simp
  rw [sum_div_normSq_induce_image_eq _ hconj]
  congr 1
  exact sumInflatedDegreeSq_ntrivial (N := A.subgroupOf H)

open scoped Classical in
/-- **(T-A2 input) Per-step `xAdjoinStep` data bundle.**

Bundles the `xAdjoinStep` premises for one adjoining step of the X-family chain — the member family
`{χmem i}ᵢ∈ₛ ⊆ S₁` (orthonormal, with the ZIrr-codomain injections `ν χmem i ∈ ZIrr`), the new
character `χ`, the degree data, and the anchor-generation condition `hSgen` — into a single
structure, so the chain fold `xChainCoherent` can take the per-step data as a function of the
(inductively produced) accumulator coherence `hS₁`.  The full `hgen` field is derived in `adjoin`
from `hSgen` and the degree-matched support of `χ - aχ₁`.  The index type `ι` is a field (each step
has its own enumerated family). -/
structure XAdjoinStepInput
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) where
  hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ)
  hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1
  hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 1
  hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0
  hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0
  hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0
  hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0
  ι : Type
  s : Finset ι
  χmem : ι → IrreducibleCharacter ↥L
  deg : ι → ℕ
  i₁ : ι
  hi₁ : i₁ ∈ s
  hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ)
  hmemdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemdegdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁
  hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁
  hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
    (χmem i : ClassFunction ↥L ℂ).conj = 0
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
      if i = j then (1 : ℂ) else 0
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData hconj)
    ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G
  ha1 : deg i₁ = 1
  hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)})

/-- `xAdjoinStep` applied to a bundled `XAdjoinStepInput`, concluding coherence of
`S₁ ∪ {χ, χ̄}`. -/
noncomputable def XAdjoinStepInput.adjoin
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} {hconj : hyp.HConjInvariant}
    {S₁ : Set (ClassFunction ↥L ℂ)}
    {hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)}
    {χ : IrreducibleCharacter ↥L} (inp : XAdjoinStepInput hyp hconj hS₁ χ) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  have h1notA : (1 : G) ∉ A := by
    intro h
    exact hyp.ne_one h rfl
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro h
    exact h1notA (by simpa using h)
  have hdegχ : ((χ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      (inp.a : ℂ) * ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    have hzero :
        (((χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) : ClassFunction ↥L ℂ) 1 = 0 := by
      by_contra h
      exact h1A (inp.hdiffasuppχ (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ inp.a
      (inp.χmem inp.i₁ : ClassFunction ↥L ℂ), ClassFunction.smul_apply] at hzero
    exact sub_eq_zero.mp hzero
  have hchi1_ne : ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (inp.χmem inp.i₁)
    rw [hd1]
    exact_mod_cast hd.ne'
  have hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup A L)
      (χ := (χ : ClassFunction ↥L ℂ)) (chibar := (χ : ClassFunction ↥L ℂ).conj)
      (chi1 := (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) (a := inp.a)
      inp.hSgen hdegχ (OddOrder.Peterfalvi.S07.irreducibleCharacter_conj_apply_one χ)
      hchi1_ne h1A
  exact xAdjoinStep hyp hconj hS₁ χ inp.hrealχ inp.hdiffsuppχ inp.hχχ inp.hχbarχbar
    inp.hχχbar inp.hχbarχ inp.hχ_S1 inp.hχbar_S1 inp.s inp.χmem inp.deg inp.i₁ inp.hi₁
    inp.hmemreal inp.hmemdiffsupp inp.hmemdegdiffsupp inp.hmemS1 inp.hmembarS1
    inp.hmemconjortho inp.hmemortho inp.hdiffasuppχ inp.htau1_memaχ inp.ha1 inp.hDeg
    inp.hSgen hgen

/-- **(T-A2) The X-family coherence chain fold.**

Folds the per-step adjoining `xAdjoinStep` (via `XAdjoinStepInput.adjoin`) over a degree-monotone
conjugate-pair cover of `X` using the `coherentOfPairChainCover` engine: the base `S₀` is coherent
(`h0`), the `i`-th step adjoins the pair `(pair i) = (χₛ i, (χₛ i)̄)` to the accumulator
`pairUnion S₀ pair i` via `hstep i`, and the cover (`hS₀`/`hpairs`/`hcover`) recovers `X`.

This is the route-B custom fold of the §J.3.6 plan: rather than strengthening `IsCoherent` with a
ZIrr-codomain field (route A, T-A3), the per-step ZIrr-codomain facts are carried as fields of
`XAdjoinStepInput hyp hconj hcoh (χₛ i)`, supplied as a function of the *inductively produced*
accumulator coherence `hcoh`.  The construction of `hstep` from the actual degree-monotone
enumeration of `X` (the `exists_conjugatePairCover` data) is the remaining T-A4 wiring. -/
noncomputable def xChainCoherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X S₀ : Set (ClassFunction ↥L ℂ)}
    (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
    (χs : ℕ → IrreducibleCharacter ↥L)
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hS₀ : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₀ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hstep : ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) S₀ pair i)
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      XAdjoinStepInput hyp hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      X (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N hS₀ hpairs hcover h0
    (fun i hi hcoh => by
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
      exact (hstep i hi hcoh).adjoin)

/-- A pair disjoint from the accumulated prefix is orthogonal to that prefix.

This is the set-to-inner-product bridge used by the X-chain per-step builder: once the
conjugate-pair cover has proved `pairSet pair i` is disjoint from `pairUnion S0 pair i`, every
irreducible member of the prefix is distinct from both `χ_i` and `χ_i.conj`, so row
orthogonality gives the two `XAdjoinStepInput` fields `hχ_S1` and `hχbar_S1`. -/
theorem pairCover_orthogonal_to_prefix
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X S₀ : Set (ClassFunction Γ ℂ)} {pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ}
    {N i : ℕ} {χ : IrreducibleCharacter Γ}
    (hXirr : ∀ φ ∈ X, IsIrreducibleCharacter φ)
    (hS₀X : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X)
    (hpair0 : (pair i).1 = (χ : ClassFunction Γ ℂ))
    (hpair1 : (pair i).2 = (χ : ClassFunction Γ ℂ).conj)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i)
      (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i))
    (hi : i < N) :
    (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ).conj x = 0) := by
  classical
  have hprefixX : OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i ⊆ X := by
    intro x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hbase | ⟨j, hji, hjpair⟩
    · exact hS₀X hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hχpair : (χ : ClassFunction Γ ℂ) ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0]
  have hχbarpair : (χ : ClassFunction Γ ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair1]
  have hχbarIrr : IsIrreducibleCharacter (χ : ClassFunction Γ ℂ).conj :=
    hXirr _ (hpairs i hi hχbarpair)
  have hdisj_left := Set.disjoint_left.mp hdisj
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χ ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ) :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχpair
      exact hdisj_left hxpair hx
    simpa [ψ, hne] using irreducibleCharacter_inner_eq_ite χ ψ
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let χbar : IrreducibleCharacter Γ := ⟨(χ : ClassFunction Γ ℂ).conj, hχbarIrr⟩
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χbar ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ).conj :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχbarpair
      exact hdisj_left hxpair hx
    simpa [χbar, ψ, hne] using irreducibleCharacter_inner_eq_ite χbar ψ

/-- **Peterfalvi (6.3) degree-bound arithmetic core.**  The real/integer inequality at the heart of
Theorem (6.3) (mmd 04.8 L33): from the (6.2) consequence `b·x − 1 ≤ 2·a·b·√x` (with `a = |L:K|`,
`b = |K:H| ≥ 1`, `x = |H:A| ≥ 1`) one gets `x ≤ 4a² + 1`.

Proof: dividing by `b` and using `b ≥ 1` gives `x − 1 ≤ 2a√x`; squaring (`x − 1 ≥ 0`) gives
`(x − 1)² ≤ 4a²x`, i.e. `x² − (4a² + 2)x + 1 ≤ 0`; for a natural `x`, `x ≥ 4a² + 2` would give
`x² − (4a² + 2)x + 1 = x·(x − (4a² + 2)) + 1 ≥ 1 > 0`, a contradiction.  This is what (6.3) combines
with its hypothesis `|H:H₁| > 4|L:K|² + 1 ≤ x` to reach a contradiction (so `𝒮(M)` is coherent). -/
theorem degreeBound_le_of_sqrt_bound {a b x : ℕ} (hb : 1 ≤ b) (hx : 1 ≤ x)
    (h : (b : ℝ) * x - 1 ≤ 2 * a * b * Real.sqrt x) : x ≤ 4 * a ^ 2 + 1 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hsx : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  -- `x − 1 ≤ 2a√x` (divide `h` by `b`, drop `1/b ≤ 1`).
  have key : (x : ℝ) - 1 ≤ 2 * a * Real.sqrt x := by
    have hbx : (b : ℝ) * ((x : ℝ) - 1) ≤ (b : ℝ) * (2 * a * Real.sqrt x) := by
      have e1 : (b : ℝ) * ((x : ℝ) - 1) = (b : ℝ) * x - b := by ring
      have e2 : (b : ℝ) * (2 * a * Real.sqrt x) = 2 * a * b * Real.sqrt x := by ring
      rw [e1, e2]; nlinarith [h, hb1]
    exact le_of_mul_le_mul_left hbx hbpos
  -- `(x − 1)² ≤ (2a√x)² = 4a²x`.
  have hkey0 : (0 : ℝ) ≤ (x : ℝ) - 1 := by linarith
  have hrhs0 : (0 : ℝ) ≤ 2 * a * Real.sqrt x := by positivity
  have hsq : ((x : ℝ) - 1) ^ 2 ≤ 4 * (a : ℝ) ^ 2 * x := by
    have hprod := mul_le_mul key key hkey0 hrhs0
    have hrw : (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x) = 4 * (a : ℝ) ^ 2 * x := by
      rw [show (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x)
          = 4 * (a : ℝ) ^ 2 * (Real.sqrt x * Real.sqrt x) by ring, Real.mul_self_sqrt hx0]
    rw [hrw] at hprod
    nlinarith [hprod]
  -- `x² − 2x + 1 ≤ 4a²x` gives `x² < (4a²+2)x`, so `x < 4a²+2`, i.e. `x ≤ 4a²+1`.
  have hxlt : (x : ℝ) < 4 * (a : ℝ) ^ 2 + 2 := by
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    nlinarith [hsq, hxpos]
  have hxltN : x < 4 * a ^ 2 + 2 := by exact_mod_cast hxlt
  omega

/-- **Peterfalvi (6.5)(a) chief-factor arithmetic.**  If `c` and `a` are odd, `c ∣ a − 1`, and
`a > 1`, then `a ≥ 2c + 1` (mmd 04.8 L40).  Indeed `a − 1 = c·m` is even (as `a` is odd) and `c` is
odd, so `m` is even and nonzero, hence `m ≥ 2` and `a − 1 = c·m ≥ 2c`.

This is the step in (6.5)(a) ruling out an intermediate normal subgroup `H₁ ⊊ H₂ ⊊ K`: with
`a = |K : H₂|` (odd, dividing the odd `|L|`) and `c = |L : K|`, hypothesis (6.4.c) gives `c ∣ a − 1`,
so `|K : H₂| ≥ 2|L : K| + 1`; likewise `|H₂ : H₁| ≥ 2|L : K| + 1`, whence
`|K : H₁| ≥ (2|L : K| + 1)² > 4|L : K|² + 1`, contradicting the (6.3) bound. -/
theorem two_mul_add_one_le_of_odd_dvd {c a : ℕ} (hc : Odd c) (ha : Odd a) (hdvd : c ∣ a - 1)
    (ha1 : 1 < a) : 2 * c + 1 ≤ a := by
  obtain ⟨m, hm⟩ := hdvd
  have hcodd : c % 2 = 1 := Nat.odd_iff.mp hc
  have haodd : a % 2 = 1 := Nat.odd_iff.mp ha
  have hmeven : m % 2 = 0 := by
    have h1 : (c * m) % 2 = 0 := by
      have h2 : (a - 1) % 2 = 0 := by omega
      rwa [hm] at h2
    rw [Nat.mul_mod, hcodd, one_mul] at h1
    omega
  have hm2 : 2 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hz | hpos
    · rw [hz, mul_zero] at hm; omega
    · omega
  have h2c : 2 * c ≤ c * m := by nlinarith [hm2]
  omega

/-- **Peterfalvi (6.3)** index reduction.  From the degree bound (6.2) applied
with `C = H, D = A`, in index form `|K:H|·|H:A| − 1 ≤ 2·|L:K|·|K:H|·√|H:A|`,
together with `|H:H₁| ≤ |H:A|` (from `A ⊆ H₁`), the index `|H:H₁|` is at most
`4|L:K|² + 1`.  (Peterfalvi states the contrapositive: `|H:H₁| > 4|L:K|² + 1`
forces `S(M)` coherent.)  The `√`-manipulation is `degreeBound_le_of_sqrt_bound`
with `a = |L:K|, b = |K:H|, x = |H:A|`. -/
theorem six_three_HH1_le {LK KH HA HH1 : ℕ} (hKH : 1 ≤ KH) (hHH1le : HH1 ≤ HA)
    (hbound : (KH : ℝ) * (HA : ℝ) - 1 ≤ 2 * (LK : ℝ) * (KH : ℝ) * Real.sqrt (HA : ℝ)) :
    HH1 ≤ 4 * LK ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos HA with hHA0 | hHA
  · subst hHA0; omega
  · have hx := degreeBound_le_of_sqrt_bound hKH hHA hbound
    omega

/-- Arithmetic core of **Peterfalvi (6.5)(a),(c)**: since
`(2c+1)² = 4c²+4c+1 > 4c²+1` for `c ≥ 1`, an index `n` cannot satisfy both
`(2c+1)² ≤ n` and `n ≤ 4c²+1`. -/
theorem six_five_index_contradiction {LK n : ℕ} (hLK : 1 ≤ LK)
    (hge : (2 * LK + 1) * (2 * LK + 1) ≤ n) (hle : n ≤ 4 * LK ^ 2 + 1) : False := by
  nlinarith [hge, hle, hLK]

/-- **Peterfalvi (6.5)(a)** chief-factor step.  If a normal subgroup `H₂` sits
strictly between `H₁` and `K`, then (6.4.c) + odd order force
`|K:H₂|, |H₂:H₁| ≥ 2|L:K|+1` (via `two_mul_add_one_le_of_odd_dvd`), so
`|K:H₁| = |K:H₂|·|H₂:H₁| ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the (6.3)
bound `|K:H₁| ≤ 4|L:K|²+1`.  Hence `K/H₁` is a chief factor of `L`. -/
theorem six_five_chief_factor_contradiction {LK KH2 H2H1 KH1 : ℕ} (hLK : 1 ≤ LK)
    (hKH2 : 2 * LK + 1 ≤ KH2) (hH2H1 : 2 * LK + 1 ≤ H2H1)
    (hmul : KH1 = KH2 * H2H1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK
    (by rw [hmul]; exact Nat.mul_le_mul hKH2 hH2H1) hKH1le

/-- **Peterfalvi (6.5)(c)** : `|L:K|` does not divide `p − 1`.  If it did then
`p ≥ 2|L:K|+1` (`two_mul_add_one_le_of_odd_dvd`), and since `K/M` is a
non-abelian `p`-group `|K:H₁| ≥ p² ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the
(6.5)(a) bound `|K:H₁| ≤ 4|L:K|²+1`. -/
theorem six_five_c_contradiction {LK p KH1 : ℕ} (hLK : 1 ≤ LK)
    (hpge : 2 * LK + 1 ≤ p) (hp2 : p * p ≤ KH1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK (le_trans (Nat.mul_le_mul hpge hpge) hp2) hKH1le

/-- **Extension of `p`-groups is a `p`-group.**  If a normal subgroup `N` and the quotient `Γ ⧸ N`
are both `p`-groups (and `Γ` is finite), then `Γ` is a `p`-group: `|Γ| = |Γ ⧸ N|·|N| = p^b·p^a`
(Lagrange, `card_eq_card_quotient_mul_card_subgroup`), so `|Γ|` is a `p`-power (`IsPGroup.iff_card`).

A general group-theory brick; used by Peterfalvi (6.5)(b) to assemble "`K/M` is a `p`-group" from
its commutator subgroup `H₁/M` and the chief factor `K/H₁` (a `p`-group). -/
theorem isPGroup_of_quotient_of_subgroup {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hN : IsPGroup p ↥N) (hQ : IsPGroup p (Γ ⧸ N)) :
    IsPGroup p Γ := by
  rw [IsPGroup.iff_card] at hN hQ ⊢
  obtain ⟨a, ha⟩ := hN
  obtain ⟨b, hb⟩ := hQ
  exact ⟨b + a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hb, ha, pow_add]⟩

/-- `Abelianization.map` of a surjective homomorphism is surjective. -/
theorem Abelianization.map_surjective {Γ Δ : Type*} [Group Γ] [Group Δ] {f : Γ →* Δ}
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨Abelianization.of a, Abelianization.map_of f a⟩

/-- A finite `p`-group whose order is coprime to `p` is trivial. -/
theorem subsingleton_of_isPGroup_of_not_dvd {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Finite Δ]
    (hΔ : IsPGroup p Δ) (hnd : ¬ p ∣ Nat.card Δ) : Subsingleton Δ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΔ
  have hk0 : k = 0 := by
    by_contra hk0
    exact hnd (by rw [hk]; exact dvd_pow_self p hk0)
  rw [hk0, pow_zero] at hk
  exact (Nat.card_eq_one_iff_unique.mp hk).1

/-- **Peterfalvi (6.5)(b) reduction core: a finite nilpotent group with `p`-group abelianization is
a `p`-group.**

Let `P` be the Sylow `p`-subgroup, normal since `Γ` is nilpotent.  The quotient `Q = Γ ⧸ P` has order
`[Γ:P]` coprime to `p`, so `Abelianization Q` — both a `p`-group (a homomorphic image of
`Abelianization Γ`, `Abelianization.map` of `Γ ↠ Q`) and of order dividing `[Γ:P]` — is trivial.
Hence `Q` is perfect (`commutator Q = ⊤`); being nilpotent (a quotient of `Γ`) and hence solvable, it
is therefore trivial (`commutator_lt_top` for a nontrivial solvable group).  So `P = ⊤` and `Γ` is a
`p`-group (`isPGroup_of_quotient_of_subgroup`).

This is the (6.5)(b) step "since `K/M` is nilpotent with commutator `H₁/M` and `K/H₁` a chief factor,
`K/M` is a `p`-group" (mmd 04.8 L45). -/
theorem isPGroup_of_isNilpotent_of_isPGroup_abelianization {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (h : IsPGroup p (Abelianization Γ)) : IsPGroup p Γ := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p Γ) := inferInstance
  haveI hPnormal : (↑P : Subgroup Γ).Normal := by
    have htfae := (Group.isNilpotent_of_finite_tfae (G := Γ)).out 0 3
    exact htfae.mp ‹_› p ‹_› P
  -- `Abelianization Q` is a `p`-group (image of `Abelianization Γ`).
  have hQab_p : IsPGroup p (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    h.of_surjective _ (Abelianization.map_surjective (QuotientGroup.mk'_surjective _))
  -- ... and trivial: its order divides `Nat.card Q = [Γ:P]`, coprime to `p`.
  have hofsurj : Function.Surjective (Abelianization.of :
      (Γ ⧸ (↑P : Subgroup Γ)) →* Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    fun y => QuotientGroup.induction_on y fun a => ⟨a, rfl⟩
  haveI hQab_triv : Subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    subsingleton_of_isPGroup_of_not_dvd hQab_p
      (fun hp => P.not_dvd_index (hp.trans (Subgroup.card_dvd_of_surjective _ hofsurj)))
  -- `Abelianization Q` trivial ⟹ `commutator Q = ⊤` ⟹ (nilpotent ⟹ solvable) `Q` trivial.
  haveI hQ_triv : Subsingleton (Γ ⧸ (↑P : Subgroup Γ)) := by
    rcases subsingleton_or_nontrivial (Γ ⧸ (↑P : Subgroup Γ)) with hs | hns
    · exact hs
    · exfalso
      haveI := hns
      have hlt : commutator (Γ ⧸ (↑P : Subgroup Γ)) < ⊤ :=
        IsSolvable.commutator_lt_top_of_nontrivial (G := Γ ⧸ (↑P : Subgroup Γ))
      refine absurd ?_ hlt.ne
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) 1 hQab_triv
  -- `Q` trivial ⟹ `Γ` is a `p`-group (Sylow `P` is `p`, quotient `Q` trivially `p`).
  refine isPGroup_of_quotient_of_subgroup P.isPGroup' ?_
  rw [IsPGroup.iff_card]
  exact ⟨0, by rw [pow_zero]; exact @Nat.card_of_subsingleton (Γ ⧸ (↑P : Subgroup Γ)) 1 hQ_triv⟩

/-- **Group-theory core of Peterfalvi (6.5)(a),(b): a Frobenius-acted abelian section obeying the
(6.3) index bound is a `p`-group.**

Let a finite group `R` act on a finite abelian group `A` by automorphisms, *fixed-point-freely*
(`IsFrobeniusAction R A`: no nonidentity `r ∈ R` fixes a nonidentity `a ∈ A`).  If `|A|` and `|R|`
are odd and `|A| ≤ 4|R|² + 1`, then `A` is a `p`-group for some prime `p`.

This is the abstract content of Peterfalvi (6.5).  In the Sibley setting `A = K/H₁` is the
abelianization section and `R = L/K` is the Frobenius complement; (6.5)(a) says `K/H₁` is a chief
factor.  Here the chief-factor argument is run through the `p`-primary component: if `A` had a prime
divisor `p` whose Sylow subgroup `P` were proper (i.e. `A` were not a `p`-group), then `P`
(characteristic in the abelian `A`, hence `R`-invariant) and the quotient index `|A : P|` would both
be nontrivial, odd, and `≡ 1 (mod |R|)` — the first two by Frobenius `card_modEq_one` applied to the
whole action and the restricted action on `P` (`IsFrobeniusAction.subgroup`), the index by the
arithmetic `|A| = |A:P|·|P|`, `|A| ≡ |P| ≡ 1`.  Oddness then forces `|P|, |A:P| ≥ 2|R| + 1`
(`two_mul_add_one_le_of_odd_dvd`), so `|A| = |A:P|·|P| ≥ (2|R|+1)² > 4|R|² + 1`, contradicting the
bound (`six_five_chief_factor_contradiction`).

The `|A| ≤ 4|R|² + 1` bound is the single character-theoretic input ((6.2)/(6.3); in the Sibley
setup supplied by `theta_degree_le_index_mul_sqrt_index`).  Everything else is discharged here. -/
theorem isPGroup_of_card_le_of_isFrobeniusAction {A R : Type*} [CommGroup A] [Finite A]
    [Group R] [Finite R] [MulDistribMulAction R A]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R A)
    (hAodd : Odd (Nat.card A)) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card A ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype R := Fintype.ofFinite R
  by_contra hcon
  -- `A` is nontrivial: a trivial group is a `p`-group for every prime.
  rcases eq_or_ne (Nat.card A) 1 with hA1 | hA1
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hcon ⟨2, Nat.prime_two, IsPGroup.iff_card.mpr ⟨0, by rw [pow_zero, hA1]⟩⟩
  -- Otherwise take a prime divisor `p` of `|A|` and its Sylow `p`-subgroup `P`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card A).exists_prime_and_dvd hA1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  -- `|P| > 1` because `p ∣ |P|`.
  have hpP : p ∣ Nat.card (P : Subgroup A) := P.dvd_card_of_dvd_card hpdvd
  have hcardP : 1 < Nat.card (P : Subgroup A) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpP)
  -- `P` is normal (abelian ambient), hence characteristic.
  have hPnormal : (P : Subgroup A).Normal :=
    ⟨fun n hn g => by
      have heq : g * n * g⁻¹ = n := by rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hn⟩
  have hPchar : (P : Subgroup A).Characteristic := P.characteristic_of_normal hPnormal
  -- `R` acts by automorphisms, which fix the characteristic `P` setwise: `P` is `R`-invariant.
  have hinv : ∀ r : R, ∀ m ∈ (P : Subgroup A), r • m ∈ (P : Subgroup A) := by
    intro r m hm
    have hmap : (P : Subgroup A).map (MulDistribMulAction.toMulAut R A r).toMonoidHom
        = (P : Subgroup A) :=
      Subgroup.characteristic_iff_map_eq.mp hPchar (MulDistribMulAction.toMulAut R A r)
    have hmem : (MulDistribMulAction.toMulAut R A r).toMonoidHom m ∈ (P : Subgroup A) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- `A` not a `p`-group ⟹ `P ≠ ⊤` ⟹ `|A : P| > 1`.
  have hindex : 1 < (P : Subgroup A).index := by
    by_contra hle
    have h : (P : Subgroup A).index ≤ 1 := Nat.not_lt.mp hle
    have hidxpos : 0 < (P : Subgroup A).index := by
      have hmc := Subgroup.index_mul_card (P : Subgroup A)
      rcases Nat.eq_zero_or_pos (P : Subgroup A).index with h0 | h0
      · rw [h0, zero_mul] at hmc; exact absurd hmc.symm Nat.card_pos.ne'
      · exact h0
    have hidx1 : (P : Subgroup A).index = 1 := by omega
    have hPtop : (P : Subgroup A) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hcardeq : Nat.card (P : Subgroup A) = Nat.card A := by
      rw [hPtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    exact hcon ⟨p, hp, IsPGroup.iff_card.mpr ⟨n, by rw [← hcardeq, hn]⟩⟩
  -- Frobenius `card ≡ 1 (mod |R|)` for the whole action and the restricted action on `P`.
  haveI : Fintype (P : Subgroup A) := Fintype.ofFinite _
  have hAmod : Nat.card A ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrob.card_modEq_one
  letI instP : MulDistribMulAction R (P : Subgroup A) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction
      (P : Subgroup A) hinv
  have hFrobP : @OddOrder.Isaacs.Ch06.IsFrobeniusAction R (P : Subgroup A) _ _ instP :=
    hFrob.subgroup (P : Subgroup A) hinv
  have hPmod : Nat.card (P : Subgroup A) ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobP.card_modEq_one
  -- `|R| ∣ |P| - 1` and (via `|A| = |A:P|·|P|`) `|R| ∣ |A:P| - 1`.
  have hRdvdP : Nat.card R ∣ Nat.card (P : Subgroup A) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hPmod.symm
  have hmul : (P : Subgroup A).index * Nat.card (P : Subgroup A) = Nat.card A :=
    Subgroup.index_mul_card _
  have hidxmod : (P : Subgroup A).index ≡ 1 [MOD Nat.card R] := by
    have h1 : (P : Subgroup A).index * Nat.card (P : Subgroup A)
        ≡ (P : Subgroup A).index * 1 [MOD Nat.card R] := Nat.ModEq.mul_left _ hPmod
    rw [mul_one, hmul] at h1
    exact h1.symm.trans hAmod
  have hRdvdidx : Nat.card R ∣ (P : Subgroup A).index - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hidxmod.symm
  -- Oddness of both factors (they multiply to the odd `|A|`).
  have hAodd' : Odd ((P : Subgroup A).index * Nat.card (P : Subgroup A)) := by
    rw [hmul]; exact hAodd
  obtain ⟨hidxodd, hcardPodd⟩ := Nat.odd_mul.mp hAodd'
  -- Each factor is `≥ 2|R| + 1`; their product exceeds the bound — contradiction.
  have hbP : 2 * Nat.card R + 1 ≤ Nat.card (P : Subgroup A) :=
    two_mul_add_one_le_of_odd_dvd hRodd hcardPodd hRdvdP hcardP
  have hbidx : 2 * Nat.card R + 1 ≤ (P : Subgroup A).index :=
    two_mul_add_one_le_of_odd_dvd hRodd hidxodd hRdvdidx hindex
  exact six_five_chief_factor_contradiction Nat.card_pos hbidx hbP hmul.symm hbound

/-- **Peterfalvi (6.5)(b) reduction: `H` is a `p`-group.**  Assemble the chief-factor core
`isPGroup_of_card_le_of_isFrobeniusAction` (the abelianization `Abelianization H` is a `p`-group)
with `isPGroup_of_isNilpotent_of_isPGroup_abelianization` (a nilpotent group with `p`-group
abelianization is a `p`-group).

Let `H` be a finite nilpotent group whose abelianization `Abelianization H` carries a
fixed-point-free action of a finite group `R` (in the Sibley setting `R = L/H` is the Frobenius
complement acting on `H/H'` by conjugation), with `|Abelianization H|` and `|R|` odd and
`|Abelianization H| ≤ 4|R|² + 1`.  Then `H` is a `p`-group for some prime `p`.

This is the group-theory conclusion of Peterfalvi (6.5) ("we may assume `H` is a non-abelian
`p`-group") in the form the (6.8) capstone consumes; the `≤ 4|R|² + 1` bound is the single
character-theoretic input ((6.2)/(6.3)), and the fixed-point-free `R`-action on `Abelianization H`
is supplied from the Frobenius alternative (6.8)(c1) / (6.4.c). -/
theorem isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {R : Type*} [Group R] [Finite R] [MulDistribMulAction R (Abelianization H)]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R (Abelianization H))
    (hHodd : Odd (Nat.card (Abelianization H))) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  obtain ⟨p, hp, hPab⟩ :=
    isPGroup_of_card_le_of_isFrobeniusAction hFrob hHodd hRodd hbound
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, isPGroup_of_isNilpotent_of_isPGroup_abelianization hPab⟩

/-- **Peterfalvi (6.5)(b) reduction in the Frobenius case (6.8)(c1): the kernel is a `p`-group.**
If `G = N ⋊ A` is a Frobenius group with nilpotent kernel `N`, `|Abelianization N|` and `|A|` are
odd, and `|Abelianization N| ≤ 4|A|² + 1`, then `N` is a `p`-group for some prime `p`.

This is `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` with the fixed-point-free
`A`-action on `Abelianization N` supplied directly from the Frobenius group: `A` acts
fixed-point-freely on `N` by conjugation (`toFrobeniusAction`), and since `⁅N,N⁆` is characteristic
in `N` (hence `A`-invariant), the action descends fixed-point-freely to the abelianization
`N / ⁅N,N⁆` (`IsFrobeniusAction.quotient`).  In the (6.8) capstone this is the Frobenius alternative
`hyp.cases.inl : IsFrobeniusGroup ↥L H W₁` (with `N = H`, `A = W₁`); the only remaining input is the
`≤ 4|W₁|² + 1` bound from the character theory ((6.2)/(6.3)). -/
theorem isPGroup_of_isFrobeniusGroup_of_card_le {G : Type*} [Group G] [Finite G]
    {N A : Subgroup G} [Group.IsNilpotent ↥N]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    (hHodd : Odd (Nat.card (Abelianization ↥N))) (hAodd : Odd (Nat.card ↥A))
    (hbound : Nat.card (Abelianization ↥N) ≤ 4 * Nat.card ↥A ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥N := by
  letI : N.Normal := h.isNormal
  letI actN : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hFrobN : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A ↥N := h.toFrobeniusAction
  -- `⁅N,N⁆` is characteristic in `N`, hence preserved by the automorphism `A`-action.
  have hM : ∀ a : ↥A, ∀ m ∈ commutator ↥N, a • m ∈ commutator ↥N := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥N).Characteristic) (MulDistribMulAction.toMulAut ↥A ↥N a)
    have hmem : (MulDistribMulAction.toMulAut ↥A ↥N a).toMonoidHom m ∈ commutator ↥N := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- The fixed-point-free action descends to the abelianization quotient.
  letI actAb : MulDistribMulAction ↥A (Abelianization ↥N) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator ↥N) hM
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A (Abelianization ↥N) :=
    hFrobN.quotient (commutator ↥N) hM
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hAodd hbound

/-- **Peterfalvi (6.5)(b) reduction in the certain-type case (6.8)(c2): the kernel is a `p`-group.**
If a finite group `W` acts on a finite nilpotent group `H` with `(|W|, |H|) = 1`, such that for
every nonidentity `w ∈ W` the `w`-fixed points of `H` lie in `⁅H,H⁆` (the certain-type centralizer
condition `C_H(x) = W₂ ⊆ ⁅H,H⁆`), and `|Abelianization H|`, `|W|` are odd with
`|Abelianization H| ≤ 4|W|² + 1`, then `H` is a `p`-group for some prime `p`.

This is the (6.8)(c2) analogue of `isPGroup_of_isFrobeniusGroup_of_card_le`.  Here `W` does *not*
act fixed-point-freely on `H` (the fixed points `C_H(x) = W₂` are nontrivial), but since
`W₂ ⊆ ⁅H,H⁆` the action descends fixed-point-freely to `Abelianization H` (`IsFrobeniusAction`'s
`quotient_of_fixedPoints_le`, via the coprime fixed-point lifting Isaacs Cor 3.28); then the
(6.5)(b) reduction `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` applies.  In the
(6.8) capstone the fixed-points hypothesis is discharged from the certain-type fields
`centralizer_W2` (`C_L(x) ⊓ H = W₂`) and `W₂ ⊆ ⁅H,H⁆`, and the coprimality from the Hall datum
`gcd(|H|, |W₁|) = 1`. -/
theorem isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator {H W : Type*}
    [Group H] [Finite H] [Group.IsNilpotent H] [Group W] [Finite W] [MulDistribMulAction W H]
    (hCop : Nat.Coprime (Nat.card W) (Nat.card H))
    (hfix : ∀ w : W, w ≠ 1 → ∀ x : H, w • x = x → x ∈ commutator H)
    (hHodd : Odd (Nat.card (Abelianization H))) (hWodd : Odd (Nat.card W))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card W ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  have hMinv : ∀ a : W, ∀ m ∈ commutator H, a • m ∈ commutator H := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator H).Characteristic) (MulDistribMulAction.toMulAut W H a)
    have hmem : (MulDistribMulAction.toMulAut W H a).toMonoidHom m ∈ commutator H := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  letI actAb : MulDistribMulAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator H) hMinv
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le hCop (commutator H) hMinv hfix
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hWodd hbound

/-- A finite group with non-trivial abelianization carries a non-trivial linear character
`Γ →* ℂˣ`. Equivalently (via `IsSolvable.commutator_lt_top_of_nontrivial`) every non-trivial
finite solvable group has one.

This is the existence ingredient feeding **Peterfalvi (6.2)**: the section `K/A` (solvable and
non-trivial, since `A ⊊ K`) carries an irreducible character of degree `1`, which is what makes
`S(A)` non-empty so the degree bound `2|L:C|√|C:D| ≥ |K:A| − 1` has content. The proof reduces to
the abelianization `Γ ⧸ ⁅Γ,Γ⁆` (non-trivial exactly when `⁅Γ,Γ⁆ ≠ ⊤`) and uses that `ℂ` is
separably closed of characteristic zero, hence has enough roots of unity
(`IsSepClosed.hasEnoughRootsOfUnity`, instantiated at `n = exponent` via the supplied `NeZero`). -/
theorem exists_monoidHom_units_ne_one_of_commutator_ne_top {Γ : Type*} [Group Γ] [Finite Γ]
    (h : commutator Γ ≠ ⊤) : ∃ χ : Γ →* ℂˣ, χ ≠ 1 := by
  -- `Abelianization Γ = Γ ⧸ ⁅Γ,Γ⁆` is non-trivial precisely because `⁅Γ,Γ⁆ ≠ ⊤`.
  haveI : Nontrivial (Abelianization Γ) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact h (by
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization Γ) 1 hns)
  obtain ⟨a, ha⟩ := exists_ne (1 : Abelianization Γ)
  -- `ℂ` separably closed + characteristic zero ⟹ enough roots of unity at `n = exponent`.
  haveI : NeZero ((Monoid.exponent (Abelianization Γ) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization Γ) ℂ ha
  -- Pull `φ` back along the surjection `Abelianization.of`; non-triviality transports.
  refine ⟨φ.comp Abelianization.of, fun hcon => hφ ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g : Γ, Abelianization.of g = a := QuotientGroup.mk_surjective a
  simpa using DFunLike.congr_fun hcon g

/-- A finite group with non-trivial abelianization carries a non-trivial **degree-one irreducible
character**. This is the `IrreducibleCharacter`-level form of the **Peterfalvi (6.2)** existence
ingredient: bridging `exists_monoidHom_units_ne_one_of_commutator_ne_top` through the linear
character functor `linearIrreducibleCharacter`. Applied to the section `K/A` (non-trivial solvable)
and inflated to `K`, it furnishes a non-trivial `θ ∈ Irr K` with `A ⊆ ker θ`, i.e. a member of
`S(A)`. -/
theorem exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top {Γ : Type*}
    [Group Γ] [Finite Γ] (h : commutator Γ ≠ ⊤) :
    ∃ χ : IrreducibleCharacter Γ,
      χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ ∧
      (χ : ClassFunction Γ ℂ) (1 : Γ) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.linearIrreducibleCharacter φ, ?_,
    OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one φ⟩
  rw [Ne, OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff]
  exact hφ

/-- **Peterfalvi (6.2): `S(A)` is non-empty when `K/A` is non-trivial.**  If `A ◁ K` is normal with
`K/A` of non-trivial abelianization (in particular when `K/A` is a non-trivial solvable group, e.g.
`A ⊊ K` with `K` solvable), then `K` carries a non-trivial irreducible character `θ` of degree `1`
with `A ⊆ ker θ` — i.e. a member of `S(A) = {Ind_K^L θ | θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1}`.

This is the concrete, `(K, A)`-level existence ingredient for the (6.2) degree bound: it inflates
the degree-one character produced on the section `K/A`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`) back up to `K` via
`OddOrder.RepresentationTheory.inflate`, transporting non-triviality
(`inflate_eq_trivial_iff`), the kernel containment (`subset_characterKernel_inflate`) and the
degree (`inflate_apply_one`). -/
theorem exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top {K : Type*}
    [Group K] [Finite K] (N : Subgroup K) [N.Normal] (h : commutator (K ⧸ N) ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter K ∧
      (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) ∧
      (θ : ClassFunction K ℂ) (1 : K) = 1 := by
  obtain ⟨χbar, hne, hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.inflate N χbar, ?_,
    OddOrder.RepresentationTheory.subset_characterKernel_inflate N χbar, ?_⟩
  · rw [Ne, OddOrder.RepresentationTheory.inflate_eq_trivial_iff]; exact hne
  · rw [OddOrder.RepresentationTheory.inflate_apply_one]; exact hdeg

/-- **Peterfalvi (6.8): Dade-based carrier** (T1, faithful replacement of `SibleySetup`).

The legacy `SibleySetup` carried an opaque `coherence.tau` with a *global* `IsIntegralIsometry`,
which does not exist in Feit–Thompson (`dim CF(L) > dim CF(G)`); its `CoherenceTarget` was
therefore undischargeable. This carrier instead packages the genuine §4 Dade datum
`dade : S04.Hypothesis G H^# L`, so the coherence map `tau` is the **real**
`dadeIntegralCharacterMap` and `CoherenceTarget` is `IsCoherent` for that map — exactly the shape
the §7 coherence engine produces (`coherentUnion_of_glued`, `coherentEqualDegree_fromDade`, …),
realizing "τ coincides with the Dade isometry relative to (A,L,G)" (mmd 04.8 L150).

**Migration status (T1, `notes/peterfalvi/s08_6_8_assembly_plan.md`)**: this commit lands the
re-parametrization (`L : Subgroup G`, source type `↥L`) and the real-`tau` `CoherenceTarget`. The
remaining (6.8) hypotheses — `S = {Ind_H^L θ | θ ≠ 1}`, the split `L = H ⋊ W₁`, `H` nilpotent, and
the case (c1)/(c2) disjunction (`S06.CertainTypeHypothesis`) — are added next, after which
`sibleySetup_is_coherent` is restated against this carrier and the legacy `SibleySetup` removed. -/
structure SibleyDadeHypothesis (G : Type*) [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (L : Subgroup G) [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (H : Subgroup ↥L) [Invertible (Nat.card ↥H : ℂ)] where
  /-- A complement-side subgroup `W₁`; the split `L = H ⋊ W₁` is added in the next migration step. -/
  W1 : Subgroup ↥L
  H_ne_bot : H ≠ ⊥
  H_normal : H.Normal
  /-- `H` is nilpotent (Peterfalvi (6.8.a)). -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- `L = H ⋊ W₁`: `W₁` is a complement to the normal `H` (Peterfalvi (6.8.a)). -/
  split : Subgroup.IsComplement' H W1
  W1_nontrivial : W1 ≠ ⊥
  card_L_odd : Odd (Nat.card L)
  /-- `H^#` is a TI-subset of `G` relative to `L` (corrected ambient: TI in `G`, not in `↥L`). -/
  H_sharp_ti : OddOrder.GroupTheory.IsTISubset (sharpImage H) L
  /-- The §4 Dade datum on `A = H^#`; its Dade isometry *is* `tau`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G (sharpImage H) L
  hconj : dade.HConjInvariant
  /-- In the TI situation ((6.8.a): `H^#` is a TI-subset of `G` with normalizer `L`), the §4 Dade
  datum's local subgroups are trivial, `dade.H a = ⊥` — i.e. `dade` is the Dade map of the
  TI-subset construction (`S04.of_isTISubset`, whose `H a = ⊥`, S04:308).  This faithful (6.8.a)
  fact makes the Dade map agree with `Ind_L^G` on the supported lattice, yielding the (2.7)
  reciprocity `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` (`inner_tau_eq_inner_restrict`), the gateway to the
  (6.8.1) `Res_L(η₁^{τ₁})` decomposition. -/
  dade_H_eq_bot : ∀ a : {a : G // a ∈ sharpImage H}, dade.H a = ⊥
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded **faithfully** by a `S06.Hypothesis46` (the *full*
    (4.6): the (4.2) structure plus the ambient (3.1) TI-cyclic `tic` for `(G, W)` (4.6.b), the
    covering `A_covers` (4.6.d), and the enlarged Dade datum `dade0`/`tau` on `A₀ = A ∪ Vᴸ`) on
    the *same* Dade datum (`h46.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime,
    `W₂ ⊆ [H,H]`, and the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a
    cyclic *Hall* subgroup of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This
    coprimality is the input to Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a
    `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `h46.K = H`), and the
  (4.2)/(6.8) complement is shared (`h46.W1 = W1`, both giving `L = H ⋊ W₁`).

  **Faithfulness note (2026-06-13):** the textbook (6.8)(c2) literally reads "Hypothesis (4.6)
  holds" (mmd 04.8 L146), and (4.6) (mmd 04.6 L53-63) includes (4.6.b) "G and W satisfy (3.1)" —
  i.e. the ambient TI-cyclic on `W − W₂`.  This is *not* derivable from a bare
  `CertainTypeHypothesis` (which carries only the (4.2) structure on `↥L` plus the §4 Dade datum on
  `A`): TI in the ambient `G` quantifies over all of `G`, not just `↥L`, so it cannot be lifted from
  the (4.3.a) TI in `↥L`.  The earlier `cases` encoding used the *weaker* `CertainTypeHypothesis`,
  which made the c2 X-coherence un-constructible (the impossible "build the ambient TI from
  nothing").  Strengthening `cases` to `Hypothesis46` restores faithfulness and moves the
  (4.6)-construction obligation to the `SibleyDadeHypothesis` *producer* (the §9 (7.10) application,
  where the maximal-subgroup structure supplies it), exactly as the textbook does. -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L,
      h46.dade = dade ∧ h46.K = H ∧ h46.W1 = W1 ∧
        (Nat.card h46.W2).Prime ∧ h46.W2 ≤ ⁅H, H⁆ ∧
        Nat.Coprime (Nat.card ↥H) (Nat.card W1)

/-- **(T7-c2 case A, brick ①)** A multiplicative `ℂ`-valued function `f` (e.g. a linear character)
that is *invariant* under a fixed-point-free endomorphism `σ` is identically `1`.  Indeed
`z ↦ z·(σ z)⁻¹` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`), and
`f (z₀·(σ z₀)⁻¹) = f z₀ · f (σ z₀)⁻¹ = f z₀ · (f z₀)⁻¹ = 1` using `f ∘ σ = f`. -/
theorem eq_one_of_fixedPointFree_invariant {Z : Type*} [Group Z] [Finite Z]
    {F : Type*} [FunLike F Z Z] [MonoidHomClass F Z Z] {σ : F}
    (hσ : MonoidHom.FixedPointFree σ)
    {f : Z → ℂ} (hf_mul : ∀ a b, f (a * b) = f a * f b) (hf_one : f 1 = 1)
    (hinv : ∀ z, f (σ z) = f z) (z : Z) : f z = 1 := by
  have hne : ∀ a : Z, f a ≠ 0 := fun a ha => one_ne_zero
    (show (1 : ℂ) = 0 by rw [← hf_one, ← mul_inv_cancel a, hf_mul, ha, zero_mul])
  have hf_inv : ∀ a : Z, f a⁻¹ = (f a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hf_mul, mul_inv_cancel, hf_one])
  obtain ⟨z₀, hz₀⟩ := hσ.commutatorMap_surjective z
  rw [MonoidHom.commutatorMap_apply, div_eq_mul_inv] at hz₀
  calc f z = f (z₀ * (σ z₀)⁻¹) := by rw [hz₀]
    _ = f z₀ * f (σ z₀)⁻¹ := hf_mul _ _
    _ = f z₀ * (f (σ z₀))⁻¹ := by rw [hf_inv]
    _ = f z₀ * (f z₀)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel₀ (hne z₀)

/-- A subgroup contained in a **prime-order** subgroup is either trivial or the whole subgroup.

Group-theoretic core of the math-case (A)/(B) dichotomy of Peterfalvi (6.8): with `|W₂|` prime
and `Z(H) ⊓ W₂ ≤ W₂`, the intersection is `⊥` (case A, `Z(H) ∩ W₂ = 1`) or `W₂` (case B, forcing
`W₂ ⊆ Z(H)`). -/
theorem eq_bot_or_eq_of_le_of_card_prime {Γ : Type*} [Group Γ] {K W : Subgroup Γ}
    [Finite W] (hle : K ≤ W) (hp : (Nat.card W).Prime) : K = ⊥ ∨ K = W := by
  rcases (Nat.dvd_prime hp).mp (Subgroup.card_dvd_of_le hle) with h1 | hcard
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

/-- **(T8.11p0) natural degree witnesses for one X-adjoin member family.**

This packages the positive natural degree of the new character, the anchor, and every member of a
finite accumulator family, together with the member square-sum `D`.  The hypothesis `i₁ ∈ s`
ensures `D` is positive. -/
theorem exists_natDegreeData_for_xAdjoinMemberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ∃ dχ d₁ D : ℕ, ∃ dmem : ι → ℕ,
      (χ : ClassFunction G ℂ) 1 = (dχ : ℂ) ∧
      (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) ∧
      (∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ)) ∧
      (∑ i ∈ s, dmem i * dmem i = D) ∧
      0 < d₁ ∧ 0 < D := by
  classical
  obtain ⟨dχ, _hdχpos, hχone⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  let dmem : ι → ℕ := fun i =>
    (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose
  have hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ) := by
    intro i _hi
    exact (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose_spec.2
  let D : ℕ := ∑ i ∈ s, dmem i * dmem i
  have hDsum : ∑ i ∈ s, dmem i * dmem i = D := rfl
  have hDpos : 0 < D := by
    have hpos_i₁ : 0 < dmem i₁ :=
      (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i₁)).choose_spec.1
    have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
    have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
    simpa [D] using hsum_pos
  exact ⟨dχ, d₁, D, dmem, hχone, hχ₁one, hmemone, hDsum, hd₁pos, hDpos⟩

/-- A natural witness for the degree of an irreducible character is positive. -/
theorem natDegree_pos_of_irreducibleCharacter_apply_one_eq
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {d : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) : 0 < d := by
  obtain ⟨e, hepos, heq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hde : d = e := Nat.cast_injective (hχone.symm.trans heq)
  rwa [hde]

/-- A common index in a factorization of an irreducible character degree is positive. -/
theorem commonIndex_pos_of_natDegree_factor
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {idx d θ : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (hd : d = idx * θ) :
    0 < idx := by
  have hdpos : 0 < d := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχone
  by_contra hidx
  have hidx0 : idx = 0 := Nat.eq_zero_of_not_pos hidx
  have hd0 : d = 0 := by simp [hd, hidx0]
  omega

/-- A common index coprime to `p` is coprime to any residual degree that is a power of `p`. -/
theorem coprime_commonIndex_primePower
    {idx p θ m : ℕ} (hidx_p : Nat.Coprime idx p) (hθ : θ = p ^ m) :
    Nat.Coprime idx θ := by
  rw [hθ]
  exact hidx_p.pow_right m

/-- A member-family square sum is positive once it contains one irreducible character. -/
theorem natDegreeSquareSum_pos_of_memberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter G} {i₁ : ι} {D : ℕ} {dmem : ι → ℕ}
    (hi₁ : i₁ ∈ s)
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D) :
    0 < D := by
  have hpos_i₁ : 0 < dmem i₁ :=
    natDegree_pos_of_irreducibleCharacter_apply_one_eq (hmemone i₁ hi₁)
  have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
  have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
  exact hDsum ▸ hsum_pos

/-- A common-index factorization of every member degree makes the common-index square divide the
member degree square sum. -/
theorem sq_dvd_natDegreeSquareSum_of_commonIndex
    {ι : Type*} {s : Finset ι} {idx D : ℕ}
    {dmem θmem : ι → ℕ}
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hdmem : ∀ i ∈ s, dmem i = idx * θmem i) :
    idx * idx ∣ D := by
  rw [← hDsum]
  apply Finset.dvd_sum
  intro i hi
  refine ⟨θmem i * θmem i, ?_⟩
  rw [hdmem i hi]
  ring



end OddOrder.Peterfalvi.S08

