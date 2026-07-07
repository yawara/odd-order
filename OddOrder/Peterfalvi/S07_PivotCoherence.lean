/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi §5: pivot coherence (norm-general uniform-degree coherence, part 1)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 17-25; Coq mirror: `PFsection5.v` `pivot_coherence` (:588) and
`uniform_degree_coherence` (:1234).

This file ports the **pivot** route to coherence: a pairwise-orthogonal family `S` of
equal-degree class functions is coherent as soon as one member `η₁` (the *pivot*) has a
virtual-character partner `ζ₁ ∈ ℤ[Irr G]` of the same norm with
`⟨τ(η − η₁), ζ₁⟩ = −⟨η₁, η₁⟩` for every other member `η`.  Unlike the norm-1 engine
`coherent_of_constant_degree` (which requires all members irreducible), the pivot engine is
**norm-general**: the members may be reducible characters (e.g. the certain-type column sums
`μ_j` of norm `q`), matching Coq's `uniform_degree_coherence`, whose Galois branch of (9.11)
applies it to the whole family `𝒮(H₀C′)` — reducible μ-columns included
(`PFsection9.v:1510-1513`; issue 9075).

The construction is explicit (no basis/freeness argument): with the coefficient functional
`s(φ) = ∑_{η ∈ S} ⟨φ, η⟩ / ⟨η, η⟩` (which is the *coefficient sum* on `ℤ[S]`, by pairwise
orthogonality), the extension is

  `ν φ := s(φ) • ζ₁ + τ (φ − s(φ) • η₁)`.

On `ℤ[S, A]` the coefficient sum vanishes (equal degrees, `1 ∉ A`), so `ν = τ` there; the
isometry law reduces to the pivot inner products and `τ`'s isometry on the supported lattice;
integrality follows since `s` is `ℤ`-valued on `ℤ[S]`.  The remaining (5.7) work — constructing
`ζ₁` from the subcoherent `R`-datum (Coq `subcoherent_split`/`subcoherent_norm`) — is part 2.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory
open IntegralCharacterMap

variable {L G : Type*} [Group L] [Group G]

/-! ### Sesquilinear expansion helper -/

section InnerExpand

variable {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- Sesquilinear expansion of `⟨a•w + x, b•w + y⟩` — the inner product of two
pivot decompositions against the common anchor `w`. -/
theorem inner_smul_add_smul_add (w x y : ClassFunction H ℂ) (a b : ℂ) :
    ClassFunction.inner (a • w + x) (b • w + y)
      = a * (star b * ClassFunction.inner w w) + a * star (ClassFunction.inner y w)
        + star b * ClassFunction.inner x w + ClassFunction.inner x y := by
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
  rw [inner_conj_symm y w]
  ring

end InnerExpand

/-! ### The pivot coefficient functional and extension -/

section PivotExtension

variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- **The pivot coefficient functional** `s(φ) = ∑_{η ∈ S} ⟨φ, η⟩ / ⟨η, η⟩`.  On the lattice
`ℤ[S]` of a pairwise-orthogonal family this recovers the **coefficient sum** (each member has
`s = 1`), the quantity that must vanish on the degree-zero sublattice `ℤ[S, A]`. -/
noncomputable def pivotCoefficient {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite) :
    ClassFunction L ℂ →ₗ[ℤ] ℂ :=
  ∑ η ∈ hSfin.toFinset, (ClassFunction.inner η η)⁻¹ • innerLeftℤ (L := L) η

@[simp] theorem pivotCoefficient_apply {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (φ : ClassFunction L ℂ) :
    pivotCoefficient (L := L) hSfin φ
      = ∑ η ∈ hSfin.toFinset, (ClassFunction.inner η η)⁻¹ * ClassFunction.inner φ η := by
  simp only [pivotCoefficient, LinearMap.sum_apply, LinearMap.smul_apply, innerLeftℤ_apply,
    smul_eq_mul]

/-- On a member of a pairwise-orthogonal family with nonzero norms, the pivot coefficient is
`1` (only the diagonal term survives). -/
theorem pivotCoefficient_apply_mem {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hnormS : ∀ a ∈ S, ClassFunction.inner a a ≠ 0)
    {η : ClassFunction L ℂ} (hη : η ∈ S) :
    pivotCoefficient (L := L) hSfin η = 1 := by
  classical
  rw [pivotCoefficient_apply]
  rw [Finset.sum_eq_single η]
  · rw [inv_mul_cancel₀ (hnormS η hη)]
  · intro η' hη' hne
    rw [horth η hη η' (hSfin.mem_toFinset.mp hη') (fun h => hne h.symm), mul_zero]
  · intro h
    exact absurd (hSfin.mem_toFinset.mpr hη) h

/-- **The pivot extension** `ν φ = s(φ) • ζ₁ + τ (φ − s(φ) • η₁)`: replace the pivot component
by `ζ₁` and push the (degree-zero) rest through `τ`. -/
noncomputable def pivotExtension (τ : IntegralCharacterMap L G)
    {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (η₁ : ClassFunction L ℂ) (ζ₁ : ClassFunction G ℂ) : IntegralCharacterMap L G :=
  (pivotCoefficient (L := L) hSfin).smulRight ζ₁ +
    τ ∘ₗ (LinearMap.id - (pivotCoefficient (L := L) hSfin).smulRight η₁)

@[simp] theorem pivotExtension_apply (τ : IntegralCharacterMap L G)
    {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (η₁ : ClassFunction L ℂ) (ζ₁ : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ φ
      = pivotCoefficient (L := L) hSfin φ • ζ₁
        + τ (φ - pivotCoefficient (L := L) hSfin φ • η₁) := by
  simp [pivotExtension, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply]

end PivotExtension

/-! ### The pivot coherence theorem -/

section PivotCoherence

variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Pivot coherence** (Coq `pivot_coherence`, `PFsection5.v:588`, specialized to equal
degrees): a finite pairwise-orthogonal family `S` of equal-degree class functions with nonzero
norms, whose member differences are `A`-supported and mapped to virtual characters, is coherent
as soon as a pivot `η₁ ∈ S` has a partner `ζ₁ ∈ ℤ[Irr G]` with `⟨ζ₁, ζ₁⟩ = ⟨η₁, η₁⟩` and
`⟨τ(η − η₁), ζ₁⟩ = −⟨η₁, η₁⟩` for every other member `η` (`hpivot`).

The coherent extension is `pivotExtension`: `ν φ = s(φ) • ζ₁ + τ(φ − s(φ) • η₁)` with `s` the
pivot coefficient functional.  This is the norm-general engine behind Peterfalvi (5.7)
(`uniform_degree_coherence`): unlike `coherent_of_constant_degree`, the members need not be
irreducible — only pairwise orthogonal with nonzero norms — so it accepts the reducible
certain-type columns `μ_j` of the (9.11) Galois/caseB family (issue 9075). -/
noncomputable def pivotCoherence
    {τ : IntegralCharacterMap L G} {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hSfin : S.Finite)
    {η₁ : ClassFunction L ℂ} (hη₁ : η₁ ∈ S)
    {ζ₁ : ClassFunction G ℂ} (hζZ : ζ₁ ∈ ZIrr G)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hnormS : ∀ a ∈ S, ClassFunction.inner a a ≠ 0)
    (hnorm : ClassFunction.inner ζ₁ ζ₁ = ClassFunction.inner η₁ η₁)
    (hpivot : ∀ η ∈ S, η ≠ η₁ →
      ClassFunction.inner (τ (η - η₁)) ζ₁ = -ClassFunction.inner η₁ η₁)
    (hiso : ∀ φ ψ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ)
    (hZdiff : ∀ a ∈ S, ∀ b ∈ S, τ (a - b) ∈ ZIrr G)
    (hdeg : ∀ a ∈ S,
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((η₁ : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((η₁ : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {η₂ : ClassFunction L ℂ} (hη₂ : η₂ ∈ S) (hη₂ne : η₂ ≠ η₁) :
    IsCoherent τ S A := by
  classical
  -- coefficient value on members
  have hsval : ∀ η ∈ S, pivotCoefficient (L := L) hSfin η = 1 := fun η hη =>
    pivotCoefficient_apply_mem hSfin horth hnormS hη
  -- δ-rearrangements (the defect `δφ = φ − s(φ)•η₁` is additive and `ℤ`-homogeneous)
  have hδadd : ∀ x y : ClassFunction L ℂ,
      x + y - pivotCoefficient (L := L) hSfin (x + y) • η₁
        = (x - pivotCoefficient (L := L) hSfin x • η₁)
          + (y - pivotCoefficient (L := L) hSfin y • η₁) := by
    intro x y
    rw [map_add, add_smul]
    abel
  have hδsmul : ∀ (c : ℤ) (x : ClassFunction L ℂ),
      c • x - pivotCoefficient (L := L) hSfin (c • x) • η₁
        = c • (x - pivotCoefficient (L := L) hSfin x • η₁) := by
    intro c x
    rw [map_smul, smul_sub]
    congr 1
    rw [zsmul_eq_mul, mul_smul, ← Int.cast_smul_eq_zsmul ℂ c
      (pivotCoefficient (L := L) hSfin x • η₁)]
  -- the defect lands in the supported lattice
  have hδmem : ∀ φ ∈ zSpan (L := L) S,
      φ - pivotCoefficient (L := L) hSfin φ • η₁ ∈ zSupportedSpan (L := L) S A := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        exact ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁),
          hsuppdiff η hη η₁ hη₁⟩
    | zero =>
        rw [map_zero, zero_smul, sub_zero]
        exact ⟨Submodule.zero_mem _, by rw [ClassFunction.support_zero]; exact Set.empty_subset A⟩
    | add x y hx hy ihx ihy =>
        rw [hδadd x y]
        exact ⟨Submodule.add_mem _ ihx.1 ihy.1,
          (ClassFunction.support_add_subset _ _).trans (Set.union_subset ihx.2 ihy.2)⟩
    | smul c x hx ih =>
        rw [hδsmul c x]
        refine ⟨Submodule.smul_mem _ c ih.1, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c]
        exact (ClassFunction.support_smul_subset _ _).trans ih.2
  -- the pivot inner product extends `ℤ`-linearly over the defect lattice
  have hτζ : ∀ φ ∈ zSpan (L := L) S,
      ClassFunction.inner (τ (φ - pivotCoefficient (L := L) hSfin φ • η₁)) ζ₁
        = ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁) η₁ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        by_cases hne : η = η₁
        · subst hne
          rw [sub_self, map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
        · rw [hpivot η hη hne, ClassFunction.inner_sub_left, horth η hη η₁ hη₁ hne, zero_sub]
    | zero =>
        rw [map_zero, zero_smul, sub_zero, map_zero, ClassFunction.inner_zero_left,
          ClassFunction.inner_zero_left]
    | add x y hx hy ihx ihy =>
        rw [hδadd x y, map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
          ihx, ihy]
    | smul c x hx ih =>
        rw [hδsmul c x, map_smul, ← Int.cast_smul_eq_zsmul ℂ c
          (τ (x - pivotCoefficient (L := L) hSfin x • η₁)),
          ← Int.cast_smul_eq_zsmul ℂ c (x - pivotCoefficient (L := L) hSfin x • η₁),
          ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih]
  -- the defect image is a virtual character
  have hZδ : ∀ φ ∈ zSpan (L := L) S,
      τ (φ - pivotCoefficient (L := L) hSfin φ • η₁) ∈ ZIrr G := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        exact hZdiff η hη η₁ hη₁
    | zero =>
        rw [map_zero, zero_smul, sub_zero, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
        rw [hδadd x y, map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
        rw [hδsmul c x, map_smul]
        exact Submodule.smul_mem _ c ih
  -- the coefficient is integral on the lattice
  have hsmem : ∀ φ ∈ zSpan (L := L) S,
      ∃ m : ℤ, pivotCoefficient (L := L) hSfin φ = (m : ℂ) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη => exact ⟨1, by rw [hsval η hη, Int.cast_one]⟩
    | zero => exact ⟨0, by rw [map_zero, Int.cast_zero]⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨m, hm⟩ := ihx
        obtain ⟨n, hn⟩ := ihy
        exact ⟨m + n, by rw [map_add, hm, hn, Int.cast_add]⟩
    | smul c x hx ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨c * m, by rw [map_smul, zsmul_eq_mul, hm, Int.cast_mul]⟩
  -- degrees: `φ(1) = s(φ)·η₁(1)` on the lattice
  have hone : ∀ φ ∈ zSpan (L := L) S,
      ((φ : ClassFunction L ℂ) : L → ℂ) 1
        = pivotCoefficient (L := L) hSfin φ * ((η₁ : ClassFunction L ℂ) : L → ℂ) 1 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη => rw [hsval η hη, one_mul]; exact hdeg η hη
    | zero => rw [map_zero, zero_mul]; rfl
    | add x y hx hy ihx ihy =>
        rw [map_add, add_mul, ← ihx, ← ihy]
        rfl
    | smul c x hx ih =>
        have hs : pivotCoefficient (L := L) hSfin (c • x)
            = (c : ℂ) * pivotCoefficient (L := L) hSfin x := by
          rw [map_smul, zsmul_eq_mul]
        rw [hs, ← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, ih, mul_assoc]
  -- assemble the coherence witness
  refine ⟨⟨η₂ - η₁,
      ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂) (Submodule.subset_span hη₁),
        hsuppdiff η₂ hη₂ η₁ hη₁⟩,
      sub_ne_zero.mpr hη₂ne⟩,
    pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁, ?_, ?_, ?_⟩
  · -- isometry on `ℤ[S]`
    intro φ ψ hφ hψ
    have hφζ := hτζ φ hφ
    have hψζ := hτζ ψ hψ
    have hδδ := hiso _ _ (hδmem φ hφ) (hδmem ψ hψ)
    have hL : ClassFunction.inner
        (pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ φ)
        (pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ ψ)
        = pivotCoefficient (L := L) hSfin φ * (star (pivotCoefficient (L := L) hSfin ψ)
            * ClassFunction.inner η₁ η₁)
          + pivotCoefficient (L := L) hSfin φ
            * star (ClassFunction.inner (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) η₁)
          + star (pivotCoefficient (L := L) hSfin ψ)
            * ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁) η₁
          + ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁)
              (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) := by
      rw [pivotExtension_apply, pivotExtension_apply, inner_smul_add_smul_add, hnorm,
        hφζ, hψζ, hδδ]
    have hR := inner_smul_add_smul_add (H := L) η₁
      (φ - pivotCoefficient (L := L) hSfin φ • η₁)
      (ψ - pivotCoefficient (L := L) hSfin ψ • η₁)
      (pivotCoefficient (L := L) hSfin φ) (pivotCoefficient (L := L) hSfin ψ)
    rw [show pivotCoefficient (L := L) hSfin φ • η₁
          + (φ - pivotCoefficient (L := L) hSfin φ • η₁) = φ by abel,
      show pivotCoefficient (L := L) hSfin ψ • η₁
          + (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) = ψ by abel] at hR
    exact hL.trans hR.symm
  · -- agreement with `τ` on the supported lattice
    intro φ hφ
    obtain ⟨hφspan, hφsupp⟩ := hφ
    have hφ1 : ((φ : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
      by_contra h
      exact h1A (hφsupp h)
    have hs0 : pivotCoefficient (L := L) hSfin φ = 0 := by
      have := hone φ hφspan
      rw [hφ1] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hdeg0
    rw [pivotExtension_apply, hs0, zero_smul, zero_smul, sub_zero, zero_add]
  · -- integrality on the lattice
    intro φ hφ
    rw [pivotExtension_apply]
    refine Submodule.add_mem _ ?_ (hZδ φ hφ)
    obtain ⟨m, hm⟩ := hsmem φ hφ
    rw [hm, Int.cast_smul_eq_zsmul ℂ m ζ₁]
    exact Submodule.smul_mem _ m hζZ

end PivotCoherence

end OddOrder.Peterfalvi.S07
