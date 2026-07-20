/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_BridgeCoherent
import OddOrder.Peterfalvi.S08_CoherenceCorePart1.CoherentAdjoin

/-!
# Peterfalvi (5.6) / Isaacs 7.14: the general mixed-degree coherence adjoin

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §5, (5.6); the
underlying theorem is Isaacs, *Character Theory of Finite Groups*, Theorem 7.14 (mathcomp
`extend_coherent`, Coq `theories/PFsection5.v:1124`).

## Why this exists

The FT main text (via §6.6 / the (9.11) capstone) consumes the mixed-degree adjoining engine
only against the **Feit–Thompson Dade map** `τ = dadeIntegralCharacterMap …`, so the repository's
adjoin step `xAdjoinStep` (`S08_CoherenceCorePart1/CoherentAdjoin.lean`) is stated for that `τ`.
Every *hard* ingredient it invokes is in fact **general** — the (5.6.2) collapse
`Y_eq_nsmul_tau1_of_lambdaForm` / `lambda_eq_zero_and_Z_eq_zero`, the crux chain
`crux1_of_memberFamily` / `inner_Y_extension_member_eq` / `crux1_of_collapse`
/ `inner_decomposition_X_extension_member_eq_zero`, and the assembly engine
`retarget_isCoherent_of_decompositions` all treat `τ` as an opaque `IntegralCharacterMap` and never
use its Dade-ness (the `hyp`/`hconj`/`_hτ` arguments are threaded for uniformity but unused in the
proofs).  Only four helpers genuinely consume Dade structure, and each is generalized here from the
abstract `S07.Hypothesis` data:

1. `inner_dade_extension_of_supported` — the cross-term `⟨τ u, ν δ⟩ = ⟨u, δ⟩`; general version
   `inner_tau_extension_of_supported` below, from the lattice isometry of `τ` plus
   `IsCoherent.extends_on_supported`.
2. the per-member `ψ = 0` decomposition (`memberExtensionDecomposition`) — general from
   `Hypothesis.difference_image`.
3. the `R(χᵢ) ⊥ R(χ)` family orthogonality — general from `Hypothesis.difference_images_orthogonal`.
4. the final bridge (`retarget_isCoherent_of_extensionImage`) — general `τ` form.

This file builds the general degree-bound adjoin that
`Appendices/FeitSibley.coherent_adjoin_of_degree_bound` (Peterfalvi Appendix IV, Lemma 1(a)) needs.
See issue 1049.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/-! ### The general cross-term (helper 1) -/

/-- **General cross-term `⟨τ u, ν δ⟩ = ⟨u, δ⟩`** (generalizes `inner_dade_extension_of_supported`,
`S08_YsetInner`).

For an isometry `τ` on the `A`-supported lattice of `S`, a coherent `(S₁, τ)` with `S₁ ⊆ S`, an
`A`-supported `u ∈ ℤ[S, A]` and a supported member combination `δ ∈ ℤ[S₁, A]`, the running
extension `ν = hS₁.extension` satisfies `⟨τ u, ν δ⟩ = ⟨u, δ⟩`.  The only inputs are the lattice
isometry `hisom` (in the application `Hypothesis.tau_isometry_diff`) and `extends_on_supported`
(`ν δ = τ δ` for supported `δ`); nothing Dade-specific is used. -/
theorem inner_tau_extension_of_supported
    {τ : IntegralCharacterMap L G} {S S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hisom : ∀ φ ζ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A →
      ζ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hS₁S : S₁ ⊆ S)
    (hS₁ : IsCoherent τ S₁ A)
    {u δ : ClassFunction L ℂ}
    (hu : u ∈ zSupportedSpan (L := L) S A)
    (hδ : δ ∈ zSupportedSpan (L := L) S₁ A) :
    ClassFunction.inner (τ u) (hS₁.extension δ) = ClassFunction.inner u δ := by
  rw [hS₁.extends_on_supported δ hδ]
  exact hisom u δ hu (zSupportedSpan_mono_left hS₁S hδ)

/-! ### The general extension-image bridge (helper 4) -/

open scoped Classical in
/-- **General `retarget_isCoherent_of_extensionImage`** (generalizes the Dade-specialized
`retarget_isCoherent_of_extensionImage`, `S08_CoherenceCorePart1/CoherentAdjoin.lean`).

Adjoins a new non-real pair `{χ, χ̄}` (`χ` orthogonal to all of `S₁`, `‖χ‖² = 1`) to a coherent
`(S₁, τ)`, mapping `χ` to the **corrected extension image** `X = τ(χ − a·χ₁) + a·ν χ₁` (both terms
integral), so the (5.6.2) image equation is definitional and the `τχ₁ = νχ₁` requirement (false for
an unsupported anchor) is bypassed.  Every obligation of `retarget_isCoherent` is discharged from
the source/`τ`/`ν` isometries plus the two crux inner products `hcrux1`, `hcrux2`.

The **only** input over the source data is `hisom`: the lattice isometry of `τ` on `A`-supported
sets, in the exact shape the Dade version drew from the supported-span inner-preservation lemma
`dadeIntegralCharacterMap_inner_eq_on_supported_span`.
In the abstract application (Feit–Sibley, Isaacs 7.14) it is supplied from
`Hypothesis.tau_isometry_diff`; in the Feit–Thompson application it is the Dade isometry.  This is
the honest replacement for the four Dade-specific helpers of `xAdjoinStep` (issue 1049). -/
noncomputable def retarget_isCoherent_of_extensionImage_general
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chi1 : ClassFunction L ℂ} {a : ℕ}
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s.support ⊆ A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hdiffsupp : (χ.conj - χ).support ⊆ A)
    (hdiffasupp : (χ - a • chi1).support ⊆ A)
    (hχχ : ClassFunction.inner χ χ = 1)
    (hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    {m₁ : ℝ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = (m₁ : ℂ))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ (χ - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ (χ - χ.conj) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension chi1) = -((a : ℂ) * (m₁ : ℂ)))
    (hcrux2 : ClassFunction.inner (τ (χ - χ.conj)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {chi1}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - χ.conj, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, χ.conj}) A := by
  classical
  -- `χ₁ ⊥ χ, χ̄` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner χ chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner χ.conj chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 χ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference set `{χ−χ̄, χ−a·χ₁}` and the isometry of `τ` on it.
  have hSdiff : ∀ s ∈ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)), s.support ⊆ A := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]; exact hdiffsupp
    · exact hdiffasupp
  have hmemu : χ - a • chi1 ∈
      Submodule.span ℤ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : χ - χ.conj ∈
      Submodule.span ℤ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)) →
      ψ ∈ Submodule.span ℤ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ :=
    fun φ ψ hφ hψ => hisom _ hSdiff φ ψ hφ hψ
  -- τ-image inner products (τ isometry + source orthonormality).
  have huu : ClassFunction.inner (τ (χ - a • chi1)) (τ (χ - a • chi1))
      = 1 + (a : ℂ) ^ 2 * (m₁ : ℂ) := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ (χ - a • chi1)) (τ (χ - χ.conj)) = 1 := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, hχχ, hχχbar, hchi1χ, hchi1χbar]
    ring
  have hdd : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2 := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hχχ, hχχbar, hχbarχ, hχbarχbar]
    ring
  have hdu : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - a • chi1)) = 1 := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `ν χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = (m₁ : ℂ) := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1) (τ (χ - a • chi1))
      = -((a : ℂ) * (m₁ : ℂ)) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1) (τ (χ - χ.conj)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ := τ (χ - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ (χ - χ.conj) with hXbar
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  have hXX : ClassFunction.inner X X = 1 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  have hXbarXbar : ClassFunction.inner Xbar Xbar = 1 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hcrux1, hvu, hvd, hvv, star_natCast]
    ring
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ν ξ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ (χ - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner χ y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y χ = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, χ - a • chi1} : Set (ClassFunction L ℂ)), s.support ⊆ A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · exact hdiffasupp
          rw [hνy, hisom _ hySdiff y (χ - a • chi1) (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp)), ← Nat.cast_smul_eq_nsmul ℂ a chi1]
          simp only [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
            hyχ, star_natCast]
          ring
        · rw [Set.mem_singleton_iff.mp hy1, hvu, hchi1chi1]; ring
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
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ (χ - χ.conj)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner χ y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner χ.conj y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y χ = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y χ.conj = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, χ - χ.conj} : Set (ClassFunction L ℂ)), s.support ⊆ A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
              exact hdiffsupp
          rw [hνy, hisom _ hySdiff y (χ - χ.conj) (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih, mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ (χ - a • chi1) = X - a • hS₁.extension chi1 := by rw [hX]; abel
  exact retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

end OddOrder.Peterfalvi.S07
