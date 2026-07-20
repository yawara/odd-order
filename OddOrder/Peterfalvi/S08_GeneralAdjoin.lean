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

/-! ### `zSupportedSpan` closure under `ℤ`-span (for supplying `hisom` from `tau_isometry_diff`) -/

/-- **`ℤ[T] ⊆ ℤ[S, A]` when `T ⊆ ℤ[S, A]`.**  The `A`-supported lattice `zSupportedSpan S A`
(`= ℤ[S] ∩ CF(L, A)`) is closed under `ℤ`-combinations, so the span of a subset it contains stays
inside it.  This is what lets the general adjoin's `hisom` (needed on the difference lattices
`ℤ[{χ − χ̄, χ − a·χ₁}]` etc.) be supplied at the Feit–Sibley call site from
`Hypothesis.tau_isometry_diff` (which preserves `⟨·,·⟩` on all of `ℤ[𝒮, A]`): every difference the
engine feeds has its two endpoints in `𝒮`, hence in `ℤ[𝒮, A]`. -/
theorem zSpan_subset_zSupportedSpan {S : Set (ClassFunction L ℂ)} {A : Set L}
    {T : Set (ClassFunction L ℂ)} (hT : ∀ s ∈ T, s ∈ zSupportedSpan (L := L) S A) :
    (Submodule.span ℤ T : Set (ClassFunction L ℂ)) ⊆ zSupportedSpan (L := L) S A := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem s hs => exact hT s hs
  | zero => exact zero_mem_zSupportedSpan
  | add x y _ _ ihx ihy => exact add_mem_zSupportedSpan ihx ihy
  | smul c x _ ih =>
      refine ⟨Submodule.smul_mem _ c ih.1, ?_⟩
      intro t ht
      apply ih.2
      rw [ClassFunction.mem_support] at ht ⊢
      intro hx0
      apply ht
      rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hx0, mul_zero]

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
    {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    {χ chi1 : ClassFunction L ℂ} {a : ℕ}
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • chi1 ∈ zSupportedSpan (L := L) Samb A)
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
  have hSdiff : ∀ s ∈ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)),
      s ∈ zSupportedSpan (L := L) Samb A := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hdiffmem
    · exact hadiffmem
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
          have hySdiff : ∀ s ∈ ({y, χ - a • chi1} : Set (ClassFunction L ℂ)),
              s ∈ zSupportedSpan (L := L) Samb A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact zSupportedSpan_mono_left hS₁Samb hsupp
            · exact hadiffmem
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
          have hySdiff : ∀ s ∈ ({y, χ - χ.conj} : Set (ClassFunction L ℂ)),
              s ∈ zSupportedSpan (L := L) Samb A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact zSupportedSpan_mono_left hS₁Samb hsupp
            · exact hdiffmem
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

/-! ### The degree-bound crux (general `crux1_of_memberFamily`) -/

open scoped Classical in
/-- **General `crux1_of_memberFamily`** (generalizes `crux1_of_memberFamily`,
`S08_CoherenceCorePart1/CoherentAdjoin.lean`; the Dade version's `hyp`/`hconj`/`_hτ` arguments are
unused in its proof — this drops them and the `L : Subgroup G` restriction).

**Peterfalvi (5.6.1)/(5.6.2) crux1: `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`** for a unit-norm member family
`{χᵢ}` (all in `S₁`, `‖χᵢ‖² = 1`), the per-member (5.6.1) coefficient values `hcoeffval`, `a₁ = 1`,
and the degree inequality `2a < ∑ aᵢ²` (`hDeg`).  The indexed integral projection writes
`Da.Y = ∑ᵢ cᵢ·νχᵢ + Z` with `cᵢ = ⟨Da.Y, νχᵢ⟩`; `hcoeffval` identifies `cᵢ = a·[i=i₁] − λ·aᵢ` with
integer `λ = a + μ`, `μ = ⟨τ(χ−a·χ₁), νχ₁⟩`; the (5.6.2) integer-forcing
`lambda_eq_zero_and_Z_eq_zero` forces `λ = 0`, i.e. `μ = −a`. -/
theorem crux1_of_memberFamily_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A)
    (χ : ClassFunction L ℂ) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ (χ - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2) :
    ClassFunction.inner (τ (χ - a • χmem i₁)) (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  have hvcinj : ∀ i ∈ s, ∀ j ∈ s, hS₁.extension (χmem i) = hS₁.extension (χmem j) → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h0 := horth i hi j hj
    rw [if_neg hne, hij, horth j hj j hj, if_pos rfl] at h0
    exact one_ne_zero h0
  obtain ⟨c, Z, hc_coeff, hYsum, hZortho⟩ :=
    OddOrder.Peterfalvi.S08.exists_indexed_intProjection_of_orthonormal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) hνZ hvcinj horth
  have hcoeff_eq : ∀ i ∈ s, (c i : ℂ) =
      (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ) := by
    intro i hi
    rw [← hc_coeff i hi, hcoeffval i hi, hμeq]
    by_cases h : i = i₁
    · simp only [if_pos h]; push_cast; ring
    · simp only [if_neg h]; push_cast; ring
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ)
        • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hcoeff_eq i hi]
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast, mul_one,
      show (a : ℂ) * (a : ℂ) = (((a : ℝ) ^ 2 * 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) ((a : ℤ) + μ) Z
    (fun i => hS₁.extension (χmem i)) (fun _ => 1) (fun i => (deg i : ℝ))
    hY horth hZortho hψ (by simp [ha1]) (by positivity)
    (by simp only [mul_one]; exact hDeg)
  have hμval : μ = -(a : ℤ) := by omega
  rw [hμeq, hμval]; push_cast; ring

/-- **General `inner_Y_extension_member_eq`** (generalizes `inner_Y_extension_member_eq`,
`S08_CoherenceCorePart1/CoherentAdjoin.lean`; the Dade map appears only as an opaque
`IntegralCharacterMap` in the proof, so `hyp`/`hconj` are dropped and it is stated for a general
`τ`).

The per-member (5.6.1) coefficient `⟨Y, ν χⱼ⟩` for the χ-decomposition residual `Y = Xχ − τ(χ −
a·χ₁)` with `Xχ ⊥ ν χⱼ` (the (5.2.e) `R(χ)`-orthogonality) and the cross-term
`⟨τ(χ − a·χ₁), ν(χⱼ − aⱼ·χ₁)⟩ = ⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩` (`hfound`; supplied by
`inner_tau_extension_of_supported`).  Expands via `ν`-linearity and the source expansion to the
`crux1_of_memberFamily_general` `hcoeffval` shape. -/
theorem inner_Y_extension_member_eq_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A)
    (χ : ClassFunction L ℂ) {chi1 cj : ClassFunction L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - τ (χ - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner (χ - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner χ cj = 0)
    (hχchi1 : ClassFunction.inner χ chi1 = 0)
    {m₁ : ℂ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = m₁) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) * m₁ + ClassFunction.inner (τ (χ - a • chi1))
          (hS₁.extension chi1)) * (aj : ℂ) := by
  have hνcj : hS₁.extension cj = hS₁.extension (cj - aj • chi1) + aj • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul]; abel
  have hsrc : ClassFunction.inner (χ - a • chi1) (cj - aj • chi1)
      = -(a : ℂ) * ClassFunction.inner chi1 cj + (a : ℂ) * (aj : ℂ) * m₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ aj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  have hsmul : ClassFunction.inner (τ (χ - a • chi1)) (aj • hS₁.extension chi1) =
      (aj : ℂ) * ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension chi1) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ aj (hS₁.extension chi1),
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub, hνcj,
    ClassFunction.inner_add_right, hfound, hsrc, hsmul]
  ring

/-! ### The member and χ decompositions (helpers 2/general) -/

/-- **General member `ψ = 0` decomposition** (generalizes `memberExtensionDecomposition`,
`S08_YsetInner`).  For a member `χ ∈ S₁` (with `χ̄ ∈ S₁`) and its `R(χ)` family, the (5.5)
decomposition of `χ` uses the **running extension `ν = hS₁.extension` as the auxiliary isometry**
(not `τ`): `ν χ ∈ ℤ[Irr G]` (`hνZ`, since `χ ∈ S₁`) whereas `τ χ` need not be integral, and `ν`
agrees with `τ` on the supported difference `χ − χ̄`.  The `R(χ)` family is w.r.t. `τ`
(supplied from `Hypothesis.difference_image`). -/
noncomputable def memberExtensionDecomposition_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) {χ : ClassFunction L ℂ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (hdiffsupp : (χ.conj - χ).support ⊆ A)
    (hχ_S1 : χ ∈ S₁) (hχbar_S1 : χ.conj ∈ S₁)
    (hνZ : hS₁.extension χ ∈ ZIrr G)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ 0 := by
  classical
  have hχmem : χ ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχ_S1
  have hχbarmem : χ.conj ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχbar_S1
  have hle : Submodule.span ℤ ({χ - χ.conj, χ - 0} : Set (ClassFunction L ℂ)) ≤
      Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  have hdiffsupported : χ - χ.conj ∈ zSupportedSpan (L := L) S₁ A :=
    mem_zSupportedSpan_iff.mpr ⟨Submodule.sub_mem _ hχmem hχbarmem, by
      rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
      exact hdiffsupp⟩
  exact CharacterPsiDecomposition.ofProjection imageFamily hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp) (by simp) hχχbar

/-- **General χ decomposition for `χ − a·χ₁`** (generalizes `decompositionDaFromDadeOfDiff`,
`S07_Coherence/FamilyBundleDade`).  Uses `ofProjection` with the auxiliary isometry `τ` itself,
whose inner-preservation is needed only on the supported **difference** lattice `{χ − χ̄, χ − a·χ₁}`
(`hisom`), and the `ZIrr`-membership only on `χ − a·χ₁` (`hτaχ1Z`).  Works for an unsupported `χ`
(e.g. `χ = Ind θ`). -/
noncomputable def decompositionDaFromDiff_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {χ chi1 : ClassFunction L ℂ} {a : ℕ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • chi1 ∈ zSupportedSpan (L := L) Samb A)
    (hτaχ1Z : τ (χ - a • chi1) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner χ (a • chi1 : ClassFunction L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner χ.conj (a • chi1 : ClassFunction L ℂ) = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1) := by
  classical
  have hSdiff : ∀ s ∈ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)),
      s ∈ zSupportedSpan (L := L) Samb A := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hdiffmem
    · exact hadiffmem
  exact CharacterPsiDecomposition.ofProjection imageFamily τ
    (fun φ ζ hφ hζ => hisom _ hSdiff φ ζ hφ hζ)
    rfl hτaχ1Z hχaχ1 hχbaraχ1 hχχbar

/-! ### The general degree-bound adjoining step (`adjoinPairCoherent`) -/

open scoped Classical in
/-- **General degree-bound coherence adjoin** (generalizes `xAdjoinStep`,
`S08_CoherenceCorePart1/CoherentAdjoin.lean`, from the Feit–Thompson Dade map to any isometry `τ`).

This is **Peterfalvi (5.6) / Isaacs, *Character Theory*, Theorem 7.14** — the mixed-degree coherence
adjoin.  Adjoins a new non-real irreducible pair `{χ, χ̄}` (`‖χ‖² = 1`, `χ ⊥ S₁`) to a coherent
`(S₁, τ)`, given a finite orthonormal unit-norm member family `{χmem i}ᵢ∈ₛ ⊆ S₁` with degree ratios
`deg i` (`deg i₁ = 1`), the signed-difference families `R(χ)`, `R(χmem i)`
(`CharacterDifferenceImage`s w.r.t. `τ`, from `Hypothesis.difference_image` in the application) with
their `(5.2.e)` cross-orthogonalities `R(χmem i) ⊥ R(χ)`, and the **degree inequality**
`2a < ∑ᵢ (deg i)²` (`a = χ(1)/χ₁(1)`).  Concludes `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`.

The lattice isometry `hisom` (in the Dade version drawn from
`dadeIntegralCharacterMap_inner_eq_on_supported_span`, here supplied from
`Hypothesis.tau_isometry_diff`) is the sole "isometry" input.  Everything else reduces to the
general leaf lemmas above and in §5/§6.  See issue 1049. -/
noncomputable def adjoinPairCoherent_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    {χ : ClassFunction L ℂ}
    (Rχ : CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hχSamb : χ ∈ Samb) (hχbarSamb : χ.conj ∈ Samb)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ A)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Rmem : ∀ i, i ∈ s → CharacterDifferenceImage (L := L) (G := G) τ (χmem i))
    (hmemdiffsupp : ∀ i ∈ s, ((χmem i).conj - χmem i).support ⊆ A)
    (hmemdegdiffsupp : ∀ i ∈ s, (χmem i - deg i • χmem i₁).support ⊆ A)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁) (hmembarS1 : ∀ i ∈ s, (χmem i).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i) (χmem i).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hmemOrtho : ∀ i (hi : i ∈ s), (Rmem i hi).Orthogonal Rχ)
    {a : ℕ}
    (hdiffasuppχ : (χ - a • χmem i₁).support ⊆ A)
    (htau1_memaχ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2)
    (hSgen : Submodule.span ℤ S₁ ≤
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χmem i₁}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - χ.conj, χ - a • χmem i₁})) :
    IsCoherent τ (S₁ ∪ {χ, χ.conj}) A := by
  classical
  have hmemνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 i hi))
  have hχaχ1 : ClassFunction.inner χ (a • χmem i₁ : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner χ.conj (a • χmem i₁ : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The two adjoined differences land in `ℤ[Samb, A]` (from the containments + supports).
  have hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A :=
    mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχSamb) (Submodule.subset_span hχbarSamb), by
        rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
        exact hdiffsuppχ⟩
  have hadiffmem : χ - a • χmem i₁ ∈ zSupportedSpan (L := L) Samb A :=
    mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχSamb) (by
        rw [← Nat.cast_smul_eq_nsmul ℤ a (χmem i₁)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hS₁Samb (hmemS1 i₁ hi₁)))),
        hdiffasuppχ⟩
  -- The χ-decomposition `Da` for `χ − a·χ₁` (`let`, so `Da.imageFamily`/`Da.tau1` reduce).
  let Da := decompositionDaFromDiff_general (τ := τ) (Samb := Samb) Rχ.toOrthonormalImage hisom
    hdiffmem hadiffmem htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - τ (χ - a • χmem i₁) := by
    have h : τ (χ - a • χmem i₁) = Da.X - Da.Y := Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁) (χmem i₁) = 1 := by
    rw [hmemortho i₁ hi₁ i₁ hi₁]; simp
  -- Per-member `ψ = 0` decomposition `Dmem` (`let`, so `.imageFamily`/`.tau1` reduce).
  let Dmem : ∀ i, i ∈ s → CharacterPsiDecomposition (L := L) (G := G) τ (χmem i) 0 := fun i hi =>
    memberExtensionDecomposition_general hS₁ (Rmem i hi).toOrthonormalImage (hmemdiffsupp i hi)
      (hmemS1 i hi) (hmembarS1 i hi) (hmemνZ i hi) (hmemconjortho i hi)
  have hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily :=
    fun i hi => (Rmem i hi).toOrthonormalImage_orthogonal Rχ (hmemOrtho i hi)
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i)) = 0 :=
    fun i hi => OddOrder.Peterfalvi.S08.inner_decomposition_X_extension_member_eq_zero hS₁ Da
      (Dmem i hi) (hortho_mem i hi) rfl
  -- The (5.6.1) cross-term `hfound` (inline: `ext δ = τ δ` for supported `δ`, then `hisom`).
  have hfound : ∀ i ∈ s, ClassFunction.inner (τ (χ - a • χmem i₁))
      (hS₁.extension (χmem i - deg i • χmem i₁)) =
      ClassFunction.inner (χ - a • χmem i₁) (χmem i - deg i • χmem i₁) := fun i hi => by
    have hδℤ : χmem i - deg i • χmem i₁ ∈ Submodule.span ℤ S₁ := by
      refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
      rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
    have hδmem : χmem i - deg i • χmem i₁ ∈ zSupportedSpan (L := L) S₁ A :=
      mem_zSupportedSpan_iff.mpr ⟨hδℤ, hmemdegdiffsupp i hi⟩
    rw [hS₁.extends_on_supported _ hδmem]
    refine hisom {χ - a • χmem i₁, χmem i - deg i • χmem i₁} ?_ _ _
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hadiffmem
    · exact zSupportedSpan_mono_left hS₁Samb hδmem
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ (χ - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq_general hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]; ring
  have hcrux1 : ClassFunction.inner (τ (χ - a • χmem i₁)) (hS₁.extension (χmem i₁)) = -(a : ℂ) :=
    crux1_of_memberFamily_general hS₁ χ s χmem deg i₁ hi₁ Da hDaY_ZIrr hmemS1 hmemortho hcoeffval
      htau1_memaχ ha1 hDeg
  have hcrux2 : ClassFunction.inner (τ (χ - χ.conj)) (hS₁.extension (χmem i₁)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily (Dmem i₁ hi₁)
          (hortho_mem i₁ hi₁) rfl hα), star_zero]
  have hτdiffZ : τ (χ - χ.conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  exact retarget_isCoherent_of_extensionImage_general hS₁ hS₁Samb hisom hdiffmem hadiffmem
    hχχ hχbarχbar hχχbar hχbarχ (m₁ := 1) (by rw [hchi1chi1]; norm_num) hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ (by rw [hcrux1]; norm_num) hcrux2 hSgen hgen

end OddOrder.Peterfalvi.S07
