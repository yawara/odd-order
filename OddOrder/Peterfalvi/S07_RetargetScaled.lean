/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi (5.6.3): re-targeting for a **non-orthonormal** (reducible) break character

The `retarget` machinery of `S07_Coherence` (`orthoResidualMap`/`retarget`/`retarget_inner_eq_on`)
builds the (5.6.3) coherence extension for an **orthonormal** break pair `{χ, χ̄}` (`‖χ‖² = 1`): the
Gram–Schmidt projection uses `⟨φ, χ⟩` directly, which is correct only when `‖χ‖² = 1`.

For a **reducible** break character (the certain-type column `μ_j`, `‖μ_j‖² = w₁ > 1`) the projection
coefficient is `⟨φ, χ⟩ / ‖χ‖²`.  Over the integral lattice this is still well-defined: on
`ℤ[S₁ ∪ {χ, χ̄}]` (with `χ ⊥ S₁`, `χ ⊥ χ̄`) any `φ` has `⟨φ, χ⟩ = m·‖χ‖²` for the integer
coordinate `m`, so `⟨φ, χ⟩ / ‖χ‖² = m ∈ ℤ`.  The functional `innerLeftℤ χ` is `ℂ`-valued, so the
**scaled** maps `orthoResidualMapS`/`retargetS` (carrying the `(⟨χ,χ⟩)⁻¹` factor) remain genuine
`ℤ`-linear maps — the projection's integrality is recovered on the lattice without ever dividing a
`ℤ`-valued quantity.

This file provides the scaled analogues:
* `inner_block_expand_gen` — the block inner-product expansion for **variable** norms `‖e‖² = ee`;
* `orthoResidualMapS` / `retargetS` — the scaled Gram–Schmidt residual and re-targeting;
* `retargetS_inner_eq_on` — the lattice-relative isometry, whose Gram-matching hypotheses are
  `⟨X,X⟩ = ⟨χ,χ⟩` (not `= 1`).

These feed the reducible-break (5.6) coherence bound needed by the case-(c2) (6.2)/(6.3) chain
(`S08_Theorem65c2`).  Reference note: `notes/peterfalvi/s08_6_8_resume_roadmap.md` (cont.¹⁸).
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory
open IntegralCharacterMap

variable {L G : Type*} [Group L] [Group G]
variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- **Block expansion of a sesquilinear inner product, variable norms.**
The `‖e‖² = ee`, `‖f‖² = ff` generalization of `inner_block_expand`: for `u, u'` each orthogonal to
`e` and `f`, and `⟨e,f⟩ = ⟨f,e⟩ = 0`,
`⟨u + s·e + t·f, u' + s'·e + t'·f⟩ = ⟨u,u'⟩ + s·s̄'·ee + t·t̄'·ff`. -/
theorem inner_block_expand_gen {W : Type*} [Group W] [Fintype W] [Invertible (Nat.card W : ℂ)]
    {e f u u' : ClassFunction W ℂ} {s t s' t' ee ff : ℂ}
    (hee : ClassFunction.inner e e = ee) (hff : ClassFunction.inner f f = ff)
    (hef : ClassFunction.inner e f = 0) (hfe : ClassFunction.inner f e = 0)
    (hue : ClassFunction.inner u e = 0) (huf : ClassFunction.inner u f = 0)
    (hu'e : ClassFunction.inner u' e = 0) (hu'f : ClassFunction.inner u' f = 0) :
    ClassFunction.inner (u + s • e + t • f) (u' + s' • e + t' • f) =
      ClassFunction.inner u u' + s * star s' * ee + t * star t' * ff := by
  have heu' : ClassFunction.inner e u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'e, star_zero]
  have hfu' : ClassFunction.inner f u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'f, star_zero]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hue, huf, heu', hfu', hee, hff, hef, hfe]
  ring

/-- The **scaled** Gram–Schmidt residual map `φ ↦ φ − (⟨φ,χ⟩/‖χ‖²)·χ − (⟨φ,χ̄⟩/‖χ̄‖²)·χ̄`.
Generalizes `orthoResidualMap` (recovered when `‖χ‖² = ‖χ̄‖² = 1`); remains `ℤ`-linear because the
`(⟨χ,χ⟩)⁻¹` factor lands in the `ℂ`-valued target of the `ℤ`-linear functional `innerLeftℤ χ`. -/
noncomputable def orthoResidualMapS (χ chibar : ClassFunction L ℂ) :
    ClassFunction L ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  LinearMap.id - (innerLeftℤ (L := L) χ).smulRight ((ClassFunction.inner χ χ)⁻¹ • χ)
    - (innerLeftℤ (L := L) chibar).smulRight ((ClassFunction.inner chibar chibar)⁻¹ • chibar)

@[simp] theorem orthoResidualMapS_apply (χ chibar φ : ClassFunction L ℂ) :
    orthoResidualMapS (L := L) χ chibar φ =
      φ - ClassFunction.inner φ χ • ((ClassFunction.inner χ χ)⁻¹ • χ)
        - ClassFunction.inner φ chibar • ((ClassFunction.inner chibar chibar)⁻¹ • chibar) := by
  simp [orthoResidualMapS, LinearMap.smulRight_apply]

/-- The scaled residual `φ⊥` is orthogonal to `χ` (using `‖χ‖² ≠ 0` and `⟨χ̄,χ⟩ = 0`). -/
theorem inner_orthoResidualMapS_left {χ chibar : ClassFunction L ℂ}
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMapS (L := L) χ chibar φ) χ = 0 := by
  simp only [orthoResidualMapS_apply, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
  rw [hχbarχ, mul_zero, mul_zero, sub_zero, inv_mul_cancel₀ hχχne, mul_one, sub_self]

/-- The scaled residual `φ⊥` is orthogonal to `χ̄` (using `‖χ̄‖² ≠ 0` and `⟨χ,χ̄⟩ = 0`). -/
theorem inner_orthoResidualMapS_right {χ chibar : ClassFunction L ℂ}
    (hχχbar : ClassFunction.inner χ chibar = 0)
    (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMapS (L := L) χ chibar φ) chibar = 0 := by
  simp only [orthoResidualMapS_apply, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
  rw [hχχbar, mul_zero, mul_zero, sub_zero, inv_mul_cancel₀ hχbarχbarne, mul_one, sub_self]

/-- The scaled rank-`2` **re-targeting** of an integral map `τ₁`:
`φ ↦ τ₁ φ⊥ + (⟨φ,χ⟩/‖χ‖²)·X + (⟨φ,χ̄⟩/‖χ̄‖²)·X̄`.  On the integral lattice `ℤ[S₁ ∪ {χ, χ̄}]`
(`χ ⊥ S₁`, `χ ⊥ χ̄`) it sends `χ ↦ X`, `χ̄ ↦ X̄` and keeps `τ₁` on the residual, with **integer**
coefficients (the projection coordinate). -/
noncomputable def retargetS (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) :
    IntegralCharacterMap L G :=
  τ₁ ∘ₗ orthoResidualMapS (L := L) χ chibar
    + (innerLeftℤ (L := L) χ).smulRight ((ClassFunction.inner χ χ)⁻¹ • X)
    + (innerLeftℤ (L := L) chibar).smulRight ((ClassFunction.inner chibar chibar)⁻¹ • Xbar)

@[simp] theorem retargetS_apply (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    retargetS τ₁ χ chibar X Xbar φ =
      τ₁ (orthoResidualMapS (L := L) χ chibar φ)
        + ClassFunction.inner φ χ • ((ClassFunction.inner χ χ)⁻¹ • X)
        + ClassFunction.inner φ chibar • ((ClassFunction.inner chibar chibar)⁻¹ • Xbar) := by
  simp [retargetS, LinearMap.smulRight_apply]

/-- **The scaled lattice-relative re-targeting isometry (Peterfalvi (5.6.3), reducible break).**

The `‖χ‖² ≠ 1` analogue of `retarget_inner_eq_on`.  The Gram-matching hypotheses are
`⟨X,X⟩ = ⟨χ,χ⟩` / `⟨X̄,X̄⟩ = ⟨χ̄,χ̄⟩` (rather than `= 1`); the residual orthogonality uses only
`⟨χ,χ⟩ ≠ 0` / `⟨χ̄,χ̄⟩ ≠ 0`.  On the submodule `M` (closed under the scaled Gram–Schmidt residual,
with `χ, χ̄ ∈ M`), `retargetS` preserves the inner product — the lattice `ℤ[S₁ ∪ {χ, χ̄}]` isometry
for a **reducible** break character.  The scaling cancels term-by-term: the `X`-block contributes
`(s/‖χ‖²)·conj(s'/‖χ‖²)·⟨X,X⟩`, equal by `⟨X,X⟩ = ⟨χ,χ⟩` to the source `χ`-block. -/
theorem retargetS_inner_eq_on {τ₁ : IntegralCharacterMap L G}
    {χ chibar : ClassFunction L ℂ} {X Xbar : ClassFunction G ℂ}
    {M : Submodule ℂ (ClassFunction L ℂ)} [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hχM : χ ∈ M) (hchibarM : chibar ∈ M)
    (hτ₁ : ∀ u v : ClassFunction L ℂ, u ∈ M → v ∈ M →
      ClassFunction.inner (τ₁ u) (τ₁ v) = ClassFunction.inner u v)
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = ClassFunction.inner χ χ)
    (hXbarXbar : ClassFunction.inner Xbar Xbar = ClassFunction.inner chibar chibar)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hX_ortho : ∀ ξ ∈ M, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ M, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) Xbar = 0)
    {φ ψ : ClassFunction L ℂ} (hφ : φ ∈ M) (hψ : ψ ∈ M) :
    ClassFunction.inner (retargetS τ₁ χ chibar X Xbar φ) (retargetS τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner φ ψ := by
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMapS (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMapS (L := L) χ chibar ψ with hψperp
  have hφperpM : φperp ∈ M := by
    rw [hφperp, orthoResidualMapS_apply]
    exact M.sub_mem (M.sub_mem hφ (M.smul_mem _ (M.smul_mem _ hχM)))
      (M.smul_mem _ (M.smul_mem _ hchibarM))
  have hψperpM : ψperp ∈ M := by
    rw [hψperp, orthoResidualMapS_apply]
    exact M.sub_mem (M.sub_mem hψ (M.smul_mem _ (M.smul_mem _ hχM)))
      (M.smul_mem _ (M.smul_mem _ hchibarM))
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMapS_left hχχne hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMapS_right hχχbar hχbarχbarne φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMapS_left hχχne hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMapS_right hχχbar hχbarχbarne ψ
  have himg : ClassFunction.inner (retargetS τ₁ χ chibar X Xbar φ)
      (retargetS τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp)
        + s * (ClassFunction.inner χ χ)⁻¹ * star (s' * (ClassFunction.inner χ χ)⁻¹)
            * ClassFunction.inner χ χ
        + t * (ClassFunction.inner chibar chibar)⁻¹ * star (t' * (ClassFunction.inner chibar chibar)⁻¹)
            * ClassFunction.inner chibar chibar := by
    rw [retargetS_apply, retargetS_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    simp only [smul_smul]
    exact inner_block_expand_gen hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperpM hφperp_χ hφperp_χbar)
      (hXbar_ortho φperp hφperpM hφperp_χ hφperp_χbar)
      (hX_ortho ψperp hψperpM hψperp_χ hψperp_χbar)
      (hXbar_ortho ψperp hψperpM hψperp_χ hψperp_χbar)
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp
        + s * (ClassFunction.inner χ χ)⁻¹ * star (s' * (ClassFunction.inner χ χ)⁻¹)
            * ClassFunction.inner χ χ
        + t * (ClassFunction.inner chibar chibar)⁻¹ * star (t' * (ClassFunction.inner chibar chibar)⁻¹)
            * ClassFunction.inner chibar chibar := by
    have hφ' : φ = φperp + (s * (ClassFunction.inner χ χ)⁻¹) • χ
        + (t * (ClassFunction.inner chibar chibar)⁻¹) • chibar := by
      rw [hφperp, orthoResidualMapS_apply, ← hs, ← ht, smul_smul, smul_smul]; abel
    have hψ' : ψ = ψperp + (s' * (ClassFunction.inner χ χ)⁻¹) • χ
        + (t' * (ClassFunction.inner chibar chibar)⁻¹) • chibar := by
      rw [hψperp, orthoResidualMapS_apply, ← hs', ← ht', smul_smul, smul_smul]; abel
    rw [hφ', hψ']
    exact inner_block_expand_gen rfl rfl hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁ φperp ψperp hφperpM hψperpM]

end OddOrder.Peterfalvi.S07
