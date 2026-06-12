/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeIsometry

/-!
# Peterfalvi (4.9)(a): conjugation of the certain-type characters

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, p. 24, statement (4.9)(a).

The (4.9)(a) argument relates the **complex conjugate** of a certain-type column character to another
column: `μ̄_j = μ_{j'}` with `j' ≠ j` (because `j ≠ 0` and `|W|` is odd).  The bridge is the σ-side
Galois equivariance (3.9): conjugation is the cyclotomic automorphism `z ↦ z̄`, so `(ω_{ij}^σ)̄ =
(ω̄_{ij})^σ`, and `ω̄_{ij}` is again a grid character `ω_{i'j'}` (the conjugate of a linear character
is its inverse).

This file develops the conjugation foundation:

* `galoisMap_conj_omega`: the complex conjugate of a linear character `ω(χ)` is `ω(χ⁻¹)` — the
  Galois action by complex conjugation on `ω(χ)` inverts the underlying character (its values are
  roots of unity, where `z̄ = z⁻¹`);
* `certainTypeOmegaSigma_conj`: the complex conjugate of the σ-image `ω_{ij}^σ` is the σ-image of
  the inverse grid character `ω((P_{ij})⁻¹)`, via the (3.9) commutation `sigma_mapRingEquiv_comm`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` ("session 35").
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **Complex conjugation inverts a linear character.**  For a linear character `χ : W →* ℂˣ` of the
finite group `W`, the Galois action of complex conjugation `Complex.conjAe` on `ω(χ)` is `ω(χ⁻¹)`.
Pointwise: `(ω(χ))(w) = χ(w)` is a root of unity (`χ(w)^{|W|} = 1`), so `‖χ(w)‖ = 1` and
`χ(w)̄ = χ(w)⁻¹ = (χ⁻¹)(w)`. -/
theorem galoisMap_conj_omega (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp.W] (χ : hyp.W →* ℂˣ) :
    IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv (hyp.omega χ) = hyp.omega χ⁻¹ := by
  apply IrreducibleCharacter.ext
  apply ClassFunction.ext
  intro w
  rw [IrreducibleCharacter.galoisMap_apply_apply, hyp.omega_apply, hyp.omega_apply,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hnorm : ‖(χ w : ℂ)‖ = 1 := by
    have hp : ((χ w : ℂ)) ^ (Fintype.card hyp.W) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_ne_zero
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- **Conjugation of a certain-type σ-image.**  The complex conjugate of `ω_{ij}^σ` is the σ-image of
the inverse grid character `(P_{ij})⁻¹` (`P_{ij} = omegaProdCharTic h χ₂ i`).  Combines the (3.9)
Galois commutation `sigma_mapRingEquiv_comm` (σ intertwines the cyclotomic Galois action) with
`galoisMap_conj_omega` (conjugation inverts the linear character).  This is the (3.9) ingredient of
(4.9)(a): the conjugate of a σ-image stays in the σ-image grid, at the conjugate index. -/
theorem certainTypeOmegaSigma_conj (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (certainTypeOmegaSigma h χ₂ i)
      = (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h)
          ((ticVdiff h).omega (omegaProdCharTic h χ₂ i)⁻¹) := by
  rw [certainTypeOmegaSigma,
    (ticVdiff h).sigma_mapRingEquiv_comm rfl (ticVdiffFullDadeApplication h),
    galoisMap_conj_omega]

/-! ### The grid-index conjugation map

The inverse grid character `(P_{ij})⁻¹` is again a grid character: since `ω(χ₁, χ₂) = χ₁∘wFst ·
χ₂∘wSnd` and the codomain `ℂˣ` is abelian, inversion acts coordinatewise, `(ω(χ₁,χ₂))⁻¹ =
ω(χ₁⁻¹, χ₂⁻¹)`.  At the certain-type level this sends column `χ₂` to `χ₂⁻¹` and row `i` to the
row `i'` with `w1CharEquiv i' = (w1CharEquiv i)⁻¹`.  Combined with `certainTypeOmegaSigma_conj`,
this yields `(ω_{ij}^σ)̄ = ω_{i'j'}^σ`: the conjugate of a σ-image is the σ-image at the conjugate
grid index (`j' = χ₂⁻¹` independent of `i`). -/

/-- **`omegaProdChar` inverts coordinatewise** (`ℂˣ` abelian): `ω(χ₁, χ₂)⁻¹ = ω(χ₁⁻¹, χ₂⁻¹)`. -/
theorem omegaProdChar_inv (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omegaProdChar χ₁ χ₂)⁻¹ = hyp.omegaProdChar χ₁⁻¹ χ₂⁻¹ := by
  ext w
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv]

/-- The **row-inversion index** `i'`: the unique row with `w1CharEquiv i' = (w1CharEquiv i)⁻¹`. -/
noncomputable def rowInv (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (i : Fin (Nat.card h.W1)) : Fin (Nat.card h.W1) :=
  h.w1CharEquiv.symm ((h.w1CharEquiv i)⁻¹)

@[simp] theorem w1CharEquiv_rowInv (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (i : Fin (Nat.card h.W1)) :
    h.w1CharEquiv (rowInv h i) = (h.w1CharEquiv i)⁻¹ :=
  h.w1CharEquiv.apply_symm_apply _

/-- **The inverse grid character is a grid character at the conjugate index.**
`(P_{ij})⁻¹ = P_{i'j'}` with column `j' = χ₂⁻¹` and row `i' = rowInv i`
(`w1CharEquiv i' = (w1CharEquiv i)⁻¹`).  `omegaProdCharTic` is a composition of `omegaProdChar`
with the bridge iso `ticWEquivSdiffW`; inversion passes through the composition (abelian `ℂˣ`) and
acts coordinatewise on `omegaProdChar` (`omegaProdChar_inv`). -/
theorem omegaProdCharTic_inv (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (omegaProdCharTic h χ₂ i)⁻¹ = omegaProdCharTic h χ₂⁻¹ (rowInv h i) := by
  ext w
  simp only [omegaProdCharTic, MonoidHom.comp_apply, w1CharEquiv_rowInv,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.inv_apply, mul_inv]
  rfl

/-- **σ-grid conjugation closure** (the (4.9)(a) grid identity through σ).  The complex conjugate of
the certain-type σ-image `ω_{ij}^σ` is the σ-image `ω_{i'j'}^σ` at the conjugate grid index
(`j' = χ₂⁻¹`, `i' = rowInv i`).  Combines `certainTypeOmegaSigma_conj` (conjugation = inverse grid
character through σ) with `omegaProdCharTic_inv` (the inverse is the conjugate-index grid character). -/
theorem certainTypeOmegaSigma_conj_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (certainTypeOmegaSigma h χ₂ i)
      = certainTypeOmegaSigma h χ₂⁻¹ (rowInv h i) := by
  rw [certainTypeOmegaSigma_conj, certainTypeOmegaSigma]
  exact congrArg
    (fun c => (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h) ((ticVdiff h).omega c))
    (omegaProdCharTic_inv h χ₂ i)

end OddOrder.Peterfalvi.S06
