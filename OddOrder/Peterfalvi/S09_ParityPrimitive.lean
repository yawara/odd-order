/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Peterfalvi (7.9) parity primitive — real virtual characters over a group of odd order

The Peterfalvi (7.9) dichotomy consumes the parity fact `cfdot_real_vchar_even`: for two **real**
virtual characters `φ, ψ ∈ ℤ[Irr G]`,
`2 ∣ ⟨φ, ψ⟩ ↔ (2 ∣ ⟨φ, 1_G⟩) ∨ (2 ∣ ⟨ψ, 1_G⟩)`.

The proof pairs each irreducible `χ` with its complex conjugate `χ̄` (`IrreducibleCharacter.conjPerm`):
for real `φ`, the Fourier coefficient `⟨φ, χ̄⟩` equals `⟨φ, χ⟩`, so a non-self-conjugate pair
`{χ, χ̄}` contributes an even amount `2⟨φ,χ⟩⟨ψ,χ⟩` to `⟨φ,ψ⟩ = ∑_χ ⟨φ,χ⟩⟨χ,ψ⟩`; the only
self-conjugate irreducible is the trivial one (`G` odd, Peterfalvi (1.1)), whose contribution is
`⟨φ,1_G⟩⟨ψ,1_G⟩`.  Hence `⟨φ,ψ⟩ ≡ ⟨φ,1_G⟩⟨ψ,1_G⟩ (mod 2)`, and Euclid closes.

This file builds the primitive incrementally.  First: the conjugation involution's only fixed point
is the trivial character (odd order).
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

section InnerConj

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Conjugation identity for the inner product**: `⟨φ, ψ̄⟩ = star ⟨φ̄, ψ⟩`.  Both sides equal
`⅟|G| ∑_g φ(g) ψ(g)` (unfolding `star` on the conjugates).  For **real** `φ` (`φ̄ = φ`) this gives
`⟨φ, ψ̄⟩ = star ⟨φ, ψ⟩`, the Fourier-coefficient symmetry used in the (7.9) parity argument. -/
theorem inner_conj_right (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ ψ.conj = star (ClassFunction.inner φ.conj ψ) := by
  have hstar_inv : star (⅟(Nat.card G : ℂ)) = ⅟(Nat.card G : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, star_natCast]
  simp only [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
    ClassFunction.conj_apply, star_mul', star_sum, hstar_inv, star_star]

/-- For a **real** virtual character `φ` and `χ ∈ Irr G`, the Fourier coefficient of the conjugate
`⟨φ, χ̄⟩` equals `⟨φ, χ⟩` (real, since `φ ∈ ℤ[Irr]`).  This makes the summand `⟨φ,χ⟩⟨ψ,χ⟩` invariant
under the conjugation involution `χ ↦ χ̄`. -/
theorem inner_conjPerm_eq_of_real {φ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G)
    (hφR : ClassFunction.IsReal φ) (χ : IrreducibleCharacter G) :
    ClassFunction.inner φ (IrreducibleCharacter.conjPerm G χ : ClassFunction G ℂ) =
      ClassFunction.inner φ (χ : ClassFunction G ℂ) := by
  rw [IrreducibleCharacter.conjPerm_apply_coe, inner_conj_right, hφR]
  -- `⟨φ, χ⟩` is a real integer, so `star ⟨φ, χ⟩ = ⟨φ, χ⟩`.
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφZ χ.property.mem_ZIrr
  rw [hm, star_intCast]

end InnerConj

/-- **The conjugation involution's only fixed point is the trivial character** (odd order).  Combines
`IrreducibleCharacter.conjPerm_eq_self_iff` (fixed point ↔ real) with Peterfalvi (1.1)
`not_isReal_of_ne_trivial_of_odd_card'` (odd order ⟹ only the trivial irreducible is real).  This is
the self-conjugate case in the (7.9) parity `cfdot_real_vchar_even` orbit-pairing argument. -/
theorem conjPerm_eq_self_iff_eq_trivial_of_odd (hodd : Odd (Nat.card G))
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.conjPerm G χ = χ ↔ χ = trivialIrreducibleCharacter G := by
  rw [IrreducibleCharacter.conjPerm_eq_self_iff]
  constructor
  · intro hreal
    by_contra hne
    exact not_isReal_of_ne_trivial_of_odd_card' hodd hne hreal
  · rintro rfl
    have : (trivialIrreducibleCharacter G : ClassFunction G ℂ) = trivialClassFunction G := rfl
    rw [this]
    exact trivialClassFunction_isReal

end OddOrder.RepresentationTheory
