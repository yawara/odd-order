/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CharacterInvolution

/-!
# Character values at an element of order dividing `4` that is real

If `y⁴ = 1` then `u = (ρ y + ρ y⁻¹)/2` satisfies

`u³ = u`,

because `(A + A³)³ = A³ + 3A⁵ + 3A⁷ + A⁹ = 4(A + A³)` once `A⁴ = 1`.  Hence
`e_± = (u² ± u)/2` are idempotent, `e₊ − e₋ = u`, and

`χ_ρ(y) + χ_ρ(y⁻¹) = 2 tr(u) = 2(dim im e₊ − dim im e₋)`.

So as soon as `χ_ρ(y⁻¹) = χ_ρ(y)` — which holds when `y` is conjugate to `y⁻¹`, as it is for an
element of order `4` of a quaternion group — the value `χ_ρ(y)` lies in the image of `ℤ`.

This is what Navarro's proof of the Brauer–Suzuki theorem records as "since the irreducible
characters of `P` are integer valued, it follows that `χ_i(y) ∈ ℤ`" (p. 140).  As with
`CharacterInvolution`, no algebraic integers and no roots of unity are involved: only that the
ground field has characteristic `≠ 2`.

## Main results

* `OddOrder.RepresentationTheory.pow_three_realProj` — `u³ = u`
* `OddOrder.RepresentationTheory.character_add_character_inv_eq` — `χ(y) + χ(y⁻¹) = 2(r₊ − r₋)`
* `OddOrder.RepresentationTheory.exists_intCast_character_of_pow_four_eq_one`
-/

namespace OddOrder.RepresentationTheory

open Module

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group G]

/-- The "real part" `(ρ y + ρ y⁻¹)/2` of `ρ y`. -/
noncomputable def realProj (σ : Representation K G V) (y : G) : Module.End K V :=
  (2 : K)⁻¹ • (σ y + σ y⁻¹)

/-- The idempotent `(u² + u)/2` cutting out the `+1`-part of `u = realProj σ y`. -/
noncomputable def realProjPos (σ : Representation K G V) (y : G) : Module.End K V :=
  (2 : K)⁻¹ • ((realProj σ y) ^ 2 + realProj σ y)

/-- The idempotent `(u² − u)/2` cutting out the `−1`-part of `u = realProj σ y`. -/
noncomputable def realProjNeg (σ : Representation K G V) (y : G) : Module.End K V :=
  (2 : K)⁻¹ • ((realProj σ y) ^ 2 - realProj σ y)

omit [FiniteDimensional K V] in
/-- **`u³ = u`** for `u = (ρ y + ρ y⁻¹)/2` and `y⁴ = 1`. -/
theorem pow_three_realProj (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {y : G} (hy : y ^ 4 = 1) :
    (realProj σ y) ^ 3 = realProj σ y := by
  have hy3 : y * y * y = y⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc y * y * y * y = y ^ 4 := by simp [pow_succ]
      _ = 1 := hy
  have hyi3 : y⁻¹ * y⁻¹ * y⁻¹ = y := by
    have hinv : y⁻¹ * y⁻¹ * y⁻¹ = (y * y * y)⁻¹ := by group
    rw [hinv, hy3, inv_inv]
  have hAB : σ y * σ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hBA : σ y⁻¹ * σ y = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hA3 : σ y * σ y * σ y = σ y⁻¹ := by rw [← map_mul, ← map_mul, hy3]
  have hB3 : σ y⁻¹ * σ y⁻¹ * σ y⁻¹ = σ y := by rw [← map_mul, ← map_mul, hyi3]
  -- expand `(A + B)³`
  have hexp : (σ y + σ y⁻¹) * (σ y + σ y⁻¹) * (σ y + σ y⁻¹)
      = (4 : K) • (σ y + σ y⁻¹) := by
    have h1 : (σ y + σ y⁻¹) * (σ y + σ y⁻¹)
        = σ y * σ y + σ y⁻¹ * σ y⁻¹ + (2 : K) • (1 : Module.End K V) := by
      rw [mul_add, add_mul, add_mul, hAB, hBA]
      module
    rw [h1, add_mul, add_mul, smul_mul_assoc, one_mul, mul_add, mul_add,
      show σ y * σ y * σ y = σ y⁻¹ from hA3,
      show σ y⁻¹ * σ y⁻¹ * σ y⁻¹ = σ y from hB3,
      show σ y * σ y * σ y⁻¹ = σ y from by rw [mul_assoc, hAB, mul_one],
      show σ y⁻¹ * σ y⁻¹ * σ y = σ y⁻¹ from by rw [mul_assoc, hBA, mul_one]]
    module
  rw [pow_succ, pow_succ, pow_one, realProj, smul_mul_smul_comm, smul_mul_smul_comm, hexp,
    smul_smul]
  congr 1
  field_simp
  ring

omit [FiniteDimensional K V] in
/-- **`(u² + u)/2` is idempotent.** -/
theorem isIdempotentElem_realProjPos (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {y : G}
    (hy : y ^ 4 = 1) : IsIdempotentElem (realProjPos σ y) := by
  have hu := pow_three_realProj σ h2 hy
  have hu4 : (realProj σ y) ^ 4 = (realProj σ y) ^ 2 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hu, ← pow_two]
  rw [IsIdempotentElem, realProjPos, smul_mul_smul_comm]
  have hsq : ((realProj σ y) ^ 2 + realProj σ y) * ((realProj σ y) ^ 2 + realProj σ y)
      = (2 : K) • ((realProj σ y) ^ 2 + realProj σ y) := by
    have e1 : (realProj σ y) ^ 2 * (realProj σ y) ^ 2 = (realProj σ y) ^ 2 := by
      rw [← pow_add]; exact hu4
    have e2 : (realProj σ y) ^ 2 * realProj σ y = realProj σ y := by
      rw [← pow_succ]; exact hu
    have e3 : realProj σ y * (realProj σ y) ^ 2 = realProj σ y := by
      rw [pow_two, ← mul_assoc, ← pow_two, ← pow_succ]; exact hu
    rw [mul_add, add_mul, add_mul, e1, e2, e3, ← pow_two]
    module
  rw [hsq, smul_smul]
  congr 1
  field_simp

omit [FiniteDimensional K V] in
/-- **`(u² − u)/2` is idempotent.** -/
theorem isIdempotentElem_realProjNeg (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {y : G}
    (hy : y ^ 4 = 1) : IsIdempotentElem (realProjNeg σ y) := by
  have hu := pow_three_realProj σ h2 hy
  have hu4 : (realProj σ y) ^ 4 = (realProj σ y) ^ 2 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hu, ← pow_two]
  rw [IsIdempotentElem, realProjNeg, smul_mul_smul_comm]
  have hsq : ((realProj σ y) ^ 2 - realProj σ y) * ((realProj σ y) ^ 2 - realProj σ y)
      = (2 : K) • ((realProj σ y) ^ 2 - realProj σ y) := by
    have e1 : (realProj σ y) ^ 2 * (realProj σ y) ^ 2 = (realProj σ y) ^ 2 := by
      rw [← pow_add]; exact hu4
    have e2 : (realProj σ y) ^ 2 * realProj σ y = realProj σ y := by
      rw [← pow_succ]; exact hu
    have e3 : realProj σ y * (realProj σ y) ^ 2 = realProj σ y := by
      rw [pow_two, ← mul_assoc, ← pow_two, ← pow_succ]; exact hu
    rw [mul_sub, sub_mul, sub_mul, e1, e2, e3, ← pow_two]
    module
  rw [hsq, smul_smul]
  congr 1
  field_simp

/-- **`χ(y) + χ(y⁻¹) = 2(dim im e₊ − dim im e₋)`.**  `e₊ − e₋ = u`, and the trace of an
idempotent is the dimension of its image. -/
theorem character_add_character_inv_eq (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {y : G}
    (hy : y ^ 4 = 1) :
    σ.character y + σ.character y⁻¹
      = 2 * ((finrank K (LinearMap.range (realProjPos σ y)) : K)
          - (finrank K (LinearMap.range (realProjNeg σ y)) : K)) := by
  have htrPos : LinearMap.trace K V (realProjPos σ y)
      = (finrank K (LinearMap.range (realProjPos σ y)) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr
      (isIdempotentElem_realProjPos σ h2 hy)).trace
  have htrNeg : LinearMap.trace K V (realProjNeg σ y)
      = (finrank K (LinearMap.range (realProjNeg σ y)) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr
      (isIdempotentElem_realProjNeg σ h2 hy)).trace
  have hdiff : realProjPos σ y - realProjNeg σ y = realProj σ y := by
    rw [realProjPos, realProjNeg, ← smul_sub]
    have : (realProj σ y) ^ 2 + realProj σ y - ((realProj σ y) ^ 2 - realProj σ y)
        = (2 : K) • realProj σ y := by module
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have htrU : LinearMap.trace K V (realProj σ y)
      = (2 : K)⁻¹ * (σ.character y + σ.character y⁻¹) := by
    rw [realProj, map_smul, map_add, smul_eq_mul]
    rfl
  have := congrArg (LinearMap.trace K V) hdiff
  rw [map_sub, htrPos, htrNeg, htrU] at this
  field_simp at this
  linear_combination -this

/-- **Character values at a real element of order dividing `4` are rational integers.** -/
theorem exists_intCast_character_of_pow_four_eq_one (σ : Representation K G V) (h2 : (2 : K) ≠ 0)
    {y : G} (hy : y ^ 4 = 1) (hreal : σ.character y⁻¹ = σ.character y) :
    ∃ n : ℤ, σ.character y = (n : K) := by
  refine ⟨(finrank K (LinearMap.range (realProjPos σ y)) : ℤ)
    - (finrank K (LinearMap.range (realProjNeg σ y)) : ℤ), ?_⟩
  have h := character_add_character_inv_eq σ h2 hy
  rw [hreal] at h
  push_cast
  refine mul_left_cancel₀ h2 ?_
  rw [← h]
  ring

end OddOrder.RepresentationTheory
