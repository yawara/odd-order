/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character

/-!
# Character values at involutions are rational integers

If `t² = 1` then `ρ t` is an involution of `V`, so `(1 + ρ t)/2` is a projection onto its
`+1`-eigenspace and

`χ_ρ(t) = 2 · dim V₊ − dim V`.

In particular `χ_ρ(t)` lies in the image of `ℤ`, whatever the ground field (of characteristic
`≠ 2`) — no theory of algebraic integers or of roots of unity is involved.

Navarro's remark after (5.1) says more, that the generalized decomposition numbers `d^x_{χφ}` lie
in `ℤ[ζ]` for `ζ` a primitive `o(x)`-th root of unity; the proof of (7.2) uses that only through
`d^t_{χ1} = χ(t)` for an involution `t`, which this file supplies directly.

## Main results

* `OddOrder.RepresentationTheory.character_eq_of_mul_self_eq_one` — `χ(t) = 2 dim V₊ − dim V`
* `OddOrder.RepresentationTheory.exists_intCast_character_of_mul_self_eq_one`
-/

namespace OddOrder.RepresentationTheory

open Module

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group G]

/-- The projection onto the `+1`-eigenspace of an involution, `(1 + ρ t)/2`. -/
noncomputable def involutionProj (σ : Representation K G V) (t : G) : Module.End K V :=
  (2 : K)⁻¹ • (1 + σ t)

omit [FiniteDimensional K V] in
theorem isIdempotentElem_involutionProj (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {t : G}
    (ht : t * t = 1) : IsIdempotentElem (involutionProj σ t) := by
  have hA : (σ t) * (σ t) = 1 := by rw [← map_mul, ht, map_one]
  have hsq : ((1 : Module.End K V) + σ t) * (1 + σ t) = (2 : K) • (1 + σ t) := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, hA]
    module
  rw [IsIdempotentElem, involutionProj, smul_mul_smul_comm, hsq, smul_smul]
  congr 1
  field_simp

/-- **`χ(t) = 2 · dim V₊ − dim V`** for `t² = 1`: the trace of the projection `(1 + ρ t)/2` is the
dimension of its image. -/
theorem character_eq_of_mul_self_eq_one (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {t : G}
    (ht : t * t = 1) :
    σ.character t
      = 2 * (finrank K (LinearMap.range (involutionProj σ t)) : K) - (finrank K V : K) := by
  have htr : LinearMap.trace K V (involutionProj σ t)
      = (finrank K (LinearMap.range (involutionProj σ t)) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr
      (isIdempotentElem_involutionProj σ h2 ht)).trace
  have htrP : LinearMap.trace K V (involutionProj σ t)
      = (2 : K)⁻¹ * ((finrank K V : K) + σ.character t) := by
    rw [involutionProj, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
    rfl
  rw [← htr, htrP]
  field_simp
  ring

/-- **Character values at involutions are rational integers.** -/
theorem exists_intCast_character_of_mul_self_eq_one (σ : Representation K G V) (h2 : (2 : K) ≠ 0)
    {t : G} (ht : t * t = 1) : ∃ n : ℤ, σ.character t = (n : K) := by
  refine ⟨2 * (finrank K (LinearMap.range (involutionProj σ t)) : ℤ) - (finrank K V : ℤ), ?_⟩
  push_cast
  exact character_eq_of_mul_self_eq_one σ h2 ht

end OddOrder.RepresentationTheory
