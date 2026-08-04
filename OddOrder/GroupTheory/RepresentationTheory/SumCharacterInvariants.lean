/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Invariants

/-!
# The sum of a character over the group counts the invariants

For a representation `ρ` of a finite group `H` over a field where `|H|` is invertible,

`∑_{h ∈ H} χ_ρ(h) = |H| · dim_K V^H`.

The averaging map `(1/|H|) ∑_h ρ(h)` is a projection onto the invariants, and the trace of a
projection is the dimension of its image.

This is what turns the intermediate sum `∑_{x ∈ P} χ(x⁻¹)` in Navarro (4.19) into `|P| [χ_P, 1_P]`
with the multiplicity `[χ_P, 1_P]` a **non-negative integer** — the point being that after
dividing by `|P| = p^a` one still has something in the valuation ring, so the expression survives
reduction to the residue field.

## Main results

* `OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants`
-/

namespace OddOrder.RepresentationTheory

variable {K H V : Type*} [Field K] [Group H] [Fintype H] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (Fintype.card H : K)]

/-- **`∑_{h ∈ H} χ_ρ(h) = |H| · dim V^H`.**  The averaging map is a projection onto the
invariants, and the trace of a projection is the dimension of its image. -/
theorem sum_character_eq_card_mul_finrank_invariants (ρ : Representation K H V) :
    ∑ h : H, ρ.character h
      = (Fintype.card H : K) * (Module.finrank K ρ.invariants : K) := by
  classical
  have htrace : LinearMap.trace K V (Representation.averageMap ρ)
      = (Module.finrank K ρ.invariants : K) := (Representation.isProj_averageMap ρ).trace
  have havg : Representation.averageMap ρ
      = (⅟(Fintype.card H : K)) • ∑ h : H, ρ h := by
    rw [Representation.averageMap, _root_.GroupAlgebra.average, map_smul]
    congr 1
    rw [map_sum]
    exact Finset.sum_congr rfl fun h _ => Representation.asAlgebraHom_single_one ρ h
  rw [havg, map_smul, map_sum] at htrace
  have hsum : ∑ h : H, LinearMap.trace K V (ρ h) = ∑ h : H, ρ.character h := rfl
  rw [hsum] at htrace
  rw [← htrace, smul_eq_mul, ← mul_assoc, mul_invOf_self, one_mul]

end OddOrder.RepresentationTheory
