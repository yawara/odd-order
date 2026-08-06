/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character

/-!
# The average of a character over a subgroup

For a representation `ρ` of `G` on a finite-dimensional space over a field of characteristic zero
and a finite subgroup `H ≤ G`,

`∑_{h ∈ H} χ_ρ(h) = |H| · n`

for a natural number `n` — namely the dimension of the space of `H`-fixed points.  The proof is the
standard averaging idempotent: `e = |H|⁻¹ ∑_{h ∈ H} ρ(h)` is a projection, so its trace is the rank
of its range (`LinearMap.IsProj.trace`), a natural number.

This is the arithmetic behind **Dickson's theorem** `|G|_p ∣ Φ_φ(1)` (Navarro (3.8)): the
projective indecomposable character `Φ_φ` vanishes off the `p`-regular elements, so on a Sylow
`p`-subgroup `P` it is supported at `1`; writing `Φ_φ = ∑_i d_{iφ} χ_i` with integral `d` and
averaging over `P` turns `Φ_φ(1)` into `|P|` times an integer.

## Main results

* `OddOrder.RepresentationTheory.exists_sum_character_subgroup`
-/

namespace OddOrder.RepresentationTheory

open LinearMap Module

variable {F G V : Type*} [Field F] [CharZero F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- **`∑_{h ∈ H} χ(h) = |H| · n` for a natural number `n`.**

`n` is the dimension of the `H`-fixed subspace: `e = |H|⁻¹ ∑_{h ∈ H} ρ(h)` is idempotent (left
multiplication by `h` permutes `H`), hence a projection onto its range, and the trace of a
projection is the rank of its range. -/
theorem exists_sum_character_subgroup (ρ : Representation F G V) (H : Subgroup G) [Fintype H] :
    ∃ n : ℕ, (∑ h : H, ρ.character (h : G)) = (Fintype.card H : F) * (n : F) := by
  classical
  set c : F := (Fintype.card H : F) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set s : V →ₗ[F] V := ∑ h : H, ρ ((h : H) : G) with hs
  -- left multiplication by `h` permutes `H`, so `ρ h` fixes the sum
  have hmul : ∀ h : H, ρ ((h : H) : G) * s = s := by
    intro h
    rw [hs, Finset.mul_sum,
      Finset.sum_congr rfl fun k _ => show ρ ((h : H) : G) * ρ ((k : H) : G)
          = ρ (((h * k : H) : H) : G) from by rw [← map_mul]; rfl]
    exact Equiv.sum_comp (Equiv.mulLeft h) fun k : H => ρ ((k : H) : G)
  have hss : s * s = c • s := by
    conv_lhs => rw [hs]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun h _ => hmul h, Finset.sum_const,
      Finset.card_univ, hc, ← Nat.cast_smul_eq_nsmul F]
  -- the averaging idempotent
  set e : V →ₗ[F] V := c⁻¹ • s with he
  have hidem : IsIdempotentElem e := by
    change e * e = e
    rw [he, smul_mul_smul_comm, hss, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  refine ⟨finrank F (LinearMap.range e), ?_⟩
  have hse : s = c • e := by rw [he, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hchar : (∑ h : H, ρ.character (h : G)) = trace F V s := by
    rw [hs, map_sum]
    rfl
  rw [hchar, hse, map_smul, hidem.isProj_range.trace, smul_eq_mul]

end OddOrder.RepresentationTheory
