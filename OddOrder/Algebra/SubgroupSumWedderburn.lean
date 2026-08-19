/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacter
import OddOrder.Algebra.SubgroupSum
import OddOrder.Algebra.TraceMulLeft

/-!
# Counting the Wedderburn blocks killed by a normal subgroup

Fix a Wedderburn splitting `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)` and a normal subgroup `N ⊴ G`.  The
subgroup sum `N̂` is central, so `e(N̂)_i = ω_i(N̂) · 1` for a scalar `ω_i(N̂) ∈ K`; and
`N̂² = |N| · N̂` forces that scalar to be `0` or `|N|`.

Computing `tr(x ↦ N̂ · x)` in two ways then counts the blocks where it is `|N|`:

* in the group-element basis of `K[G]` the trace is `|G| · N̂(1) = |G|`;
* across `e` it is `∑_i m_i · tr(e(N̂)_i) = ∑_i m_i² · ω_i(N̂)`.

So `|N| · ∑_{ω_i(N̂) = |N|} m_i² = |G|`.  For `N` a normal `p`-complement this is Navarro's
`∑_{χ ∈ Irr(B_0)} χ(1)² = |G|_p`, the Cartan matrix of the principal block (6.13).

No rank-of-an-idempotent theory is needed — only the two trace computations.

## Main results

* `OddOrder.GroupAlgebra.centralScalar_subgroupSum_eq_zero_or_card` — `ω_i(N̂) ∈ {0, |N|}`
* `OddOrder.GroupAlgebra.sum_sq_centralScalar_subgroupSum` — `∑_i m_i² ω_i(N̂) = |G|`
* `OddOrder.GroupAlgebra.card_mul_sum_sq_eq_card` — `|N| · ∑_{ω_i(N̂) ≠ 0} m_i² = |G|`
-/

namespace OddOrder.GroupAlgebra

open Matrix MonoidAlgebra OddOrder.MatrixModule

variable {K G : Type*} [Field K] [Group G] [Finite G]
variable {ι : Type*} {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

/-- `N̂` is central, so `e` sends it to a scalar matrix in each block. -/
theorem apply_subgroupSum_eq_scalar {N : Subgroup G} (hN : N.Normal) (i : ι) :
    e (subgroupSum K N) i
      = Matrix.scalar (m i) (centralScalar e.toAlgHom.toRingHom i (subgroupSum K N)) :=
  scalar_centralScalar e.toAlgHom.toRingHom i e.surjective
    (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp (subgroupSum_mem_center hN)))

/-- **`ω_i(N̂)` is `0` or `|N|`**, because `N̂² = |N| · N̂` and `K` is a field. -/
theorem centralScalar_subgroupSum_eq_zero_or_card {N : Subgroup G} (hN : N.Normal) (i : ι) :
    centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) = 0 ∨
      centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) = ((Nat.card ↥N : ℕ) : K) := by
  set c := centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) with hc
  have hscal : c * c = ((Nat.card ↥N : ℕ) : K) * c := by
    have h := congrArg (fun x => e x i) (subgroupSum_mul_subgroupSum (R := K) N)
    simp only [map_mul, map_nsmul, Pi.mul_apply, Pi.smul_apply,
      apply_subgroupSum_eq_scalar e hN i, ← hc] at h
    rw [← map_mul] at h
    have h2 := congrFun (congrFun h (Classical.arbitrary (m i))) (Classical.arbitrary (m i))
    simp only [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq] at h2
    rw [nsmul_eq_mul] at h2
    exact h2
  rcases mul_eq_zero.mp (by linear_combination hscal : c * (c - ((Nat.card ↥N : ℕ) : K)) = 0) with
    h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

section Counting

variable [Fintype ι]

/-- **`∑_i m_i² ω_i(N̂) = |G|`**: the trace of `x ↦ N̂ · x`, computed on both sides of `e`. -/
theorem sum_sq_centralScalar_subgroupSum {N : Subgroup G} (hN : N.Normal) :
    ∑ i, (Fintype.card (m i) : K) ^ 2
        * centralScalar e.toAlgHom.toRingHom i (subgroupSum K N)
      = ((Nat.card G : ℕ) : K) := by
  let := Fintype.ofFinite G
  have hgrp : LinearMap.trace K (MonoidAlgebra K G)
      (LinearMap.mulLeft K (subgroupSum K N)) = ((Nat.card G : ℕ) : K) := by
    rw [OddOrder.Algebra.trace_mulLeft_monoidAlgebra, coeff_subgroupSum_one, mul_one,
      Nat.card_eq_fintype_card]
  have hmat := OddOrder.Algebra.trace_mulLeft_algEquiv e (subgroupSum K N)
  rw [hgrp, OddOrder.Algebra.trace_mulLeft_pi_matrix] at hmat
  rw [← hmat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_subgroupSum_eq_scalar e hN i]
  have htr : Matrix.trace (Matrix.scalar (m i)
      (centralScalar e.toAlgHom.toRingHom i (subgroupSum K N)))
      = (Fintype.card (m i) : K)
        * centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) := by
    simp [Matrix.trace, Matrix.scalar_apply, Finset.card_univ, nsmul_eq_mul]
  rw [htr, sq]
  ring

open scoped Classical in
/-- **`|N| · ∑_{ω_i(N̂) ≠ 0} m_i² = |G|`.**  The blocks split into those killed by `N` — where
`ω_i(N̂) = |N|` — and the rest, where it vanishes. -/
theorem card_mul_sum_sq_eq_card {N : Subgroup G} (hN : N.Normal) :
    ((Nat.card ↥N : ℕ) : K)
        * ∑ i ∈ Finset.univ.filter
            (fun i => centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) ≠ 0),
          (Fintype.card (m i) : K) ^ 2
      = ((Nat.card G : ℕ) : K) := by
  classical
  rw [← sum_sq_centralScalar_subgroupSum e hN, Finset.mul_sum]
  rw [← Finset.sum_filter_of_ne (f := fun i => (Fintype.card (m i) : K) ^ 2 *
    centralScalar e.toAlgHom.toRingHom i (subgroupSum K N))
    (p := fun i => centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) ≠ 0)
    (fun i _ h => fun hz => h (by rw [hz, mul_zero]))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hne := (Finset.mem_filter.mp hi).2
  rw [(centralScalar_subgroupSum_eq_zero_or_card e hN i).resolve_left hne]
  ring

end Counting

end OddOrder.GroupAlgebra
