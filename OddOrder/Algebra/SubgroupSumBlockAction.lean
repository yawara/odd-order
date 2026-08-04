/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacter
import OddOrder.Algebra.SubgroupSum

/-!
# A normal subgroup whose sum acts invertibly on a block is killed by it

`N̂ = ∑_{n ∈ N} n` is central for `N ⊴ G`, so it acts on the `i`-th block of a splitting
`π : k[G] ↠ ∏_j M_{n_j}(k)` by the scalar `ω_i(N̂)`.  The absorption `n · N̂ = N̂` then says that
`π(n) i` fixes that scalar matrix, so as soon as `ω_i(N̂)` is invertible we get `π(n) i = 1`.

This is the `p'`-counterpart of `NormalPSubgroupTrivialAction`: there a normal `p`-subgroup is
killed by *every* block, here a normal subgroup is killed by exactly those blocks on which `N̂`
acts invertibly.  It is what makes `ker(B)` (Navarro (6.9)) sit inside the kernels of the
irreducible Brauer characters of `B`, the first half of Navarro (6.12).

## Main results

* `OddOrder.GroupAlgebra.pi_single_eq_one_of_isUnit_centralScalar` — `ω_i(N̂)` invertible ⟹ the
  `i`-th block kills `N`
-/

namespace OddOrder.GroupAlgebra

open Matrix MonoidAlgebra OddOrder.MatrixModule

variable {k ι G : Type*} [Field k] [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) [Nonempty (nn i)]

/-- `N̂` acts on the `i`-th block by the scalar matrix `ω_i(N̂)`. -/
theorem pi_subgroupSum_eq_scalar (hπ : Function.Surjective π) {N : Subgroup G} (hN : N.Normal) :
    π (subgroupSum k N) i
      = Matrix.scalar (nn i) (centralScalar π i (subgroupSum k N)) :=
  scalar_centralScalar π i hπ
    (Semigroup.mem_center_iff.mpr
      (Subalgebra.mem_center_iff.mp (subgroupSum_mem_center hN)))

/-- **A block on which `N̂` acts invertibly kills `N`.**

The absorption `n · N̂ = N̂` gives `π(n) i · ω_i(N̂) = ω_i(N̂)` as matrices; cancelling the
invertible scalar matrix leaves `π(n) i = 1`. -/
theorem pi_single_eq_one_of_isUnit_centralScalar (hπ : Function.Surjective π) {N : Subgroup G}
    (hN : N.Normal) (hunit : IsUnit (centralScalar π i (subgroupSum k N)))
    {u : G} (hu : u ∈ N) : π (single u (1 : k)) i = 1 := by
  have habs : π (single u (1 : k)) i * π (subgroupSum k N) i = π (subgroupSum k N) i := by
    rw [← Pi.mul_apply, ← map_mul, single_mul_subgroupSum hu]
  rw [pi_subgroupSum_eq_scalar π i hπ hN] at habs
  obtain ⟨v, hv⟩ := (Matrix.scalar (nn i)).isUnit_map hunit
  rw [← hv] at habs
  simpa using congrArg (· * (↑v⁻¹ : Matrix (nn i) (nn i) k)) habs

end OddOrder.GroupAlgebra
