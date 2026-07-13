/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusGammaNormEstimate
import OddOrder.Peterfalvi.S09_NonexistenceCertain.FrobeniusFamily

/-!
# Frobenius-family B-sum estimate (Peterfalvi 7.10)

This file combines the concrete weighted Gamma decomposition from (7.9) with
the residual norm bound from (7.8.b).  The orthogonal integer-decomposition
estimate then gives Peterfalvi's unweighted sum bound

`sum_{j in B} (h_j - 1) / e_j <= e_i - 1`

for the concrete set `B` of vanishing reverse coefficients.

Textbook: Peterfalvi, Section 7, pp. 41-43, equation (7.10).
Coq comparison: `PFsection7.v`, proof of `CoherentFrobeniusPartition`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyBsum

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))
variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- Peterfalvi's concrete set `B` contains only indices different from the
selected member. -/
theorem reverseCoefficientZeroIndices_avoids (i : Fin k) :
    ∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i, i ≠ j := by
  intro j hj
  exact (F.mem_reverseCoefficientZeroIndices_iff
    hodd hnilp C hFrob i j).mp hj |>.1

/-- **Peterfalvi (7.10), concrete B-sum bound.**  On the set of other family
members whose reverse coefficient vanishes, the weighted Gamma projection and
`‖Gamma_i‖² ≤ e_i - 1` give
`sum_{j in B} (h_j - 1) / e_j ≤ e_i - 1`. -/
theorem reverseCoefficientZeroIndices_Bsum_le (i : Fin k) :
    (∑ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
      ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1 := by
  classical
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  obtain ⟨x, Γ₁, horth, hΓ, hΓ₁, hx_nonzero⟩ :=
    F.exists_weightedGammaDecomposition_on_reverseCoefficientZeroIndices
      hodd hnilp C hFrob i
  exact F.Bsum_le_of_orthogonal_integer_decomposition B
    (F.weightedNuSumAt hodd hnilp C hFrob) x
    (F.gammaAt hodd hnilp C hFrob i) Γ₁
    hΓ horth hΓ₁ hx_nonzero
    (F.gammaAt_inner_self_re_le hodd hnilp C hFrob i)

end FamilyBsum

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
