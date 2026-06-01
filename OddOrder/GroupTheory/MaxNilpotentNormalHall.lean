/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.GroupTheory.OpResidual

/-!
# Maximal nilpotent normal Hall subgroups

This shared module records the subgroup used by BG Section 15 and Peterfalvi
Section 10: `M_F`, the maximal nilpotent normal Hall subgroup of a finite
subgroup `M`.

At the scaffold stage the object is defined as a supremum of the subgroups with
Peterfalvi's defining property.  The theorem that this supremum again has the
same maximal nilpotent-normal-Hall property is part of the later BG Section 15
analysis, so downstream files should use the definition for statements and cite
that later result for proofs.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- The relative `pi`-core of `M`: the supremum of normal `pi`-subgroups of `M`,
realized as a subgroup of the ambient group.  This is the generic object behind
notations such as `O_p(M)` and `O_{p'}(M)` when the subgroup is viewed in `G`. -/
noncomputable def piCoreIn (pi : Set ℕ) (M : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Subgroup.IsPiSubgroup pi N}

/-- `O_{p'}(M)`, viewed as a subgroup of the ambient group. -/
noncomputable def pPrimeCoreIn (p : ℕ) (M : Subgroup G) : Subgroup G :=
  piCoreIn ({p}ᶜ) M

/-- `O_p(M)`, viewed as a subgroup of the ambient group. -/
noncomputable def pCoreIn (p : ℕ) (M : Subgroup G) : Subgroup G :=
  piCoreIn {p} M

/-- Peterfalvi's `M_F`: the maximal nilpotent normal Hall subgroup of `M`,
realized in the ambient group.  The Hall set is the set of prime divisors of the
candidate subgroup. -/
noncomputable def maxNilpotentNormalHall (M : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G |
    N ≤ M ∧
      (N.subgroupOf M).Normal ∧
      Group.IsNilpotent ↥(N.subgroupOf M) ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)}

end OddOrder.GroupTheory
