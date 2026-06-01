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

-- The `O_π(M)` / `O_p(M)` / `O_{p'}(M)`-in-`G` constructions formerly defined here
-- (`piCoreIn` / `pCoreIn` / `pPrimeCoreIn`) are unified into the canonical
-- `OddOrder.GroupTheory.opiCoreInG` in `GroupTheory.SubgroupInAmbient` (issue 0052).

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
