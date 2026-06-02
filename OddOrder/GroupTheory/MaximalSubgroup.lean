/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Order.Atoms

/-!
# Maximal subgroup families `ℳ`, `ℳ(H)` and the uniqueness predicate `𝒰`

`OddOrder.GroupTheory` shared module providing the Bender–Glauberman notation for the
**family of maximal subgroups** and the **uniqueness subgroups** of a group `G`.

These are introduced in BG §7 (mmd L2135, where `G` is fixed as a minimal counterexample)
and used pervasively through §8–§16. They live in the shared `GroupTheory` namespace because
every chapter II–IV section refers to them.

## Main definitions

* `maximalSubgroups G` (BG `ℳ`): the set of maximal subgroups of `G`, i.e. the coatoms of
  the subgroup lattice (`IsCoatom`).
* `maximalSubgroupsContaining H` (BG `ℳ(H)`): the maximal subgroups of `G` containing `H`.
* `IsUniquelyMaximal H` (BG `H ∈ 𝒰`): `H` is a proper subgroup contained in a **unique**
  maximal subgroup of `G`. This is the conclusion form of the BG Uniqueness Theorem (§9).

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  Chapter II §7 (p. 55), §9 (pp. 62-66).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℳ`** (§7): the family of *maximal subgroups* of `G` — the coatoms of the subgroup
lattice (proper subgroups `M < ⊤` maximal under inclusion). -/
def maximalSubgroups (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | IsCoatom M}

/-- **BG `ℳ(H)`** (§7): the maximal subgroups of `G` containing `H`. -/
def maximalSubgroupsContaining (H : Subgroup G) : Set (Subgroup G) :=
  {M | IsCoatom M ∧ H ≤ M}

/-- **BG `H ∈ 𝒰`** (§9, Uniqueness): `H` is *uniquely maximal* — a proper subgroup contained
in exactly one maximal subgroup of `G`. The BG Uniqueness Theorem (Thm 9.6) concludes
`K ∈ 𝒰` for various `K`, and §10–§16 use `𝒰`-membership to pin down the maximal subgroup
attached to a local structure. -/
def IsUniquelyMaximal (H : Subgroup G) : Prop :=
  H < ⊤ ∧ ∃! M : Subgroup G, IsCoatom M ∧ H ≤ M

@[simp]
theorem mem_maximalSubgroups {M : Subgroup G} : M ∈ maximalSubgroups G ↔ IsCoatom M :=
  Iff.rfl

@[simp]
theorem mem_maximalSubgroupsContaining {H M : Subgroup G} :
    M ∈ maximalSubgroupsContaining H ↔ IsCoatom M ∧ H ≤ M :=
  Iff.rfl

namespace IsUniquelyMaximal

/-- A uniquely maximal subgroup is proper. -/
theorem lt_top {H : Subgroup G} (h : IsUniquelyMaximal H) : H < ⊤ :=
  h.1

/-- The unique maximal subgroup containing a uniquely maximal `H` (its `ℳ(H)`-singleton). -/
theorem existsUnique {H : Subgroup G} (h : IsUniquelyMaximal H) :
    ∃! M : Subgroup G, IsCoatom M ∧ H ≤ M :=
  h.2

/-- The maximal subgroup attached to a uniquely maximal `H`. -/
noncomputable def uniqueMaximalSubgroup {H : Subgroup G} (h : IsUniquelyMaximal H) :
    Subgroup G :=
  Classical.choose h.existsUnique

/-- The chosen maximal subgroup over `H` is maximal and contains `H`. -/
theorem uniqueMaximalSubgroup_spec {H : Subgroup G} (h : IsUniquelyMaximal H) :
    IsCoatom (h.uniqueMaximalSubgroup) ∧ H ≤ h.uniqueMaximalSubgroup :=
  (Classical.choose_spec h.existsUnique).1

/-- The chosen maximal subgroup over `H` is a member of `ℳ(H)`. -/
theorem uniqueMaximalSubgroup_mem {H : Subgroup G} (h : IsUniquelyMaximal H) :
    h.uniqueMaximalSubgroup ∈ maximalSubgroupsContaining H :=
  h.uniqueMaximalSubgroup_spec

/-- The chosen maximal subgroup over `H` is maximal. -/
theorem uniqueMaximalSubgroup_isCoatom {H : Subgroup G} (h : IsUniquelyMaximal H) :
    IsCoatom h.uniqueMaximalSubgroup :=
  h.uniqueMaximalSubgroup_spec.1

/-- The uniquely maximal subgroup `H` lies in its chosen maximal subgroup. -/
theorem le_uniqueMaximalSubgroup {H : Subgroup G} (h : IsUniquelyMaximal H) :
    H ≤ h.uniqueMaximalSubgroup :=
  h.uniqueMaximalSubgroup_spec.2

/-- Any maximal subgroup containing `H` is the chosen one. -/
theorem eq_uniqueMaximalSubgroup_of_isCoatom_of_le {H M : Subgroup G}
    (h : IsUniquelyMaximal H) (hM : IsCoatom M) (hHM : H ≤ M) :
    M = h.uniqueMaximalSubgroup :=
  (Classical.choose_spec h.existsUnique).2 M ⟨hM, hHM⟩

/-- Two maximal subgroups containing a uniquely maximal `H` are equal. -/
theorem eq_of_isCoatom_of_le {H M N : Subgroup G} (h : IsUniquelyMaximal H)
    (hM : IsCoatom M) (hHM : H ≤ M) (hN : IsCoatom N) (hHN : H ≤ N) :
    M = N :=
  (h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hM hHM).trans
    (h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hN hHN).symm

/-- Membership in `ℳ(H)` is equality with the chosen maximal subgroup. -/
theorem mem_maximalSubgroupsContaining_iff_eq_uniqueMaximalSubgroup {H M : Subgroup G}
    (h : IsUniquelyMaximal H) :
    M ∈ maximalSubgroupsContaining H ↔ M = h.uniqueMaximalSubgroup := by
  constructor
  · intro hM
    exact h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hM.1 hM.2
  · intro hM
    rw [hM]
    exact h.uniqueMaximalSubgroup_mem

/-- `ℳ(H)` is the singleton consisting of the chosen maximal subgroup. -/
theorem maximalSubgroupsContaining_eq_singleton {H : Subgroup G} (h : IsUniquelyMaximal H) :
    maximalSubgroupsContaining H = {h.uniqueMaximalSubgroup} := by
  ext M
  rw [h.mem_maximalSubgroupsContaining_iff_eq_uniqueMaximalSubgroup, Set.mem_singleton_iff]

end IsUniquelyMaximal

end OddOrder.GroupTheory
