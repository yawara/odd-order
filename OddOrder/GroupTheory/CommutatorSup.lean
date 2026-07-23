/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Commutators with subgroup joins modulo a normal subgroup

The subgroup commutator does not distribute over joins as an equality in a
general group.  Modulo a normal subgroup, however, centralising two subgroups
implies centralising their join.  This file records that reusable inclusion.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open scoped commutatorElement

/-- **Bilinearity modulo a normal subgroup.**  If `⁅A, B⁆ ≤ K` and
`⁅A, C⁆ ≤ K` with `K` normal, then `⁅A, B ⊔ C⁆ ≤ K`.

The statement is proved in `G ⧸ K`: the image of `A` centralises the images
of `B` and `C`, hence their join. -/
theorem commutator_sup_le_of_le
    {G : Type*} [Group G] {A B C K : Subgroup G} [K.Normal]
    (hB : ⁅A, B⁆ ≤ K) (hC : ⁅A, C⁆ ≤ K) : ⁅A, B ⊔ C⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  have hle : (B ⊔ C).map (QuotientGroup.mk' K) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' K) a} : Set (G ⧸ K)) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_ <;>
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      change Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) y)
      rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      first
        | exact hB (Subgroup.commutator_mem_commutator ha hy)
        | exact hC (Subgroup.commutator_mem_commutator ha hy)
  have hcomm : Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) x) := by
    have hmem := hle (Subgroup.mem_map_of_mem _ hx)
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact hmem ((QuotientGroup.mk' K) a) rfl
  rw [← QuotientGroup.eq_one_iff,
    show ((⁅a, x⁆ : G) : G ⧸ K) = (QuotientGroup.mk' K) ⁅a, x⁆ from rfl,
    map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact hcomm

end OddOrder.GroupTheory
