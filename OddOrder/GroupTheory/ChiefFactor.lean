/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Chief factors

`OddOrder.GroupTheory` shared module for chief factors `U/V` of a finite group.

BG §1 Prop. 1.2 uses intersections of centralizers `C_{G*}(U/V)` over all chief
factors.  mathlib v4.29.1 has an abstract `Order.JordanHolder.CompositionSeries`,
but it does not provide the group-level chief-factor centralizer API needed here.

## Main definitions

* `IsChiefFactor U V`: `V < U`, both normal in `G`, and there is no normal subgroup
  strictly between `V` and `U`.
* `chiefFactorCentralizer U V`: the ambient centralizer `C_G(U/V)`, defined as the
  preimage of the centralizer of the image of `U` in `G ⧸ V`.

The centralizer in a normal subgroup `G*` is obtained as
`G* ⊓ chiefFactorCentralizer U V`.
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A chief factor `U/V` of `G`.

The order of arguments follows the mathematical notation `U/V`: the top subgroup
comes first, then the bottom subgroup. -/
structure IsChiefFactor (U V : Subgroup G) : Prop where
  normal_top : U.Normal
  normal_bot : V.Normal
  lt : V < U
  eq_bot_or_eq_top_of_normal :
    ∀ W : Subgroup G, W.Normal → V ≤ W → W ≤ U → W = V ∨ W = U

namespace IsChiefFactor

variable {U V W : Subgroup G}

/-- In a chief factor `U/V`, the bottom subgroup is contained in the top subgroup. -/
theorem le (h : IsChiefFactor U V) : V ≤ U :=
  h.lt.le

/-- Any normal subgroup between the two terms of a chief factor is one endpoint. -/
theorem eq_or_eq_of_normal (h : IsChiefFactor U V)
    (hW_normal : W.Normal) (hVW : V ≤ W) (hWU : W ≤ U) :
    W = V ∨ W = U :=
  h.eq_bot_or_eq_top_of_normal W hW_normal hVW hWU

end IsChiefFactor

/-- The ambient centralizer `C_G(U/V)` of a factor `U/V`.

This is the preimage in `G` of the centralizer of the image of `U` in `G ⧸ V`.
For a subgroup `G* ≤ G`, BG's `C_{G*}(U/V)` is
`G* ⊓ chiefFactorCentralizer U V`. -/
def chiefFactorCentralizer (U V : Subgroup G) [V.Normal] : Subgroup G :=
  (Subgroup.centralizer
    ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V))).comap
      (QuotientGroup.mk' V)

namespace chiefFactorCentralizer

variable {U V H : Subgroup G} [V.Normal]

/-- If `U` is normal, then the ambient centralizer of `U/V` is normal. -/
instance normal [U.Normal] : (chiefFactorCentralizer U V).Normal := by
  change ((Subgroup.centralizer
    (U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V))).comap
      (QuotientGroup.mk' V)).Normal
  infer_instance

/-- Membership in `C_G(U/V)` is membership of the quotient image in the quotient centralizer. -/
theorem mem_iff {g : G} :
    g ∈ chiefFactorCentralizer U V ↔
      (QuotientGroup.mk' V) g ∈
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
  Iff.rfl

/-- A subgroup lies in `C_G(U/V)` iff its quotient image lies in the quotient centralizer. -/
theorem le_iff_map_le_centralizer :
    H ≤ chiefFactorCentralizer U V ↔
      H.map (QuotientGroup.mk' V) ≤
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) := by
  constructor
  · intro hH
    rintro _ ⟨h, hh, rfl⟩
    exact hH hh
  · intro hH g hg
    exact hH ⟨g, hg, rfl⟩

/-- If the quotient image of `H` centralizes `U/V`, then `H ≤ C_G(U/V)`. -/
theorem le_of_map_le_centralizer
    (hH : H.map (QuotientGroup.mk' V) ≤
      Subgroup.centralizer
        ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V))) :
    H ≤ chiefFactorCentralizer U V :=
  le_iff_map_le_centralizer.mpr hH

/-- If `H ≤ C_G(U/V)`, then `[U, H] ≤ V`. -/
theorem commutator_le_of_le (hH : H ≤ chiefFactorCentralizer U V) :
    ⁅U, H⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro u hu h hh
  have hqh_cent :
      (QuotientGroup.mk' V) h ∈
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
    mem_iff.mp (hH hh)
  have hmul :
      (QuotientGroup.mk' V) u * (QuotientGroup.mk' V) h =
        (QuotientGroup.mk' V) h * (QuotientGroup.mk' V) u :=
    Subgroup.mem_centralizer_iff.mp hqh_cent
      ((QuotientGroup.mk' V) u) ⟨u, hu, rfl⟩
  apply (QuotientGroup.eq_one_iff ⁅u, h⁆).mp
  change (QuotientGroup.mk' V) ⁅u, h⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hmul

/-- If `[U, H] ≤ V`, then `H ≤ C_G(U/V)`. -/
theorem le_of_commutator_le (hcomm : ⁅U, H⁆ ≤ V) :
    H ≤ chiefFactorCentralizer U V := by
  rw [le_iff_map_le_centralizer]
  intro qh hqh
  rw [Subgroup.mem_centralizer_iff]
  intro qu hqu
  obtain ⟨h, hh, rfl⟩ := hqh
  obtain ⟨u, hu, rfl⟩ := hqu
  have hcomm_el : ⁅u, h⁆ ∈ V :=
    Subgroup.commutator_le.mp hcomm u hu h hh
  have hq_comm : ⁅(QuotientGroup.mk' V) u, (QuotientGroup.mk' V) h⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅u, h⁆).mpr hcomm_el
  exact commutatorElement_eq_one_iff_mul_comm.mp hq_comm

/-- A subgroup centralizes `U/V` iff its commutator with `U` lies in `V`. -/
theorem le_iff_commutator_le :
    H ≤ chiefFactorCentralizer U V ↔ ⁅U, H⁆ ≤ V :=
  ⟨commutator_le_of_le, le_of_commutator_le⟩

end chiefFactorCentralizer

end OddOrder.GroupTheory
