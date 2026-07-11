/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_MinimalSimpleBasic
import OddOrder.Peterfalvi.S08_YsetInner

/-!
# Peterfalvi (10.10) case (a): type-V Sibley coordinates

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§10, pp. 58-63 — Theorem (10.10) proof, first sentence ("If case (a) of Definition
(8.7) holds, then `S` is coherent by Theorem (6.8)").

Coordinate layer for the case-(a) branch of `typeV_forces_coherence` (issue 1021):
when a type-V maximal `M` satisfies the (8.7)(a) TI alternative, coherence of `S`
comes from Theorem (6.8) (`S08.sibleySetup_is_coherent`) applied to a
`SibleyDadeHypothesis` over `L = M`, `H = (M').subgroupOf M`.  This file aligns the
three coordinates of the support set —

* `sharpImage ((M').subgroupOf M)` (the Sibley/(6.8) coordinate),
* `sharpSubgroup (M')` (the ambient sharp set), and
* `typePA M data` (the §8/§10 `A(M)`)

— and upgrades the (8.7)(a) TI from its `N_G(H)`-relative statement to the
`M`-relative one the Sibley structure carries: `N_G(H) = M` by
maximality/simplicity (the (8.15) normalizer identification
`normalizer_support_eq`), using `M' = M_F = H` for type V (`U = ⊥`).
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Type V has `M' = M_F = data.H`** — for *any* `TypePData` witness `data` of the same
`M` (the kernel is the data-independent `maxNilpotentNormalHall M` via `H_eq`).  From
`M' = M_F ⊔ U` (`derivedInG_eq_fitting_sup_U`) and the type-V `U = ⊥`.  Book: the (10.10)
proof opens with "Set `H = M'`". -/
theorem TypeVData.derivedInG_eq_H {M : Subgroup G} (dV : TypeVData M)
    (data : TypePData M) : derivedInG M = data.H := by
  rw [dV.typeP.derivedInG_eq_fitting_sup_U, dV.U_eq_bot, sup_bot_eq, data.H_eq]

/-- **The Sibley support coordinate is the ambient sharp set**:
`sharpImage ((M').subgroupOf M) = (M')^#`.  Mapping `(M').subgroupOf M` back through
`M.subtype` recovers `M'` (as `M' ≤ M`), and `sharpImage`/`sharpSubgroup` both remove the
identity.  Type-V instance of the `S09.FrobeniusFamily.sharpImage_subgroupOf_eq` pattern. -/
theorem sharpImage_subgroupOf_derivedInG (M : Subgroup G) :
    OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)
      = sharpSubgroup (derivedInG M) := by
  rw [OddOrder.Peterfalvi.S08.sharpImage, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (show derivedInG M ≤ M from Subgroup.map_subtype_le _)]
  rfl

/-- **The set-normalizers of `H` and `H^# = H ∖ {1}` coincide**: conjugation fixes `1`, so
normalizing the punctured set is the same condition as normalizing the subgroup's carrier
set.  Bridges the (8.7)(a) TI bound `N_G(H)` with the sharp-set normalizer that the (8.15)
identification `normalizer_support_eq` computes. -/
theorem normalizer_sharpSubgroup (H : Subgroup G) :
    Subgroup.normalizer (sharpSubgroup H) = Subgroup.normalizer (H : Set G) := by
  have hconj1 : ∀ g x : G, g * x * g⁻¹ = 1 ↔ x = 1 := by
    intro g x
    constructor
    · intro h
      have hx : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [hx, h]
      group
    · rintro rfl
      group
  ext g
  simp only [Subgroup.mem_set_normalizer_iff, sharpSubgroup, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · intro h x
    by_cases hx1 : x = 1
    · subst hx1
      simp
    · constructor
      · intro hxH
        exact ((h x).mp ⟨hxH, hx1⟩).1
      · intro hgxH
        exact ((h x).mpr ⟨hgxH, fun he => hx1 ((hconj1 g x).mp he)⟩).1
  · intro h x
    exact and_congr (h x) (not_congr (hconj1 g x).symm)

/-- **`N_G((M')^#) = M`** for a maximal subgroup `M` of a minimal simple odd group carrying
type-`P` data: `(M')^#` is a nonempty (`W₂ ≤ H ≤ M'` nontrivial) `M`-invariant
(`le_normalizer_derivedInG`) subset of `M ∖ {1}`, so the (8.15) normalizer identification
`normalizer_support_eq` applies. -/
theorem normalizer_sharpSubgroup_derivedInG_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M) :
    Subgroup.normalizer (sharpSubgroup (derivedInG M)) = M := by
  refine OddOrder.Peterfalvi.S10.normalizer_support_eq hG hM ?_ ?_ ?_ ?_
  · exact fun x hx => (Subgroup.map_subtype_le _) hx.1
  · exact fun x hx => hx.2
  · obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.W2_nontrivial
    exact ⟨w.1, data.H_le ((inf_le_left : data.H ⊓ _ ≤ data.H) (data.W2_le w.2)),
      fun h => hw1 (Subtype.ext h)⟩
  · intro m x hm
    constructor
    · intro hmx
      have hback := OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M (inv_mem hm)) hmx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at hback
    · exact OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm)

/-- **Type-V case (a) in the `M`-coordinate**: under the (8.7)(a) TI alternative for a
type-`P` witness `data` (as produced by `TypeVData.alternative_transfer`), the support
`A(M) = (M')^# = H^#` is a TI-subset of `G` relative to `M` itself — the shape the
`SibleyDadeHypothesis.H_sharp_ti` field takes (via `sharpImage_subgroupOf_derivedInG`).
The (8.7)(a) bound `N_G(H)` collapses to `M` by `normalizer_sharpSubgroup_derivedInG_eq`. -/
theorem typePA_isTISubset_of_typeV_TI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (dV : TypeVData M) (data : TypePData M)
    (hTI : IsTISubset (sharpSubgroup data.H)
      (Subgroup.normalizer (data.H : Set G))) :
    IsTISubset (typePA M data) M := by
  have hHeq : derivedInG M = data.H := TypeVData.derivedInG_eq_H dV data
  have hN : Subgroup.normalizer (data.H : Set G) = M := by
    rw [← hHeq, ← normalizer_sharpSubgroup]
    exact normalizer_sharpSubgroup_derivedInG_eq hG hM data
  rw [typePA_eq_sharpSubgroup_derivedInG, hHeq]
  rw [hN] at hTI
  exact hTI

end OddOrder.Peterfalvi.S12
