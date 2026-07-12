/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Nilpotent groups with cyclic abelianization are cyclic

A nilpotent group `G` with `G/G'` cyclic is cyclic (mathcomp
`cyclic_nilpotent_quo_der1_cyclic`; consumed by the odd-order proof at Peterfalvi (11.9.c),
Coq `PFsection11.v`, `FTtype34_structure`).

The engine is the lower-central-series stabilization: writing `γ₂ = ⁅⊤,⊤⁆ = G'` and
`γ₃ = ⁅γ₂,⊤⁆`, the quotient `G/γ₃` has its commutator `γ₂/γ₃` central, and its central quotient
is an image of the cyclic `G/γ₂`, so `G/γ₃` is abelian
(`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`) — that is `γ₂ ≤ γ₃`, so the lower
central series stabilizes at `γ₂` and nilpotency forces `γ₂ = ⊥`.

## Main statements

* `OddOrder.GroupTheory.commutator_le_lowerCentralSeries_of_isCyclic_quotient`:
  `G/G'` cyclic forces `G' ≤ γ₃`.
* `OddOrder.GroupTheory.commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient`:
  `G` nilpotent and `G/G'` cyclic force `G' = ⊥` (so `G` is abelian).
* `OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_isCyclic_quotient`: `G` is then cyclic.
* `OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_ker_le_commutator`: the application form —
  a nilpotent `G` with a hom `f : G →* C` to a cyclic group with `ker f ≤ G'` is cyclic.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

open Subgroup
open scoped commutatorElement

/-- **The lower central series step under a cyclic abelianization**: if `G/G'` is cyclic then
`G' ≤ γ₃ = ⁅G', ⊤⁆`.  In `K = G/γ₃` the image of `G'` is central (its commutators with everything
land in `γ₃`), and `K` modulo that central image is the cyclic `G/G'`, so `K` is abelian
(`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`); evaluating on commutator generators
gives `G' ≤ γ₃`. -/
theorem commutator_le_lowerCentralSeries_of_isCyclic_quotient
    (hcyc : IsCyclic (G ⧸ commutator G)) :
    commutator G ≤ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  set γ₃ : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries 2 with hγ₃def
  haveI hnorm : γ₃.Normal := by rw [hγ₃def]; infer_instance
  have hγ₃le : γ₃ ≤ commutator G := by
    rw [hγ₃def, ← Subgroup.top_lowerCentralSeries_one]
    exact (⊤ : Subgroup G).lowerCentralSeries_antitone one_le_two
  -- the natural map `G/γ₃ →* G/G'`
  set f : G ⧸ γ₃ →* G ⧸ commutator G :=
    QuotientGroup.map γ₃ (commutator G) (MonoidHom.id G)
      (fun x hx => hγ₃le hx) with hfdef
  have hker : f.ker ≤ Subgroup.center (G ⧸ γ₃) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
    rw [MonoidHom.mem_ker, hfdef, QuotientGroup.map_mk, MonoidHom.id_apply,
      QuotientGroup.eq_one_iff] at hk
    -- `hk : x ∈ commutator G`; its commutators with everything lie in `γ₃ = ⁅G', ⊤⁆`
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have hcomm : ⁅x, y⁆ ∈ γ₃ := by
      rw [hγ₃def, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator
        (by rwa [Subgroup.top_lowerCentralSeries_one]) (Subgroup.mem_top y)
    have h1 : ⁅(↑x : G ⧸ γ₃), (↑y : G ⧸ γ₃)⁆ = 1 := by
      rw [show ((x : G ⧸ γ₃)) = QuotientGroup.mk' γ₃ x from rfl,
        show ((y : G ⧸ γ₃)) = QuotientGroup.mk' γ₃ y from rfl,
        ← map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hcomm
    exact (commutatorElement_eq_one_iff_commute.mp h1).symm.eq
  haveI hab : IsMulCommutative (G ⧸ γ₃) :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  -- evaluate on the commutator generators
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have h1 : QuotientGroup.mk' γ₃ ⁅g₁, g₂⁆
      = ⁅QuotientGroup.mk' γ₃ g₁, QuotientGroup.mk' γ₃ g₂⁆ :=
    map_commutatorElement (QuotientGroup.mk' γ₃) g₁ g₂
  have h2 : QuotientGroup.mk' γ₃ ⁅g₁, g₂⁆ = 1 := by
    rw [h1]
    exact commutatorElement_eq_one_iff_commute.mpr
      (hab.is_comm.comm (QuotientGroup.mk' γ₃ g₁) (QuotientGroup.mk' γ₃ g₂))
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

/-- **A nilpotent group with cyclic abelianization is abelian**: `G' = ⊥`.  The previous lemma
gives `γ₂ ≤ γ₃ = ⁅γ₂, ⊤⁆ ≤ γ₂`, so the lower central series stabilizes at `γ₂` from step `1` on;
nilpotency (`Subgroup.nilpotent_iff_lowerCentralSeries`) sends some term — hence `γ₂` — to `⊥`. -/
theorem commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient
    [hnil : Group.IsNilpotent G] (hcyc : IsCyclic (G ⧸ commutator G)) :
    commutator G = ⊥ := by
  have hstab : ∀ n, 1 ≤ n → (⊤ : Subgroup G).lowerCentralSeries n = commutator G := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge 0 m with hm | hm
      · -- `γ_{m+1} = ⁅γ_m, ⊤⁆ = ⁅γ₁, ⊤⁆ = γ₂ = commutator G` via stabilization
        refine le_antisymm ?_ ?_
        · rw [← Subgroup.top_lowerCentralSeries_one]
          exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
        · have h2 := commutator_le_lowerCentralSeries_of_isCyclic_quotient hcyc
          rw [Subgroup.lowerCentralSeries_succ, ih hm]
          rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
            Subgroup.top_lowerCentralSeries_one] at h2
          exact h2
      · -- `m = 0`: `γ₁ = commutator G`
        have hm0 : m = 0 := by omega
        subst hm0
        exact Subgroup.top_lowerCentralSeries_one
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- `γ₀ = ⊤ = ⊥`: the group is trivial
    rw [Subgroup.lowerCentralSeries_zero] at hn
    rw [eq_bot_iff, ← hn]
    exact le_top
  · rw [← hstab n hpos, hn]

/-- **A nilpotent group with cyclic abelianization is cyclic** (mathcomp
`cyclic_nilpotent_quo_der1_cyclic`): `G' = ⊥` collapses `G ≃* G/G'`, transporting the
cyclicity. -/
theorem isCyclic_of_isNilpotent_of_isCyclic_quotient
    [Group.IsNilpotent G] (hcyc : IsCyclic (G ⧸ commutator G)) : IsCyclic G := by
  have hbot := commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient hcyc
  -- `G ⧸ G' ≃* G ⧸ ⊥ ≃* G` (a `rw` at `hcyc` would break the quotient's instance motive)
  set e : (G ⧸ commutator G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := G))
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- **Application form**: a nilpotent group admitting a hom to a cyclic group with kernel inside
the commutator subgroup is cyclic.  `G/G'` is an image of `G/ker f ≃* range f ≤ C`, hence
cyclic, and `isCyclic_of_isNilpotent_of_isCyclic_quotient` applies. -/
theorem isCyclic_of_isNilpotent_of_ker_le_commutator {C : Type*} [Group C] [IsCyclic C]
    [Group.IsNilpotent G] (f : G →* C) (hker : f.ker ≤ commutator G) : IsCyclic G := by
  haveI hrange : IsCyclic ↥f.range :=
    isCyclic_of_injective f.range.subtype f.range.subtype_injective
  haveI hqker : IsCyclic (G ⧸ f.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).symm.surjective
  have hsurj : Function.Surjective
      (QuotientGroup.map f.ker (commutator G) (MonoidHom.id G) (fun x hx => hker hx)) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : G ⧸ f.ker), by rw [QuotientGroup.map_mk, MonoidHom.id_apply]⟩
  exact isCyclic_of_isNilpotent_of_isCyclic_quotient
    (isCyclic_of_surjective _ hsurj)

/-- A cyclic group is commutative, in `IsMulCommutative` form — the shape the type-III/IV
discriminator (`TypeIIIData.U_commutative`) consumes. -/
theorem isMulCommutative_of_isCyclic (h : IsCyclic G) : IsMulCommutative G := by
  letI : CommGroup G := IsCyclic.commGroup
  exact ⟨⟨mul_comm⟩⟩

end OddOrder.GroupTheory
