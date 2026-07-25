/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFourteenSylow
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.NonsplitTorus

/-!
# Peterfalvi Part II, Ch. II, step (15): the cyclic subgroup `L` of order `9`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (15), pp. 113-114.

> **(15)** There is a subgroup `L` of `R₁` which is cyclic of order `9`, inverted by
> `s`, normalized by `V` and centralized by `W` but not by `P`. …

The subgroup is `L = C_G(st) ∩ ⟨Q₀, K, t⟩`, and Peterfalvi reads "cyclic of order `9`"
off the isomorphism `⟨Q₀, K, t⟩ ≅ PSL(2, 8)` of Ch. I §3, Lemma 4.  This file supplies
that reading: by the nonsplit torus construction the Sylow `3`-subgroups of `PSL(2, 8)`
are cyclic of order `9`, and one of them centralizes `st`; conversely `C_G(st)` is a
`3`-group by (13), so the intersection has order dividing `9`.
-/

set_option autoImplicit false

open OddOrder.GroupTheory.ProjectiveSpecialLinear

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **`L = C_G(st) ⊓ ⟨Q₀, K, t⟩` is cyclic of order `9`** ((15), p. 113).

`⟨Q₀, K, t⟩ ≅ PSL(2, 8)` has order `504`, and its Sylow `3`-subgroups are cyclic of
order `9` (the nonsplit torus).  The one containing `st` is abelian, hence centralizes
`st`, so it lies inside `L`; and `L` is a `3`-group by (13), so `|L|` divides `9`. -/
theorem isCyclic_and_card_centralizer_inf_orderThreeGeneratedSubgroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    IsCyclic ↥(Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup)
      ∧ Nat.card ↥(Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup) = 9 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  set z : G := fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t with hz_def
  set L₀ : Subgroup G := fc.toHypothesis.orderThreeGeneratedSubgroup with hL₀_def
  have hstord : orderOf z = 3 := by
    rw [hz_def, fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `V ≠ 1`
  have hV : fc.toHypothesis.V ≠ ⊥ := by
    intro h
    have hcard := fc.card_V_eq_card_P_mul_card_W
    rw [h, Subgroup.card_bot, fc.card_P, hp3] at hcard
    have hWpos : 0 < Nat.card ↥fc.toHypothesis.W := Nat.card_pos
    omega
  -- `⟨Q₀, K, t⟩ ≅ PSL(2, F')` with `|F'| = |Q₀| = 8`
  obtain ⟨F', _, _, _, hcardF', ⟨e⟩⟩ :=
    fc.toHypothesis.exists_orderThreeGeneratedSubgroup_mulEquiv_psl2 hstord hV ind
  have hF'8 : Nat.card F' = 8 := by
    rw [hcardF', fc.card_Q0_eq_two_pow, hp3]
    norm_num
  have hL₀card : Nat.card ↥L₀ = 504 := by
    rw [hL₀_def, Nat.card_congr e.toEquiv]
    exact natCard_projectiveSpecialLinearGroup_eq_of_card_eq_eight F' hF'8
  -- `st ∈ ⟨Q₀, K, t⟩`
  have hsQ0 : fc.toHypothesis.distinguishedInvolution ∈ fc.toHypothesis.Q0 :=
    ⟨fc.toHypothesis.distinguishedInvolution_sq,
      fc.toHypothesis.distinguishedInvolution_mem_H⟩
  have hzL₀ : z ∈ L₀ := Subgroup.mul_mem _
    (fc.toHypothesis.orderThree_Q0_le hsQ0) fc.toHypothesis.orderThree_t_mem
  -- a cyclic Sylow `3`-subgroup of `⟨Q₀, K, t⟩` containing `st`
  have hcyc9 : ∃ C : Subgroup ↥L₀, IsCyclic ↥C ∧ Nat.card ↥C = 9 :=
    exists_isCyclic_card_nine_of_mulEquiv e.symm
      (exists_isCyclic_card_nine_projectiveSpecialLinearGroup F' hF'8)
  have hxord : orderOf (⟨z, hzL₀⟩ : ↥L₀) = 3 := by
    rw [Subgroup.orderOf_mk]; exact hstord
  obtain ⟨S, hzS, hScyc, hScard⟩ :=
    exists_isCyclic_card_nine_mem hL₀card hcyc9 hxord
  -- transport `S` to a subgroup of `G`
  set S' : Subgroup G := S.map L₀.subtype with hS'_def
  have hS'card : Nat.card ↥S' = 9 := by
    rw [hS'_def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hScard
  have hS'cyc : IsCyclic ↥S' := by
    rw [hS'_def]
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective S L₀.subtype (Subgroup.subtype_injective _)).surjective
  -- `S'` is abelian and contains `st`, so it centralizes `st`; and `S' ≤ L₀`
  haveI : IsMulCommutative ↥S' := IsCyclic.isMulCommutative
  have hS'le : S' ≤ Subgroup.centralizer ({z} : Set G) ⊓ L₀ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, y.2⟩
    have hzS' : (⟨z, hzL₀⟩ : ↥L₀) ∈ S := hzS
    have := ‹IsMulCommutative ↥S'›.is_comm.comm
      (⟨L₀.subtype y, ⟨y, hy, rfl⟩⟩ : ↥S')
      (⟨z, ⟨⟨z, hzL₀⟩, hzS', rfl⟩⟩ : ↥S')
    exact congrArg Subtype.val this
  -- `L` is a `3`-group by (13), so `|L|` divides `9`
  have hcen : Subgroup.centralizer
      ((Subgroup.zpowers z : Subgroup G) : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hLp : IsPGroup 3 ↥(Subgroup.centralizer ({z} : Set G) ⊓ L₀) := by
    refine IsPGroup.to_le ?_ (inf_le_left)
    rw [← hcen]
    exact fc.isPGroup_three_centralizer_Z₁ model ind hB2
  have hLdvd : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ L₀) ∣ 504 := by
    rw [← hL₀card]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hLnine := card_dvd_nine_of_isPGroup_three hLp hLdvd
  have hLeq : Subgroup.centralizer ({z} : Set G) ⊓ L₀ = S' :=
    (Subgroup.eq_of_le_of_card_ge hS'le
      (by rw [hS'card]; exact Nat.le_of_dvd (by norm_num) hLnine)).symm
  exact ⟨hLeq ▸ hS'cyc, hLeq ▸ hS'card⟩

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
