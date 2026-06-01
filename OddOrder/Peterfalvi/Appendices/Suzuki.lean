/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG

/-!
# Peterfalvi Appendix A: A Theorem of Suzuki

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix A, pp. 97--134.

This appendix reprints Suzuki's theorem on a class of doubly transitive groups.
It is not on the main Feit--Thompson route, but it supplies the surrounding
classification material used in the historical proof.  The scaffold records the
global hypotheses (A1)--(A3), Theorem A, and the chapter-level reductions.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

variable {G Ω : Type*} [Group G]

/-! ## Hypotheses (A1)--(A3) and Theorem A -/

/-- **Peterfalvi App.A (A1)--(A3)**: Suzuki's doubly transitive setup. -/
structure Hypothesis where
  H : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  Omega_nonempty : Nonempty Ω
  t : G
  action_on_Omega : Prop
  action_on_Omega_holds : action_on_Omega
  doubly_transitive : Prop
  doubly_transitive_holds : doubly_transitive
  H_stabilizer : Prop
  H_stabilizer_holds : H_stabilizer
  t_involution : t ^ 2 = 1 ∧ t ≠ 1
  t_not_mem_H : t ∉ H
  D_eq_H_inter_Ht : Prop
  D_eq_H_inter_Ht_holds : D_eq_H_inter_Ht
  H_eq_Q_semidirect_D : Prop
  H_eq_Q_semidirect_D_holds : H_eq_Q_semidirect_D
  Q_even : Even (Nat.card ↥Q)
  D_odd : Odd (Nat.card ↥D)
  faithful_action : Prop
  faithful_action_holds : faithful_action
  two_rank_atLeast_two : Prop
  two_rank_atLeast_two_holds : two_rank_atLeast_two

/-- Conclusion of Suzuki's Theorem A: an odd-index normal subgroup is one of
`PSL(2,q)`, `Sz(q)`, or `PSU(3,q)`. -/
structure Conclusion (hyp : Hypothesis (G := G) (Ω := Ω)) where
  L : Subgroup G
  L_normal : L.Normal
  quotient_odd : Prop
  quotient_odd_holds : quotient_odd
  q : ℕ
  q_power_of_two : Prop
  q_power_of_two_holds : q_power_of_two
  q_gt_two : 2 < q
  classification : Prop
  classification_holds : classification
  standard_action : Prop
  standard_action_holds : standard_action

/-- **Peterfalvi App.A, Theorem A**: Suzuki's classification conclusion. -/
theorem theoremA [Finite G] (hyp : Hypothesis (G := G) (Ω := Ω)) :
    ∃ data : Conclusion hyp, data.quotient_odd ∧ data.classification := by
  sorry

/-! ## Chapter I: general structure -/

/-- Data produced in Chapter I: canonical form, the distinguished involution,
and the subgroups `K`, `V`, and `W`. -/
structure GeneralStructureData (hyp : Hypothesis (G := G) (Ω := Ω)) where
  K : Subgroup G
  V : Subgroup G
  W : Subgroup G
  distinguishedInvolution : G
  canonical_form : Prop
  canonical_form_holds : canonical_form
  K_cyclic_normal : Prop
  K_cyclic_normal_holds : K_cyclic_normal
  Q_nilpotent : Prop
  Q_nilpotent_holds : Q_nilpotent
  V_eq_centralizer : Prop
  V_eq_centralizer_holds : V_eq_centralizer
  nearField_model : Prop
  nearField_model_holds : nearField_model

/-- **Peterfalvi App.A, Chapter I**: the basic structural package for
Suzuki's setup. -/
theorem general_structure [Finite G] (hyp : Hypothesis (G := G) (Ω := Ω)) :
    ∃ data : GeneralStructureData hyp,
      data.canonical_form ∧ data.K_cyclic_normal ∧
        data.Q_nilpotent ∧ data.nearField_model := by
  sorry

/-! ## Chapters II--IV: the three reductions -/

/-- **Peterfalvi App.A, Chapter II (B1)**: the first case, where a prime-order
subgroup of `V` has centralizer of 2-rank one. -/
structure FirstCaseHypothesis (hyp : Hypothesis (G := G) (Ω := Ω)) where
  P : Subgroup G
  P_prime_order : Prop
  P_prime_order_holds : P_prime_order
  P_le_V : Prop
  P_le_V_holds : P_le_V
  centralizer_two_rank_one : Prop
  centralizer_two_rank_one_holds : centralizer_two_rank_one

/-- **Peterfalvi App.A, Theorem B**: under the first-case hypothesis, Theorem A
already holds. -/
theorem first_case_theorem [Finite G] (hyp : Hypothesis (G := G) (Ω := Ω))
    (caseB : FirstCaseHypothesis hyp) :
    ∃ data : Conclusion hyp, data.classification := by
  sorry

/-- **Peterfalvi App.A, Chapter III**: structure of `H`, in particular the
reduction showing `Q` is a 2-group and the Suzuki 2-group alternatives. -/
structure StructureOfHData (hyp : Hypothesis (G := G) (Ω := Ω)) where
  Q_is_twoGroup : Prop
  Q_is_twoGroup_holds : Q_is_twoGroup
  sylow_two_structure : Prop
  sylow_two_structure_holds : sylow_two_structure
  suzuki_type_split : Prop
  suzuki_type_split_holds : suzuki_type_split

/-- **Peterfalvi App.A, Chapter III**: the structural reduction for `H`. -/
theorem structure_of_H [Finite G] (hyp : Hypothesis (G := G) (Ω := Ω)) :
    ∃ data : StructureOfHData hyp,
      data.Q_is_twoGroup ∧ data.suzuki_type_split := by
  sorry

/-- **Peterfalvi App.A, Chapter IV**: the explicit calculation determining the
map `f` and yielding the `PSU(3,q)` conclusion. -/
structure PSUCharacterizationData (hyp : Hypothesis (G := G) (Ω := Ω)) where
  maps_f_g_h : Prop
  maps_f_g_h_holds : maps_f_g_h
  theta_eq_one : Prop
  theta_eq_one_holds : theta_eq_one
  f_formula : Prop
  f_formula_holds : f_formula
  psu_or_pgu_conclusion : Prop
  psu_or_pgu_conclusion_holds : psu_or_pgu_conclusion

/-- **Peterfalvi App.A, Chapter IV**: the final explicit computation for
`PSU(3,q)`. -/
theorem psu_characterization [Finite G]
    (hyp : Hypothesis (G := G) (Ω := Ω)) :
    ∃ data : PSUCharacterizationData hyp,
      data.theta_eq_one ∧ data.f_formula ∧ data.psu_or_pgu_conclusion := by
  sorry

end OddOrder.Peterfalvi.Appendices.Suzuki
