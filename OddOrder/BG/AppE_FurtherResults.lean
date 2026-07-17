/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults

/-!
# BG Appendix E: Further Results of Feit and Thompson

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 157--164.

Appendix E records later Feit-Thompson and Philip Hall results.  These results
are not used in the main BG proof, but they are useful historical and technical
extensions around regular operator actions on `p`-groups.
-/

namespace OddOrder.BG.AppE
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

variable {G R B : Type*} [Group G] [Group R] [Group B]

/-! ## Hall collection and regular p-groups -/

/-- Data for the Hall commutator collection formula in BG Theorem E.1. -/
structure HallCollectionData (G : Type*) [Group G] (n : ℕ) where
  positive_n : 0 < n
  lowerCentralSeries_formula : Prop
  lowerCentralSeries_formula_holds : lowerCentralSeries_formula
  binomial_exponents : Prop
  binomial_exponents_holds : binomial_exponents

/-- **BG Theorem E.1**: Hall's collection formula along the lower central
series. -/
theorem hall_collection_formula (n : ℕ) :
    ∃ data : HallCollectionData G n,
      data.lowerCentralSeries_formula ∧ data.binomial_exponents := by
  sorry

/-- Data for the regular `p`-group consequences in BG Proposition E.2. -/
structure RegularPGroupData (R : Type*) [Group R] (p : ℕ) where
  p_odd_prime : p.Prime ∧ p ≠ 2
  nilpotenceClass_le : Prop
  nilpotenceClass_le_holds : nilpotenceClass_le
  omegaOne_exponent : Prop
  omegaOne_exponent_holds : omegaOne_exponent
  pPowerMap_hom : Prop
  pPowerMap_hom_holds : pPowerMap_hom

/-- **BG Proposition E.2**: if a `p`-group has nilpotence class at most
`p - 1`, then `Omega_1` has exponent `1` or `p`, and the `p`-power map is a
homomorphism under the derived-subgroup hypothesis. -/
theorem regular_pGroup_power_map (p : ℕ) :
    ∃ data : RegularPGroupData R p,
      data.omegaOne_exponent ∧ data.pPowerMap_hom := by
  sorry

/-! ## Feit-Thompson 1991 operator results -/

/-- The standing setup for BG Theorem E.3.  The operator action is kept as
named proposition fields until the final automorphism-action API is fixed. -/
structure OperatorHypothesis (R B : Type*) [Group R] [Group B] where
  p : ℕ
  q : ℕ
  R0 : Subgroup R
  R1 : Subgroup R
  A : Subgroup B
  odd_distinct_primes : Prop
  odd_distinct_primes_holds : odd_distinct_primes
  R_pGroup : Prop
  R_pGroup_holds : R_pGroup
  p_not_dvd_B : Prop
  p_not_dvd_B_holds : p_not_dvd_B
  A_card_eq_q : Prop
  A_card_eq_q_holds : A_card_eq_q
  R0_card_eq_p : Prop
  R0_card_eq_p_holds : R0_card_eq_p
  R1_cyclic : Prop
  R1_cyclic_holds : R1_cyclic
  centralizer_split : Prop
  centralizer_split_holds : centralizer_split
  A_fixes_R0 : Prop
  A_fixes_R0_holds : A_fixes_R0
  A_regular_on_R : Prop
  A_regular_on_R_holds : A_regular_on_R

/-- Conclusion data for BG Theorem E.3. -/
structure OperatorBoundData (hyp : OperatorHypothesis R B) where
  q_dvd_half_p_sub_one : Prop
  q_dvd_half_p_sub_one_holds : q_dvd_half_p_sub_one
  omegaOne_exponent_p : Prop
  omegaOne_exponent_p_holds : omegaOne_exponent_p
  R0_not_le_omegaOne_commutator : Prop
  R0_not_le_omegaOne_commutator_holds : R0_not_le_omegaOne_commutator
  omegaOne_abelianization_card : Prop
  omegaOne_abelianization_card_holds : omegaOne_abelianization_card
  omegaOne_card_bound : Prop
  omegaOne_card_bound_holds : omegaOne_card_bound
  Frattini_fixing_descent : Prop
  Frattini_fixing_descent_holds : Frattini_fixing_descent

/-- **BG Theorem E.3**: the Feit-Thompson regular-operator bound. -/
theorem regular_operator_bound (hyp : OperatorHypothesis R B) :
    ∃ data : OperatorBoundData hyp,
      data.omegaOne_exponent_p ∧ data.omegaOne_card_bound ∧
        data.Frattini_fixing_descent := by
  sorry

/-- Conclusion data for BG Proposition E.4. -/
structure CentralizerUpperCenterData (hyp : OperatorHypothesis R B) where
  omegaOne_large : Prop
  omegaOne_large_holds : omegaOne_large
  B_regular_on_R : Prop
  B_regular_on_R_holds : B_regular_on_R
  B_not_fix_R0 : Prop
  B_not_fix_R0_holds : B_not_fix_R0
  centralizer_Z2_abelian : Prop
  centralizer_Z2_abelian_holds : centralizer_Z2_abelian
  centralizer_Z2_index_p : Prop
  centralizer_Z2_index_p_holds : centralizer_Z2_index_p

/-- **BG Proposition E.4**: under the Theorem E.3 hypotheses and the large
`Omega_1` condition, `C_S(Z_2(S))` is abelian of index `p` in `S`. -/
theorem centralizer_upperCenter_abelian_index
    (hyp : OperatorHypothesis R B) :
    ∃ data : CentralizerUpperCenterData hyp,
      data.centralizer_Z2_abelian ∧ data.centralizer_Z2_index_p := by
  sorry

/-! ## Maximal subgroup application -/

/-- The maximal-subgroup setup for BG Corollary E.5. -/
structure MaximalApplicationHypothesis (G : Type*) [Group G] where
  M : Subgroup G
  N : Subgroup G
  x : G
  p : ℕ
  M_maximal : Prop
  M_maximal_holds : M_maximal
  x_mem_Msigma : Prop
  x_mem_Msigma_holds : x_mem_Msigma
  x_prime_order : Prop
  x_prime_order_holds : x_prime_order
  centralizer_not_le_M : Prop
  centralizer_not_le_M_holds : centralizer_not_le_M
  N_contains_centralizer : Prop
  N_contains_centralizer_holds : N_contains_centralizer
  N_not_F_type : Prop
  N_not_F_type_holds : N_not_F_type
  abelianization_prime_or_no_index_p : Prop
  abelianization_prime_or_no_index_p_holds : abelianization_prime_or_no_index_p

/-- Conclusion data for BG Corollary E.5. -/
structure TypeClassificationData
    (hyp : MaximalApplicationHypothesis (G := G)) where
  all_maximal_typeI_or_typeII : Prop
  all_maximal_typeI_or_typeII_holds : all_maximal_typeI_or_typeII

/-- **BG Corollary E.5**: the Appendix E operator results imply a Type I/II
maximal-subgroup classification under the stated additional hypotheses. -/
theorem maximalSubgroups_typeI_or_typeII
    (hyp : MaximalApplicationHypothesis (G := G)) :
    ∃ data : TypeClassificationData hyp,
      data.all_maximal_typeI_or_typeII := by
  sorry

end OddOrder.BG.AppE
