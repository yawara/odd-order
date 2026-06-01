/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups

/-!
# Peterfalvi Appendix E: The Feit-Sibley Theorem

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix E, pp. 144--150.

This appendix proves the odd-order Feit--Sibley coherence theorem used in the
Suzuki appendix.  The main Peterfalvi proof already has a coherence API in
Sections 7--8; this file records the appendix-specific induction-isometry setup.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **Peterfalvi Appendix E, hypotheses**: `H = Q semidirect D`, coprime
orders, trivial intersections for conjugates of `Q`, and the character family
`S` induced from `Q`. -/
structure Hypothesis where
  H : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  Q1 : Subgroup G
  S : Subgroup G
  H_eq_Q_semidirect_D : Prop
  H_eq_Q_semidirect_D_holds : H_eq_Q_semidirect_D
  coprime_Q_D : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥D)
  Q_trivial_intersections : Prop
  Q_trivial_intersections_holds : Q_trivial_intersections
  Q_eq_S_prod_Q1 : Prop
  Q_eq_S_prod_Q1_holds : Q_eq_S_prod_Q1
  D_fixedPointFree_on_Q1 : Prop
  D_fixedPointFree_on_Q1_holds : D_fixedPointFree_on_Q1
  Sset : Set (ClassFunction ↥H ℂ)
  A : Set ↥H
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥H G
  d : ℕ
  d_eq_card_D : d = Nat.card ↥D

/-- **Peterfalvi Appendix E, Lemma 1**: two sufficient criteria for coherence. -/
theorem coherence_adjoin_or_equal_degree [Finite G]
    (hyp : Hypothesis (G := G)) :
    ∃ adjoinCriterion equalDegreeCriterion : Prop,
      adjoinCriterion ∧ equalDegreeCriterion := by
  sorry

/-- **Peterfalvi Appendix E, Lemma 2**: the induced characters from `Q` form the
family `S`, induction is an isometry on the reduced lattice, and the odd case has
no real characters. -/
structure InductionIsometryData (hyp : Hypothesis (G := G)) where
  induced_family_formula : Prop
  induced_family_formula_holds : induced_family_formula
  induction_isometry : Prop
  induction_isometry_holds : induction_isometry
  no_real_characters : Prop
  no_real_characters_holds : no_real_characters

/-- **Peterfalvi Appendix E, Lemma 2**. -/
theorem induction_isometry [Finite G] (hyp : Hypothesis (G := G)) :
    ∃ data : InductionIsometryData hyp,
      data.induced_family_formula ∧ data.induction_isometry ∧
        data.no_real_characters := by
  sorry

/-- **Peterfalvi Appendix E, Theorem**: if `d` is odd, the family `S` is
coherent with respect to the induction isometry. -/
theorem feit_sibley_coherence [Fintype G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    [Invertible (Nat.card G : ℂ)] (hd : Odd hyp.d) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  sorry

end OddOrder.Peterfalvi.Appendices.FeitSibley
