/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki

/-!
# Peterfalvi Appendix C: On Near-Fields

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix C, pp. 137--138.

The appendix uses finite near-fields to describe the 2-rank one case of the
Suzuki theorem and records the special Zassenhaus classification needed there.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

variable {G Ω F : Type*} [Group G]

/-- A lightweight carrier for finite near-field structure.  The algebraic laws
are proposition fields until a reusable near-field API is introduced. -/
structure FiniteNearField where
  carrier_nonempty : Nonempty F
  finite : Prop
  finite_holds : finite
  additive_group : Prop
  additive_group_holds : additive_group
  multiplicative_group : Prop
  multiplicative_group_holds : multiplicative_group
  right_distrib : Prop
  right_distrib_holds : right_distrib

/-- **Peterfalvi Appendix C, Proposition 1**: a 2-rank one group satisfying
Suzuki hypotheses (A1)--(A2) is an affine group over a finite near-field. -/
structure RankOneNearFieldData
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω)) where
  nearField : FiniteNearField (F := F)
  Sigma : Type*
  affine_model : Prop
  affine_model_holds : affine_model
  Q_identification : Prop
  Q_identification_holds : Q_identification
  D_identification : Prop
  D_identification_holds : D_identification
  unique_involution_in_H : Prop
  unique_involution_in_H_holds : unique_involution_in_H

/-- **Peterfalvi Appendix C, Proposition 1**. -/
theorem rankOne_affine_nearField [Finite G]
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω))
    (two_rank_one : Prop) :
    two_rank_one → ∃ data : RankOneNearFieldData (F := F) hyp,
      data.affine_model := by
  sorry

/-- **Peterfalvi Appendix C, Proposition 2**: a finite near-field whose
multiplicative group has a cyclic subgroup of index two is either a field or the
exceptional near-field `F_{r^2,2}`. -/
theorem cyclic_index_two_nearField_classification
    (nearField : FiniteNearField (F := F)) (cyclic_index_two : Prop) :
    cyclic_index_two → ∃ classification : Prop, classification := by
  sorry

end OddOrder.Peterfalvi.Appendices.NearFields
