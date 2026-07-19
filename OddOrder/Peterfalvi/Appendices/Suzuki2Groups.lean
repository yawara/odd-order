/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Basic
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AgemoLayers
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanAbelian
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanNormalAbelian
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanNormalCover
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanFrattiniConsequences
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanEndomorphismLift
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanIdempotents
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanIdempotentAction
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanIdempotentFamily
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanIdempotentCovariance
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanKernel
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanImageOrder
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanFinalCase
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.CenterInvolutions
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.CenterHomocyclic
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.KSubgroupOrbit
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ActualQuotientAction
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types

/-!
# Peterfalvi Appendix III: On Suzuki 2-Groups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, pp. 139--143.

This appendix recalls the quadratic-map model of Suzuki 2-groups and Higman's
classification.  Definition 1 is encoded by an honest regular automorphism
action; Higman's theorem (d)--(e) is represented by concrete invariant
two-summand data; and Definitions 2--3 are the concrete `TypeAData` and
`TypeBData` models re-exported from `Suzuki2Groups.Types`.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups
-- The declarations below predate the concrete type models and are retained for
-- compatibility only.  Their opaque `Prop` fields do not count as coverage and
-- must not be cited in new proofs.

variable {P V W F : Type*} [Group P]

/-- A proposition-valued carrier for a quadratic map over `F_2`. -/
structure QuadraticMapData where
  quadratic_law : Prop
  quadratic_law_holds : quadratic_law
  polar_bilinear : Prop
  polar_bilinear_holds : polar_bilinear

/-- **Peterfalvi Appendix III, Lemma 1(a)**: for a central extension with
elementary abelian quotient, the squaring map is quadratic. -/
theorem square_map_quadratic (Wsub : Subgroup P) (hcentral : Wsub ≤ Subgroup.center P)
    (hW : Prop) (hV : Prop) :
    hW → hV → Nonempty QuadraticMapData := by
  sorry

/-- **Peterfalvi Appendix III, Lemma 2**: the linear, bilinear, and quadratic maps
over a finite field of characteristic two have the stated automorphism bases. -/
structure FiniteFieldTwoMapBasis where
  linear_basis : Prop
  linear_basis_holds : linear_basis
  bilinear_basis : Prop
  bilinear_basis_holds : bilinear_basis
  quadratic_basis : Prop
  quadratic_basis_holds : quadratic_basis

/-- **Peterfalvi Appendix III, Definitions 2--3**: types A and B. -/
structure SuzukiTypeData (P : Type*) [Group P] where
  typeA : Prop
  typeB : Prop
  typeC_or_typeD : Prop

/-- **Peterfalvi Appendix III, Higman theorem**: the structural alternatives for
Suzuki 2-groups. -/
theorem higman_classification [Finite P] (hP : IsSuzuki2Group P) :
    ∃ data : SuzukiTypeData P, data.typeA ∨ data.typeB ∨ data.typeC_or_typeD := by
  sorry

/-- **Peterfalvi Appendix III, Proposition 1**: the group `B(n,1,epsilon)` admits
the field model `q(x) = x * conjugate x`. -/
theorem typeB_field_model (hB : Prop) :
    hB → ∃ fieldModel : Prop, fieldModel := by
  sorry

/-- **Peterfalvi Appendix III, Proposition 2**: the automorphism map of
`B(n,1)` is surjective with elementary abelian 2-kernel. -/
theorem typeB_automorphism_structure (hB : Prop) :
    hB → ∃ automorphismStructure : Prop, automorphismStructure := by
  sorry

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
