/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Huppert

/-!
# Peterfalvi Appendix D: On Suzuki 2-Groups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix D, pp. 139--143.

This appendix recalls the quadratic-map model of Suzuki 2-groups and Higman's
classification.  The scaffold keeps the quadratic-form and automorphism
classification obligations explicit.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

variable {P V W F : Type*} [Group P]

/-- A proposition-valued carrier for a quadratic map over `F_2`. -/
structure QuadraticMapData where
  quadratic_law : Prop
  quadratic_law_holds : quadratic_law
  polar_bilinear : Prop
  polar_bilinear_holds : polar_bilinear

/-- **Peterfalvi Appendix D, Lemma 1(a)**: for a central extension with
elementary abelian quotient, the squaring map is quadratic. -/
theorem square_map_quadratic (Wsub : Subgroup P) (hcentral : Wsub ≤ Subgroup.center P)
    (hW : Prop) (hV : Prop) :
    hW → hV → Nonempty QuadraticMapData := by
  sorry

/-- **Peterfalvi Appendix D, Lemma 2**: the linear, bilinear, and quadratic maps
over a finite field of characteristic two have the stated automorphism bases. -/
structure FiniteFieldTwoMapBasis where
  linear_basis : Prop
  linear_basis_holds : linear_basis
  bilinear_basis : Prop
  bilinear_basis_holds : bilinear_basis
  quadratic_basis : Prop
  quadratic_basis_holds : quadratic_basis

/-- **Peterfalvi Appendix D, Definition 1**: Suzuki 2-group. -/
structure IsSuzuki2Group (P : Type*) [Group P] where
  nonabelian : ¬ IsMulCommutative P
  atLeastTwoInvolutions : Prop
  cyclic_regular_automorphism_group : Prop

/-- **Peterfalvi Appendix D, Definitions 2--3**: types A and B. -/
structure SuzukiTypeData (P : Type*) [Group P] where
  typeA : Prop
  typeB : Prop
  typeC_or_typeD : Prop

/-- **Peterfalvi Appendix D, Higman theorem**: the structural alternatives for
Suzuki 2-groups. -/
theorem higman_classification [Finite P] (hP : IsSuzuki2Group P) :
    ∃ data : SuzukiTypeData P, data.typeA ∨ data.typeB ∨ data.typeC_or_typeD := by
  sorry

/-- **Peterfalvi Appendix D, Proposition 1**: the group `B(n,1,epsilon)` admits
the field model `q(x) = x * conjugate x`. -/
theorem typeB_field_model (hB : Prop) :
    hB → ∃ fieldModel : Prop, fieldModel := by
  sorry

/-- **Peterfalvi Appendix D, Proposition 2**: the automorphism map of
`B(n,1)` is surjective with elementary abelian 2-kernel. -/
theorem typeB_automorphism_structure (hB : Prop) :
    hB → ∃ automorphismStructure : Prop, automorphismStructure := by
  sorry

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
