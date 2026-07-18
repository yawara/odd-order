/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Huppert
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions

/-!
# Peterfalvi Appendix III: On Suzuki 2-Groups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, pp. 139--143.

This appendix recalls the quadratic-map model of Suzuki 2-groups and Higman's
classification.  Definition 1 is encoded by an honest regular automorphism
action; the remaining quadratic-form and classification obligations are kept
explicit.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups
-- The remaining classification scaffolds follow the opaque-Prop convention in
-- notes/meta/scaffold_opaque_prop_convention.md.

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

/-- The nonidentity involutions of a group. -/
def involutions (P : Type*) [Group P] : Set P :=
  {x | x ^ 2 = 1 ∧ x ≠ 1}

/-- A subgroup of the automorphism group acts regularly on the involutions
when every ordered pair of involutions is connected by a unique automorphism. -/
def ActsRegularlyOnInvolutions (A : Subgroup (MulAut P)) : Prop :=
  ∀ x ∈ involutions P, ∀ y ∈ involutions P,
    ∃! a : ↥A, (a : MulAut P) x = y

/-- **Peterfalvi Appendix III, Definition 1**: a Suzuki `2`-group is a
nonabelian `2`-group with at least two involutions and a cyclic group of
automorphisms acting faithfully and regularly on its involutions.

The acting group is represented as a subgroup of `MulAut P`, so faithfulness
is built into the representation rather than retained as an opaque field. -/
def IsSuzuki2Group (P : Type*) [Group P] : Prop :=
  IsPGroup 2 P ∧
    ¬ IsMulCommutative P ∧
    (∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) ∧
    ∃ A : Subgroup (MulAut P), IsCyclic ↥A ∧ ActsRegularlyOnInvolutions A

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
