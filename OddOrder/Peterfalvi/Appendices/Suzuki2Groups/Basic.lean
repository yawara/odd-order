/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup

/-!
# Peterfalvi Appendix III: Suzuki 2-group definition

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Definition 1, p. 139.

This leaf contains the definition-level API shared by the Appendix III
classification and its Part II applications.  Keeping it independent of the
classification hub lets individual structural lemmas import the definition
without importing the full appendix.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

variable {P : Type*} [Group P]

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

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
