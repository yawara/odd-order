/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppB_Thm62
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity

/-!
# BG Appendix D: CN-Groups of Odd Order

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--156.

Appendix D is a guide to the Feit-Hall-Thompson CN-theorem proof.  It is not
part of the main BG-to-Peterfalvi proof path, but it records two reusable
local-analysis consequences for a minimal simple CN-group of odd order.
-/

namespace OddOrder.BG.AppD
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ## CN-groups -/

/-- A `CN`-group is a group in which every nonidentity element has nilpotent
centralizer. -/
def IsCNGroup (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({x} : Set G))

/-- The standing hypothesis for BG Appendix D.  The minimal-simple condition is
kept as a named proposition until the global minimal-counterexample API is
standardized. -/
structure MinimalSimpleCNHypothesis where
  cn : IsCNGroup G
  odd_order : Odd (Nat.card G)
  minimal_simple : Prop
  minimal_simple_holds : minimal_simple
  nonsolvable : Prop
  nonsolvable_holds : nonsolvable

/-! ## Appendix D lemmas -/

/-- **BG Lemma D.1**: in a minimal simple CN-group of odd order, Sylow
`p`-subgroups form a TI family. -/
theorem sylow_eq_of_nontrivial_inter [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : MinimalSimpleCNHypothesis (G := G)) (P Q : Sylow p G)
    (hinter : ((P : Subgroup G) ⊓ (Q : Subgroup G)) ≠ ⊥) :
    (P : Subgroup G) = Q := by
  sorry

/-- **BG Lemma D.2**: for a nontrivial Sylow subgroup `P`, the focal subgroup
argument places `P` inside the derived subgroup of its normalizer. -/
theorem sylow_le_commutator_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : MinimalSimpleCNHypothesis (G := G)) (P : Sylow p G)
    (hPne : (P : Subgroup G) ≠ ⊥) :
    (P : Subgroup G) ≤
      derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  sorry

/-- The Appendix D reduction package: Lemmas D.1 and D.2 are the local-analysis
inputs that replace long passages of Gorenstein's CN-theorem proof. -/
structure CNTheoremReductionData
    (hyp : MinimalSimpleCNHypothesis (G := G)) where
  sylowTI : Prop
  sylowTI_holds : sylowTI
  focalControl : Prop
  focalControl_holds : focalControl
  threeStepExclusion : Prop
  threeStepExclusion_holds : threeStepExclusion

/-- **BG Appendix D guide**: the CN-theorem local-analysis reduction. -/
theorem cnTheorem_reduction [Finite G]
    (hyp : MinimalSimpleCNHypothesis (G := G)) :
    ∃ data : CNTheoremReductionData hyp,
      data.sylowTI ∧ data.focalControl ∧ data.threeStepExclusion := by
  sorry

end OddOrder.BG.AppD
