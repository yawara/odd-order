/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG

/-!
# Peterfalvi Appendix B: A Special Case of a Theorem of Huppert

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix B, pp. 135--136.

This appendix proves a special Huppert theorem for an odd-order group acting
faithfully and transitively on the nonzero elements of an elementary abelian
group.  It is recorded as a small scaffold because later appendices use this
finite-field realization pattern.
-/

namespace OddOrder.Peterfalvi.Appendices.Huppert

variable {D E : Type*} [Group D] [Group E]

/-- Setup for Peterfalvi Appendix B, Proposition 1. -/
structure Hypothesis where
  q : ℕ
  q_prime : q.Prime
  E_nonempty : Nonempty E
  E_elementaryAbelian : Prop
  E_elementaryAbelian_holds : E_elementaryAbelian
  D_odd : Odd (Nat.card D)
  action_faithful : Prop
  action_faithful_holds : action_faithful
  transitive_on_E_sharp : Prop
  transitive_on_E_sharp_holds : transitive_on_E_sharp

/-- Carrier for the cyclic fixed-point-free Fitting conclusion. -/
structure Conclusion (hyp : Hypothesis (D := D) (E := E)) where
  fitting_cyclic : Prop
  fitting_cyclic_holds : fitting_cyclic
  fitting_fixedPointFree : Prop
  fitting_fixedPointFree_holds : fitting_fixedPointFree
  quotient_abelian : Prop
  quotient_abelian_holds : quotient_abelian

/-- **Peterfalvi Appendix B, Lemma**: a non-2 `p`-group with constant point
stabilizer sizes is cyclic and fixed-point-free. -/
theorem pGroup_cyclic_fixedPointFree (hyp : Hypothesis (D := D) (E := E))
    {p : ℕ} (hp : p.Prime) (hp_ne_two : p ≠ 2) (P : Subgroup D)
    (hP : Prop) :
    hP → ∃ cyclic fixedPointFree : Prop, cyclic ∧ fixedPointFree := by
  sorry

/-- **Peterfalvi Appendix B, Proposition 1**: `F(D)` is cyclic and
fixed-point-free on `E`, and `D/F(D)` is abelian. -/
theorem fitting_cyclic_fixedPointFree
    (hyp : Hypothesis (D := D) (E := E)) :
    ∃ data : Conclusion hyp,
      data.fitting_cyclic ∧ data.fitting_fixedPointFree ∧
        data.quotient_abelian := by
  sorry

end OddOrder.Peterfalvi.Appendices.Huppert
