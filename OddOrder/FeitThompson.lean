import OddOrder.BG.AppC_FinalContradiction

/-!
# Feit-Thompson Theorem

This file is the top-level scaffold for Phase 4 of the project.  The full theorem
is the usual odd-order theorem: every finite group of odd order is solvable.

The current bridge records the final contradiction route already scaffolded in
BG Appendix C and Peterfalvi Section 16:

* `BG.IsMinimalSimpleOdd G` packages the minimal counterexample hypotheses.
* `Peterfalvi.S16.Hypothesis` packages the Section 16 field-normalizer setup.
* `BG.AppC.final_contradiction` closes that setup by combining Peterfalvi
  Section 16 with BG Appendix C.
-/

namespace OddOrder

/-- **Feit-Thompson theorem**: every finite group of odd order is solvable. -/
theorem feitThompson {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    IsSolvable G := by
  sorry

/-- The currently scaffolded final-contradiction bridge: once the BG minimal
counterexample and Peterfalvi Section 16 hypotheses are constructed, BG Appendix C
closes the contradiction. -/
theorem noMinimalSimpleOdd_of_section16 {G : Type*} [Group G] [Finite G]
    (hG : BG.IsMinimalSimpleOdd G)
    (hyp : Peterfalvi.S16.Hypothesis (G := G)) :
    False :=
  BG.AppC.final_contradiction hG hyp

end OddOrder
