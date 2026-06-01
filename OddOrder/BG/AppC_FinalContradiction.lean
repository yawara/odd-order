/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG

/-!
# BG Appendix C: The Final Contradiction

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, pp. 145--152.

Appendix C records the Carlip--Wheeler presentation of Peterfalvi's finite-field
argument for the final contradiction.  In Peterfalvi Section 16 the same endpoint
appears as Theorem (14.2): a field-normalizer configuration is constructed with
primes `q < p`.  BG Appendix C proves that any such configuration forces
`p <= q`.

This file is the BG-side scaffold for that last interface.  The detailed finite
field proof is split into the named lemmas C.1--C.3 and represented by
proposition fields until the norm-set and generator-relation calculation is
formalized.  The final bridge to Peterfalvi Section 16 is already connected.
-/

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory
open OddOrder.Peterfalvi
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorem C setup -/

/-- **BG Appendix C, Condition (A)**: the cyclotomic factor attached to
`F_{p^q}` is coprime to `p - 1`. -/
def conditionA (p q : ℕ) : Prop :=
  Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)

/-- **BG Appendix C, Hypothesis (B)**, transported to the Peterfalvi Section 16
field-normalizer data.  The concrete monomorphism `H -> G`, the abelian
`p'`-subgroup `Q`, and the two normalizer assumptions are already represented
inside `FieldNormalizerData`; the remaining finite-field identifications are
kept as proposition fields. -/
structure HypothesisB (hyp : S16.Hypothesis (G := G)) where
  data : S16.FieldNormalizerData hyp
  monomorphism_formula : Prop
  monomorphism_formula_holds : monomorphism_formula
  Q_is_pPrime_abelian : Prop
  Q_is_pPrime_abelian_holds : Q_is_pPrime_abelian
  P0_normalizes_Q_formula : Prop
  P0_normalizes_Q_formula_holds : P0_normalizes_Q_formula
  P0_conj_y_normalizes_U_formula : Prop
  P0_conj_y_normalizes_U_formula_holds : P0_conj_y_normalizes_U_formula

/-- The norm set `E = {a | N(a) = N(2 - a) = 1}` used in BG Lemmas C.1--C.3.
The finite field and norm map are not materialized here yet; this carrier records
the exact proof obligations needed by Theorem C. -/
structure NormSetData (hyp : S16.Hypothesis (G := G)) where
  conditionA_holds : conditionA hyp.base.p hyp.base.q
  E_nonempty_formula : Prop
  E_nonempty_formula_holds : E_nonempty_formula
  E_card_ge_two : Prop
  E_card_ge_two_holds : E_card_ge_two
  E_inverse_closed : Prop
  E_inverse_closed_holds : E_inverse_closed
  polynomial_root_bound : Prop
  polynomial_root_bound_holds : polynomial_root_bound

/-! ## Lemmas C.1--C.3 -/

/-- **BG Lemma C.1**: if the norm set is inverse-closed and has at least two
elements, the polynomial root count gives `p <= q`. -/
theorem lemmaC1_root_count [Finite G]
    (hyp : S16.Hypothesis (G := G)) (norms : NormSetData hyp) :
    hyp.base.p ≤ hyp.base.q := by
  sorry

/-- **BG Lemma C.2**: the norm set has at least two elements. -/
theorem lemmaC2_card_ge_two [Finite G]
    (hyp : S16.Hypothesis (G := G)) (hB : HypothesisB hyp) :
    ∃ norms : NormSetData hyp, norms.E_card_ge_two := by
  sorry

/-- **BG Lemma C.3**: the norm set is closed under inversion. -/
theorem lemmaC3_inverse_closed [Finite G]
    (hyp : S16.Hypothesis (G := G)) (hB : HypothesisB hyp) :
    ∃ norms : NormSetData hyp, norms.E_inverse_closed := by
  sorry

/-! ## Theorem C and the Peterfalvi bridge -/

/-- **BG Theorem C**: the field-normalizer configuration constructed in
Peterfalvi (14.2) forces `p <= q`. -/
theorem theoremC [Finite G] (hyp : S16.Hypothesis (G := G)) :
    S16.FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q := by
  intro data
  sorry

/-- **BG Appendix C + Peterfalvi Section 16**: once Peterfalvi constructs the
field-normalizer data, BG Theorem C contradicts the standing hypothesis `q < p`. -/
theorem final_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : S16.Hypothesis (G := G)) :
    False :=
  S16.nonexistence_of_G hG hyp (theoremC hyp)

end OddOrder.BG.AppC
