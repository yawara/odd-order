/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelAction
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3CorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourModel

/-!
# Ch. IV §4, step (2): the Proposition of Ch. III §3 on `U/Z(U)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2), p. 133.

Step (2) runs §2 and §3 "relative to `U`", that is on the quotient `U/Z(U)` that
Ch. I §3 Proposition 1(c) identifies with the standard `PSU(3, ℓ)`.  The standing
hypothesis there is `residualQuotientHypothesis`, and every numerical input the
Proposition of Ch. III §3 takes — `|s t| = 3`, `n ≠ 0`, `|Q̄₀| = 2ⁿ`, `|Q̄| = |Q̄₀|³`
and the induction hypothesis — is already available for it.

So the Proposition itself is available, and this file says so: the caller obtains the
model on `U/Z(U)` and feeds it to `corollaryTwo_of_sectionThree`.

## Main results

* `Hypothesis.isStandardModel_residualQuotient` — the Proposition of Ch. III §3 holds
  on `U/Z(U)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}
  (details : CentralizerPSUData hyp X result data)

/-- **The Proposition of Ch. III §3 holds on `U/Z(U)`** (Peterfalvi Part II, Ch. IV §4,
step (2), p. 133).

`exists_standardModel` takes `|s t| = 3`, `n ≠ 0`, `|Q̄₀| = 2ⁿ`, `|Q̄| = |Q̄₀|³` and the
induction hypothesis; all five were transported to `U/Z(U)` in
`PSU3SectionFourModel`, the last one along `natCard_residualQuotient_lt`.  The two
standing bundles `LemmaFiveSetup` and `QuotientFieldModel` and the central `x₀ ≠ 1` are
also available there (`nonempty_standingData_residualQuotient`,
`exists_center_Q_ne_one_residualQuotient`), so a caller can discharge every argument. -/
theorem isStandardModel_residualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∀ (sfive : (hyp.residualQuotientHypothesis details).LemmaFiveSetup data.n)
      (M : (hyp.residualQuotientHypothesis details).QuotientFieldModel data.n)
      (x₀ : ↥(Subgroup.center (hyp.residualQuotientHypothesis details).Q)), x₀ ≠ 1 →
      (hyp.residualQuotientHypothesis details).IsStandardModel sfive M x₀ := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  have ihq : TheoremAInductionBelow
      (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) :=
    hyp.theoremAInductionBelow_residualQuotient details hXV hX ih
  intro sfive M x₀ hx₀
  exact (hyp.residualQuotientHypothesis details).exists_standardModel sfive M
    (hyp.residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t details)
    (Nat.zero_lt_one.trans data.one_lt_n).ne'
    (hyp.natCard_residualQuotientHypothesis_Q0 details)
    (hyp.natCard_residualQuotientHypothesis_Q details) ihq x₀ hx₀

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
