/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StandardModelHypothesis
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourSetup

/-!
# Ch. IV §4, step (2): the standing hypothesis on `U/Z(U)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2), p. 133:

> If `f₁` and `h₁` denote the mappings `f` and `h` relative to `U`, `U ∩ H` and `t`, then,
> by Corollary 2 of the proposition of §3, there is an element `ω ∈ (Q − Q₀) ∩ U` such
> that `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` and `h₁(ω) ∈ ζ₁³(P ∩ U)`.

Running §2/§3 "relative to `U`" means having the standing hypothesis on `U/(P ∩ U)`,
which is `U/Z(U)` (`mem_center_primeComplementResidual_of_mem_P`).  Ch. I §3
Proposition 1(c) identifies that quotient with the standard `PSU(3, ℓ)`
(`CentralizerPSUData.residualQuotientEquiv`), and `standardHypothesis` puts (A1)–(A3) on
the standard model; transporting along the identification therefore puts them on
`U/Z(U)`.

Going through the model rather than through the faithful centralizer quotient
`C_G(X)/𝒩(C_G(X))` is what makes `V = W` available: it is a theorem in the model
(`standardHypothesis_V_eq_W`) and not generally true for the other quotient.

## Main results

* `Hypothesis.residualQuotientHypothesis` — the (A1)–(A3) carrier on `U/Z(U)`.
* the transported hypotheses of `exists_standardModel`: `hVW`, `hQ0card`, `hcardQ`,
  `hst`, a non-trivial element of `W`, and the induction hypothesis.
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

/-- The residual `U = O^{2′}(C_G(X))`, as a subgroup of the centralizer. -/
abbrev residual (X : Subgroup G) : Subgroup ↥(Subgroup.centralizer (X : Set G)) :=
  Subgroup.primeComplementResidual 2 (Subgroup.centralizer (X : Set G))

/-- **The standing hypothesis on `U/Z(U)`**, transported from the standard
`PSU(3, ℓ)` model along Ch. I §3 Proposition 1(c)'s identification. -/
noncomputable def residualQuotientHypothesis
    (details : CentralizerPSUData hyp X result data) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Hypothesis (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) :=
  (standardHypothesisULift data.n data.one_lt_n).ofMulEquivPullback
    details.residualQuotientEquiv.symm


/-! ### The hypotheses of `exists_standardModel`, on `U/Z(U)`

Each is the corresponding fact for the standard model ((86)–(89) of issue 0168) pushed
along the identification by the `ofMulEquiv_*` transport lemmas. -/

variable (details : CentralizerPSUData hyp X result data)

/-- `V = W` on `U/Z(U)`. -/
theorem residualQuotientHypothesis_V_eq_W :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    (hyp.residualQuotientHypothesis details).V
      = (hyp.residualQuotientHypothesis details).W := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact Hypothesis.ofMulEquivPullback_V_eq_W _ _
    (standardHypothesisULift_V_eq_W data.n data.one_lt_n)

/-- `|Q₀| = ℓ` on `U/Z(U)`. -/
theorem natCard_residualQuotientHypothesis_Q0 :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Nat.card ((hyp.residualQuotientHypothesis details).Q0) = 2 ^ data.n := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact (Hypothesis.ofMulEquivPullback_natCard_Q0 _ _).trans
    (natCard_standardHypothesisULift_Q0.{v} data.n data.one_lt_n)

/-- `|Q| = |Q₀|³` on `U/Z(U)`. -/
theorem natCard_residualQuotientHypothesis_Q :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Nat.card ((hyp.residualQuotientHypothesis details).Q)
      = Nat.card ((hyp.residualQuotientHypothesis details).Q0) ^ 3 := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact calc Nat.card ((hyp.residualQuotientHypothesis details).Q)
      = Nat.card ((standardHypothesisULift.{v} data.n data.one_lt_n).Q) :=
        Hypothesis.ofMulEquivPullback_natCard_Q _ _
    _ = Nat.card ((standardHypothesisULift.{v} data.n data.one_lt_n).Q0) ^ 3 :=
        natCard_standardHypothesisULift_Q.{v} data.n data.one_lt_n
    _ = Nat.card ((hyp.residualQuotientHypothesis details).Q0) ^ 3 :=
        congrArg (· ^ 3) (Hypothesis.ofMulEquivPullback_natCard_Q0 _ _).symm

/-- `|s t| = 3` on `U/Z(U)`. -/
theorem residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    orderOf ((hyp.residualQuotientHypothesis details).distinguishedInvolution *
        (hyp.residualQuotientHypothesis details).t) = 3 := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact (Hypothesis.ofMulEquivPullback_orderOf_distinguishedInvolution_mul_t _ _).trans
    (standardHypothesisULift_orderOf_distinguishedInvolution_mul_t data.n data.one_lt_n)

/-- A non-trivial element of `W` on `U/Z(U)`. -/
theorem exists_ne_one_mem_residualQuotientHypothesis_W :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∃ x ∈ (hyp.residualQuotientHypothesis details).W, x ≠ 1 := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact Hypothesis.ofMulEquivPullback_exists_ne_one_mem_W _ _
    (exists_ne_one_mem_standardHypothesisULift_W data.n data.one_lt_n)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
