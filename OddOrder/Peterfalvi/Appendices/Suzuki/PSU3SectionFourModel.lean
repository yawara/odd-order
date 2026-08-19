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
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact Hypothesis.ofMulEquivPullback_V_eq_W _ _
    (standardHypothesisULift_V_eq_W data.n data.one_lt_n)

/-- `|Q₀| = ℓ` on `U/Z(U)`. -/
theorem natCard_residualQuotientHypothesis_Q0 :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Nat.card ((hyp.residualQuotientHypothesis details).Q0) = 2 ^ data.n := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact (Hypothesis.ofMulEquivPullback_natCard_Q0 _ _).trans
    (natCard_standardHypothesisULift_Q0.{v} data.n data.one_lt_n)

/-- `|Q| = |Q₀|³` on `U/Z(U)`. -/
theorem natCard_residualQuotientHypothesis_Q :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Nat.card ((hyp.residualQuotientHypothesis details).Q)
      = Nat.card ((hyp.residualQuotientHypothesis details).Q0) ^ 3 := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
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
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact (Hypothesis.ofMulEquivPullback_orderOf_distinguishedInvolution_mul_t _ _).trans
    (standardHypothesisULift_orderOf_distinguishedInvolution_mul_t data.n data.one_lt_n)

/-- A non-trivial element of `W` on `U/Z(U)`. -/
theorem exists_ne_one_mem_residualQuotientHypothesis_W :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∃ x ∈ (hyp.residualQuotientHypothesis details).W, x ≠ 1 := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact Hypothesis.ofMulEquivPullback_exists_ne_one_mem_W _ _
    (exists_ne_one_mem_standardHypothesisULift_W data.n data.one_lt_n)

/-- `Q` on `U/Z(U)` is a Suzuki `2`-group: it is the image of the standard root
subgroup under the identification. -/
theorem isSuzuki2Group_residualQuotientHypothesis_Q :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥((hyp.residualQuotientHypothesis details).Q) := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  refine OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv
    (standardRootSubgroup_isSuzuki2Group data.n data.one_lt_n) ?_
  exact (Subgroup.equivMapOfInjective _ (MulEquiv.refl (standardPermGroup data.n)).toMonoidHom
      (MulEquiv.refl (standardPermGroup data.n)).injective).trans
    (Subgroup.equivMapOfInjective _ details.residualQuotientEquiv.symm.toMonoidHom
      details.residualQuotientEquiv.symm.injective)

/-- The ambient induction hypothesis restricts to `U/Z(U)`, which is smaller than `G`
(`natCard_residualQuotient_lt`). -/
theorem theoremAInductionBelow_residualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    TheoremAInductionBelow
      (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  intro A Λ'' _ _ _ hlt hA
  exact ih (hlt.trans (hyp.natCard_residualQuotient_lt hXV hX)) hA

/-- **§2/§3 run on `U/Z(U)`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

Both standing bundles those sections are parametrized by — `LemmaFiveSetup` (Ch. I §3
Lemma 5) and `QuotientFieldModel` (Ch. III §3) — are available for `U/Z(U)` on §4's
ambient hypotheses alone, because every input is either a transported fact about the
standard model or the ambient induction hypothesis restricted along
`natCard_residualQuotient_lt`. -/
theorem nonempty_standingData_residualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    Nonempty ((hyp.residualQuotientHypothesis details).LemmaFiveSetup data.n) ∧
      Nonempty ((hyp.residualQuotientHypothesis details).QuotientFieldModel data.n) := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  obtain ⟨w, hwW, hw1⟩ := hyp.exists_ne_one_mem_residualQuotientHypothesis_W details
  have hst := hyp.residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t details
  have hQsuz := hyp.isSuzuki2Group_residualQuotientHypothesis_Q details
  have hQ0card := hyp.natCard_residualQuotientHypothesis_Q0 details
  have hcardQ := hyp.natCard_residualQuotientHypothesis_Q details
  have ihq : TheoremAInductionBelow
      (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) :=
    hyp.theoremAInductionBelow_residualQuotient details hXV hX ih
  have hn0 : data.n ≠ 0 := (Nat.zero_lt_one.trans data.one_lt_n).ne'
  obtain ⟨sfive⟩ :=
    (hyp.residualQuotientHypothesis details).lemmaFiveSetup_of_orderThree_of_mem_W
      hwW hw1 hst hQsuz hn0 hQ0card hcardQ ihq
  exact ⟨⟨sfive⟩,
    (hyp.residualQuotientHypothesis details).nonempty_quotientFieldModel_of_orderThree
      hst hQsuz hn0 hQ0card hcardQ ihq sfive hwW hw1⟩

/-- The `x₀ ∈ Z(Q)`, `x₀ ≠ 1` that `exists_standardModel` takes, on `U/Z(U)`. -/
theorem exists_center_Q_ne_one_residualQuotient :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∃ x₀ : ↥(Subgroup.center (hyp.residualQuotientHypothesis details).Q), x₀ ≠ 1 := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  exact (hyp.residualQuotientHypothesis details).exists_center_Q_ne_one

/-- `M.mu` is injective on `U/Z(U)` — the `hmu` of the stage-(4) chain.

`mu_injective` (Ch. III §3 step (4)) needs exactly the numerics and the induction
hypothesis, all of which are available here. -/
theorem mu_injective_residualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∀ (_sfive : (hyp.residualQuotientHypothesis details).LemmaFiveSetup data.n)
      (M : (hyp.residualQuotientHypothesis details).QuotientFieldModel data.n),
      Function.Injective M.mu := by
  let := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  have ihq : TheoremAInductionBelow
      (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X))
      (ULift.{v} (Unital data.n)) :=
    hyp.theoremAInductionBelow_residualQuotient details hXV hX ih
  intro sfive M
  exact (hyp.residualQuotientHypothesis details).mu_injective
    (hyp.residualQuotientHypothesis_orderOf_distinguishedInvolution_mul_t details)
    (Nat.zero_lt_one.trans data.one_lt_n).ne'
    (hyp.natCard_residualQuotientHypothesis_Q0 details)
    (hyp.natCard_residualQuotientHypothesis_Q details) ihq sfive M

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
