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

Step (2) also has to know that the mappings `f`, `g`, `h` of §1 do not leave `C_G(P)`
when applied inside it; `fgh_mem_centralizer` is that, for any `X ≤ D` centralizing `t`.

## Main results

* `Hypothesis.fgh_mem_centralizer` — `f`, `g`, `h` map `C_Q(X)^#` into `C_Q(X)`,
  `C_Q(X)`, `C_D(X)`.
* `Hypothesis.isStandardModel_residualQuotient` — the Proposition of Ch. III §3 holds
  on `U/Z(U)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open scoped Pointwise

section Centralizer

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G} {X : Subgroup G}

/-- **The mappings of Ch. IV §1 stay inside a centralizer** (Peterfalvi Part II,
Ch. IV §4, step (2), p. 133 — "the mappings `f` and `h` relative to `U`, `U ∩ H` and
`t`" presupposes exactly this).

If `X ≤ D` centralizes `t`, then conjugation by `p ∈ X` fixes `t x t` for every
`x ∈ C_Q(X)`, and carries the canonical factorization `t x t = g(x) h(x) t f(x)` to
another one — the factors stay where they belong because `p ∈ H` and `Q ⊴ H`.
Uniqueness of the canonical form (Ch. I Prop 4(a)) therefore fixes `g(x) h(x)` and
`f(x)`, so both centralize `X`.

Splitting `g(x) h(x)` is then Ch. I Prop 6(a): `C_H(X) = C_Q(X) ⋊ C_D(X)`, and the
uniqueness of the `Q D`-decomposition identifies the two factors with `g(x)` and
`h(x)`. -/
theorem fgh_mem_centralizer
    (Hfgh : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    {x : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1)
    (hxX : x ∈ Subgroup.centralizer (X : Set G)) :
    f x ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G) ∧
      g x ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G) ∧
      h x ∈ hyp.D ⊓ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨hfQ, hgQ, hhD⟩ := Hfgh.mem x hxQ hx1
  have hgh : g x * h x ∈ hyp.H := hyp.H.mul_mem (hyp.Q_le_H hgQ) (hyp.D_le_H hhD)
  -- conjugation by `p ∈ X` produces a second canonical form of `t x t`
  have hkey : ∀ p ∈ X, p * (g x * h x) * p⁻¹ = g x * h x ∧ p * f x * p⁻¹ = f x := by
    intro p hp
    have hpH : p ∈ hyp.H := hyp.D_le_H (hXD hp)
    have hpt : p * hyp.t * p⁻¹ = hyp.t := by
      rw [Subgroup.mem_centralizer_iff.mp htX p hp]; group
    have hpx : p * x * p⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp hxX p hp]; group
    have heq : p * (g x * h x) * p⁻¹ * hyp.t * (p * f x * p⁻¹)
        = g x * h x * hyp.t * f x := by
      calc p * (g x * h x) * p⁻¹ * hyp.t * (p * f x * p⁻¹)
          = p * (g x * h x) * p⁻¹ * (p * hyp.t * p⁻¹) * (p * f x * p⁻¹) := by
            rw [hpt]
        _ = p * (g x * h x * hyp.t * f x) * p⁻¹ := by group
        _ = p * (hyp.t * x * hyp.t) * p⁻¹ := by rw [← Hfgh.eq x hxQ hx1]
        _ = (p * hyp.t * p⁻¹) * (p * x * p⁻¹) * (p * hyp.t * p⁻¹) := by group
        _ = hyp.t * x * hyp.t := by rw [hpt, hpx]
        _ = g x * h x * hyp.t * f x := Hfgh.eq x hxQ hx1
    exact hyp.canonicalForm_unique
      (hyp.H.mul_mem (hyp.H.mul_mem hpH hgh) (hyp.H.inv_mem hpH))
      (hyp.Q_normal_in_H p hpH (f x) hfQ) hgh hfQ heq
  have hcent : ∀ (y : G), (∀ p ∈ X, p * y * p⁻¹ = y) →
      y ∈ Subgroup.centralizer (X : Set G) := by
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    have := hy p hp
    calc p * y = (p * y * p⁻¹) * p := by group
      _ = y * p := by rw [this]
  have hghC := hcent _ fun p hp => (hkey p hp).1
  have hfC := hcent _ fun p hp => (hkey p hp).2
  -- `C_H(X) = C_Q(X) · C_D(X)`, and the `Q D`-decomposition is unique
  have hmem : g x * h x ∈
      ((hyp.Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) *
        ((hyp.D ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    rw [hyp.cQ_mul_cD_eq_cH hXD]
    exact Subgroup.mem_inf.mpr ⟨hgh, hghC⟩
  obtain ⟨q, hq, d, hd, hqd⟩ := hmem
  rw [SetLike.mem_coe] at hq hd
  obtain ⟨p₀, -, huniq⟩ := hyp.existsUnique_Q_mul_D hgh
  have e₁ := huniq (⟨g x, hgQ⟩, ⟨h x, hhD⟩) rfl
  have e₂ := huniq (⟨q, (Subgroup.mem_inf.mp hq).1⟩, ⟨d, (Subgroup.mem_inf.mp hd).1⟩)
    hqd.symm
  have hpair := e₁.trans e₂.symm
  have hgq : g x = q :=
    congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) (congrArg Prod.fst hpair)
  have hhd : h x = d :=
    congrArg (Subtype.val (p := fun z => z ∈ hyp.D)) (congrArg Prod.snd hpair)
  refine ⟨Subgroup.mem_inf.mpr ⟨hfQ, hfC⟩, ?_, ?_⟩
  · rw [hgq]; exact hq
  · rw [hhd]; exact hd

end Centralizer

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
