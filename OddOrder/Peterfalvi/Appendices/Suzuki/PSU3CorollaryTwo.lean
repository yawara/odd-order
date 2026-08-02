/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelAction
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3ModelTwistOdd
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SequenceCoordinate
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepFive

/-!
# Peterfalvi Part II, Ch. IV §3, Corollary 2, from a single base pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 130–132.

`corollaryTwo_of_stepFour` leaves stage (4) — the cover `hcover` of the fibre of one
`ω₀ ∈ Q − Q₀` — as an input.  This file discharges it.

The book runs stage (4) twice, at `(ω, ζ)` and at `(ω⁻¹, ζ⁻¹)`, and each run covers the
fibre except for one point; the two exceptions differ because `ζ + 1 ≠ ζ⁻¹ + 1`
(`mu_W_ne_inv`), so the runs together cover it.  Here `stepFour_fibre` is one run —
`stepFour_base` for the base point followed by `stepFour_elem`, whose three pointwise
inputs are `stepFour_pointwise`, `stepTwo_quotient` and `stepFour_at_omega` — and
`stepFour_cover_of_base` glues the two by `stepFour_cover`.

The second run needs nothing new: `f_inv_eq` turns the standing hypothesis
`f(ω) = ω^{-ζ}` into `f(ω⁻¹) = (ω⁻¹)^{-ζ⁻¹}`, and stage (3) is invariant under the swap
because inversion fixes the quotient coordinate (`quotient_inv_eq`) while `μ(1, ζ⁻¹)` is
`μ(1, ζ)⁻¹`, so the trace `μ(1, ζ) + μ(1, ζ)⁻¹` is the same.

## Main results

* `Hypothesis.stepFour_fibre` — one run of stage (4): the base point's unitary
  coordinate is `μ(1, ζ)`, and the inversion formula holds off the excluded point.
* `Hypothesis.stepFour_cover_of_base` — stage (4) on the whole fibre, i.e. the `hcover`
  of `corollaryTwo_of_stepFour`.
* `Hypothesis.corollaryTwo_of_base` — Corollary 2 with only the base pair of §2 left as
  a hypothesis.
* `Hypothesis.corollaryTwo_of_standardModel` — the same, phrased directly on the output
  of the Proposition of Ch. III §3 (`exists_standardModel`) plus §3 (3): the unitary
  coordinates, the normalization `ν c(s) = 1`, the exponent `d = 2` and stage (3) at the
  base pair are all built here.
* `Hypothesis.stepThree_model` — §3 (3) in the two shapes that endpoint consumes.
* `Hypothesis.corollaryTwo_of_sectionThree` — the two composed: Corollary 2 from the
  model of Ch. III §3, the type-`B` scaling pair and §2's base pair.
* `Hypothesis.corollaryTwo_of_isStandardModel` — the same off the bundled predicate
  `IsStandardModel`, so a caller supplies only the scaling pair and §2's base pair.
* `Hypothesis.corollaryTwo_of_isStandardModel_of_normalization` — and with the base pair
  itself produced by §2 (9), leaving only the square relation of §2 (20).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **One run of stage (4)** (Peterfalvi Part II, Ch. IV §3 (4), p. 131).

The base point is `stepFour_base`: the unitary coordinate of `ω` is `μ(1, ζ)` — the
book's `x = ζ⁻¹`.  With it, `stepFour_elem` evaluates `f` at every point of the fibre of
`ω̄` except the one whose unitary coordinate is `x + 1`; its three inputs are the value
at `ω s^a` (`stepFour_pointwise`), the quotient coordinate there (`stepTwo_quotient`)
and the value at `ω` itself (`stepFour_at_omega`). -/
theorem stepFour_fibre (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹) :
    Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
        = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ∧
      ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q),
        (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
            ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩) + 1 →
          (Ψ ⟨f ρ, hfρQ⟩).quotient
              = (Ψ ⟨ω, hωQ⟩).quotient /
                Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
              = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  have hfibQ : ∀ a : G, a ∈ hyp.K →
      f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q := fun a haK =>
    hfQ _ (hyp.Q.mul_mem hωQ (hyp.Q0_le_Q
      (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hyp.distinguishedInvolution_mem_Q0)))
  have hx := hyp.stepFour_base H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ hΨq hΨc
    hconjq hconjy d hequiv hdsq hs hζ hζ1 hωQ hωQ0 hf hstage3 hm hQ0card hfibQ
  refine ⟨hx, fun ρ hρQ hfρQ hfib hne => ?_⟩
  refine hyp.stepFour_elem sfive M hZc Φ hquot ι hker hu Ψ hene hΨq hΨc d hequiv hdsq hs
    hωQ (fun a haK hfaQ hA1 => ?_) (fun a haK hfaQ => ?_) (fun hfωQ => ?_) hρQ hfρQ hfib
    hne
  · rw [hx]
    exact hyp.stepFour_pointwise H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ hΨq hΨc
      hconjq hconjy d hequiv hdsq hs hζ hζ1 hωQ hωQ0 hf hstage3 hx haK hA1 hfaQ
  · rw [hx]
    exact hyp.stepTwo_quotient H hC2 M hZc hmu hVW Φ hquot hu Ψ hΨq hζ hζ1 hωQ hωQ0
      (by rw [← hyp.coe_K]; exact haK) (pow_mem haK 2) hf hfaQ
  · exact hyp.stepFour_at_omega M hu Ψ hconjq hconjy hζ hωQ hf hfωQ hx

/-- **Stage (4) on the whole fibre**, from the base pair alone (Peterfalvi Part II,
Ch. IV §3 (4), p. 131) — the `hcover` of `corollaryTwo_of_stepFour`.

The run at `(ω⁻¹, ζ⁻¹)` is the run at `(ω, ζ)` with the swap of `f_inv_eq`; stage (3)
transports because inversion fixes the quotient coordinate and `μ(1, ζ⁻¹) = μ(1, ζ)⁻¹`
leaves the trace `μ(1, ζ) + μ(1, ζ)⁻¹` alone.  The two runs exclude the points
`x + 1` and `x⁻¹ + 1` of the fibre, which differ by `mu_W_ne_inv`. -/
theorem stepFour_cover_of_base (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹) :
    ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q) (hfρQ : f ρ ∈ hyp.Q),
      (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
        (Ψ ⟨f ρ, hfρQ⟩).quotient
            = (Ψ ⟨ρ, hρQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinvQ0 : ω⁻¹ ∉ hyp.Q0 := fun hc => hωQ0 (by simpa using hyp.Q0.inv_mem hc)
  have hζinv : ζ⁻¹ ∈ hyp.W := hyp.W.inv_mem hζ
  have hζinv1 : (⟨ζ⁻¹, hζinv⟩ : ↥hyp.W) ≠ 1 := by
    intro hc
    exact hζ1 (Subtype.ext (inv_eq_one.mp (congrArg Subtype.val hc)))
  -- `μ(1, ζ⁻¹) = μ(1, ζ)⁻¹`
  have hmuinv : ((M.mu ((1 : ↥hyp.actualKActor),
        (⟨ζ⁻¹, hζinv⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [show ((1 : ↥hyp.actualKActor), (⟨ζ⁻¹, hζinv⟩ : ↥hyp.W))
        = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W))⁻¹ from
      Prod.ext (inv_one (G := ↥hyp.actualKActor)).symm (Subtype.ext rfl),
      map_inv, Units.val_inv_eq_inv_val]
  -- the swapped standing hypothesis, `f(ω⁻¹) = (ω⁻¹)^{-ζ⁻¹}`
  have hfinv : f ω⁻¹ = ζ⁻¹⁻¹ * ω⁻¹⁻¹ * ζ⁻¹ := by
    rw [hyp.f_inv_eq H hζ hωQ hωQ0 hf]
    group
  -- stage (3) is invariant under the swap
  have hstage3inv : (Ψ ⟨ω⁻¹, hωinvQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ⁻¹, hζinv⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor),
          (⟨ζ⁻¹, hζinv⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [hyp.quotient_inv_eq M hu Ψ hωQ hωinvQ, hstage3, hmuinv, inv_inv]
    exact add_comm _ _
  obtain ⟨hx, hcov1⟩ := hyp.stepFour_fibre H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu Ψ
    hene hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hfQ hζ hζ1 hωQ hωQ0 hf hstage3
  obtain ⟨hxinv, hcov2⟩ := hyp.stepFour_fibre H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu
    Ψ hene hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hfQ hζinv hζinv1 hωinvQ
    hωinvQ0 hfinv hstage3inv
  have hxne : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω, hωQ⟩)
      ≠ Suzuki2Groups.unitaryCoord m u (Ψ ⟨ω⁻¹, hωinvQ⟩) := by
    rw [hx, hxinv, hmuinv]
    exact hyp.mu_W_ne_inv M hmu hζ1
  intro ρ hρQ hfρQ hfib
  obtain ⟨hA, hB⟩ :=
    hyp.stepFour_cover M hu Ψ hωQ hωinvQ hxne hcov1 hcov2 ρ hρQ hfρQ hfib
  exact ⟨hA.trans (by rw [hfib]), hB⟩

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2** (p. 132), with only §2's base pair
left as a hypothesis.

> For every `ζ ∈ W^#` there is an `ω ∈ Q − Q₀` with `f(ω) = ω^{-ζ}` and `h(ω) = ζ³`.

`corollaryTwo_of_stepFour` still asked for stage (4) on the fibre of some `ω₀ ∈ Q − Q₀`;
`stepFour_cover_of_base` builds it from a single pair `(ω₀, ζ₀)` obeying the inversion
formula, which is what §2 closes with (`f_eq_conj_inv_of_stepTwenty_chain`).  Stage (3)
at that pair enters as `hstage3`. -/
theorem corollaryTwo_of_base (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdsq : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) ^ 2)
    (hs : (ν : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    {ζ₀ ω₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hf₀ : f ω₀ = ζ₀⁻¹ * ω₀⁻¹ * ζ₀)
    (hstage3 : (Ψ ⟨ω₀, hω₀Q⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 :=
  hyp.corollaryTwo_of_stepFour H hC2 sfive M hZc hVW Φ hquot ι hker hu Ψ hene hΨq hΨc
    hconjq hconjy d hequiv hdsq hs hm hQ0card hmu hKcard hWdvd hW1 hfQ hω₀Q hω₀Q0
    (fun σ hσQ => hyp.stepFour_cover_of_base H hC2 sfive M hZc hmu hVW Φ hquot ι hker hu
      Ψ hene hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hfQ hζ₀ hζ₀1 hω₀Q hω₀Q0
      hf₀ hstage3 σ hσQ (hfQ σ hσQ))
    hhW hζ hζ1

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2**, on the output of the Proposition of
Ch. III §3 (pp. 120–132).

Everything between `exists_standardModel` and Corollary 2 is assembled here:

* `hθ` (§3 (3): the model's twist is the identity on `F`) turns the semilinearity into
  `F`-bilinearity, so `cocycle_diag_eq_norm` puts the cocycle's diagonal in the Hermitian
  shape `φ(1,1) · x^{1+q}`;
* that shape evaluates the opaque exponent `d` as squaring (`mu_K_zpow_eq_sq`) — the
  concrete content of `θ = 1`;
* `exists_modelEquiv_conj` makes the conjugation action pointwise and
  `exists_unitaryModel_conj` moves to the book's unitary coordinates `(a, y)` with
  `Tr y = a ā`;
* the book's normalization `s = (0, 1)` is imposed by taking `ν = c(s)⁻¹`;
* stage (3) at the base pair is `stepThree_quotient_norm` read through `hα`.

`hθ` and `hα` are the two conclusions of §3 (3) (`stepThree` composed with
`thetaModel_eq_id_on_frobFixed`, which also says `σ` is the identity on `F` — that is
why `hα` can be stated without `σ`).  The base pair itself is what §2 closes with
(`f_eq_conj_inv_of_stepTwenty_chain`); it arrives in §2's shape `f(ω₀) = (ω₀ ω₀²)^{ζ₀}`
and `f_eq_conj_inv_of_sq_eq` reads it as the inversion formula. -/
theorem corollaryTwo_of_standardModel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    -- the model of Ch. III §3
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E → M.E)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hθ : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θm a = a)
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    (hW : ∀ (v : ↥hyp.W) (x y : M.E),
      ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    {d : ℤ}
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
            ((p.central :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (uAut : MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (huAut : uAut ∈
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts)
    (hconj : (((MulAut.congr Φ).toMonoidHom.comp (hyp.conjQHom)).range).map
      (MulAut.conj uAut).toMonoidHom = Θ.range)
    -- §2's base pair, and stage (3) at it
    {ζ₀ ω₀ y₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hy₀Q0 : y₀ ∈ hyp.Q0)
    (hsqω₀ : ω₀ * ω₀ = y₀) (hfω₀ : f ω₀ = ζ₀⁻¹ * (ω₀ * y₀) * ζ₀)
    (hα : hyp.centerCoord sfive M ι hy₀Q0 /
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 := by
  classical
  -- ### `θ = 1` makes the cocycle `F`-bilinear, hence Hermitian on the diagonal
  have hbil : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
    intro a ha b hb x y
    rw [hsemi a ha b hb x y, hθ b hb]
  have hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      ≠ 0 := fun hc => haniso 1 one_ne_zero (Subtype.ext hc)
  have hnorm := hyp.cocycle_diag_eq_norm M hm θm hsemi hθ hW hmu hζ₀1
  -- ### the exponent `d` is squaring
  have hdsq := hyp.mu_K_zpow_eq_sq M hnorm hone Θ hΘq hΘc
  -- ### the book's normalization `ν c(s) = 1`
  set c : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    ι (Additive.ofMul (hyp.toCenter sfive hyp.distinguishedInvolution_mem_Q0)) with hcdef
  have hcval : ((c : M.E)) =
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := rfl
  have hcs0 : hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 ≠ 0 :=
    hyp.centerCoord_distinguishedInvolution_ne_zero sfive M ι
  have hc0 : c ≠ 0 := fun hcc => hcs0 (by rw [← hcval, hcc]; simp)
  have hν : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hνval : ((c⁻¹ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = (hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)⁻¹ := by
    rw [← hcval]
    push_cast
    ring
  have hs : ((c⁻¹ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1 := by
    rw [hνval]
    exact inv_mul_cancel₀ hcs0
  -- ### the conjugation action, pointwise
  obtain ⟨Φ', hquot', hcentre', hconj'⟩ :=
    hyp.exists_modelEquiv_conj M Φ Θ uAut hquot hΘq huAut hconj hmu
  have hker' : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ' (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩ := by
    intro z
    have hz : Φ.symm (⟨0, ι (Additive.ofMul z)⟩ :
        Suzuki2Groups.BilinearTwistedProduct φ) = (z : ↥hyp.Q) := by
      rw [← hker z, Φ.symm_apply_apply]
    rw [← hz]
    exact hcentre' _
  -- ### the unitary coordinates
  obtain ⟨u, hu, e, Ψ, hene, -, hΨq, hΨc, hconjq, hconjy⟩ :=
    hyp.exists_unitaryModel_conj M hm hbil hnorm hone hν Φ' Θ hΘq
      (fun kv => ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E)) hΘc hconj'
  -- ### the base pair in the shape stage (4) uses, and stage (3) at it
  have hf₀ : f ω₀ = ζ₀⁻¹ * ω₀⁻¹ * ζ₀ :=
    hyp.f_eq_conj_inv_of_sq_eq hy₀Q0 hfω₀ hsqω₀
  have hstage3 : (Ψ ⟨ω₀, hω₀Q⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor),
          (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [hyp.stepThree_quotient_norm sfive M Φ' ι hker' hu Ψ hΨq hΨc hω₀Q hy₀Q0 hsqω₀,
      ← hα, hνval, div_eq_mul_inv]
    exact mul_comm _ _
  exact hyp.corollaryTwo_of_base H hC2 sfive M hZc hmu hVW Φ' hquot' ι hker' hu Ψ hene
    hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hKcard hWdvd hW1 hfQ hhW hζ₀ hζ₀1
    hω₀Q hω₀Q0 hf₀ hstage3 hζ hζ1

/-- **§3 (3), in the shape `corollaryTwo_of_standardModel` consumes it** (Peterfalvi
Part II, Ch. IV §3 (3), p. 130).

`stepThree` states its two conclusions through the type-`B` scaling pair `σ`, `τ`: the
first says `σ = τ` on `F`, the second reads `α` after applying `σ⁻¹`.  Both mentions of
`σ` disappear once `thetaModel_eq_id_on_frobFixed` turns `σ|_F = τ|_F` into `σ|_F = 1` —
and it simultaneously says the *model's* twist `θ` is the identity on `F`, which is the
form the unitary coordinates need.

So this is `stepThree_of_odd` composed with that upgrade: out come exactly `hθ` and `hα`.

`hodd` is the book's "`θ` is of odd order" (p. 130), which is what it derives `|F| ≥ 8`
from; `hcard` is then only the three elements the `θ|_F = 1` branch needs.  It is stated
for `θF`, the restriction of `θ = σ⁻¹τ` to `F`, because that is where the book's `θ` lives
— on `E` the same map may be the `q`-Frobenius, of order `2`. -/
theorem stepThree_model (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E ≃ₐ[ZMod 2] M.E)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdiagscale : ∀ a b : M.E,
      (∀ x : M.E,
        ((hyp.centreQuadraticMap sfive M ι (a * x) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((hyp.centreQuadraticMap sfive M ι x :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
      ∀ x y : M.E,
        ((φ (a * x) (a * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((φ x y :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    -- the type-`B` scaling pair
    (σ τ : M.E ≃+* M.E)
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    (θF : RingAut ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hθF : ∀ a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      ((θF a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = σ.symm (τ a))
    (hodd : Odd (orderOf θF))
    -- §2's base pair
    {ζ₀ ω₀ y₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hy₀Q0 : y₀ ∈ hyp.Q0)
    (hsqω₀ : ω₀ * ω₀ = y₀) (hfω₀ : f ω₀ = ζ₀⁻¹ * (ω₀ * y₀) * ζ₀) :
    (∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θm a = a) ∧
      hyp.centerCoord sfive M ι hy₀Q0 /
          hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0
        = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
          + ((M.mu ((1 : ↥hyp.actualKActor),
            (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
  have hζ₀ne : ζ₀ ≠ 1 := fun hc => hζ₀1 (Subtype.ext hc)
  obtain ⟨hστ0, hαst⟩ := hyp.stepThree_of_odd H hC2 hm hQ0card sfive M hZc hmu hVW hcard
    ι d hequiv σ τ (σ.symm.toRingHom.comp τ.toRingHom).toAddMonoidHom (fun _ => rfl) θF
    hθF hodd hscale hWinv hζ₀ hζ₀ne hω₀Q hω₀Q0 hy₀Q0 hsqω₀ hfω₀
  -- `σ = τ` on `F`, which is what the upgrade takes
  have hστ : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      σ.toRingHom a = τ.toRingHom a := by
    intro a ha
    have h0 : σ.symm (τ a) = a := hστ0 a ha
    change σ a = τ a
    have h1 := congrArg (σ : M.E → M.E) h0
    rw [σ.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨hσid, hθid⟩ := hyp.thetaModel_eq_id_on_frobFixed M hm hQ0card sfive
    σ.toRingHom τ.toRingHom θm.toRingEquiv.toRingHom d hsemi haniso
    (hyp.cocycle_scale_of_diagScale M sfive ι d hequiv hdiagscale) hscale hστ
  refine ⟨hθid, ?_⟩
  -- `σ` fixes `F` pointwise, hence so does `σ⁻¹`
  have hmemF : hyp.centerCoord sfive M ι hy₀Q0 /
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    div_mem (SetLike.coe_mem _) (SetLike.coe_mem _)
  have hfix : σ.symm (hyp.centerCoord sfive M ι hy₀Q0 /
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)
      = hyp.centerCoord sfive M ι hy₀Q0 /
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := by
    have h0 : σ (hyp.centerCoord sfive M ι hy₀Q0 /
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)
        = hyp.centerCoord sfive M ι hy₀Q0 /
          hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := hσid _ hmemF
    rw [σ.symm_apply_eq]
    exact h0.symm
  rwa [hfix] at hαst

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2**, from the Proposition of Ch. III §3
and §2's Proposition alone (pp. 120–132).

`stepThree_model` supplies `corollaryTwo_of_standardModel`'s two `§3 (3)` inputs, so
what is left is exactly: the model of Ch. III §3 (which `exists_standardModel` produces
from the numerics and the induction hypothesis), the type-`B` scaling pair `σ`, `τ` — of
which §3 (3) asks only that `θ = σ⁻¹τ` have odd order, as in the book — and the base pair
`f(ω₀) = (ω₀ ω₀²)^{ζ₀}` that §2 closes with. -/
theorem corollaryTwo_of_sectionThree (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E ≃ₐ[ZMod 2] M.E)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    (hW : ∀ (v : ↥hyp.W) (x y : M.E),
      ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    {d : ℤ}
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
            ((p.central :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hdiagscale : ∀ a b : M.E,
      (∀ x : M.E,
        ((hyp.centreQuadraticMap sfive M ι (a * x) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((hyp.centreQuadraticMap sfive M ι x :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
      ∀ x y : M.E,
        ((φ (a * x) (a * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((φ x y :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (uAut : MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (huAut : uAut ∈
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts)
    (hconj : (((MulAut.congr Φ).toMonoidHom.comp (hyp.conjQHom)).range).map
      (MulAut.conj uAut).toMonoidHom = Θ.range)
    (σ τ : M.E ≃+* M.E)
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    (θF : RingAut ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hθF : ∀ a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      ((θF a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = σ.symm (τ a))
    (hodd : Odd (orderOf θF))
    {ζ₀ ω₀ y₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hy₀Q0 : y₀ ∈ hyp.Q0)
    (hsqω₀ : ω₀ * ω₀ = y₀) (hfω₀ : f ω₀ = ζ₀⁻¹ * (ω₀ * y₀) * ζ₀)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 := by
  obtain ⟨hθ, hα⟩ := hyp.stepThree_model H hC2 hm hQ0card sfive M hZc hmu hVW hcard θm
    hsemi haniso ι d hequiv hdiagscale σ τ hscale hWinv θF hθF hodd hζ₀ hζ₀1 hω₀Q hω₀Q0
    hy₀Q0 hsqω₀ hfω₀
  exact hyp.corollaryTwo_of_standardModel H hC2 sfive M hZc hmu hVW hm hQ0card hKcard
    hWdvd hW1 hfQ hhW θm hsemi hθ haniso Φ hquot ι hker hW Θ hΘq hΘc hequiv uAut huAut
    hconj hζ₀ hζ₀1 hω₀Q hω₀Q0 hy₀Q0 hsqω₀ hfω₀ hα hζ hζ1

/-! ### The remaining inputs of `corollaryTwo_of_sectionThree`

Apart from the model, the type-`B` scaling pair and §2's base pair, every hypothesis is
a fact about the standing hypothesis itself. -/

/-- **The braid relation `t s t = s t s`** (Peterfalvi Part II, Ch. I §3, Lemma 4,
p. 107) for the standing hypothesis' own involutions — the `hC2` of §3.

Both `s` and `t` are involutions, so `|s t| = 3` *is* the braid relation. -/
theorem braid_of_orderThree
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3) :
    hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution :=
  braid_of_involutions_of_orderOf_mul_eq_three hyp.distinguishedInvolution_sq hyp.t_sq hst

/-- **`1 < |W|`** — the `hW1` of §3, from a single non-trivial element. -/
theorem one_lt_natCard_W (hW : ∃ x ∈ hyp.W, x ≠ 1) : 1 < Nat.card ↥hyp.W := by
  obtain ⟨x, hxW, hx1⟩ := hW
  haveI : Nontrivial ↥hyp.W :=
    ⟨⟨⟨x, hxW⟩, 1, fun hc => hx1 (congrArg Subtype.val hc)⟩⟩
  exact Finite.one_lt_card

/-- **`f` may be taken to map `Q` into `Q`** — the `hfQ` of §3.

`IsFGH` constrains `f` only on `Q^#`, so the `f` of `exists_fgh` need not send `1`
anywhere in particular.  Redefining it at `1` changes nothing that `IsFGH` sees and makes
it map `Q` into `Q`, which is the form stages (4) and (5) use (they apply `f` to elements
of `Q` without knowing they are non-trivial). -/
theorem exists_fgh_mapsTo :
    ∃ f₁ g₁ h₁ : G → G,
      OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f₁ g₁ h₁ ∧
        ∀ ρ : G, ρ ∈ hyp.Q → f₁ ρ ∈ hyp.Q := by
  classical
  obtain ⟨f₁, g₁, h₁, H₁⟩ := hyp.exists_fgh
  refine ⟨fun x => if x = 1 then 1 else f₁ x, g₁, h₁,
    ⟨fun x hxQ hx1 => ?_, fun x hxQ hx1 => ?_⟩, fun ρ hρQ => ?_⟩
  · rw [if_neg hx1]
    exact H₁.mem x hxQ hx1
  · rw [if_neg hx1]
    exact H₁.eq x hxQ hx1
  · change (if ρ = 1 then (1 : G) else f₁ ρ) ∈ hyp.Q
    by_cases hρ1 : ρ = 1
    · rw [if_pos hρ1]
      exact hyp.Q.one_mem
    · rw [if_neg hρ1]
      exact (H₁.mem ρ hρQ hρ1).1

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2, straight off `IsStandardModel`**
(pp. 120–132).

`corollaryTwo_of_sectionThree` consumes the Proposition of Ch. III §3 clause by clause;
this unpacks `IsStandardModel` — the same Proposition as a single predicate — and feeds
it in, so a caller who has the Proposition on some group needs to supply only what is
genuinely extra:

* the base pair `f(ω₀) = (ω₀ ω₀²)^{ζ₀}` that §2 closes with.

The type-`B` scaling pair is *not* asked for: it is built from the model's own coordinate
by `Hypothesis.exists_scalingPair_of_centerCoordinate`, and the book's "`θ` is of odd
order" comes with it (`Hypothesis.odd_orderOf_scalingPair_of_model`), `K` being regular
on `Z(Q)^#`.

Two of the eleven clauses go unused here — the normalization `Φ(x₀) = (0, 1)` and the
central half of the `K`-scaling — because Corollary 2 reads the model only through its
quotient coordinate and its cocycle. -/
theorem corollaryTwo_of_isStandardModel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hmodel : hyp.IsStandardModel sfive M x₀)
    -- §2's base pair
    {ζ₀ ω₀ y₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hy₀Q0 : y₀ ∈ hyp.Q0)
    (hsqω₀ : ω₀ * ω₀ = y₀) (hfω₀ : f ω₀ = ζ₀⁻¹ * (ω₀ * y₀) * ζ₀)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 := by
  obtain ⟨φ, θm, Φ, Θ, u, ι, hsemi, haniso, -, hΘq, hu, hconj, hquot, hW, hker,
    hdiagscale, d, hequiv, -, hΘc⟩ := hmodel
  -- the type-`B` scaling pair, for the model's own `ι` and `d`
  obtain ⟨σ, τ, hscale, hWinv⟩ :=
    hyp.exists_scalingPair_of_centerCoordinate sfive M ι d hequiv
  set θF : RingAut ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    (OddOrder.FiniteField.restrictToFrobFixed (m := m) σ)⁻¹ *
      OddOrder.FiniteField.restrictToFrobFixed (m := m) τ with hθFdef
  have hθF : ∀ a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      ((θF a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = σ.symm (τ (a : M.E)) :=
    fun a => OddOrder.FiniteField.coe_restrictToFrobFixed_inv_mul σ τ a
  -- the book's "`θ` is of odd order" is a *theorem* about the model: `K` is regular
  -- on `Z(Q)^#`, so `a ↦ a^d = a · θ(a)` is onto `F^×`
  have hodd : Odd (orderOf θF) :=
    hyp.odd_orderOf_scalingPair_of_model hm hQ0card sfive M θm.toRingEquiv hsemi haniso
      (hyp.cocycle_scale_of_diagScale M sfive ι d hequiv hdiagscale) ι hequiv σ τ hscale
      θF hθF
  exact hyp.corollaryTwo_of_sectionThree H hC2 sfive M hZc hmu hVW hm hQ0card hcard
    hKcard hWdvd hW1 hfQ hhW θm hsemi haniso Φ hquot ι hker hW Θ hΘq hΘc hequiv
    hdiagscale u hu hconj σ τ hscale hWinv θF hθF hodd hζ₀ hζ₀1 hω₀Q hω₀Q0 hy₀Q0 hsqω₀
    hfω₀ hζ hζ1

/-- `Q` is strictly larger than `Q₀`, since `|Q| = |Q₀|³` and `|Q₀| > 1`. -/
theorem exists_mem_Q_notMem_Q0 {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3) : ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 := by
  by_contra hcon
  push Not at hcon
  have hle : hyp.Q ≤ hyp.Q0 := fun x hx => hcon x hx
  have heq : hyp.Q = hyp.Q0 := le_antisymm hle (fun x hx => hyp.Q0_le_Q hx)
  rw [heq, hQ0card] at hcardQ
  have h1 : 1 < 2 ^ m := by
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
  have hgt : (2 ^ m : ℕ) ^ 1 < (2 ^ m : ℕ) ^ 3 := Nat.pow_lt_pow_right h1 (by norm_num)
  rw [pow_one] at hgt
  omega

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2, with §2's base pair produced in place**
(pp. 120–132).

`stepNine` is §2's normalization "the `ω_i` may be chosen so that `f(ω_i) = (ω_i y_i)^ζ`"
(p. 125), so the base pair need not be supplied: only the *square* relation `ω² = y` that
§2 closes with (step (20)) is left, and it is taken here in the shape step (20) proves it
— for every normalized pair at once.

That isolates exactly what "run §2 relative to `U`" still owes: `hsq`, the square relation
of step (20).  The type-`B` scaling pair is no longer owed — it comes from the model
itself (`Hypothesis.exists_scalingPair_of_centerCoordinate`). -/
theorem corollaryTwo_of_isStandardModel_of_normalization
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hmodel : hyp.IsStandardModel sfive M x₀)
    -- §2 (20): a normalized pair squares to its `y`
    {ζ₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hsq : ∀ ω' ∈ hyp.Q, ω' ∉ hyp.Q0 → ∀ y ∈ hyp.Q0,
      f ω' = ζ₀⁻¹ * (ω' * y) * ζ₀ → ω' * ω' = y)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 := by
  obtain ⟨ω, hωQ, hωQ0⟩ := hyp.exists_mem_Q_notMem_Q0 hm hQ0card hcardQ
  obtain ⟨ω₀, hω₀Q, hω₀Q0, y₀, hy₀Q0, -, hfω₀⟩ := hyp.stepNine M hZc H hC2 hVW hm hQ0card
    hmu hKcard hWdvd hωQ hωQ0 hζ₀ (fun hc => hζ₀1 (Subtype.ext hc))
  exact hyp.corollaryTwo_of_isStandardModel H hC2 sfive M hZc hmu hVW hm hQ0card hcard
    hKcard hWdvd hW1 hfQ hhW x₀ hmodel hζ₀ hζ₀1 hω₀Q hω₀Q0 hy₀Q0
    (hsq ω₀ hω₀Q hω₀Q0 y₀ hy₀Q0 hfω₀) hfω₀ hζ hζ1

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
