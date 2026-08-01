/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
