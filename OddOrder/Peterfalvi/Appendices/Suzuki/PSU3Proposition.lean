/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3CorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3UnitaryRootEquiv

/-!
# Peterfalvi Part II, Ch. IV §3: the Proposition

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, p. 129:

> **Proposition.** Suppose that there are elements `ω ∈ Q − Q₀` and `ζ ∈ W^#` such that
> `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W`.  Then `θ = 1` and `f(ρ) = (ρ̄/y, 1/y)` for all
> `ρ = (ρ̄, y) ∈ Q − Q₀`.

Stages (1)–(3) give `θ = 1` (`stepThree`, `thetaModel_eq_id_on_frobFixed`); stage (4)
gives the formula on the fibre of `ω̄` (`stepFour_cover_of_base`) and stage (5) removes
that restriction (`stepFive`).  This file states the two halves together, in the form
Corollary 1 consumes: the formula holds at *every* `ρ ∈ Q − Q₀`, and, transported to the
unitary root group along `unitaryRootEquiv`, it says exactly that `f` is
`RootGroup.reciprocal`.

None of it uses `V = W`: the book's hypothesis `h(ω) ∈ W` is what closes the two places
where the repository previously appealed to the fixed-point-freeness of the whole of `D`
(`h_inv_eq`, and the fibre count of §2 (8) — see `PSU3StepEightKW`).  That is what makes
the Proposition available to §4, whose whole point is the case `V ≠ W`.

## Main results

* `Hypothesis.proposition_inverseFormula` — the formula at every `ρ ∈ Q − Q₀`.
* `Hypothesis.inverseFormula_of_mem_Q0` — the same on `Q₀^#`, which is §2 (1).
* `Hypothesis.proposition_inverseFormula_of_ne_one` — the two together, on `Q^#`.
* `Hypothesis.proposition_reciprocal` — the same, read in `RootGroup q` through
  `unitaryRootEquiv`: `ε (f ρ) = reciprocal (ε ρ)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

section /- Ch. IV §3, the Proposition (pp. 129–131) -/

/-- **The Proposition of Peterfalvi Part II, Ch. IV §3** (p. 129), stages (4)–(5):

> `f(ρ) = (ρ̄/y, 1/y)` for all `ρ = (ρ̄, y) ∈ Q − Q₀`.

Stage (4) (`stepFour_cover_of_base`) proves it on the fibre of `ω̄`, and stage (5)
(`stepFive`) spreads it over the remaining `K W`-orbits.  Its hypotheses are the book's:
`ω ∈ Q − Q₀`, `ζ ∈ W^#`, `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W`, together with the numerology
of the model and stage (3) at `ω` (`hstage3`, the relation `ω² = (0, ζ + ζ⁻¹)` read in
the unitary coordinates). -/
theorem proposition_inverseFormula (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
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
    (hmu : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hhW : h ω ∈ hyp.W)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hρQ0 : ρ ∉ hyp.Q0) :
    (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
        = (Ψ ⟨ρ, hρQ⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ :=
  hyp.stepFive H hC2 sfive M hZc Φ hquot ι hker hu Ψ hene hΨq hΨc hconjq hconjy d hequiv
    hdsq hs hm hQ0card hmu hKcard hWdvd hW1 hfQ hωQ hωQ0
    (fun σ hσQ => hyp.stepFour_cover_of_base H hC2 sfive M hZc hmu Φ hquot ι hker hu Ψ
      hene hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hfQ hζ hζ1 hωQ hωQ0 hf hhW
      hstage3 σ hσQ (hfQ σ hσQ))
    hρQ hρQ0

/-- **The inversion formula on `Q₀^#`** (Peterfalvi Part II, Ch. IV §2 (1), p. 123, read
in the unitary coordinates).

The book states the Proposition for `ρ ∈ Q − Q₀`, but the Lemma of §1 compares `f` on the
whole of `Q^#`, so the central elements have to be covered too.  There the formula is step
(1) of §2 rather than anything from §3: writing `ρ = s^k` with `k ∈ K` (`K` is regular on
`Q₀^#`), it says `f(s^k) = s^{k⁻¹}`, and `centerCoord_conj_eq_mu_sq` turns that into
`y ↦ 1/y` once the centre is normalized so that `s = (0, 1)` — which is `hs`.  Both
quotient coordinates are `0`, so the first equation is `0 = 0 / y`. -/
theorem inverseFormula_of_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
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
    {e : M.E}
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hΨc : ∀ ρ : ↥hyp.Q, (Ψ ρ).central = ν * (Φ ρ).central)
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
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ρ : G} (hρQ0 : ρ ∈ hyp.Q0) (hρ1 : ρ ≠ 1) :
    (Ψ ⟨f ρ, hfQ ρ (hyp.Q0_le_Q hρQ0)⟩).quotient
        = (Ψ ⟨ρ, hyp.Q0_le_Q hρQ0⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hyp.Q0_le_Q hρQ0⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ (hyp.Q0_le_Q hρQ0)⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hyp.Q0_le_Q hρQ0⟩))⁻¹ := by
  classical
  -- `ρ = s^k` with `k ∈ K`, and then `f ρ = s^{k⁻¹}`
  obtain ⟨k, hkSet, hkeq⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hρQ0 hρ1
  have hkK : k ∈ hyp.K := by rw [← hyp.coe_K] at hkSet; exact hkSet
  have hkinvK : k⁻¹ ∈ hyp.K := hyp.K.inv_mem hkK
  obtain ⟨hfval, -, -⟩ := hyp.fgh_at_conj_distinguishedInvolution H hC2 hkSet
  rw [hkeq] at hfval
  -- the two central coordinates
  have hcoordρ : hyp.centerCoord sfive M ι hρQ0
      = ((M.mu (hyp.kActor (pow_mem hkinvK 2), 1) : M.Eˣ) : M.E) *
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := by
    have hconj := hyp.centerCoord_conj_eq_mu_sq sfive M ι d hequiv hdsq hkinvK
      hyp.distinguishedInvolution_mem_Q0
    have hmem : k⁻¹ * hyp.distinguishedInvolution * k⁻¹⁻¹ = ρ := by
      rw [inv_inv]; exact hkeq
    simpa only [hmem] using hconj
  have hfρQ0 : f ρ ∈ hyp.Q0 := by
    rw [hfval]
    have := hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hkK) hyp.distinguishedInvolution_mem_Q0
    exact this
  have hcoordf : hyp.centerCoord sfive M ι hfρQ0
      = ((M.mu (hyp.kActor (pow_mem hkK 2), 1) : M.Eˣ) : M.E) *
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := by
    have hconj := hyp.centerCoord_conj_eq_mu_sq sfive M ι d hequiv hdsq hkK
      hyp.distinguishedInvolution_mem_Q0
    simpa only [hfval] using hconj
  -- the two unitary coordinates, using the normalization `s = (0, 1)`
  have hAcoe : ∀ {x : G} (hx : x ∈ hyp.Q0),
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨x, hyp.Q0_le_Q hx⟩)
        = (ν : M.E) * hyp.centerCoord sfive M ι hx := by
    intro x hx
    have h := hyp.unitaryCoord_toCenter sfive M Φ ι hker hu Ψ hΨq hΨc hx
    have hxx : ((hyp.toCenter sfive hx : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q)
        = ⟨x, hyp.Q0_le_Q hx⟩ := Subtype.ext (hyp.toCenter_coe sfive hx)
    rwa [hxx] at h
  have hμinv : ((M.mu (hyp.kActor (pow_mem hkinvK 2), 1) : M.Eˣ) : M.E)
      = (((M.mu (hyp.kActor (pow_mem hkK 2), 1) : M.Eˣ) : M.E))⁻¹ := by
    rw [hyp.kActor_eq_inv (pow_mem hkK 2) (pow_mem hkinvK 2) (by rw [inv_pow]),
      show ((hyp.kActor (pow_mem hkK 2))⁻¹, (1 : ↥hyp.W))
        = ((hyp.kActor (pow_mem hkK 2)), (1 : ↥hyp.W))⁻¹ from
        Prod.ext rfl (inv_one (G := ↥hyp.W)).symm, map_inv, Units.val_inv_eq_inv_val]
  have hUρ : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hyp.Q0_le_Q hρQ0⟩)
      = (((M.mu (hyp.kActor (pow_mem hkK 2), 1) : M.Eˣ) : M.E))⁻¹ := by
    rw [hAcoe hρQ0, hcoordρ, hμinv, ← mul_assoc, mul_comm (ν : M.E), mul_assoc, hs,
      mul_one]
  have hUf : Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hyp.Q0_le_Q hfρQ0⟩)
      = ((M.mu (hyp.kActor (pow_mem hkK 2), 1) : M.Eˣ) : M.E) := by
    rw [hAcoe hfρQ0, hcoordf, ← mul_assoc, mul_comm (ν : M.E), mul_assoc, hs, mul_one]
  -- both quotient coordinates vanish
  have hQz : ∀ {x : G} (hx : x ∈ hyp.Q0),
      (Ψ ⟨x, hyp.Q0_le_Q hx⟩).quotient = 0 := by
    intro x hx
    rw [hΨq, hquot,
      show M.coord (Additive.ofMul (QuotientGroup.mk'
            (Subgroup.center hyp.Q) (⟨x, hyp.Q0_le_Q hx⟩ : ↥hyp.Q)))
          = M.coord (Additive.ofMul
            (QuotientGroup.mk (⟨x, hyp.Q0_le_Q hx⟩ : ↥hyp.Q))) from rfl,
      hyp.coord_mk_eq_zero_of_mem_Q0 M hZc hx (hyp.Q0_le_Q hx), mul_zero]
  have hsub : (⟨f ρ, hfQ ρ (hyp.Q0_le_Q hρQ0)⟩ : ↥hyp.Q) = ⟨f ρ, hyp.Q0_le_Q hfρQ0⟩ := rfl
  refine ⟨?_, ?_⟩
  · rw [hsub, hQz hfρQ0, hQz hρQ0, zero_div]
  · rw [hsub, hUf, hUρ, inv_inv]

/-- **The Proposition of §3 on the whole of `Q^#`** (Peterfalvi Part II, Ch. IV §3,
p. 129, together with §2 (1), p. 123).

The book's Proposition covers `Q − Q₀`; the Lemma of §1 compares `f` on all of `Q^#`, and
on the centre the same formula is step (1) of §2 (`inverseFormula_of_mem_Q0`).  This is
the statement `conjQMulEquivOfData` consumes. -/
theorem proposition_inverseFormula_of_ne_one (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
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
    (hmu : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hhW : h ω ∈ hyp.W)
    (hstage3 : (Ψ ⟨ω, hωQ⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hρ1 : ρ ≠ 1) :
    (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
        = (Ψ ⟨ρ, hρQ⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  by_cases hρQ0 : ρ ∈ hyp.Q0
  · exact hyp.inverseFormula_of_mem_Q0 H hC2 sfive M hZc Φ hquot ι hker hu Ψ hΨq hΨc d
      hequiv hdsq hs hfQ hρQ0 hρ1
  · exact hyp.proposition_inverseFormula H hC2 sfive M hZc Φ hquot ι hker hu Ψ hene hΨq
      hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hmu hKcard hWdvd hW1 hfQ hζ hζ1 hωQ
      hωQ0 hf hhW hstage3 hρQ hρQ0

/-- **The Proposition, read in the root group of `PSU(3, q)`** (Peterfalvi Part II,
Ch. IV §3 (4), p. 131).

`unitaryRootEquiv` carries the two unitary coordinates of `Ψ` to the two coordinates of
`RootGroup q`, and `unitaryRootEquiv_reciprocal` turns the Proposition's pair of
equations into the single statement that `f` is `RootGroup.reciprocal` — which is what
the Lemma of §1 compares with the standard model (`standardModel_f_rootHom`). -/
theorem proposition_reciprocal {m : ℕ}
    (M : hyp.QuotientFieldModel m) (hm : 0 < m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (σ : M.E ≃+* Field m)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ρ : G} (hρQ : ρ ∈ hyp.Q)
    (hA : (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
        = (Ψ ⟨ρ, hρQ⟩).quotient / Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))
    (hB : Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹)
    (h1 : Suzuki2Groups.unitaryRootEquiv hm M.card hu σ (Ψ ⟨ρ, hρQ⟩) ≠ 1) :
    Suzuki2Groups.unitaryRootEquiv hm M.card hu σ (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
      = RootGroup.reciprocal
          (Suzuki2Groups.unitaryRootEquiv hm M.card hu σ (Ψ ⟨ρ, hρQ⟩)) h1 :=
  Suzuki2Groups.unitaryRootEquiv_reciprocal hm M.card hu σ hA hB h1

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
