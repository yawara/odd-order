/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3InverseFormula

/-!
# Peterfalvi Part II, Ch. IV §3 (5): the second case, wired up

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (5), p. 131.

Stage (5) splits: if `ρ̄` lies in the `K W`-orbit of `ω̄` the formula comes from stage
(4) and `stepFive_orbit`; if not, the book instead arranges — using (8) of §2 — that
`f(ρ)` lies in that orbit, and works backwards.  This file carries the second case.

The mathematical content is already in `PSU3StarEquation` and `PSU3InverseFormula`:

* `inverseFormula_symm` — knowing `f` at `f(ρ)` gives `f(ρ) = (ρ̄/x, 1/x)`, since `f` is
  an involution (H2);
* `sectionTwoStepTwo_coords` — §2 (2) read in the unitary coordinates;
* `stepFive_secondCase_at` — the two combined.

What this file adds is the wiring: the coordinates of `f(ρ) s^a` and of `ρ s^{a⁻¹}`,
and the bookkeeping that turns "the formula holds throughout the fibre of `f(ρ)`" into
"the formula holds throughout the fibre of `ρ`".

## Main results

* `Hypothesis.stepFive_secondCase_elem` — the inversion formula at `ρ s^{a⁻¹}`, given it
  on the fibre of `f(ρ)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **Stage (5)'s second case** (Peterfalvi Part II, p. 131).

`hsolved` is the first case, applied on the fibre of `f(ρ)`: it says the inversion
formula holds at every element of `Q` whose quotient coordinate agrees with that of
`f(ρ)`.  Applied at `f(ρ)` itself — where `f` gives back `ρ` by (H2) — it determines the
coordinates of `f(ρ)` as `(ρ̄/x, 1/x)`; applied at `f(ρ) s^a` it gives the inner `f` of
§2 (2).  Out comes the formula at `ρ s^{a⁻¹}`, and as `a` ranges over `K` those sweep
the whole fibre of `ρ` except `ρ` itself, which `hsolved` at `f(ρ)` has already
settled. -/
theorem stepFive_secondCase_elem (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
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
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hρ1 : ρ ≠ 1)
    (hρ0 : (Ψ ⟨ρ, hρQ⟩).quotient ≠ 0)
    (hff : f (f ρ) = ρ)
    (hsolved : ∀ (σ : G) (hσQ : σ ∈ hyp.Q),
      (Ψ ⟨σ, hσQ⟩).quotient = (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient →
        (Ψ ⟨f σ, hfQ σ hσQ⟩).quotient
            = (Ψ ⟨σ, hσQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f σ, hfQ σ hσQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩))⁻¹)
    {a : G} (haK : a ∈ hyp.K) (haKSet : a ∈ hyp.KSet)
    (hne : ρ * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1)
    (hρ'Q : ρ * (a⁻¹ * hyp.distinguishedInvolution * a) ∈ hyp.Q) :
    (Ψ ⟨f (ρ * (a⁻¹ * hyp.distinguishedInvolution * a)),
        hfQ _ hρ'Q⟩).quotient
        = (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩).quotient /
          Suzuki2Groups.unitaryCoord m u
            (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩) ∧
      Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨f (ρ * (a⁻¹ * hyp.distinguishedInvolution * a)), hfQ _ hρ'Q⟩)
        = (Suzuki2Groups.unitaryCoord m u
          (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩))⁻¹ := by
  classical
  have hσQ : f ρ ∈ hyp.Q := hfQ ρ hρQ
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hyp.distinguishedInvolution_mem_Q0
  have hz'Q0 : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hm := hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D (hyp.K.inv_mem haK))
      hyp.distinguishedInvolution_mem_Q0
    rwa [inv_inv] at hm
  have hσzQ : f ρ * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hσQ (hyp.Q0_le_Q hzQ0)
  -- ### the coordinates of `f ρ`
  have hfσ : (⟨f (f ρ), hfQ _ hσQ⟩ : ↥hyp.Q) = ⟨ρ, hρQ⟩ := Subtype.ext hff
  obtain ⟨hb1, hb2⟩ := hsolved (f ρ) hσQ rfl
  rw [hfσ] at hb1 hb2
  have hyσ0 : Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hσQ⟩) ≠ 0 := by
    intro hc
    exact hρ0 (by rw [hb1, hc, div_zero])
  obtain ⟨hσq, hσy⟩ := inverseFormula_symm hyσ0 hb1 hb2
  have hx0 : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ≠ 0 :=
    Suzuki2Groups.unitaryCoord_ne_zero m M.card hu hρ0
  -- ### the inner `f`, at `f(ρ) s^a`
  have hAF : ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 0 :=
    Units.ne_zero _
  have hinnerq : (Ψ ⟨f ρ * (a * hyp.distinguishedInvolution * a⁻¹),
      hσzQ⟩).quotient = (Ψ ⟨f ρ, hσQ⟩).quotient := by
    have hmul : (⟨f ρ * (a * hyp.distinguishedInvolution * a⁻¹), hσzQ⟩ : ↥hyp.Q)
        = (⟨f ρ, hσQ⟩ : ↥hyp.Q) *
          ⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩ := Subtype.ext rfl
    have hcq : (Ψ ⟨a * hyp.distinguishedInvolution * a⁻¹,
        hyp.Q0_le_Q hzQ0⟩).quotient = 0 := by
      rw [show (⟨a * hyp.distinguishedInvolution * a⁻¹, hyp.Q0_le_Q hzQ0⟩ : ↥hyp.Q)
          = ((hyp.toCenter sfive hzQ0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) from rfl,
        hΨq, hker]
      exact mul_zero e
    rw [hmul, map_mul, Suzuki2Groups.BilinearTwistedProduct.quotient_mul, hcq, add_zero]
  have hinnery := hyp.unitaryCoord_mul_conj sfive M Φ ι hker hu Ψ hΨq hΨc d hequiv hdsq
    hs hσQ haK hσzQ
  obtain ⟨hRq, hRy⟩ := hsolved _ hσzQ (hinnerq.trans rfl)
  rw [hinnerq, hinnery, hσq, hσy] at hRq
  rw [hinnery, hσy] at hRy
  -- ### the coordinates of `ρ s^{a⁻¹}`
  have hρ'q : (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩).quotient
      = (Ψ ⟨ρ, hρQ⟩).quotient := by
    have hmul : (⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩ : ↥hyp.Q)
        = (⟨ρ, hρQ⟩ : ↥hyp.Q) *
          ⟨a⁻¹ * hyp.distinguishedInvolution * a, hyp.Q0_le_Q hz'Q0⟩ := Subtype.ext rfl
    have hcq : (Ψ ⟨a⁻¹ * hyp.distinguishedInvolution * a,
        hyp.Q0_le_Q hz'Q0⟩).quotient = 0 := by
      rw [show (⟨a⁻¹ * hyp.distinguishedInvolution * a, hyp.Q0_le_Q hz'Q0⟩ : ↥hyp.Q)
          = ((hyp.toCenter sfive hz'Q0 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) from rfl,
        hΨq, hker]
      exact mul_zero e
    rw [hmul, map_mul, Suzuki2Groups.BilinearTwistedProduct.quotient_mul, hcq, add_zero]
  have hprodQ : ρ * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹) ∈ hyp.Q := by
    rwa [inv_inv]
  have hρ'y0 := hyp.unitaryCoord_mul_conj sfive M Φ ι hker hu Ψ hΨq hΨc d hequiv hdsq
    hs hρQ (hyp.K.inv_mem haK) hprodQ
  rw [hyp.mu_kActor_sq_inv M haK] at hρ'y0
  have hEqQ : (⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩ : ↥hyp.Q)
      = ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹), hprodQ⟩ :=
    Subtype.ext (by
      change ρ * (a⁻¹ * hyp.distinguishedInvolution * a)
        = ρ * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹)
      group)
  have hρ'y : Suzuki2Groups.unitaryCoord m u
      (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hρ'Q⟩)
      = Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
        + ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹ := by
    rw [hEqQ]
    exact hρ'y0
  have hxA : Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩)
      + ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹ ≠ 0 := by
    rw [← hρ'y]
    exact Suzuki2Groups.unitaryCoord_ne_zero m M.card hu (by rw [hρ'q]; exact hρ0)
  -- ### §2 (2) and the composition
  obtain ⟨hLq, hLy⟩ := hyp.sectionTwoStepTwo_coords H hC2 sfive M Φ ι hker hu Ψ hΨq hΨc
    hconjq hconjy d hequiv hdsq hs haK haKSet hρQ hρ1 hne (hfQ _ hρ'Q) (hfQ _ hσzQ)
  exact hyp.stepFive_secondCase_at M hu Ψ hAF hx0 hxA hLq hLy hRq hRy hρ'q hρ'y

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
