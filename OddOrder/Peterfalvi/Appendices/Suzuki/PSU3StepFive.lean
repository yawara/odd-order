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

* `Hypothesis.stepFive_of_mem_orbit` — the first case, packaged: the formula at every
  `K W`-translate of `ω`'s fibre.
* `Hypothesis.stepFive_secondCase_elem` — the second case: the inversion formula at
  `ρ s^{a⁻¹}`, given it on the fibre of `f(ρ)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **Every `conjQHom kv` is a `conjQHom` at an explicit element of `K`.**

`actualKActor` is the range of `conjQByK`, so its elements come from `K`; the statements
of §2 and §3 that name `k ∈ G` explicitly — `conjQHom_kActor_apply_val`, hence
`stepFive_orbit` — therefore apply to an arbitrary `kv`.

This is the bridge from the orbit condition, which lives in `E^× ⧸ μ(K W)` and so
produces an abstract `kv`, to the group-level statements. -/
theorem exists_mem_K_conjQHom_eq (kv : ↥hyp.actualKActor × ↥hyp.W) :
    ∃ (k : G) (hk : k ∈ hyp.K),
      (hyp.kActor hk, kv.2) = kv := by
  obtain ⟨x, hx⟩ := kv.1.2
  exact ⟨(x : G), x.2, Prod.ext (Subtype.ext hx) rfl⟩

/-- **Pulling back along a `K W`-translate**: if `ρ`'s quotient coordinate is `μ(kv)`
times `ω`'s, then `ρ` is the `kv`-conjugate of an element in `ω`'s fibre.

This is the first case of stage (5) in usable form: "`ρ̄` lies in the orbit of `ω̄` under
`K W`" is a statement about coordinates, and this turns it into a group-level conjugacy
so that `stepFive_orbit` applies. -/
theorem exists_conjQHom_eq_of_quotient_smul {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (kv : ↥hyp.actualKActor × ↥hyp.W) {p q : ↥hyp.Q}
    (h : (Ψ p).quotient = ((M.mu kv : M.Eˣ) : M.E) * (Ψ q).quotient) :
    ∃ σ : ↥hyp.Q, (Ψ σ).quotient = (Ψ q).quotient ∧ hyp.conjQHom kv σ = p := by
  refine ⟨hyp.conjQHom kv⁻¹ p, ?_, ?_⟩
  · rw [hconjq, h, map_inv, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero (M.mu kv)), one_mul]
  · rw [map_inv]
    exact (hyp.conjQHom kv).apply_symm_apply p

/-- **Stage (5)'s first case, packaged** (Peterfalvi Part II, p. 131: "If `ρ̄` is in the
orbit of `ω̄` under `K W`, then (5) follows from (4)").

`hcover` is stage (4) on the fibre of `ω̄` (`stepFour_cover`).  If `ρ`'s quotient
coordinate is `μ(kv)` times `ω`'s, then `ρ` is the `kv`-conjugate of a point of that
fibre (`exists_conjQHom_eq_of_quotient_smul`), and `stepFive_orbit` carries the formula
across. -/
theorem stepFive_of_mem_orbit (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    (hconjq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      (Ψ (hyp.conjQHom kv ρ)).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ρ).quotient)
    (hconjy : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W) (ρ : ↥hyp.Q),
      Suzuki2Groups.unitaryCoord m u (Ψ (hyp.conjQHom kv ρ))
        = ((M.mu kv : M.Eˣ) : M.E) ^ (2 ^ m + 1) *
          Suzuki2Groups.unitaryCoord m u (Ψ ρ))
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q)
    (hcover : ∀ (σ : G) (hσQ : σ ∈ hyp.Q),
      (Ψ ⟨σ, hσQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
        (Ψ ⟨f σ, hfQ σ hσQ⟩).quotient
            = (Ψ ⟨σ, hσQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f σ, hfQ σ hσQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩))⁻¹)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hω0 : (Ψ ⟨ω, hωQ⟩).quotient ≠ 0)
    (kv : ↥hyp.actualKActor × ↥hyp.W)
    (hkv : (Ψ ⟨ρ, hρQ⟩).quotient
      = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ⟨ω, hωQ⟩).quotient) :
    (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
        = (Ψ ⟨ρ, hρQ⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  classical
  obtain ⟨k, hkK, hkveq⟩ := hyp.exists_mem_K_conjQHom_eq kv
  rw [← hkveq] at hkv
  obtain ⟨σ, hσq, hσeq⟩ := hyp.exists_conjQHom_eq_of_quotient_smul M hu Ψ hconjq _ hkv
  have hkSet : k ∈ hyp.KSet := by rw [← hyp.coe_K]; exact hkK
  -- the conjugate, at the group level
  have hval : k * (kv.2 : G) * (σ : G) * (k * (kv.2 : G))⁻¹ = ρ := by
    have h := congrArg (Subtype.val (p := fun x => x ∈ hyp.Q)) hσeq
    rw [hyp.conjQHom_kActor_apply_val hkK kv.2.2 σ] at h
    exact h
  have hσ1 : (σ : G) ≠ 1 := by
    intro hc
    have hone : σ = 1 := Subtype.ext hc
    rw [hone, map_one, Suzuki2Groups.BilinearTwistedProduct.quotient_one] at hσq
    exact hω0 hσq.symm
  have hy : Suzuki2Groups.unitaryCoord m u (Ψ σ) ≠ 0 := by
    refine Suzuki2Groups.unitaryCoord_ne_zero m M.card hu ?_
    rw [hσq]
    exact hω0
  obtain ⟨hc1, hc2⟩ := hcover (σ : G) σ.2 hσq
  have hρ'Q : k * (kv.2 : G) * (σ : G) * (k * (kv.2 : G))⁻¹ ∈ hyp.Q := by
    rw [hval]; exact hρQ
  obtain ⟨e1, e2⟩ := hyp.stepFive_orbit H M hu Ψ hconjq hconjy hkSet hkK kv.2.2
    σ.2 hσ1 (hfQ _ σ.2) hρ'Q (hfQ _ hρ'Q) hy hc1 hc2
  have hQeq : (⟨k * (kv.2 : G) * (σ : G) * (k * (kv.2 : G))⁻¹, hρ'Q⟩ : ↥hyp.Q)
      = ⟨ρ, hρQ⟩ := Subtype.ext hval
  have hFeq : (⟨f (k * (kv.2 : G) * (σ : G) * (k * (kv.2 : G))⁻¹),
      hfQ _ hρ'Q⟩ : ↥hyp.Q) = ⟨f ρ, hfQ ρ hρQ⟩ := Subtype.ext (congrArg f hval)
  rw [hQeq, hFeq] at e1 e2
  exact ⟨e1, e2⟩

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

/-- **From the points `ρ s^{a⁻¹}` to the whole fibre of `ρ`.**

`stepFive_secondCase_elem` produces the formula one shift at a time; the fibre of `ρ` is
`{ρ} ∪ {ρ s^a : a ∈ K}` (`eq_or_exists_conj_mul_of_quotient_eq`), and `s^a = s^{(a⁻¹)⁻¹}`,
so the two together cover it. -/
theorem stepFive_secondCase_fibre {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    {u : M.E} (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
    (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
      (OddOrder.FiniteField.hermitianCocycle m M.card hu))
    {e : M.E} (hene : e ≠ 0)
    (hΨq : ∀ ρ : ↥hyp.Q, (Ψ ρ).quotient = e * (Φ ρ).quotient)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ρ : G} (hρQ : ρ ∈ hyp.Q)
    (hbase : (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
          = (Ψ ⟨ρ, hρQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹)
    (hstep : ∀ (a : G), a ∈ hyp.K →
      ∀ hQ : ρ * (a⁻¹ * hyp.distinguishedInvolution * a) ∈ hyp.Q,
        (Ψ ⟨f (ρ * (a⁻¹ * hyp.distinguishedInvolution * a)), hfQ _ hQ⟩).quotient
            = (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u
                (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u
              (Ψ ⟨f (ρ * (a⁻¹ * hyp.distinguishedInvolution * a)), hfQ _ hQ⟩)
            = (Suzuki2Groups.unitaryCoord m u
              (Ψ ⟨ρ * (a⁻¹ * hyp.distinguishedInvolution * a), hQ⟩))⁻¹)
    {τ : G} (hτQ : τ ∈ hyp.Q)
    (hfib : (Ψ ⟨τ, hτQ⟩).quotient = (Ψ ⟨ρ, hρQ⟩).quotient) :
    (Ψ ⟨f τ, hfQ τ hτQ⟩).quotient
        = (Ψ ⟨τ, hτQ⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨τ, hτQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f τ, hfQ τ hτQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨τ, hτQ⟩))⁻¹ := by
  obtain hcase | ⟨a, haK, hτeq⟩ :=
    hyp.eq_or_exists_conj_mul_of_quotient_eq M hZc Φ hquot hu Ψ hene hΨq hτQ hρQ hfib
  · subst hcase
    exact hbase
  · subst hτeq
    have hQ : ρ * (a⁻¹⁻¹ * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q := by
      rwa [inv_inv]
    obtain ⟨e1, e2⟩ := hstep a⁻¹ (hyp.K.inv_mem haK) hQ
    have hQeq : (⟨ρ * (a * hyp.distinguishedInvolution * a⁻¹), hτQ⟩ : ↥hyp.Q)
        = ⟨ρ * (a⁻¹⁻¹ * hyp.distinguishedInvolution * a⁻¹), hQ⟩ :=
      Subtype.ext (by
        change ρ * (a * hyp.distinguishedInvolution * a⁻¹)
          = ρ * (a⁻¹⁻¹ * hyp.distinguishedInvolution * a⁻¹)
        group)
    have hFeq : (⟨f (ρ * (a * hyp.distinguishedInvolution * a⁻¹)),
        hfQ _ hτQ⟩ : ↥hyp.Q)
        = ⟨f (ρ * (a⁻¹⁻¹ * hyp.distinguishedInvolution * a⁻¹)), hfQ _ hQ⟩ :=
      Subtype.ext (congrArg f (by group))
    rw [hQeq, hFeq]
    exact ⟨e1, e2⟩

/-- **Stage (5)** (Peterfalvi Part II, Ch. IV §3 (5), p. 131), complete: for every
`ρ ∈ Q − Q₀` the map `f` is given in unitary coordinates by `f(ρ̄, y) = (ρ̄/y, 1/y)`.

The book splits into two cases and so does this proof.

* If `ρ̄` lies in the `K W`-orbit of `ω̄` — the orbit on which stage (4) has already
  established the formula, here supplied as `hcover` — then `stepFive_of_mem_orbit`
  transports it.
* Otherwise, "possibly on replacing `ρ` by an element of `ρ Q₀`, we may assume by (8) of
  §2 that `f(ρ)` is in the orbit of `ω̄`": `exists_mem_Q0_orbitOfF_eq` produces the
  `x ∈ Q₀` with `f(ρ x)` in that orbit, so the formula holds throughout the fibre of
  `f(ρ x)`; `inverseFormula_symm` reads it back at `ρ x` itself and
  `stepFive_secondCase_elem` / `stepFive_secondCase_fibre` walk it out to the whole
  fibre of `ρ x`, which contains `ρ`.

Note that the orbit condition depends on `ρ` only through its quotient coordinate, which
is why the *whole* fibre of `f(ρ x)` comes for free in the second case — that is exactly
the `hsolved` hypothesis of `stepFive_secondCase_elem`. -/
theorem stepFive (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
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
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hcover : ∀ (σ : G) (hσQ : σ ∈ hyp.Q),
      (Ψ ⟨σ, hσQ⟩).quotient = (Ψ ⟨ω, hωQ⟩).quotient →
        (Ψ ⟨f σ, hfQ σ hσQ⟩).quotient
            = (Ψ ⟨σ, hσQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f σ, hfQ σ hσQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩))⁻¹)
    {ρ : G} (hρQ : ρ ∈ hyp.Q) (hρQ0 : ρ ∉ hyp.Q0) :
    (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
        = (Ψ ⟨ρ, hρQ⟩).quotient /
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
      Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
        = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  classical
  -- off `Q₀` the quotient coordinate is nonzero
  have hne0 : ∀ (τ : G) (hτQ : τ ∈ hyp.Q), τ ∉ hyp.Q0 →
      (Ψ ⟨τ, hτQ⟩).quotient ≠ 0 := by
    intro τ hτQ hτQ0 hc
    rw [hΨq, hquot] at hc
    rcases mul_eq_zero.mp hc with h0 | h0
    · exact hene h0
    · exact hyp.coord_ne_zero_of_not_mem_Q0 M hZc hτQ hτQ0 h0
  have hω0 : (Ψ ⟨ω, hωQ⟩).quotient ≠ 0 := hne0 ω hωQ hωQ0
  -- the formula holds at every point of `Q` in the `K W`-orbit of `ω`
  have key : ∀ (τ : G) (hτQ : τ ∈ hyp.Q),
      (∃ kv : ↥hyp.actualKActor × ↥hyp.W, (Ψ ⟨τ, hτQ⟩).quotient
        = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ⟨ω, hωQ⟩).quotient) →
      ((Ψ ⟨f τ, hfQ τ hτQ⟩).quotient
          = (Ψ ⟨τ, hτQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨τ, hτQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f τ, hfQ τ hτQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨τ, hτQ⟩))⁻¹) := by
    rintro τ hτQ ⟨kv, hkv⟩
    exact hyp.stepFive_of_mem_orbit H M hu Ψ hconjq hconjy hfQ hωQ hcover hτQ hω0 kv hkv
  by_cases horb : ∃ kv : ↥hyp.actualKActor × ↥hyp.W, (Ψ ⟨ρ, hρQ⟩).quotient
      = ((M.mu kv : M.Eˣ) : M.E) * (Ψ ⟨ω, hωQ⟩).quotient
  · exact key ρ hρQ horb
  -- ### the second case: move inside the fibre of `ρ` so that `f` lands in the orbit
  obtain ⟨x, hx⟩ := hyp.exists_mem_Q0_orbitOfF_eq M hZc H hC2 hVW hm hQ0card hinj
    hKcard hWdvd hW1 hρQ hρQ0 (QuotientGroup.mk (hyp.baseUnit M hZc hωQ hωQ0))
  obtain ⟨hρxQ, hρxQ0⟩ := hyp.mul_mem_sdiff_Q0 hρQ hρQ0 x.2
  have hρx0 : (Ψ ⟨ρ * (x : G), hρxQ⟩).quotient ≠ 0 := hne0 _ hρxQ hρxQ0
  have hρx1 : ρ * (x : G) ≠ 1 := by
    intro hc
    exact hρxQ0 (by rw [hc]; exact hyp.Q0.one_mem)
  have hff : f (f (ρ * (x : G))) = ρ * (x : G) :=
    (hTwo hyp.rankOneSetup H hρxQ hρx1).1
  -- `f(ρ x)` lies in the orbit of `ω`, read off the coordinates
  have hΨf : (Ψ ⟨f (ρ * (x : G)), hfQ _ hρxQ⟩).quotient
      = e * ((hyp.fUnit M hZc H hC2 hρQ hρQ0 x : M.Eˣ) : M.E) := by
    rw [hΨq, hquot, hyp.fUnit_val]
    rfl
  have hΨω : (Ψ ⟨ω, hωQ⟩).quotient
      = e * ((hyp.baseUnit M hZc hωQ hωQ0 : M.Eˣ) : M.E) := by
    rw [hΨq, hquot, hyp.baseUnit_val]
    rfl
  have hmk : (QuotientGroup.mk (hyp.fUnit M hZc H hC2 hρQ hρQ0 x)
      : M.Eˣ ⧸ MonoidHom.range M.mu)
      = QuotientGroup.mk (hyp.baseUnit M hZc hωQ hωQ0) := hx
  obtain ⟨kv, hkv⟩ := QuotientGroup.eq.mp hmk
  have hprod : hyp.fUnit M hZc H hC2 hρQ hρQ0 x * M.mu kv
      = hyp.baseUnit M hZc hωQ hωQ0 := by rw [hkv, mul_inv_cancel_left]
  have hfb : hyp.fUnit M hZc H hC2 hρQ hρQ0 x
      = M.mu kv⁻¹ * hyp.baseUnit M hZc hωQ hωQ0 := by
    rw [map_inv, ← hprod, mul_comm (hyp.fUnit M hZc H hC2 hρQ hρQ0 x) (M.mu kv),
      inv_mul_cancel_left]
  have hforb : (Ψ ⟨f (ρ * (x : G)), hfQ _ hρxQ⟩).quotient
      = ((M.mu kv⁻¹ : M.Eˣ) : M.E) * (Ψ ⟨ω, hωQ⟩).quotient := by
    rw [hΨf, hΨω, hfb, Units.val_mul]; ring
  -- hence the formula throughout the fibre of `f(ρ x)`
  have hsolved : ∀ (σ : G) (hσQ : σ ∈ hyp.Q),
      (Ψ ⟨σ, hσQ⟩).quotient = (Ψ ⟨f (ρ * (x : G)), hfQ _ hρxQ⟩).quotient →
      ((Ψ ⟨f σ, hfQ σ hσQ⟩).quotient
          = (Ψ ⟨σ, hσQ⟩).quotient /
            Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩) ∧
        Suzuki2Groups.unitaryCoord m u (Ψ ⟨f σ, hfQ σ hσQ⟩)
          = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩))⁻¹) :=
    fun σ hσQ hfib => key σ hσQ ⟨kv⁻¹, hfib.trans hforb⟩
  -- at `f(ρ x)` itself the formula inverts (H2), giving the base point of the fibre
  obtain ⟨hb1, hb2⟩ := hsolved (f (ρ * (x : G))) (hfQ _ hρxQ) rfl
  have hfσ : (⟨f (f (ρ * (x : G))), hfQ _ (hfQ _ hρxQ)⟩ : ↥hyp.Q)
      = ⟨ρ * (x : G), hρxQ⟩ := Subtype.ext hff
  rw [hfσ] at hb1 hb2
  have hyσ0 : Suzuki2Groups.unitaryCoord m u
      (Ψ ⟨f (ρ * (x : G)), hfQ _ hρxQ⟩) ≠ 0 := by
    intro hc
    exact hρx0 (by rw [hb1, hc, div_zero])
  have hbase := inverseFormula_symm hyσ0 hb1 hb2
  -- and the shifts `ρ x s^{a⁻¹}` sweep the rest of the fibre
  have hstep : ∀ a : G, a ∈ hyp.K →
      ∀ hQ : ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a) ∈ hyp.Q,
        (Ψ ⟨f (ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a)),
            hfQ _ hQ⟩).quotient
            = (Ψ ⟨ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a),
                hQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u
                (Ψ ⟨ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a), hQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u
              (Ψ ⟨f (ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a)),
                hfQ _ hQ⟩)
            = (Suzuki2Groups.unitaryCoord m u
              (Ψ ⟨ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a),
                hQ⟩))⁻¹ := by
    intro a haK hQ
    have haKSet : a ∈ hyp.KSet := by rw [← hyp.coe_K]; exact haK
    have hz'Q0 : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
      have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D (hyp.K.inv_mem haK))
        hyp.distinguishedInvolution_mem_Q0
      rwa [inv_inv] at hmem
    have hne : ρ * (x : G) * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 := by
      intro hc
      refine hρxQ0 ?_
      have hz : ρ * (x : G) = (a⁻¹ * hyp.distinguishedInvolution * a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; exact hc
      rw [hz]
      exact hyp.Q0.inv_mem hz'Q0
    exact hyp.stepFive_secondCase_elem H hC2 sfive M Φ ι hker hu Ψ hΨq hΨc hconjq
      hconjy d hequiv hdsq hs hfQ hρxQ hρx1 hρx0 hff hsolved haK haKSet hne hQ
  -- `ρ` lies in that fibre, since `x ∈ Q₀` is central
  have hfibρ : (Ψ ⟨ρ, hρQ⟩).quotient = (Ψ ⟨ρ * (x : G), hρxQ⟩).quotient := by
    have hmul : (⟨ρ * (x : G), hρxQ⟩ : ↥hyp.Q)
        = (⟨ρ, hρQ⟩ : ↥hyp.Q) * ⟨(x : G), hyp.Q0_le_Q x.2⟩ := Subtype.ext rfl
    have hcq : (Ψ ⟨(x : G), hyp.Q0_le_Q x.2⟩).quotient = 0 := by
      rw [show (⟨(x : G), hyp.Q0_le_Q x.2⟩ : ↥hyp.Q)
          = ((hyp.toCenter sfive x.2 : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) from rfl,
        hΨq, hker]
      exact mul_zero e
    rw [hmul, map_mul, Suzuki2Groups.BilinearTwistedProduct.quotient_mul, hcq, add_zero]
  exact hyp.stepFive_secondCase_fibre M hZc Φ hquot hu Ψ hene hΨq hfQ hρxQ hbase hstep
    hρQ hfibρ

/-- **Peterfalvi Part II, Ch. IV §3, Corollary 2** (p. 132), unconditional.

`corollaryTwo` takes stage (5) as the hypothesis `hfive`; `stepFive` now proves it from
stage (4), so this is the same statement with only stage (4) — the cover `hcover` of the
fibre of a single `ω₀ ∈ Q − Q₀` — left as an input.

That input is where §3 as a whole rests: everything else here is the standing data of
§2 (the field model `M`, the two twisted-product coordinatizations `Φ`, `Ψ` and their
comparison `e`, `ν`, the scalar action `μ` of `K W`) together with the numerology
`|Q₀| = 2^m`, `|K| = 2^m − 1`, `|W| ∣ 2^m + 1`, `1 < |W|` that step (8) counts with. -/
theorem corollaryTwo_of_stepFour (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hVW : hyp.V = hyp.W)
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
    {ω₀ : G} (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0)
    (hcover : ∀ (σ : G) (hσQ : σ ∈ hyp.Q),
      (Ψ ⟨σ, hσQ⟩).quotient = (Ψ ⟨ω₀, hω₀Q⟩).quotient →
        (Ψ ⟨f σ, hfQ σ hσQ⟩).quotient
            = (Ψ ⟨σ, hσQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f σ, hfQ σ hσQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨σ, hσQ⟩))⁻¹)
    (hhW : ∀ ρ : G, ρ ∈ hyp.Q → ρ ∉ hyp.Q0 → h ρ ∈ hyp.W)
    {ζ : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ ∧ h ω = ζ ^ 3 :=
  hyp.corollaryTwo H M hZc hVW Φ hquot hu Ψ hΨq hconjq hconjy hmu hζ hζ1 hfQ
    (fun _ρ hρQ hρQ0 => hyp.stepFive H hC2 sfive M hZc Φ hquot ι hker hu Ψ hene hΨq hΨc
      hconjq hconjy d hequiv hdsq hs hVW hm hQ0card hmu hKcard hWdvd hW1 hfQ hω₀Q hω₀Q0
      hcover hρQ hρQ0)
    hhW

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
