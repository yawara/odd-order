/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepTwenty

/-!
# Peterfalvi Part II, Ch. IV §3: determination of `f`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 129–134.

> **Proposition.** Suppose that there are elements `ω ∈ Q − Q₀` and `ζ ∈ W^#` such that
> `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W`.  Then `θ = 1` and `f(ρ) = (ρ̄/y, 1/y)` for all
> `ρ = (ρ̄, y) ∈ Q − Q₀`.

Both hypotheses are supplied by §2: `f_eq_conj_inv_of_stepTwenty_chain` and `h_mem_W`.

This file starts the proof.  Its first stage (the book's (1), p. 130) opens with the
computation `(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`, which is three applications of (H3) to the
hypothesis, and then reads off `h(ω⁻¹) = ζ⁻³` from (H5) — a step the book justifies by
`h(ω⁻¹) = h(ω)^{-t} ∈ W`, and which here is again the freeness of the `D`-action.

## Main results

* `Hypothesis.fj_cube_of_f_eq_conj_inv` — `(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`.
* `Hypothesis.f_inv_eq`, `Hypothesis.g_inv_eq` — `f(ω⁻¹) = ω^{ζ⁻¹}` and
  `g(ω⁻¹) = ω^ζ`.
* `Hypothesis.h_inv_eq` — `h(ω⁻¹) = ζ⁻³`.
* `Hypothesis.h_eq_zpow_three` — `h(ω) = ζ³`, given `h(ω) ∈ W`.
* `Hypothesis.stepOne_chain` — §3's stage (1).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- `t` centralizes every power of an element of `W`. -/
theorem conj_t_pow_eq {ζ : G} (hζ : ζ ∈ hyp.W) (n : ℕ) :
    hyp.t * ζ ^ n * hyp.t = ζ ^ n := by
  have hc : Commute ζ hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hζ)
  rw [← (hc.pow_left n).eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]

/-- **`(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`** (Peterfalvi Part II, p. 130, opening of §3's stage (1)).

Each of the three steps is (H3) applied to `f(ω) = (ω⁻¹)^ζ`, the twist `a ↦ a^t` being
trivial on `W`. -/
theorem fj_cube_of_f_eq_conj_inv (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    f ((f ((f ω)⁻¹))⁻¹) = (ζ ^ 3)⁻¹ * ω⁻¹ * ζ ^ 3 := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωQ hω1 hζD
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  rw [htζt] at h3
  -- second step
  have e2 : f ((f ω)⁻¹) = (ζ ^ 2)⁻¹ * ω⁻¹ * ζ ^ 2 := by
    have hinv1 : (f ω)⁻¹ = ζ⁻¹ * ω * ζ := by rw [hf]; group
    rw [hinv1, h3, hf, pow_two]
    group
  -- third step, by (H3) at `ζ²`
  have hζ2D : ζ ^ 2 ∈ hyp.D := pow_mem hζD 2
  obtain ⟨h3'', -, -⟩ := hThree hyp.rankOneSetup H hωQ hω1 hζ2D
  rw [hyp.conj_t_pow_eq hζ 2] at h3''
  have hinv2 : (f ((f ω)⁻¹))⁻¹ = (ζ ^ 2)⁻¹ * ω * ζ ^ 2 := by rw [e2]; group
  rw [hinv2, h3'', hf, pow_two, pow_three']
  group

/-- **`f(ω⁻¹) = ω^{ζ⁻¹}`** (Peterfalvi Part II, p. 130): applying `f` to the hypothesis
`f(ω) = (ω⁻¹)^ζ` and moving the conjugation across by (H3). -/
theorem f_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    f ω⁻¹ = ζ * ω * ζ⁻¹ := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωinvQ hωinv1 hζD
  rw [htζt] at h3
  have h2 : f (f ω) = ω := (hTwo hyp.rankOneSetup H hωQ hω1).1
  rw [hf, h3] at h2
  calc f ω⁻¹ = ζ * (ζ⁻¹ * f ω⁻¹ * ζ) * ζ⁻¹ := by group
    _ = ζ * ω * ζ⁻¹ := by rw [h2]

/-- **`g(ω⁻¹) = ω^ζ`** (Peterfalvi Part II, p. 130): (H1) says `g(x⁻¹) = f(x)⁻¹`. -/
theorem g_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    g ω⁻¹ = ζ⁻¹ * ω * ζ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨-, o2, -⟩ := hOne hyp.rankOneSetup H hωQ hω1
  rw [o2, hf]
  group

/-- **`h(ω⁻¹) = ζ⁻³`** (Peterfalvi Part II, p. 130).

(H5) says `(f ∘ j)³(ω⁻¹) = (ω⁻¹)^{h(ω⁻¹)⁻¹}`, and the left side is `ω^{-ζ³}`; so
`ζ³ h(ω⁻¹) ∈ D` fixes `ω⁻¹`, hence is trivial by `eq_one_of_conj_eq_mul_Q0_of_mem_D`.

The book instead argues that `h(ω⁻¹) = h(ω)^{-t}` lies in `W` and reads the exponent off
there; the freeness makes the detour unnecessary. -/
theorem h_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    h ω⁻¹ = (ζ ^ 3)⁻¹ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinvQ0 : ω⁻¹ ∉ hyp.Q0 := fun hc => hωQ0 (by simpa using hyp.Q0.inv_mem hc)
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  -- (H5) at `ω⁻¹`, whose `j` is `ω`
  have h5 := hFive hyp.rankOneSetup H hωinvQ hωinv1
  rw [inv_inv, hyp.fj_cube_of_f_eq_conj_inv H hζ hωQ hωQ0 hf] at h5
  -- `ζ³ · h(ω⁻¹)` fixes `ω⁻¹`
  have hζ3D : ζ ^ 3 ∈ hyp.D := pow_mem (hyp.V_le_D (hyp.W_le_V hζ)) 3
  have hhD : h ω⁻¹ ∈ hyp.D := H.h_mem hωinvQ hωinv1
  have hcD : ζ ^ 3 * h ω⁻¹ ∈ hyp.D := hyp.D.mul_mem hζ3D hhD
  have hconj : (ζ ^ 3 * h ω⁻¹)⁻¹ * ω⁻¹ * (ζ ^ 3 * h ω⁻¹) = ω⁻¹ * 1 := by
    rw [mul_one]
    calc (ζ ^ 3 * h ω⁻¹)⁻¹ * ω⁻¹ * (ζ ^ 3 * h ω⁻¹)
        = (h ω⁻¹)⁻¹ * ((ζ ^ 3)⁻¹ * ω⁻¹ * ζ ^ 3) * h ω⁻¹ := by group
      _ = (h ω⁻¹)⁻¹ * (h ω⁻¹ * ω⁻¹ * (h ω⁻¹)⁻¹) * h ω⁻¹ := by rw [← h5]
      _ = ω⁻¹ := by group
  have hone := hyp.eq_one_of_conj_eq_mul_Q0_of_mem_D M hZ hmu hVW hωinvQ hωinvQ0 hcD
    hyp.Q0.one_mem hconj
  calc h ω⁻¹ = (ζ ^ 3)⁻¹ * (ζ ^ 3 * h ω⁻¹) := by group
    _ = (ζ ^ 3)⁻¹ := by rw [hone, mul_one]

/-- **`h(ω) = ζ³`** (Peterfalvi Part II, p. 130): with `h(ω) ∈ W`, the twist `a ↦ a^t` of
(H1) is trivial, so `h(ω⁻¹) = h(ω)⁻¹`. -/
theorem h_eq_zpow_three (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hhW : h ω ∈ hyp.W) :
    h ω = ζ ^ 3 := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨-, -, o3⟩ := hOne hyp.rankOneSetup H hωQ hω1
  have hth : hyp.t * h ω * hyp.t = h ω := by
    have hc : Commute (h ω) hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hhW)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  rw [hth] at o3
  have hkey := hyp.h_inv_eq H M hZ hmu hVW hζ hωQ hωQ0 hf
  rw [o3] at hkey
  exact inv_injective hkey

/-- **§3, stage (1)** (Peterfalvi Part II, p. 130):

  `f(ω^{ζ⁻¹} s^{a⁻¹})^{a²} s^a = f(ω^ζ s^a)^{ζ⁻³} ω^{ζ⁻¹}`   for `a ∈ K`.

Both sides are the same element `f(ω⁻¹ s^a)`, read through the two halves of (H6) that
§2 packaged as its steps (2) and (3) — the left through
`f_mul_conj_distinguishedInvolution`, the right through
`f_conj_distinguishedInvolution_mul`.  What makes them meet is that the conjugates of
`s` lie in `Q₀ = Z(Q)`, so the two orders of the product agree; the substitutions are
`f(ω⁻¹) = ω^{ζ⁻¹}`, `g(ω⁻¹) = ω^ζ` and `h(ω⁻¹) = ζ⁻³`, whose `t`-twist is again `ζ⁻³`
because `ζ ∈ W`. -/
theorem stepOne_chain (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    a ^ 2 * f ((ζ * ω * ζ⁻¹) * (a * hyp.distinguishedInvolution * a⁻¹)) * (a⁻¹) ^ 2
        * (a * hyp.distinguishedInvolution * a⁻¹)
      = (ζ ^ 3) * f ((a * hyp.distinguishedInvolution * a⁻¹) * (ζ⁻¹ * ω * ζ))
        * (ζ ^ 3)⁻¹ * (ζ * ω * ζ⁻¹) := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinvQ0 : ω⁻¹ ∉ hyp.Q0 := fun hc => hωQ0 (by simpa using hyp.Q0.inv_mem hc)
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  have hsaQ0 : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haK.1) hsQ0
    rwa [inv_inv] at hmem
  obtain ⟨-, hprodQ0⟩ := hyp.mul_mem_sdiff_Q0 hωinvQ hωinvQ0 hsaQ0
  have hne1 : ω⁻¹ * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 :=
    fun hc => hprodQ0 (hc ▸ hyp.Q0.one_mem)
  -- the two orders of the product agree, `s^a` being central in `Q`
  have hcomm : ω⁻¹ * (a⁻¹ * hyp.distinguishedInvolution * a)
      = (a⁻¹ * hyp.distinguishedInvolution * a) * ω⁻¹ :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hsaQ0) ω⁻¹ hωinvQ
  have hne2 : (a⁻¹ * hyp.distinguishedInvolution * a) * ω⁻¹ ≠ 1 := by
    rw [← hcomm]; exact hne1
  -- the two readings of `f(ω⁻¹ s^a)`
  have hA := hyp.f_mul_conj_distinguishedInvolution H hC2 haK hωinvQ hωinv1 hne1
  have hB := hyp.f_conj_distinguishedInvolution_mul H hC2 haK hωinvQ hωinv1 hne2
  rw [← hcomm] at hB
  rw [hyp.f_inv_eq H hζ hωQ hωQ0 hf] at hA
  rw [hyp.g_inv_eq H hωQ hωQ0 hf, hyp.f_inv_eq H hζ hωQ hωQ0 hf,
    hyp.h_inv_eq H M hZ hmu hVW hζ hωQ hωQ0 hf] at hB
  -- the `t`-twist of `ζ⁻³` is `ζ⁻³`
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right hyp.rankOneSetup.invol
  have htw : hyp.t * (ζ ^ 3)⁻¹ * hyp.t = (ζ ^ 3)⁻¹ := by
    have hp := hyp.conj_t_pow_eq hζ 3
    calc hyp.t * (ζ ^ 3)⁻¹ * hyp.t = (hyp.t⁻¹ * ζ ^ 3 * hyp.t⁻¹)⁻¹ := by group
      _ = (hyp.t * ζ ^ 3 * hyp.t)⁻¹ := by rw [htinv]
      _ = (ζ ^ 3)⁻¹ := by rw [hp]
  rw [htw, inv_inv] at hB
  exact hA.symm.trans hB

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
