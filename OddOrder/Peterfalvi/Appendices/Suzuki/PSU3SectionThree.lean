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
* `Hypothesis.f_conj_zeta_of_mem_Q0` — the two `f`-values of stage (1) as `ζ^{±1}`-conjugates
  of `f(ω s^a)`.
* `Hypothesis.stepTwo_linear` — §3's stage (2), the linear equation
  `(a² + ζ⁻¹) · f(ω s^a)‾ = ω̄` in `E`.
* `Hypothesis.stepTen_quotient_coord` — §2's stage (10) read in `E`.
* `Hypothesis.stepThree_sq_eq` — the group-to-field bridge of §3 (3):
  `b² = ζ + ζ⁻¹ + a⁻²`.
* `Hypothesis.stepThree_center_relation` — its `Q₀`-side companion
  `b^{2(1+θ)} = α² + a^{-2(1+θ)}`.
* `Hypothesis.stepThree_star` — the book's `(∗)`, for one admissible `a`.
* `Hypothesis.exists_mem_K_mu_sq_inv_eq` — the scalars `a⁻²` sweep `F^×`, so that `(∗)`
  is available at every `X ∈ F^×`.
* `Hypothesis.stepThree` — §3's stage (3): `θ = 1` and `ω² = (0, ζ + ζ⁻¹)`.
* `Hypothesis.thetaModel_eq_id_on_frobFixed` — the model's `θ` and `σ` are both the
  identity on `F`, so stage (3) really is the book's `θ = 1`.
* `Hypothesis.cocycle_scale_of_diagScale` — its `K`-scaling input, straight from
  `centreQuadraticMap_smul`.
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

/-- **The two `f`-values of stage (1) are conjugates of a single one** (Peterfalvi
Part II, p. 130, entering stage (2)).

Writing `X = f(ω s^a)`, the arguments occurring in `stepOne_chain` are `ω s^a` conjugated
by `ζ^{±1}`: the conjugation does not move `s^a`, which lies in `Q₀ = Z(Q)`, and (H3)
moves `f` across it without a twist because `t` centralizes `W`.

This is what turns stage (1) into a *linear* equation for the single unknown `X̄` in `E`.
-/
theorem f_conj_zeta_of_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω z : G} (hζ : ζ ∈ hyp.W) (hzQ0 : z ∈ hyp.Q0)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    f ((ζ * ω * ζ⁻¹) * z) = ζ * f (ω * z) * ζ⁻¹ ∧
      f (z * (ζ⁻¹ * ω * ζ)) = ζ⁻¹ * f (ω * z) * ζ := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right hyp.rankOneSetup.invol
  have htζit : hyp.t * ζ⁻¹ * hyp.t = ζ⁻¹ := by
    calc hyp.t * ζ⁻¹ * hyp.t = (hyp.t⁻¹ * ζ * hyp.t⁻¹)⁻¹ := by group
      _ = (hyp.t * ζ * hyp.t)⁻¹ := by rw [htinv]
      _ = ζ⁻¹ := by rw [htζt]
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  have hcz : ζ * z = z * ζ := hyp.W_centralizes_Q0 hζ hzQ0
  constructor
  · -- `(ζ ω ζ⁻¹) z = ζ (ω z) ζ⁻¹`, then (H3) at `ζ⁻¹`
    obtain ⟨h3, -, -⟩ :=
      hThree hyp.rankOneSetup H hωzQ hωz1 (hyp.D.inv_mem hζD)
    rw [htζit, inv_inv] at h3
    have harg : (ζ * ω * ζ⁻¹) * z = ζ * (ω * z) * ζ⁻¹ := by
      calc (ζ * ω * ζ⁻¹) * z = ζ * ω * (ζ⁻¹ * z * ζ) * ζ⁻¹ := by group
        _ = ζ * ω * z * ζ⁻¹ := by
            rw [show ζ⁻¹ * z * ζ = z from by
              calc ζ⁻¹ * z * ζ = ζ⁻¹ * (z * ζ) := by group
                _ = ζ⁻¹ * (ζ * z) := by rw [← hcz]
                _ = z := by group]
        _ = ζ * (ω * z) * ζ⁻¹ := by group
    rw [harg, h3]
  · -- `z (ζ⁻¹ ω ζ) = ζ⁻¹ (ω z) ζ`, then (H3) at `ζ`
    obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωzQ hωz1 hζD
    rw [htζt] at h3
    have harg : z * (ζ⁻¹ * ω * ζ) = ζ⁻¹ * (ω * z) * ζ := by
      calc z * (ζ⁻¹ * ω * ζ) = ζ⁻¹ * (ζ * z * ζ⁻¹) * ω * ζ := by group
        _ = ζ⁻¹ * z * ω * ζ := by
            rw [show ζ * z * ζ⁻¹ = z from by
              calc ζ * z * ζ⁻¹ = (z * ζ) * ζ⁻¹ := by rw [hcz]
                _ = z := by group]
        _ = ζ⁻¹ * (ω * z) * ζ := by
            have hzω : z * ω = ω * z :=
              (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hzQ0) ω hωQ).symm
            calc ζ⁻¹ * z * ω * ζ = ζ⁻¹ * (z * ω) * ζ := by group
              _ = ζ⁻¹ * (ω * z) * ζ := by rw [hzω]
    rw [harg, h3]

/-- **§3, stage (1), with its conjugations packaged as `conjQHom`** (Peterfalvi Part II,
p. 130, the form stage (4) reads in the unitary coordinates).

`stepOne_chain` presents both sides as iterated conjugations in `G`; collecting them,

  `X^{a²ζ} · s^a = X^{ζ²} · ω^ζ`,   `X = f(ω s^a)`

(all conjugations written `c · x · c⁻¹`, and `ζ³ · ζ⁻¹ = ζ²` on the right).  This is
exactly the display the book reads coordinatewise on p. 131: each `conjQHom kv` scales
the quotient coordinate by `μ(kv)` and — once the cocycle's diagonal is known to be a
multiple of the norm — the unitary coordinate by `μ(kv)^{1+q}`. -/
theorem stepOne_conjQHom (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    hyp.conjQHom (hyp.kActor ha2, ⟨ζ, hζ⟩)
          ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩
        * ⟨a * hyp.distinguishedInvolution * a⁻¹,
            hyp.Q0_le_Q (hyp.conj_mem_Q0_of_mem_D haK.1
              hyp.distinguishedInvolution_mem_Q0)⟩
      = hyp.conjQHom (hyp.kActor hyp.K.one_mem, ⟨ζ ^ 2, hyp.W.pow_mem hζ 2⟩)
            ⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩
          * hyp.conjQHom (hyp.kActor hyp.K.one_mem, ⟨ζ, hζ⟩) ⟨ω, hωQ⟩ := by
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haK.1 hyp.distinguishedInvolution_mem_Q0
  obtain ⟨hcL, hcR⟩ := hyp.f_conj_zeta_of_mem_Q0 H hζ hzQ0 hωQ hωQ0
  have hchain := hyp.stepOne_chain H hC2 M hZ hmu hVW hζ hωQ hωQ0 haK hf
  rw [hcL, hcR] at hchain
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, Submonoid.coe_mul,
    hyp.conjQHom_kActor_apply_val ha2 hζ,
    hyp.conjQHom_kActor_apply_val hyp.K.one_mem (hyp.W.pow_mem hζ 2),
    hyp.conjQHom_kActor_apply_val hyp.K.one_mem hζ]
  set X := f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) with hX
  calc (a ^ 2 * ζ) * X * (a ^ 2 * ζ)⁻¹
        * (a * hyp.distinguishedInvolution * a⁻¹)
      = a ^ 2 * (ζ * X * ζ⁻¹) * (a⁻¹) ^ 2
          * (a * hyp.distinguishedInvolution * a⁻¹) := by group
    _ = ζ ^ 3 * (ζ⁻¹ * X * ζ) * (ζ ^ 3)⁻¹ * (ζ * ω * ζ⁻¹) := hchain
    _ = (1 * ζ ^ 2) * X * (1 * ζ ^ 2)⁻¹ * ((1 * ζ) * ω * (1 * ζ)⁻¹) := by group

/-- **§3, stage (2)** (Peterfalvi Part II, p. 130): stage (1), read in the coordinates of
`Q ⧸ Z(Q) ≅ E`, is the linear equation

  `(a² + ζ⁻¹) · f(ω s^a)‾ = ω̄`.

The conjugate `s^a` lies in `Q₀ = Z(Q)` and so disappears in the quotient
(`coord_mk_eq_zero_of_mem_Q0`); each conjugation becomes multiplication by a scalar
(`coord_conj_eq`), and the products split by additivity (`coord_mk_mul`).

The book's `ζ⁻¹` is `μ(1, ζ)` here — its `x^d` is conjugation by `d⁻¹`, whereas `coord_act`
is stated for conjugation by `d`. -/
theorem stepTwo_linear (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E))
      * M.coord (Additive.ofMul (QuotientGroup.mk
          (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
  classical
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hconjQ : ∀ {c x : G}, c ∈ hyp.D → x ∈ hyp.Q → c * x * c⁻¹ ∈ hyp.Q := by
    intro c x hc hx
    have hm := hyp.rankOneSetup.DQ c⁻¹ (hyp.D.inv_mem hc) x hx
    rwa [inv_inv] at hm
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haK.1 hyp.distinguishedInvolution_mem_Q0
  have hzQ : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q := hyp.Q0_le_Q hzQ0
  -- the chain of stage (1), with both `f`-values expressed through `X`
  obtain ⟨hcL, hcR⟩ := hyp.f_conj_zeta_of_mem_Q0 H hζ hzQ0 hωQ hωQ0
  have hchain := hyp.stepOne_chain H hC2 M hZ hmu hVW hζ hωQ hωQ0 haK hf
  rw [hcL, hcR] at hchain
  -- memberships
  have ha2D : a ^ 2 ∈ hyp.D := hyp.K_le_D ha2
  have hζ3D : ζ ^ 3 ∈ hyp.D := pow_mem hζD 3
  have hYQ : ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹ ∈ hyp.Q :=
    hconjQ hζD hXQ
  have hZ'Q : ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ ∈ hyp.Q := by
    have hm := hconjQ (hyp.D.inv_mem hζD) hXQ
    rwa [inv_inv] at hm
  have hAQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 ∈ hyp.Q := by
    have hm := hconjQ ha2D hYQ
    rwa [show (a ^ 2)⁻¹ = (a⁻¹) ^ 2 from by group] at hm
  have hBQ : ζ ^ 3 * (ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ)
      * (ζ ^ 3)⁻¹ ∈ hyp.Q := hconjQ hζ3D hZ'Q
  have hCQ : ζ * ω * ζ⁻¹ ∈ hyp.Q := hconjQ hζD hωQ
  have hLQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hAQ hzQ
  have hRQ : ζ ^ 3 * (ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ)
      * (ζ ^ 3)⁻¹ * (ζ * ω * ζ⁻¹) ∈ hyp.Q := hyp.Q.mul_mem hBQ hCQ
  -- one coordinate of each side
  have hone : (⟨(1 : G), hyp.W.one_mem⟩ : ↥hyp.W) = 1 := rfl
  have honeK : (hyp.kActor (hyp.K.one_mem)) = 1 := hyp.kActor_one hyp.K.one_mem
  have hL : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) *
        (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hXQ⟩ : ↥hyp.Q)))) := by
    rw [hyp.coord_mk_mul M hAQ hzQ hLQ,
      hyp.coord_mk_eq_zero_of_mem_Q0 M hZ hzQ0 hzQ, add_zero,
      hyp.coord_conj_eq M ha2 hyp.W.one_mem hYQ hAQ (by group),
      hyp.coord_conj_eq M hyp.K.one_mem hζ hXQ hYQ (by group)]
    rw [hone, honeK]
  have hR : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) : M.Eˣ) : M.E) *
          (((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) : M.Eˣ) : M.E) *
            M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hXQ⟩ : ↥hyp.Q))))
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
    rw [hyp.coord_mk_mul M hBQ hCQ hRQ,
      hyp.coord_conj_eq M hyp.K.one_mem (hyp.W.pow_mem hζ 3) hZ'Q hBQ (by group),
      hyp.coord_conj_eq M hyp.K.one_mem (hyp.W.inv_mem hζ) hXQ hZ'Q (by group),
      hyp.coord_conj_eq M hyp.K.one_mem hζ hωQ hCQ (by group)]
    rw [honeK]
    rfl
  -- the two sides of stage (1) are the same element, so their coordinates agree
  have hcoordeq : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q))) :=
    congrArg (fun q : ↥hyp.Q => M.coord (Additive.ofMul (QuotientGroup.mk q)))
      (Subtype.ext hchain)
  have hprod : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) *
      ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹)
      = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ^ 2 := by
    have e1 : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) *
        ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹)
        = ((1 : ↥hyp.actualKActor) * 1,
            (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3 * (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) := rfl
    have e2 : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ^ 2
        = ((1 : ↥hyp.actualKActor) ^ 2, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2) := rfl
    rw [e1, e2, one_mul, one_pow]
    congr 1
    group
  have hVpow : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) : M.Eˣ) : M.E)
      * ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) : M.Eˣ) : M.E)
      = ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 := by
    rw [← Units.val_mul, ← map_mul, hprod, map_pow, Units.val_pow_eq_pow_val]
  rw [hL, hR] at hcoordeq
  refine mul_left_cancel₀ (Units.ne_zero (M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)))) ?_
  linear_combination hcoordeq
    + (M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))) * hVpow
    + (((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 *
      M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))) * h2E

/-- **§2's stage (10), read in `Q ⧸ Z(Q) ≅ E`** (Peterfalvi Part II, p. 130, first display
of §3 (3)).

Stage (10) says `f(ω s^a) = (f(ω z) · s^a)^{ζ a⁻²}` with `z = y · s^{a⁻¹}`; in the
quotient the factor `s^a ∈ Q₀ = Z(Q)` disappears and the conjugation becomes a scalar, so

  `f(ω s^a)‾ = (μ(a²) μ(ζ))⁻¹ · f(ω z)‾`.

This is the book's `f(ωs^a)‾ = ζ a⁻² · f(ω(0, α + a^{-(1+θ)}))‾`.  The scalars are the
*inverses* of the book's throughout: its `x^d` is conjugation by `d⁻¹`, whereas `coord_act`
is stated for conjugation by `d`.  Both stages invert in the same way, so the eventual
field identity has the book's shape (`stepThree_sq_eq`).

The conjugate of `s` is written `a s a⁻¹` — the convention of `stepTwo_linear`, which is
`s^{a⁻¹}` in the book's; stage (10) is therefore applied at `a⁻¹`. -/
theorem stepTen_quotient_coord (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω y a z : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (haK : a ∈ hyp.K) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hz : y * (a⁻¹ * hyp.distinguishedInvolution * a) = z)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hWQ : f (ω * z) ∈ hyp.Q) :
    M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
            * ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E))⁻¹
        * M.coord (Additive.ofMul (QuotientGroup.mk (⟨f (ω * z), hWQ⟩ : ↥hyp.Q))) := by
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  have haD : a ∈ hyp.D := hyp.K_le_D haK
  -- stage (10) at `a⁻¹`, with the double inverses removed
  have hstep := hyp.stepTen H hC2 hζ hωQ hωQ0 hyQ0 (hyp.K.inv_mem haK) hfω
    (show y * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹) = z by rwa [inv_inv])
  rw [inv_inv] at hstep
  -- the `Q₀`-factor and the memberships
  have hsaQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haD hsQ0
  have hsaQ : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q := hyp.Q0_le_Q hsaQ0
  have hUQ : f (ω * z) * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hWQ hsaQ
  have hκ : (a ^ 2)⁻¹ ∈ hyp.K := hyp.K.inv_mem (pow_mem haK 2)
  have hv : ζ⁻¹ ∈ hyp.W := hyp.W.inv_mem hζ
  -- the conjugating element is `(a²)⁻¹ ζ⁻¹`
  have hval : ((a ^ 2)⁻¹ * ζ⁻¹) * (f (ω * z) * (a * hyp.distinguishedInvolution * a⁻¹))
      * ((a ^ 2)⁻¹ * ζ⁻¹)⁻¹ = f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) := by
    rw [hstep]; group
  rw [hyp.coord_conj_eq M hκ hv hUQ hXQ hval, hyp.coord_mk_mul M hWQ hsaQ hUQ,
    hyp.coord_mk_eq_zero_of_mem_Q0 M hZ hsaQ0 hsaQ, add_zero]
  -- identify the scalar as the inverse of `μ(a²) μ(ζ)`
  congr 1
  have hpair : (hyp.kActor hκ, (⟨ζ⁻¹, hv⟩ : ↥hyp.W))
      = ((hyp.kActor (pow_mem haK 2), (1 : ↥hyp.W)) *
          ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)))⁻¹ := by
    have hfst : hyp.kActor hκ = (hyp.kActor (pow_mem haK 2))⁻¹ :=
      hyp.kActor_eq_inv (pow_mem haK 2) hκ rfl
    have hsnd : (⟨ζ⁻¹, hv⟩ : ↥hyp.W) = (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹ := Subtype.ext rfl
    rw [Prod.mk_mul_mk, one_mul, mul_one, Prod.inv_mk, hfst, hsnd]
  rw [hpair, map_inv, Units.val_inv_eq_inv_val, map_mul, Units.val_mul]

/-- **`b² = ζ + ζ⁻¹ + a⁻²`** (Peterfalvi Part II, p. 130, inside §3 (3)) — the bridge from
the group to the field.

The book gets there by dividing the two instances of stage (2),

  `1/(a² + ζ⁻¹) = ζ a⁻² / (b² + ζ⁻¹)`,

but the division is avoidable: stage (2) at `a` and at `b` both evaluate `ω̄`, and stage
(10) relates the two unknowns, so cancelling the (nonzero) unknown at `b` already gives the
identity — no side condition `a² + ζ⁻¹ ≠ 0` is needed.

Written with `A = μ(a²)` and `Z = μ(ζ)`, the three inputs are
`(A + Z) X_a = ω̄`, `(B + Z) X_b = ω̄` and `X_a = (A Z)⁻¹ X_b`, whence
`(A + Z)(A Z)⁻¹ = B + Z`, i.e. `B = A⁻¹ + Z + Z⁻¹`.  The scalars being the inverses of the
book's (see `stepTen_quotient_coord`), this is its `b² = ζ + ζ⁻¹ + a⁻²`.

The element `b` is the one produced by `stepTen_exists`; its defining relation
`s^b = y · s^{a⁻¹}` is the book's `b^{1+θ} = α + a^{-(1+θ)}` (`stepTen_coord`). -/
theorem stepThree_sq_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y a b : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) (haK : a ∈ hyp.K) (hbK : b ∈ hyp.K)
    (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a)) :
    ((M.mu (hyp.kActor (pow_mem hbK 2), 1) : M.Eˣ) : M.E)
      = ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹ := by
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  -- the §3 hypothesis in the form stage (1) needs
  have hf : f ω = ζ⁻¹ * ω⁻¹ * ζ := hyp.f_eq_conj_inv_of_sq_eq hyQ0 hfω hsq
  -- the two arguments of `f`, and their images
  have hsaQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hsQ0
  have hsbQ0 : b * hyp.distinguishedInvolution * b⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hbK) hsQ0
  obtain ⟨hωaQ, hωaQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hsaQ0
  obtain ⟨hωbQ, hωbQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hsbQ0
  obtain ⟨hXaQ, -⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωaQ hωaQ0
  obtain ⟨hXbQ, hXbQ0⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωbQ hωbQ0
  -- the three equations
  have hA := hyp.stepTwo_linear H hC2 M hZ hmu hVW hζ hωQ hωQ0
    (by rw [← hyp.coe_K] at *; exact haK) (pow_mem haK 2) hf hXaQ
  have hB := hyp.stepTwo_linear H hC2 M hZ hmu hVW hζ hωQ hωQ0
    (by rw [← hyp.coe_K] at *; exact hbK) (pow_mem hbK 2) hf hXbQ
  have hT := hyp.stepTen_quotient_coord H hC2 M hZ hζ hωQ hωQ0 hyQ0 haK hfω hb.symm
    hXaQ hXbQ
  -- the unknown at `b` is nonzero, so it cancels
  have hXb0 := hyp.coord_ne_zero_of_not_mem_Q0 M hZ hXbQ hXbQ0
  have hAne : ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  have hZne : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  rw [hT] at hA
  exact eq_add_inv_add_inv_of_mul_inv_eq h2E hAne hZne
    (mul_right_cancel₀ hXb0 (by rw [← mul_assoc] at hA; exact hA.trans hB.symm))

/-- **`b^{2(1+θ)} = α² + a^{-2(1+θ)}`** (Peterfalvi Part II, p. 130, inside §3 (3)):
the defining relation of `b`, read on `Q₀ ≅ F` and squared.

`stepTen_coord` turns `s^b = y · s^{a⁻¹}` into `α + a^{-(1+θ)} = b^{1+θ}`, where the
`K`-action on `Q₀` is the integer power `μ(·)^d` and `α` is the ratio
`centerCoord y / centerCoord s` (the book normalizes `s ↦ (0,1)`, so that the ratio is
its `α`).  Squaring in characteristic `2` kills the cross term and moves the exponent onto
`a²`, `b²` — the scalars in which `stepThree_sq_eq` speaks. -/
theorem stepThree_center_relation {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {y a b : G} (hyQ0 : y ∈ hyp.Q0) (haK : a ∈ hyp.K) (hbK : b ∈ hyp.K)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a)) :
    ((M.mu (hyp.kActor (pow_mem hbK 2), 1) ^ d : M.Eˣ) : M.E)
      = (hyp.centerCoord s M ι hyQ0 /
          hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0) ^ 2
        + (((M.mu (hyp.kActor (pow_mem haK 2), 1) ^ d : M.Eˣ) : M.E))⁻¹ := by
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hadd_sq : ∀ x z : M.E, (x + z) ^ 2 = x ^ 2 + z ^ 2 := fun x z => by
    linear_combination x * z * h2E
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  have hcs : hyp.centerCoord s M ι hsQ0 ≠ 0 := by
    rw [Ne, hyp.centerCoord_eq_zero_iff]
    exact hyp.distinguishedInvolution_ne_one
  -- the scalar of `c²` is the square of that of `c`
  have hsq : ∀ {c : G} (hc : c ∈ hyp.K),
      ((M.mu (hyp.kActor (pow_mem hc 2), 1) ^ d : M.Eˣ) : M.E)
        = (((M.mu (hyp.kActor hc, 1) ^ d : M.Eˣ) : M.E)) ^ 2 := by
    intro c hc
    rw [hyp.kActor_eq_pow hc (pow_mem hc 2) 2 rfl,
      show ((hyp.kActor hc) ^ 2, (1 : ↥hyp.W)) = ((hyp.kActor hc, (1 : ↥hyp.W))) ^ 2 from
        Prod.ext rfl (one_pow 2).symm,
      map_pow, pow_two, mul_zpow, Units.val_mul, ← pow_two]
  -- the scalar of `a⁻¹` is the inverse of that of `a`
  have hinv : ((M.mu (hyp.kActor (hyp.K.inv_mem haK), 1) ^ d : M.Eˣ) : M.E)
      = (((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E))⁻¹ := by
    rw [hyp.kActor_eq_inv haK (hyp.K.inv_mem haK) rfl,
      show ((hyp.kActor haK)⁻¹, (1 : ↥hyp.W)) = ((hyp.kActor haK, (1 : ↥hyp.W)))⁻¹ from
        Prod.ext rfl inv_one.symm,
      map_inv, inv_zpow, Units.val_inv_eq_inv_val]
  -- the relation on `Q₀`, in coordinates
  have hiff := hyp.stepTen_coord s M ι d hequiv hyQ0 hsQ0 (hyp.K.inv_mem haK) hbK
  rw [inv_inv] at hiff
  have hrel := hiff.mp hb.symm
  rw [hinv] at hrel
  -- divide by `centerCoord s` and square
  have hV : ((M.mu (hyp.kActor hbK, 1) ^ d : M.Eˣ) : M.E)
      = hyp.centerCoord s M ι hyQ0 / hyp.centerCoord s M ι hsQ0
        + (((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E))⁻¹ := by
    have hU : ((M.mu (hyp.kActor haK, 1) ^ d : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
    field_simp at hrel ⊢
    linear_combination -hrel
  rw [hsq hbK, hsq haK, hV, hadd_sq, ← inv_pow]

/-- **§3 (3)'s `(∗)`, for one admissible `a`** (Peterfalvi Part II, p. 130):

  `α² + w² + w · (X + X^θ) = 0`,   `w = ζ + ζ⁻¹`,  `X = a⁻²`.

Everything group-theoretic has already happened: `stepThree_sq_eq` gives `b² = w + a⁻²`
in `Q/Q₀`, `stepThree_center_relation` gives `b^{2(1+θ)} = α² + a^{-2(1+θ)}` in `Q₀`, and
`star_of_scaling_pair` combines the two through the scaling pair `(σ, τ)` of Ch. III §3,
which is what expresses the `Q₀`-exponent `d` as `x ↦ σ(x · θ x)`.

The pair is passed as ring isomorphisms; `exists_scalingPair_of_lemmaFiveSetup` produces
it as `ZMod 2`-algebra isomorphisms, of which these are the underlying maps.  `θ` is
supplied as an additive map together with `hθ`, so that a caller may present `σ⁻¹ ∘ τ` in
whatever bundled form it has. -/
theorem stepThree_star (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (σ τ : M.E ≃+* M.E) (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x))
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    {ζ ω y a b : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) (haK : a ∈ hyp.K) (hbK : b ∈ hyp.K)
    (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a)) :
    (σ.symm (hyp.centerCoord sfive M ι hyQ0 /
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)) ^ 2
      + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) ^ 2
      + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹)
        * (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹
            + θ (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹)) = 0 := by
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  exact star_of_scaling_pair h2E σ τ θ hθ (hWinv ⟨ζ, hζ⟩)
    (hscale (hyp.kActor (pow_mem haK 2))) (hscale (hyp.kActor (pow_mem hbK 2)))
    (hyp.stepThree_sq_eq H hC2 M hZc hmu hVW hζ hωQ hωQ0 hyQ0 hsq haK hbK hfω hb)
    (hyp.stepThree_center_relation sfive M ι d hequiv hyQ0 haK hbK hb)

/-- **The scalars `a⁻²` sweep `F^×`** (Peterfalvi Part II, p. 130: `(∗)` is asserted for
every `X ∈ F − {0, α^{2τ}}`).

`μ` maps `K` *onto* `F^×` (`exists_actualKActor_mu_eq`, from `|K| = q − 1` and
`mu_K_injective`), and squaring is a bijection of a field of characteristic `2` — here
inverted explicitly by `x ↦ x^{2^{m-1}}`, which is a square root because `x^{2^m} = x` on
`F`.  So the `X` for which `stepThree_star` produces `(∗)` are *all* of `F^×`; only the
book's single excluded point survives, namely the `a` for which `b` fails to exist. -/
theorem exists_mem_K_mu_sq_inv_eq {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) {c : M.E}
    (hc : c ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (hc0 : c ≠ 0) :
    ∃ (a : G) (haK : a ∈ hyp.K),
      ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹ = c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- a square root of `c⁻¹` inside `F`
  have hcinv : c⁻¹ ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    Subfield.inv_mem _ hc
  have hrmem : c⁻¹ ^ 2 ^ (m - 1) ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    Subfield.pow_mem _ hcinv _
  have hr0 : c⁻¹ ^ 2 ^ (m - 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hc0)
  have hrsq : (c⁻¹ ^ 2 ^ (m - 1)) ^ 2 = c⁻¹ := by
    rw [← pow_mul, mul_comm, ← pow_succ']
    have hm1 : 2 ^ (m - 1 + 1) = 2 ^ m := by
      congr 1
      omega
    rw [hm1]
    exact OddOrder.FiniteField.mem_frobFixedSubfield.mp hcinv
  -- an element of `K` with that scalar
  obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq sfive M hm hQ0card hrmem hr0
  obtain ⟨x, hx⟩ := k.2
  refine ⟨(x : G), x.2, ?_⟩
  have hkActor : hyp.kActor x.2 = k := Subtype.ext hx
  rw [hyp.mu_kActor_sq M x.2, hkActor, hk, hrsq, inv_inv]

/-- **The scalars `a²` sweep `F^×`** — `exists_mem_K_mu_sq_inv_eq` without the inverse.

§3 (4) needs it in this direction: its `(∗∗)` is asserted for every `a ∈ F − {0}`, and
`a` there is the centre coordinate `μ(a²)` of `s^a`. -/
theorem exists_mem_K_mu_sq_eq {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) {c : M.E}
    (hc : c ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (hc0 : c ≠ 0) :
    ∃ (a : G) (haK : a ∈ hyp.K),
      ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) = c := by
  obtain ⟨a, haK, h⟩ := hyp.exists_mem_K_mu_sq_inv_eq hm hQ0card sfive M
    (Subfield.inv_mem _ hc) (inv_ne_zero hc0)
  exact ⟨a, haK, inv_inj.mp h⟩

/-- **`w = ζ + ζ⁻¹` lies in `F`** (Peterfalvi Part II, p. 130: `(∗)` is an equation of
`F`, even though `ζ` itself is not in `F`).

The bar operation `x ↦ x^q` inverts `W₁` (`bar_mu_W`), so it exchanges the two summands
and fixes their sum — `w` is the trace of `ζ`. -/
theorem mu_W_add_inv_mem_frobFixed {m : ℕ} (M : hyp.QuotientFieldModel m) (v : ↥hyp.W) :
    ((M.mu (1, v) : M.Eˣ) : M.E) + ((M.mu (1, v) : M.Eˣ) : M.E)⁻¹
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [OddOrder.FiniteField.mem_frobFixedSubfield, ← M.bar_apply, map_add, M.bar_mu_W v,
    map_inv₀, M.bar_mu_W v, inv_inv, add_comm]

/-- **`w = ζ + ζ⁻¹ ≠ 0` for `ζ ≠ 1`**: otherwise `ζ` would be its own inverse, hence — in
characteristic `2`, where squaring is injective — trivial, and `μ` is faithful. -/
theorem mu_W_add_inv_ne_zero {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hmu : Function.Injective M.mu) {v : ↥hyp.W} (hv : v ≠ 1) :
    ((M.mu (1, v) : M.Eˣ) : M.E) + ((M.mu (1, v) : M.Eˣ) : M.E)⁻¹ ≠ 0 := by
  intro hzero
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hne : ((M.mu (1, v) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  -- `Z + Z⁻¹ = 0` gives `Z² = 1`, and `(Z + 1)² = Z² + 1`
  have hsq : (((M.mu (1, v) : M.Eˣ) : M.E) + 1) ^ 2 = 0 := by
    have hmul := congrArg (fun x => x * ((M.mu (1, v) : M.Eˣ) : M.E)) hzero
    simp only [add_mul, inv_mul_cancel₀ hne, zero_mul] at hmul
    linear_combination hmul + ((M.mu (1, v) : M.Eˣ) : M.E) * h2E
  have hone : ((M.mu (1, v) : M.Eˣ) : M.E) + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
  have hval : ((M.mu (1, v) : M.Eˣ) : M.E) = 1 := by linear_combination hone - h2E
  have hmu1 : M.mu (1, v) = 1 := Units.ext hval
  exact hv (congrArg Prod.snd (hmu (hmu1.trans (map_one M.mu).symm)))

/-- `θ = σ⁻¹ ∘ τ` preserves `F`, being a composite of ring maps. -/
theorem theta_mem_frobFixed {m : ℕ} (M : hyp.QuotientFieldModel m) (σ τ : M.E ≃+* M.E)
    (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x)) :
    ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      θ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
  intro x hx
  rw [OddOrder.FiniteField.mem_frobFixedSubfield] at hx ⊢
  rw [hθ, ← map_pow, ← map_pow, hx]

/-- `σ⁻¹` preserves `F`, being a ring map. -/
theorem sigma_symm_mem_frobFixed {m : ℕ} (M : hyp.QuotientFieldModel m) (σ : M.E ≃+* M.E) :
    ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      σ.symm x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
  intro x hx
  rw [OddOrder.FiniteField.mem_frobFixedSubfield] at hx ⊢
  rw [← map_pow, hx]

/-- `θ = σ⁻¹ ∘ τ` is injective. -/
theorem theta_injective {m : ℕ} (M : hyp.QuotientFieldModel m) (σ τ : M.E ≃+* M.E)
    (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x)) : Function.Injective θ := by
  intro x₁ x₂ hx
  rw [hθ, hθ] at hx
  exact τ.injective (σ.symm.injective hx)

/-- The book's `α` — the ratio of two central coordinates, read through `σ⁻¹` — lies
in `F`, both coordinates being values of `ι`. -/
theorem centerCoord_div_mem_frobFixed {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (σ : M.E ≃+* M.E) {y z : G} (hy : y ∈ hyp.Q0) (hz : z ∈ hyp.Q0) :
    σ.symm (hyp.centerCoord sfive M ι hy / hyp.centerCoord sfive M ι hz)
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
  hyp.sigma_symm_mem_frobFixed M σ _ (Subfield.div_mem _
    (ι (Additive.ofMul (hyp.toCenter sfive hy))).2
    (ι (Additive.ofMul (hyp.toCenter sfive hz))).2)

/-- **`(∗)` at every admissible point of `F`** (Peterfalvi Part II, p. 130, inside §3 (3)).

`stepThree_star` gives the book's `(∗)` for one admissible `a`; this assembles the whole
count.  The `X` occurring there sweep all of `F^×` (`exists_mem_K_mu_sq_inv_eq`), and the
only `X` at which the argument is unavailable is the one whose `a` solves `s^a = y` —
unique because `K` is regular on `Q₀^#` (`eq_of_conj_distinguishedInvolution_eq`).  That is
the book's single excluded point `α^{2τ}`.

What `(∗)` is then used for splits into two halves with *different* hypotheses —
`stepThree` (the book's `|F| ≥ 8`) and `stepThree_of_odd` (the book's "`θ` is of odd
order") — and both start here. -/
theorem stepThree_star_all (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (σ τ : M.E ≃+* M.E) (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x))
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (_hζ1 : ζ ≠ 1) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    ∃ z ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      ∀ X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, X ≠ 0 → X ≠ z →
        (σ.symm (hyp.centerCoord sfive M ι hyQ0 /
            hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)) ^ 2
          + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
              + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) ^ 2
          + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
              + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) * (X + θ X) = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  -- `y = ω² ≠ 1`, since `ω ∉ Q₀`
  have hy1 : y ≠ 1 := by
    intro hc
    refine hωQ0 (hyp.mem_Q0_iff.mpr ⟨?_, hyp.Q_le_H hωQ⟩)
    rw [pow_two, hsqω, hc]
  -- the exceptional element: the unique `a₀ ∈ K` with `s^{a₀} = y`
  obtain ⟨a₀, ha₀KSet, ha₀⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hyQ0 hy1
  have ha₀K : a₀ ∈ hyp.K := by rw [← hyp.coe_K] at ha₀KSet; exact ha₀KSet
  -- `θ` and `σ⁻¹` preserve `F`, being ring maps
  have hθmem : ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      θ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
    intro x hx
    rw [OddOrder.FiniteField.mem_frobFixedSubfield] at hx ⊢
    rw [hθ, ← map_pow, ← map_pow, hx]
  have hσmem : ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      σ.symm x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
    intro x hx
    rw [OddOrder.FiniteField.mem_frobFixedSubfield] at hx ⊢
    rw [← map_pow, hx]
  have hθinj : Function.Injective θ := by
    intro x₁ x₂ hx
    rw [hθ, hθ] at hx
    exact τ.injective (σ.symm.injective hx)
  -- the constants of `(∗)` all lie in `F`
  have hαmem : σ.symm (hyp.centerCoord sfive M ι hyQ0 /
      hyp.centerCoord sfive M ι hsQ0)
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    hσmem _ (Subfield.div_mem _
      (ι (Additive.ofMul (hyp.toCenter sfive hyQ0))).2
      (ι (Additive.ofMul (hyp.toCenter sfive hsQ0))).2)
  have hzmem : ((M.mu (hyp.kActor (pow_mem ha₀K 2), 1) : M.Eˣ) : M.E)⁻¹
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m :=
    Subfield.inv_mem _
      (OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed _))
  -- `(∗)` at every point of `F^×` other than the excluded one
  have hstar : ∀ X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, X ≠ 0 →
      X ≠ ((M.mu (hyp.kActor (pow_mem ha₀K 2), 1) : M.Eˣ) : M.E)⁻¹ →
      (σ.symm (hyp.centerCoord sfive M ι hyQ0 /
          hyp.centerCoord sfive M ι hsQ0)) ^ 2
        + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
            + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) ^ 2
        + (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
            + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) * (X + θ X) = 0 := by
    intro X hXmem hX0 hXz
    obtain ⟨a, haK, hXa⟩ := hyp.exists_mem_K_mu_sq_inv_eq hm hQ0card sfive M hXmem hX0
    have hconjQ0 : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
      have hc := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem (hyp.K_le_D haK)) hsQ0
      rwa [inv_inv] at hc
    have hprodQ0 : y * (a⁻¹ * hyp.distinguishedInvolution * a) ∈ hyp.Q0 :=
      hyp.Q0.mul_mem hyQ0 hconjQ0
    -- `b` exists exactly when `X` is not the excluded point
    have hprod1 : y * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 := by
      intro hc
      have hyy : y * y = 1 := by
        have hy2 := hyQ0.1
        rwa [pow_two] at hy2
      have hey : a⁻¹ * hyp.distinguishedInvolution * a = y := by
        calc a⁻¹ * hyp.distinguishedInvolution * a
            = y * (y * (a⁻¹ * hyp.distinguishedInvolution * a)) := by
              rw [← mul_assoc, hyy, one_mul]
          _ = y := by rw [hc, mul_one]
      have haa₀ : a = a₀ :=
        hyp.eq_of_conj_distinguishedInvolution_eq haK ha₀K (hey.trans ha₀.symm)
      refine hXz ?_
      subst haa₀
      exact hXa.symm
    obtain ⟨c, hcKSet, hc⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hprodQ0 hprod1
    have hcK : c ∈ hyp.K := by rw [← hyp.coe_K] at hcKSet; exact hcKSet
    have hb : c⁻¹ * hyp.distinguishedInvolution * (c⁻¹)⁻¹
        = y * (a⁻¹ * hyp.distinguishedInvolution * a) := by rwa [inv_inv]
    have hs := hyp.stepThree_star H hC2 sfive M hZc hmu hVW ι d hequiv σ τ θ hθ
      hscale hWinv hζ hωQ hωQ0 hyQ0 hsqω haK (hyp.K.inv_mem hcK) hfω hb
    rwa [hXa] at hs
  exact ⟨_, hzmem, hstar⟩

/-- **§3 (3)** (Peterfalvi Part II, p. 130): **`θ = 1` and `ω² = (0, ζ + ζ⁻¹)`**, run off
`(∗)` by the book's counting.

`hcard` is the book's "`|F| ≥ 8`", which it derives from the odd order of `θ`.  Carried
as a hypothesis here, it is the *only* thing the counting needs; `stepThree_of_odd`
replaces it by the odd order itself and so also covers `|F| = 4`.

Two normalizations of the book are visible in the conclusion and are *not* gaps:

* `θ = 1` reads here as `σ|_F = τ|_F`, since `θ` is defined as `σ⁻¹ ∘ τ` rather than
  imported from the type-`B` datum.
* correspondingly `α` appears as `σ⁻¹ α`.

Neither survives: `eq_id_of_sq_eq_mul_on` shows that `σ|_F = τ|_F` already *forces*
`σ|_F = 1` — the book's `{μ|_F, ν|_F} = {1_F, θ}` is a consequence, not a choice — so the
model's `θ` is the identity on `F` and `σ⁻¹ α` is `α`. -/
theorem stepThree (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hcard : 5 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (σ τ : M.E ≃+* M.E) (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x))
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    (∀ X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θ X = X) ∧
      σ.symm (hyp.centerCoord sfive M ι hyQ0 /
          hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)
        = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  obtain ⟨z, hzmem, hstar⟩ := hyp.stepThree_star_all H hC2 hm hQ0card sfive M hZc hmu hVW
    ι d hequiv σ τ θ hθ hscale hWinv hζ hζ1 hωQ hωQ0 hyQ0 hsqω hfω
  exact eq_one_and_eq_of_star_subfield h2E _ θ
    (hyp.theta_mem_frobFixed M σ τ θ hθ) (hyp.theta_injective M σ τ θ hθ)
    (hyp.centerCoord_div_mem_frobFixed sfive M ι σ hyQ0 hyp.distinguishedInvolution_mem_Q0)
    (hyp.mu_W_add_inv_mem_frobFixed M ⟨ζ, hζ⟩) hzmem
    (hyp.mu_W_add_inv_ne_zero M hmu (fun hc => hζ1 (congrArg Subtype.val hc)))
    hcard hstar

/-- **§3 (3) with the book's own hypothesis** (Peterfalvi Part II, p. 130): `θ = 1` and
`ω² = (0, ζ + ζ⁻¹)`, from **"`θ` is of odd order"** rather than from `|F| ≥ 8`.

The book writes "if `θ ≠ 1`, then `|F| > 8` since `θ` is of odd order", and only then runs
the count.  Both branches are here:

* `θ ≠ 1` — `OddOrder.RingAut.three_le_of_odd_orderOf` turns the odd order into `m ≥ 3`,
  i.e. `|F| ≥ 8`, and `stepThree` runs the count;
* `θ = 1` — nothing to count: `(∗)` loses its bracket in characteristic `2` at any single
  admissible `X`, leaving `α² = w²`.  Three elements of `F` suffice, which `hcard` gives.

So `|F| = 4` — the case the count genuinely fails on, since over `𝐅₄` the Frobenius
satisfies `X + X^θ = 1` at both points outside `𝐅₂` — is covered: there the Frobenius has
order `2`, so an automorphism of odd order is already the identity. -/
theorem stepThree_of_odd (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (σ τ : M.E ≃+* M.E) (θ : M.E →+ M.E) (hθ : ∀ x : M.E, θ x = σ.symm (τ x))
    (hodd : Odd (orderOf (τ.trans σ.symm)))
    (hscale : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hWinv : ∀ v : ↥hyp.W,
      σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    (∀ X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θ X = X) ∧
      σ.symm (hyp.centerCoord sfive M ι hyQ0 /
          hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)
        = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  by_cases hne : (τ.trans σ.symm : M.E ≃+* M.E) = 1
  · -- `θ` is the identity outright; `(∗)` at one admissible point gives `α = w`
    have hfix : ∀ x : M.E, θ x = x := by
      intro x
      rw [hθ]
      exact congrFun (congrArg (fun ρ : M.E ≃+* M.E => (ρ : M.E → M.E)) hne) x
    refine ⟨fun X _ => hfix X, ?_⟩
    obtain ⟨z, hzmem, hstar⟩ := hyp.stepThree_star_all H hC2 hm hQ0card sfive M hZc hmu
      hVW ι d hequiv σ τ θ hθ hscale hWinv hζ hζ1 hωQ hωQ0 hyQ0 hsqω hfω
    obtain ⟨X, hX0, hXz⟩ :=
      exists_ne_zero_ne (α := ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) hcard
        ⟨z, hzmem⟩
    have hs := hstar (X : M.E) X.2 (fun hc => hX0 (Subtype.ext hc))
      (fun hc => hXz (Subtype.ext hc))
    rw [hfix (X : M.E)] at hs
    refine eq_of_sq_add_sq h2E ?_
    linear_combination hs - (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
      + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹) * (X : M.E) * h2E
  · -- `θ ≠ 1`: the odd order forces `m ≥ 3`, i.e. the book's `|F| ≥ 8`
    have hcardE : Nat.card M.E = 2 ^ (m * 2) := by rw [M.card, ← pow_mul]
    have hm3 : 3 ≤ m :=
      OddOrder.RingAut.three_le_of_odd_orderOf (p := 2) hcardE hodd hne
    have hcard5 : 5 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) := by
      rw [OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm]
      calc (5 : ℕ) ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    exact hyp.stepThree H hC2 hm hQ0card sfive M hZc hmu hVW hcard5 ι d hequiv σ τ θ hθ
      hscale hWinv hζ hζ1 hωQ hωQ0 hyQ0 hsqω hfω

/-- **The model's `θ` is the identity on `F` — and so is `σ`** (Peterfalvi Part II, p. 130,
reconciling the two `θ`'s of §3).

Ch. III §3 produces a cocycle `φ` that is `F`-semilinear with a twist `θ` (`hsemi`) and is
scaled by `μ(k)^d` under the action of `k ∈ K` (`hscaleQ0`).  Evaluating both at `x = y = 1`
— legitimate because `φ` is anisotropic, so `φ(1,1) ≠ 0` — identifies the two scalars:

  `μ(k) · θ(μ(k)) = μ(k)^d`.

The scaling pair of the same Proposition reads the very same `μ(k)^d` as `σ(μ(k)) τ(μ(k))`
(`hpair`).  Once §3 (3) has identified `σ` with `τ` on `F` (`hστ`), and since `μ` covers all
of `F^×`, this says `σ(a)² = a · θ(a)` throughout `F` — which by `eq_id_of_sq_eq_mul_on`
forces both maps to be the identity there.

So the book's normalization `{μ|_F, ν|_F} = {1_F, θ}` is *forced*, and `stepThree`'s
conclusion is literally the book's `θ = 1`. -/
theorem thetaModel_eq_id_on_frobFixed {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (sfive : hyp.LemmaFiveSetup m)
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (σ τ θm : M.E →+* M.E) (d : ℤ)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (hscaleQ0 : ∀ k : ↥hyp.actualKActor, ∀ x y : M.E,
      ((φ (((M.mu (k, 1) : M.Eˣ) : M.E) * x) (((M.mu (k, 1) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hpair : ∀ k : ↥hyp.actualKActor,
      σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E))
    (hστ : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, σ a = τ a) :
    (∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, σ a = a) ∧
      (∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θm a = a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  -- `φ(1,1) ≠ 0`, by anisotropy
  have hφ1 : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) ≠ 0 := by
    intro hc
    exact haniso 1 one_ne_zero (Subtype.ext hc)
  -- the model's scaling law: `μ(k) · θ(μ(k)) = μ(k)^d`
  have hmodel : ∀ k : ↥hyp.actualKActor,
      ((M.mu (k, 1) : M.Eˣ) : M.E) * θm ((M.mu (k, 1) : M.Eˣ) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) := by
    intro k
    have hmemF : ((M.mu (k, 1) : M.Eˣ) : M.E)
        ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) :=
      OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k)
    have h1 := hsemi _ hmemF _ hmemF 1 1
    have h2 := hscaleQ0 k 1 1
    rw [mul_one] at h1 h2
    exact mul_right_cancel₀ hφ1 (h1.symm.trans h2)
  -- `σ(a)² = a · θ(a)` on all of `F`
  have hkey : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      σ a ^ 2 = a * θm a := by
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq sfive M hm hQ0card ha ha0
    calc σ a ^ 2 = σ a * τ a := by rw [pow_two, hστ a ha]
      _ = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) := by rw [← hk]; exact hpair k
      _ = a * θm a := by rw [← hk]; exact (hmodel k).symm
  exact eq_id_of_sq_eq_mul_on h2E _ σ θm hkey

/-- **The cocycle is scaled by `μ(k)^d` under `K`** — the input `hscaleQ0` of
`thetaModel_eq_id_on_frobFixed`.

`exists_mulEquiv_bookCocycle` provides `φ`'s diagonal scaling law conditionally: *if* the
centre's quadratic map scales by `b` under `a`, *then* so does `φ`.  The premise for
`a = μ(k)`, `b = μ(k)^d` is exactly `centreQuadraticMap_smul`, which is the `K`-equivariance
of the descended square map.  So the two feed straight into each other. -/
theorem cocycle_scale_of_diagScale {m : ℕ} (M : hyp.QuotientFieldModel m)
    (sfive : hyp.LemmaFiveSetup m)
    (ι' : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d' : ℤ)
    (hequiv' : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι' (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d' : M.Eˣ) : M.E) *
          ((ι' (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (hdiagscale : ∀ a b : M.E,
      (∀ x : M.E,
        ((hyp.centreQuadraticMap sfive M ι' (a * x) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((hyp.centreQuadraticMap sfive M ι' x :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
      ∀ x y : M.E,
        ((φ (a * x) (a * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = b * ((φ x y :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (k : ↥hyp.actualKActor) (x y : M.E) :
    ((φ (((M.mu (k, 1) : M.Eˣ) : M.E) * x) (((M.mu (k, 1) : M.Eˣ) : M.E) * y) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (k, 1) ^ d' : M.Eˣ) : M.E) *
        ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) :=
  hdiagscale _ _ (fun z => hyp.centreQuadraticMap_smul sfive M ι' d' hequiv' k z) x y

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
