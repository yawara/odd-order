/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SequenceCoordinate

/-!
# Peterfalvi Part II, Ch. IV §2, step (17): `v_i = u_i + α`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 126.

> **(17)** For `1 ≤ i ≤ m − 1`, `f(ω(0,u_i)) = (ω(0, u_i + α))^{d_i}`.

At the level of the group this says that the *second* component of the sequence of (11)
is determined by the first:

  `w_i = y z_i`,

since `y` has coordinate `α` and `z_i` has coordinate `u_i`.  Establishing it needs the
scalar by which `d_i` acts on `Q₀`.  That scalar is `(c₁/c_{i+1})²` — the book's
`d_i^{-(1+σ)}` — because each step of (11) multiplies `d` by `ζ`, which centralizes `Q₀`,
and by the square of the step's `a ∈ K`, whose scalar is `u_{i+1}`; the resulting product
telescopes.

The book's own route is the displayed computation `u_i/u_{i+1} = 1 + (c₁/c_{i+1})²`, which
is `betaRatio_div_betaRatio`; here the same identity of `betaSum`s
(`betaSum_mul_betaSum_add_two`) is used in the form that survives `c_0 = 0`, so that the
induction can start at `i = 1`.

## Main results

* `betaSum_sq_div_mul_betaRatio` — the field identity
  `(c₁/c_{i+1})² u_{i+1} = u_i + u_{i+1}`.
* `Hypothesis.centerCoord_conj_stepElevenSeq` — `d_i` acts on `Q₀` by the scalar
  `(c₁/c_{i+1})²`.
* `Hypothesis.stepElevenSeq_snd_fst_eq` — **step (17)**, group form: `w_i = y z_i`.
* `Hypothesis.stepSeventeen` — the invariant of (11) with `w_i` eliminated.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

/-- **The field identity behind step (17)**: `(c₁/c_{i+1})² u_{i+1} = u_i + u_{i+1}`.

Clearing denominators turns it into `c₁² = c_i c_{i+2} + c_{i+1}²`, which is
`betaSum_mul_betaSum_add_two` in characteristic `2`.  Unlike the book's
`u_i/u_{i+1} = 1 + (c₁/c_{i+1})²` this form does not divide by `u_i`, so it also holds at
`i = 0`, where `u_0 = 0`. -/
theorem betaSum_sq_div_mul_betaRatio {E : Type*} [Field E] (h2 : (2 : E) = 0) {β : E}
    (hβ : β ≠ 0) (i : ℕ) (hc1 : betaSum β (i + 1) ≠ 0) (hc2 : betaSum β (i + 2) ≠ 0) :
    (betaSum β 1 / betaSum β (i + 1)) ^ 2 * betaRatio β (i + 1)
      = betaRatio β i + betaRatio β (i + 1) := by
  have hkey := betaSum_mul_betaSum_add_two h2 hβ i
  have hA : betaSum β i * betaSum β (i + 2) + betaSum β (i + 1) ^ 2 = betaSum β 1 ^ 2 := by
    linear_combination hkey + (betaSum β (i + 1) ^ 2) * h2
  have hbr0 : betaRatio β i = betaSum β i / betaSum β (i + 1) := rfl
  have hbr1 : betaRatio β (i + 1) = betaSum β (i + 1) / betaSum β (i + 2) := rfl
  rw [hbr0, hbr1, div_pow, div_mul_div_comm, div_add_div _ _ hc1 hc2,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hc1) hc2) (mul_ne_zero hc1 hc2)]
  linear_combination (-(betaSum β (i + 1) ^ 2 * betaSum β (i + 2))) * hA

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- The coordinate of the `i`-th entry of the sequence, scaled back up by `coord s`. -/
theorem centerCoord_stepElevenSeq_fst {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n + 1 → β ^ i ≠ 1) :
    hyp.centerCoord s M ι (hyp.stepElevenSeq_mem hζ hyQ0 n).1
      = betaRatio β n * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 := by
  have hU := hyp.stepElevenCoord_eq_betaRatio s M ι d hequiv hζ hyQ0 hβ hα n hns
    (fun i hi hin => hpow i hi (by omega))
  rw [stepElevenCoord, div_eq_iff (hyp.centerCoord_distinguishedInvolution_ne_zero s M ι)]
    at hU
  exact hU

/-- **`d_i` acts on `Q₀` by the scalar `(c₁/c_{i+1})²`** — the book's `d_i^{-(1+σ)}`.

Induction along the sequence: `d_0 = ζ` centralizes `Q₀`, so the scalar starts at
`(c₁/c₁)² = 1`; and `d_{i+1} = d_i ζ a⁻²` with `a` the step's element of `K`, whose
inverse has scalar `u_{i+1} = c_{i+1}/c_{i+2}` (its conjugate of `s` *is* `z_{i+1}`), so
the scalar is multiplied by `u_{i+1}²`. -/
theorem centerCoord_conj_stepElevenSeq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n + 1 → β ^ i ≠ 1) :
    ∀ (x w : G) (hx : x ∈ hyp.Q0) (hw : w ∈ hyp.Q0),
      (hyp.stepElevenSeq ζ y n).2.2 * x * ((hyp.stepElevenSeq ζ y n).2.2)⁻¹ = w →
      hyp.centerCoord s M ι hw
        = (betaSum β 1 / betaSum β (n + 1)) ^ 2 * hyp.centerCoord s M ι hx := by
  classical
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hσ0 := hyp.centerCoord_distinguishedInvolution_ne_zero s M ι
  induction n with
  | zero =>
    intro x w hx hw hval
    have hc1 : betaSum β 1 ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow 1 le_rfl le_rfl
    rw [div_self hc1, one_pow, one_mul]
    refine hyp.centerCoord_congr s M ι hw hx ?_
    have hd0 : (hyp.stepElevenSeq ζ y 0).2.2 = ζ := rfl
    rw [hd0] at hval
    rw [← hval, hyp.W_centralizes_Q0 hζ hx]
    group
  | succ n ih =>
    intro x w hx hw hval
    obtain ⟨a, haK, ha, hstep⟩ := hyp.stepElevenSeq_succ_of_ne ζ y n
      (hyp.exists_mem_K_conj_eq_mul hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1
        (hns n (by omega)))
    have haiK : a⁻¹ ∈ hyp.K := hyp.K.inv_mem haK
    have hc1 : betaSum β (n + 1) ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow (n + 1) (by omega) (by omega)
    have hc2 : betaSum β (n + 2) ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow (n + 2) (by omega) (by omega)
    have hfst : (hyp.stepElevenSeq ζ y (n + 1)).1
        = a⁻¹ * hyp.distinguishedInvolution * a := by rw [hstep]
    -- the scalar of `a⁻¹` is `u_{n+1}`
    have hμ : ((M.mu (hyp.kActor haiK, 1) ^ d : M.Eˣ) : M.E) = betaRatio β (n + 1) := by
      have hcc := hyp.centerCoord_conj_eq s M ι d hequiv haiK
        hyp.distinguishedInvolution_mem_Q0 (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1
        (by rw [hfst]; group)
      have hU := hyp.centerCoord_stepElevenSeq_fst s M ι d hequiv hζ hyQ0 hβ hα (n + 1)
        hns hpow
      rw [hcc] at hU
      exact mul_right_cancel₀ hσ0 hU
    -- the group identity: the `ζ` of the step drops out
    have hxa : a⁻¹ * x * a ∈ hyp.Q0 := by
      have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haiK) hx
      rwa [inv_inv] at hmem
    have hxaa : a⁻¹ * (a⁻¹ * x * a) * a ∈ hyp.Q0 := by
      have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haiK) hxa
      rwa [inv_inv] at hmem
    have hw' : (hyp.stepElevenSeq ζ y n).2.2 * (a⁻¹ * (a⁻¹ * x * a) * a)
        * ((hyp.stepElevenSeq ζ y n).2.2)⁻¹ = w := by
      have hd : (hyp.stepElevenSeq ζ y (n + 1)).2.2
          = (hyp.stepElevenSeq ζ y n).2.2 * ζ * (a⁻¹ * a⁻¹) := by
        rw [hstep]
        group
      have hzv : ζ * (a⁻¹ * (a⁻¹ * x * a) * a) * ζ⁻¹ = a⁻¹ * (a⁻¹ * x * a) * a := by
        rw [hyp.W_centralizes_Q0 hζ hxaa]
        group
      rw [← hval, hd]
      calc (hyp.stepElevenSeq ζ y n).2.2 * (a⁻¹ * (a⁻¹ * x * a) * a)
            * ((hyp.stepElevenSeq ζ y n).2.2)⁻¹
          = (hyp.stepElevenSeq ζ y n).2.2 * (ζ * (a⁻¹ * (a⁻¹ * x * a) * a) * ζ⁻¹)
              * ((hyp.stepElevenSeq ζ y n).2.2)⁻¹ := by rw [hzv]
        _ = (hyp.stepElevenSeq ζ y n).2.2 * ζ * (a⁻¹ * a⁻¹) * x
              * ((hyp.stepElevenSeq ζ y n).2.2 * ζ * (a⁻¹ * a⁻¹))⁻¹ := by
            group
            rw [zpow_two]
            simp only [mul_assoc]
    -- assemble
    rw [ih (fun i hi => hns i (by omega)) (fun i hi hin => hpow i hi (by omega))
      (a⁻¹ * (a⁻¹ * x * a) * a) w hxaa hw hw',
      hyp.centerCoord_conj_eq s M ι d hequiv haiK hxa hxaa (by group),
      hyp.centerCoord_conj_eq s M ι d hequiv haiK hx hxa (by group), hμ]
    simp only [betaRatio]
    field_simp

/-- **Step (17)**, group form (Peterfalvi Part II, p. 126): the second component of the
sequence of (11) is `y z_i`, i.e. the book's `v_i = u_i + α`.

The step of (11) sets `w_{i+1} = w_i · z_{i+1}^{d_i⁻¹}`, so with `w_i = y z_i` the claim
reduces to `z_i · z_{i+1}^{d_i⁻¹} = z_{i+1}`, which in coordinates is
`u_i + (c₁/c_{i+1})² u_{i+1} = u_{i+1}` — the identity `betaSum_sq_div_mul_betaRatio`. -/
theorem stepElevenSeq_snd_fst_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ y : G} (hζ : ζ ∈ hyp.W) (hyQ0 : y ∈ hyp.Q0) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n + 1 → β ^ i ≠ 1) :
    (hyp.stepElevenSeq ζ y n).2.1 = y * (hyp.stepElevenSeq ζ y n).1 := by
  classical
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hσ0 := hyp.centerCoord_distinguishedInvolution_ne_zero s M ι
  induction n with
  | zero => rw [hyp.stepElevenSeq_zero]; exact (mul_one y).symm
  | succ n ih =>
    have hprev := ih (fun i hi => hns i (by omega)) (fun i hi hin => hpow i hi (by omega))
    obtain ⟨a, haK, ha, hstep⟩ := hyp.stepElevenSeq_succ_of_ne ζ y n
      (hyp.exists_mem_K_conj_eq_mul hyQ0 (hyp.stepElevenSeq_mem hζ hyQ0 n).1
        (hns n (by omega)))
    have hc1 : betaSum β (n + 1) ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow (n + 1) (by omega) (by omega)
    have hc2 : betaSum β (n + 2) ≠ 0 := by
      rw [Ne, betaSum_eq_zero_iff h2 hβ]
      exact hpow (n + 2) (by omega) (by omega)
    have hfst : (hyp.stepElevenSeq ζ y (n + 1)).1
        = a⁻¹ * hyp.distinguishedInvolution * a := by rw [hstep]
    have hsnd : (hyp.stepElevenSeq ζ y (n + 1)).2.1
        = (hyp.stepElevenSeq ζ y n).2.1 * ((hyp.stepElevenSeq ζ y n).2.2 *
            (a⁻¹ * hyp.distinguishedInvolution * a) *
            ((hyp.stepElevenSeq ζ y n).2.2)⁻¹) := by rw [hstep]
    -- the conjugate `z_{n+1}^{d_n⁻¹}` and its coordinate
    have hcmem : (hyp.stepElevenSeq ζ y n).2.2 * (hyp.stepElevenSeq ζ y (n + 1)).1 *
        ((hyp.stepElevenSeq ζ y n).2.2)⁻¹ ∈ hyp.Q0 :=
      hyp.conj_mem_Q0_of_mem_D (hyp.stepElevenSeq_mem hζ hyQ0 n).2.2
        (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1
    have hcoord := hyp.centerCoord_conj_stepElevenSeq s M ι d hequiv hζ hyQ0 hβ hα n
      (fun i hi => hns i (by omega)) (fun i hi hin => hpow i hi (by omega))
      _ _ (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1 hcmem rfl
    -- compare coordinates in `Q₀`
    have hkey : (hyp.stepElevenSeq ζ y n).1 *
        ((hyp.stepElevenSeq ζ y n).2.2 * (hyp.stepElevenSeq ζ y (n + 1)).1 *
          ((hyp.stepElevenSeq ζ y n).2.2)⁻¹)
        = (hyp.stepElevenSeq ζ y (n + 1)).1 := by
      refine (hyp.eq_iff_centerCoord_eq s M ι
        (hyp.Q0.mul_mem (hyp.stepElevenSeq_mem hζ hyQ0 n).1 hcmem)
        (hyp.stepElevenSeq_mem hζ hyQ0 (n + 1)).1).mpr ?_
      rw [hyp.centerCoord_mul s M ι (hyp.stepElevenSeq_mem hζ hyQ0 n).1 hcmem, hcoord,
        hyp.centerCoord_stepElevenSeq_fst s M ι d hequiv hζ hyQ0 hβ hα n
          (fun i hi => hns i (by omega)) (fun i hi hin => hpow i hi (by omega)),
        hyp.centerCoord_stepElevenSeq_fst s M ι d hequiv hζ hyQ0 hβ hα (n + 1) hns hpow]
      have hfield := betaSum_sq_div_mul_betaRatio h2 hβ n hc1 hc2
      calc betaRatio β n * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0
            + (betaSum β 1 / betaSum β (n + 1)) ^ 2 *
              (betaRatio β (n + 1) *
                hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
          = (betaRatio β n + (betaSum β 1 / betaSum β (n + 1)) ^ 2 * betaRatio β (n + 1))
              * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 := by ring
        _ = (betaRatio β n + (betaRatio β n + betaRatio β (n + 1)))
              * hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 := by rw [hfield]
        _ = betaRatio β (n + 1) *
              hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0 := by
            linear_combination (betaRatio β n *
              hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0) * h2
    rw [hsnd, hprev, hfst] at *
    rw [mul_assoc]
    exact congrArg (fun z => y * z) (by rw [← hfst]; exact hkey)

/-- **Step (17)** (Peterfalvi Part II, p. 126): with the second component eliminated, the
invariant of (11) reads

  `f(ω z_i) = (ω y z_i)^{d_i}`,

the book's `f(ω(0,u_i)) = (ω(0, u_i + α))^{d_i}`. -/
theorem stepSeventeen (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : hyp.IsCenterCoordAction M ι d)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) {β : M.E} (hβ : β ≠ 0)
    (hα : β + β⁻¹
      = hyp.centerCoord s M ι hyQ0
        / hyp.centerCoord s M ι hyp.distinguishedInvolution_mem_Q0)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hpow : ∀ i, 1 ≤ i → i ≤ n + 1 → β ^ i ≠ 1) :
    f (ω * (hyp.stepElevenSeq ζ y n).1)
      = ((hyp.stepElevenSeq ζ y n).2.2)⁻¹ * (ω * (y * (hyp.stepElevenSeq ζ y n).1))
        * (hyp.stepElevenSeq ζ y n).2.2 := by
  rw [← hyp.stepElevenSeq_snd_fst_eq s M ι d hequiv hζ hyQ0 hβ hα n hns hpow]
  exact hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω n

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
