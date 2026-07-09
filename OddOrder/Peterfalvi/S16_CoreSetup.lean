/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_AppendixC3

/-!
# S16_CoreSetup

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceGCore` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceGCore` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

namespace FieldNormalizerData
section Step4

/-- `local instance` は file 境界を越えないため prefix-split 後に再宣言 (原本 = S16_AppendixC3)。 -/
local instance factPPrimeStep4' {hyp : Hypothesis (G := G)} : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

/-! ### BG Appendix C (C.4) connector `q`-swaps

The three connector words appearing between the conjugated factors in the BG (C.4)
relation are single `Q`-commutator swaps `qᵢ qⱼ = qⱼ qᵢ` (`qᵢ = (s⁻¹)ⁱ tⁱ ∈ Q`,
`Q` abelian).  Each rewrites a connector to a form whose `t`-powers telescope with
the neighbouring conjugates. -/

/-- BG (C.4) connector 1: `s⁻³ t² s = t⁻¹ s⁻² t³`, by commuting `(s⁻¹)³t³` and
`t⁻¹s` inside the abelian `Q`. -/
theorem connectorC4_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s =
      data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 :=
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s
        = ((data.s⁻¹) ^ 3 * data.t ^ 3) * (data.t⁻¹ * data.s) := by group
    _ = (data.t⁻¹ * data.s) * ((data.s⁻¹) ^ 3 * data.t ^ 3) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 3) data.t_inv_mul_s_mem_Q
    _ = data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 := by group

/-- BG (C.4) connector 2: `s⁻² t⁻¹ s³ = t⁻³ s t²`, by commuting `(s⁻¹)²t²` and
`(t⁻¹)³s³` inside the abelian `Q`. -/
theorem connectorC4_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3 =
      (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 :=
  calc
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3
        = ((data.s⁻¹) ^ 2 * data.t ^ 2) * ((data.t⁻¹) ^ 3 * data.s ^ 3) := by group
    _ = ((data.t⁻¹) ^ 3 * data.s ^ 3) * ((data.s⁻¹) ^ 2 * data.t ^ 2) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 2)
            (data.t_inv_pow_mul_s_pow_mem_Q 3)
    _ = (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 := by group

/-- BG (C.4) connector 3: `s⁻¹ t⁻¹ s² = t⁻² s t`, by commuting `s⁻¹t` and
`(t⁻¹)²s²` inside the abelian `Q`. -/
theorem connectorC4_three {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2 =
      (data.t⁻¹) ^ 2 * data.s * data.t :=
  calc
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2
        = (data.s⁻¹ * data.t) * ((data.t⁻¹) ^ 2 * data.s ^ 2) := by group
    _ = ((data.t⁻¹) ^ 2 * data.s ^ 2) * (data.s⁻¹ * data.t) :=
          data.Q_mul_comm data.s_inv_mul_t_mem_Q (data.t_inv_pow_mul_s_pow_mem_Q 2)
    _ = (data.t⁻¹) ^ 2 * data.s * data.t := by group

/-- **BG Appendix C, Lemma C.3 relation (C.4)** (mmd L4994, PDF p.150): the
backward conjugated `k = 3` relation
`s⁻³ t² M₁ t⁻¹ M₂ t⁻¹ M₃ s³ = 1`, where
`M₁ = s · (t⁻³ σ(inr a)⁻¹ t³) · s⁻²`, `M₂ = s³ · (t⁻² σ(inr (a b⁻¹)) t²) · s⁻¹`,
`M₃ = s² · (t⁻¹ σ(inr b) t) · s⁻³` are BG's `s^{k-2}(a⁻¹)^{t^k}s^{-k+1}` etc.  The
connector words between the conjugated factors `q`-swap (Connectors 1–3) and the
`t`-powers then telescope to `t⁻¹ · (C.2) · t = 1`. -/
theorem relationC4 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
        (data.s *
            ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
          (data.s⁻¹) ^ 2) *
      data.t⁻¹ *
        (data.s ^ 3 *
            ((data.t⁻¹) ^ 2 *
              (data.sigma (SemidirectProduct.inr a) *
                (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
          data.s⁻¹) *
      data.t⁻¹ *
        (data.s ^ 2 *
            (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
          (data.s⁻¹) ^ 3) *
      data.s ^ 3 = 1 := by
  have hC2 := data.relationC2 a b hab
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
          (data.s *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
            (data.s⁻¹) ^ 2) *
        data.t⁻¹ *
          (data.s ^ 3 *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
            data.s⁻¹) *
        data.t⁻¹ *
          (data.s ^ 2 *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
            (data.s⁻¹) ^ 3) *
        data.s ^ 3
        = ((data.s⁻¹) ^ 3 * data.t ^ 2 * data.s) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              (data.s⁻¹ * data.t⁻¹ * data.s ^ 2) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        group
    _ = (data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * data.s * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 * data.s * data.t) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        rw [data.connectorC4_one, data.connectorC4_two, data.connectorC4_three]
    _ = data.t⁻¹ *
          (data.s ^ (-2 : ℤ) *
            (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr a)) *
              ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr b)))) *
          data.t := by
        group
    _ = data.t⁻¹ * 1 * data.t := by rw [hC2]
    _ = 1 := by group

/-- The first BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^3)⁻¹ a⁻¹`. -/
theorem step4M1_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    data.step4M1 a =
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) := by
  unfold step4M1
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    3 a⁻¹]
  simp [map_inv]
  group

/-- The second BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^2)⁻¹ (a b⁻¹)`. -/
theorem step4M2_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    data.step4M2 a b =
      data.s ^ (3 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-1 : ℤ) := by
  unfold step4M2
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    2 (a * b⁻¹)]
  simp [map_mul, map_inv]
  group

/-- The third BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = tConj⁻¹ b`. -/
theorem step4M3_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) :
    data.step4M3 b =
      data.s ^ (2 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-3 : ℤ) := by
  unfold step4M3
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 b]
  group

/-- Relation `(C.4)` restated using the named BG `(C.5)` factors. -/
theorem relationC4_step4M {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.step4M1 a *
      data.t⁻¹ * data.step4M2 a b * data.t⁻¹ * data.step4M3 b *
        data.s ^ 3 = 1 := by
  simpa [step4M1, step4M2, step4M3] using data.relationC4 a b hab

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` normal-form package for the three
terms appearing in the already-proved relation `(C.4)`.  The `hM*` fields state
the Step 1 normal forms of BG's named factors, and the `right*` fields record the
corresponding mod-`P` complement readings. -/
structure Step4C5NormalForms {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (a b : fieldNormalizerNormOneUnits hyp) where
  c1 : ZMod hyp.base.p
  c2 : ZMod hyp.base.p
  c3 : ZMod hyp.base.p
  u1 : fieldNormalizerNormOneUnits hyp
  v1 : fieldNormalizerNormOneUnits hyp
  u2 : fieldNormalizerNormOneUnits hyp
  v2 : fieldNormalizerNormOneUnits hyp
  u3 : fieldNormalizerNormOneUnits hyp
  v3 : fieldNormalizerNormOneUnits hyp
  hM1 :
    data.step4M1 a =
      data.sigma (SemidirectProduct.inr u1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
          data.sigma (SemidirectProduct.inr v1 : fieldNormalizerFrobeniusGroup hyp)
  hM2 :
    data.step4M2 a b =
      data.sigma (SemidirectProduct.inr u2 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.sigma (SemidirectProduct.inr v2 : fieldNormalizerFrobeniusGroup hyp)
  hM3 :
    data.step4M3 b =
      data.sigma (SemidirectProduct.inr u3 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c3) *
          data.sigma (SemidirectProduct.inr v3 : fieldNormalizerFrobeniusGroup hyp)
  right1 : (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u1 * v1
  right2 : (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹) = u2 * v2
  right3 : (data.tConjNormOneUnitsAut ^ 1)⁻¹ b = u3 * v3

/-- The three BG `(C.5)` factors in relation `(C.4)` admit compatible Step 1
normal forms and mod-`P` complement readings. -/
theorem exists_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    Nonempty (Step4C5NormalForms data a b) := by
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) with
    ⟨c1, u1, v1, h1⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (3 : ℤ)) (r := (-1 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) with
    ⟨c2, u2, v2, h2⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (2 : ℤ)) (r := (-3 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b) with
    ⟨c3, u3, v3, h3⟩
  exact ⟨{
    c1 := c1
    c2 := c2
    c3 := c3
    u1 := u1
    v1 := v1
    u2 := u2
    v2 := v2
    u3 := u3
    v3 := v3
    hM1 := by
      rw [data.step4M1_eq_sigma_inr]
      simpa using h1
    hM2 := by
      rw [data.step4M2_eq_sigma_inr]
      simpa using h2
    hM3 := by
      rw [data.step4M3_eq_sigma_inr]
      simpa using h3
    right1 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (1 : ℤ)) (r := (-2 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
        (u₁ := u1) (v₁ := v1) (c := c1) h1
    right2 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (3 : ℤ)) (r := (-1 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
        (u₁ := u2) (v₁ := v2) (c := c2) h2
    right3 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (2 : ℤ)) (r := (-3 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
        (u₁ := u3) (v₁ := v3) (c := c3) h3
  }⟩

namespace Step4C5NormalForms

/-- The first normal-form factor `u₁ s₁ v₁` from `(C.5)`. -/
noncomputable def factor1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)

/-- The second normal-form factor `u₂ s₂ v₂` from `(C.5)`. -/
noncomputable def factor2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
      data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)

/-- The third normal-form factor `u₃ s₃ v₃` from `(C.5)`. -/
noncomputable def factor3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)

/-- BG Appendix C `(C.8)` applied to the first `(C.5)` normal form. -/
theorem hM1_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M1 (a ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr (forms.v1 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (1 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
            data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM1
    rw [data.step4M1_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (1 : ℤ)) (r := (-2 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
    (u := forms.u1) (v := forms.v1) (c := forms.c1) hneutral
  rw [data.step4M1_eq_sigma_inr]
  simpa [map_pow, map_inv] using hpow

/-- BG Appendix C `(C.8)` applied to the second `(C.5)` normal form. -/
theorem hM2_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M2 (a ^ hyp.base.p) (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.sigma (SemidirectProduct.inr (forms.v2 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (3 : ℤ) *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-1 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
            data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM2
    rw [data.step4M2_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (3 : ℤ)) (r := (-1 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
    (u := forms.u2) (v := forms.v2) (c := forms.c2) hneutral
  rw [data.step4M2_eq_sigma_inr]
  simpa [map_pow, map_mul, map_inv, mul_pow] using hpow

/-- BG Appendix C `(C.8)` applied to the third `(C.5)` normal form. -/
theorem hM3_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M3 (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u3 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr (forms.v3 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (2 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-3 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
            data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM3
    rw [data.step4M3_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (2 : ℤ)) (r := (-3 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
    (u := forms.u3) (v := forms.v3) (c := forms.c3) hneutral
  rw [data.step4M3_eq_sigma_inr]
  simpa [map_pow] using hpow

/-- BG Appendix C `(C.8)` as closure of the whole `(C.5)` normal-form package
under the concrete `p`-power Frobenius. -/
noncomputable def frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    Step4C5NormalForms data (a ^ hyp.base.p) (b ^ hyp.base.p) where
  c1 := forms.c1
  c2 := forms.c2
  c3 := forms.c3
  u1 := forms.u1 ^ hyp.base.p
  v1 := forms.v1 ^ hyp.base.p
  u2 := forms.u2 ^ hyp.base.p
  v2 := forms.v2 ^ hyp.base.p
  u3 := forms.u3 ^ hyp.base.p
  v3 := forms.v3 ^ hyp.base.p
  hM1 := forms.hM1_frobenius
  hM2 := forms.hM2_frobenius
  hM3 := forms.hM3_frobenius
  right1 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right1
    simpa [map_pow, map_inv, mul_pow] using h
  right2 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right2
    simpa [map_pow, map_mul, map_inv, mul_pow] using h
  right3 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right3
    simpa [map_pow, mul_pow] using h

end Step4C5NormalForms

/-- Relation `(C.4)` after substituting the three `(C.5)` normal forms. -/
theorem relationC4_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 *
      data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 * data.s ^ 3 = 1 := by
  have h := data.relationC4_step4M a b hab
  rw [forms.hM1, forms.hM2, forms.hM3] at h
  simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
    Step4C5NormalForms.factor3] using h

/-- The first rearranged relation on the way to BG `(C.7)`: multiply `(C.4)` by
`s^3` on the left and `s^{-3}` on the right after substituting `(C.5)`. -/
theorem relationC7_seed
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
      1 := by
  have h := data.relationC4_step4C5NormalForms hab forms
  calc
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
        data.s ^ 3 *
          ((data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 *
            data.t⁻¹ * forms.factor3 * data.s ^ 3) * (data.s ^ 3)⁻¹ := by
      group
    _ = data.s ^ 3 * 1 * (data.s ^ 3)⁻¹ := by rw [h]
    _ = 1 := by group


namespace Step4C5NormalForms

/-- BG `w₁ = v₂^{t⁻¹} u₃` from the rearrangement leading to `(C.7)`. -/
noncomputable def w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  data.tConjNormOneUnitsAut forms.v2 * forms.u3

/-- BG `w₂ = v₃ u₁^{t⁻²}` from the rearrangement leading to `(C.7)`. -/
noncomputable def w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v3 * (data.tConjNormOneUnitsAut ^ 2) forms.u1

/-- BG `w₃ = v₁ u₂^t` from the rearrangement leading to `(C.7)`. -/
noncomputable def w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v1 * (data.tConjNormOneUnitsAut ^ 1)⁻¹ forms.u2

/-- Under `(C.8)`, the first `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w1
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w1 = forms.w1 ^ hyp.base.p := by
  simp [frobenius, w1, map_pow, mul_pow]

/-- Under `(C.8)`, the second `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w2
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w2 = forms.w2 ^ hyp.base.p := by
  simp [frobenius, w2, map_pow, mul_pow]

/-- Under `(C.8)`, the third `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w3
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w3 = forms.w3 ^ hyp.base.p := by
  simp [frobenius, w3, map_pow, mul_pow]

/-- The ambient reading of `w₁`: `σ(w₁) = t σ(v₂) t⁻¹ σ(u₃)`. -/
theorem sigma_inr_w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) =
      data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ *
          data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) := by
  unfold Step4C5NormalForms.w1
  simp only [map_mul]
  have hφ :
      data.sigma
          (SemidirectProduct.inr (data.tConjNormOneUnitsAut forms.v2) :
            fieldNormalizerFrobeniusGroup hyp) =
        data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t⁻¹ := by
    simpa using
      (data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 1 forms.v2).symm
  rw [hφ]

/-- The ambient reading of `w₂`: `σ(w₂) = σ(v₃) t² σ(u₁) t⁻²`. -/
theorem sigma_inr_w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ 2 *
          data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
            (data.t ^ 2)⁻¹ := by
  unfold Step4C5NormalForms.w2
  simp only [map_mul]
  rw [← data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 2 forms.u1]
  group

/-- The ambient reading of `w₃`: `σ(w₃) = σ(v₁) t⁻¹ σ(u₂) t`. -/
theorem sigma_inr_w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ * data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t := by
  unfold Step4C5NormalForms.w3
  simp only [map_mul]
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 forms.u2]
  group

/-- The three BG `(C.7)` words are elements of `U`, expressed after applying `σ`. -/
theorem sigma_inr_w_mem_U {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
      data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
        data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) ∈
          hyp.base.U := by
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w1, ⟨forms.w1, rfl⟩, rfl⟩
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w3, ⟨forms.w3, rfl⟩, rfl⟩

/-- BG Appendix C `(C.6)` for the first `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₁=0`, then the first normal form lies in `U`;
reading the same element as `s · U · s⁻²` and applying Step 2 with prime-line
coordinates `(1,-2)` gives either `1=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem c1_ne_zero {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.c1 ≠ 0 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hc1
  have hu1 :
      data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u1, ⟨forms.u1, rfl⟩, rfl⟩
  have hv1 :
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v1, ⟨forms.v1, rfl⟩, rfl⟩
  have hM1U : data.step4M1 a ∈ hyp.base.U := by
    rw [forms.hM1, hc1]
    simpa [fieldNormalizerPrimeLineElement, mul_assoc] using hyp.base.U.mul_mem hu1 hv1
  have hM1_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp (1 : ZMod hyp.base.p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) ∈
          hyp.base.U := by
    have h := hM1U
    rw [data.step4M1_eq_sigma_inr] at h
    have hs_one :
        data.s = data.sigma (fieldNormalizerPrimeLineElement hyp (1 : ZMod hyp.base.p)) := by
      simp [s, fieldNormalizerPrimeLineElement_one]
    have hs_neg_two :
        data.s ^ (-2 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-2 : ℤ)
    rw [hs_neg_two] at h
    rw [hs_one] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (1 : ZMod hyp.base.p)) (d := (-2 : ZMod hyp.base.p))
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) hM1_step
  rcases hstep with hzero | hone
  · exact one_ne_zero hzero.1
  · have hsum : (1 : ZMod hyp.base.p) + -2 = (-1 : ZMod hyp.base.p) := by
      ring
    have hneg : (-1 : ZMod hyp.base.p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

/-- BG Appendix C `(C.6)` for the third `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₃=0`, then the third normal form lies in `U`;
reading the same element as `s² · U · s⁻³` and applying Step 2 with prime-line
coordinates `(2,-3)` gives either `2=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem c3_ne_zero {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.c3 ≠ 0 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hc3
  have hu3 :
      data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u3, ⟨forms.u3, rfl⟩, rfl⟩
  have hv3 :
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v3, ⟨forms.v3, rfl⟩, rfl⟩
  have hM3U : data.step4M3 b ∈ hyp.base.U := by
    rw [forms.hM3, hc3]
    simpa [fieldNormalizerPrimeLineElement, mul_assoc] using hyp.base.U.mul_mem hu3 hv3
  have hM3_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp (2 : ZMod hyp.base.p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-3 : ZMod hyp.base.p)) ∈
          hyp.base.U := by
    have h := hM3U
    rw [data.step4M3_eq_sigma_inr] at h
    have hs_two :
        data.s ^ (2 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (2 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (2 : ℤ)
    have hs_neg_three :
        data.s ^ (-3 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (-3 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-3 : ℤ)
    rw [hs_two, hs_neg_three] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (2 : ZMod hyp.base.p)) (d := (-3 : ZMod hyp.base.p))
    ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) hM3_step
  rcases hstep with hzero | hone
  · exact hyp.zmod_two_ne_zero hzero.1
  · have hsum : (2 : ZMod hyp.base.p) + -3 = (-1 : ZMod hyp.base.p) := by
      ring
    have hneg : (-1 : ZMod hyp.base.p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

end Step4C5NormalForms

/-- BG Appendix C `(C.7)`, obtained by rearranging the `(C.5)` substitution relation and
absorbing the conjugated complement terms into `w₁`, `w₂`, and `w₃`. -/
theorem relationC7
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) *
            data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp))⁻¹ := by
  let U1 := data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp)
  let V1 := data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)
  let U2 := data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp)
  let V2 := data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)
  let U3 := data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp)
  let V3 := data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  have hseed :
      data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 =
        1 := by
    have h := data.relationC7_seed hab forms
    simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
      Step4C5NormalForms.factor3, U1, V1, U2, V2, U3, V3, S1, S2, S3, mul_assoc]
      using h
  have hw1_t : data.t⁻¹ * W1 = V2 * data.t⁻¹ * U3 := by
    dsimp [W1, V2, U3]
    rw [forms.sigma_inr_w1]
    group
  have hw2_t : W2 * data.t ^ 2 = V3 * data.t ^ 2 * U1 := by
    dsimp [W2, V3, U1]
    rw [forms.sigma_inr_w2]
    group
  have hw3_t : W3 * data.t⁻¹ = V1 * data.t⁻¹ * U2 := by
    dsimp [W3, V1, U2]
    rw [forms.sigma_inr_w3]
    group
  have hword :
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
        1 := by
    calc
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
          data.t ^ 2 * U1 * S1 * (W3 * data.t⁻¹) * S2 *
            (data.t⁻¹ * W1) * S3 * V3 := by
        group
      _ = data.t ^ 2 * U1 * S1 * (V1 * data.t⁻¹ * U2) * S2 *
            (V2 * data.t⁻¹ * U3) * S3 * V3 := by
        rw [hw3_t, hw1_t]
      _ = data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 := by
        group
      _ = 1 := hseed
  have hwordPrime :
      (data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
          (W1 * S3 * V3) = 1 := by
    simpa [mul_assoc] using hword
  have hmain : data.t⁻¹ * S2 * data.t⁻¹ =
      (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
    calc
      data.t⁻¹ * S2 * data.t⁻¹ =
          (data.t ^ 2 * U1 * S1 * W3)⁻¹ *
            ((data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
              (W1 * S3 * V3)) * (W1 * S3 * V3)⁻¹ := by
        group
      _ = (data.t ^ 2 * U1 * S1 * W3)⁻¹ * 1 * (W1 * S3 * V3)⁻¹ := by
        rw [hwordPrime]
      _ = ((W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3))⁻¹ := by
        group
      _ = (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
        have hD : W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
            (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
          calc
            W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
                W1 * S3 * (W2 * data.t ^ 2) * S1 * W3 := by
              group
            _ = W1 * S3 * (V3 * data.t ^ 2 * U1) * S1 * W3 := by
              rw [hw2_t]
            _ = (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
              group
        rw [← hD]
  simpa [S1, S2, S3, W1, W2, W3, mul_assoc] using hmain


/-- BG Appendix C `(C.8)` Frobenius entry: if the inverse field values of `a` and
`b` lie in `E` and satisfy the companion equation, then the inverse field values of
`a^p` and `b^p` again lie in `E` and satisfy the same companion equation. -/
theorem unitVal_inv_frobenius_pair
    {hyp : Hypothesis (G := G)} {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    unitVal (a ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
      unitVal (b ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
        unitVal (a ^ hyp.base.p)⁻¹ + unitVal (b ^ hyp.base.p)⁻¹ = 2 := by
  have hpair := OddOrder.BG.AppC.NormSet.normSetE_frobenius_pair
    hyp.base.p hyp.base.q hyp.base.q_prime.ne_zero ha hb hab
  simpa [unitVal, map_pow] using hpair

/-- BG Appendix C `(C.9)` for the third word: comparing `(C.7)` for `(a,b)`
with `(C.7)` for `(a^p,b^p)` shows that
`S₁ W₃^(p-1) S₁⁻¹` lies in `PU` and its `t²`-conjugate also lies in `PU`. -/
theorem relationC9_w3_mem_P_sup_U_and_conj
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    S1 * W3pow * S1⁻¹ ∈ hyp.base.P ⊔ hyp.base.U ∧
      data.t ^ 2 * (S1 * W3pow * S1⁻¹) * (data.t ^ 2)⁻¹ ∈
        hyp.base.P ⊔ hyp.base.U := by
  classical
  dsimp only
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hA_mem : A ∈ PU := by
    change A ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 * SemidirectProduct.inr forms.w2,
      trivial, ?_⟩
    simp [A, W1, W2, S3, map_mul]
  have hAp_mem : Ap ∈ PU := by
    change Ap ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr (forms.w1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 *
          SemidirectProduct.inr (forms.w2 ^ hyp.base.p), trivial, ?_⟩
    simp [Ap, W1p, W2p, S3, map_mul]
  have hX_mem : X ∈ PU := by
    change X ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨fieldNormalizerPrimeLineElement hyp forms.c1 *
        (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
          fieldNormalizerFrobeniusGroup hyp) *
          (fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹, trivial, ?_⟩
    simp [X, S1, W3pow, map_mul, map_inv]
  have hconj_mem : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    have hleft : Ap⁻¹ * A ∈ PU := PU.mul_mem (PU.inv_mem hAp_mem) hA_mem
    rwa [hApA] at hleft
  exact ⟨by simpa [PU, X, S1, W3pow] using hX_mem,
    by simpa [PU, X, S1, W3pow] using hconj_mem⟩


/-- BG Appendix C exact `(C.9)` word equation.  This is the equality displayed
just before `(C.9)`: after comparing `(C.7)` for `(a,b)` with the Frobenius-powered
`(C.7)`, the remaining `w₁/w₂` word is a `t²`-conjugate of
`S₁ W₃^(p-1) S₁⁻¹`. -/
theorem relationC9_w3_word
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by
  classical
  dsimp only
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hleft : W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2 = Ap⁻¹ * A := by
    simp [A, Ap]
    group
  calc
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) *
        data.t ^ 2 =
        (data.t ^ 2)⁻¹ * (Ap⁻¹ * A) * data.t ^ 2 := by
      rw [hleft]
    _ = X := by
      rw [hApA]
      group

/-- After the third word has been killed, exact `(C.9)` and Step 2 force the
remaining two words to satisfy condition `(A)`.  The nontriviality of the third
prime-line factor is the `(C.6)` input, kept explicit here because the global
`C.6` theorem is a separate frontier. -/
theorem relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc3 : forms.c3 ≠ 0) (hw3 : forms.w3 = 1) :
    forms.w1 ^ (hyp.base.p - 1) = 1 ∧ forms.w2 ^ (hyp.base.p - 1) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U1 := (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1
  let L := W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2
  have hC9 := data.relationC9_w3_word ha hb hab forms
  have hC9' : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = S1 * W3pow * S1⁻¹ := by
    simpa [S1, S3, W1, W2, W1p, W2p, W3pow, L, mul_assoc] using hC9
  have hW3pow_one : W3pow = 1 := by
    simp [W3pow, hw3]
  have hL_one : L = 1 := by
    have hconj : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = 1 := by
      simpa [hW3pow_one] using hC9'
    calc
      L = data.t ^ 2 * ((data.t ^ 2)⁻¹ * L * data.t ^ 2) * (data.t ^ 2)⁻¹ := by
        group
      _ = 1 := by
        rw [hconj]
        group
  have hU1_sigma : data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) =
      W1p⁻¹ * W1 := by
    simp [U1, W1p, W1, map_mul, map_inv]
  have hS3_inv : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) = S3⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c3)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S3⁻¹ := by
        simp [S3]
  have hW2p_mem : W2p ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr (forms.w2 ^ hyp.base.p),
      ⟨forms.w2 ^ hyp.base.p, rfl⟩, rfl⟩
  have hW2_mem : W2 ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  have hW2_ratio_mem : W2p * W2⁻¹ ∈ hyp.base.U :=
    hyp.base.U.mul_mem hW2p_mem (hyp.base.U.inv_mem hW2_mem)
  have hL' : W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2 = 1 := by
    simpa [L, mul_assoc] using hL_one
  have hmid_eq : S3⁻¹ * W1p⁻¹ * W1 * S3 = W2p * W2⁻¹ := by
    calc
      S3⁻¹ * W1p⁻¹ * W1 * S3 =
          W2p * (W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2) * W2⁻¹ := by
        group
      _ = W2p * 1 * W2⁻¹ := by
        rw [hL']
      _ = W2p * W2⁻¹ := by
        group
  have hmid_mem : S3⁻¹ * W1p⁻¹ * W1 * S3 ∈ hyp.base.U := by
    rw [hmid_eq]
    exact hW2_ratio_mem
  have hmem_step : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) *
        data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) ∈ hyp.base.U := by
    simpa [hS3_inv, hU1_sigma, S3, mul_assoc] using hmid_mem
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -forms.c3) (d := forms.c3) U1 hmem_step
  have hU1_one : U1 = 1 := by
    rcases hstep with hzero | hone
    · have hc3_zero : forms.c3 = 0 := by
        simpa using (neg_eq_zero.mp hzero.1)
      exact False.elim (hc3 hc3_zero)
    · exact hone.1
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hU1_one' : (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1 = 1 := by
    simpa [U1] using hU1_one
  have hw1p_eq : forms.w1 ^ hyp.base.p = forms.w1 := by
    calc
      forms.w1 ^ hyp.base.p = forms.w1 ^ hyp.base.p * 1 := by simp
      _ = forms.w1 ^ hyp.base.p * ((forms.w1 ^ hyp.base.p)⁻¹ * forms.w1) := by
        rw [hU1_one']
      _ = forms.w1 := by
        group
  have hw1 : forms.w1 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w1 ^ (hyp.base.p - 1) * forms.w1 = forms.w1 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w1 ^ (hyp.base.p - 1) =
          (forms.w1 ^ (hyp.base.p - 1) * forms.w1) * forms.w1⁻¹ := by
        group
      _ = forms.w1 ^ hyp.base.p * forms.w1⁻¹ := by
        rw [hpow]
      _ = forms.w1 * forms.w1⁻¹ := by
        rw [hw1p_eq]
      _ = 1 := by
        group
  have hW1_ratio_one : W1p⁻¹ * W1 = 1 := by
    rw [← hU1_sigma, hU1_one]
    simp
  have hW2_ratio_one : W2p⁻¹ * W2 = 1 := by
    calc
      W2p⁻¹ * W2 = W2p⁻¹ * S3⁻¹ * (W1p⁻¹ * W1) * S3 * W2 := by
        rw [hW1_ratio_one]
        group
      _ = 1 := by
        simpa [L, mul_assoc] using hL_one
  have hW2p_eq : W2p = W2 := by
    calc
      W2p = W2p * 1 := by simp
      _ = W2p * (W2p⁻¹ * W2) := by
        rw [hW2_ratio_one]
      _ = W2 := by
        group
  have hw2p_eq : forms.w2 ^ hyp.base.p = forms.w2 := by
    have hinr : (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) = SemidirectProduct.inr forms.w2 :=
      data.sigma_injective (by simpa [W2p, W2] using hW2p_eq)
    exact (SemidirectProduct.inr_inj.mp hinr)
  have hw2 : forms.w2 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w2 ^ (hyp.base.p - 1) * forms.w2 = forms.w2 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w2 ^ (hyp.base.p - 1) =
          (forms.w2 ^ (hyp.base.p - 1) * forms.w2) * forms.w2⁻¹ := by
        group
      _ = forms.w2 ^ hyp.base.p * forms.w2⁻¹ := by
        rw [hpow]
      _ = forms.w2 * forms.w2⁻¹ := by
        rw [hw2p_eq]
      _ = 1 := by
        group
  exact ⟨hw1, hw2⟩


/-- BG Appendix C condition `(A)` in S16 form: a norm-one unit with
`(p - 1)`-st power equal to `1` is trivial. -/
theorem normOneUnit_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) (hu : u ^ (hyp.base.p - 1) = 1) :
    u = 1 :=
  OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
    hyp.base.p hyp.base.q hyp.base.q_prime data.cyclotomic_coprime u hu

namespace Step4C5NormalForms

/-- The post-`(C.9)` condition `(A)` step for the three BG words. -/
theorem w_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 ^ (hyp.base.p - 1) = 1)
    (hw2 : forms.w2 ^ (hyp.base.p - 1) = 1)
    (hw3 : forms.w3 ^ (hyp.base.p - 1) = 1) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 :=
  ⟨data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w1 hw1,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w2 hw2,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3⟩

end Step4C5NormalForms


/-- BG Appendix C `(C.10)`: once `(C.9)` and condition `(A)` have forced
`w₁ = w₂ = w₃ = 1`, relation `(C.7)` collapses to
`t² s₁ t⁻¹ s₂ t⁻¹ s₃ = 1`. -/
theorem relationC10_of_w_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 = 1) (hw2 : forms.w2 = 1) (hw3 : forms.w3 = 1) :
    data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  have hC7 := data.relationC7 hab forms
  rw [hw1, hw2, hw3] at hC7
  simp only [map_one, one_mul, mul_one] at hC7
  calc
    data.t ^ 2 * S1 * data.t⁻¹ * S2 * data.t⁻¹ * S3 =
        data.t ^ 2 * S1 * (data.t⁻¹ * S2 * data.t⁻¹) * S3 := by
      group
    _ = data.t ^ 2 * S1 * (S3 * data.t ^ 2 * S1)⁻¹ * S3 := by
      rw [hC7]
    _ = 1 := by group

/-- BG Appendix C Step 4 after Step 3: once Step 3 supplies the membership
`s₁ w₃^(p-1) s₁⁻¹ ∈ U`, Step 2 and condition `(A)` force
`w₁ = w₂ = w₃ = 1`, and hence `(C.10)`.

The two nonzero hypotheses are the `(C.6)` inputs for the first and third
prime-line factors.  The remaining frontier is to produce the displayed
`U`-membership from the Step 3 intersection theorem. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hw3U :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma
            (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
              fieldNormalizerFrobeniusGroup hyp) *
            (data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1))⁻¹ ∈ hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U3 := forms.w3 ^ (hyp.base.p - 1)
  have hS1_inv :
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) = S1⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S1⁻¹ := by
        simp [S1]
  have hU3_sigma :
      data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) =
        W3pow := by
    simp [U3, W3pow]
  have hmem_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) ∈ hyp.base.U := by
    simpa [S1, W3pow, U3, hS1_inv, hU3_sigma, mul_assoc] using hw3U
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := forms.c1) (d := -forms.c1) U3 hmem_step
  have hU3_one : U3 = 1 := by
    rcases hstep with hzero | hone
    · exact False.elim (hc1 hzero.1)
    · exact hone.1
  have hw3_pow : forms.w3 ^ (hyp.base.p - 1) = 1 := by
    simpa [U3] using hU3_one
  have hw3 : forms.w3 = 1 :=
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3_pow
  have h12 :=
    data.relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one ha hb hab forms hc3 hw3
  have hwords := forms.w_eq_one_of_pow_sub_one_eq_one h12.1 h12.2 hw3_pow
  have hC10 := data.relationC10_of_w_eq_one hab forms hwords.1 hwords.2.1 hwords.2.2
  exact ⟨hwords.1, hwords.2.1, hwords.2.2, hC10⟩

/-- BG Appendix C Step 4, Step 3 producer in the `U` branch: the concrete `(C.9)`
membership places `S₁ W₃^(p-1) S₁⁻¹` in `PU` and, after applying the inverse Lean
conjugation convention, in `(PU)^{t^{-2}}`.  If Step 3 identifies that
intersection with `U`, the already-landed `(C.9)` collapse gives `w₁=w₂=w₃=1`
and hence `(C.10)`.

This theorem isolates the remaining Step 3 obstruction: after this point the only
missing part of the producer is ruling out the alternative intersection `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hstep3 :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let X := S1 * W3pow * S1⁻¹
  have hC9 := data.relationC9_w3_mem_P_sup_U_and_conj ha hb hab forms
  have hX_PU : X ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.1
  have hX_conj_PU : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.2
  have hX_smul : X ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
        data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
      rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
          (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ X from rfl,
        MulAut.conj_inv_apply]
      group
    rwa [hsmul]
  have hX_inf : X ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := ⟨hX_PU, hX_smul⟩
  have hX_U : X ∈ hyp.base.U := by
    have hX_inf' : X ∈ (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) := by
      simpa [PU] using hX_inf
    rwa [hstep3] at hX_inf'
  exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    ha hb hab forms hc1 hc3 (by simpa [X, S1, W3pow] using hX_U)

/-- BG Appendix C Step 4 after applying Step 3 to the `(C.9)` element: either
`(C.10)` has already been forced, or the only remaining Step 3 obstruction is
the bad branch where the relevant intersection is all of `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    (forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1) ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U := by
  classical
  have ht2_norm : data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    data.t_pow_normalizes_U 2
  have ht2_inv_norm : (data.t ^ 2)⁻¹ ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    (Subgroup.normalizer (hyp.base.U : Set G)).inv_mem ht2_norm
  have hstep3 := data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U ht2_inv_norm
  rcases hstep3 with hU | hPU
  · left
    exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
      ha hb hab forms hc1 hc3 hU
  · right
    exact hPU

/-- BG Appendix C Step 3 bad branch, first concrete consequence: if the relevant
intersection is all of `PU`, then conjugation by `t²` sends every element of
`PU` back into `PU`.

The following bad-branch lemmas upgrade this inclusion first to `t² ∈ N_G(PU)`
and then, via `P char PU`, to `t² ∈ N_G(P)`.  The remaining Step 3 work is to
pass from `t²` to `P₁ ≤ N_G(P)` and then derive the `P₀=P₁` contradiction. -/
theorem step3_badBranch_t_sq_conj_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U →
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ ∈ hyp.base.P ⊔ hyp.base.U := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  intro x hx
  have hx_inf : x ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := by
    rw [hbad]
    simpa [PU] using hx
  have hx_smul : x ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ := by
    rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
        (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ x from rfl,
      MulAut.conj_inv_apply]
    group
  rw [hsmul] at hx_smul
  simpa [PU] using hx_smul

/-- BG Appendix C Step 3 bad branch: the previous one-sided inclusion upgrades to
normalization of `PU` because `t²` has finite `p`-power order.  This is the
formal version of BG's line “hence `t₁` normalizes `PU`” for the current
`t₁ = t²` branch. -/
theorem step3_badBranch_t_sq_normalizes_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.t ^ 2 ∈ Subgroup.normalizer ((hyp.base.P ⊔ hyp.base.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let g : G := data.t ^ 2
  have hinc : ∀ ⦃x : G⦄, x ∈ PU → g * x * g⁻¹ ∈ PU := by
    intro x hx
    simpa [g, PU] using data.step3_badBranch_t_sq_conj_mem_P_sup_U hbad hx
  have hgpow : g ^ hyp.base.p = 1 := by
    calc
      g ^ hyp.base.p = (data.t ^ 2) ^ hyp.base.p := by rfl
      _ = data.t ^ (2 * hyp.base.p) := by rw [pow_mul]
      _ = data.t ^ (hyp.base.p * 2) := by rw [Nat.mul_comm]
      _ = (data.t ^ hyp.base.p) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [data.t_pow_p_eq_one, one_pow]
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        have hn := ih hx
        have h := hinc hn
        simpa [pow_succ', mul_assoc] using h
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have g_inv_eq : g⁻¹ = g ^ (hyp.base.p - 1) := by
    have hmul : g ^ (hyp.base.p - 1) * g = 1 := by
      calc
        g ^ (hyp.base.p - 1) * g = g ^ ((hyp.base.p - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ hyp.base.p := by
          rw [Nat.sub_one_add_one_eq_of_pos hp_pos]
        _ = 1 := hgpow
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    have h := hiter (hyp.base.p - 1) hx
    simpa [g_inv_eq] using h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hinc hx
  · intro hx
    have hpre := hinv_inc (x := g * x * g⁻¹) hx
    convert hpre using 1
    group

/-- BG Appendix C Step 3 bad branch after `P char PU`: the forced normalization of
`PU` already forces `t²` to normalize the additive kernel `P`. -/
theorem step3_badBranch_t_sq_normalizes_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.P : Set G) :=
  data.normalizer_P_sup_U_le_normalizer_P
    (data.step3_badBranch_t_sq_normalizes_P_sup_U hbad)

/-- BG Appendix C Step 3 bad branch after cyclic generation: since `P₁=⟨t⟩` and
`p` is odd, the normalization of `P` by `t²` forces all of `P₁` to normalize
`P`. -/
theorem step3_badBranch_P1_le_normalizer_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.P : Set G) :=
  data.P1_le_normalizer_P_of_t_sq_mem
    (data.step3_badBranch_t_sq_normalizes_P hbad)

/-- BG Appendix C Step 3 bad branch after `P ∩ W₂Q = W₂`: the forced
normalization of `P` by `P₁`, together with `P₁ ≤ W₂Q`, forces `P₁` to normalize
`W₂ = P ∩ W₂Q`. -/
theorem step3_badBranch_P1_le_normalizer_W2
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.W2 : Set G) :=
  data.P1_le_normalizer_W2_of_le_normalizer_P
    (data.step3_badBranch_P1_le_normalizer_P hbad)

/-- BG Appendix C Step 3 bad branch is impossible: it forces `P₁ = W₂`, while
`P₁` normalizes `U` and `W₂` does not. -/
theorem step3_badBranch_false [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    False :=
  data.P1_ne_W2
    (data.P1_eq_W2_of_le_normalizer_W2
      (data.step3_badBranch_P1_le_normalizer_W2 hbad))

/-- BG Appendix C Step 4 after Step 3 and the bad-branch contradiction: with the
two `(C.6)` nonzero inputs for the first and third prime-line factors, exact
`(C.9)` no longer leaves a Step 3 alternative.  The dichotomy either gives the
`U` branch, where the existing `(C.9)` collapse forces `w₁=w₂=w₃=1` and `(C.10)`,
or gives the bad branch, now contradictory by `step3_badBranch_false`.

This is the branch-free Step 3/C.10 producer still waiting only for the global
`(C.6)` wiring that supplies `forms.c1 ≠ 0` and `forms.c3 ≠ 0`. -/
theorem relationC9_w_eq_one_and_relationC10_of_c6 [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  rcases data.relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
      ha hb hab forms hc1 hc3 with hC10 | hbad
  · exact hC10
  · exact False.elim (data.step3_badBranch_false hbad)

/-- BG Appendix C Step 4 branch-free `(C.10)` producer: exact `(C.9)`, Step 3,
the bad-branch contradiction, and the `(C.6)` nonzero facts for `c₁` and `c₃`
together force `w₁=w₂=w₃=1` and the displayed `(C.10)` relation. -/
theorem relationC9_w_eq_one_and_relationC10 [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 :=
  data.relationC9_w_eq_one_and_relationC10_of_c6
    ha hb hab forms forms.c1_ne_zero forms.c3_ne_zero


/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**, as a statement: for
every norm-one unit `a` whose inverse field value `↑a⁻¹` lies in `E` (so that BG's
companion `b = 2 - ↑a⁻¹` is again a norm-one value), the `k = 3` first normal form
of `s · σ(inr ((tConj⁻³)(a⁻¹))) · s⁻²` has central prime-line factor `s⁻¹`.  This is
the remaining mathematical content; it follows from the (C.2)–(C.10) chain and the
kernel/fixed-point-free argument inside `End ⁅Q, P₀⁆`.

We use the **backward** conjugation `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`, so that
`σ(inr ((tConj⁻³)(a⁻¹))) = t⁻³ σ(inr a⁻¹) t³` matches BG's `(a⁻¹)^{t³}` exactly (BG's
right-conjugation convention `x^{t^k} = t⁻ᵏ x tᵏ`).  This makes the BG (C.4) connector
`q`-swap telescoping (`qⱼ = s⁻ʲtʲ ∈ Q`) port directly; the downstream
`normSetE_eq_inv_of_twisted_normOne_step` is `φ`-agnostic (it only needs `φ^p = 1`,
and `((tConj^3)⁻¹)^p = 1`). -/
def Step4Capstone {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : Prop :=
  ∀ a : fieldNormalizerNormOneUnits hyp,
    unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
      ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
        data.s *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁) *
          data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
            data.sigma (SemidirectProduct.inr v₁)

/-- The Step 4 capstone yields BG's one-step twisted-inverse output for the
backward conjugation automorphism `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`:
`a ∈ E ⟹ (a⁻¹)^{t³} ∈ E` (BG's right-conjugation).  We apply the capstone at
`a = u⁻¹` so that its hypothesis `↑(u⁻¹)⁻¹ = ↑u ∈ E` is exactly the input, and the
E-extraction `(↑W)⁻¹ ∈ E` (with `W = (tConj⁻³)(u)`) reads as `↑((tConj⁻³)(u⁻¹)) ∈ E`. -/
theorem normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hcap : data.Step4Capstone) :
    OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
      (p := hyp.base.p) (q := hyp.base.q) (data.tConjNormOneUnitsAut ^ 3)⁻¹ := by
  intro u hu
  have hcond : unitVal (u⁻¹)⁻¹ ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
    rw [inv_inv]; exact hu
  obtain ⟨u₁, v₁, hdec⟩ := hcap u⁻¹ hcond
  have hext := data.unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ (u⁻¹)⁻¹) u₁ v₁ hdec
  rw [inv_inv, ← unitVal_inv, ← map_inv] at hext
  rw [OddOrder.BG.AppC.NormSet.twistedInv]
  exact hext

/-- The Step 4 capstone supplies the AppC norm-one twisted-inverse output. -/
theorem appCNormSetTwistedNormOneStep_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetTwistedNormOneStep hyp := by
  refine ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹, ?_,
    data.normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone hcap⟩
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, data.tConjNormOneUnitsAut_pow_p_eq_one,
    one_pow, inv_one]

/-- The Step 4 capstone supplies the AppC generator relation `∀ a ∈ E, N(2a-1)=1`,
without any carrier field.  This is what `appC_normSet_generator_relation` (proved
once `step4Capstone` is available) calls. -/
theorem appC_normSet_generator_relation_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp
    (data.appCNormSetTwistedNormOneStep_of_capstone hcap)

end Step4
end FieldNormalizerData
end OddOrder.Peterfalvi.S16
