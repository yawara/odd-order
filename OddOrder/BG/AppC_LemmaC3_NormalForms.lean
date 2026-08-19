/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_ScalarCalculus

/-!
# BG Appendix C, Lemma C.3 Step 4: relations (C.4)--(C.7) and the (C.5) normal forms

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152), Step 4.

Relations (C.4)--(C.7).  The three connector words appearing between the conjugated factors of
BG's relation (C.4) are single commutator swaps `qᵢ qⱼ = qⱼ qᵢ` inside the abelian group `Q`
(with `qᵢ = (s⁻¹)ⁱ tⁱ ∈ Q`); each rewrites a connector so that the neighbouring `t`-powers
telescope.  That turns the product `M₁ M₂ M₃` of the Step 4 words into relation (C.4).

Writing each `Mᵢ` in the `U P₀ U` normal form of Step 1 gives the (C.5) normal forms
`Mᵢ = σ(inr uᵢ) s^{cᵢ} σ(inr vᵢ)`.  Their prime-line coordinates `c₁` and `c₃` are nonzero
(otherwise Step 2 forces `1 = 0` or `−1 = 0` in `𝔽_p`), and applying the Frobenius produces
relation (C.7).

Migrated from `OddOrder.Peterfalvi.S16_CoreSetupBasic` (issue 0151).
-/

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory
open scoped Pointwise
open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-! ### BG Appendix C (C.4) connector `q`-swaps

The three connector words appearing between the conjugated factors in the BG (C.4)
relation are single `Q`-commutator swaps `qᵢ qⱼ = qⱼ qᵢ` (`qᵢ = (s⁻¹)ⁱ tⁱ ∈ Q`,
`Q` abelian).  Each rewrites a connector to a form whose `t`-powers telescope with
the neighbouring conjugates. -/

/-- BG (C.4) connector 1: `s⁻³ t² s = t⁻¹ s⁻² t³`, by commuting `(s⁻¹)³t³` and
`t⁻¹s` inside the abelian `Q`. -/
theorem connectorC4_one (data : FieldNormalizerData p q G) :
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
theorem connectorC4_two (data : FieldNormalizerData p q G) :
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
theorem connectorC4_three (data : FieldNormalizerData p q G) :
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
theorem relationC4 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
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
    (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) :
    data.step4M1 a =
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) := by
  unfold step4M1
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    3 a⁻¹]
  simp [map_inv]

/-- The second BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^2)⁻¹ (a b⁻¹)`. -/
theorem step4M2_eq_sigma_inr
    (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) :
    data.step4M2 a b =
      data.s ^ (3 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-1 : ℤ) := by
  unfold step4M2
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    2 (a * b⁻¹)]
  simp [map_mul, map_inv]

/-- The third BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = tConj⁻¹ b`. -/
theorem step4M3_eq_sigma_inr
    (data : FieldNormalizerData p q G)
    (b : NormSet.normOneUnits p q) :
    data.step4M3 b =
      data.s ^ (2 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-3 : ℤ) := by
  unfold step4M3
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 b]
  group

/-- Relation `(C.4)` restated using the named BG `(C.5)` factors. -/
theorem relationC4_step4M (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.step4M1 a *
      data.t⁻¹ * data.step4M2 a b * data.t⁻¹ * data.step4M3 b *
        data.s ^ 3 = 1 := by
  simpa [step4M1, step4M2, step4M3] using data.relationC4 a b hab

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` normal-form package for the three
terms appearing in the already-proved relation `(C.4)`.  The `hM*` fields state
the Step 1 normal forms of BG's named factors, and the `right*` fields record the
corresponding mod-`P` complement readings. -/
structure Step4C5NormalForms (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) where
  c1 : ZMod p
  c2 : ZMod p
  c3 : ZMod p
  u1 : NormSet.normOneUnits p q
  v1 : NormSet.normOneUnits p q
  u2 : NormSet.normOneUnits p q
  v2 : NormSet.normOneUnits p q
  u3 : NormSet.normOneUnits p q
  v3 : NormSet.normOneUnits p q
  hM1 :
    data.step4M1 a =
      data.sigma (SemidirectProduct.inr u1 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c1) *
          data.sigma (SemidirectProduct.inr v1 : NormSet.normOneFrobeniusGroup p q)
  hM2 :
    data.step4M2 a b =
      data.sigma (SemidirectProduct.inr u2 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c2) *
          data.sigma (SemidirectProduct.inr v2 : NormSet.normOneFrobeniusGroup p q)
  hM3 :
    data.step4M3 b =
      data.sigma (SemidirectProduct.inr u3 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c3) *
          data.sigma (SemidirectProduct.inr v3 : NormSet.normOneFrobeniusGroup p q)
  right1 : (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u1 * v1
  right2 : (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹) = u2 * v2
  right3 : (data.tConjNormOneUnitsAut ^ 1)⁻¹ b = u3 * v3

/-- The three BG `(C.5)` factors in relation `(C.4)` admit compatible Step 1
normal forms and mod-`P` complement readings. -/
theorem exists_step4C5NormalForms
    (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) :
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
noncomputable def factor1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c1) *
      data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q)

/-- The second normal-form factor `u₂ s₂ v₂` from `(C.5)`. -/
noncomputable def factor2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c2) *
      data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q)

/-- The third normal-form factor `u₃ s₃ v₃` from `(C.5)`. -/
noncomputable def factor3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) *
    data.sigma (primeLineElement p q forms.c3) *
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q)

/-- BG Appendix C `(C.8)` applied to the first `(C.5)` normal form. -/
theorem hM1_frobenius
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M1 (a ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u1 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c1) *
          data.sigma (SemidirectProduct.inr (forms.v1 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (1 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c1) *
            data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q) := by
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
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M2 (a ^ p) (b ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u2 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c2) *
          data.sigma (SemidirectProduct.inr (forms.v2 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (3 : ℤ) *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-1 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c2) *
            data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) := by
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
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.step4M3 (b ^ p) =
      data.sigma (SemidirectProduct.inr (forms.u3 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c3) *
          data.sigma (SemidirectProduct.inr (forms.v3 ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  have hneutral :
      data.s ^ (2 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-3 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c3) *
            data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) := by
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
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    Step4C5NormalForms data (a ^ p) (b ^ p) where
  c1 := forms.c1
  c2 := forms.c2
  c3 := forms.c3
  u1 := forms.u1 ^ p
  v1 := forms.v1 ^ p
  u2 := forms.u2 ^ p
  v2 := forms.v2 ^ p
  u3 := forms.u3 ^ p
  v3 := forms.v3 ^ p
  hM1 := forms.hM1_frobenius
  hM2 := forms.hM2_frobenius
  hM3 := forms.hM3_frobenius
  right1 := by
    have h := congrArg (fun x => x ^ p) forms.right1
    simpa [map_pow, map_inv, mul_pow] using h
  right2 := by
    have h := congrArg (fun x => x ^ p) forms.right2
    simpa [map_pow, map_mul, map_inv, mul_pow] using h
  right3 := by
    have h := congrArg (fun x => x ^ p) forms.right3
    simpa [map_pow, mul_pow] using h

end Step4C5NormalForms

/-- Relation `(C.4)` after substituting the three `(C.5)` normal forms. -/
theorem relationC4_step4C5NormalForms
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
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
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
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
noncomputable def w1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  data.tConjNormOneUnitsAut forms.v2 * forms.u3

/-- BG `w₂ = v₃ u₁^{t⁻²}` from the rearrangement leading to `(C.7)`. -/
noncomputable def w2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  forms.v3 * (data.tConjNormOneUnitsAut ^ 2) forms.u1

/-- BG `w₃ = v₁ u₂^t` from the rearrangement leading to `(C.7)`. -/
noncomputable def w3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    NormSet.normOneUnits p q :=
  forms.v1 * (data.tConjNormOneUnitsAut ^ 1)⁻¹ forms.u2

/-- Under `(C.8)`, the first `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w1
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w1 = forms.w1 ^ p := by
  simp [frobenius, w1, map_pow, mul_pow]

/-- Under `(C.8)`, the second `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w2
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w2 = forms.w2 ^ p := by
  simp [frobenius, w2, map_pow, mul_pow]

/-- Under `(C.8)`, the third `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w3
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w3 = forms.w3 ^ p := by
  simp [frobenius, w3, map_pow, mul_pow]

/-- The ambient reading of `w₁`: `σ(w₁) = t σ(v₂) t⁻¹ σ(u₃)`. -/
theorem sigma_inr_w1 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) =
      data.t * data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) *
        data.t⁻¹ *
          data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) := by
  unfold Step4C5NormalForms.w1
  simp only [map_mul]
  have hφ :
      data.sigma
          (SemidirectProduct.inr (data.tConjNormOneUnitsAut forms.v2) :
            NormSet.normOneFrobeniusGroup p q) =
        data.t * data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q) *
          data.t⁻¹ := by
    simpa using
      (data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 1 forms.v2).symm
  rw [hφ]

/-- The ambient reading of `w₂`: `σ(w₂) = σ(v₃) t² σ(u₁) t⁻²`. -/
theorem sigma_inr_w2 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) =
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) *
        data.t ^ 2 *
          data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) *
            (data.t ^ 2)⁻¹ := by
  unfold Step4C5NormalForms.w2
  simp only [map_mul]
  rw [← data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 2 forms.u1]
  group

/-- The ambient reading of `w₃`: `σ(w₃) = σ(v₁) t⁻¹ σ(u₂) t`. -/
theorem sigma_inr_w3 {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q) =
      data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q) *
        data.t⁻¹ * data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q) *
          data.t := by
  unfold Step4C5NormalForms.w3
  simp only [map_mul]
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 forms.u2]
  group

/-- The three BG `(C.7)` words are elements of `U`, expressed after applying `σ`. -/
theorem sigma_inr_w_mem_U {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) ∈ data.U ∧
      data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) ∈ data.U ∧
        data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q) ∈
          data.U := by
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
theorem c1_ne_zero {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.c1 ≠ 0 := by
  intro hc1
  have hu1 :
      data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u1, ⟨forms.u1, rfl⟩, rfl⟩
  have hv1 :
      data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v1, ⟨forms.v1, rfl⟩, rfl⟩
  have hM1U : data.step4M1 a ∈ data.U := by
    rw [forms.hM1, hc1]
    simpa [primeLineElement, mul_assoc] using data.U.mul_mem hu1 hv1
  have hM1_step :
      data.sigma (primeLineElement p q (1 : ZMod p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-2 : ZMod p)) ∈
          data.U := by
    have h := hM1U
    rw [data.step4M1_eq_sigma_inr] at h
    have hs_one :
        data.s =
          data.sigma (primeLineElement p q (1 : ZMod p)) := by
      simp [FieldNormalizerData.s, primeLineElement_one]
    have hs_neg_two :
        data.s ^ (-2 : ℤ) =
          data.sigma
            (primeLineElement p q (-2 : ZMod p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-2 : ℤ)
    rw [hs_neg_two] at h
    rw [hs_one] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (1 : ZMod p)) (d := (-2 : ZMod p))
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) hM1_step
  rcases hstep with hzero | hone
  · exact one_ne_zero hzero.1
  · have hsum : (1 : ZMod p) + -2 = (-1 : ZMod p) := by
      ring
    have hneg : (-1 : ZMod p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

/-- BG Appendix C `(C.6)` for the third `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₃=0`, then the third normal form lies in `U`;
reading the same element as `s² · U · s⁻³` and applying Step 2 with prime-line
coordinates `(2,-3)` gives either `2=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem c3_ne_zero {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b) :
    forms.c3 ≠ 0 := by
  intro hc3
  have hu3 :
      data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u3, ⟨forms.u3, rfl⟩, rfl⟩
  have hv3 :
      data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v3, ⟨forms.v3, rfl⟩, rfl⟩
  have hM3U : data.step4M3 b ∈ data.U := by
    rw [forms.hM3, hc3]
    simpa [primeLineElement, mul_assoc] using data.U.mul_mem hu3 hv3
  have hM3_step :
      data.sigma (primeLineElement p q (2 : ZMod p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-3 : ZMod p)) ∈
          data.U := by
    have h := hM3U
    rw [data.step4M3_eq_sigma_inr] at h
    have hs_two :
        data.s ^ (2 : ℤ) =
          data.sigma (primeLineElement p q (2 : ZMod p)) := by
      simpa using data.s_zpow_eq_primeLineElement (2 : ℤ)
    have hs_neg_three :
        data.s ^ (-3 : ℤ) =
          data.sigma
            (primeLineElement p q (-3 : ZMod p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-3 : ℤ)
    rw [hs_two, hs_neg_three] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (2 : ZMod p)) (d := (-3 : ZMod p))
    ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) hM3_step
  rcases hstep with hzero | hone
  · exact data.zmod_two_ne_zero hzero.1
  · have hsum : (2 : ZMod p) + -3 = (-1 : ZMod p) := by
      ring
    have hneg : (-1 : ZMod p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

end Step4C5NormalForms

/-- BG Appendix C `(C.7)`, obtained by rearranging the `(C.5)` substitution relation and
absorbing the conjugated complement terms into `w₁`, `w₂`, and `w₃`. -/
theorem relationC7
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q) *
            data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q))⁻¹ := by
  let U1 := data.sigma (SemidirectProduct.inr forms.u1 : NormSet.normOneFrobeniusGroup p q)
  let V1 := data.sigma (SemidirectProduct.inr forms.v1 : NormSet.normOneFrobeniusGroup p q)
  let U2 := data.sigma (SemidirectProduct.inr forms.u2 : NormSet.normOneFrobeniusGroup p q)
  let V2 := data.sigma (SemidirectProduct.inr forms.v2 : NormSet.normOneFrobeniusGroup p q)
  let U3 := data.sigma (SemidirectProduct.inr forms.u3 : NormSet.normOneFrobeniusGroup p q)
  let V3 := data.sigma (SemidirectProduct.inr forms.v3 : NormSet.normOneFrobeniusGroup p q)
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q)
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
theorem unitVal_inv_frobenius_pair (hq : q ≠ 0)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    unitVal (a ^ p)⁻¹ ∈ NormSet.normSetE p q ∧
      unitVal (b ^ p)⁻¹ ∈ NormSet.normSetE p q ∧
        unitVal (a ^ p)⁻¹ + unitVal (b ^ p)⁻¹ = 2 := by
  have hpair := NormSet.normSetE_frobenius_pair
    p q hq ha hb hab
  simpa [unitVal, map_pow] using hpair


end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
