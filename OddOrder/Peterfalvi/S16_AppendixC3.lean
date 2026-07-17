/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_CoreBounds

/-!
# S16_AppendixC3

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

/-! ### BG Appendix C, Lemma C.3 Step 4: the generator relation `s₁ = s⁻¹`

The remaining mathematical gap of BG Appendix C (mmd L4994–5095): the central
prime-line factor of the relevant `k = 3` normal form is `s⁻¹`.  The argument is
the group-relation chain (C.2)–(C.10), a kernel/fixed-point-free step inside
`End ⁅Q, P₀⁆`, and a final contradiction via Steps 2–3.

We work throughout with the prime-field-line scalar `s^x := σ(inl(ofAdd x))` for a
field scalar `x ∈ 𝔽_{p^q}`; conjugating by `σ(inr a)` (`a ∈ U`) scales by `↑a⁻¹`. -/

section Step4

/-- Local `Fact` instance for the Step 4 development, so that
`GaloisField hyp.base.p hyp.base.q` elaborates in signatures with a field scalar
argument.  Scoped to the section; downstream callers supply their own. -/
local instance factPPrimeStep4 {hyp : Hypothesis (G := G)} : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

/-- BG Appendix C prime-field-line scalar `s^x`: the additive-line element
`σ(inl(ofAdd x))` for a field scalar `x ∈ 𝔽_{p^q}`.  The distinguished generator is
`s = s^1`, and `s^x · s^y = s^{x+y}`. -/
noncomputable def sScalar {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) : G :=
  data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x y : GaloisField hyp.base.p hyp.base.q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp),
    ← ofAdd_add]

/-- The trivial scalar `s^0 = 1`. -/
theorem sScalar_zero {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.sScalar 0 = 1 := by
  rw [sScalar, ofAdd_zero, map_one, map_one]

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s = data.sScalar 1 := by
  rw [sScalar, s, fieldNormalizerPrimeLineGenerator]

/-- The field value `↑a ∈ 𝔽_{p^q}` of a norm-one unit `a ∈ U`. -/
def unitVal {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    GaloisField hyp.base.p hyp.base.q :=
  ((a : (GaloisField hyp.base.p hyp.base.q)ˣ) : GaloisField hyp.base.p hyp.base.q)

/-- The field value of an inverse unit is the inverse field value. -/
theorem unitVal_inv {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a⁻¹ = (unitVal a)⁻¹ := by
  simp [unitVal]

/-- The field value of a norm-one unit is nonzero. -/
theorem unitVal_ne_zero {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a ≠ 0 := by
  simp [unitVal]

/-- Conjugating the prime-line scalar `s^x` by `σ(inr a)` scales the exponent by
`↑a⁻¹`: `σ(inr a)⁻¹ · s^x · σ(inr a) = s^{(↑a⁻¹)·x}`.  This is BG's `s^a` notation. -/
theorem sScalar_conj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.sScalar x *
        data.sigma (SemidirectProduct.inr a) =
      data.sScalar (unitVal a⁻¹ * x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl
    (p := hyp.base.p) (q := hyp.base.q) a⁻¹ x
  rw [inv_inv] at h
  exact h

/-- Inversion of a prime-line scalar negates the exponent: `(s^x)⁻¹ = s^{-x}`. -/
theorem sScalar_inv {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sScalar x)⁻¹ = data.sScalar (-x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_inv, ← ofAdd_neg]

/-- `s⁻¹ = s^{-1}` as a prime-line scalar. -/
theorem s_inv_eq_sScalar_neg_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ = data.sScalar (-1) := by
  rw [s_eq_sScalar_one, sScalar_inv]

/-- `s² = s^2` as a prime-line scalar. -/
theorem s_sq_eq_sScalar_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ 2 = data.sScalar 2 := by
  rw [s_eq_sScalar_one, pow_two, sScalar_mul]
  congr 1
  norm_num

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c) =
      data.sScalar
        (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) := by
  rw [sScalar, fieldNormalizerPrimeLineElement]

/-- The central prime-line scalar `s^{-1}` equals `σ(P₀ (-1))`, the middle factor
of the target normal form. -/
theorem sScalar_neg_one_eq_sigma_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.sScalar (-1) =
      data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) := by
  rw [sigma_primeLineElement_eq_sScalar]
  congr 1
  push_cast
  ring

/-- **BG Appendix C, Lemma C.3 Step 4 base relation** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`, BG's identity `s^a · s^b = s²`, where the BG
conjugate `s^a = σ(inr a)⁻¹ · s · σ(inr a) = s^{↑a⁻¹}`. -/
theorem sBGConj_mul_sBGConj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    ((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr a)) *
        ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr b)) =
      data.s ^ 2 := by
  have ha : (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr a) = data.sScalar (unitVal a⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  have hb : (data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr b) = data.sScalar (unitVal b⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  rw [ha, hb, sScalar_mul, hab, s_sq_eq_sScalar_two]

/-- **BG Appendix C, Lemma C.3 Step 4 relation (C.2)** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`,
`s⁻² · (σ(inr a)⁻¹ s σ(inr a)) · (σ(inr b)⁻¹ s σ(inr b)) = 1`. -/
theorem relationC2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    data.s ^ (-2 : ℤ) *
        (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr a)) *
          ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr b))) = 1 := by
  rw [data.sBGConj_mul_sBGConj a b hab, zpow_neg, zpow_two, ← pow_two,
    inv_mul_cancel]

/-- **BG Appendix C, Lemma C.3 Step 4 companion** (mmd L4994): for a norm-one unit
`a` whose inverse field value lies in `E`, BG's companion element `b ∈ E` with
`a + b = 2` exists as a norm-one unit.  Concretely, `↑b⁻¹ = 2 - ↑a⁻¹` (so the base
relation `↑a⁻¹ + ↑b⁻¹ = 2` of `sBGConj_mul_sBGConj` holds), and `↑b⁻¹` again lies in
`E`. -/
theorem exists_companion_of_unitVal_inv_mem_normSetE {hyp : Hypothesis (G := G)}
    (_data : FieldNormalizerData hyp) {a : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q) :
    ∃ b : fieldNormalizerNormOneUnits hyp,
      unitVal a⁻¹ + unitVal b⁻¹ = 2 ∧
        unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hq : 0 < hyp.base.q := hyp.base.q_prime.pos
  have ha2 : (2 - unitVal a⁻¹) ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q :=
    OddOrder.BG.AppC.NormSet.two_sub_mem_normSetE hyp.base.p hyp.base.q ha
  have hval : unitVal
      ((OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
        hyp.base.p hyp.base.q hq ha2)⁻¹)⁻¹ = 2 - unitVal a⁻¹ := by
    rw [inv_inv]
    simp only [unitVal]
    exact OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE_coe
      hyp.base.p hyp.base.q hq ha2
  refine ⟨(OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
      hyp.base.p hyp.base.q hq ha2)⁻¹, ?_, ?_⟩
  · rw [hval]; ring
  · rw [hval]; exact ha2

/-- **BG Appendix C, Lemma C.3 Step 4 E-membership extraction** (mmd L5090–5094):
if the `k = 3` normal form of `s · σ(inr W) · s⁻²` has central prime-line factor
`s⁻¹`, then the inverse field value `(↑W)⁻¹` lies in the norm set `E`.  This is BG's
final paragraph `v₁ = 2 - W ⟹ N(2 - W) = N(v₁) = 1 ⟹ W ∈ E`, read in the repo's
(inverse) convention so that it is `(↑W)⁻¹` that enters `E`. -/
theorem unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (W u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s * data.sigma (SemidirectProduct.inr W) * data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁)) :
    (unitVal W)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  have hN :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
        ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) = 1 :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition W u₁ v₁ hdec
  have hWnorm :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q (unitVal W) = 1 :=
    (OddOrder.BG.AppC.NormSet.mem_normOneUnits_iff_normN hyp.base.p hyp.base.q
      hyp.base.q_prime.ne_zero (W : (GaloisField hyp.base.p hyp.base.q)ˣ)).mp W.property
  have hW0 : unitVal W ≠ 0 := unitVal_ne_zero W
  refine ⟨?_, ?_⟩
  · rw [OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one]
  · have hcalc :
        (2 : GaloisField hyp.base.p hyp.base.q) - (unitVal W)⁻¹ =
          (unitVal W)⁻¹ * ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) := by
      field_simp
    rw [hcalc, OddOrder.BG.AppC.NormSet.normN_mul,
      OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one, one_mul, hN]

/-- **Backward conjugation rewrite**: `(t^n)⁻¹ · σ(inr u) · t^n = σ(inr ((tConj^n)⁻¹ u))`.
This is the inverse-direction companion of
`t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16), giving BG's
right-conjugation `(u)^{t^n} = t⁻ⁿ u tⁿ` directly.  It lets the BG (C.4) connector
`q`-swap telescoping be carried out on the backward `tConj⁻³` form of `M₁`. -/
theorem t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    (data.t ^ n)⁻¹ *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ n =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) :
          fieldNormalizerFrobeniusGroup hyp) := by
  have hself : (data.tConjNormOneUnitsAut ^ n) ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) = u := by
    simp
  have h := data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n
    ((data.tConjNormOneUnitsAut ^ n)⁻¹ u)
  rw [hself] at h
  rw [← h]; group

/-- **Backward `k = 3` first `(C.5)` decomposition** (the entry point for the
capstone proof): for any norm-one unit `a`, the backward form
`s · σ(inr ((tConj³)⁻¹ a⁻¹)) · s⁻²` (BG's `s · (a⁻¹)^{t³} · s⁻²`) admits a Step 1
normal form `σ(inr u₁) · σ(P₀ c) · σ(inr v₁)`.  BG's Lemma C.3 Step 4 pins `c = -1`;
that is the content of `Step4Capstone`. -/
theorem exists_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
  apply data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
  have hs : data.s ∈ hyp.base.P ⊔ hyp.base.U := by
    rw [← zpow_one data.s]; exact data.s_zpow_mem_P_sup_U 1
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹),
      ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ (-2 : ℤ) ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U (-2)
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hs hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge in a neutral form:
any word `s^m · σ(inr w) · s^r`, with the middle term already a concrete
norm-one complement element, lies in `PU`. -/
theorem s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr w, ⟨w, rfl⟩, rfl⟩
  have hmid :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- Neutral Step 4 `(C.5)` decomposition bridge: every word
`s^m · σ(inr w) · s^r` admits Step 1 normal form
`σ(inr u) · σ(P₀ c) · σ(inr v)`. -/
theorem exists_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U m r w)

/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge in a neutral form: if a
word `s^m · σ(inr w) · s^r` is written in Step 1 normal form `u₁ s₁ v₁`, then the
right component is `w = u₁ v₁`.  This is the reusable right-projection step behind
both the forward and backward `k = 3` `(C.5)` equations. -/
theorem right_component_of_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    w = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ hyp.base.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ hyp.base.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (fieldNormalizerPrimeLineElement hyp c) = 1 := by
    simp [fieldNormalizerPrimeLineElement]
  have hσ :
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
          data.s ^ m *
              data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp c) *
              data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C `(C.8)` normal-form transport in neutral form: applying the
concrete `p`-power Frobenius to a `(C.5)` equation keeps the prime-line factor
fixed and raises the three complement terms to their `p`-th powers. -/
theorem frobenius_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u v : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp)) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  let g := fieldNormalizerPrimeLineGenerator hyp
  let W : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr w
  let U : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr u
  let V : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr v
  let S : fieldNormalizerFrobeniusGroup hyp := fieldNormalizerPrimeLineElement hyp c
  have hleft_sigma :
      data.sigma (g ^ m * W * g ^ r) =
        data.s ^ m * data.sigma W * data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_sigma :
      data.sigma (U * S * V) = data.sigma U * data.sigma S * data.sigma V := by
    rw [map_mul, map_mul]
  have hH : g ^ m * W * g ^ r = U * S * V := by
    apply data.sigma_injective
    calc
      data.sigma (g ^ m * W * g ^ r) =
          data.s ^ m * data.sigma W * data.s ^ r := hleft_sigma
      _ = data.sigma U * data.sigma S * data.sigma V := hdec
      _ = data.sigma (U * S * V) := hright_sigma.symm
  have hpowH := congrArg (fieldNormalizerFrobeniusHom hyp) hH
  have hpowH' :
      g ^ m * (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          g ^ r =
        (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          fieldNormalizerPrimeLineElement hyp c *
            (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) := by
    simpa [W, U, V, S, g, map_mul, map_pow,
      fieldNormalizerFrobeniusHom_primeLineGenerator,
      fieldNormalizerFrobeniusHom_inr,
      fieldNormalizerFrobeniusHom_primeLineElement] using hpowH
  have hleft_pow_sigma :
      data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) =
        data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_pow_sigma :
      data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)) =
        data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
              fieldNormalizerFrobeniusGroup hyp) := by
    rw [map_mul, map_mul]
  calc
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
        data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) := hleft_pow_sigma.symm
    _ = data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) :
                fieldNormalizerFrobeniusGroup hyp)) := by
      rw [hpowH']
    _ = data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := hright_pow_sigma

/-- The `mod P` reading of the backward `k = 3` first `(C.5)` equation: BG's
middle term `(a⁻¹)^{t^3}` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 first `(C.5)` factor
`M₁ = s · (a⁻¹)^{t^3} · s⁻²`, in BG's backward conjugation convention. -/
noncomputable def step4M1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) : G :=
  data.s *
      ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
    (data.s⁻¹) ^ 2

/-- BG Appendix C, Lemma C.3 Step 4 second `(C.5)` factor
`M₂ = s³ · (ab⁻¹)^{t^2} · s⁻¹`. -/
noncomputable def step4M2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 3 *
      ((data.t⁻¹) ^ 2 *
        (data.sigma (SemidirectProduct.inr a) *
          (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
    data.s⁻¹

/-- BG Appendix C, Lemma C.3 Step 4 third `(C.5)` factor
`M₃ = s² · b^t · s⁻³`. -/
noncomputable def step4M3 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 2 *
      (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
    (data.s⁻¹) ^ 3

end Step4
end FieldNormalizerData
end OddOrder.Peterfalvi.S16
