/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_ConjugateLine

/-!
# BG Appendix C, Lemma C.3 Step 4: the scalar calculus `s^x` and the words `M₁, M₂, M₃`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152), Step 4.

BG writes the prime-field line multiplicatively as `s^x := σ(inl(ofAdd x))` for a field scalar
`x ∈ 𝔽_{p^q}`, so that `s^x · s^y = s^{x+y}` and conjugating by `σ(inr a)` for `a ∈ U` scales
the exponent by `↑a⁻¹` (BG's `s^a` notation).  This file sets up that calculus and runs it
through the first relations of Step 4.

The remaining mathematical content of Appendix C is that the central prime-line factor of the
relevant `k = 3` normal form is `s⁻¹`.  Here we produce relation (C.2), obtain the Step 4
decompositions of `s^{±1} σ(inr a) s^{∓2}` and their inverse forms, and package the three
words `M₁, M₂, M₃` whose (C.4) relation drives the rest of the argument.

Migrated from `OddOrder.Peterfalvi.S16_AppendixC3` (issue 0151).
-/

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory
open scoped Pointwise
open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-! ### BG Appendix C, Lemma C.3 Step 4: the generator relation `s₁ = s⁻¹`

The remaining mathematical gap of BG Appendix C (mmd L4994–5095): the central
prime-line factor of the relevant `k = 3` normal form is `s⁻¹`.  The argument is
the group-relation chain (C.2)–(C.10), a kernel/fixed-point-free step inside
`End ⁅Q, P₀⁆`, and a final contradiction via Steps 2–3.

We work throughout with the prime-field-line scalar `s^x := σ(inl(ofAdd x))` for a
field scalar `x ∈ 𝔽_{p^q}`; conjugating by `σ(inr a)` (`a ∈ U`) scales by `↑a⁻¹`. -/

section Step4

/-- BG Appendix C prime-field-line scalar `s^x`: the additive-line element
`σ(inl(ofAdd x))` for a field scalar `x ∈ 𝔽_{p^q}`.  The distinguished generator is
`s = s^1`, and `s^x · s^y = s^{x+y}`. -/
noncomputable def sScalar (data : FieldNormalizerData p q G)
    (x : GaloisField p q) : G :=
  data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul (data : FieldNormalizerData p q G)
    (x y : GaloisField p q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      NormSet.additiveFieldGroup p q →*
        NormSet.normOneFrobeniusGroup p q),
    ← ofAdd_add]

/-- The trivial scalar `s^0 = 1`. -/
theorem sScalar_zero (data : FieldNormalizerData p q G) :
    data.sScalar 0 = 1 := by
  rw [sScalar, ofAdd_zero, map_one, map_one]

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one (data : FieldNormalizerData p q G) :
    data.s = data.sScalar 1 := by
  rw [sScalar, FieldNormalizerData.s, primeLineGenerator]

/-- The field value `↑a ∈ 𝔽_{p^q}` of a norm-one unit `a ∈ U`. -/
def unitVal (a : NormSet.normOneUnits p q) :
    GaloisField p q :=
  ((a : (GaloisField p q)ˣ) : GaloisField p q)

/-- The field value of an inverse unit is the inverse field value. -/
theorem unitVal_inv (a : NormSet.normOneUnits p q) :
    unitVal a⁻¹ = (unitVal a)⁻¹ := by
  simp [unitVal]

/-- The field value of a norm-one unit is nonzero. -/
theorem unitVal_ne_zero (a : NormSet.normOneUnits p q) :
    unitVal a ≠ 0 := by
  simp [unitVal]

/-- Conjugating the prime-line scalar `s^x` by `σ(inr a)` scales the exponent by
`↑a⁻¹`: `σ(inr a)⁻¹ · s^x · σ(inr a) = s^{(↑a⁻¹)·x}`.  This is BG's `s^a` notation. -/
theorem sScalar_conj (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) (x : GaloisField p q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.sScalar x *
        data.sigma (SemidirectProduct.inr a) =
      data.sScalar (unitVal a⁻¹ * x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := NormSet.normOneFrobenius_conj_inl
    (p := p) (q := q) a⁻¹ x
  rw [inv_inv] at h
  exact h

/-- Inversion of a prime-line scalar negates the exponent: `(s^x)⁻¹ = s^{-x}`. -/
theorem sScalar_inv (data : FieldNormalizerData p q G)
    (x : GaloisField p q) :
    (data.sScalar x)⁻¹ = data.sScalar (-x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_inv, ← ofAdd_neg]

/-- `s⁻¹ = s^{-1}` as a prime-line scalar. -/
theorem s_inv_eq_sScalar_neg_one (data : FieldNormalizerData p q G) :
    data.s⁻¹ = data.sScalar (-1) := by
  rw [s_eq_sScalar_one, sScalar_inv]

/-- `s² = s^2` as a prime-line scalar. -/
theorem s_sq_eq_sScalar_two (data : FieldNormalizerData p q G) :
    data.s ^ 2 = data.sScalar 2 := by
  rw [s_eq_sScalar_one, pow_two, sScalar_mul]
  congr 1
  norm_num

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar (data : FieldNormalizerData p q G) (c : ZMod p) :
    data.sigma (primeLineElement p q c) =
      data.sScalar
        (algebraMap (ZMod p) (GaloisField p q) c) := by
  rw [sScalar, primeLineElement]

/-- The central prime-line scalar `s^{-1}` equals `σ(P₀ (-1))`, the middle factor
of the target normal form. -/
theorem sScalar_neg_one_eq_sigma_primeLineElement (data : FieldNormalizerData p q G) :
    data.sScalar (-1) =
      data.sigma (primeLineElement p q (-1 : ZMod p)) := by
  rw [sigma_primeLineElement_eq_sScalar]
  congr 1
  push_cast
  ring

/-- **BG Appendix C, Lemma C.3 Step 4 base relation** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`, BG's identity `s^a · s^b = s²`, where the BG
conjugate `s^a = σ(inr a)⁻¹ · s · σ(inr a) = s^{↑a⁻¹}`. -/
theorem sBGConj_mul_sBGConj (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
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
theorem relationC2 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q)
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
theorem exists_companion_of_unitVal_inv_mem_normSetE (data : FieldNormalizerData p q G)
    {a : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q) :
    ∃ b : NormSet.normOneUnits p q,
      unitVal a⁻¹ + unitVal b⁻¹ = 2 ∧
        unitVal b⁻¹ ∈ NormSet.normSetE p q := by
  have hq : 0 < q := data.q_prime.pos
  have ha2 : (2 - unitVal a⁻¹) ∈
      NormSet.normSetE p q :=
    NormSet.two_sub_mem_normSetE p q ha
  have hval : unitVal
      ((NormSet.normOneUnitOfMemNormSetE
        p q hq ha2)⁻¹)⁻¹ = 2 - unitVal a⁻¹ := by
    rw [inv_inv]
    simp only [unitVal]
    exact NormSet.normOneUnitOfMemNormSetE_coe
      p q hq ha2
  refine ⟨(NormSet.normOneUnitOfMemNormSetE
      p q hq ha2)⁻¹, ?_, ?_⟩
  · rw [hval]; ring
  · rw [hval]; exact ha2

/-- **BG Appendix C, Lemma C.3 Step 4 E-membership extraction** (mmd L5090–5094):
if the `k = 3` normal form of `s · σ(inr W) · s⁻²` has central prime-line factor
`s⁻¹`, then the inverse field value `(↑W)⁻¹` lies in the norm set `E`.  This is BG's
final paragraph `v₁ = 2 - W ⟹ N(2 - W) = N(v₁) = 1 ⟹ W ∈ E`, read in the repo's
(inverse) convention so that it is `(↑W)⁻¹` that enters `E`. -/
theorem unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (W u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s * data.sigma (SemidirectProduct.inr W) * data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁)) :
    (unitVal W)⁻¹ ∈ NormSet.normSetE p q := by
  have hN :
      NormSet.normN p q
        ((2 : GaloisField p q) * unitVal W - 1) = 1 :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition W u₁ v₁ hdec
  have hWnorm :
      NormSet.normN p q (unitVal W) = 1 :=
    (NormSet.mem_normOneUnits_iff_normN p q
      data.q_prime.ne_zero (W : (GaloisField p q)ˣ)).mp W.property
  have hW0 : unitVal W ≠ 0 := unitVal_ne_zero W
  refine ⟨?_, ?_⟩
  · rw [NormSet.normN_inv, hWnorm, inv_one]
  · have hcalc :
        (2 : GaloisField p q) - (unitVal W)⁻¹ =
          (unitVal W)⁻¹ * ((2 : GaloisField p q) * unitVal W - 1) := by
      field_simp
    rw [hcalc, NormSet.normN_mul,
      NormSet.normN_inv, hWnorm, inv_one, one_mul, hN]

/-- **Backward conjugation rewrite**: `(t^n)⁻¹ · σ(inr u) · t^n = σ(inr ((tConj^n)⁻¹ u))`.
This is the inverse-direction companion of
`t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16), giving BG's
right-conjugation `(u)^{t^n} = t⁻ⁿ u tⁿ` directly.  It lets the BG (C.4) connector
`q`-swap telescoping be carried out on the backward `tConj⁻³` form of `M₁`. -/
theorem t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    (data : FieldNormalizerData p q G)
    (n : ℕ) (u : NormSet.normOneUnits p q) :
    (data.t ^ n)⁻¹ *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.t ^ n =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) :
          NormSet.normOneFrobeniusGroup p q) := by
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
    (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u₁ v₁ : NormSet.normOneUnits p q,
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := by
  apply data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
  have hs : data.s ∈ data.P ⊔ data.U := by
    rw [← zpow_one data.s]; exact data.s_zpow_mem_P_sup_U 1
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            NormSet.normOneFrobeniusGroup p q) ∈ data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹),
      ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            NormSet.normOneFrobeniusGroup p q) ∈ data.P ⊔ data.U :=
    (le_sup_right : data.U ≤ data.P ⊔ data.U) hmidU
  have hr : data.s ^ (-2 : ℤ) ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U (-2)
  exact (data.P ⊔ data.U).mul_mem
    ((data.P ⊔ data.U).mul_mem hs hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge in a neutral form:
any word `s^m · σ(inr w) · s^r`, with the middle term already a concrete
norm-one complement element, lies in `PU`. -/
theorem s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w : NormSet.normOneUnits p q) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r ∈ data.P ⊔ data.U := by
  have hm : data.s ^ m ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr w, ⟨w, rfl⟩, rfl⟩
  have hmid :
      data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) ∈
        data.P ⊔ data.U :=
    (le_sup_right : data.U ≤ data.P ⊔ data.U) hmidU
  have hr : data.s ^ r ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U r
  exact (data.P ⊔ data.U).mul_mem
    ((data.P ⊔ data.U).mul_mem hm hmid) hr

/-- Neutral Step 4 `(C.5)` decomposition bridge: every word
`s^m · σ(inr w) · s^r` admits Step 1 normal form
`σ(inr u) · σ(P₀ c) · σ(inr v)`. -/
theorem exists_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      data.s ^ m *
            data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U m r w)

/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge in a neutral form: if a
word `s^m · σ(inr w) · s^r` is written in Step 1 normal form `u₁ s₁ v₁`, then the
right component is `w = u₁ v₁`.  This is the reusable right-projection step behind
both the forward and backward `k = 3` `(C.5)` equations. -/
theorem right_component_of_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w u₁ v₁ : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    w = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ data.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ data.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (primeLineElement p q c) = 1 := by
    simp [primeLineElement]
  have hσ :
      data.sigma (pm * (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma (pm * (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) * pr) =
          data.s ^ m *
              data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q c) *
              data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      NormSet.normOneFrobeniusGroup p q →* NormSet.normOneUnits p q) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C `(C.8)` normal-form transport in neutral form: applying the
concrete `p`-power Frobenius to a `(C.5)` equation keeps the prime-line factor
fixed and raises the three complement terms to their `p`-th powers. -/
theorem frobenius_step4_sigma_inr_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (w u v : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q)) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr (u ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr (v ^ p) :
            NormSet.normOneFrobeniusGroup p q) := by
  let g := primeLineGenerator p q
  let W : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr w
  let U : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr u
  let V : NormSet.normOneFrobeniusGroup p q := SemidirectProduct.inr v
  let S : NormSet.normOneFrobeniusGroup p q := primeLineElement p q c
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
  have hpowH := congrArg (frobeniusHom p q) hH
  have hpowH' :
      g ^ m * (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
          g ^ r =
        (SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
          primeLineElement p q c *
            (SemidirectProduct.inr (v ^ p) : NormSet.normOneFrobeniusGroup p q) := by
    simpa [W, U, V, S, g, map_mul, map_pow,
      frobeniusHom_primeLineGenerator,
      frobeniusHom_inr,
      frobeniusHom_primeLineElement] using hpowH
  have hleft_pow_sigma :
      data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
              g ^ r) =
        data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
            data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_pow_sigma :
      data.sigma
          ((SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c *
              (SemidirectProduct.inr (v ^ p) : NormSet.normOneFrobeniusGroup p q)) =
        data.sigma (SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr (v ^ p) :
              NormSet.normOneFrobeniusGroup p q) := by
    rw [map_mul, map_mul]
  calc
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ p) :
            NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
        data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ p) : NormSet.normOneFrobeniusGroup p q) *
              g ^ r) := hleft_pow_sigma.symm
    _ = data.sigma
          ((SemidirectProduct.inr (u ^ p) : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c *
              (SemidirectProduct.inr (v ^ p) :
                NormSet.normOneFrobeniusGroup p q)) := by
      rw [hpowH']
    _ = data.sigma (SemidirectProduct.inr (u ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr (v ^ p) :
            NormSet.normOneFrobeniusGroup p q) := hright_pow_sigma

/-- The `mod P` reading of the backward `k = 3` first `(C.5)` equation: BG's
middle term `(a⁻¹)^{t^3}` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_inv_decomposition
    (data : FieldNormalizerData p q G)
    (a u₁ v₁ : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 first `(C.5)` factor
`M₁ = s · (a⁻¹)^{t^3} · s⁻²`, in BG's backward conjugation convention. -/
noncomputable def step4M1 (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) : G :=
  data.s *
      ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
    (data.s⁻¹) ^ 2

/-- BG Appendix C, Lemma C.3 Step 4 second `(C.5)` factor
`M₂ = s³ · (ab⁻¹)^{t^2} · s⁻¹`. -/
noncomputable def step4M2 (data : FieldNormalizerData p q G)
    (a b : NormSet.normOneUnits p q) : G :=
  data.s ^ 3 *
      ((data.t⁻¹) ^ 2 *
        (data.sigma (SemidirectProduct.inr a) *
          (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
    data.s⁻¹

/-- BG Appendix C, Lemma C.3 Step 4 third `(C.5)` factor
`M₃ = s² · b^t · s⁻³`. -/
noncomputable def step4M3 (data : FieldNormalizerData p q G)
    (b : NormSet.normOneUnits p q) : G :=
  data.s ^ 2 *
      (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
    (data.s⁻¹) ^ 3

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
