/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_NormalForms

/-!
# BG Appendix C, Lemma C.3 Step 4: relations (C.9), (C.10) and the capstone

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152), Steps 3 and 4.

Relations (C.9) and (C.10), and the Step 4 capstone.  Pushing the (C.7) relation through the
`U`-side bookkeeping gives (C.9): either the third normal-form factor `w₃` is trivial -- in
which case the surviving word `w₁ w₂^{p−1} = 1` forces `w = 1` and yields the displayed
relation (C.10) -- or the Step 3 intersection is all of `PU`.  The latter branch is
contradictory: it would make `t²` normalize `PU`, hence `P` (as `P` is characteristic in `PU`),
hence `W₂`, forcing `P₁ = W₂`, which contradicts `P₁ ≠ W₂`.

`Step4Capstone` is the resulting statement `s₁ = s⁻¹`, and from it the Step 4 twisted-inverse
output on the norm-one group -- and hence the generator relation `N(2a − 1) = 1` -- follows.

Migrated from `OddOrder.Peterfalvi.S16_CoreSetup` (issue 0151).
-/

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory
open scoped Pointwise
open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

section Step4

/-- `local instance` は file 境界を越えないため prefix-split 後に再宣言 (原本 = S16_AppendixC3)。 -/
local instance factPPrimeStep4Split : Fact p.Prime :=
  ⟨(Fact.out : Nat.Prime p)⟩
/-- BG Appendix C `(C.9)` for the third word: comparing `(C.7)` for `(a,b)`
with `(C.7)` for `(a^p,b^p)` shows that
`S₁ W₃^(p-1) S₁⁻¹` lies in `PU` and its `t²`-conjugate also lies in `PU`. -/
theorem relationC9_w3_mem_P_sup_U_and_conj
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (primeLineElement p q forms.c1)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
        NormSet.normOneFrobeniusGroup p q)
    S1 * W3pow * S1⁻¹ ∈ data.P ⊔ data.U ∧
      data.t ^ 2 * (S1 * W3pow * S1⁻¹) * (data.t ^ 2)⁻¹ ∈
        data.P ⊔ data.U := by
  classical
  dsimp only
  let PU : Subgroup G := data.P ⊔ data.U
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair data.q_prime.ne_zero ha hb hab
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
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_eq : p = p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ p * W3⁻¹ = W3 ^ (p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (p - 1) := hW3_pow_mul_inv
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
    change A ∈ data.P ⊔ data.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q forms.c3 * SemidirectProduct.inr forms.w2,
      trivial, ?_⟩
    simp [A, W1, W2, S3, map_mul]
  have hAp_mem : Ap ∈ PU := by
    change Ap ∈ data.P ⊔ data.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr (forms.w1 ^ p) :
          NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q forms.c3 *
          SemidirectProduct.inr (forms.w2 ^ p), trivial, ?_⟩
    simp [Ap, W1p, W2p, S3, map_mul]
  have hX_mem : X ∈ PU := by
    change X ∈ data.P ⊔ data.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨primeLineElement p q forms.c1 *
        (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
          NormSet.normOneFrobeniusGroup p q) *
          (primeLineElement p q forms.c1)⁻¹, trivial, ?_⟩
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
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (primeLineElement p q forms.c1)
    let S3 := data.sigma (primeLineElement p q forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
        NormSet.normOneFrobeniusGroup p q)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by
  classical
  dsimp only
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : NormSet.normOneFrobeniusGroup p q)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair data.q_prime.ne_zero ha hb hab
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
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_eq : p = p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ p * W3⁻¹ = W3 ^ (p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (p - 1) := hW3_pow_mul_inv
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
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc3 : forms.c3 ≠ 0) (hw3 : forms.w3 = 1) :
    forms.w1 ^ (p - 1) = 1 ∧ forms.w2 ^ (p - 1) = 1 := by
  classical
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S3 := data.sigma (primeLineElement p q forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : NormSet.normOneFrobeniusGroup p q)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : NormSet.normOneFrobeniusGroup p q)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ p) : NormSet.normOneFrobeniusGroup p q)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let U1 := (forms.w1 ^ p)⁻¹ * forms.w1
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
  have hU1_sigma : data.sigma (SemidirectProduct.inr U1 : NormSet.normOneFrobeniusGroup p q) =
      W1p⁻¹ * W1 := by
    simp [U1, W1p, W1, map_mul, map_inv]
  have hS3_inv : data.sigma (primeLineElement p q (-forms.c3)) = S3⁻¹ := by
    calc
      data.sigma (primeLineElement p q (-forms.c3)) =
          data.sigma ((primeLineElement p q forms.c3)⁻¹) := by
        rw [primeLineElement_neg]
      _ = S3⁻¹ := by
        simp [S3]
  have hW2p_mem : W2p ∈ data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr (forms.w2 ^ p),
      ⟨forms.w2 ^ p, rfl⟩, rfl⟩
  have hW2_mem : W2 ∈ data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  have hW2_ratio_mem : W2p * W2⁻¹ ∈ data.U :=
    data.U.mul_mem hW2p_mem (data.U.inv_mem hW2_mem)
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
  have hmid_mem : S3⁻¹ * W1p⁻¹ * W1 * S3 ∈ data.U := by
    rw [hmid_eq]
    exact hW2_ratio_mem
  have hmem_step : data.sigma (primeLineElement p q (-forms.c3)) *
        data.sigma (SemidirectProduct.inr U1 : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q forms.c3) ∈ data.U := by
    simpa [hS3_inv, hU1_sigma, S3, mul_assoc] using hmid_mem
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -forms.c3) (d := forms.c3) U1 hmem_step
  have hU1_one : U1 = 1 := by
    rcases hstep with hzero | hone
    · have hc3_zero : forms.c3 = 0 := by
        simpa using (neg_eq_zero.mp hzero.1)
      exact False.elim (hc3 hc3_zero)
    · exact hone.1
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hU1_one' : (forms.w1 ^ p)⁻¹ * forms.w1 = 1 := by
    simpa [U1] using hU1_one
  have hw1p_eq : forms.w1 ^ p = forms.w1 := by
    calc
      forms.w1 ^ p = forms.w1 ^ p * 1 := by simp
      _ = forms.w1 ^ p * ((forms.w1 ^ p)⁻¹ * forms.w1) := by
        rw [hU1_one']
      _ = forms.w1 := by
        group
  have hw1 : forms.w1 ^ (p - 1) = 1 := by
    have hpow : forms.w1 ^ (p - 1) * forms.w1 = forms.w1 ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w1 ^ (p - 1) =
          (forms.w1 ^ (p - 1) * forms.w1) * forms.w1⁻¹ := by
        group
      _ = forms.w1 ^ p * forms.w1⁻¹ := by
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
  have hw2p_eq : forms.w2 ^ p = forms.w2 := by
    have hinr : (SemidirectProduct.inr (forms.w2 ^ p) :
          NormSet.normOneFrobeniusGroup p q) = SemidirectProduct.inr forms.w2 :=
      data.sigma_injective (by simpa [W2p, W2] using hW2p_eq)
    exact (SemidirectProduct.inr_inj.mp hinr)
  have hw2 : forms.w2 ^ (p - 1) = 1 := by
    have hpow : forms.w2 ^ (p - 1) * forms.w2 = forms.w2 ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w2 ^ (p - 1) =
          (forms.w2 ^ (p - 1) * forms.w2) * forms.w2⁻¹ := by
        group
      _ = forms.w2 ^ p * forms.w2⁻¹ := by
        rw [hpow]
      _ = forms.w2 * forms.w2⁻¹ := by
        rw [hw2p_eq]
      _ = 1 := by
        group
  exact ⟨hw1, hw2⟩


/-- BG Appendix C condition `(A)` in S16 form: a norm-one unit with
`(p - 1)`-st power equal to `1` is trivial. -/
theorem normOneUnit_eq_one_of_pow_sub_one_eq_one
    (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) (hu : u ^ (p - 1) = 1) :
    u = 1 :=
  NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
    p q data.q_prime data.cyclotomic_coprime u hu

namespace Step4C5NormalForms

/-- The post-`(C.9)` condition `(A)` step for the three BG words. -/
theorem w_eq_one_of_pow_sub_one_eq_one
    {data : FieldNormalizerData p q G}
    {a b : NormSet.normOneUnits p q} (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 ^ (p - 1) = 1)
    (hw2 : forms.w2 ^ (p - 1) = 1)
    (hw3 : forms.w3 ^ (p - 1) = 1) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 :=
  ⟨data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w1 hw1,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w2 hw2,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3⟩

end Step4C5NormalForms


/-- BG Appendix C `(C.10)`: once `(C.9)` and condition `(A)` have forced
`w₁ = w₂ = w₃ = 1`, relation `(C.7)` collapses to
`t² s₁ t⁻¹ s₂ t⁻¹ s₃ = 1`. -/
theorem relationC10_of_w_eq_one
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 = 1) (hw2 : forms.w2 = 1) (hw3 : forms.w3 = 1) :
    data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let S2 := data.sigma (primeLineElement p q forms.c2)
  let S3 := data.sigma (primeLineElement p q forms.c3)
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
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hw3U :
      data.sigma (primeLineElement p q forms.c1) *
          data.sigma
            (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
              NormSet.normOneFrobeniusGroup p q) *
            (data.sigma (primeLineElement p q forms.c1))⁻¹ ∈ data.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  classical
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
  let U3 := forms.w3 ^ (p - 1)
  have hS1_inv :
      data.sigma (primeLineElement p q (-forms.c1)) = S1⁻¹ := by
    calc
      data.sigma (primeLineElement p q (-forms.c1)) =
          data.sigma ((primeLineElement p q forms.c1)⁻¹) := by
        rw [primeLineElement_neg]
      _ = S1⁻¹ := by
        simp [S1]
  have hU3_sigma :
      data.sigma (SemidirectProduct.inr U3 : NormSet.normOneFrobeniusGroup p q) =
        W3pow := by
    simp [U3, W3pow]
  have hmem_step :
      data.sigma (primeLineElement p q forms.c1) *
          data.sigma (SemidirectProduct.inr U3 : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q (-forms.c1)) ∈ data.U := by
    simpa [S1, W3pow, U3, hS1_inv, hU3_sigma, mul_assoc] using hw3U
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := forms.c1) (d := -forms.c1) U3 hmem_step
  have hU3_one : U3 = 1 := by
    rcases hstep with hzero | hone
    · exact False.elim (hc1 hzero.1)
    · exact hone.1
  have hw3_pow : forms.w3 ^ (p - 1) = 1 := by
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
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hstep3 :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) = data.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  let S1 := data.sigma (primeLineElement p q forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (p - 1)) :
      NormSet.normOneFrobeniusGroup p q)
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
  have hX_U : X ∈ data.U := by
    have hX_inf' : X ∈ (data.P ⊔ data.U) ⊓
        (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) := by
      simpa [PU] using hX_inf
    rwa [hstep3] at hX_inf'
  exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    ha hb hab forms hc1 hc3 (by simpa [X, S1, W3pow] using hX_U)

/-- BG Appendix C Step 4 after applying Step 3 to the `(C.9)` element: either
`(C.10)` has already been forced, or the only remaining Step 3 obstruction is
the bad branch where the relevant intersection is all of `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    (forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1) ∨
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U := by
  classical
  have ht2_norm : data.t ^ 2 ∈ Subgroup.normalizer (data.U : Set G) :=
    data.t_pow_normalizes_U 2
  have ht2_inv_norm : (data.t ^ 2)⁻¹ ∈ Subgroup.normalizer (data.U : Set G) :=
    (Subgroup.normalizer (data.U : Set G)).inv_mem ht2_norm
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
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    ∀ ⦃x : G⦄, x ∈ data.P ⊔ data.U →
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ ∈ data.P ⊔ data.U := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
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
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.t ^ 2 ∈ Subgroup.normalizer ((data.P ⊔ data.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := data.P ⊔ data.U
  let g : G := data.t ^ 2
  have hinc : ∀ ⦃x : G⦄, x ∈ PU → g * x * g⁻¹ ∈ PU := by
    intro x hx
    simpa [g, PU] using data.step3_badBranch_t_sq_conj_mem_P_sup_U hbad hx
  have hgpow : g ^ p = 1 := by
    calc
      g ^ p = (data.t ^ 2) ^ p := by rfl
      _ = data.t ^ (2 * p) := by rw [pow_mul]
      _ = data.t ^ (p * 2) := by rw [Nat.mul_comm]
      _ = (data.t ^ p) ^ 2 := by rw [pow_mul]
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
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have g_inv_eq : g⁻¹ = g ^ (p - 1) := by
    have hmul : g ^ (p - 1) * g = 1 := by
      calc
        g ^ (p - 1) * g = g ^ ((p - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ p := by
          rw [Nat.sub_one_add_one_eq_of_pos hp_pos]
        _ = 1 := hgpow
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    have h := hiter (p - 1) hx
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
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.t ^ 2 ∈ Subgroup.normalizer (data.P : Set G) :=
  data.normalizer_P_sup_U_le_normalizer_P
    (data.step3_badBranch_t_sq_normalizes_P_sup_U hbad)

/-- BG Appendix C Step 3 bad branch after cyclic generation: since `P₁=⟨t⟩` and
`p` is odd, the normalization of `P` by `t²` forces all of `P₁` to normalize
`P`. -/
theorem step3_badBranch_P1_le_normalizer_P
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.P1 ≤ Subgroup.normalizer (data.P : Set G) :=
  data.P1_le_normalizer_P_of_t_sq_mem
    (data.step3_badBranch_t_sq_normalizes_P hbad)

/-- BG Appendix C Step 3 bad branch after `P ∩ W₂Q = W₂`: the forced
normalization of `P` by `P₁`, together with `P₁ ≤ W₂Q`, forces `P₁` to normalize
`W₂ = P ∩ W₂Q`. -/
theorem step3_badBranch_P1_le_normalizer_W2
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
    data.P1 ≤ Subgroup.normalizer (data.W2 : Set G) :=
  data.P1_le_normalizer_W2_of_le_normalizer_P
    (data.step3_badBranch_P1_le_normalizer_P hbad)

/-- BG Appendix C Step 3 bad branch is impossible: it forces `P₁ = W₂`, while
`P₁` normalizes `U` and `W₂` does not. -/
theorem step3_badBranch_false
    (data : FieldNormalizerData p q G)
    (hbad :
      (data.P ⊔ data.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (data.P ⊔ data.U)) =
        data.P ⊔ data.U) :
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
theorem relationC9_w_eq_one_and_relationC10_of_c6
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 := by
  rcases data.relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
      ha hb hab forms hc1 hc3 with hC10 | hbad
  · exact hC10
  · exact False.elim (data.step3_badBranch_false hbad)

/-- BG Appendix C Step 4 branch-free `(C.10)` producer: exact `(C.9)`, Step 3,
the bad-branch contradiction, and the `(C.6)` nonzero facts for `c₁` and `c₃`
together force `w₁=w₂=w₃=1` and the displayed `(C.10)` relation. -/
theorem relationC9_w_eq_one_and_relationC10
    (data : FieldNormalizerData p q G)
    {a b : NormSet.normOneUnits p q}
    (ha : unitVal a⁻¹ ∈ NormSet.normSetE p q)
    (hb : unitVal b⁻¹ ∈ NormSet.normSetE p q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (primeLineElement p q forms.c1) *
        data.t⁻¹ * data.sigma (primeLineElement p q forms.c2) *
          data.t⁻¹ * data.sigma (primeLineElement p q forms.c3) = 1 :=
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
def Step4Capstone (data : FieldNormalizerData p q G) : Prop :=
  ∀ a : NormSet.normOneUnits p q,
    unitVal a⁻¹ ∈ NormSet.normSetE p q →
      ∃ u₁ v₁ : NormSet.normOneUnits p q,
        data.s *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁) *
          data.sigma (primeLineElement p q (-1 : ZMod p)) *
            data.sigma (SemidirectProduct.inr v₁)

/-- The Step 4 capstone yields BG's one-step twisted-inverse output for the
backward conjugation automorphism `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`:
`a ∈ E ⟹ (a⁻¹)^{t³} ∈ E` (BG's right-conjugation).  We apply the capstone at
`a = u⁻¹` so that its hypothesis `↑(u⁻¹)⁻¹ = ↑u ∈ E` is exactly the input, and the
E-extraction `(↑W)⁻¹ ∈ E` (with `W = (tConj⁻³)(u)`) reads as `↑((tConj⁻³)(u⁻¹)) ∈ E`. -/
theorem normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone
    (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    NormSet.normSetETwistedNormOneStep
      (p := p) (q := q) (data.tConjNormOneUnitsAut ^ 3)⁻¹ := by
  intro u hu
  have hcond : unitVal (u⁻¹)⁻¹ ∈
      NormSet.normSetE p q := by
    rw [inv_inv]; exact hu
  obtain ⟨u₁, v₁, hdec⟩ := hcap u⁻¹ hcond
  have hext := data.unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ (u⁻¹)⁻¹) u₁ v₁ hdec
  rw [inv_inv, ← unitVal_inv, ← map_inv] at hext
  rw [NormSet.twistedInv]
  exact hext

/-- The Step 4 capstone supplies the AppC norm-one twisted-inverse output. -/
theorem normSetTwistedNormOneStep_of_capstone (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    normSetTwistedNormOneStep p q := by
  refine ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹, ?_,
    data.normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone hcap⟩
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, data.tConjNormOneUnitsAut_pow_p_eq_one,
    one_pow, inv_one]

/-- The Step 4 capstone supplies the AppC generator relation `∀ a ∈ E, N(2a-1)=1`,
without any carrier field.  This is what `normSetGeneratorRelation` (proved
once `step4Capstone` is available) calls. -/
theorem normSetGeneratorRelation_of_capstone (data : FieldNormalizerData p q G)
    (hcap : data.Step4Capstone) :
    normSetGeneratorRelation p q :=
  normSetGeneratorRelation_of_twisted_normOne_step p q
    data.q_prime.pos data.p_odd (data.normSetTwistedNormOneStep_of_capstone hcap)

end Step4

end FieldNormalizerData

end OddOrder.BG.AppC
