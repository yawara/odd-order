/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_CoreSetup

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
local instance factPPrimeStep4'' {hyp : Hypothesis (G := G)} : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

/-! #### BG Appendix C, Lemma C.3 Step 4: the kernel/fixed-point-free argument

This proves the capstone `s₁ = s⁻¹` from the displayed relation `(C.10)`.  Setting
`t = y⁻¹ s y` with `y ∈ ⁅Q, W₂⁆` (Remark (XI)), BG rewrites `(C.10)` modulo the
abelian group `⁅Q, P₀⁆` (= `⁅Q, W₂⁆`) as `y` lying in the kernel of
`(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)(s⁻¹ - 1)`.  Because `s⁻¹` operates fixed-point-freely on
`⁅Q, P₀⁆` (Remark (X)), the factor `(s⁻¹ - 1)` is injective, so `y` lies in the
kernel of `(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)`; unwinding gives `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃`
(`tᵢ = y⁻¹ sᵢ y`).  Steps 2–3 then force `t₁ = t⁻¹`, i.e. `s₁ = s⁻¹`.

We avoid building the endomorphism ring `End ⁅Q, P₀⁆`: BG's "`y ∈ ker(BC)`, `C`
injective ⟹ `y ∈ ker B`" is realised concretely as "`β(Y_B)·Y_B⁻¹ = ⋆` and `⋆ = 1`
⟹ `β(Y_B) = Y_B` ⟹ (fixed-point-free) `Y_B = 1`", where `β` is conjugation by `s`
on the abelian `⁅Q, W₂⁆` and `Y_B` the four-fold `y`-conjugate of BG's `(5074)`. -/

/-- The transported prime-line element `σ(P₀ c)` lies in `W₂`. -/
theorem sigma_primeLineElement_mem_W2 {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c) ∈ hyp.base.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact Subgroup.mem_map_of_mem _ (fieldNormalizerPrimeLineElement_mem hyp c)

/-- Any two transported prime-line elements commute (the prime line `P₀` is
abelian). -/
theorem sigma_primeLineElement_commute {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c d : ZMod hyp.base.p) :
    Commute (data.sigma (fieldNormalizerPrimeLineElement hyp c))
      (data.sigma (fieldNormalizerPrimeLineElement hyp d)) := by
  rw [Commute, SemiconjBy, sigma_primeLineElement_eq_sScalar,
    sigma_primeLineElement_eq_sScalar, sScalar_mul, sScalar_mul, add_comm]

/-- The distinguished generator `s` commutes with every transported prime-line
element. -/
theorem s_commute_sigma_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    Commute data.s (data.sigma (fieldNormalizerPrimeLineElement hyp c)) := by
  have h := data.sigma_primeLineElement_commute 1 c
  rwa [show data.sigma (fieldNormalizerPrimeLineElement hyp 1) = data.s by
    rw [fieldNormalizerPrimeLineElement_one, s, fieldNormalizerPrimeLineGenerator]] at h

/-- **BG Appendix C, Lemma C.3 Step 4: `(C.10)` modulo `Q`** (mmd L5058).  Since
`P₀ ∩ Q = 1` (`W2_inf_Q_eq_bot`) and `t ≡ s` modulo `Q`, the displayed relation
`(C.10)` collapses to `s₁ s₂ s₃ = 1`.  We conjugate `(C.10)` by `y⁻¹` (so each `t`
becomes `s`), telescope the resulting `Q`-cosets to the left, and use that
`P₀`-conjugation normalizes `Q`. -/
theorem step4_sigma_primeLine_prod_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c2 c3 : ZMod hyp.base.p}
    (hC10 : data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1 := by
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s2 := data.sigma (fieldNormalizerPrimeLineElement hyp c2) with hs2def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  -- The three prime-line factors lie in `W₂`.
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs2W : s2 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c2
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  have hprodW : s1 * s2 * s3 ∈ hyp.base.W2 := mul_mem (mul_mem hs1W hs2W) hs3W
  -- `y⁻¹`-conjugates `σᵢ = y⁻¹ sᵢ y`, congruent to `sᵢ` modulo `Q`.
  set σ1 := data.y⁻¹ * s1 * data.y with hσ1def
  set σ2 := data.y⁻¹ * s2 * data.y with hσ2def
  set σ3 := data.y⁻¹ * s3 * data.y with hσ3def
  -- conjugating `(C.10)` by `y⁻¹` turns each `t` into `s` (since `t = y s y⁻¹`).
  have hyt2 : data.y⁻¹ * data.t ^ 2 * data.y = data.s ^ 2 := by
    rw [t, MulAut.conj_apply, pow_two, pow_two]; group
  have hyti : data.y⁻¹ * data.t⁻¹ * data.y = data.s⁻¹ := by
    rw [t, MulAut.conj_apply]; group
  have hconj : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 = 1 := by
    rw [← hyt2, ← hyti, hσ1def, hσ2def, hσ3def,
      show data.y⁻¹ * data.t ^ 2 * data.y * (data.y⁻¹ * s1 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s2 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s3 * data.y) =
          data.y⁻¹ * (data.t ^ 2 * s1 * data.t⁻¹ * s2 * data.t⁻¹ * s3) * data.y from by group,
      hC10, mul_one, inv_mul_cancel]
  -- each `σᵢ sᵢ⁻¹` lies in `Q`.
  have hQconj : ∀ g ∈ hyp.base.W2, ∀ x ∈ hyp.base.Q, g * x * g⁻¹ ∈ hyp.base.Q :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (data.W2_normalizes_Q hg) x).mp hx
  set q1 := σ1 * s1⁻¹ with hq1def
  set q2 := σ2 * s2⁻¹ with hq2def
  set q3 := σ3 * s3⁻¹ with hq3def
  have hq1Q : q1 ∈ hyp.base.Q := by
    rw [show q1 = data.y⁻¹ * (s1 * data.y * s1⁻¹) from by rw [hq1def, hσ1def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s1 hs1W data.y data.y_mem_Q)
  have hq2Q : q2 ∈ hyp.base.Q := by
    rw [show q2 = data.y⁻¹ * (s2 * data.y * s2⁻¹) from by rw [hq2def, hσ2def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s2 hs2W data.y data.y_mem_Q)
  have hq3Q : q3 ∈ hyp.base.Q := by
    rw [show q3 = data.y⁻¹ * (s3 * data.y * s3⁻¹) from by rw [hq3def, hσ3def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s3 hs3W data.y data.y_mem_Q)
  -- `s`-power and `sᵢ` normalize `Q`.
  have hsN : data.s ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.s_normalizes_Q
  have hs1N : s1 ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.W2_normalizes_Q hs1W
  have hs2N : s2 ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.W2_normalizes_Q hs2W
  -- the telescoped `Q`-element.
  set Q1 := data.s ^ 2 * q1 * (data.s ^ 2)⁻¹ with hQ1def
  set Q2 := data.s ^ 2 * s1 * data.s⁻¹ * q2 * (data.s ^ 2 * s1 * data.s⁻¹)⁻¹ with hQ2def
  set Q3 := data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * q3 *
    (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹)⁻¹ with hQ3def
  have hQ1Q : Q1 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp (pow_mem hsN 2) q1).mp hq1Q
  have hQ2Q : Q2 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) q2).mp hq2Q
  have hQ3Q : Q3 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) hs2N)
        (inv_mem hsN)) q3).mp hq3Q
  -- free-group telescoping identity.
  have hfactor : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 =
      Q1 * Q2 * Q3 * (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3) := by
    rw [hQ1def, hQ2def, hQ3def,
      show σ1 = q1 * s1 by rw [hq1def]; group,
      show σ2 = q2 * s2 by rw [hq2def]; group,
      show σ3 = q3 * s3 by rw [hq3def]; group]
    group
  -- collapse the bare `s`-word to `s₁ s₂ s₃` using commutativity of `W₂`.
  have hcollapse : data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3 = s1 * s2 * s3 := by
    have h1 : Commute (data.s ^ 2) s1 := (data.s_commute_sigma_primeLineElement c1).pow_left 2
    have h2 : Commute data.s s2 := data.s_commute_sigma_primeLineElement c2
    rw [h1.eq]
    rw [show s1 * data.s ^ 2 * data.s⁻¹ = s1 * data.s by group,
      show s1 * data.s * s2 = s1 * (data.s * s2) by group, h2.eq,
      show s1 * (s2 * data.s) * data.s⁻¹ = s1 * s2 by group]
  rw [hcollapse] at hfactor
  -- conclude `s₁ s₂ s₃ ∈ Q`, hence `∈ W₂ ⊓ Q = ⊥`.
  have hprodQ : s1 * s2 * s3 ∈ hyp.base.Q := by
    have hQ0 : Q1 * Q2 * Q3 ∈ hyp.base.Q := mul_mem (mul_mem hQ1Q hQ2Q) hQ3Q
    have hone : Q1 * Q2 * Q3 * (s1 * s2 * s3) = 1 := by rw [← hfactor, hconj]
    have hmem : (Q1 * Q2 * Q3)⁻¹ ∈ hyp.base.Q := inv_mem hQ0
    rwa [inv_eq_of_mul_eq_one_right hone] at hmem
  have : s1 * s2 * s3 ∈ hyp.base.W2 ⊓ hyp.base.Q := ⟨hprodW, hprodQ⟩
  rw [data.W2_inf_Q_eq_bot] at this
  simpa using this

/-- A fixed point of an automorphism is fixed by every integer power of it. -/
theorem zpow_apply_fixed {M : Type*} [Group M] (f : MulAut M) {z : M} (hf : f z = z)
    (m : ℤ) : (f ^ m) z = z := by
  have hfinv : (f⁻¹) z = z := by
    have h1 : (f⁻¹ * f) z = z := by rw [inv_mul_cancel]; rfl
    rwa [MulAut.mul_apply, hf] at h1
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hf, ih]
  | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, hfinv, ih]

/-- **BG Appendix C, Remark (X), `s`-only form**: if `x ∈ ⁅Q, W₂⁆` is fixed by
conjugation by the single generator `s`, then `x = 1`.  Since `W₂ = ⟨s⟩`, being
`s`-fixed is being `W₂`-fixed, and `(X)` (`C_Q(W₂) ∩ ⁅Q,W₂⁆ = 1`) applies. -/
theorem w2ConjQAut_eq_one_of_mem_actionCommutator_of_s_fixed [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {x : ↥hyp.base.Q}
    (hx : x ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut)
    (hsfix : data.w2ConjQAut ⟨data.s, data.s_mem_W2⟩ x = x) :
    x = 1 := by
  apply data.w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed hx
  intro w
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨data.s, data.s_mem_W2⟩ : ↥hyp.base.W2) ^ n = w := by
    have hwz : (w : G) ∈ Subgroup.zpowers data.s := by
      rw [← data.W2_eq_zpowers_s]; exact w.2
    obtain ⟨n, hn⟩ := hwz
    exact ⟨n, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hn)⟩
  rw [← hn, map_zpow]
  exact zpow_apply_fixed _ hsfix n

/-- **BG Appendix C, Lemma C.3 Step 4 kernel identity** (mmd L5060–5076): from the
displayed relation `(C.10)`, BG's `y ∈ ⁅Q, W₂⁆` lies in the kernel of
`(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)(s⁻¹ - 1)`; the fixed-point-free action of `s` (Remark (X))
removes the factor `(s⁻¹ - 1)`, leaving `Y_B = 1`, i.e. `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃`
where `tᵢ = y⁻¹ sᵢ y`.  We produce this relation with the explicit conjugator `yc`. -/
theorem step4_relation_5076 [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c2 c3 : ZMod hyp.base.p}
    (hC10 : data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1) :
    ∃ yc : G, data.t = yc⁻¹ * data.s * yc ∧
      data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
          (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c1))⁻¹ * yc) * data.t⁻¹ =
        data.t⁻¹ * (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c3))⁻¹ * yc) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c3) := by
  classical
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s2 := data.sigma (fieldNormalizerPrimeLineElement hyp c2) with hs2def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  -- `s₁ s₂ s₃ = 1` (mod-Q collapse), hence `s₂ = s₁⁻¹ s₃⁻¹`.
  have hs123 : s1 * s2 * s3 = 1 := data.step4_sigma_primeLine_prod_eq_one hC10
  have h12 : s1 * s2 = s3⁻¹ := eq_inv_of_mul_eq_one_left hs123
  have hs2eq : s2 = s1⁻¹ * s3⁻¹ := by rw [← h12]; group
  -- Remark (XI): a conjugator `yc = yD⁻¹ ∈ ⁅Q, W₂⁆` with `t = yc⁻¹ s yc`.
  obtain ⟨yD, hyD_mem, hyD_conj⟩ := data.exists_yD_mem_actionCommutator_conj_s_eq_t
  set Yq : ↥hyp.base.Q := yD⁻¹ with hYqdef
  have hYq_mem : Yq ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut := inv_mem hyD_mem
  set yc : G := (Yq : G) with hycdef
  have hyc_eq : yc = (yD : G)⁻¹ := by rw [hycdef, hYqdef, InvMemClass.coe_inv]
  have hty : data.t = yc⁻¹ * data.s * yc := by
    rw [hyc_eq, inv_inv, ← hyD_conj, MulAut.conj_apply]
  refine ⟨yc, hty, ?_⟩
  -- `W₂` elements used as conjugators.
  set sW : ↥hyp.base.W2 := ⟨data.s, data.s_mem_W2⟩ with hsWdef
  set s1W : ↥hyp.base.W2 := ⟨s1, hs1W⟩ with hs1Wdef
  set s3W : ↥hyp.base.W2 := ⟨s3, hs3W⟩ with hs3Wdef
  have hsW_coe : (sW : G) = data.s := rfl
  have hs1W_coe : (s1W : G) = s1 := rfl
  have hs3W_coe : (s3W : G) = s3 := rfl
  -- BG's `Y_B` (the four-fold conjugate, `(5074)`), as an element of `⁅Q, W₂⁆`.
  set YB : ↥hyp.base.Q :=
    (data.w2ConjQAut s3W⁻¹ Yq)⁻¹ * data.w2ConjQAut sW Yq *
      (data.w2ConjQAut (sW * s1W) Yq)⁻¹ * Yq with hYBdef
  have hinv := OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator data.w2ConjQAut
  have hYB_mem : YB ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut := by
    rw [hYBdef]
    exact mul_mem (mul_mem (mul_mem (inv_mem (hinv.smul_mem _ hYq_mem))
      (hinv.smul_mem _ hYq_mem)) (inv_mem (hinv.smul_mem _ hYq_mem))) hYq_mem
  -- `(Y_B : G)` is BG's `s₃⁻¹ t₃ t s₁ t₁⁻¹ t⁻¹` (mmd `(5074)`).
  have hYB_coe : (YB : G) =
      (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
        (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc := by
    rw [hYBdef]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, data.w2ConjQAut_apply_coe,
      hsW_coe, hs1W_coe, hs3W_coe, hycdef]
    group
  -- BG's `(5060)` element `⋆`, the six-fold conjugate product.
  set starQ : ↥hyp.base.Q :=
    Yq⁻¹ * data.w2ConjQAut (sW * sW) Yq * (data.w2ConjQAut (sW * (sW * s1W)) Yq)⁻¹ *
      data.w2ConjQAut (sW * s1W) Yq * (data.w2ConjQAut (sW * s3W⁻¹) Yq)⁻¹ *
        data.w2ConjQAut s3W⁻¹ Yq with hstarQdef
  -- (B) `⋆ = (C.10)`-LHS `= 1` (the `(5060)` regrouping, using `s₂ = s₁⁻¹ s₃⁻¹`).
  have hstarQ_coe : (starQ : G) =
      data.t ^ 2 * s1 * data.t⁻¹ * s2 * data.t⁻¹ * s3 := by
    have hc1 : Commute data.s s1 := data.s_commute_sigma_primeLineElement c1
    have hc3 : Commute data.s s3 := data.s_commute_sigma_primeLineElement c3
    have ht2 : data.t ^ 2 = yc⁻¹ * (data.s * data.s) * yc := by rw [hty, pow_two]; group
    have hti : data.t⁻¹ = yc⁻¹ * data.s⁻¹ * yc := by rw [hty]; group
    -- BG's `(5060)` over-product (the six brackets, before regrouping).
    have hSC : (starQ : G) =
        (yc⁻¹ * (data.s * data.s) * yc) *
          (data.s⁻¹ * data.s⁻¹ * data.s * data.s * s1) *
          (yc⁻¹ * s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 * yc) *
          (s1⁻¹ * data.s⁻¹ * data.s * s3⁻¹) *
          (yc⁻¹ * s3 * data.s⁻¹ * s3⁻¹ * yc) * s3 := by
      rw [hstarQdef]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, data.w2ConjQAut_apply_coe,
        hsW_coe, hs1W_coe, hs3W_coe, hycdef]
      group
    -- the two `(C.10)` `t⁻¹`-brackets collapse using `[s, sᵢ] = 1`.
    have e3 : s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 = data.s⁻¹ := by
      rw [show s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 = s1⁻¹ * data.s⁻¹ * s1 from by group,
        mul_assoc, (hc1.inv_left).eq]; group
    have e5 : s3 * data.s⁻¹ * s3⁻¹ = data.s⁻¹ := by
      rw [(hc3.inv_left.eq).symm]; group
    rw [hSC, ht2, hti, hs2eq,
      show data.s⁻¹ * data.s⁻¹ * data.s * data.s * s1 = s1 from by group,
      show yc⁻¹ * s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 * yc =
          yc⁻¹ * (s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1) * yc from by group,
      e3,
      show s1⁻¹ * data.s⁻¹ * data.s * s3⁻¹ = s1⁻¹ * s3⁻¹ from by group,
      show yc⁻¹ * s3 * data.s⁻¹ * s3⁻¹ * yc = yc⁻¹ * (s3 * data.s⁻¹ * s3⁻¹) * yc from by group,
      e5]
  have hstarQ1 : starQ = 1 := by
    apply Subtype.ext
    rw [hstarQ_coe, hC10, OneMemClass.coe_one]
  -- (A) `(s • Y_B) · Y_B⁻¹ = ⋆` (abelian regrouping inside `⁅Q, W₂⁆`).
  have hA : data.w2ConjQAut sW YB * YB⁻¹ = starQ := by
    have hadd : (Additive.ofMul (data.w2ConjQAut sW YB * YB⁻¹) :
        Additive ↥hyp.base.Q) = Additive.ofMul starQ := by
      rw [hYBdef, hstarQdef]
      simp only [map_mul, map_inv, MulAut.mul_apply, mul_inv_rev, inv_inv, ofMul_mul,
        ofMul_inv]
      abel
    exact Additive.ofMul.injective hadd
  have hβfix : data.w2ConjQAut sW YB = YB :=
    mul_inv_eq_one.mp (by rw [hA]; exact hstarQ1)
  have hYB1 : YB = 1 :=
    data.w2ConjQAut_eq_one_of_mem_actionCommutator_of_s_fixed hYB_mem hβfix
  -- unwind `Y_B = 1` to `(5074)`, hence the `(5076)` relation.
  have hR1 : (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
      (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc = 1 := by
    rw [← hYB_coe, hYB1, OneMemClass.coe_one]
  have hW : s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
      (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc) = 1 := by
    rw [show s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
          (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc) =
        (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
          (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc from by group]
    exact hR1
  rw [hty, ← mul_inv_eq_one,
    show s1 * (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s * yc)⁻¹ *
        ((yc⁻¹ * data.s * yc)⁻¹ * (yc⁻¹ * s3⁻¹ * yc) * s3)⁻¹ =
      (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc))⁻¹ *
        (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
          (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc)) *
        (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc)) from by group,
    hW, mul_one, inv_mul_cancel]

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch inclusion for a general conjugator
`g`: if `(PU) ∩ (PU)^g = PU`, then conjugation by `g` preserves `PU`. -/
theorem conj_mem_P_sup_U_of_inf_conj_eq {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G}
    (hbad : (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.P ⊔ hyp.base.U) :
    ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U → g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U := by
  intro x hx
  have hx_inf : x ∈ (hyp.base.P ⊔ hyp.base.U) ⊓
      (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) := by rw [hbad]; exact hx
  have hx_smul : x ∈ MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U) := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj g⁻¹)⁻¹ • x) = g * x * g⁻¹ := by
    rw [show ((MulAut.conj g⁻¹)⁻¹ • x) = (MulAut.conj g⁻¹)⁻¹ x from rfl,
      MulAut.conj_inv_apply]; group
  rwa [hsmul] at hx_smul

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch normalization for a general
conjugator `g` of `p`-power order: a one-sided conjugation inclusion of `PU`
upgrades to `g ∈ N_G(PU)`. -/
theorem mem_normalizer_P_sup_U_of_conj_of_pow {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G}
    (hconj : ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U → g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U)
    (hgp : g ^ hyp.base.p = 1) :
    g ∈ Subgroup.normalizer ((hyp.base.P ⊔ hyp.base.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; simpa [pow_succ', mul_assoc] using hconj (ih hx)
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have g_inv_eq : g⁻¹ = g ^ (hyp.base.p - 1) := by
    have hmul : g ^ (hyp.base.p - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hp_pos, hgp]
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    simpa [g_inv_eq] using hiter (hyp.base.p - 1) hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj hx, fun hx => ?_⟩
  have hpre := hinv_inc (x := g * x * g⁻¹) hx
  convert hpre using 1; group

/-- **BG Appendix C, Lemma C.3 Step 3** (mmd L4988–4992): for `g ∈ P₁^#`,
`(PU) ∩ (PU)^g = U`.  We use the dichotomy `= U ∨ = PU`; the `= PU` branch forces
`g ∈ N_G(PU) ⊆ N_G(P)`, hence (since `g` generates `P₁`) `P₁ ≤ N_G(P)`, giving the
`P₀ = P₁` contradiction `P1_ne_W2`. -/
theorem step3_inf_conj_eq_U_of_mem_P1 [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G} (hg : g ∈ data.P1) (hg1 : g ≠ 1) :
    (hyp.base.P ⊔ hyp.base.U) ⊓ (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) =
      hyp.base.U := by
  rcases data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
      (inv_mem (data.P1_normalizes_U hg)) with hU | hPU
  · exact hU
  · exfalso
    have hgp : g ^ hyp.base.p = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.P1_eq_zpowers_t ▸ hg)
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        data.t_pow_p_eq_one, one_zpow]
    have hgP : g ∈ Subgroup.normalizer (hyp.base.P : Set G) :=
      data.normalizer_P_sup_U_le_normalizer_P
        (data.mem_normalizer_P_sup_U_of_conj_of_pow
          (data.conj_mem_P_sup_U_of_inf_conj_eq hPU) hgp)
    have horder : orderOf g = hyp.base.p := by
      rcases (hyp.base.p_prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hgp))
        with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have hP1g : data.P1 = Subgroup.zpowers g := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
      rw [Nat.card_zpowers, horder, data.P1_eq_zpowers_t, Nat.card_zpowers,
        data.t_orderOf_eq_p]
    exact data.P1_ne_W2 (data.P1_eq_W2_of_le_normalizer_W2
      (data.P1_le_normalizer_W2_of_le_normalizer_P
        (hP1g ▸ Subgroup.zpowers_le.mpr hgP)))

/-- **BG Appendix C, Lemma C.3 Step 4 conclusion** (mmd L5078–5082): the `(5076)`
relation `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃` (`tᵢ = yc⁻¹ sᵢ yc`) forces `t₁ = t⁻¹`, hence
`s₁ = s⁻¹`.  Otherwise `g = t₁⁻¹ t⁻¹ ∈ P₁^#`, and for `u ∈ U^#` the common value
`u^{s₁ t₁⁻¹ t⁻¹} = u^{t⁻¹ t₃⁻¹ s₃}` lies in `(PU) ∩ (PU)^g`, which is `U` by Step 3;
then `u^{s₁} ∈ U^{t t₁} = U`, so Step 2 gives `s₁ = 1`, contradicting `(C.6)`. -/
theorem step4_sigma_primeLine_eq_s_inv [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c3 : ZMod hyp.base.p}
    (hc1 : c1 ≠ 0) (hc3 : c3 ≠ 0) (yc : G) (hty : data.t = yc⁻¹ * data.s * yc)
    (hrel : data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c1))⁻¹ * yc) * data.t⁻¹ =
      data.t⁻¹ * (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c3))⁻¹ * yc) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c3)) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c1) = data.s⁻¹ := by
  classical
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  -- conjugation by `yc` sends `⟨s⟩ = W₂` into `⟨t⟩ = P₁`.
  have hconj_zpow : ∀ n : ℤ, (yc⁻¹ * data.s * yc) ^ n = yc⁻¹ * data.s ^ n * yc := by
    intro n
    rw [show yc⁻¹ * data.s * yc = MulAut.conj yc⁻¹ data.s from by
      rw [MulAut.conj_apply, inv_inv], ← map_zpow, MulAut.conj_apply, inv_inv]
  have hmem_W2_P1 : ∀ w ∈ hyp.base.W2, yc⁻¹ * w * yc ∈ data.P1 := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.W2_eq_zpowers_s ▸ hw)
    rw [data.P1_eq_zpowers_t, Subgroup.mem_zpowers_iff]
    exact ⟨n, by rw [hty, hconj_zpow, hn]⟩
  have ht1_P1 : yc⁻¹ * s1 * yc ∈ data.P1 := hmem_W2_P1 s1 hs1W
  by_contra hne
  -- `t₁ ≠ t⁻¹`, so `g = t₁⁻¹ t⁻¹ ∈ P₁^#`.
  set g : G := (yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹ with hgdef
  have hg_P1 : g ∈ data.P1 := mul_mem (inv_mem ht1_P1) (inv_mem data.t_mem_P1)
  have hg1 : g ≠ 1 := by
    intro hg0
    apply hne
    have ht1eq : yc⁻¹ * s1 * yc = data.t⁻¹ :=
      inv_injective (eq_inv_of_mul_eq_one_left (hgdef ▸ hg0))
    have h2 : yc⁻¹ * s1 * yc = yc⁻¹ * data.s⁻¹ * yc := by rw [ht1eq, hty]; group
    exact mul_left_cancel (mul_right_cancel h2)
  -- pick a nontrivial `u ∈ U`.
  obtain ⟨u, hu_ne⟩ := exists_fieldNormalizerNormOneUnit_ne_one hyp
  set U_elt := data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp)
    with hUdef
  have hU_elt : U_elt ∈ hyp.base.U := by
    rw [hUdef, ← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  -- `s₁ g = t⁻¹ t₃⁻¹ s₃` (BG (5076)).
  have hs1g : s1 * g = data.t⁻¹ * (yc⁻¹ * s3⁻¹ * yc) * s3 := by
    rw [hgdef,
      show s1 * ((yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹) =
        s1 * (yc⁻¹ * s1⁻¹ * yc) * data.t⁻¹ from by group]
    exact hrel
  -- the common value `v = u^{s₁ g}`.
  set v : G := (s1 * g)⁻¹ * U_elt * (s1 * g) with hvdef
  -- conjugation by an `N_G(U)` element fixes `U`.
  have hconjU : ∀ h : G, h ∈ Subgroup.normalizer (hyp.base.U : Set G) →
      ∀ x : G, x ∈ hyp.base.U → h * x * h⁻¹ ∈ hyp.base.U :=
    fun h hh x hx => (Subgroup.mem_normalizer_iff.mp hh x).mp hx
  -- `v ∈ (PU)^g` since `g v g⁻¹ = s₁⁻¹ U_elt s₁ ∈ PU`.
  have hv_conj : v ∈ MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U) := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have heq : (MulAut.conj g⁻¹)⁻¹ • v = s1⁻¹ * U_elt * s1 := by
      rw [show (MulAut.conj g⁻¹)⁻¹ • v = (MulAut.conj g⁻¹)⁻¹ v from rfl,
        MulAut.conj_inv_apply, hvdef]; group
    rw [heq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs1W)))
      (Subgroup.mem_sup_right hU_elt)) (Subgroup.mem_sup_left (data.W2_le_P hs1W))
  -- `v ∈ PU` since `v = u^{t⁻¹ t₃⁻¹ s₃}` and `t, t₃ ∈ N(U)`, `s₃ ∈ P`.
  have hv_PU : v ∈ hyp.base.P ⊔ hyp.base.U := by
    have hvrw : v = s3⁻¹ * ((yc⁻¹ * s3⁻¹ * yc)⁻¹ *
        (data.t * U_elt * data.t⁻¹) * (yc⁻¹ * s3⁻¹ * yc)) * s3 := by
      rw [hvdef, hs1g]; group
    rw [hvrw]
    have h1 : data.t * U_elt * data.t⁻¹ ∈ hyp.base.U :=
      hconjU data.t data.t_normalizes_U U_elt hU_elt
    have ht3i_N : (yc⁻¹ * s3⁻¹ * yc) ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
      data.P1_normalizes_U (hmem_W2_P1 s3⁻¹ (inv_mem hs3W))
    have h2 : (yc⁻¹ * s3⁻¹ * yc)⁻¹ * (data.t * U_elt * data.t⁻¹) *
        ((yc⁻¹ * s3⁻¹ * yc)⁻¹)⁻¹ ∈ hyp.base.U :=
      hconjU _ (inv_mem ht3i_N) _ h1
    rw [inv_inv] at h2
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs3W)))
      (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_left (data.W2_le_P hs3W))
  -- by Step 3, `v ∈ U`.
  have hv_U : v ∈ hyp.base.U := by
    have hstep3 := data.step3_inf_conj_eq_U_of_mem_P1 hg_P1 hg1
    rw [← hstep3]; exact ⟨hv_PU, hv_conj⟩
  -- hence `u^{s₁} = s₁⁻¹ U_elt s₁ = g v g⁻¹ ∈ U`.
  have hu_s1 : s1⁻¹ * U_elt * s1 ∈ hyp.base.U := by
    have hconj_v : g * v * g⁻¹ = s1⁻¹ * U_elt * s1 := by rw [hvdef]; group
    rw [← hconj_v]
    exact hconjU g (data.P1_normalizes_U hg_P1) v hv_U
  -- Step 2 forces `s₁ = 1` or `u = 1`, both contradictions.
  have hmem_step : data.sigma (fieldNormalizerPrimeLineElement hyp (-c1)) *
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c1) ∈ hyp.base.U := by
    rw [fieldNormalizerPrimeLineElement_neg, map_inv]
    exact hu_s1
  rcases data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -c1) (d := c1) u hmem_step with hzero | hone
  · exact hc1 hzero.2
  · exact hu_ne hone.1

/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**: the central prime-line
factor of the `k = 3` first normal form is `s⁻¹`.  This is the last gap of BG
Appendix C; combined with the existing finite-field core it discharges
`appC_normSet_generator_relation` without the carrier field. -/
theorem step4Capstone [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.Step4Capstone := by
  intro a ha
  obtain ⟨b, hab, hb⟩ := data.exists_companion_of_unitVal_inv_mem_normSetE ha
  obtain ⟨forms⟩ := data.exists_step4C5NormalForms a b
  have hC10 := (data.relationC9_w_eq_one_and_relationC10 ha hb hab forms).2.2.2
  obtain ⟨yc, hty, h5076⟩ := data.step4_relation_5076 hC10
  have hs1 : data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) = data.s⁻¹ :=
    data.step4_sigma_primeLine_eq_s_inv forms.c1_ne_zero forms.c3_ne_zero yc hty h5076
  refine ⟨forms.u1, forms.v1, ?_⟩
  rw [← data.step4M1_eq_sigma_inr, forms.hM1, hs1,
    ← data.sScalar_neg_one_eq_sigma_primeLineElement, ← data.s_inv_eq_sScalar_neg_one]

/-- The C.3 generator-relation interface consumed by BG Appendix C
(`∀ a ∈ E, N(2a-1) = 1`), now **derived** from the Step 4 capstone `s₁ = s⁻¹`
rather than carried as the former `appC_twisted_normOne_step` field. -/
theorem appC_normSet_generator_relation [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    appCNormSetGeneratorRelation hyp :=
  data.appC_normSet_generator_relation_of_capstone data.step4Capstone

end Step4

end FieldNormalizerData

end OddOrder.Peterfalvi.S16


