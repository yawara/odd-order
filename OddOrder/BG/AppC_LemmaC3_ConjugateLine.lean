/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_Setup
import OddOrder.Mathlib.Subgroup
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# BG Appendix C, Lemma C.3: the conjugate prime line `P₁ = W₂^y`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152), Steps 3 and 4.

Hypothesis (B) supplies an element `y ∈ Q`, and BG's argument runs on the **conjugate prime
line** `P₁ = W₂^y` with generator `t = s^y`.  This file develops that line: `t` has order `p`,
`P₁ = ⟨t⟩` normalizes `U` (unlike `W₂` itself, by `W2_not_le_normalizer_U`), so conjugation by
`t` therefore induces an automorphism `tConjNormOneUnitsAut` of the norm-one group `U` of
`p`-power order.  Feeding powers of `t` through the decomposition `PU = U P₀ U` of Step 1 yields
the Step 4 decompositions, whose right components produce the norm relation `N(2a − 1) = 1`.

The second half records how `W₂` and `Q` interact: `t s⁻¹ ∈ Q`, `W₂ ∩ Q = 1`, `P ∩ Q = 1`,
the
commuting relations inside the abelian group `Q`, and the action `w2ConjQAut` of `W₂` on `Q`
used to produce the element `y_D` with `s^{y_D} = t`.

Migrated from `OddOrder.Peterfalvi.S16_CoreBounds` (issue 0151): the content is BG Appendix C,
so it is stated against the book's hypotheses (A) + (B), not against the Section 16
configuration, which merely supplies one instance of (B).
-/

namespace OddOrder.BG.AppC

open scoped Pointwise
open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- Consequently the transported prime line `W₂ = P₀` is not contained in
`N_G(U)`.  This is the Step 3 obstruction BG uses after forcing
`P₁ = P₀`. -/
theorem W2_not_le_normalizer_U (data : FieldNormalizerData p q G) :
    ¬ data.W2 ≤ Subgroup.normalizer (data.U : Set G) := by
  intro hW2
  exact data.s_not_normalizes_U (hW2 data.s_mem_W2)

/-- Applying the norm-one/unit equivalence is just `σ` on the concrete
semidirect-product complement. -/
theorem normOneUnitsEquivU_apply_coe (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) :
    (data.normOneUnitsEquivU u : G) = data.sigma (SemidirectProduct.inr u) := by
  rfl

/-- Equality of `σ`-images reflects the additive-kernel coordinate in the
concrete semidirect product. -/
theorem sigma_eq_left_eq (data : FieldNormalizerData p q G)
    {g h : NormSet.normOneFrobeniusGroup p q} (heq : data.sigma g = data.sigma h) :
    g.left = h.left :=
  congrArg (fun x : NormSet.normOneFrobeniusGroup p q => x.left)
    (data.sigma_injective heq)

/-- Equality of `σ`-images reflects the norm-one complement coordinate in the
concrete semidirect product.  This is the precise "mod `P`" reading used in BG
Appendix C, Lemma C.3 Step 4. -/
theorem sigma_eq_right_eq (data : FieldNormalizerData p q G)
    {g h : NormSet.normOneFrobeniusGroup p q} (heq : data.sigma g = data.sigma h) :
    g.right = h.right :=
  congrArg (fun x : NormSet.normOneFrobeniusGroup p q => x.right)
    (data.sigma_injective heq)

/-- Semidirect normal forms remain unique after applying the field-normalizer
embedding `σ`. -/
theorem sigma_eq_iff_left_right_eq (data : FieldNormalizerData p q G)
    {g h : NormSet.normOneFrobeniusGroup p q} :
    data.sigma g = data.sigma h ↔ g.left = h.left ∧ g.right = h.right := by
  constructor
  · intro heq
    exact ⟨data.sigma_eq_left_eq heq, data.sigma_eq_right_eq heq⟩
  · rintro ⟨hleft, hright⟩
    apply congrArg data.sigma
    apply SemidirectProduct.ext
    · exact hleft
    · exact hright

/-- The conjugate prime-line subgroup `P₁` used in BG Appendix C, expressed
with Lean left-conjugation convention. -/
noncomputable def P1 (data : FieldNormalizerData p q G) :
    Subgroup G :=
  MulAut.conj data.y • data.W2

/-- The BG element `t`, the `y`-conjugate of `s` in Lean convention. -/
noncomputable def t (data : FieldNormalizerData p q G) : G :=
  MulAut.conj data.y data.s

/-- The transported conjugate generator lies in `P₁`. -/
theorem t_mem_P1 (data : FieldNormalizerData p q G) :
    data.t ∈ data.P1 := by
  dsimp [P1, t]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  convert data.s_mem_W2 using 1
  simp
  group

/-- The conjugate generator `t` is nontrivial. -/
theorem t_ne_one (data : FieldNormalizerData p q G) :
    data.t ≠ 1 := by
  intro ht
  exact data.s_ne_one ((MulAut.conj data.y).injective (by simpa [t] using ht))

/-- The conjugate generator `t` has `p`-th power equal to `1`. -/
theorem t_pow_p_eq_one (data : FieldNormalizerData p q G) :
    data.t ^ p = 1 := by
  simpa [t, map_pow] using congrArg (MulAut.conj data.y) data.s_pow_p_eq_one

/-- The conjugate generator `t` has exact order `p`. -/
theorem t_orderOf_eq_p (data : FieldNormalizerData p q G) :
    orderOf data.t = p := by
  have hdiv : orderOf data.t ∣ p :=
    orderOf_dvd_of_pow_eq_one data.t_pow_p_eq_one
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf data.t) hdiv with h | h
  · exact False.elim (data.t_ne_one (orderOf_eq_one_iff.mp h))
  · exact h

/-- The conjugate prime line `P₁ = P₀^y` is generated by the conjugate generator
`t = s^y`. -/
theorem P1_eq_zpowers_t (data : FieldNormalizerData p q G) :
    data.P1 = Subgroup.zpowers data.t := by
  rw [P1, data.W2_eq_zpowers_s, Subgroup.pointwise_smul_def]
  simp [t]

/-- The conjugate prime line `P₁ = ⟨t⟩` is finite, of order `p`. -/
instance finite_P1 (data : FieldNormalizerData p q G) : Finite data.P1 :=
  Nat.finite_of_card_ne_zero (by
    rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p]
    exact (Fact.out : Nat.Prime p).ne_zero)

/-- The conjugate prime line `P₁` is a `p`-group of order `p`. -/
theorem P1_isPGroup (data : FieldNormalizerData p q G) :
    IsPGroup p data.P1 := by
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p, pow_one]⟩

/-- The conjugate generator `t = ysy⁻¹` lies in `QW₂`.  Indeed
`ysy⁻¹ = (ysy⁻¹s⁻¹)s`, the first factor is in `Q` because `y ∈ Q` and `s`
normalizes `Q`, and the second factor is in `W₂`. -/
theorem t_mem_Q_sup_W2 (data : FieldNormalizerData p q G) :
    data.t ∈ data.Q ⊔ data.W2 := by
  have hy_inv : data.y⁻¹ ∈ data.Q := inv_mem data.y_mem_Q
  have hsy : data.s * data.y⁻¹ * data.s⁻¹ ∈ data.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp data.s_normalizes_Q data.y⁻¹).mp hy_inv
  have hq : data.y * data.s * data.y⁻¹ * data.s⁻¹ ∈ data.Q := by
    simpa [mul_assoc] using mul_mem data.y_mem_Q hsy
  have hprod : (data.y * data.s * data.y⁻¹ * data.s⁻¹) * data.s ∈
      data.Q ⊔ data.W2 := by
    exact mul_mem
      ((le_sup_left : data.Q ≤ data.Q ⊔ data.W2) hq)
      ((le_sup_right : data.W2 ≤ data.Q ⊔ data.W2) data.s_mem_W2)
  convert hprod using 1
  dsimp [t]
  group

/-- The conjugate prime line `P₁` lies in `QW₂`.  This is the subgroup-level
form of the preceding semidirect-product decomposition of `t`. -/
theorem P1_le_Q_sup_W2 (data : FieldNormalizerData p q G) :
    data.P1 ≤ data.Q ⊔ data.W2 := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr data.t_mem_Q_sup_W2

/-- The same containment as `P1_le_Q_sup_W2`, in the `W₂Q` order used by the
product/Sylow argument in BG Appendix C Step 3. -/
theorem P1_le_W2_sup_Q (data : FieldNormalizerData p q G) :
    data.P1 ≤ data.W2 ⊔ data.Q := by
  intro x hx
  have hx' := data.P1_le_Q_sup_W2 hx
  simpa [sup_comm] using hx'

/-- Since `p` is odd, any subgroup containing `t²` also contains `t`.  This is
the cyclic-generation step in BG Appendix C, Lemma C.3 Step 3. -/
theorem t_mem_of_t_sq_mem (data : FieldNormalizerData p q G)
    {N : Subgroup G} (ht2 : data.t ^ 2 ∈ N) :
    data.t ∈ N := by
  rcases data.p_odd with ⟨k, hp⟩
  have ht_pow : (data.t ^ 2) ^ (k + 1) = data.t := by
    calc
      (data.t ^ 2) ^ (k + 1) = data.t ^ (2 * (k + 1)) := by rw [pow_mul]
      _ = data.t ^ (p + 1) := by
        congr 1
        omega
      _ = data.t := by
        rw [pow_succ, data.t_pow_p_eq_one, one_mul]
  simpa [ht_pow] using N.pow_mem ht2 (k + 1)

/-- If `t²` normalizes `P`, then the whole conjugate prime line `P₁ = ⟨t⟩`
normalizes `P`.  This is the next BG Step 3 consequence after `P char PU`. -/
theorem P1_le_normalizer_P_of_t_sq_mem
    (data : FieldNormalizerData p q G)
    (ht2 : data.t ^ 2 ∈ Subgroup.normalizer (data.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (data.P : Set G) := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr (data.t_mem_of_t_sq_mem ht2)

/-- `P₁` normalizes Peterfalvi subgroup `U`, as required in BG C.3 Step 3. -/
theorem P1_normalizes_U (data : FieldNormalizerData p q G) :
    data.P1 ≤ Subgroup.normalizer (data.U : Set G) := by
  simpa [P1] using data.W2_conj_y_normalizes_U

/-- BG Appendix C, Lemma C.3 Step 3 contradiction endpoint: the conjugate
prime line `P₁` cannot equal the original prime line `P₀ = W₂`, because `P₁`
normalizes `U` while `W₂` cannot be contained in `N_G(U)`. -/
theorem P1_ne_W2 (data : FieldNormalizerData p q G) :
    data.P1 ≠ data.W2 := by
  intro hP1
  exact data.W2_not_le_normalizer_U (by
    intro x hxW2
    exact data.P1_normalizes_U (by simpa [hP1] using hxW2))

/-- The symmetric form of `P1_ne_W2`, useful when BG has derived `P₀ = P₁`. -/
theorem W2_ne_P1 (data : FieldNormalizerData p q G) :
    data.W2 ≠ data.P1 := by
  intro hW2
  exact data.P1_ne_W2 hW2.symm

/-- The conjugate generator `t` normalizes `U`. -/
theorem t_normalizes_U (data : FieldNormalizerData p q G) :
    data.t ∈ Subgroup.normalizer (data.U : Set G) :=
  data.P1_normalizes_U data.t_mem_P1

/-- Powers of the conjugate generator `t` normalize `U`. -/
theorem t_pow_normalizes_U (data : FieldNormalizerData p q G) (n : ℕ) :
    data.t ^ n ∈ Subgroup.normalizer (data.U : Set G) :=
  pow_mem data.t_normalizes_U n

/-- Integer powers of the conjugate generator `t` normalize `U`. -/
theorem t_zpow_normalizes_U (data : FieldNormalizerData p q G) (n : ℤ) :
    data.t ^ n ∈ Subgroup.normalizer (data.U : Set G) :=
  (Subgroup.normalizer (data.U : Set G)).zpow_mem data.t_normalizes_U n

/-- Conjugating a concrete norm-one complement element by any integer power of
`t` remains in the transported subgroup `U`. -/
theorem t_zpow_conj_sigma_inr_mem_U (data : FieldNormalizerData p q G)
    (n : ℤ) (u : NormSet.normOneUnits p q) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        (data.t ^ n)⁻¹ ∈ data.U := by
  have huU :
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (data.t_zpow_normalizes_U n)
    (data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q))).mp huU

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge: any expression
`s^m (u)^{t^n} s^r` with `u ∈ U` lies in `PU`. -/
theorem s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U
    (data : FieldNormalizerData p q G)
    (m n r : ℤ) (u : NormSet.normOneUnits p q) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
              (data.t ^ n)⁻¹) *
        data.s ^ r ∈ data.P ⊔ data.U := by
  have hm : data.s ^ m ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U m
  have hmid :
      data.t ^ n * data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          (data.t ^ n)⁻¹ ∈ data.P ⊔ data.U :=
    (le_sup_right : data.U ≤ data.P ⊔ data.U)
      (data.t_zpow_conj_sigma_inr_mem_U n u)
  have hr : data.s ^ r ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U r
  exact (data.P ⊔ data.U).mul_mem
    ((data.P ⊔ data.U).mul_mem hm hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` decomposition bridge: expressions
of the form `s^m (u)^{t^n} s^r` admit the Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConj_normOne
    (data : FieldNormalizerData p q G)
    (m n r : ℤ) (u : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u₁ v₁ : NormSet.normOneUnits p q,
      data.s ^ m *
            (data.t ^ n *
              data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
                (data.t ^ n)⁻¹) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U m n r u)


/-- BG Appendix C, Lemma C.3 Step 3 intersection dichotomy before the final
contradiction: if `g` normalizes `U`, then `(PU) ∩ (PU)^g` is either `U` or
all of `PU`. -/
theorem P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    (data : FieldNormalizerData p q G) {g : G}
    (hgU : g ∈ Subgroup.normalizer (data.U : Set G)) :
    (data.P ⊔ data.U) ⊓
        (MulAut.conj g • (data.P ⊔ data.U)) = data.U ∨
      (data.P ⊔ data.U) ⊓
        (MulAut.conj g • (data.P ⊔ data.U)) = data.P ⊔ data.U := by
  let X : Subgroup G :=
    (data.P ⊔ data.U) ⊓ (MulAut.conj g • (data.P ⊔ data.U))
  have hUle : data.U ≤ X := by
    intro u hu
    refine ⟨(le_sup_right : data.U ≤ data.P ⊔ data.U) hu, ?_⟩
    have hU_image : MulAut.conj g '' (data.U : Set G) = data.U :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hgU
    have hu_image : u ∈ MulAut.conj g '' (data.U : Set G) := by
      rw [hU_image]
      exact hu
    rcases hu_image with ⟨u0, hu0, hu0_eq⟩
    have hu0_PU : u0 ∈ data.P ⊔ data.U :=
      (le_sup_right : data.U ≤ data.P ⊔ data.U) hu0
    rw [← hu0_eq]
    exact Set.smul_mem_smul_set hu0_PU
  by_cases hX : X = data.U
  · left
    exact hX
  · right
    exact data.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U hUle inf_le_left hX

/-- The same Step 3 intersection dichotomy for powers of the chosen conjugate
generator `t`. -/
theorem P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U
    (data : FieldNormalizerData p q G) (n : ℕ) :
    (data.P ⊔ data.U) ⊓
        (MulAut.conj (data.t ^ n) • (data.P ⊔ data.U)) = data.U ∨
      (data.P ⊔ data.U) ⊓
        (MulAut.conj (data.t ^ n) • (data.P ⊔ data.U)) =
          data.P ⊔ data.U :=
  data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    (data.t_pow_normalizes_U n)

/-- Conjugation by `t` as an automorphism of Peterfalvi's subgroup `U`. -/
noncomputable def tConjUAut (data : FieldNormalizerData p q G) : MulAut data.U :=
  data.U.normalizerMonoidHom ⟨data.t, data.t_normalizes_U⟩

/-- The subgroup automorphism `tConjUAut` is ambient conjugation by `t`. -/
theorem tConjUAut_apply_coe (data : FieldNormalizerData p q G) (u : data.U) :
    (data.tConjUAut u : G) = data.t * (u : G) * data.t⁻¹ := by
  rfl

/-- The `t`-conjugation automorphism of `U` has `p`-th power equal to `1`. -/
theorem tConjUAut_pow_p_eq_one (data : FieldNormalizerData p q G) : data.tConjUAut ^ p = 1 := by
  have ht_norm :
      (⟨data.t, data.t_normalizes_U⟩ : Subgroup.normalizer (data.U : Set G)) ^
          p = 1 := by
    ext
    exact data.t_pow_p_eq_one
  rw [tConjUAut, ← map_pow, ht_norm, map_one]

/-- Conjugation by `t`, transported back to the concrete norm-one unit group. -/
noncomputable def tConjNormOneUnitsAut (data : FieldNormalizerData p q G)
    : MulAut (NormSet.normOneUnits p q) :=
  (MulAut.congr data.normOneUnitsEquivU).symm data.tConjUAut

/-- The transported `t`-conjugation automorphism has `p`-th power equal to `1`. -/
theorem tConjNormOneUnitsAut_pow_p_eq_one (data : FieldNormalizerData p q G)
    : data.tConjNormOneUnitsAut ^ p = 1 := by
  rw [tConjNormOneUnitsAut,
    ← map_pow ((MulAut.congr data.normOneUnitsEquivU).symm) data.tConjUAut p,
    data.tConjUAut_pow_p_eq_one, map_one]

/-- The transported automorphism agrees with conjugation by `t` after applying
`σ` to the concrete complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) :
    data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) =
      data.tConjUAut (data.normOneUnitsEquivU u) := by
  simp [tConjNormOneUnitsAut]

/-- After transporting back to the concrete complement, the `t`-automorphism is
ambient conjugation of `σ(inr u)`. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
    (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) :
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
  calc
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
        (data.tConjUAut (data.normOneUnitsEquivU u) : G) := by
      rw [data.normOneUnitsEquivU_tConjNormOneUnitsAut]
    _ = data.t * (data.normOneUnitsEquivU u : G) * data.t⁻¹ :=
      data.tConjUAut_apply_coe (data.normOneUnitsEquivU u)
    _ = data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
      rw [data.normOneUnitsEquivU_apply_coe]

/-- Iterating the transported `t`-automorphism agrees with conjugation by
the corresponding natural power of `t` after applying `σ` to the concrete
complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe
    (data : FieldNormalizerData p q G)
    (n : ℕ) (u : NormSet.normOneUnits p q) :
    (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) =
      data.t ^ n * data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        (data.t ^ n)⁻¹ := by
  induction n with
  | zero =>
      simp [data.normOneUnitsEquivU_apply_coe]
  | succ n ih =>
      calc
        (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ (n + 1)) u) : G) =
            data.t *
                (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) *
              data.t⁻¹ := by
          rw [pow_succ']
          exact data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
            ((data.tConjNormOneUnitsAut ^ n) u)
        _ = data.t *
              (data.t ^ n *
                data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
                  (data.t ^ n)⁻¹) *
            data.t⁻¹ := by
          rw [ih]
        _ = data.t ^ (n + 1) *
              data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
                (data.t ^ (n + 1))⁻¹ := by
          group

/-- The natural-power conjugate of a concrete complement element is the `σ`
image of the corresponding power of the transported norm-one automorphism. -/
theorem t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow
    (data : FieldNormalizerData p q G)
    (n : ℕ) (u : NormSet.normOneUnits p q) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        (data.t ^ n)⁻¹ =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
          NormSet.normOneFrobeniusGroup p q) := by
  rw [← data.normOneUnitsEquivU_apply_coe ((data.tConjNormOneUnitsAut ^ n) u)]
  exact (data.normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe n u).symm

/-- Natural-power form of the Step 4 conjugation rewrite: the middle
`(u)^{t^n}` term can be read as the concrete norm-one unit obtained by iterating
`tConjNormOneUnitsAut`. -/
theorem s_zpow_mul_t_pow_conj_sigma_inr_mul_s_zpow_eq_sigma_inr_tConjNormOneUnitsAut_pow
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (n : ℕ) (u : NormSet.normOneUnits p q) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
              (data.t ^ n)⁻¹) *
        data.s ^ r =
      data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r := by
  rw [data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n u]

/-- Natural-power variant of the Step 4 `(C.5)` membership bridge, with the
middle term already expressed in the concrete norm-one complement. -/
theorem s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (n : ℕ) (u : NormSet.normOneUnits p q) :
    data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r ∈ data.P ⊔ data.U := by
  have hm : data.s ^ m ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            NormSet.normOneFrobeniusGroup p q) ∈ data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u),
      ⟨(data.tConjNormOneUnitsAut ^ n) u, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            NormSet.normOneFrobeniusGroup p q) ∈ data.P ⊔ data.U :=
    (le_sup_right : data.U ≤ data.P ⊔ data.U) hmidU
  have hr : data.s ^ r ∈ data.P ⊔ data.U := data.s_zpow_mem_P_sup_U r
  exact (data.P ⊔ data.U).mul_mem
    ((data.P ⊔ data.U).mul_mem hm hmid) hr

/-- Natural-power variant of the Step 4 `(C.5)` decomposition bridge: after
rewriting `(u)^{t^n}` as a concrete iterate of `tConjNormOneUnitsAut`, the term
still admits Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (n : ℕ) (u : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u₁ v₁ : NormSet.normOneUnits p q,
      data.s ^ m *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U m r n u)


/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge: once a natural-power
`(C.5)` term is written in Step 1 normal form, applying the right projection of
the concrete semidirect product reads off the complement equation. -/
theorem right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
    (data : FieldNormalizerData p q G)
    (m r : ℤ) (n : ℕ) (u u₁ v₁ : NormSet.normOneUnits p q)
    (c : ZMod p)
    (hdec : data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    (data.tConjNormOneUnitsAut ^ n) u = u₁ * v₁ := by
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
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              NormSet.normOneFrobeniusGroup p q) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
            primeLineElement p q c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              NormSet.normOneFrobeniusGroup p q) * pr) =
          data.s ^ m *
              data.sigma
                (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                  NormSet.normOneFrobeniusGroup p q) *
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

/-- BG Appendix C, Lemma C.3 Step 4 final specialization: the first equation of
`(C.5)` at `k = 3` has a Step 1 normal form.  This is the entry point for the
final paragraph, where `u` is instantiated with the norm-one unit represented by
`a ∈ E`. -/
theorem exists_step4_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) :
    ∃ c : ZMod p, ∃ u₁ v₁ : NormSet.normOneUnits p q,
      data.s *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
                NormSet.normOneFrobeniusGroup p q) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q c) *
            data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := by
  simpa using
    data.exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)

/-- The `mod P` reading of the `k = 3` first `(C.5)` equation: the middle term
`u^{-1}` conjugated by `t^3` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (u u₁ v₁ : NormSet.normOneUnits p q) (c : ZMod p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    (data.tConjNormOneUnitsAut ^ 3) u⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if a first `k = 3` normal form has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for the middle complement
element `w`. -/
theorem normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (w u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    NormSet.normN p q
      ((2 : GaloisField p q) *
          (((w : NormSet.normOneUnits p q) :
              (GaloisField p q)ˣ) :
              GaloisField p q) - 1) = 1 := by
  let F := GaloisField p q
  let H := NormSet.normOneFrobeniusGroup p q
  have hline_neg_one :
      primeLineElement p q (-1 : ZMod p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) : H) := by
    simp [primeLineElement, F]
  have hline_neg_two :
      primeLineElement p q (-2 : ZMod p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
    simp [primeLineElement, F, map_neg, map_ofNat]
  have hσ :
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
        data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
          data.s * data.sigma (SemidirectProduct.inr w : H) * data.s ^ (-2 : ℤ) := by
        have hs :
            data.s =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) := by
          simp [FieldNormalizerData.s, primeLineGenerator, F]
        have hsneg_two :
            data.s ^ (-2 : ℤ) =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
          simpa [hline_neg_two] using data.s_zpow_neg_two_eq_primeLineElement_neg_two
        rw [map_mul, map_mul, hsneg_two, hs]
      _ = data.sigma (SemidirectProduct.inr u₁ : H) *
            data.sigma (primeLineElement p q (-1 : ZMod p)) *
              data.sigma (SemidirectProduct.inr v₁ : H) := by
        exact hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
        simp [map_mul, hline_neg_one]
  have hH := data.sigma_injective hσ
  simpa [F] using
    NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
      (p := p) (q := q) data.q_prime.ne_zero w u₁ v₁ hH

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if the first `k = 3` equation of `(C.5)` has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for
`w = (tConjNormOneUnitsAut^3)(u^{-1})`. -/
theorem normN_two_mul_sub_one_of_step4_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (u u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    NormSet.normN p q
      ((2 : GaloisField p q) *
          ((((data.tConjNormOneUnitsAut ^ 3) u⁻¹ : NormSet.normOneUnits p q) :
              (GaloisField p q)ˣ) :
              GaloisField p q) - 1) = 1 := by
  simpa using
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
      ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) u₁ v₁ hdec

/-- A first `k = 3` coordinate step for every element of `E` implies the
AppC generator relation.  This is the exact S16-facing target left after the
BG C.3 Step 4 argument has shown that the middle prime-line factor in the
relevant normal form is `s^{-1}`. -/
theorem appC_normSet_generator_relation_of_first_k_three_coordinate
    (data : FieldNormalizerData p q G)
    (hstep :
      ∀ w : NormSet.normOneUnits p q,
        (((w : NormSet.normOneUnits p q) :
            (GaloisField p q)ˣ) :
            GaloisField p q) ∈
          NormSet.normSetE p q →
          ∃ u₁ v₁ : NormSet.normOneUnits p q,
            data.s *
                data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
              data.s ^ (-2 : ℤ) =
            data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
              data.sigma (primeLineElement p q (-1 : ZMod p)) *
                data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    normSetGeneratorRelation p q := by
  intro a ha
  let w : NormSet.normOneUnits p q :=
    NormSet.normOneUnitOfMemNormSetE
      p q data.q_prime.pos ha
  have hwE :
      (((w : NormSet.normOneUnits p q) :
          (GaloisField p q)ˣ) :
          GaloisField p q) ∈
        NormSet.normSetE p q := by
    simpa [w] using ha
  rcases hstep w hwE with ⟨u₁, v₁, hdec⟩
  have hnorm :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition w u₁ v₁ hdec
  simpa [w] using hnorm

/-- The `twistedInv` operation in the norm-one C.3 interface is ambient
conjugation by `t` applied to the inverse complement element. -/
theorem normOneUnitsEquivU_twistedInv_tConjNormOneUnitsAut_apply_coe
    (data : FieldNormalizerData p q G)
    (u : NormSet.normOneUnits p q) :
    (data.normOneUnitsEquivU
        (NormSet.twistedInv data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u⁻¹) * data.t⁻¹ := by
  simpa [NormSet.twistedInv] using
    data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe u⁻¹

/-- To produce the S16 AppC C.3 interface it is enough to prove the norm-set
step for the concrete automorphism induced by conjugation with `t`. -/
theorem appC_twisted_normOne_step_of_tConjNormOneUnitsAut
    (data : FieldNormalizerData p q G) :
    NormSet.normSetETwistedNormOneStep
        (p := p) (q := q) data.tConjNormOneUnitsAut →
      normSetTwistedNormOneStep p q := by
  intro hstep
  exact ⟨data.tConjNormOneUnitsAut, data.tConjNormOneUnitsAut_pow_p_eq_one, hstep⟩

/-- The conjugate generator `t` also normalizes `Q`. -/
theorem t_normalizes_Q (data : FieldNormalizerData p q G) :
    data.t ∈ Subgroup.normalizer (data.Q : Set G) := by
  have hyN : data.y ∈ Subgroup.normalizer (data.Q : Set G) :=
    Subgroup.le_normalizer data.y_mem_Q
  dsimp [t]
  exact mul_mem (mul_mem hyN data.s_normalizes_Q) (inv_mem hyN)

/-- The first BG commutator factor `s⁻¹t` lies in `Q`. -/
theorem s_inv_mul_t_mem_Q (data : FieldNormalizerData p q G) :
    data.s⁻¹ * data.t ∈ data.Q := by
  have hsN_inv : data.s⁻¹ ∈ Subgroup.normalizer (data.Q : Set G) :=
    inv_mem data.s_normalizes_Q
  have hconj_y : data.s⁻¹ * data.y * data.s ∈ data.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hsN_inv data.y).mp data.y_mem_Q
  have hy_inv : data.y⁻¹ ∈ data.Q := inv_mem data.y_mem_Q
  dsimp [t]
  simpa [mul_assoc] using mul_mem hconj_y hy_inv

private theorem inv_pow_mul_pow_mem_of_inv_mul_mem {H : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (H : Set G)) (hrel : a⁻¹ * b ∈ H) :
    ∀ n : ℕ, (a⁻¹) ^ n * b ^ n ∈ H := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have haN_inv : a⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem haN
      have hconj : a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a ∈ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp haN_inv ((a⁻¹) ^ n * b ^ n)).mp ih
      have hprod : (a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a) * (a⁻¹ * b) ∈ H :=
        mul_mem hconj hrel
      convert hprod using 1
      group

/-- The BG commutator factors `(s⁻¹)^n t^n` lie in `Q`. -/
theorem s_inv_pow_mul_t_pow_mem_Q (data : FieldNormalizerData p q G) (n : ℕ) :
    (data.s⁻¹) ^ n * data.t ^ n ∈ data.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.s_normalizes_Q data.s_inv_mul_t_mem_Q n

/-- Elements of the transported `Q` commute.  This is the S16-facing form of
BG Appendix C Remark (B)/(X) used in Lemma C.3 Step 4 when rewriting (C.3) to
(C.4). -/
theorem Q_mul_comm (data : FieldNormalizerData p q G)
    {x y : G} (hx : x ∈ data.Q) (hy : y ∈ data.Q) :
    x * y = y * x := by
  have := data.Q_commutative
  exact setLike_mul_comm (s := data.Q) hx hy

/-- In `W₂Q`, the `Q` factor is normalized by both `W₂` and `Q`. -/
theorem W2_sup_Q_le_normalizer_Q (data : FieldNormalizerData p q G) :
    data.W2 ⊔ data.Q ≤ Subgroup.normalizer (data.Q : Set G) :=
  sup_le data.W2_normalizes_Q Subgroup.le_normalizer

/-- The `Q` factor is normal inside the product subgroup `W₂Q`.  This is the
structural input needed before applying the standard p-subgroup/Sylow argument
inside `W₂Q`. -/
theorem Q_subgroupOf_W2_sup_Q_normal (data : FieldNormalizerData p q G) :
    (data.Q.subgroupOf (data.W2 ⊔ data.Q)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer data.W2_sup_Q_le_normalizer_Q

/-- Elements of the transported prime line `W₂ = σ(P₀)` have `p`-th power
`1`.  This is the ambient `G` form needed when reading BG Appendix C Step 4
modulo `Q`. -/
theorem W2_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.W2) :
    x ^ p = 1 := by
  have : Finite data.W2 := Nat.finite_of_card_ne_zero (by
    rw [data.card_W2]
    exact (Fact.out : Nat.Prime p).ne_zero)
  have hxpow := pow_card_eq_one' (G := data.W2) (x := (⟨x, hx⟩ : data.W2))
  have hxpow_coe := congrArg Subtype.val hxpow
  simpa [data.card_W2] using hxpow_coe

/-- The transported additive kernel `P` and the transported elementary abelian
subgroup `Q` meet trivially.  In BG Appendix C Step 3 this is the first input for
reading `P ∩ QP₀ = P₀`. -/
theorem P_inf_Q_eq_bot (data : FieldNormalizerData p q G) :
    data.P ⊓ data.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxp : x ^ p = 1 := data.P_pow_p_eq_one hx.1
  simpa [Subgroup.mem_bot] using data.eq_one_of_mem_Q_of_pow_p_eq_one hx.2 hxp

/-- BG Appendix C Step 3 product intersection: inside the product subgroup `W₂Q`,
the transported additive kernel `P` meets `W₂Q` exactly in `W₂`.  This is the
Lean form of BG's `P ∩ QP₀ = P₀`. -/
theorem P_inf_W2_sup_Q_eq_W2 (data : FieldNormalizerData p q G) :
    data.P ⊓ (data.W2 ⊔ data.Q) = data.W2 := by
  let H : Subgroup G := data.W2 ⊔ data.Q
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ data.P := hx.1
    have hxH : x ∈ H := hx.2
    have : (data.Q.subgroupOf H).Normal := data.Q_subgroupOf_W2_sup_Q_normal
    have hmem : (⟨x, hxH⟩ : H) ∈
        data.W2.subgroupOf H ⊔ data.Q.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup (le_sup_left : data.W2 ≤ H)
        (le_sup_right : data.Q ≤ H), Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨⟨w, _hwH⟩, hw, ⟨q, _hqH⟩, hq, heq⟩ := hmem
    have hxeq : x = w * q := (congrArg Subtype.val heq).symm
    have hwW2 : w ∈ data.W2 := hw
    have hqQ : q ∈ data.Q := hq
    have hqP : q ∈ data.P := by
      have : w⁻¹ * x ∈ data.P :=
        data.P.mul_mem (data.P.inv_mem (data.W2_le_P hwW2)) hxP
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have hq_one : q = 1 := by
      have : q ∈ data.P ⊓ data.Q := ⟨hqP, hqQ⟩
      rw [data.P_inf_Q_eq_bot, Subgroup.mem_bot] at this
      exact this
    rw [hxeq, hq_one, mul_one]
    exact hwW2
  · exact le_inf data.W2_le_P le_sup_left

/-- The same product-intersection statement in BG's displayed `QP₀` order. -/
theorem P_inf_Q_sup_W2_eq_W2 (data : FieldNormalizerData p q G) :
    data.P ⊓ (data.Q ⊔ data.W2) = data.W2 := by
  simpa [sup_comm] using data.P_inf_W2_sup_Q_eq_W2

/-- If the conjugate line `P₁` normalizes `P`, then, since `P₁ ≤ W₂Q`, it also
normalizes `P ∩ W₂Q = W₂`.  This is the formal normalizer step in BG Appendix C
Step 3 before the final Sylow/product p-subgroup contradiction. -/
theorem P1_le_normalizer_W2_of_le_normalizer_P
    (data : FieldNormalizerData p q G)
    (hP1P : data.P1 ≤ Subgroup.normalizer (data.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (data.W2 : Set G) := by
  let H : Subgroup G := data.W2 ⊔ data.Q
  intro x hxP1
  have hxNP : x ∈ Subgroup.normalizer (data.P : Set G) := hP1P hxP1
  have hxH : x ∈ H := data.P1_le_W2_sup_Q hxP1
  have hxNH : x ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hxH
  rw [Subgroup.mem_normalizer_iff] at hxNP hxNH ⊢
  intro y
  constructor
  · intro hyW2
    have hyInf : y ∈ data.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hyW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mp hyInf.1, (hxNH y).mp hyInf.2⟩
  · intro hconjW2
    have hconjInf : x * y * x⁻¹ ∈ data.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hconjW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mpr hconjInf.1, (hxNH y).mpr hconjInf.2⟩

/-- The transported prime line and the transported elementary abelian `Q` meet
trivially.  This is the BG Appendix C Step 4 `P₀ ∩ Q = 1` input after
identifying `P₀` with `W₂ = σ(P₀)`. -/
theorem W2_inf_Q_eq_bot (data : FieldNormalizerData p q G) :
    data.W2 ⊓ data.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxW2 : x ∈ data.W2 := hx.1
  have hxQ : x ∈ data.Q := hx.2
  have hxp : x ^ p = 1 := data.W2_pow_p_eq_one hxW2
  simpa [Subgroup.mem_bot] using data.eq_one_of_mem_Q_of_pow_p_eq_one hxQ hxp

/-- The orders of `W₂ = σ(P₀)` and `Q` are coprime: `|W₂| = p` is prime, `|Q|`
is a power of `q`, and `p ≠ q`.  This is the coprimality input to BG Appendix C
Remark (X)'s coprime decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆` (Isaacs Thm 4.34 /
BG Prop 1.6(d)), used in the Lemma C.3 Step 4 kernel argument. -/
theorem W2_card_coprime_Q_card (data : FieldNormalizerData p q G) :
    Nat.Coprime (Nat.card ↥data.W2) (Nat.card ↥data.Q) := by
  rw [data.card_W2]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr data.Q_pPrime

/-- If `P₁` normalizes `W₂`, then the product `W₂P₁` is a p-subgroup of `W₂Q`.
Since `Q` is p-prime and `|W₂| = p`, the p-part of `W₂Q` has order exactly `p`,
so `P₁ = W₂`.  This is the final product/Sylow argument in BG Appendix C Step 3. -/
theorem P1_eq_W2_of_le_normalizer_W2
    (data : FieldNormalizerData p q G)
    (hP1W2 : data.P1 ≤ Subgroup.normalizer (data.W2 : Set G)) :
    data.P1 = data.W2 := by
  let R : Subgroup G := data.W2 ⊔ data.P1
  let H : Subgroup G := data.W2 ⊔ data.Q
  have hR_p : IsPGroup p R := by
    exact IsPGroup.to_sup_of_normal_left' data.W2_isPGroup data.P1_isPGroup hP1W2
  have hW2_le_R : data.W2 ≤ R := le_sup_left
  have hR_le_H : R ≤ H := sup_le le_sup_left data.P1_le_W2_sup_Q
  have : Finite ↥R := (data.setFinite_W2_sup_Q.subset hR_le_H).to_subtype
  obtain ⟨k, hR_card⟩ := (IsPGroup.iff_card (p := p) (G := R)).mp hR_p
  have hW2_card_le_R : Nat.card ↥data.W2 ≤ Nat.card ↥R :=
    Subgroup.card_le_of_le hW2_le_R
  have hk_pos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hp_le_one : p ≤ 1 := by
      simpa [hR_card, hk0, pow_zero, ← data.card_W2] using hW2_card_le_R
    exact (not_lt_of_ge hp_le_one) (Fact.out : Nat.Prime p).one_lt
  have hR_dvd_H : Nat.card ↥R ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hR_le_H
  have hH_card : Nat.card ↥H = p * Nat.card ↥data.Q := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card data.W2 data.Q
    have hcarrier : (↑H : Set G) = (↑data.W2 * ↑data.Q : Set G) := by
      simpa [H] using
        Subgroup.coe_mul_of_left_le_normalizer_right
          data.W2 data.Q data.W2_normalizes_Q
    rw [data.W2_inf_Q_eq_bot, Subgroup.card_bot, mul_one,
      data.card_W2, ← hcarrier] at hcard
    simpa [H, Nat.card_coe_set_eq] using hcard
  have hpk_dvd : p ^ k ∣ p * Nat.card ↥data.Q := by
    simpa [hR_card, hH_card] using hR_dvd_H
  have hQ_coprime_p : Nat.Coprime (Nat.card ↥data.Q) p := by
    simpa [← data.card_W2] using (data.W2_card_coprime_Q_card).symm
  have hpk_coprime_Q : Nat.Coprime (p ^ k) (Nat.card ↥data.Q) :=
    hQ_coprime_p.symm.pow_left k
  have hpk_dvd_p : p ^ k ∣ p :=
    Nat.Coprime.dvd_of_dvd_mul_right hpk_coprime_Q hpk_dvd
  have hk_le_one : k ≤ 1 := by
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : Nat.Prime p).one_lt).mp
      (by simpa [pow_one] using hpk_dvd_p)
  have hk_eq_one : k = 1 := le_antisymm hk_le_one (Nat.succ_le_of_lt hk_pos)
  have hR_card_eq_W2 : Nat.card ↥R = Nat.card ↥data.W2 := by
    rw [hR_card, hk_eq_one, pow_one, data.card_W2]
  have hW2_eq_R : data.W2 = R := by
    exact Subgroup.eq_of_le_of_card_ge hW2_le_R (by rw [hR_card_eq_W2])
  have hP1_le_W2 : data.P1 ≤ data.W2 := by
    intro x hx
    have hxR : x ∈ R := (le_sup_right : data.P1 ≤ R) hx
    simpa [hW2_eq_R] using hxR
  have hP1_card : Nat.card ↥data.P1 = p := by
    rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p]
  exact Subgroup.eq_of_le_of_card_ge hP1_le_W2 (by
    rw [data.card_W2, hP1_card])


/-- The conjugation action of `W₂ = σ(P₀)` on the normal elementary abelian
subgroup `Q`, restricted to `↥Q`.  This is the coprime action used to
instantiate BG Appendix C Remark (X)'s decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆`
(Isaacs Thm 4.34 / BG Prop 1.6(d)) in the Lemma C.3 Step 4 kernel argument. -/
noncomputable def w2ConjQAut (data : FieldNormalizerData p q G) :
    ↥data.W2 →* MulAut ↥data.Q :=
  (Subgroup.normalizerMonoidHom (H := data.Q)).comp
    (Subgroup.inclusion data.W2_normalizes_Q)

/-- **BG Appendix C, Remark (X)** (Isaacs Thm 4.34 / BG Prop 1.6(d)): under the
coprime conjugation action of `W₂` on the elementary abelian `Q`, the fixed
points `C_Q(W₂)` and the action commutator `⁅Q, W₂⁆` meet trivially.  This is the
fixed-point-free input to the BG Lemma C.3 Step 4 kernel argument: an element of
`⁅Q, W₂⁆` fixed by `W₂` (equivalently, centralizing the prime line) is trivial. -/
theorem w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot
    (data : FieldNormalizerData p q G) :
    Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut = ⊥ := by
  have := data.Q_commutative
  let : CommGroup ↥data.Q :=
    { (inferInstance : Group ↥data.Q) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm (s := data.Q) a.2 b.2) }
  exact OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    data.w2ConjQAut data.W2_card_coprime_Q_card

/-- **BG Appendix C, Lemma C.3 Step 4 fixed-point-free input**: an element of the
action commutator `⁅Q, W₂⁆` fixed by the whole `W₂`-action is trivial.  Since
`W₂` is generated by `s`, this is BG's statement that `s` acts without nonzero
fixed points on `⁅Q, P₀⁆`, the key to inverting `(s⁻¹ - 1)` in the kernel step. -/
theorem w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed
    (data : FieldNormalizerData p q G)
    {x : ↥data.Q}
    (hx : x ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut)
    (hfix : ∀ w : ↥data.W2, data.w2ConjQAut w x = x) :
    x = 1 := by
  have hmem : x ∈ Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut :=
    ⟨Subgroup.mem_fixedPointsOfMulAut.mpr hfix, hx⟩
  rw [data.w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot] at hmem
  simpa using hmem

/-- The `W₂`-conjugation action on `Q`, read in the ambient group `G`: it is
genuine conjugation `w x w⁻¹`. -/
theorem w2ConjQAut_apply_coe (data : FieldNormalizerData p q G)
    (w : ↥data.W2) (x : ↥data.Q) :
    ((data.w2ConjQAut w x : ↥data.Q) : G) = (w : G) * (x : G) * (w : G)⁻¹ := rfl

/-- **BG Appendix C, Remark (XI)**: we may assume `y ∈ ⁅Q, P₀⁆`.  Writing the
coprime decomposition `Q = ⁅Q,W₂⁆ · C_Q(W₂)`, the centralizer component `yC` of
`y` commutes with `s ∈ W₂`, so the conjugate generator `t = y s y⁻¹` is already
produced by the action-commutator component `yD ∈ ⁅Q, W₂⁆`: `t = yD s yD⁻¹`. -/
theorem exists_yD_mem_actionCommutator_conj_s_eq_t
    (data : FieldNormalizerData p q G) :
    ∃ yD : ↥data.Q,
      yD ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ∧
        MulAut.conj (yD : G) data.s = data.t := by
  have := data.Q_commutative
  let : CommGroup ↥data.Q :=
    { (inferInstance : Group ↥data.Q) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm (s := data.Q) a.2 b.2) }
  have hsup : OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
      Subgroup.fixedPointsOfMulAut data.w2ConjQAut = ⊤ := by
    rw [sup_comm]
    exact OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      data.W2_card_coprime_Q_card (Or.inr inferInstance)
  have hmem : (⟨data.y, data.y_mem_Q⟩ : ↥data.Q) ∈
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
        Subgroup.fixedPointsOfMulAut data.w2ConjQAut := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨yD, hyD, yC, hyC, hyDyC⟩ := hmem
  refine ⟨yD, hyD, ?_⟩
  have hyC_s : (yC : G) * data.s = data.s * (yC : G) := by
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hyC ⟨data.s, data.s_mem_W2⟩
    have hcoe := congrArg (Subtype.val) hfix
    rw [data.w2ConjQAut_apply_coe] at hcoe
    exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
  have hconj_raw : (yC : G) * data.s * (yC : G)⁻¹ = data.s := by
    rw [hyC_s]; group
  have hy_coe : (data.y : G) = (yD : G) * (yC : G) := by
    have h := congrArg (Subtype.val) hyDyC
    simpa using h.symm
  change MulAut.conj (yD : G) data.s = MulAut.conj data.y data.s
  rw [MulAut.conj_apply, MulAut.conj_apply, hy_coe, mul_inv_rev,
    show (yD : G) * (yC : G) * data.s * ((yC : G)⁻¹ * (yD : G)⁻¹)
        = (yD : G) * ((yC : G) * data.s * (yC : G)⁻¹) * (yD : G)⁻¹ by group,
    hconj_raw]

/-- **BG Appendix C, Lemma C.3 Step 4, the `s^a` notation**: conjugating the
prime-line generator `s` by `σ(inr a)` (`a ∈ U`) acts as scalar multiplication by
`a⁻¹` on the additive line, i.e. `σ(inr a)⁻¹ s σ(inr a) = σ(inl (a⁻¹ · 1))`.  This
is the concrete reading of BG's relation `as + bs = 2s ⟹ s^a s^b = s²`. -/
theorem sigma_inr_inv_mul_s_mul_sigma_inr (data : FieldNormalizerData p q G)
    (a : NormSet.normOneUnits p q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
        data.sigma (SemidirectProduct.inr a) =
      data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd
        (((((a⁻¹ : NormSet.normOneUnits p q) :
            (GaloisField p q)ˣ) :
            GaloisField p q)) *
          (1 : GaloisField p q)))) := by
  rw [FieldNormalizerData.s, primeLineGenerator, ← map_inv, ← map_mul,
    ← map_mul]
  congr 1
  rw [← map_inv]
  have h := NormSet.normOneFrobenius_conj_inl
    (p := p) (q := q) a⁻¹
    (1 : GaloisField p q)
  rw [inv_inv] at h
  exact h

/-- The BG factors `(s⁻¹)^m t^m` and `(s⁻¹)^n t^n` commute because both lie
in `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm (data : FieldNormalizerData p q G) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.s⁻¹) ^ n * data.t ^ n) =
      ((data.s⁻¹) ^ n * data.t ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.s_inv_pow_mul_t_pow_mem_Q n)

/-- The opposite first commutator factor `t⁻¹s` lies in `Q`. -/
theorem t_inv_mul_s_mem_Q (data : FieldNormalizerData p q G) :
    data.t⁻¹ * data.s ∈ data.Q := by
  simpa using inv_mem data.s_inv_mul_t_mem_Q

/-- The opposite BG commutator factors `(t⁻¹)^n s^n` lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mem_Q (data : FieldNormalizerData p q G) (n : ℕ) :
    (data.t⁻¹) ^ n * data.s ^ n ∈ data.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.t_normalizes_Q data.t_inv_mul_s_mem_Q n

/-- The opposite BG factors `(t⁻¹)^m s^m` and `(t⁻¹)^n s^n` commute because
both lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mul_comm (data : FieldNormalizerData p q G) (m n : ℕ) :
    ((data.t⁻¹) ^ m * data.s ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.t⁻¹) ^ m * data.s ^ m) :=
  data.Q_mul_comm (data.t_inv_pow_mul_s_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

/-- The two BG commutator-factor families commute with each other inside `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm_t_inv_pow_mul_s_pow
    (data : FieldNormalizerData p q G) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

-- The C.3 generator-relation interface `appC_normSet_generator_relation` is now
-- *derived* from the Step 4 capstone (`s₁ = s⁻¹`) rather than carried as a field;
-- see its definition after `step4Capstone` below.

end FieldNormalizerData

end OddOrder.BG.AppC
