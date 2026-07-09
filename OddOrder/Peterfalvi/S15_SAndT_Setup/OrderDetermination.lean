import OddOrder.Peterfalvi.S15_SAndT_Setup.NormEstimates

/-!
# Peterfalvi (13.11)-(13.15) — order and divisor determination

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (13.11)--(13.15): order and divisor determination -/

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

/-- **Numerical core shared by Peterfalvi (13.12) and (13.15)**: the upper estimate
`m < q·p / ((2q+1)(p-1))` — obtained from `c ≥ 2q+1` (13.12) resp. the divisor `x ≥ 2q+1`
(13.15) together with the analytic inequality (13.10) and `u ≤ (p^q-1)/(p-1)` (13.2.c) — combined
with the (13.11) lower bounds on `m` forces `q = 3`.

Self-contained `ℚ`-arithmetic over an abstract `m` satisfying the (13.11.a,b) lower bounds; `p`, `q`
are odd primes so `p = 3 ∨ p ≥ 5` and `q = 3 ∨ q ≥ 5`, as supplied by the callers.

* `p ≥ 5`: `m < q·p/((2q+1)(p-1)) < (1/2)(5/4) = 5/8 < 7/10`, against `m > 7/10` (13.11.b).
* `p = 3`, `q ≥ 7`: `m < 3q/(2(2q+1)) < 3/4 < 8/10`, against `m > 8/10` (13.11.a).
* `p = 3`, `5 ≤ q < 7`: `m < 3q/(2(2q+1)) < 7/10`, against `m > 7/10` (13.11.b). -/
theorem caseB_numeric_forces_q_three {p q : ℕ} {m : ℚ}
    (hp : p = 3 ∨ 5 ≤ p) (hq : q = 3 ∨ 5 ≤ q)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hbound : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1))) :
    q = 3 := by
  rcases hq with hq3 | hq5
  · exact hq3
  exfalso
  have hqR : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
  have hm7over : (7 : ℚ) / 10 < m := hm5 hq5
  rcases hp with rfl | hp5
  · -- `p = 3`
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * (((3 : ℕ) : ℚ) - 1) := by
      rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num]; nlinarith [hqR]
    have hb := (lt_div_iff₀ hden).mp hbound
    rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num] at hb
    by_cases hq7 : 7 ≤ q
    · have h87 : (8 : ℚ) / 10 < m := hm7 hq7
      nlinarith [hb, h87, hqR]
    · have hqlt7 : (q : ℚ) < 7 := by exact_mod_cast (show q < 7 by omega)
      nlinarith [hb, hm7over, hqR, hqlt7]
  · -- `p ≥ 5`
    have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by nlinarith [hqR, hpR5]
    have hb := (lt_div_iff₀ hden).mp hbound
    nlinarith [hb, hm7over, hqR, hpR5]

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

/-- The `m`-only part of **Peterfalvi (13.11)**.  The full `numeric_bounds`
theorem below also packages the `u/c` inequality in the `q = 3` branch, so it
still waits for the analytic estimate (13.10). -/
theorem numeric_m_bounds (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 → 5 ≤ hyp.p → hyp.m > (49 / 100 : ℚ)) := by
  exact ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q,
    fun hq3 hp5 => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5⟩

end Hypothesis

/-- **Arithmetic bridge for Peterfalvi (13.2.c), non-Galois case**: `(p-1)^(q-1) ≤ (p^q-1)/(p-1)`.

In the non-Galois type-`P` case the Singer/semilinear bound gives `u ≤ (p-1)^(q-1)` (Coq
`FTtypeP_facts`, via `card_mx`), which this relaxes to the uniform (13.2.c) form
`u ≤ (p^q-1)/(p-1)`.  Elementary: `(p-1)^(q-1) ≤ p^(q-1) ≤ (p^q-1)/(p-1)` (the last since
`p^(q-1)·(p-1) = p^q - p^(q-1) ≤ p^q - 1`).  Pure `ℕ` arithmetic, `sorry`-free. -/
theorem pred_pow_le_cyclotomic_quotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  refine le_trans (Nat.pow_le_pow_left (Nat.sub_le p 1) (q - 1)) ?_
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have ha : 1 ≤ (d + 1) ^ (q - 1) := Nat.one_le_pow _ _ (by omega)
  have hap' : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ q := by
    have h1 : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ (q - 1) * (d + 1) := by ring
    rw [h1, ← pow_succ]; congr 1; omega
  omega

/-- **Peterfalvi (8.4.d) restricted to `C`**: `W₁` acts fixed-point-freely on `C ⊆ U` by
conjugation — no `w ∈ W₁ #` centralizes any `c ∈ C #`.  `U W₁` is a Frobenius group with kernel `U`
(`typeP_uW1_frobenius`), and `C = U ⊓ C_G(P) ≤ U`, so the Frobenius fpf condition restricts to `C`.
The fpf input to the (13.12) `c ≡ 1 (mod q)` step (Coq `dv_2q_c1`). -/
theorem Hypothesis.W1_fpf_C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ w ∈ hyp.W1, w ≠ 1 → ∀ c ∈ hyp.C, c ≠ 1 → w * c * w⁻¹ ≠ c := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have frob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hUne
  rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at frob
  have hCU : hyp.C ≤ hyp.U := by rw [hyp.C_eq]; exact inf_le_left
  intro w hw hw1 c hc hc1
  have hwL : w ∈ hyp.U ⊔ hyp.W1 := (le_sup_right : hyp.W1 ≤ _) hw
  have hcL : c ∈ hyp.U ⊔ hyp.W1 := (le_sup_left : hyp.U ≤ _) (hCU hc)
  have hne1 : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hw1 (by simpa using congrArg Subtype.val h)
  have hnec : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hc1 (by simpa using congrArg Subtype.val h)
  have hmemw : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr hw
  have hmemc : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr (hCU hc)
  have hconj := frob.conj_frobenius _ hmemw hne1 _ hmemc hnec
  intro heq
  apply hconj
  apply Subtype.ext
  push_cast
  exact heq

/-- `W₁` normalizes `C = U ⊓ C_G(P)`: `W₁ ≤ S ≤ N_G(P)` (so it normalizes `C_G(P)`) and
`W₁ ≤ N_G(U)` (`W1_normalizes_U`), hence it normalizes their intersection.  The `N_G(C)`-input to
the conjugation action of the (13.12) `c ≡ 1 (mod q)` step. -/
theorem Hypothesis.W1_le_normalizer_C (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.C : Set G) := by
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  intro w hw
  have hwP := hSP (hW1S hw)
  have hwU := hyp.W1_normalizes_U hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  rw [hyp.C_eq]
  simp only [Subgroup.mem_inf, SetLike.mem_coe]
  -- `w` normalizes `U` and `C_G(P)`; combine.
  have hU_iff : x ∈ hyp.U ↔ w * x * w⁻¹ ∈ hyp.U :=
    Subgroup.mem_set_normalizer_iff.mp hwU x
  have hCP_iff : x ∈ Subgroup.centralizer (hyp.P : Set G) ↔
      w * x * w⁻¹ ∈ Subgroup.centralizer (hyp.P : Set G) := by
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w⁻¹ * p * w ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff''.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * (w * x * w⁻¹) = w * ((w⁻¹ * p * w) * x) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * p * w)) * w⁻¹ := by rw [hcomm]
        _ = (w * x * w⁻¹) * p := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w * p * w⁻¹ ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * x = w⁻¹ * ((w * p * w⁻¹) * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * (w * p * w⁻¹)) * w := by rw [hcomm]
        _ = x * p := by group
  rw [hU_iff, hCP_iff]

/-- **Peterfalvi (13.12), structural step**: `c ≡ 1 (mod q)`.

The cyclic factor `W₁` (order `q`) acts fixed-point-freely on `C ⊆ U` by conjugation
(`W1_fpf_C`, `W1_le_normalizer_C`).  Since `W₁` is a `q`-group, the class equation
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|C| ≡ |C_C(W₁)| (mod q)`, and the fpf condition
makes `C_C(W₁) = {1}`.  This is the Coq `dv_2q_c1` ingredient (`q ∣ c − 1`) of
`FTtypeP_Ind_Fitting_reg_Fcore`. -/
theorem Hypothesis.c_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.c ≡ 1 [MOD hyp.q] := by
  classical
  haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hfpf := hyp.W1_fpf_C hG
  letI : MulAction ↥hyp.W1 ↥hyp.C :=
    MulAction.compHom ↥hyp.C (Subgroup.inclusion hyp.W1_le_normalizer_C)
  have hsmul : ∀ (w : ↥hyp.W1) (x : ↥hyp.C), ((w • x : ↥hyp.C) : G) = (w : G) * (x : G) * (w : G)⁻¹ :=
    fun _ _ => rfl
  have hW1pg : IsPGroup hyp.q ↥hyp.W1 := IsPGroup.of_card (by rw [← hyp.q_eq_card_W1, pow_one])
  have hmod : Nat.card ↥hyp.C ≡ Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) [MOD hyp.q] :=
    hW1pg.card_modEq_card_fixedPoints ↥hyp.C
  -- `W₁ ≠ ⊥`, pick `w₀ ∈ W₁ #`.
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro h; have h3 := hyp.three_le_q
    rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at h3; omega
  haveI : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨⟨w₀, hw₀W1⟩, hw₀ne⟩ := exists_ne (1 : ↥hyp.W1)
  have hw₀ne' : w₀ ≠ 1 := by rintro rfl; exact hw₀ne rfl
  -- `C_C(W₁) = {1}`.
  have hfixset : MulAction.fixedPoints ↥hyp.W1 ↥hyp.C = {1} := by
    ext a
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hafix
      by_contra hane
      have hav : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
      have hc := congrArg (Subtype.val) (hafix ⟨w₀, hw₀W1⟩)
      rw [hsmul] at hc
      exact hfpf w₀ hw₀W1 hw₀ne' (a : G) a.2 hav hc
    · rintro rfl w
      apply Subtype.ext
      rw [hsmul]; simp
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) = 1 := by
    rw [hfixset]; simp
  rw [hfix, ← hyp.c_eq_card_C] at hmod
  exact hmod

/-- **Peterfalvi (13.12), `dv_2q_c1`**: `2q ∣ c − 1`.  `c ≡ 1 (mod q)` (`c_modEq_one`) and `c` is
odd (`|C| ∣ |G|`, `|G|` odd), so both `q` and `2` divide `c − 1`; coprimality (`q` odd) gives
`2q ∣ c − 1`.  In the `c > 1` branch this forces `c ≥ 2q + 1`, the lower bound Peterfalvi's numeric
elimination contradicts. -/
theorem Hypothesis.two_mul_q_dvd_c_pred [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.q ∣ hyp.c - 1 := by
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hq : hyp.q ∣ hyp.c - 1 := (Nat.modEq_iff_dvd' hc1).mp (hyp.c_modEq_one hG).symm
  have hcodd : ¬ 2 ∣ hyp.c := by
    have hcG : hyp.c ∣ Nat.card G := by
      rw [hyp.c_eq_card_C]; exact Subgroup.card_subgroup_dvd_card _
    have hodd : Nat.card G % 2 = 1 := Nat.odd_iff.mp hG.odd
    intro h2c
    have h2G : (2 : ℕ) ∣ Nat.card G := h2c.trans hcG
    omega
  have h2 : 2 ∣ hyp.c - 1 := by omega
  have hcop : Nat.Coprime 2 hyp.q :=
    (Nat.coprime_primes Nat.prime_two hyp.q_prime).mpr (Ne.symm hyp.q_ne_two)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hq

/-- **Peterfalvi (13.11)**: the elementary numerical bounds for `m`.

The `q ≥ 7` and `q ≥ 5` bounds are the genuine arithmetic estimates
`m_value_gt_four_fifths` / `m_value_gt_seven_tenths` applied through the now
concrete value `m_eq` (they need only `p ≥ 3`, supplied by `three_le_p`).  The
`q = 3` value bound is available as `m_value_q_three_gt_49_hundredths` under
`p ≥ 5`, which Section 16 supplies from `q < p`; this bundled Section 15
statement still keeps the branch open because its `u/c` bound is the analytic
inequality (13.10). -/
theorem numeric_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  refine ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q, fun hq3 => ?_⟩
  · -- `q = 3`: the `m`-only API needs `p ≥ 5`, and the bundled `u/c` bound
    -- still needs the analytic inequality (13.10).
    sorry

/-- **Peterfalvi (13.12), numeric elimination** (04.15 p.85): the (13.10)+(13.2.c) upper bound
`m < q(p^q − 1)/(c · p^(q−1) · (p − 1))`, together with the fixed-point-free lower bound `c ≥ 2q+1`
(with `2q ∣ c − 1`) and the (13.11) lower bounds on `m`, forces `p = 5`, `q = 3`, `c = 7`.

This is the `sorry`-free `ℕ/ℚ`-arithmetic heart of (13.12): `q = 3` via
`caseB_numeric_forces_q_three`; the `q = 3` bound `m < 3(p³−1)/(c p²(p−1))` then eliminates `c ≥ 13`
(`< 49/100`, against (13.11.c)) forcing `c = 7`, eliminates `p ≥ 11` (`< 399/847 < 49/100`) forcing
`p < 11`, and eliminates `p = 7` (the exact value `m = ½ − 1/(2·3^{p−1}) = ½ − 1/1458` exceeds the
bound `171/343`) forcing `p = 5`.  Only the final `p = 5, q = 3, c = 7` structural contradiction
(`PC` normal nilpotent Hall ⊋ `P = S_F`) remains, isolated in `c_eq_one_final_case`. -/
theorem c_eq_one_forces_params {p q c : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc2q1 : 2 * q + 1 ≤ c) (h2q : 2 * q ∣ c - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hm49 : q = 3 → 5 ≤ p → (49 : ℚ) / 100 < m)
    (hmval : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hbound : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))) :
    p = 5 ∧ q = 3 ∧ c = 7 := by
  -- Basic positivity.
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
  have hc2q1R : (2 * (q : ℚ) + 1) ≤ (c : ℚ) := by
    have : ((2 * q + 1 : ℕ) : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc2q1
    push_cast at this; linarith
  -- Odd prime `≥ 3` is `3` or `≥ 5`.
  have prime_split : ∀ n : ℕ, n.Prime → 3 ≤ n → n = 3 ∨ 5 ≤ n := by
    intro n hn hn3
    by_contra hcon
    rw [not_or, not_le] at hcon
    obtain ⟨hne, hlt⟩ := hcon
    interval_cases n
    · exact hne rfl
    · exact (by norm_num : ¬ Nat.Prime 4) hn
  have hp35 : p = 3 ∨ 5 ≤ p := prime_split p hp hp3
  have hq35 : q = 3 ∨ 5 ≤ q := prime_split q hq hq3le
  -- `p^q = p^(q-1) · p`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: derive `m < q p / ((2q+1)(p-1))`, hence `q = 3`.
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hc2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hbound, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  -- With `q = 3`, `p ≥ 5`.
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
  subst hq3
  -- Specialize the bound to `q = 3`.
  have hbound3 : m < (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1)) := by
    have he : (p : ℚ) ^ (3 - 1) = (p : ℚ) ^ 2 := by norm_num
    have hc3 : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
    rw [he, hc3] at hbound
    exact hbound
  have hm49p : (49 : ℚ) / 100 < m := hm49 rfl hp5
  -- `c ≡ 1 mod 6`, `c ≥ 7`, so `c = 7 ∨ c ≥ 13`.
  have h6 : 6 ∣ c - 1 := by simpa using h2q
  have hc7or13 : c = 7 ∨ 13 ≤ c := by omega
  -- Kill `c ≥ 13`.
  have hc7 : c = 7 := by
    rcases hc7or13 with h | h
    · exact h
    exfalso
    have hcR13 : (13 : ℚ) ≤ (c : ℚ) := by exact_mod_cast h
    have hden : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb13 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hcR13, hpR5, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1,
        sq_nonneg ((p : ℚ) - 5)]
    linarith [hbound3, hb13, hm49p]
  subst hc7
  -- Kill `p ≥ 11`.
  have hp_lt_11 : p < 11 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR11 : (11 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have hden : (0 : ℚ) < (7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb11 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hpR11, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1]
    linarith [hbound3, hb11, hm49p]
  -- Kill `p = 7` via the exact value of `m`.
  have hp_ne_7 : p ≠ 7 := by
    intro h7
    subst h7
    rw [hmval] at hbound3
    norm_num at hbound3
  -- `5 ≤ p < 11`, prime, `≠ 7` ⇒ `p = 5`.
  refine ⟨?_, rfl, rfl⟩
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exact absurd rfl hp_ne_7
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

/-- **Peterfalvi (13.12), the isolated `PC`-Hall obligation**: for the numerically-forced
`p = 5, q = 3, c = 7`, the subgroup `PC = P ⊔ C` is contained in `M_F = maxNilpotentNormalHall S`.

Peterfalvi's argument: `PC` is **abelian** (hence nilpotent) — `P` is elementary abelian, `C ≤ U` is
abelian, and `C` centralizes `P` (`C_eq`); it is **normal** in `S` (type-`P` `W₁`-structure); and it
is a **Hall** subgroup once `gcd(c, u) = 1`, which holds because case (9.7.b) for `S` (as `p − 1 = 4`
has no odd divisor `≠ 1`) forces `u ∣ (p^q − 1)/(p − 1) = 31` (Singer / `typeP_Galois`), coprime to
`c = 7`.  By `le_maxNilpotentNormalHall` these three facts give `PC ≤ M_F`.  The `typeP_Galois`
dichotomy and the `W₁`-normality are the genuinely deep §13 σ-structure content (Coq
`FTtypeP_Ind_Fitting_reg_Fcore`: `typeP_Galois` + Fitting-core maximality `Fcore_max`), §14-gated /
multi-session — the sole remaining gap of (13.12). -/
theorem pc_le_maxNilpotentNormalHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) :
    hyp.P ⊔ hyp.C ≤ maxNilpotentNormalHall hyp.S :=
  sorry

/-- **Peterfalvi (13.12), structural residual**: the numerically-forced case `p = 5, q = 3, c = 7`
is impossible.  By `pc_le_maxNilpotentNormalHall`, `PC = P ⊔ C ≤ M_F = P` (`P_eq_SF`), so `C ≤ P`;
but `|C| = c = 7` cannot divide `|P| = p^q = 125`.  The genuine gap is isolated in
`pc_le_maxNilpotentNormalHall` (the `PC`-nilpotent-normal-Hall obligation, `typeP_Galois`-gated); the
`C ≤ P ⟹ 7 ∣ 125` maximality contradiction is discharged here. -/
theorem c_eq_one_final_case [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) : False := by
  -- `C ≤ P ⊔ C ≤ M_F = P`.
  have hCleP : hyp.C ≤ hyp.P := by
    have h := pc_le_maxNilpotentNormalHall hG hyp hp5 hq3 hc7
    rw [← hyp.P_eq_SF] at h
    exact le_trans le_sup_right h
  -- `|C| = 7`, `|P| = p^q = 125`.
  have hCcard : Nat.card ↥hyp.C = 7 := by rw [← hyp.c_eq_card_C, hc7]
  have hPcard : Nat.card ↥hyp.P = 5 ^ 3 := by
    obtain ⟨_, _, _, hcard, _, _⟩ := basic_structure hG hyp
    rw [hcard, hp5, hq3]
  -- `C ≤ P ⟹ |C| ∣ |P|`, i.e. `7 ∣ 125`, false.
  have hdvd : Nat.card ↥hyp.C ∣ Nat.card ↥hyp.P := by
    have hd := Subgroup.card_subgroup_dvd_card (hyp.C.subgroupOf hyp.P)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleP).toEquiv] at hd
  rw [hCcard, hPcard] at hdvd
  norm_num at hdvd

/-- **The analytic core of Peterfalvi (13.12)** (side-agnostic, pure `ℚ`-arithmetic).

From the `(13.10)` analytic inequality `u/c > m·a^(b−1)/b` and the `(13.2.c)` Singer *upper*
bound `u·(a−1) ≤ a^b − 1`, derive the upper bound `m < b·(a^b−1) / (c·a^(b−1)·(a−1))` that
(with the fixed-point-free lower bound `c ≥ 2b+1`) feeds the finite numeric elimination.

Both the `S`-side `c = 1` finish (`c_eq_one`, `a = p, b = q, u = u, c = c`) and the `T`-side
`d = 1` dual (`a = q, b = p, u = v, c = d`) instantiate this same core; extracted per issue
9013 (案A: generalize the §13 estimate so both sides `cite` it).  Uses only the Singer *upper*
bound, so it is ungated (the `T`-side lower-bound gate of the (13.15) `v`-value is a different
consumer — the ratio inequality — and does not enter here). -/
theorem analytic_singer_m_bound {a b u c : ℕ} {m : ℚ}
    (hbR : (0 : ℚ) < b) (hcR : (0 : ℚ) < c) (haR : (1 : ℚ) < a)
    (hanalytic : (u : ℚ) / c > m * (a : ℚ) ^ (b - 1) / b)
    (hsinger : (u : ℚ) * ((a : ℚ) - 1) ≤ (a : ℚ) ^ b - 1) :
    m < (b : ℚ) * ((a : ℚ) ^ b - 1)
      / ((c : ℚ) * (a : ℚ) ^ (b - 1) * ((a : ℚ) - 1)) := by
  have haR0 : (0 : ℚ) < (a : ℚ) := by linarith
  have hp1R : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  -- From (13.10): `m · a^(b-1) · c < u · b`.
  rw [gt_iff_lt, div_lt_div_iff₀ hbR hcR] at hanalytic
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hanalytic hp1R,
    mul_le_mul_of_nonneg_left hsinger (le_of_lt hbR)]

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`.

The numeric elimination `c_eq_one_forces_params` — fed the (13.10) analytic inequality
(`analytic_inequality`, `u/c > m p^(q-1)/q`), the (13.2.c) Singer bound (`basic_structure`,
`u ≤ (p^q-1)/(p-1)`), the fixed-point-free lower bound `c ≥ 2q+1` (`two_mul_q_dvd_c_pred`), and the
(13.11) `m`-bounds — forces `p = 5, q = 3, c = 7`, ruled out by the isolated structural residual
`c_eq_one_final_case`. -/
theorem c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.c = 1 := by
  by_contra hne
  -- `c > 1`; with `2q ∣ c − 1` (`two_mul_q_dvd_c_pred`) this forces `c ≥ 2q + 1`.
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hcgt : 1 < hyp.c := lt_of_le_of_ne hc1 (Ne.symm hne)
  have hc_ge : 2 * hyp.q + 1 ≤ hyp.c := by
    have h2q : 2 * hyp.q ≤ hyp.c - 1 := Nat.le_of_dvd (by omega) (hyp.two_mul_q_dvd_c_pred hG)
    omega
  -- (13.10) analytic inequality: `u/c > m · p^(q-1) / q`.
  obtain ⟨_, _, h1310⟩ := analytic_inequality hG hyp
  have hWcast : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  rw [hWcast] at h1310
  -- (13.2.c) Singer bound: `u ≤ (p^q - 1)/(p - 1)`, hence `u · (p-1) ≤ p^q - 1`.
  obtain ⟨_, _, _, _, hu_bound, _⟩ := basic_structure hG hyp
  have hp1nat : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hp0nat : 0 < hyp.p - 1 := by have := hyp.three_le_p; omega
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have huP : hyp.u * (hyp.p - 1) ≤ hyp.p ^ hyp.q - 1 :=
    (Nat.le_div_iff_mul_le hp0nat).mp hu_bound
  have huPR : (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) ≤ (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) ≤ ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) := by
      exact_mod_cast huP
    have e1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) = (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) := by
      push_cast [Nat.cast_sub hp1nat]; ring
    have e2 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) = (hyp.p : ℚ) ^ hyp.q - 1 := by
      push_cast [Nat.cast_sub hpq1]; ring
    rw [e1, e2] at h1; exact h1
  -- Positivity, then the side-agnostic analytic core (`analytic_singer_m_bound`) assembles the
  -- abstract bound `m < q(p^q-1)/(c p^(q-1)(p-1))` from (13.10) + the Singer bound.
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hcRpos : (0 : ℚ) < (hyp.c : ℚ) := by exact_mod_cast (show 0 < hyp.c by omega)
  have haR : (1 : ℚ) < (hyp.p : ℚ) := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.three_le_p
    linarith
  have hbound := analytic_singer_m_bound hqR hcRpos haR h1310 huPR
  -- Numeric elimination forces `p = 5, q = 3, c = 7`.
  obtain ⟨hp5, hq3, hc7⟩ := c_eq_one_forces_params hyp.p_prime hyp.q_prime hyp.three_le_p
    hyp.q_ne_two hyp.p_ne_q hc_ge (hyp.two_mul_q_dvd_c_pred hG)
    (fun h => hyp.m_gt_seven_tenths_of_five_le_q h)
    (fun h => hyp.m_gt_four_fifths_of_seven_le_q h)
    (fun hq hp => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq hp)
    hyp.m_eq hbound
  exact c_eq_one_final_case hG hyp hp5 hq3 hc7

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`. -/
theorem caseA_parameters [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseA_for_S : Prop) :
    caseA_for_S → hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  sorry

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

/-- The coprimality part of **Peterfalvi (13.14)** when `p` is not `1 mod q`. -/
theorem cyclotomic_quotient_coprime_of_not_modEq_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpmod : p ≡ 1 [MOD p - 1] := Nat.modEq_sub (le_of_lt hp.one_lt)
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD p - 1] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpmod
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  have hmod : (∑ k ∈ Finset.range q, p ^ k) ≡ q [MOD p - 1] := by
    exact hterms.trans (by rw [hsum_one])
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp <|
    hq.coprime_iff_not_dvd.mpr fun hdiv => hpq <| by
      exact ((Nat.modEq_iff_dvd'
        (show 1 ≤ p from le_of_lt hp.one_lt)).mpr hdiv).symm

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  haveI : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_pow_primeFactors_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

/-- **Peterfalvi (13.14)**: divisibility facts for
`(p^q - 1) / (p - 1)`. -/
theorem cyclotomic_divisor_facts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) ∧
      (p ≡ 1 [MOD q] → q ∣ (p ^ q - 1) / (p - 1)) ∧
      (¬ (p ≡ 1 [MOD q]) →
        Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ∧
          ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q]) := by
  refine ⟨cyclotomic_quotient_odd hp hpodd hqodd, ?_, ?_⟩
  · exact cyclotomic_quotient_dvd_of_modEq_one hp
  · intro hpq
    exact ⟨cyclotomic_quotient_coprime_of_not_modEq_one hp hq hpq,
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hpq⟩

/-- **Peterfalvi (13.15)**: in case (9.7.b), `u` has the final cyclotomic
value, depending on whether `p` is `1 mod q`. -/
theorem caseB_order_u [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) :
    caseB_for_S →
      ((p_mod : hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
        (¬ (hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  sorry

/-- Carrier for the `u`-order conclusion in **Peterfalvi (13.15)** under
case (9.7.b).  It packages the two congruence branches so Section 16 can carry
the order data together with the case-(b) certificate. -/
structure CaseBOrderUData (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) where
  caseB_holds : caseB_for_S
  u_eq_of_p_modEq_one :
    hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))
  u_eq_of_not_modEq_one :
    ¬ hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)

/-- Data form of **Peterfalvi (13.15)**, derived from `caseB_order_u`. -/
theorem caseB_order_u_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {caseB_for_S : Prop} (hcase : caseB_for_S) :
    CaseBOrderUData hyp caseB_for_S := by
  rcases caseB_order_u hG hyp caseB_for_S hcase with ⟨hmod, hnot⟩
  exact
    { caseB_holds := hcase
      u_eq_of_p_modEq_one := hmod
      u_eq_of_not_modEq_one := hnot }


end OddOrder.Peterfalvi.S15

