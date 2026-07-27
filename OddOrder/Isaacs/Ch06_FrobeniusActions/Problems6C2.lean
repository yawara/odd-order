/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6C1
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# Isaacs Problem 6C.2(a) — 位数 `p²` の elementary abelian 作用と `p + 1` 個の冪零部分群
(書籍 p. 197)

**主張 (a)**: `A` が位数 `p²` の elementary abelian 群で, 非冪零群 `N` に自己同型として作用し
`C_N(A) = 1` とする。このとき `N` は `1 < K_i` (`1 ≤ i ≤ p + 1`) なる冪零部分群を持ち,
`i ≠ j` なら `K_i ⊓ K_j = 1`。

**証明**: `A` の位数 `p` の部分群は `p + 1` 個ある (`x`, `y` を基底にとり
`⟨x y^k⟩` (`0 ≤ k < p`) と `⟨y⟩`)。`K_i := C_N(A_i)` と置くと,

* `K_i ≠ 1`: さもなくば `A_i` (位数 `p`) の作用が Frobenius になり Thompson
  (`isNilpotent_of_isFrobeniusAction`) で `N` が冪零になってしまう。
* `K_i` は冪零: `j ≠ i` を取ると `A_j` は `K_i` に作用し, その固定点は
  `C_N(A_i ⊔ A_j) = C_N(A) = 1` なので Frobenius。再び Thompson。
* `K_i ⊓ K_j = 1`: 共通の元は `A_i ⊔ A_j = A` に固定されるので `C_N(A) = 1` より単位元。

`A_i ⊔ A_j = A` (`i ≠ j`) は「位数 `p` の相異なる部分群の交わりは自明, 位数 `p²` の群で
指数を数える」ことから。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6C.2(a): `p + 1` 個の冪零部分群 (p. 197) -/

/-! ### 位数 `p` の部分群の族 (elementary abelian `p²`) -/

/-- 可換な 2 元の指数比較: `x^a y^b = x^c y^d` なら `x^(a-c) y^(b-d) = 1`。 -/
theorem zpow_mul_zpow_eq_one_of_eq {A : Type*} [Group A] (hcomm : ∀ u v : A, u * v = v * u)
    {x y : A} {a b c d : ℤ} (h : x ^ a * y ^ b = x ^ c * y ^ d) :
    x ^ (a - c) * y ^ (b - d) = 1 := by
  have hmove : (x ^ c)⁻¹ * (y ^ b * (y ^ d)⁻¹) = (y ^ b * (y ^ d)⁻¹) * (x ^ c)⁻¹ := hcomm _ _
  have key : x ^ (a - c) * y ^ (b - d) = (x ^ a * y ^ b) * (x ^ c * y ^ d)⁻¹ := by
    have e1 : x ^ (a - c) * y ^ (b - d) = x ^ a * ((x ^ c)⁻¹ * (y ^ b * (y ^ d)⁻¹)) := by
      rw [zpow_sub, zpow_sub]; group
    rw [e1, hmove]
    group
  rw [key, h, mul_inv_cancel]

/-- elementary abelian `p²` 群の `x, y` (`y ∉ ⟨x⟩`) に関する表示の一意性 (指数版)。 -/
theorem eq_zero_of_zpow_mul_zpow_eq_one {A : Type*} [Group A] [Finite A] {p : ℕ} {x y : A}
    (hx : orderOf x = p) (hy : orderOf y = p) (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {a b : ℤ} (h : x ^ a * y ^ b = 1) : ((p : ℤ) ∣ a) ∧ ((p : ℤ) ∣ b) := by
  have hmem : x ^ a ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
    refine ⟨Subgroup.mem_zpowers_iff.mpr ⟨a, rfl⟩, Subgroup.mem_zpowers_iff.mpr ⟨-b, ?_⟩⟩
    rw [zpow_neg]
    exact inv_eq_of_mul_eq_one_left h
  rw [hinf, Subgroup.mem_bot] at hmem
  have hb : y ^ b = 1 := by
    rw [hmem, one_mul] at h
    exact h
  constructor
  · have := orderOf_dvd_iff_zpow_eq_one.mpr hmem
    rwa [hx] at this
  · have := orderOf_dvd_iff_zpow_eq_one.mpr hb
    rwa [hy] at this

/-- **位数 `p` の部分群 `p + 1` 個**: elementary abelian `p²` 群には位数 `p` の部分群が
`p + 1` 個あり, 相異なる 2 つは全体を生成する。 -/
theorem exists_family_subgroups_card_prime {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hA : ∀ u : A, u ^ p = 1) (hcomm : ∀ u v : A, u * v = v * u)
    (hcard : Nat.card A = p ^ 2) :
    ∃ B : Fin (p + 1) → Subgroup A, (∀ i, Nat.card ↥(B i) = p) ∧
      (∀ i j, i ≠ j → B i ⊔ B j = ⊤) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- 位数 `p` の元 `x`, および `⟨x⟩` の外の元 `y`
  have horder : ∀ u : A, u ≠ 1 → orderOf u = p := by
    intro u hu
    have hdvd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one (hA u)
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
    · exact absurd (orderOf_eq_one_iff.mp h1) hu
    · exact hpp
  obtain ⟨x, hx1⟩ : ∃ x : A, x ≠ 1 := by
    have h1 : 1 < Nat.card A := by
      rw [hcard]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    obtain ⟨u, v, huv⟩ := Finite.one_lt_card_iff_nontrivial.mp h1
    rcases eq_or_ne u 1 with rfl | hu
    · exact ⟨v, fun h => huv h.symm⟩
    · exact ⟨u, hu⟩
  have hxord : orderOf x = p := horder x hx1
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  obtain ⟨y, hy⟩ : ∃ y : A, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    have htop : Subgroup.zpowers x = ⊤ :=
      eq_top_iff.mpr fun u _ => not_not.mp fun h => hcon ⟨u, h⟩
    rw [htop, Subgroup.card_top, hcard] at hxcard
    rw [pow_two] at hxcard
    have h1 := hp.one_lt
    nlinarith
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := horder y hy1
  -- `⟨x⟩ ⊓ ⟨y⟩ = ⊥`
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    by_contra hzne
    have hzne1 : z ≠ 1 := fun h => hzne (by rw [h]; exact Subgroup.mem_bot.mpr rfl)
    have hzx : Subgroup.zpowers z = Subgroup.zpowers x :=
      Subgroup.zpowers_eq_of_prime_card (by rw [hxcard]; exact hp) hz.1 hzne1
    have hzy : Subgroup.zpowers z = Subgroup.zpowers y :=
      Subgroup.zpowers_eq_of_prime_card (by rw [Nat.card_zpowers, hyord]; exact hp) hz.2 hzne1
    exact hy (hzx ▸ hzy ▸ Subgroup.mem_zpowers y)
  -- 相異なる位数 `p` の部分群は全体を生成する
  have hsup : ∀ B C : Subgroup A, Nat.card ↥B = p → Nat.card ↥C = p → B ≠ C → B ⊔ C = ⊤ := by
    intro B C hB hC hBC
    have hBle : B ≤ B ⊔ C := le_sup_left
    have hCle : C ≤ B ⊔ C := le_sup_right
    have hdvd : Nat.card ↥(B ⊔ C) ∣ p ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hpdvd : p ∣ Nat.card ↥(B ⊔ C) := by
      rw [← hB]
      exact Subgroup.card_dvd_of_le hBle
    have hne : Nat.card ↥(B ⊔ C) ≠ p := by
      intro heq
      refine hBC ?_
      have h1 : B = B ⊔ C := Subgroup.eq_of_le_of_card_ge hBle (by rw [heq, hB])
      have h2 : C = B ⊔ C := Subgroup.eq_of_le_of_card_ge hCle (by rw [heq, hC])
      exact h1.trans h2.symm
    obtain ⟨i, hi, hpow⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hi2 : i = 2 := by
      rcases Nat.lt_or_ge i 2 with hlt | hge
      · interval_cases i
        · rw [hpow] at hpdvd
          simp only [pow_zero] at hpdvd
          exact absurd (Nat.dvd_one.mp hpdvd) hp.ne_one
        · exact absurd (by rw [hpow, pow_one]) hne
      · omega
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hpow, hi2, hcard]
  -- 族の構成: `i < p` では `⟨x y^i⟩`, `i = p` では `⟨y⟩`
  refine ⟨fun i => if (i : ℕ) < p then Subgroup.zpowers (x * y ^ (i : ℕ))
    else Subgroup.zpowers y, ?_, ?_⟩
  · intro i
    by_cases hlt : (i : ℕ) < p
    · simp only [hlt, if_true]
      rw [Nat.card_zpowers]
      refine horder _ ?_
      intro hone
      have := (eq_zero_of_zpow_mul_zpow_eq_one hxord hyord hinf
        (a := 1) (b := ((i : ℕ) : ℤ)) (by rw [zpow_one, zpow_natCast]; exact hone)).1
      exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast this))
    · simp only [hlt, if_false]
      rw [Nat.card_zpowers, hyord]
  · intro i j hij
    have hcardi : ∀ k : Fin (p + 1), Nat.card ↥(if (k : ℕ) < p
        then Subgroup.zpowers (x * y ^ (k : ℕ)) else Subgroup.zpowers y) = p := by
      intro k
      by_cases hlt : (k : ℕ) < p
      · simp only [hlt, if_true]
        rw [Nat.card_zpowers]
        refine horder _ ?_
        intro hone
        have := (eq_zero_of_zpow_mul_zpow_eq_one hxord hyord hinf
          (a := 1) (b := (k : ℕ)) (by rw [zpow_one, zpow_natCast]; exact hone)).1
        exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast this))
      · simp only [hlt, if_false]
        rw [Nat.card_zpowers, hyord]
    refine hsup _ _ (hcardi i) (hcardi j) ?_
    -- 相異性
    by_cases hi : (i : ℕ) < p
    · by_cases hj : (j : ℕ) < p
      · simp only [hi, hj, if_true]
        intro heq
        -- `x y^j ∈ ⟨x y^i⟩` から `j ≡ i (mod p)`
        have hmem : x * y ^ (j : ℕ) ∈ Subgroup.zpowers (x * y ^ (i : ℕ)) := by
          rw [heq]; exact Subgroup.mem_zpowers _
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hexp : x ^ m * y ^ (((i : ℕ) : ℤ) * m) = x ^ (1 : ℤ) * y ^ (((j : ℕ) : ℤ)) := by
          rw [zpow_one, zpow_natCast, ← hm,
            Commute.mul_zpow (hcomm x (y ^ (i : ℕ))), ← zpow_natCast y (i : ℕ), ← zpow_mul]
        obtain ⟨hd1, hd2⟩ := eq_zero_of_zpow_mul_zpow_eq_one hxord hyord hinf
          (zpow_mul_zpow_eq_one_of_eq hcomm hexp)
        -- `p ∣ m - 1` と `p ∣ i*m - j` から `p ∣ i - j`
        have hdij : (p : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by
          have hmul : (p : ℤ) ∣ ((i : ℕ) : ℤ) * (m - 1) := Dvd.dvd.mul_left hd1 _
          have hrw : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)
              = (((i : ℕ) : ℤ) * m - ((j : ℕ) : ℤ)) - ((i : ℕ) : ℤ) * (m - 1) := by ring
          rw [hrw]
          exact dvd_sub hd2 hmul
        have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        have hb1 : ((i : ℕ) : ℤ) < p := by exact_mod_cast hi
        have hb2 : ((j : ℕ) : ℤ) < p := by exact_mod_cast hj
        have hn1 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := Int.natCast_nonneg _
        have hn2 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
        obtain ⟨t, ht⟩ := hdij
        have hzero : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
          rcases lt_trichotomy t 0 with hlt | hz | hgt
          · exfalso
            have hple : (p : ℤ) * t ≤ (p : ℤ) * (-1) :=
              mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp0)
            rw [← ht] at hple
            linarith
          · rw [hz, mul_zero] at ht; linarith
          · exfalso
            have hpge : (p : ℤ) * 1 ≤ (p : ℤ) * t :=
              mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp0)
            rw [← ht] at hpge
            linarith
        exact hij (Fin.ext (by exact_mod_cast hzero))
      · simp only [hi, hj, if_true, if_false]
        intro heq
        -- `x y^i ∈ ⟨y⟩` は `p ∣ 1` を導く
        have hmem : x * y ^ (i : ℕ) ∈ Subgroup.zpowers y := by
          rw [← heq]; exact Subgroup.mem_zpowers _
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have heq2 : x ^ (1 : ℤ) * y ^ (((i : ℕ) : ℤ)) = x ^ (0 : ℤ) * y ^ m := by
          rw [zpow_one, zpow_natCast, zpow_zero, one_mul]
          exact hm.symm
        have hd := (eq_zero_of_zpow_mul_zpow_eq_one hxord hyord hinf
          (zpow_mul_zpow_eq_one_of_eq hcomm heq2)).1
        rw [sub_zero] at hd
        exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast hd))
    · -- `i = p` なので `j < p`
      have hip : (i : ℕ) = p := by
        have := i.isLt
        omega
      have hj : (j : ℕ) < p := by
        have hjlt := j.isLt
        by_contra hjc
        exact hij (Fin.ext (by omega))
      simp only [hi, hj, if_true, if_false]
      intro heq
      have hmem : x * y ^ (j : ℕ) ∈ Subgroup.zpowers y := by
        rw [heq]; exact Subgroup.mem_zpowers _
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have heq2 : x ^ (1 : ℤ) * y ^ (((j : ℕ) : ℤ)) = x ^ (0 : ℤ) * y ^ m := by
        rw [zpow_one, zpow_natCast, zpow_zero, one_mul]
        exact hm.symm
      have hd := (eq_zero_of_zpow_mul_zpow_eq_one hxord hyord hinf
        (zpow_mul_zpow_eq_one_of_eq hcomm heq2)).1
      rw [sub_zero] at hd
      exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast hd))

/-! ### `C_N(B)` と 6C.2(a) 本体 -/

/-- 作用側の部分群 `B` に固定される元全体 `C_N(B)`。 -/
def fixedSubgroup {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (B : Subgroup A) : Subgroup N where
  carrier := {n : N | ∀ b ∈ B, b • n = n}
  mul_mem' := by
    intro u v hu hv b hb
    rw [smul_mul', hu b hb, hv b hb]
  one_mem' := by
    intro b _
    exact smul_one b
  inv_mem' := by
    intro u hu b hb
    rw [smul_inv', hu b hb]

theorem mem_fixedSubgroup_iff {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    {B : Subgroup A} {n : N} :
    n ∈ (fixedSubgroup B : Subgroup N) ↔ ∀ b ∈ B, b • n = n := Iff.rfl

/-- 位数が素数の部分群 `B` では「非自明元 1 つが固定する」= 「`B` 全体が固定する」。 -/
theorem mem_fixedSubgroup_of_smul_eq {A N : Type*} [Group A] [Finite A] [Group N]
    [MulDistribMulAction A N] {B : Subgroup A} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥B = p) {b : A} (hbB : b ∈ B) (hb1 : b ≠ 1) {n : N} (h : b • n = n) :
    n ∈ (fixedSubgroup B : Subgroup N) := by
  intro c hc
  have hgen : Subgroup.zpowers b = B :=
    Subgroup.zpowers_eq_of_prime_card (by rw [hcard]; exact hp) hbB hb1
  have hcz : c ∈ Subgroup.zpowers b := by rw [hgen]; exact hc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcz
  rw [← hm]
  exact zpow_mem (show b ∈ MulAction.stabilizer A n from h) m

/-- **Isaacs Problem 6C.2(a)** (p. 197) ⭐: 位数 `p²` の elementary abelian 群 `A` が
非冪零な有限群 `N` に自己同型として作用し `C_N(A) = 1` なら, `N` には非自明な冪零部分群が
`p + 1` 個あり, どの 2 つの交わりも自明。

`K_i := C_N(A_i)` (`A_i` は `A` の位数 `p` の部分群) と置く。 -/
theorem exists_family_nilpotent_subgroups_of_card_prime_sq
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    {p : ℕ} (hp : p.Prime) (hA : ∀ u : A, u ^ p = 1) (hcomm : ∀ u v : A, u * v = v * u)
    (hcard : Nat.card A = p ^ 2) (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1)
    (hN : ¬ Group.IsNilpotent N) :
    ∃ K : Fin (p + 1) → Subgroup N, (∀ i, K i ≠ ⊥) ∧ (∀ i, Group.IsNilpotent ↥(K i)) ∧
      (∀ i j, i ≠ j → K i ⊓ K j = ⊥) := by
  classical
  obtain ⟨B, hBcard, hBsup⟩ := exists_family_subgroups_card_prime hp hA hcomm hcard
  haveI hBnt : ∀ i, Nontrivial ↥(B i) := by
    intro i
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hBcard i]
    exact hp.one_lt
  -- `B i` と `B j` (`i ≠ j`) に固定される元は `A` 全体に固定される
  have hfix_two : ∀ i j : Fin (p + 1), i ≠ j → ∀ n : N,
      n ∈ (fixedSubgroup (B i) : Subgroup N) → n ∈ (fixedSubgroup (B j) : Subgroup N) → n = 1 := by
    intro i j hij n hni hnj
    refine hfixA n fun a => ?_
    have hle : B i ⊔ B j ≤ MulAction.stabilizer A n :=
      sup_le (fun b hb => hni b hb) (fun b hb => hnj b hb)
    rw [hBsup i j hij] at hle
    exact hle (Subgroup.mem_top a)
  -- `K i` は `A`-不変
  have hinv : ∀ i : Fin (p + 1), ∀ a : A, ∀ m ∈ (fixedSubgroup (B i) : Subgroup N),
      a • m ∈ (fixedSubgroup (B i) : Subgroup N) := by
    intro i a m hm b hb
    rw [← mul_smul, hcomm b a, mul_smul, hm b hb]
  refine ⟨fun i => fixedSubgroup (B i), ?_, ?_, ?_⟩
  · -- 非自明性: さもなくば `B i` の作用が Frobenius で `N` が冪零になる
    intro i hbot
    have hbot' : (fixedSubgroup (B i) : Subgroup N) = ⊥ := hbot
    refine hN ?_
    have hFrob : IsFrobeniusAction ↥(B i) N := by
      intro b hb n hn hsmul
      refine hn ?_
      have hb1 : (b : A) ≠ 1 := fun h => hb (Subtype.ext h)
      have hmem := mem_fixedSubgroup_of_smul_eq hp (hBcard i) b.2 hb1
        (n := n) ((Subgroup.smul_def b n).symm.trans hsmul)
      rw [hbot', Subgroup.mem_bot] at hmem
      exact hmem
    exact isNilpotent_of_isFrobeniusAction hFrob
  · -- 冪零性: `j ≠ i` を取ると `B j` は `K i` に Frobenius に作用する
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin (p + 1), i ≠ j := by
      have hp1 := hp.one_lt
      rcases eq_or_ne i ⟨0, by omega⟩ with rfl | hne
      · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, hne⟩
    letI actKi : MulDistribMulAction A ↥(fixedSubgroup (B i) : Subgroup N) :=
      IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ (hinv i)
    have hFrob : IsFrobeniusAction ↥(B j) ↥(fixedSubgroup (B i) : Subgroup N) := by
      intro b hb m hm hsmul
      refine hm ?_
      have hb1 : (b : A) ≠ 1 := fun h => hb (Subtype.ext h)
      have hsmulN : (b : A) • ((m : N)) = (m : N) := by
        have := (Subgroup.smul_def b m).symm.trans hsmul
        exact congrArg (fun w : ↥(fixedSubgroup (B i) : Subgroup N) => (w : N)) this
      have hmj := mem_fixedSubgroup_of_smul_eq hp (hBcard j) b.2 hb1 hsmulN
      exact Subtype.ext (hfix_two i j hij (m : N) m.2 hmj)
    exact isNilpotent_of_isFrobeniusAction hFrob
  · -- 交わりの自明性
    intro i j hij
    rw [eq_bot_iff]
    intro n hn
    exact Subgroup.mem_bot.mpr (hfix_two i j hij n hn.1 hn.2)

/-! ### (b) の準備: 固定点自由な `p`-群作用は位数を互いに素にする -/

open Pointwise in
/-- **`p`-群が固定点自由に作用すれば `p ∤ |N|`**: `p`-群 `A` が `N` に作用して
`C_N(A) = 1` なら `p` は `|N|` を割らない。

`p ∣ |N|` とすると `|Syl_p(N)| ≡ 1 (mod p)` と `A` が `p`-群であることから `A`-不変な
Sylow `p`-部分群 `P` が取れる。`A` の `P` への作用の固定点の個数は `|P| ≡ 0 (mod p)` に
合同なので `p` 個以上あり, 単位元以外の固定点が存在してしまう。 -/
theorem not_dvd_card_of_fixedFree_of_isPGroup {A N : Type*} [Group A] [Finite A] [Group N]
    [Finite N] [MulDistribMulAction A N] {p : ℕ} (hp : p.Prime) (hA : IsPGroup p A)
    (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1) : ¬ p ∣ Nat.card N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  -- `A`-不変 Sylow `p`-部分群を取る
  obtain ⟨P, hPfix⟩ : ∃ P : Sylow p N, ∀ a : A, a • P = P := by
    have h1 : Nat.card (Sylow p N) ≡ 1 [MOD p] := card_sylow_modEq_one p N
    have h2 : Nat.card (Sylow p N) ≡ Nat.card (MulAction.fixedPoints A (Sylow p N)) [MOD p] :=
      hA.card_modEq_card_fixedPoints (Sylow p N)
    have h3 : Nat.card (MulAction.fixedPoints A (Sylow p N)) ≡ 1 [MOD p] := h2.symm.trans h1
    have hne : Nat.card (MulAction.fixedPoints A (Sylow p N)) ≠ 0 := by
      intro h0
      rw [h0] at h3
      have hd : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp h3
      exact hp.ne_one (Nat.dvd_one.mp hd)
    obtain ⟨⟨Q, hQ⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
    exact ⟨Q, fun a => hQ a⟩
  -- 部分群としての `A`-不変性
  have hPinv : ∀ a : A, ∀ m ∈ (P : Subgroup N), a • m ∈ (P : Subgroup N) := by
    intro a m hm
    have hs : a • ((P : Sylow p N) : Subgroup N) = ((P : Sylow p N) : Subgroup N) := by
      have h := congrArg (fun S : Sylow p N => (S : Subgroup N)) (hPfix a)
      rwa [Sylow.pointwise_smul_def] at h
    rw [← hs]
    exact Subgroup.smul_mem_pointwise_smul m a _ hm
  -- `P` は非自明な `p`-群
  have hPbot : (P : Subgroup N) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  haveI hPnt : Nontrivial ↥(P : Subgroup N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPbot
  have hPcard : p ∣ Nat.card ↥(P : Subgroup N) := by
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [pow_zero] at hk
      exact absurd hk (Finite.one_lt_card_iff_nontrivial.mpr hPnt).ne'
    · rw [hk]
      exact dvd_pow_self p (by omega)
  -- `A` の `↥P` への作用 (不変部分群への制限)
  letI actP : MulDistribMulAction A ↥(P : Subgroup N) :=
    IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hPinv
  have hmod : Nat.card ↥(P : Subgroup N)
      ≡ Nat.card (MulAction.fixedPoints A ↥(P : Subgroup N)) [MOD p] :=
    hA.card_modEq_card_fixedPoints _
  have hfp : p ∣ Nat.card (MulAction.fixedPoints A ↥(P : Subgroup N)) :=
    (Nat.modEq_zero_iff_dvd.mp ((Nat.modEq_zero_iff_dvd.mpr hPcard).symm.trans hmod).symm)
  -- 単位元は固定点なので個数は正, `p ∣` なので `2` 以上
  have hone : (1 : ↥(P : Subgroup N)) ∈ MulAction.fixedPoints A ↥(P : Subgroup N) :=
    fun a => smul_one a
  have hpos : 0 < Nat.card (MulAction.fixedPoints A ↥(P : Subgroup N)) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hge : 2 ≤ Nat.card (MulAction.fixedPoints A ↥(P : Subgroup N)) := by
    obtain ⟨t, ht⟩ := hfp
    have h2 := hp.two_le
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [mul_zero] at ht
      omega
    · exact le_trans h2 (by rw [ht]; exact Nat.le_mul_of_pos_right p htpos)
  haveI : Nontrivial ↥(MulAction.fixedPoints A ↥(P : Subgroup N)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, v, huv⟩ := ‹Nontrivial ↥(MulAction.fixedPoints A ↥(P : Subgroup N))›
  -- `u`, `v` のどちらかは単位元でない
  obtain ⟨m, hmfix, hmne⟩ : ∃ m : ↥(P : Subgroup N),
      (∀ a : A, a • m = m) ∧ m ≠ 1 := by
    rcases eq_or_ne (u : ↥(P : Subgroup N)) 1 with hu | hu
    · refine ⟨(v : ↥(P : Subgroup N)), fun a => v.2 a, ?_⟩
      intro hv
      exact huv (Subtype.ext (by rw [hu, hv]))
    · exact ⟨(u : ↥(P : Subgroup N)), fun a => u.2 a, hu⟩
  refine hmne (Subtype.ext (hfixA ((m : ↥(P : Subgroup N)) : N) fun a => ?_))
  exact congrArg (fun w : ↥(P : Subgroup N) => (w : N)) (hmfix a)

/-- **冪零部分群の最大 `q`-部分群**: `K ≤ N` の `↥K` が冪零なら, `K` の `q`-部分群を
すべて含む `q`-部分群 `Q ≤ K` がある (= `K` の唯一の Sylow `q`-部分群)。

冪零 ⟹ `NormalizerCondition` ⟹ Sylow は正規 ⟹ Sylow は一意 (`Sylow.unique_of_normal`)。 -/
theorem exists_max_qSubgroup_le_of_isNilpotent {N : Type*} [Group N] [Finite N]
    {K : Subgroup N} (hK : Group.IsNilpotent ↥K) {q : ℕ} (hq : q.Prime) :
    ∃ Q : Subgroup N, Q ≤ K ∧ IsPGroup q ↥Q ∧
      ∀ R : Subgroup N, R ≤ K → IsPGroup q ↥R → R ≤ Q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hK
  obtain ⟨S⟩ : Nonempty (Sylow q ↥K) := inferInstance
  have hSnormal : ((S : Subgroup ↥K)).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent S
  haveI hU : Unique (Sylow q ↥K) := Sylow.unique_of_normal S hSnormal
  refine ⟨(S : Subgroup ↥K).map K.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨u, _, rfl⟩
    exact u.2
  · exact S.2.map _
  · intro R hRK hRq
    have hRsub : IsPGroup q ↥(R.comap K.subtype) :=
      hRq.comap_of_injective K.subtype (Subgroup.subtype_injective K)
    obtain ⟨T, hT⟩ := hRsub.exists_le_sylow
    have hTS : T = S := Subsingleton.elim _ _
    intro x hx
    have hxK : x ∈ K := hRK hx
    have hmem : (⟨x, hxK⟩ : ↥K) ∈ R.comap K.subtype := hx
    exact ⟨⟨x, hxK⟩, hTS ▸ hT hmem, rfl⟩

open Pointwise in
/-- **最大 `q`-部分群は `A`-不変**: `K` が `A`-不変なら, `K` の最大 `q`-部分群 `Q` も
`A`-不変 (`a • Q` も `K` の `q`-部分群なので最大性から `a • Q ≤ Q`)。 -/
theorem smul_mem_of_max_qSubgroup {A N : Type*} [Group A] [Group N] [Finite N]
    [MulDistribMulAction A N] {K Q : Subgroup N} {q : ℕ}
    (hKinv : ∀ a : A, ∀ m ∈ K, a • m ∈ K) (hQK : Q ≤ K) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ R : Subgroup N, R ≤ K → IsPGroup q ↥R → R ≤ Q) :
    ∀ a : A, ∀ m ∈ Q, a • m ∈ Q := by
  intro a m hm
  have hsmul_le : a • Q ≤ K := by
    intro x hx
    rw [Subgroup.pointwise_smul_def] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hKinv a y (hQK hy)
  have hsmul_q : IsPGroup q ↥(a • Q) := by
    rw [Subgroup.pointwise_smul_def]
    exact hQq.map _
  exact hQmax _ hsmul_le hsmul_q (Subgroup.smul_mem_pointwise_smul m a Q hm)

/-! ### `MulDistribMulAction` と Ch.3/Ch.4 の `IsAInvariant` の橋渡し -/

open Pointwise in
/-- 元ごとの不変性から `IsAInvariant` (Ch.3/Ch.4 の A-不変性) へ。 -/
theorem isAInvariant_of_smul_mem {A N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] {H : Subgroup N} (h : ∀ a : A, ∀ m ∈ H, a • m ∈ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant (MulDistribMulAction.toMulAut A N) H := by
  have hle : ∀ b : A, (MulDistribMulAction.toMulAut A N b : MulAut N) • H ≤ H := by
    intro b x hx
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h b y hy
  intro a
  refine le_antisymm (hle a) fun x hx => ?_
  rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
  refine ⟨a⁻¹ • x, h a⁻¹ x hx, ?_⟩
  change a • (a⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel, one_smul]

open Pointwise in
/-- `IsAInvariant` から元ごとの不変性へ。 -/
theorem smul_mem_of_isAInvariant {A N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] {H : Subgroup N}
    (h : OddOrder.Isaacs.Ch03.IsAInvariant (MulDistribMulAction.toMulAut A N) H) :
    ∀ a : A, ∀ m ∈ H, a • m ∈ H := by
  intro a m hm
  have hEq := h a
  rw [← hEq, Subgroup.pointwise_smul_def, Subgroup.mem_map]
  exact ⟨m, hm, rfl⟩

/-! ### `A`-不変 Sylow `q`-部分群の一意性 -/

/-- **`C_N(A) = 1` なら `A`-不変 Sylow `q`-部分群は一意**: Isaacs Thm 3.23(b) の共役元は
`C_N(A)` に入るので自明。 -/
theorem aInvariant_sylow_unique {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    [MulDistribMulAction A N] [IsSolvable A] {q : ℕ} [Fact q.Prime]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1) {S T : Sylow q N}
    (hS : ∀ a : A, ∀ m ∈ (S : Subgroup N), a • m ∈ (S : Subgroup N))
    (hT : ∀ a : A, ∀ m ∈ (T : Subgroup N), a • m ∈ (T : Subgroup N)) :
    (S : Subgroup N) = (T : Subgroup N) := by
  obtain ⟨c, hcfix, hconj⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_sylow_conj hCop (Or.inl ‹IsSolvable A›)
      (isAInvariant_of_smul_mem hS) (isAInvariant_of_smul_mem hT)
  have hc1 : c = 1 := hfixA c fun a => hcfix a
  rw [hc1] at hconj
  simpa using hconj

/-- **`A`-不変 `q`-部分群は (唯一の) `A`-不変 Sylow `q`-部分群に含まれる**:
Cor 3.25 で `A`-不変 Sylow に入れ, 一意性で目的の `S` に一致させる。 -/
theorem le_sylow_of_aInvariant_qSubgroup {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    [MulDistribMulAction A N] [IsSolvable A] {q : ℕ} [Fact q.Prime]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1) {S : Sylow q N}
    (hS : ∀ a : A, ∀ m ∈ (S : Subgroup N), a • m ∈ (S : Subgroup N))
    {R : Subgroup N} (hRq : IsPGroup q ↥R) (hRinv : ∀ a : A, ∀ m ∈ R, a • m ∈ R) :
    R ≤ (S : Subgroup N) := by
  obtain ⟨T, hTinv, hRT⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow hCop
      (Or.inl ‹IsSolvable A›) hRq (isAInvariant_of_smul_mem hRinv)
  rw [← aInvariant_sylow_unique hCop hfixA (smul_mem_of_isAInvariant hTinv) hS]
  exact hRT

/-! ### (b) 本体の準備 -/

/-- `A` 可換なら `C_N(B)` は `A`-不変。 -/
theorem smul_mem_fixedSubgroup {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (hcomm : ∀ u v : A, u * v = v * u) (B : Subgroup A) :
    ∀ a : A, ∀ m ∈ (fixedSubgroup B : Subgroup N), a • m ∈ (fixedSubgroup B : Subgroup N) := by
  intro a m hm b hb
  rw [← mul_smul, hcomm b a, mul_smul, hm b hb]

/-- exponent `p` の位数 `p²` 群は非巡回 (Thm 6.21 を使うのに要る)。 -/
theorem not_isCyclic_of_card_prime_sq {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hA : ∀ u : A, u ^ p = 1) (hcard : Nat.card A = p ^ 2) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hzp : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hord : orderOf g = p ^ 2 := by
    rw [← hcard, ← Subgroup.card_top (G := A), ← hzp, Nat.card_zpowers]
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hA g)
  rw [hord] at hdvd
  have h1 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.one_lt
  nlinarith

/-- 位数 `p²` の群が固定点自由に作用すれば位数は互いに素。 -/
theorem coprime_card_of_fixedFree {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    [MulDistribMulAction A N] {p : ℕ} (hp : p.Prime) (hcardA : Nat.card A = p ^ 2)
    (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1) :
    Nat.Coprime (Nat.card A) (Nat.card N) := by
  have hnd := not_dvd_card_of_fixedFree_of_isPGroup hp (IsPGroup.of_card hcardA) hfixA
  rw [hcardA]
  exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)

/-- **Isaacs Problem 6C.2(b)** (p. 197) ⭐: `A` の位数 `p` の部分群 `D` ごとに
`K_D = C_N(D)` の最大 `q`-部分群 `Q_D` を取ると, `X = ⨆_D Q_D` は `N` の Sylow
`q`-部分群になる ((a) より位数 `p` の部分群はちょうど `p + 1` 個なので, これが書籍の
`X = ⟨Q_1, …, Q_{p+1}⟩`)。

* `X ≤ S`: `A`-不変 Sylow `q`-部分群 `S` は一意で, 各 `Q_D` は `A`-不変な `q`-部分群
  (`smul_mem_of_max_qSubgroup`) なので `S` に入る。
* `S ≤ X`: **Isaacs Thm 6.21** (可換非巡回 `A` の coprime 作用では `C_S(a)` (`a ≠ 1`) が
  `S` を生成) から。`a ≠ 1` なら `S ⊓ C_N(⟨a⟩)` は `C_N(⟨a⟩)` の `q`-部分群なので
  最大性で `Q_{⟨a⟩}` に入る。 -/
theorem exists_sylow_eq_iSup_maxQSubgroup {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    [MulDistribMulAction A N] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hA : ∀ u : A, u ^ p = 1) (hcomm : ∀ u v : A, u * v = v * u) (hcardA : Nat.card A = p ^ 2)
    (hfixA : ∀ n : N, (∀ a : A, a • n = n) → n = 1)
    (Qf : Subgroup A → Subgroup N)
    (hQle : ∀ D : Subgroup A, Nat.card ↥D = p → Qf D ≤ fixedSubgroup D)
    (hQq : ∀ D : Subgroup A, Nat.card ↥D = p → IsPGroup q ↥(Qf D))
    (hQmax : ∀ D : Subgroup A, Nat.card ↥D = p →
      ∀ R : Subgroup N, R ≤ fixedSubgroup D → IsPGroup q ↥R → R ≤ Qf D) :
    ∃ S : Sylow q N,
      (S : Subgroup N) = ⨆ D : {D : Subgroup A // Nat.card ↥D = p}, Qf (D : Subgroup A) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hsolvA : IsSolvable A := isSolvable_of_comm hcomm
  haveI hcommA : IsMulCommutative A := ⟨⟨hcomm⟩⟩
  have hCop := coprime_card_of_fixedFree hp hcardA hfixA
  have hnc := not_isCyclic_of_card_prime_sq hp hA hcardA
  obtain ⟨S, hSinvA⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (G := N) (A := A)
      (φ := MulDistribMulAction.toMulAut A N) hCop (Or.inl hsolvA) q
  have hS : ∀ a : A, ∀ m ∈ (S : Subgroup N), a • m ∈ (S : Subgroup N) :=
    smul_mem_of_isAInvariant hSinvA
  refine ⟨S, le_antisymm ?_ ?_⟩
  · -- `S ≤ X` (Thm 6.21)
    letI actS : MulDistribMulAction A ↥(S : Subgroup N) :=
      IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hS
    have hCopS : Nat.Coprime (Nat.card A) (Nat.card ↥(S : Subgroup N)) :=
      hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
    have h621 : nontrivialActionFixedByClosure
        (MulDistribMulAction.toMulAut A ↥(S : Subgroup N)) = ⊤ :=
      nontrivialActionFixedByClosure_eq_top_of_not_isCyclic hCopS hnc
    have hgen : nontrivialActionFixedByClosure
        (MulDistribMulAction.toMulAut A ↥(S : Subgroup N))
        ≤ (⨆ D : {D : Subgroup A // Nat.card ↥D = p},
            Qf (D : Subgroup A)).subgroupOf (S : Subgroup N) := by
      rw [nontrivialActionFixedByClosure]
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro u ⟨a, ha, hu⟩
      -- `a • u = u`, `a ≠ 1` から `D := ⟨a⟩` (位数 `p`) を取る
      have hsmul : a • (u : N) = (u : N) := congrArg (fun w : ↥(S : Subgroup N) => (w : N)) hu
      have haord : orderOf a = p := by
        have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hA a)
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
        · exact absurd (orderOf_eq_one_iff.mp h1) ha
        · exact hpp
      have hDcard : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, haord]
      -- `u ∈ S ⊓ C_N(⟨a⟩) ≤ Q_{⟨a⟩}`
      have hufix : (u : N) ∈ (fixedSubgroup (Subgroup.zpowers a) : Subgroup N) := by
        intro b hb
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← hm]
        exact zpow_mem (show a ∈ MulAction.stabilizer A (u : N) from hsmul) m
      have hle : (S : Subgroup N) ⊓ fixedSubgroup (Subgroup.zpowers a) ≤ Qf (Subgroup.zpowers a) :=
        hQmax _ hDcard _ inf_le_right (S.2.to_le inf_le_left)
      have humem : (u : N) ∈ Qf (Subgroup.zpowers a) := hle ⟨u.2, hufix⟩
      exact le_iSup (fun D : {D : Subgroup A // Nat.card ↥D = p} => Qf (D : Subgroup A))
        ⟨Subgroup.zpowers a, hDcard⟩ humem
    rw [h621] at hgen
    exact Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp hgen)
  · -- `X ≤ S`
    refine iSup_le fun D => ?_
    exact le_sylow_of_aInvariant_qSubgroup hCop hfixA hS (hQq _ D.2)
      (smul_mem_of_max_qSubgroup (smul_mem_fixedSubgroup hcomm _) (hQle _ D.2) (hQq _ D.2)
        (hQmax _ D.2))

end

end OddOrder.Isaacs.Ch06
