/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Theorem131
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.RootGroupSylow

/-!
# Isaacs Problem 7A.2 — `SL(2,3)` の位数 `8` の正規部分群 (書籍 p. 209)

**主張**: `S = SL(2,3)`, `Z = {±I}` とすると `S/Z` (位数 `12`) の Sylow `3`-部分群は `4` 個
あり, したがって Sylow `2`-部分群は一意。これから `S` は位数 `8` の正規部分群を持つ。

本ファイルはまず `S` についての**具体的な計算事実**を用意する:

* `|S| = 24` (`natCard_specialLinearGroup_fin_two`, `|ZMod 3| = 3` で `3 · 2 · 4`)
* `Z := ⟨-I⟩` は中心的で位数 `2` (`-I ≠ I` は標数 `3` ゆえ)
* 位数 `3` の元 `a = [[1,1],[0,1]]`, `b = [[1,0],[1,1]]` で `b ∉ ⟨a⟩`
  (書籍 hint の「`GL(n,q)` は Sylow `p`-部分群を 2 個以上持つ」を具体行列で実現する)
-/

namespace OddOrder.Isaacs.Ch07

section /- 7A.2: `SL(2,3)` の具体計算 (p. 209) -/

/-- `SL(2,3)`。 -/
abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

open OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear in
/-- `|SL(2,3)| = 24`。 -/
theorem natCard_sl23 : Nat.card SL23 = 24 := by
  have h := natCard_specialLinearGroup_fin_two (F := ZMod 3)
  have h3 : Nat.card (ZMod 3) = 3 := by simp
  rw [h3] at h
  simpa using h

/-- `-I ∈ SL(2,3)` (標数 `3` なので `-I ≠ I`)。 -/
def negOneSL23 : SL23 := ⟨!![2, 0; 0, 2], by decide⟩

/-- 位数 `3` の元 `a = [[1,1],[0,1]]`。 -/
def transvectionA : SL23 := ⟨!![1, 1; 0, 1], by decide⟩

/-- 位数 `3` の元 `b = [[1,0],[1,1]]`。 -/
def transvectionB : SL23 := ⟨!![1, 0; 1, 1], by decide⟩

theorem negOneSL23_sq : negOneSL23 ^ 2 = 1 := by decide

theorem negOneSL23_ne_one : negOneSL23 ≠ 1 := by decide

theorem transvectionA_pow_three : transvectionA ^ 3 = 1 := by decide

theorem transvectionA_ne_one : transvectionA ≠ 1 := by decide

theorem transvectionB_pow_three : transvectionB ^ 3 = 1 := by decide

theorem transvectionB_ne_one : transvectionB ≠ 1 := by decide

/-- `b ∉ ⟨a⟩`: `⟨a⟩ = {1, a, a²}` を直接展開して確かめる。 -/
theorem transvectionB_notMem_zpowers_transvectionA :
    transvectionB ∉ Subgroup.zpowers transvectionA := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  -- `a` の位数は `3` なので `a ^ m ∈ {1, a, a²}`
  have hord : orderOf transvectionA = 3 := by
    have hdvd : orderOf transvectionA ∣ 3 := orderOf_dvd_of_pow_eq_one transvectionA_pow_three
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) transvectionA_ne_one
    · exact h3
  have ha3 : transvectionA ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from by norm_num, zpow_natCast]
    exact transvectionA_pow_three
  have hmod : transvectionA ^ m = transvectionA ^ (m % 3) := by
    conv_lhs => rw [show m = 3 * (m / 3) + m % 3 from by omega]
    rw [zpow_add, zpow_mul, ha3, one_zpow, one_mul]
  rw [hmod] at hm
  have hlt : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hlt with h | h | h <;> rw [h] at hm <;> revert hm <;> decide

/-! ### `Z = ⟨-I⟩` と商群 `S/Z` (位数 `12`) -/

/-- `Z := ⟨-I⟩ ≤ SL(2,3)`。 -/
abbrev centerZ : Subgroup SL23 := Subgroup.zpowers negOneSL23

theorem orderOf_negOneSL23 : orderOf negOneSL23 = 2 := by
  have hdvd : orderOf negOneSL23 ∣ 2 := orderOf_dvd_of_pow_eq_one negOneSL23_sq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) negOneSL23_ne_one
  · exact h2

theorem natCard_centerZ : Nat.card ↥centerZ = 2 := by
  rw [Nat.card_zpowers, orderOf_negOneSL23]

/-- `-I` は `SL(2,3)` の中心元 (スカラー行列)。 -/
theorem negOneSL23_mem_center : negOneSL23 ∈ Subgroup.center SL23 := by
  refine Subgroup.mem_center_iff.mpr ?_
  decide

instance centerZ_normal : centerZ.Normal where
  conj_mem n hn g := by
    have hfix : ∀ x ∈ centerZ, g * x * g⁻¹ = x := by
      intro x hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcomm : Commute g negOneSL23 :=
        Subgroup.mem_center_iff.mp negOneSL23_mem_center g
      have hcx : Commute g x := by rw [← hm]; exact hcomm.zpow_right m
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcx.eq]
        _ = x := by group
    rw [hfix n hn]
    exact hn

/-- `|SL(2,3)/Z| = 12`。 -/
theorem natCard_quotient_centerZ : Nat.card (SL23 ⧸ centerZ) = 12 := by
  have h := Subgroup.card_mul_index centerZ
  rw [natCard_centerZ, natCard_sl23] at h
  have hidx : centerZ.index = 12 := by omega
  have : Nat.card (SL23 ⧸ centerZ) = centerZ.index := rfl
  rw [this, hidx]

/-! ### `n_3(S/Z) = 4` と主結論 -/

/-- `Z = {1, -I}`。 -/
theorem mem_centerZ_iff {x : SL23} : x ∈ centerZ ↔ x = 1 ∨ x = negOneSL23 := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : negOneSL23 ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
      exact negOneSL23_sq
    have hmod : negOneSL23 ^ m = negOneSL23 ^ (m % 2) := by
      conv_lhs => rw [show m = 2 * (m / 2) + m % 2 from by omega]
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rw [hmod] at hm
    have : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] at hm
    · exact Or.inl (by simpa using hm.symm)
    · exact Or.inr (by simpa using hm.symm)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/-- `S/Z` の Sylow `3`-部分群はちょうど `4` 個。

`n_3 ∣ 4` かつ `n_3 ≡ 1 (mod 3)` から `n_3 ∈ {1, 4}`。`n_3 = 1` なら `a`, `b` の像が
生成する位数 `3` の部分群が一致してしまい, `b ∈ ⟨a⟩ · Z` (6 通り) がすべて偽なので矛盾。 -/
theorem card_sylow_three_quotient : Nat.card (Sylow 3 (SL23 ⧸ centerZ)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := SL23 ⧸ centerZ with hQdef
  have hQcard : Nat.card Q = 2 ^ 2 * 3 := by
    rw [hQdef, natCard_quotient_centerZ]; norm_num
  obtain ⟨P0⟩ : Nonempty (Sylow 3 Q) := inferInstance
  have hP0card : Nat.card (P0 : Subgroup Q) = 3 :=
    OddOrder.Isaacs.Ch01.card_sylow_q_of_card_eq_sq_mul_prime (by norm_num) hQcard P0
  have hidx : (P0 : Subgroup Q).index = 4 := by
    have h := Subgroup.card_mul_index (P0 : Subgroup Q)
    rw [hP0card, hQcard] at h
    omega
  have hdvd : Nat.card (Sylow 3 Q) ∣ 4 := hidx ▸ Sylow.card_dvd_index P0
  have hmod : Nat.card (Sylow 3 Q) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 Q
  -- `n_3 ∈ {1, 4}`
  have hcases : Nat.card (Sylow 3 Q) = 1 ∨ Nat.card (Sylow 3 Q) = 4 := by
    have h4 : Nat.card (Sylow 3 Q) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Sylow 3 Q)
    · simp at hdvd
    · exact Or.inl rfl
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exact Or.inr rfl
  rcases hcases with h1 | h4
  swap
  · exact h4
  -- `n_3 = 1` を排除する
  exfalso
  haveI hsub : Subsingleton (Sylow 3 Q) := Nat.card_eq_one_iff_unique.mp h1 |>.1
  -- `a`, `b` の像は位数 `3`
  have hnotmem : ∀ x : SL23, x ≠ 1 → x ≠ negOneSL23 → (QuotientGroup.mk x : Q) ≠ 1 := by
    intro x hx1 hx2 hcon
    rcases mem_centerZ_iff.mp ((QuotientGroup.eq_one_iff x).mp hcon) with h | h
    · exact hx1 h
    · exact hx2 h
  have hord : ∀ x : SL23, x ^ 3 = 1 → (QuotientGroup.mk x : Q) ≠ 1 →
      orderOf (QuotientGroup.mk x : Q) = 3 := by
    intro x hx3 hxne
    have hdvd3 : orderOf (QuotientGroup.mk x : Q) ∣ 3 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← QuotientGroup.mk_pow, hx3]
      rfl
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxne
    · exact h
  have hane : (QuotientGroup.mk transvectionA : Q) ≠ 1 :=
    hnotmem _ transvectionA_ne_one (by decide)
  have hbne : (QuotientGroup.mk transvectionB : Q) ≠ 1 :=
    hnotmem _ transvectionB_ne_one (by decide)
  have haord := hord _ transvectionA_pow_three hane
  have hbord := hord _ transvectionB_pow_three hbne
  -- 両者の生成する位数 `3` の部分群は Sylow に含まれ, 一意性から一致する
  have hpg : ∀ x : Q, orderOf x = 3 → IsPGroup 3 ↥(Subgroup.zpowers x) := by
    intro x hx
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨P1, hP1⟩ := (hpg _ haord).exists_le_sylow
  obtain ⟨P2, hP2⟩ := (hpg _ hbord).exists_le_sylow
  have hPeq : P1 = P2 := Subsingleton.elim _ _
  have hzp : Subgroup.zpowers (QuotientGroup.mk transvectionA : Q)
      = Subgroup.zpowers (QuotientGroup.mk transvectionB : Q) := by
    have h1' : Subgroup.zpowers (QuotientGroup.mk transvectionA : Q) = (P1 : Subgroup Q) :=
      Subgroup.eq_of_le_of_card_ge hP1 (by
        rw [OddOrder.Isaacs.Ch01.card_sylow_q_of_card_eq_sq_mul_prime (by norm_num) hQcard P1,
          Nat.card_zpowers, haord])
    have h2' : Subgroup.zpowers (QuotientGroup.mk transvectionB : Q) = (P2 : Subgroup Q) :=
      Subgroup.eq_of_le_of_card_ge hP2 (by
        rw [OddOrder.Isaacs.Ch01.card_sylow_q_of_card_eq_sq_mul_prime (by norm_num) hQcard P2,
          Nat.card_zpowers, hbord])
    rw [h1', h2', hPeq]
  -- `b̄ ∈ ⟨ā⟩` から `(a^i)⁻¹ * b ∈ Z` (6 通り) で矛盾
  have hbmem : (QuotientGroup.mk transvectionB : Q)
      ∈ Subgroup.zpowers (QuotientGroup.mk transvectionA : Q) := by
    rw [hzp]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hbmem
  have ha3 : transvectionA ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from by norm_num, zpow_natCast]
    exact transvectionA_pow_three
  have hmodi : (QuotientGroup.mk transvectionA : Q) ^ i
      = (QuotientGroup.mk transvectionA : Q) ^ (i % 3) := by
    conv_lhs => rw [show i = 3 * (i / 3) + i % 3 from by omega]
    have h3q : (QuotientGroup.mk transvectionA : Q) ^ (3 : ℤ) = 1 := by
      rw [← QuotientGroup.mk_zpow, ha3]
      rfl
    rw [zpow_add, zpow_mul, h3q, one_zpow, one_mul]
  rw [hmodi] at hi
  have hcoset : ∀ j : ℤ, (QuotientGroup.mk transvectionA : Q) ^ j
      = (QuotientGroup.mk transvectionB : Q) →
      (transvectionA ^ j)⁻¹ * transvectionB ∈ centerZ := by
    intro j hj
    rw [← QuotientGroup.mk_zpow] at hj
    exact QuotientGroup.eq.mp hj
  have hi3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi3 with h | h | h <;> rw [h] at hi <;>
    rcases mem_centerZ_iff.mp (hcoset _ hi) with hc | hc <;> revert hc <;> decide

/-- **Isaacs Problem 7A.2** (p. 209) ⭐: `SL(2,3)` は位数 `8` の正規部分群を持つ。 -/
theorem exists_normal_card_eight_sl23 :
    ∃ N : Subgroup SL23, N.Normal ∧ Nat.card ↥N = 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPnormal⟩ := OddOrder.Isaacs.Ch01.sylow_two_normal_of_card_twelve_of_four_sylow_three
    natCard_quotient_centerZ card_sylow_three_quotient
  refine ⟨(P : Subgroup (SL23 ⧸ centerZ)).comap (QuotientGroup.mk' centerZ), ?_, ?_⟩
  · exact Subgroup.Normal.comap hPnormal _
  · -- 指数が保たれるので `|N| = 24 / 3 = 8`
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hQcard : Nat.card (SL23 ⧸ centerZ) = 2 ^ 2 * 3 := by
      rw [natCard_quotient_centerZ]; norm_num
    have hPcard : Nat.card (P : Subgroup (SL23 ⧸ centerZ)) = 4 :=
      OddOrder.Isaacs.Ch01.card_sylow_p_of_card_eq_sq_mul_prime (by norm_num) hQcard P
    have hPidx : (P : Subgroup (SL23 ⧸ centerZ)).index = 3 := by
      have h := Subgroup.card_mul_index (P : Subgroup (SL23 ⧸ centerZ))
      rw [hPcard, hQcard] at h
      omega
    have hidx : ((P : Subgroup (SL23 ⧸ centerZ)).comap (QuotientGroup.mk' centerZ)).index = 3 := by
      rw [Subgroup.index_comap, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective centerZ),
        Subgroup.relIndex_top_right, hPidx]
    have h := Subgroup.card_mul_index
      ((P : Subgroup (SL23 ⧸ centerZ)).comap (QuotientGroup.mk' centerZ))
    rw [hidx, natCard_sl23] at h
    omega

end

end OddOrder.Isaacs.Ch07
