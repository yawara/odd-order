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

end

end OddOrder.Isaacs.Ch07
