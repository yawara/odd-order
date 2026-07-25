/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch02_Subnormality.Basic

/-!
# Isaacs Chapter 2 — Problems §2B: involution と二面体群 (p. 57)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 §2B のうち **involution
(位数 2 の元) と二面体群**を扱う問題 (2B.2-2B.5)。§2B の部分正規性の問題 (2B.1) は
`Problems.lean` (実体は `Basic.lean` の `isSubnormal_of_forall_nilpotent_or_permutable`)。

⚠ 同ディレクトリの `DihedralBasics.lean` は「巡回部分群を反転する involution」型の**抽象**
補題群 (Lemma 2.14 / Matsuyama で使う) であって、mathlib の具体的な `DihedralGroup n` は
扱っていない。本ファイルは mathlib `DihedralGroup n` (元は `r i` / `sr i`, `i : ZMod n`,
位数 `2n`) の上で議論する。

## 主な内容

- involution の分類 (`orderOf_r_eq_two_iff` / `orderOf_sr` (mathlib) / `orderOf_eq_two_iff`)
- **2B.2(a)**: `n` 奇 ⟹ involution はちょうど `n` 個で、すべて単一の共役類
-/

namespace OddOrder.Isaacs.Ch02

namespace DihedralGroup

open _root_.DihedralGroup

variable {n : ℕ}

section /- Problems 2B: involutions in dihedral groups (p. 57) -/

/-- `r i = 1` は `i = 0` と同値。 -/
theorem r_eq_one_iff (i : ZMod n) : (r i : _root_.DihedralGroup n) = 1 ↔ i = 0 := by
  rw [one_def]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

/-- **回転部分の involution 判定**: `r i` の位数が `2` ⟺ `i ≠ 0` かつ `2i = 0`。 -/
theorem orderOf_r_eq_two_iff (i : ZMod n) :
    orderOf (r i : _root_.DihedralGroup n) = 2 ↔ i ≠ 0 ∧ i + i = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    have hsq : (r i : _root_.DihedralGroup n) ^ 2 = 1 := h ▸ pow_orderOf_eq_one _
    rw [sq, r_mul_r, r_eq_one_iff] at hsq
    refine ⟨fun hi => ?_, hsq⟩
    rw [hi, r_zero, orderOf_one] at h
    exact absurd h (by norm_num)
  · rintro ⟨hne, hsum⟩
    refine orderOf_eq_prime ?_ ((r_eq_one_iff i).not.mpr hne)
    rw [sq, r_mul_r, hsum, r_zero]

/-- **involution の分類**: `DihedralGroup n` の位数 2 の元は、すべての鏡映 `sr i` と、
`2i = 0` をみたす非自明な回転 `r i` である。 -/
theorem orderOf_eq_two_iff (g : _root_.DihedralGroup n) :
    orderOf g = 2 ↔ (∃ i, g = sr i) ∨ ∃ i, g = r i ∧ i ≠ 0 ∧ i + i = 0 := by
  cases g with
  | r i =>
    rw [orderOf_r_eq_two_iff]
    constructor
    · exact fun h => Or.inr ⟨i, rfl, h⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj, h⟩)
      · exact absurd hj (by simp)
      · injection hj with hij; exact hij ▸ h
  | sr i => simp

/-! ### 2B.2(a): `n` が奇数のとき -/

/-- `n` が奇数なら `2i = 0` をみたす `i : ZMod n` は `0` のみ (`2` が `ZMod n` の単元)。 -/
theorem eq_zero_of_add_self_eq_zero_of_odd (hn : Odd n) {i : ZMod n} (h : i + i = 0) :
    i = 0 := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have h2 : (2 : ZMod n) * i = 0 := by rw [two_mul]; exact h
  have hu : IsUnit (2 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at h2
  simpa using congrArg (fun x => (↑u⁻¹ : ZMod n) * x) h2

/-- **Isaacs Problem 2B.2(a)** (involution の記述). `n` 奇数のとき `DihedralGroup n` の
involution はちょうど鏡映 `sr i` (`i : ZMod n`) 全体。 -/
theorem orderOf_eq_two_iff_of_odd (hn : Odd n) (g : _root_.DihedralGroup n) :
    orderOf g = 2 ↔ ∃ i, g = sr i := by
  rw [orderOf_eq_two_iff]
  refine or_iff_left ?_
  rintro ⟨i, -, hne, hsum⟩
  exact hne (eq_zero_of_add_self_eq_zero_of_odd hn hsum)

/-- **Isaacs Problem 2B.2(a)** (個数). `n` 奇数のとき `DihedralGroup n` の involution は
ちょうど `n` 個。 -/
theorem card_involutions_of_odd (hn : Odd n) :
    Nat.card {g : _root_.DihedralGroup n // orderOf g = 2} = n := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hset : {g : _root_.DihedralGroup n | orderOf g = 2} = Set.range sr := by
    ext g
    simpa [eq_comm] using orderOf_eq_two_iff_of_odd hn g
  calc Nat.card {g : _root_.DihedralGroup n // orderOf g = 2}
      = Nat.card (Set.range (sr : ZMod n → _root_.DihedralGroup n)) := by rw [← hset]; rfl
    _ = Nat.card (ZMod n) :=
        Nat.card_range_of_injective (fun i j h => by injection h)
    _ = n := Nat.card_zmod n

/-- 鏡映どうしの共役: `sr j` で `sr i` を共役すると `sr (2j - i)`。 -/
theorem sr_conj_sr (i j : ZMod n) :
    (sr j : _root_.DihedralGroup n) * sr i * (sr j)⁻¹ = sr (j + j - i) := by
  rw [inv_sr, sr_mul_sr, r_mul_sr]
  ring_nf

/-- 回転による鏡映の共役: `r j` で `sr i` を共役すると `sr (i - 2j)`。 -/
theorem r_conj_sr (i j : ZMod n) :
    (r j : _root_.DihedralGroup n) * sr i * (r j)⁻¹ = sr (i - (j + j)) := by
  rw [inv_r, r_mul_sr, sr_mul_r]
  ring_nf

/-- **Isaacs Problem 2B.2(a)** (共役類). `n` 奇数のとき、すべての involution は
単一の共役類をなす (`2` が `ZMod n` の単元なので `sr i ↦ sr (i - 2j)` が推移的)。 -/
theorem isConj_sr_of_odd (hn : Odd n) (i j : ZMod n) :
    IsConj (sr i : _root_.DihedralGroup n) (sr j) := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  -- `2` は単元ゆえ `k + k = i - j` なる `k` が取れる
  obtain ⟨u, hu⟩ : IsUnit (2 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  have hkey : (↑u⁻¹ : ZMod n) * (i - j) + (↑u⁻¹ : ZMod n) * (i - j) = i - j := by
    rw [← two_mul, ← mul_assoc, ← hu]
    simp
  rw [isConj_iff]
  refine ⟨r ((↑u⁻¹ : ZMod n) * (i - j)), ?_⟩
  rw [r_conj_sr]
  congr 1
  rw [hkey]
  ring

end

end DihedralGroup

end OddOrder.Isaacs.Ch02
