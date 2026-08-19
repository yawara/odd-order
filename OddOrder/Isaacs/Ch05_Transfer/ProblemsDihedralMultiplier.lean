/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch05_Transfer.ProblemsSchurMultiplier

/-!
# Isaacs Problem 5A.6 — 二面体群の Schur 乗数は位数 2

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 5A.6 (書籍 p. 153)。

> **5A.6** Let `D` be dihedral of order `2^n` where `n ≥ 2`. Show that the Schur
> multiplier `M(D)` has order 2.

⚠ **`pdftotext` 抽出は上付き文字を落とす**: 書籍の `2^n` が `2n` に潰れ、
「order `2n` where `n > 2`」と読める。この読みは**偽** — `n` が奇数なら
`M(D_{2n}) = 1` (例: `D_6 = S_3` は Sylow がすべて巡回なので Isaacs 自身の Cor 5.4 から
`M(S_3) = 1`)。PDF ページ画像 (p. 153 = PDF p. 166) で `2^n`, `n ≥ 2` を確認済み。
同種の上付き潰れは書籍 p. 76 の semidihedral `SD_{2^n}` でも起きている。

本ファイルは書籍の `2^n` 版より**強い一般形**を証明する:

> `m` が偶数なら, 位数 `2m` の二面体群 `DihedralGroup m` の Schur 乗数は位数 2。

(書籍の `D` は `m = 2^{n-1}`, `n ≥ 2` の場合。`m` が奇数なら 5A.5 から直ちに
`M = 1` になるので, 偶数条件は本質的。)

`M(G)` の universal object は未実装 (issue 9206) なので, `ProblemsSchurMultiplier.lean`
と同じく **stem extension (`IsStemExtension`) についての ∀/∃ の対**で述べる:

* 上界 `card_ker_dvd_two_of_dihedral` — 任意の stem extension の核は位数が 2 を割る。
* 下界 `isStemExtension_dihedralReduce` — `D_{4m} ↠ D_{2m}` が核 位数 2 の stem extension。

## 主な内容

* `orderOf_r_natCast_self` / `r_natCast_self_mem_center` — `D_{4t}` の中心対合 `r t`。
* `zpowers_r_one_inf_center` — 回転部分群 ∩ 中心 = `⟨r t⟩` (位数 2)。
* `dihedralReduce` — `m ∣ k` のときの reduction 準同型 `DihedralGroup k →* DihedralGroup m`。

⚠ 回転部分群の巡回性は mathlib の `Subgroup.zpowers` 用 `IsCyclic` instance がそのまま効く
(`inferInstance`) ので, 本ファイルでは補題を立てない。
-/

open scoped commutatorElement

namespace OddOrder.Isaacs.Ch05

open DihedralGroup

section /- 5A.6: Schur multiplier of the dihedral group (p. 153) -/

/-! ### `ZMod (2t)` の 2-torsion -/

/-- `ZMod (2t)` の元 `i` で `t ∣ i.val` なるものは `0` か `t` のみ。

`i.val < 2t` と `i.val = t * q` から `q < 2`。 -/
theorem eq_zero_or_eq_natCast_of_dvd_val {t : ℕ} (ht : t ≠ 0) {i : ZMod (2 * t)}
    (h : t ∣ i.val) : i = 0 ∨ i = ((t : ℕ) : ZMod (2 * t)) := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  obtain ⟨q, hq⟩ := h
  have hlt : t * q < t * 2 := by
    have := ZMod.val_lt i
    rw [hq] at this
    omega
  have hq2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
  interval_cases q
  · left
    have : i.val = 0 := by omega
    exact (ZMod.val_eq_zero i).mp this
  · right
    refine ZMod.val_injective _ ?_
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega

/-! ### `D_{4t}` の中心対合 -/

/-- `DihedralGroup (2t)` の回転 `r t` は位数 2 (`t ≠ 0`)。 -/
theorem orderOf_r_natCast_self {t : ℕ} (ht : t ≠ 0) :
    orderOf (r ((t : ℕ) : ZMod (2 * t)) : DihedralGroup (2 * t)) = 2 := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  rw [DihedralGroup.orderOf_r, ZMod.val_natCast_of_lt (by omega)]
  rw [Nat.gcd_eq_right ⟨2, by ring⟩]
  rw [Nat.mul_div_assoc 2 (dvd_refl t), Nat.div_self (Nat.pos_of_ne_zero ht), mul_one]

/-- `DihedralGroup (2t)` の回転 `r t` は中心元 (`2t = 0` なので反転で不変)。 -/
theorem r_natCast_self_mem_center {t : ℕ} :
    (r ((t : ℕ) : ZMod (2 * t)) : DihedralGroup (2 * t)) ∈
      Subgroup.center (DihedralGroup (2 * t)) := by
  rw [Subgroup.mem_center_iff]
  have hzero : ((t : ℕ) : ZMod (2 * t)) + ((t : ℕ) : ZMod (2 * t)) = 0 := by
    have : ((2 * t : ℕ) : ZMod (2 * t)) = 0 := ZMod.natCast_self _
    push_cast at this
    linear_combination this
  rintro (j | j)
  · simp [add_comm]
  · simp only [sr_mul_r, r_mul_sr]
    congr 1
    linear_combination hzero

/-! ### 回転部分群 -/

/-- `DihedralGroup m` の回転部分群 `⟨r 1⟩` の元は `r i` の形のものちょうど。 -/
theorem mem_zpowers_r_one_iff {m : ℕ} {x : DihedralGroup m} :
    x ∈ Subgroup.zpowers (r (1 : ZMod m)) ↔ ∃ i : ZMod m, x = r i := by
  constructor
  · rintro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨(k : ZMod m), by rw [← hk, r_one_zpow]⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, r_one_zpow k⟩

/-- 回転部分群は正規 (指数 2)。 -/
theorem zpowers_r_one_normal {m : ℕ} : (Subgroup.zpowers (r (1 : ZMod m))).Normal := by
  constructor
  intro x hx g
  rw [mem_zpowers_r_one_iff] at hx ⊢
  obtain ⟨i, rfl⟩ := hx
  rcases g with j | j
  · exact ⟨i, by simp⟩
  · exact ⟨-i, by simp⟩

/-- 回転部分群の位数は `m`。 -/
theorem card_zpowers_r_one (m : ℕ) [NeZero m] :
    Nat.card (Subgroup.zpowers (r (1 : ZMod m))) = m := by
  rw [Nat.card_zpowers, orderOf_r_one]

/-- 回転部分群の指数は 2。 -/
theorem index_zpowers_r_one (m : ℕ) [NeZero m] :
    (Subgroup.zpowers (r (1 : ZMod m))).index = 2 := by
  have hcard := Subgroup.card_mul_index (Subgroup.zpowers (r (1 : ZMod m)))
  rw [card_zpowers_r_one, DihedralGroup.nat_card, mul_comm 2 m] at hcard
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne m)) hcard

/-- 回転部分群による剰余群は位数 2 ゆえ巡回。 -/
theorem isCyclic_quotient_zpowers_r_one (m : ℕ) [NeZero m] :
    letI := zpowers_r_one_normal (m := m)
    IsCyclic (DihedralGroup m ⧸ Subgroup.zpowers (r (1 : ZMod m))) := by
  let := zpowers_r_one_normal (m := m)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card (p := 2) (index_zpowers_r_one m)

/-! ### 回転部分群 ∩ 中心 -/

/-- `m = 2t` が偶数のとき, 回転部分群と中心の交わりは `⟨r t⟩` (位数 2)。

`r i` が中心的 ⟺ `sr 0` と可換 ⟺ `i = -i` ⟺ `2t ∣ 2 i.val` ⟺ `t ∣ i.val`。 -/
theorem zpowers_r_one_inf_center {t : ℕ} (ht : t ≠ 0) :
    Subgroup.zpowers (r (1 : ZMod (2 * t))) ⊓ Subgroup.center (DihedralGroup (2 * t))
      = Subgroup.zpowers (r ((t : ℕ) : ZMod (2 * t))) := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_r_one_iff.mp hx
    -- 中心性を `sr 0` に対して使う
    have hcomm := (Subgroup.mem_center_iff.mp hxc) (sr 0)
    rw [sr_mul_r, r_mul_sr] at hcomm
    have hi : i + i = 0 := by
      have := sr.inj hcomm
      linear_combination this
    -- `i + i = 0` ⇒ `t ∣ i.val`
    have hdvd : (2 * t) ∣ (i.val + i.val) := by
      have h0 : ((i.val + i.val : ℕ) : ZMod (2 * t)) = 0 := by
        push_cast [ZMod.natCast_zmod_val]
        exact hi
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hdvd2 : 2 * t ∣ 2 * i.val := by
      have htwo : i.val + i.val = 2 * i.val := by ring
      rwa [htwo] at hdvd
    have hdvd' : t ∣ i.val :=
      (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hdvd2
    rcases eq_zero_or_eq_natCast_of_dvd_val ht hdvd' with h | h
    · rw [h]
      simp
    · rw [h]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨mem_zpowers_r_one_iff.mpr ⟨_, rfl⟩, r_natCast_self_mem_center⟩

/-- `m = 2t` が偶数のとき `|C ∩ Z(D)| = 2` (`C` = 回転部分群)。 -/
theorem card_zpowers_r_one_inf_center {t : ℕ} (ht : t ≠ 0) :
    Nat.card (Subgroup.zpowers (r (1 : ZMod (2 * t))) ⊓
      Subgroup.center (DihedralGroup (2 * t)) : Subgroup (DihedralGroup (2 * t))) = 2 := by
  rw [zpowers_r_one_inf_center ht, Nat.card_zpowers, orderOf_r_natCast_self ht]

/-! ### Problem 5A.6 の上界 -/

/-- **Isaacs Problem 5A.6 上界** (∀-形): `m = 2t` が偶数なら, 位数 `2m` の二面体群
`DihedralGroup m` の任意の stem extension `f : Γ →* DihedralGroup m` について
`|ker f|` は 2 を割る。すなわち `|M(D)| ∣ 2`。

Problem 5A.5 (`card_ker_dvd_relIndex_commutator`) を `C` = 回転部分群 (巡回・正規・
剰余は位数 2 ゆえ巡回) に適用し, Lemma 4.6 の指数形で `|C : D'| = |C ∩ Z(D)| = 2`。 -/
theorem card_ker_dvd_two_of_dihedral {Γ : Type*} [Group Γ] [Finite Γ] {t : ℕ} (ht : t ≠ 0)
    {f : Γ →* DihedralGroup (2 * t)} (hf : IsStemExtension f) :
    Nat.card f.ker ∣ 2 := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  let := zpowers_r_one_normal (m := 2 * t)
  have := isCyclic_quotient_zpowers_r_one (2 * t)
  have hdvd := card_ker_dvd_relIndex_commutator hf
    (C := Subgroup.zpowers (r (1 : ZMod (2 * t))))
    inferInstance (isCyclic_quotient_zpowers_r_one (2 * t))
  have hrel : (_root_.commutator (DihedralGroup (2 * t))).relIndex
      (Subgroup.zpowers (r (1 : ZMod (2 * t)))) = 2 := by
    rw [relIndex_commutator_eq_card_inf_center
      (forall_mul_comm_of_isMulCommutative inferInstance)
      (isCyclic_quotient_zpowers_r_one (2 * t))]
    exact card_zpowers_r_one_inf_center ht
  rwa [hrel] at hdvd

/-! ### Problem 5A.6 の下界 (stem extension の構成) -/

/-- `m ∣ k` のときの reduction 準同型 `DihedralGroup k →* DihedralGroup m`
(`r i ↦ r (i mod m)`, `sr i ↦ sr (i mod m)`)。 -/
def dihedralReduce {m k : ℕ} (h : m ∣ k) : DihedralGroup k →* DihedralGroup m where
  toFun x := match x with
    | r i => r (ZMod.castHom h (ZMod m) i)
    | sr i => sr (ZMod.castHom h (ZMod m) i)
  map_one' := by
    change (r (ZMod.castHom h (ZMod m) 0) : DihedralGroup m) = 1
    simp
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j <;>
      simp [map_add, map_sub]

@[simp]
theorem dihedralReduce_r {m k : ℕ} (h : m ∣ k) (i : ZMod k) :
    dihedralReduce h (r i) = r (ZMod.castHom h (ZMod m) i) := rfl

@[simp]
theorem dihedralReduce_sr {m k : ℕ} (h : m ∣ k) (i : ZMod k) :
    dihedralReduce h (sr i) = sr (ZMod.castHom h (ZMod m) i) := rfl

theorem dihedralReduce_surjective {m k : ℕ} [NeZero m] [NeZero k] (h : m ∣ k) :
    Function.Surjective (dihedralReduce h) := by
  have hcast : ∀ j : ZMod m, ∃ i : ZMod k, ZMod.castHom h (ZMod m) i = j := by
    intro j
    refine ⟨((j.val : ℕ) : ZMod k), ?_⟩
    rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  rintro (j | j)
  · obtain ⟨i, hi⟩ := hcast j
    exact ⟨r i, by simp [hi]⟩
  · obtain ⟨i, hi⟩ := hcast j
    exact ⟨sr i, by simp [hi]⟩

/-- `D_{4t} ↠ D_{2t}` の核は `⟨r (2t)⟩`。 -/
theorem ker_dihedralReduce_two_mul {t : ℕ} (ht : t ≠ 0) :
    (dihedralReduce (m := 2 * t) (k := 2 * (2 * t)) ⟨2, by ring⟩).ker =
      Subgroup.zpowers (r (((2 * t : ℕ)) : ZMod (2 * (2 * t)))) := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  have : NeZero (2 * (2 * t)) := ⟨by positivity⟩
  apply le_antisymm
  · rintro (i | i) hx
    · rw [MonoidHom.mem_ker, dihedralReduce_r, one_def] at hx
      have hcast : ZMod.castHom (⟨2, by ring⟩ : (2 * t) ∣ (2 * (2 * t))) (ZMod (2 * t)) i = 0 :=
        r.inj hx
      have hdvd : (2 * t) ∣ i.val := by
        have h0 : ((i.val : ℕ) : ZMod (2 * t)) = 0 := by
          rw [← map_natCast (ZMod.castHom (⟨2, by ring⟩ : (2 * t) ∣ (2 * (2 * t)))
            (ZMod (2 * t))) i.val, ZMod.natCast_zmod_val]
          exact hcast
        exact (ZMod.natCast_eq_zero_iff _ _).mp h0
      rcases eq_zero_or_eq_natCast_of_dvd_val (by positivity) (i := i) hdvd with h | h
      · rw [h]
        simp
      · rw [h]
        exact Subgroup.mem_zpowers _
    · rw [MonoidHom.mem_ker, dihedralReduce_sr, one_def] at hx
      simp only [reduceCtorEq] at hx
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, dihedralReduce_r, map_natCast,
      ZMod.natCast_self, r_zero]

/-- **Isaacs Problem 5A.6 下界**: `m = 2t` が偶数のとき `D_{4t} ↠ D_{2t}` は
核が位数 2 の stem extension。したがって `|M(D_{2t·2})| = 2` の下界が実現される。

* 核 `⟨r (2t)⟩` は位数 2 (`orderOf_r_natCast_self`)。
* 核は中心 (`r_natCast_self_mem_center`)。
* 核は交換子群: `⁅r t, sr 0⁆ = r (2t)` (二面体群の交換子計算)。 -/
theorem isStemExtension_dihedralReduce {t : ℕ} (ht : t ≠ 0) :
    IsStemExtension (dihedralReduce (m := 2 * t) (k := 2 * (2 * t)) ⟨2, by ring⟩) ∧
      Nat.card (dihedralReduce (m := 2 * t) (k := 2 * (2 * t)) ⟨2, by ring⟩).ker = 2 := by
  have : NeZero (2 * t) := ⟨by positivity⟩
  have : NeZero (2 * (2 * t)) := ⟨by positivity⟩
  have hker := ker_dihedralReduce_two_mul ht
  refine ⟨⟨dihedralReduce_surjective _, ?_, ?_⟩, ?_⟩
  · -- ker ≤ commutator: 生成元 `r (2t) = ⁅r t, sr 0⁆`
    rw [hker, Subgroup.zpowers_le]
    have hcomm : ⁅(r ((t : ℕ) : ZMod (2 * (2 * t))) : DihedralGroup (2 * (2 * t))), sr 0⁆
        = r (((2 * t : ℕ)) : ZMod (2 * (2 * t))) := by
      rw [commutatorElement_def]
      simp only [r_mul_sr, sr_mul_r, inv_r, inv_sr, sr_mul_sr]
      congr 1
      push_cast
      ring
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [hker, Subgroup.zpowers_le]
    exact r_natCast_self_mem_center
  · rw [hker, Nat.card_zpowers, orderOf_r_natCast_self (by positivity)]

end

end OddOrder.Isaacs.Ch05
