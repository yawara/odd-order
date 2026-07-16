/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt

/-!
# Isaacs Ch. 2 — Lemma 2.14: dihedral structure from two involutions (pp. 56-57)

Isaacs, *Finite Group Theory* (AMS GSM 92), section 2B, **Lemma 2.14** の完全形.
書籍の定義: 群 `D` が **dihedral** ⟺ nontrivial cyclic `C ≤ D` with `|D : C| = 2` が存在し
`D - C` の元が全て involution.

Lemma 2.14 の核心 (inversion `t * z * t = z⁻¹` と `⟨{s, t}⟩` の coset 分解) は
`Theorem211Wielandt.lean` が Matsuyama Thm 2.13 用に既証明
(`inv_by_two_involutions`, `mem_zpowers_or_mul_t_mem_of_mem_closure_pair`).
本ファイルはそれらを cite して残りの clause を book 強度でパッケージする:

- **(a) iff** `forall_involution_iff_conj_eq_inv`: `C = ⟨c⟩` index `2`, involution `t ∉ C`
  について「`D - C` の元が全て involution ⟺ `t * c * t = c⁻¹`」.
- **(a) 帰結**: `conj_eq_inv_of_notMem_zpowers` (`y * x * y⁻¹ = x⁻¹` for `x ∈ C`, `y ∉ C`),
  `mul_sq_eq_one_of_conj_eq_inv` (`c * t` は involution),
  `closure_mul_involution_eq_top` (`D = ⟨c * t, t⟩`; 「`c * t ≠ t`」は `c ≠ 1` と同値なので
  独立の statement は持たない).
- **(b)**: 相異なる nontrivial involution `s, t` が生成する群で `C = ⟨s * t⟩` について
  `mul_ne_one_of_ne` (`C` nontrivial), `left/right_notMem_zpowers_mul` (`s, t ∉ C`),
  `index_zpowers_mul_eq_two` (`|D : C| = 2`).
  「`t` が生成元 `s * t` を invert する」は既存 `inv_by_two_involutions` そのもの (再掲しない).
- **capstone** `sq_eq_one_of_notMem_zpowers_mul`: (b) の状況で `D - C` の元は全て involution
  (= `D` は book の意味で dihedral).

有限性は一切仮定しない (infinite dihedral group を含む). 有限 case の mathlib
`DihedralGroup (orderOf c)` との同型は Ch06 `DQSDRecognition.lean`
(`dihedralOrQuaternion_of_invertingConjugation` の dihedral 枝) が担う.
-/

namespace OddOrder.Isaacs.Ch02

section /- 2B: Dihedral groups, Lemma 2.14 (pp. 56-57) -/
variable {D : Type*} [Group D]

/-- Index-`2` 部分群の coset 二分法: `t ∉ C` かつ `y ∉ C` なら `y * t ∈ C`.
Lemma 2.14 で `D - C = Ct` (index 2 の非自明 coset) として繰り返し使う. -/
private lemma mul_mem_of_notMem_of_notMem {C : Subgroup D} (h_idx : C.index = 2)
    {t y : D} (ht_not : t ∉ C) (hy : y ∉ C) : y * t ∈ C := by
  rw [Subgroup.mul_mem_iff_of_index_two h_idx]
  exact iff_of_false hy ht_not

/-- **Isaacs Lemma 2.14(a) 補助**: involution `t` が `c` を invert する
(`t * c * t = c⁻¹`) なら, `⟨c⟩` の任意の元を invert する.

`inv_by_two_involutions` を `s := c * t` (involution になる) として再利用する. -/
theorem conj_eq_inv_of_mem_zpowers {c t : D} (ht : t * t = 1)
    (h_conj : t * c * t = c⁻¹) {x : D} (hx : x ∈ Subgroup.zpowers c) :
    t * x * t = x⁻¹ := by
  have hs : (c * t) * (c * t) = 1 := by
    calc (c * t) * (c * t) = c * (t * c * t) := by group
      _ = c * c⁻¹ := by rw [h_conj]
      _ = 1 := mul_inv_cancel c
  have hgen : (c * t) * t = c := by rw [mul_assoc, ht, mul_one]
  exact inv_by_two_involutions hs ht (by rwa [hgen])

/-- **Isaacs Lemma 2.14(a) (iff)**: `C = ⟨c⟩` が index `2` の部分群, `t ∉ C` が
involution のとき, 「`D - C` の元が全て involution」⟺「`t` が `c` を invert する」.

この iff の成立時 (`D` が nontrivial `C` を持つとき) が書籍の **dihedral** の定義. -/
theorem forall_involution_iff_conj_eq_inv {c t : D}
    (h_idx : (Subgroup.zpowers c).index = 2)
    (ht_not : t ∉ Subgroup.zpowers c) (ht : t * t = 1) :
    (∀ y, y ∉ Subgroup.zpowers c → y * y = 1) ↔ t * c * t = c⁻¹ := by
  constructor
  · intro h_all
    have hct_not : c * t ∉ Subgroup.zpowers c := by
      intro hmem
      have h1 : c⁻¹ * (c * t) ∈ Subgroup.zpowers c :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) hmem
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
      exact ht_not h1
    have h2 : c * (t * c * t) = 1 := by
      calc c * (t * c * t) = (c * t) * (c * t) := by group
        _ = 1 := h_all _ hct_not
    calc t * c * t = c⁻¹ * (c * (t * c * t)) := by group
      _ = c⁻¹ := by rw [h2, mul_one]
  · intro h_conj y hy
    have ha : y * t ∈ Subgroup.zpowers c :=
      mul_mem_of_notMem_of_notMem h_idx ht_not hy
    have h_inv : t * (y * t) * t = (y * t)⁻¹ :=
      conj_eq_inv_of_mem_zpowers ht h_conj ha
    have hy_eq : (y * t) * t = y := by rw [mul_assoc, ht, mul_one]
    calc y * y = ((y * t) * t) * ((y * t) * t) := by rw [hy_eq]
      _ = (y * t) * (t * (y * t) * t) := by group
      _ = (y * t) * (y * t)⁻¹ := by rw [h_inv]
      _ = 1 := mul_inv_cancel _

/-- **Isaacs Lemma 2.14(a) (全反転)**: dihedral 状況 (`C = ⟨c⟩` index `2`, involution
`t ∉ C` が `c` を invert) で, `C` の任意の元 `x` は `D - C` の任意の元 `y` に反転される:
`y * x * y⁻¹ = x⁻¹`. -/
theorem conj_eq_inv_of_notMem_zpowers {c t : D}
    (h_idx : (Subgroup.zpowers c).index = 2)
    (ht_not : t ∉ Subgroup.zpowers c) (ht : t * t = 1)
    (h_conj : t * c * t = c⁻¹) {x y : D}
    (hx : x ∈ Subgroup.zpowers c) (hy : y ∉ Subgroup.zpowers c) :
    y * x * y⁻¹ = x⁻¹ := by
  have ht_inv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  have ha : y * t ∈ Subgroup.zpowers c := mul_mem_of_notMem_of_notMem h_idx ht_not hy
  have h_tx : t * x * t = x⁻¹ := conj_eq_inv_of_mem_zpowers ht h_conj hx
  -- `y * t ∈ ⟨c⟩` は `x ∈ ⟨c⟩` と可換なので, `x` の `y * t`-共役は `x` 自身.
  have h_axa : (y * t) * x * (y * t)⁻¹ = x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk, ← hm, (Commute.zpow_zpow_self c k m).eq, mul_assoc, mul_inv_cancel, mul_one]
  -- 一方その共役は `t`-共役を経由して `y * x⁻¹ * y⁻¹` に等しい.
  have h1 : (y * t) * x * (y * t)⁻¹ = y * x⁻¹ * y⁻¹ := by
    rw [mul_inv_rev, ht_inv]
    calc y * t * x * (t * y⁻¹) = y * (t * x * t) * y⁻¹ := by group
      _ = y * x⁻¹ * y⁻¹ := by rw [h_tx]
  have h2 : y * x⁻¹ * y⁻¹ = x := h1.symm.trans h_axa
  calc y * x * y⁻¹ = (y * x⁻¹ * y⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [h2]

/-- **Isaacs Lemma 2.14(a) (`c * t` は involution)**: `t` が `c` を invert すれば
`(c * t)² = 1`. 書籍の「`D` は相異なる involution `c * t` と `t` で生成される」の
involution 部分 (`c * t ≠ t` は `c ≠ 1` と同値). -/
theorem mul_sq_eq_one_of_conj_eq_inv {c t : D} (h_conj : t * c * t = c⁻¹) :
    (c * t) * (c * t) = 1 := by
  calc (c * t) * (c * t) = c * (t * c * t) := by group
    _ = c * c⁻¹ := by rw [h_conj]
    _ = 1 := mul_inv_cancel c

/-- **Isaacs Lemma 2.14(a) (生成)**: `C = ⟨c⟩` が index `2`, `t ∉ C` なら
`D = ⟨c * t, t⟩`. (`t` が involution である必要すらない; coset 分解のみで従う.) -/
theorem closure_mul_involution_eq_top {c t : D}
    (h_idx : (Subgroup.zpowers c).index = 2)
    (ht_not : t ∉ Subgroup.zpowers c) :
    Subgroup.closure {c * t, t} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have htm : t ∈ Subgroup.closure ({c * t, t} : Set D) :=
    Subgroup.subset_closure (by simp)
  have hctm : c * t ∈ Subgroup.closure ({c * t, t} : Set D) :=
    Subgroup.subset_closure (by simp)
  have hcm : c ∈ Subgroup.closure ({c * t, t} : Set D) := by
    have h1 := Subgroup.mul_mem _ hctm (Subgroup.inv_mem _ htm)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
  have hC_le : Subgroup.zpowers c ≤ Subgroup.closure ({c * t, t} : Set D) :=
    Subgroup.zpowers_le.mpr hcm
  by_cases hy : y ∈ Subgroup.zpowers c
  · exact hC_le hy
  · have ha : y * t ∈ Subgroup.zpowers c := mul_mem_of_notMem_of_notMem h_idx ht_not hy
    have h2 := Subgroup.mul_mem _ (hC_le ha) (Subgroup.inv_mem _ htm)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2

/-- **Isaacs Lemma 2.14(b) (`C` nontrivial)**: 相異なる元 `s ≠ t` で `s² = 1` なら
`s * t ≠ 1`, すなわち `C = ⟨s * t⟩` は nontrivial. -/
theorem mul_ne_one_of_ne {s t : D} (hs : s * s = 1) (hst : s ≠ t) : s * t ≠ 1 := by
  intro h
  apply hst
  have h2 : s * t = s * s := by rw [h, hs]
  exact (mul_left_cancel h2).symm

/-- **Isaacs Lemma 2.14(b) (`t ∉ C`)**: 相異なる nontrivial involution `s, t` について
`t ∉ ⟨s * t⟩`.

書籍の論法「cyclic group は involution を高々 1 つしか含まない」の実装: もし `t ∈ C` なら
`t` は `C` の全元と可換, 一方 `t` は `C` を反転する (`inv_by_two_involutions`) ので `C` の
全元が involution となり `C = {1, s * t}`. `t = 1` は `t` nontrivial に, `t = s * t` は
`s ≠ 1` に矛盾する. -/
theorem right_notMem_zpowers_mul {s t : D}
    (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    t ∉ Subgroup.zpowers (s * t) := by
  intro htC
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htC
  -- `t ∈ C` なら `C` の全元が involution.
  have h_sq : ∀ z ∈ Subgroup.zpowers (s * t), z * z = 1 := by
    intro z hz
    have h1 : t * z * t = z⁻¹ := inv_by_two_involutions hs ht hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h_comm : t * z = z * t := by
      rw [← hk, ← hm]
      exact (Commute.zpow_zpow_self (s * t) k m).eq
    have h2 : z⁻¹ = z := by
      calc z⁻¹ = t * z * t := h1.symm
        _ = z * (t * t) := by rw [h_comm]; group
        _ = z := by rw [ht, mul_one]
    have h3 := mul_inv_cancel z
    rwa [h2] at h3
  have hst_sq : (s * t) * (s * t) = 1 := h_sq _ (Subgroup.mem_zpowers _)
  have hst_sq' : (s * t) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hst_sq
  -- `t = (s * t) ^ k` は `1` か `s * t` のいずれかで, どちらも矛盾.
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h4 : (s * t) ^ k = 1 := by
      rw [hj, ← two_mul, zpow_mul, hst_sq', one_zpow]
    exact ht1 (by rw [← hk]; exact h4)
  · have h4 : (s * t) ^ k = s * t := by
      rw [hj, zpow_add, zpow_mul, hst_sq', one_zpow, one_mul, zpow_one]
    have h5 : s * t = t := h4.symm.trans hk
    have h6 : s * t = 1 * t := by rw [h5, one_mul]
    exact hs1 (mul_right_cancel h6)

/-- **Isaacs Lemma 2.14(b) (`s ∉ C`)**: 相異なる nontrivial involution `s, t` について
`s ∉ ⟨s * t⟩`. (`s ∈ C` なら `t = s⁻¹ · (s * t) ∈ C` となり `right_notMem_zpowers_mul`
に矛盾.) -/
theorem left_notMem_zpowers_mul {s t : D}
    (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    s ∉ Subgroup.zpowers (s * t) := by
  intro hsC
  refine right_notMem_zpowers_mul hs ht hs1 ht1 ?_
  have h1 : s⁻¹ * (s * t) ∈ Subgroup.zpowers (s * t) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hsC) (Subgroup.mem_zpowers _)
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1

/-- **Isaacs Lemma 2.14(b) (index)**: 相異なる nontrivial involution `s, t` が `D` を
生成するなら `|D : ⟨s * t⟩| = 2`.

証明は書籍どおり: `⟨{s, t}⟩` の coset 分解 (`mem_zpowers_or_mul_t_mem_of_mem_closure_pair`)
で任意の元が `C` か `C · t` に入り, `t ∉ C` (`right_notMem_zpowers_mul`) で 2 coset が
相異なる. -/
theorem index_zpowers_mul_eq_two {s t : D}
    (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hD : Subgroup.closure {s, t} = ⊤) :
    (Subgroup.zpowers (s * t)).index = 2 := by
  have ht_not := right_notMem_zpowers_mul hs ht hs1 ht1
  rw [Subgroup.index_eq_two_iff]
  refine ⟨t, fun b => ?_⟩
  have hb : b ∈ Subgroup.closure ({s, t} : Set D) := by
    rw [hD]; exact Subgroup.mem_top b
  rcases mem_zpowers_or_mul_t_mem_of_mem_closure_pair hs ht hb with hbC | ⟨x, hxC, hb_eq⟩
  · refine Or.inr ⟨hbC, fun hbt => ?_⟩
    have h1 : b⁻¹ * (b * t) ∈ Subgroup.zpowers (s * t) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hbC) hbt
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact ht_not h1
  · subst hb_eq
    refine Or.inl ⟨?_, fun hbC => ?_⟩
    · rwa [mul_assoc, ht, mul_one]
    · have h1 : x⁻¹ * (x * t) ∈ Subgroup.zpowers (s * t) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hxC) hbC
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
      exact ht_not h1

/-- **Isaacs Lemma 2.14(b) (capstone)**: 相異なる nontrivial involution `s, t` が生成する
群では, `C = ⟨s * t⟩` の外の元は全て involution — すなわち `D` は (`C` を witness に)
書籍の意味で dihedral. (a) と (b) の合成. -/
theorem sq_eq_one_of_notMem_zpowers_mul {s t : D}
    (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hD : Subgroup.closure {s, t} = ⊤) {y : D}
    (hy : y ∉ Subgroup.zpowers (s * t)) : y * y = 1 :=
  (forall_involution_iff_conj_eq_inv
      (index_zpowers_mul_eq_two hs ht hs1 ht1 hD)
      (right_notMem_zpowers_mul hs ht hs1 ht1) ht).mpr
    (inv_by_two_involutions hs ht (Subgroup.mem_zpowers _)) y hy

end

end OddOrder.Isaacs.Ch02
