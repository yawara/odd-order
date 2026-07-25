/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch04_Commutators.ProblemsWreathNonCommutator

/-!
# Isaacs Chapter 4 — Problem 4A.12(c) の `H = D₈` の場合

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.12(c) 後半 (書籍 p. 125)。

`H = D₈` (`DihedralGroup 4`) では **`m = 3` が取れる**, すなわち `|A| > 3` なら
Problem 4A.12(b) の不等式が成り立つ (`sum_lt_of_three_lt_card_dihedralFour`)。

これは `|𝒯(D₈)| ≤ 3` (`card_le_three_of_maximal_dihedralFour`) から従う。`D₈` の
可換部分群は必ず 3 つの指数 2 部分群

`⟨r⟩ = closure {r 1}`, `closure {r 2, sr 0}`, `closure {r 2, sr 1}`

のいずれかに含まれるので, 極大なものはこの 3 つしかない。`ZMod 4` の算術
(`2k = 0 ↔ k = 0 ∨ k = 2` 等) は `decide` で片付く。
-/

namespace OddOrder.Isaacs.Ch04

open DihedralGroup

section /- Problem 4A.12(c): `H = D₈` (p. 125) -/

/-! ### `ZMod 4` の算術 (すべて `decide`) -/

theorem zmod_four_of_sub_eq_add : ∀ i k : ZMod 4, i - k = i + k → k = 0 ∨ k = 2 := by decide

theorem zmod_four_of_sub_eq_sub : ∀ i j : ZMod 4, i - j = j - i → j = i ∨ j = i + 2 := by decide

theorem zmod_four_sub_two : ∀ i : ZMod 4, i - 2 = i + 2 := by decide

theorem zmod_four_add_two_sub_two : ∀ i : ZMod 4, i + 2 - 2 = i := by decide

theorem zmod_four_cases : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

/-! ### 3 つの候補 -/

/-- `D₈` の回転部分群 `⟨r⟩` (2 元生成の形で書いておく). -/
abbrev rotFour : Subgroup (DihedralGroup 4) :=
  Subgroup.closure ({r 1, r 1} : Set (DihedralGroup 4))

/-- `D₈` の Klein 4-群 `⟨r², sr i⟩`. -/
abbrev kleinFour (i : ZMod 4) : Subgroup (DihedralGroup 4) :=
  Subgroup.closure ({r 2, sr i} : Set (DihedralGroup 4))

theorem isAbelianTwoGen_rotFour : IsAbelianTwoGen rotFour :=
  isAbelianTwoGen_closure_pair rfl

theorem isAbelianTwoGen_kleinFour (i : ZMod 4) : IsAbelianTwoGen (kleinFour i) := by
  refine isAbelianTwoGen_closure_pair ?_
  rw [r_mul_sr, sr_mul_r]
  congr 1
  exact zmod_four_sub_two i

/-- `D₈` は可換でない (`r 1` と `sr 0` が非可換). -/
theorem not_isAbelianTwoGen_top :
    ¬ IsAbelianTwoGen (⊤ : Subgroup (DihedralGroup 4)) := by
  rintro ⟨hab, -⟩
  have := hab (r 1) (Subgroup.mem_top _) (sr 0) (Subgroup.mem_top _)
  rw [r_mul_sr, sr_mul_r] at this
  exact absurd this (by decide)

/-! ### 可換部分群は 3 つのいずれかに含まれる -/

/-- 鏡映を含む可換部分群は `⟨r², sr i⟩` に含まれる. -/
theorem le_kleinFour_of_mem {T : Subgroup (DihedralGroup 4)}
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {i : ZMod 4} (hi : sr i ∈ T) :
    T ≤ kleinFour i := by
  have hr2 : r 2 ∈ kleinFour i := Subgroup.subset_closure (by simp)
  have hsri : sr i ∈ kleinFour i := Subgroup.subset_closure (by simp)
  intro x hx
  match x with
  | r k =>
    -- `r k` が `sr i` と可換 ⟹ `k = 0` or `k = 2`
    have hcomm := hab (r k) hx (sr i) hi
    rw [r_mul_sr, sr_mul_r] at hcomm
    have heq : i - k = i + k := by injection hcomm
    rcases zmod_four_of_sub_eq_add i k heq with rfl | rfl
    · rw [← one_def]
      exact Subgroup.one_mem _
    · exact hr2
  | sr j =>
    -- `sr j` が `sr i` と可換 ⟹ `j = i` or `j = i + 2`
    have hcomm := hab (sr j) hx (sr i) hi
    rw [sr_mul_sr, sr_mul_sr] at hcomm
    have heq : i - j = j - i := by injection hcomm
    rcases zmod_four_of_sub_eq_sub i j heq with rfl | rfl
    · exact hsri
    · have hmul : (r 2 : DihedralGroup 4) * sr i = sr (i + 2) := by
        rw [r_mul_sr]
        congr 1
        exact zmod_four_sub_two i
      rw [← hmul]
      exact Subgroup.mul_mem _ hr2 hsri

/-- 鏡映を含まない部分群は回転部分群に含まれる. -/
theorem le_rotFour_of_forall {T : Subgroup (DihedralGroup 4)}
    (h : ∀ i : ZMod 4, sr i ∉ T) : T ≤ rotFour := by
  have hr1 : r 1 ∈ rotFour := Subgroup.subset_closure (by simp)
  intro x hx
  match x with
  | r k =>
    have hpow : (r 1 : DihedralGroup 4) ^ (k.val) = r k := by
      rw [r_one_pow]
      congr 1
      simp
    rw [← hpow]
    exact Subgroup.pow_mem _ hr1 _
  | sr j => exact absurd hx (h j)

/-! ### `|𝒯(D₈)| ≤ 3` -/

/-- `D₈` の「可換 2 元生成」極大部分群は 3 つの候補のいずれか. -/
theorem maximal_eq_of_dihedralFour {T : Subgroup (DihedralGroup 4)}
    (hT : Maximal IsAbelianTwoGen T) : T = rotFour ∨ T = kleinFour 0 ∨ T = kleinFour 1 := by
  by_cases hsr : ∃ i : ZMod 4, sr i ∈ T
  · obtain ⟨i, hi⟩ := hsr
    have hle : T ≤ kleinFour i := le_kleinFour_of_mem hT.prop.1 hi
    have heq : T = kleinFour i :=
      le_antisymm hle (hT.le_of_ge (isAbelianTwoGen_kleinFour i) hle)
    -- `kleinFour i` は `i` の偶奇でしか決まらない (`sr (i+2) = r 2 · sr i`)
    have hshift : ∀ j : ZMod 4, kleinFour (j + 2) = kleinFour j := by
      intro j
      have hmem : (sr (j + 2) : DihedralGroup 4) = r 2 * sr j := by
        rw [r_mul_sr]
        congr 1
        exact (zmod_four_sub_two j).symm
      have hmem' : (sr j : DihedralGroup 4) = r 2 * sr (j + 2) := by
        rw [r_mul_sr]
        congr 1
        exact (zmod_four_add_two_sub_two j).symm
      refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) (Subgroup.closure_le _ |>.mpr ?_)
      · rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · rw [hmem]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
      · rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · rw [hmem']
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
    have hi2 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := zmod_four_cases i
    rcases hi2 with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr heq)
    · refine Or.inr (Or.inl ?_)
      rw [heq, show (2 : ZMod 4) = 0 + 2 by decide, hshift]
    · refine Or.inr (Or.inr ?_)
      rw [heq, show (3 : ZMod 4) = 1 + 2 by decide, hshift]
  · have hsr' : ∀ i : ZMod 4, sr i ∉ T := fun i hi => hsr ⟨i, hi⟩
    have hle : T ≤ rotFour := le_rotFour_of_forall hsr'
    exact Or.inl (le_antisymm hle (hT.le_of_ge isAbelianTwoGen_rotFour hle))

/-- **`|𝒯(D₈)| ≤ 3`**. -/
theorem card_le_three_of_maximal_dihedralFour (𝒯 : Finset (Subgroup (DihedralGroup 4)))
    (h𝒯 : ∀ T ∈ 𝒯, Maximal (IsAbelianTwoGen (Q := DihedralGroup 4)) T) : 𝒯.card ≤ 3 := by
  classical
  have hsub : 𝒯 ⊆ {rotFour, kleinFour 0, kleinFour 1} := by
    intro T hT
    rcases maximal_eq_of_dihedralFour (h𝒯 T hT) with h | h | h <;> simp [h]
  calc 𝒯.card ≤ ({rotFour, kleinFour 0, kleinFour 1} :
        Finset (Subgroup (DihedralGroup 4))).card := Finset.card_le_card hsub
    _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
        simp

/-! ### Problem 4A.12(c) の `D₈` の場合 -/

/-- **Isaacs Problem 4A.12(c)** (`H = D₈`): `|A| > 3` なら (b) の不等式が成り立つ. -/
theorem sum_lt_of_three_lt_card_dihedralFour {D : Type*} [CommGroup D] [Finite D]
    {𝒯 : Finset (Subgroup (DihedralGroup 4))}
    (h𝒯 : ∀ T ∈ 𝒯, Maximal (IsAbelianTwoGen (Q := DihedralGroup 4)) T)
    (hD : 3 < Nat.card D) :
    ∑ T ∈ 𝒯, Nat.card D ^ (Nat.card (DihedralGroup 4) - T.index)
      < Nat.card D ^ (Nat.card (DihedralGroup 4) - 1) :=
  sum_lt_of_card_lt h𝒯 not_isAbelianTwoGen_top
    (lt_of_le_of_lt (card_le_three_of_maximal_dihedralFour 𝒯 h𝒯) hD)

end

end OddOrder.Isaacs.Ch04
