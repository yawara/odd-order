/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ProblemsIteratedCommutator

/-!
# Isaacs Chapter 4 — Problems 4B.1 / 4B.4 (three subgroups lemma の応用)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 4B (書籍 p. 131)。

* **4B.1** 冪零類が `2` を超える群は**中心的でない特性可換部分群**を持つ
  (`exists_characteristic_abelian_not_le_center`)
* **4B.4(a)** `Y` が `⁅X,Y⁆` を中心化すれば `Y'` は `X` を中心化する
  (`commutator_le_centralizer_of_centralizes`)
* **4B.4(b)** 同じ仮定で `⁅X,Y⁆` は可換 (`commutator_isCommutative_of_centralizes`)

4B.1 は下降中心列の**最後から 2 番目の項** `γ_{c-1}` が答え:
`⁅γ_{c-1}, γ_{c-1}⁆ ≤ γ_{2(c-1)} = 1` (`c ≥ 3` ゆえ `2(c-1) ≥ c+1`) で可換,
`⁅γ_{c-1}, G⁆ = γ_c ≠ 1` ゆえ中心的でない。特性性は下降中心列の項だから自動。

4B.4 はどちらも three subgroups lemma (`commutator_commutator_le_of_rotate`) の直接適用。
⚠ (b) は書籍が `X ⊴ G` を仮定するが, 実際には**不要** — `⁅X,Y⁆` が `X` で正規化される
(`le_normalizer_commutator_left`) ことだけ使えばよい。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problems 4B (p. 131) -/

variable {G : Type*} [Group G]

/-! ### Problem 4B.4 -/

/-- **Isaacs Problem 4B.4(a)**: `Y` が `⁅X,Y⁆` を中心化すれば `Y'` は `X` を中心化する.

three subgroups lemma を `(H₁, H₂, H₃) = (Y, Y, X)` で使う:
`⁅⁅Y,X⁆,Y⁆ = 1` と `⁅⁅X,Y⁆,Y⁆ = 1` から `⁅⁅Y,Y⁆,X⁆ = 1`. -/
theorem commutator_le_centralizer_of_centralizes {X Y : Subgroup G}
    (h : Y ≤ Subgroup.centralizer (⁅X, Y⁆ : Subgroup G)) :
    ⁅Y, Y⁆ ≤ Subgroup.centralizer (X : Subgroup G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
  have hXY : ⁅(⁅X, Y⁆ : Subgroup G), Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h
  refine le_bot_iff.mp ?_
  refine commutator_commutator_le_of_rotate (H₁ := Y) (H₂ := Y) (H₃ := X) ?_ (le_of_eq hXY)
  rw [Subgroup.commutator_comm Y X]
  exact le_of_eq hXY

/-- **Isaacs Problem 4B.4(b)**: `Y` が `⁅X,Y⁆` を中心化すれば `⁅X,Y⁆` は可換.

three subgroups lemma を `(H₁, H₂, H₃) = (X, Y, ⁅X,Y⁆)` で使う:
`⁅Y, ⁅X,Y⁆⁆ = 1` (仮定) と `⁅⁅⁅X,Y⁆, X⁆, Y⁆ ≤ ⁅⁅X,Y⁆, Y⁆ = 1`
(`X` は `⁅X,Y⁆` を正規化する) から `⁅⁅X,Y⁆, ⁅X,Y⁆⁆ = 1`.

⚠ 書籍は `X ⊴ G` を仮定するが不要. -/
theorem commutator_isCommutative_of_centralizes {X Y : Subgroup G}
    (h : Y ≤ Subgroup.centralizer (⁅X, Y⁆ : Subgroup G)) :
    ⁅(⁅X, Y⁆ : Subgroup G), (⁅X, Y⁆ : Subgroup G)⁆ = ⊥ := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hXY : ⁅(⁅X, Y⁆ : Subgroup G), Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h
  have hnorm : ⁅(⁅X, Y⁆ : Subgroup G), X⁆ ≤ ⁅X, Y⁆ :=
    commutator_le_of_le_normalizer (le_normalizer_commutator_left X Y)
  refine le_bot_iff.mp ?_
  refine commutator_commutator_le_of_rotate (H₁ := X) (H₂ := Y) (H₃ := ⁅X, Y⁆) ?_ ?_
  · rw [h]
    simp
  · exact le_trans (Subgroup.commutator_mono hnorm le_rfl) (le_of_eq hXY)

/-! ### Problem 4B.3 -/

/-- 上昇中心列の定義: `⁅Z_m, G⁆ ≤ Z_{m-1}`. -/
theorem commutator_upperCentralSeries_top_le (m : ℕ) :
    ⁅Subgroup.upperCentralSeries G m, (⊤ : Subgroup G)⁆
      ≤ Subgroup.upperCentralSeries G (m - 1) := by
  cases m with
  | zero =>
    rw [Subgroup.upperCentralSeries_zero]
    simp
  | succ n =>
    refine Subgroup.commutator_le.2 fun x hx y _ => ?_
    simpa using (Subgroup.mem_upperCentralSeries_succ_iff.mp hx) y

/-- **Isaacs Problem 4B.3**: `⁅G^i, Z_j⁆ ⊆ Z_{j-i}` (`G^i` = 下降中心列, `Z_j` = 上昇中心列).

mathlib の添字では `G^{k+1} = lowerCentralSeries ⊤ k` なので
`⁅lcs k, Z_j⁆ ≤ Z_{j-(k+1)}`. `k` の帰納で, 段は three subgroups lemma:
`⁅⁅⊤, Z_j⁆, G^{k+1}⁆ ≤ ⁅G^{k+1}, Z_{j-1}⁆ ≤ Z_{j-k-2}` と
`⁅⁅Z_j, G^{k+1}⁆, ⊤⁆ ≤ ⁅Z_{j-k-1}, ⊤⁆ ≤ Z_{j-k-2}`. -/
theorem commutator_lowerCentralSeries_upperCentralSeries_le (k : ℕ) :
    ∀ j : ℕ, ⁅Subgroup.lowerCentralSeries (⊤ : Subgroup G) k, Subgroup.upperCentralSeries G j⁆
      ≤ Subgroup.upperCentralSeries G (j - (k + 1)) := by
  induction k with
  | zero =>
    intro j
    rw [Subgroup.lowerCentralSeries_zero, Subgroup.commutator_comm]
    simpa using commutator_upperCentralSeries_top_le (G := G) j
  | succ k ih =>
    intro j
    rw [Subgroup.lowerCentralSeries_succ]
    refine commutator_commutator_le_of_rotate
      (H₁ := Subgroup.lowerCentralSeries (⊤ : Subgroup G) k) (H₂ := ⊤)
      (H₃ := Subgroup.upperCentralSeries G j) ?_ ?_
    · have h1 : ⁅(⊤ : Subgroup G), Subgroup.upperCentralSeries G j⁆
          ≤ Subgroup.upperCentralSeries G (j - 1) := by
        rw [Subgroup.commutator_comm]
        exact commutator_upperCentralSeries_top_le j
      refine le_trans (Subgroup.commutator_mono h1 le_rfl) ?_
      rw [Subgroup.commutator_comm]
      refine le_trans (ih (j - 1)) (le_of_eq (congrArg _ (by omega)))
    · have h2 : ⁅Subgroup.upperCentralSeries G j, Subgroup.lowerCentralSeries (⊤ : Subgroup G) k⁆
          ≤ Subgroup.upperCentralSeries G (j - (k + 1)) := by
        rw [Subgroup.commutator_comm]
        exact ih j
      refine le_trans (Subgroup.commutator_mono h2 le_rfl) ?_
      refine le_trans (commutator_upperCentralSeries_top_le (j - (k + 1)))
        (le_of_eq (congrArg _ (by omega)))

/-- **Isaacs Problem 4B.3** (系): `⁅G^i, Z_i⁆ = 1`. -/
theorem commutator_lowerCentralSeries_upperCentralSeries_eq_bot (i : ℕ) :
    ⁅Subgroup.lowerCentralSeries (⊤ : Subgroup G) i,
      Subgroup.upperCentralSeries G (i + 1)⁆ = ⊥ := by
  refine le_bot_iff.mp (le_trans
    (commutator_lowerCentralSeries_upperCentralSeries_le i (i + 1)) ?_)
  simp

/-! ### Problem 4B.1 -/

/-- **Isaacs Problem 4B.1**: 冪零類が `2` を超える群は**中心的でない特性可換部分群**を持つ.

`c = class(G)` に対し `γ_{c-1} = lowerCentralSeries ⊤ (c-2)` が答え. -/
theorem exists_characteristic_abelian_not_le_center [Group.IsNilpotent G]
    (hc : 2 < Group.nilpotencyClass G) :
    ∃ A : Subgroup G, A.Characteristic ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ¬ A ≤ Subgroup.center G := by
  set c := Group.nilpotencyClass G with hcdef
  set A : Subgroup G := Subgroup.lowerCentralSeries (⊤ : Subgroup G) (c - 2) with hA
  have htop : Subgroup.lowerCentralSeries (⊤ : Subgroup G) c = ⊥ :=
    Subgroup.lowerCentralSeries_nilpotencyClass
  refine ⟨A, inferInstance, ?_, ?_⟩
  · -- `⁅A, A⁆ ≤ γ_{2c-3} ≤ γ_c = 1`
    have hbot : ⁅A, A⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (commutator_lowerCentralSeries_le (c - 2) (c - 2)) ?_)
      refine le_trans (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)
        (show c ≤ (c - 2) + (c - 2) + 1 by omega)) (le_of_eq htop)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hbot ha)) b hb).symm
  · -- 中心に入るなら `γ_{c-1} = 1` となり類が下がる
    intro hcen
    have hbot : Subgroup.lowerCentralSeries (⊤ : Subgroup G) (c - 1) = ⊥ := by
      rw [show c - 1 = (c - 2) + 1 by omega, Subgroup.lowerCentralSeries_succ]
      refine le_bot_iff.mp (Subgroup.commutator_le.2 fun x hx y _ => ?_)
      have := Subgroup.mem_center_iff.mp (hcen hx) y
      rw [Subgroup.mem_bot, commutatorElement_def, ← this]
      group
    have := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
    omega

end

end OddOrder.Isaacs.Ch04
