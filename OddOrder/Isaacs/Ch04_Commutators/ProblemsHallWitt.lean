/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ProblemsIteratedCommutator
import OddOrder.Isaacs.Ch04_Commutators.ProblemsNilpotencyClass

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

/-! ### Problem 4B.2 -/

/-- 相対下降中心列の交換子評価 (Thm 4.11 の相対版; `↥S` の中の ⊤ 版を `S.subtype` で押し出す). -/
theorem commutator_lowerCentralSeries_le' (S : Subgroup G) (i j : ℕ) :
    ⁅Subgroup.lowerCentralSeries S i, Subgroup.lowerCentralSeries S j⁆
      ≤ Subgroup.lowerCentralSeries S (i + j + 1) := by
  rw [← Subgroup.top_subtype_lowerCentralSeries S i, ← Subgroup.top_subtype_lowerCentralSeries S j,
    ← Subgroup.top_subtype_lowerCentralSeries S (i + j + 1), ← Subgroup.map_commutator]
  exact Subgroup.map_mono (commutator_lowerCentralSeries_le i j)

/-- 特性部分群の join は特性. -/
theorem characteristic_sup (A K : Subgroup G) [A.Characteristic] [K.Characteristic] :
    (A ⊔ K).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [Subgroup.map_sup, Subgroup.characteristic_iff_map_eq.mp ‹A.Characteristic› φ,
    Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic› φ]

/-- **class ≤ 2 の元同士を可換に貼り合わせる**: `A`, `K` が正規, `⁅A,K⁆ = 1`, どちらも
class ≤ 2 なら `A ⊔ K` も class ≤ 2. -/
theorem lowerCentralSeries_sup_eq_bot {A K : Subgroup G} [A.Normal] [K.Normal]
    (hAK : ⁅A, K⁆ = ⊥) (hA : Subgroup.lowerCentralSeries A 2 = ⊥)
    (hK : Subgroup.lowerCentralSeries K 2 = ⊥) :
    Subgroup.lowerCentralSeries (A ⊔ K) 2 = ⊥ := by
  have hKA : ⁅K, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hAK
  set N : Subgroup G := ⁅A, A⁆ ⊔ ⁅K, K⁆ with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  have hAA : Subgroup.lowerCentralSeries A 1 = ⁅A, A⁆ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  have hKK : Subgroup.lowerCentralSeries K 1 = ⁅K, K⁆ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  have hA2 : ⁅(⁅A, A⁆ : Subgroup G), A⁆ = ⊥ := by
    rw [← hAA, ← Subgroup.lowerCentralSeries_succ]; exact hA
  have hK2 : ⁅(⁅K, K⁆ : Subgroup G), K⁆ = ⊥ := by
    rw [← hKK, ← Subgroup.lowerCentralSeries_succ]; exact hK
  have hKAle : (⁅K, A⁆ : Subgroup G) ≤ N := by rw [hKA]; exact bot_le
  have hAKle : (⁅A, K⁆ : Subgroup G) ≤ N := by rw [hAK]; exact bot_le
  -- 第 1 段: `⁅A ⊔ K, A ⊔ K⁆ ≤ N`
  have hfixA : ∀ a ∈ A, A ⊔ K ≤ commutatorMemLeft N a := by
    intro a ha
    refine sup_le (fun a' ha' => ?_) (fun k' hk' => ?_)
    · exact (le_sup_left : (⁅A, A⁆ : Subgroup G) ≤ N)
        (Subgroup.commutator_mem_commutator ha' ha)
    · exact hKAle (Subgroup.commutator_mem_commutator hk' ha)
  have hfixK : ∀ k ∈ K, A ⊔ K ≤ commutatorMemLeft N k := by
    intro k hk
    refine sup_le (fun a' ha' => ?_) (fun k' hk' => ?_)
    · exact hAKle (Subgroup.commutator_mem_commutator ha' hk)
    · exact (le_sup_right : (⁅K, K⁆ : Subgroup G) ≤ N)
        (Subgroup.commutator_mem_commutator hk' hk)
  have hstep1 : ⁅A ⊔ K, A ⊔ K⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    have hsub : A ⊔ K ≤ commutatorMemLeft N y := by
      refine sup_le (fun a ha => ?_) (fun k hk => ?_)
      · exact commutatorElement_mem_comm (show ⁅y, a⁆ ∈ N from hfixA a ha hy)
      · exact commutatorElement_mem_comm (show ⁅y, k⁆ ∈ N from hfixK k hk hy)
    exact hsub hx
  -- 第 2 段: `⁅N, A ⊔ K⁆ = ⊥`
  have hfixAA : ∀ w ∈ (⁅A, A⁆ : Subgroup G),
      A ⊔ K ≤ commutatorMemLeft (⊥ : Subgroup G) w := by
    intro w hw
    have hwA : w ∈ A := Subgroup.commutator_le_left A A hw
    refine sup_le (fun a ha => ?_) (fun k hk => ?_)
    · exact commutatorElement_mem_comm
        ((le_of_eq hA2) (Subgroup.commutator_mem_commutator hw ha))
    · exact (le_of_eq hKA) (Subgroup.commutator_mem_commutator hk hwA)
  have hfixKK : ∀ w ∈ (⁅K, K⁆ : Subgroup G),
      A ⊔ K ≤ commutatorMemLeft (⊥ : Subgroup G) w := by
    intro w hw
    have hwK : w ∈ K := Subgroup.commutator_le_left K K hw
    refine sup_le (fun a ha => ?_) (fun k hk => ?_)
    · exact (le_of_eq hAK) (Subgroup.commutator_mem_commutator ha hwK)
    · exact commutatorElement_mem_comm
        ((le_of_eq hK2) (Subgroup.commutator_mem_commutator hw hk))
  have hstep2 : ⁅N, A ⊔ K⁆ ≤ ⊥ := by
    refine Subgroup.commutator_le.2 fun z hz y hy => ?_
    have hsub : N ≤ commutatorMemLeft (⊥ : Subgroup G) y := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact commutatorElement_mem_comm
          (show ⁅y, w⁆ ∈ (⊥ : Subgroup G) from hfixAA w hw hy)
      · exact commutatorElement_mem_comm
          (show ⁅y, w⁆ ∈ (⊥ : Subgroup G) from hfixKK w hw hy)
    exact hsub hz
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono hstep1 le_rfl) hstep2)



/-- **Isaacs Problem 4B.2**: 冪零群は「`C_G(K) ⊆ K` かつ冪零類 ≤ 2」な特性部分群 `K` を持つ.

`K` を「特性かつ class ≤ 2」の中で極大に取る。`C := C_G(K)` として `C ⊆ K` を示す:
`A ≤ C` が特性で class ≤ 2 なら `A ⊔ K` も特性 class ≤ 2 (`lowerCentralSeries_sup_eq_bot`)
なので極大性から `A ≤ K` (吸収)。`C` 自身が class ≤ 2 ならこれで終わり。そうでなければ
Problem 4B.1 と同じく `A := γ_{c-1}(C)` (`c = class(C) ≥ 3`) が特性可換で吸収され `A ≤ K`、
すると `C = C_G(K) ≤ C_G(A)` から `⁅A, C⁆ = γ_c(C) = 1` となり `c` の最小性に矛盾. -/
theorem exists_characteristic_selfCentralizing_class_le_two [Finite G] [Group.IsNilpotent G] :
    ∃ K : Subgroup G, K.Characteristic ∧ Subgroup.lowerCentralSeries K 2 = ⊥ ∧
      Subgroup.centralizer (K : Set G) ≤ K := by
  classical
  obtain ⟨K, -, hKmax⟩ := Finite.exists_le_maximal (α := Subgroup G)
    (p := fun K : Subgroup G => K.Characteristic ∧ Subgroup.lowerCentralSeries K 2 = ⊥)
    (a := ⊥) ⟨inferInstance, by simp⟩
  obtain ⟨hKchar, hKcls⟩ := hKmax.prop
  haveI := hKchar
  refine ⟨K, hKchar, hKcls, ?_⟩
  set C : Subgroup G := Subgroup.centralizer (K : Set G) with hCdef
  haveI hCchar : C.Characteristic := by rw [hCdef]; infer_instance
  -- 吸収補題
  have habsorb : ∀ A : Subgroup G, A.Characteristic → Subgroup.lowerCentralSeries A 2 = ⊥ →
      A ≤ C → A ≤ K := by
    intro A hAchar hAcls hAC
    haveI := hAchar
    have hAK : ⁅A, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hAC
    have hle := hKmax.le_of_ge
      (⟨characteristic_sup A K, lowerCentralSeries_sup_eq_bot hAK hAcls hKcls⟩ :
        (A ⊔ K).Characteristic ∧ Subgroup.lowerCentralSeries (A ⊔ K) 2 = ⊥) le_sup_right
    exact le_trans le_sup_left hle
  by_cases hCcls : Subgroup.lowerCentralSeries C 2 = ⊥
  · exact habsorb C hCchar hCcls le_rfl
  · exfalso
    set c := Group.nilpotencyClass ↥C with hcdef
    have hcbot : Subgroup.lowerCentralSeries C c = ⊥ :=
      (nilpotencyClass_le_iff_lowerCentralSeries_eq_bot C).mp le_rfl
    have hc3 : 2 < c := by
      by_contra hcon
      exact hCcls (le_bot_iff.mp (le_trans
        (Subgroup.lowerCentralSeries_antitone C (by omega)) (le_of_eq hcbot)))
    set A : Subgroup G := Subgroup.lowerCentralSeries C (c - 2) with hAdef
    have hAchar : A.Characteristic := by rw [hAdef]; infer_instance
    have hAA : ⁅A, A⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (commutator_lowerCentralSeries_le' C (c - 2) (c - 2)) ?_)
      exact le_trans (Subgroup.lowerCentralSeries_antitone C
        (show c ≤ (c - 2) + (c - 2) + 1 by omega)) (le_of_eq hcbot)
    have hAcls : Subgroup.lowerCentralSeries A 2 = ⊥ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
        Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero, hAA]
      simp
    have hAC : A ≤ C := Subgroup.lowerCentralSeries_le_self C _
    have hAK : A ≤ K := habsorb A hAchar hAcls hAC
    -- `C` は `K ⊇ A` を中心化するので `⁅A, C⁆ = ⊥`
    have hCA : C ≤ Subgroup.centralizer (A : Set G) := by
      rw [hCdef]
      exact Subgroup.centralizer_le (by exact_mod_cast hAK)
    have hbot : Subgroup.lowerCentralSeries C (c - 1) = ⊥ := by
      rw [show c - 1 = (c - 2) + 1 by omega, Subgroup.lowerCentralSeries_succ, ← hAdef]
      rw [Subgroup.commutator_comm]
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hCA
    have := (nilpotencyClass_le_iff_lowerCentralSeries_eq_bot C).mpr hbot
    omega

end

end OddOrder.Isaacs.Ch04
