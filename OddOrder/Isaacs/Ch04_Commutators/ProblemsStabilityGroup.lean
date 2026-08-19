/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Mann
import OddOrder.Isaacs.Ch04_Commutators.ProblemsIteratedCommutator
import Mathlib.GroupTheory.IsSubnormal

/-!
# Isaacs Chapter 4 — Problems 4C (安定化群)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 4C (書籍 p. 137)。

`A` が `G` に自己同型で作用するとき, Isaacs は `A` と `G` をともに半直積
`Γ = G ⋊ A` の部分群とみなして交換子 `⁅G, A⁆` を `Γ` の中で計算する (§4C 冒頭, p. 131)。
本ファイルもその流儀に従い, **周囲群 `Γ` の部分群 `G`, `A`** に対する形で述べる
(半直積 `G ⋊[φ] A` はその特別な場合で, `inl`/`inr` の像を取ればよい)。

「`A` が鎖 `1 = H₀ ⊆ H₁ ⊆ ⋯ ⊆ H_m = G` を **stabilize** する」= 「`H_{i-1}` の `H_i`
における各右剰余類が `A`-不変」は, 交換子の言葉で `⁅H i, A⁆ ≤ H (i-1)` と同値
(`StabilizesChain`)。

## 主結果

* **4C.1** `exists_stabilizes_isSubnormal_chain` — `A` が鎖を stabilize するなら
  **部分正規部分群の鎖**も stabilize する。その鎖は反復交換子
  `M i = ⁅G, A; m - i⁆` (`commIterate`, Problem 4A.9) が与える。
* **4C.2** `StabilizesChain.nilpotencyClass_le` — `A` が **正規**部分群の鎖を faithful に
  stabilize するなら `A` は冪零で class `≤ m - 1`。
* **4C.3** `commutator_commutator_eq_bot_of_trivial_on_normal` — `A` が `N ⊴ G` に自明に
  作用するなら `N` は `⁅G, A⁆` を中心化する。

4C.1 / 4C.2 は書籍の文言 (有限鎖 `1 = H₀ ⊆ ⋯ ⊆ H_m = G`, 条件は `0 < i ≤ m` のみ) に
そのまま対応する版 `exists_stabilizes_isSubnormal_chain_of_finite` /
`nilpotencyClass_le_of_stabilizes_finite_normal_chain` も用意した。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problems 4C: 安定化群 (p. 137) -/

variable {Γ : Type*} [Group Γ]

/-! ### 鎖の stabilize -/

/-- **`A` が部分群の鎖 `H` を stabilize する** (Isaacs §4C, Problems 4C.1/4C.2)。

Isaacs の定義は「`H (i-1)` の `H i` における各右剰余類が `A`-不変」だが, これは交換子の
言葉で `⁅H i, A⁆ ≤ H (i-1)` と同値。鎖の上端 (`H m = G`) は用途ごとに変わるので
フィールドには含めない。 -/
structure StabilizesChain (H : ℕ → Subgroup Γ) (A : Subgroup Γ) : Prop where
  /-- 鎖は `1` から始まる. -/
  base : H 0 = ⊥
  /-- 各段で `A` との交換子はちょうど 1 段下がる. -/
  step : ∀ i, ⁅H (i + 1), A⁆ ≤ H i

namespace StabilizesChain

variable {H : ℕ → Subgroup Γ} {A : Subgroup Γ}

/-- `step` の切り捨て減算版 (`i = 0` の場合は `H 0 = ⊥` から従う). -/
theorem commutator_le_pred (hs : StabilizesChain H A) (i : ℕ) :
    ⁅H i, A⁆ ≤ H (i - 1) := by
  cases i with
  | zero =>
    rw [Nat.zero_sub, hs.base, Subgroup.commutator_bot_left]
  | succ i => simpa using hs.step i

/-- **鎖の各項と `A` の下降中心列の交換子評価**: `⁅H i, γ_{j+1}(A)⁆ ≤ H (i - (j+1))`。

これが Problem 4C.2 の核心。`j` についての帰納法で, 各段は Isaacs Cor 4.10
(three subgroups lemma の mod `N` 形 `commutator_commutator_le_of_rotate`) を
`N = H (i - (j+2))` に適用する。ここで **`H i` が `Γ` で正規**であることが本質的
(4C.2 が「正規部分群の鎖」を要求する理由)。 -/
theorem commutator_lowerCentralSeries_le (hs : StabilizesChain H A)
    (hnorm : ∀ i, (H i).Normal) (j : ℕ) :
    ∀ i, ⁅H i, Subgroup.lowerCentralSeries A j⁆ ≤ H (i - (j + 1)) := by
  induction j with
  | zero =>
    intro i
    simpa using hs.commutator_le_pred i
  | succ j ih =>
    intro i
    have := hnorm (i - (j + 2))
    -- `⁅⁅A, H i⁆, γ_{j+1}(A)⁆ ≤ H (i - (j+2))`
    have h1 : ⁅⁅A, H i⁆, Subgroup.lowerCentralSeries A j⁆ ≤ H (i - (j + 2)) := by
      have hA : ⁅A, H i⁆ ≤ H (i - 1) := by
        rw [Subgroup.commutator_comm]
        exact hs.commutator_le_pred i
      refine le_trans (Subgroup.commutator_mono hA le_rfl) ?_
      have hih := ih (i - 1)
      rwa [show i - 1 - (j + 1) = i - (j + 2) by omega] at hih
    -- `⁅⁅H i, γ_{j+1}(A)⁆, A⁆ ≤ H (i - (j+2))`
    have h2 : ⁅⁅H i, Subgroup.lowerCentralSeries A j⁆, A⁆ ≤ H (i - (j + 2)) := by
      refine le_trans (Subgroup.commutator_mono (ih i) le_rfl) ?_
      have hst := hs.commutator_le_pred (i - (j + 1))
      rwa [show i - (j + 1) - 1 = i - (j + 2) by omega] at hst
    have h3 := commutator_commutator_le_of_rotate
      (H₁ := Subgroup.lowerCentralSeries A j) (H₂ := A) (H₃ := H i)
      (N := H (i - (j + 2))) h1 h2
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm,
      show j + 1 + 1 = j + 2 from rfl]
    exact h3

/-- **`A` の下降中心列は `m - 1` 段で消える**。

`A` が `H m` を忠実に安定化する (`A ⊓ C_Γ(H m) = 1`) ことが faithfulness の内容。 -/
theorem lowerCentralSeries_eq_bot (hs : StabilizesChain H A)
    (hnorm : ∀ i, (H i).Normal) {m : ℕ}
    (hfaithful : A ⊓ Subgroup.centralizer (H m : Set Γ) = ⊥) :
    Subgroup.lowerCentralSeries A (m - 1) = ⊥ := by
  have hkey := hs.commutator_lowerCentralSeries_le hnorm (m - 1) m
  rw [show m - (m - 1 + 1) = 0 by omega, hs.base, le_bot_iff] at hkey
  have hcent : Subgroup.lowerCentralSeries A (m - 1) ≤ Subgroup.centralizer (H m : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hkey
  have hle : Subgroup.lowerCentralSeries A (m - 1) ≤ A :=
    A.lowerCentralSeries_antitone (Nat.zero_le _)
  rw [eq_bot_iff, ← hfaithful]
  exact le_inf hle hcent

/-- **Isaacs Problem 4C.2**: `A` が `G = H m` の**正規**部分群の鎖を忠実に stabilize するなら,
`A` は冪零で class は `m - 1` 以下。

faithfulness は「`A` の元で `H m` を中心化するものは `1` のみ」(`A ⊓ C_Γ(H m) = 1`) の形。
半直積 `Γ = G ⋊[φ] A` では `φ` が単射であることに他ならない。

⚠ 書籍は `m ≥ 1` を暗黙に仮定するが不要 (`m = 0` なら `G = H 0 = 1` で faithfulness が
`A = 1` を強いるので結論は自明に成立する)。 -/
theorem nilpotencyClass_le (hs : StabilizesChain H A)
    (hnorm : ∀ i, (H i).Normal) {m : ℕ}
    (hfaithful : A ⊓ Subgroup.centralizer (H m : Set Γ) = ⊥) :
    Group.nilpotencyClass ↥A ≤ m - 1 :=
  nilpotencyClass_le_of_lowerCentralSeries_eq_bot
    (hs.lowerCentralSeries_eq_bot hnorm hfaithful)

/-- Problem 4C.2 の冪零性の部分 (class の評価を落とした形). -/
theorem isNilpotent (hs : StabilizesChain H A)
    (hnorm : ∀ i, (H i).Normal) {m : ℕ}
    (hfaithful : A ⊓ Subgroup.centralizer (H m : Set Γ) = ⊥) :
    Group.IsNilpotent ↥A :=
  Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot
    (hs.lowerCentralSeries_eq_bot (m := m) hnorm hfaithful)

end StabilizesChain

/-- 正規部分群 `N ⊴ Γ` は任意の `A` に正規化される. -/
theorem le_normalizer_of_normal (N A : Subgroup Γ) [N.Normal] :
    A ≤ Subgroup.normalizer (N : Set Γ) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›]
  exact le_top

/-! ### 有限の鎖からの構成

Isaacs の鎖は `1 = H₀ ⊆ ⋯ ⊆ H_m = G` と有限だが, `StabilizesChain` は添字を `ℕ` 全体で
取る。両者は `H` を上端 `G` で延長する (= `H (min i m)` を取る) ことで橋渡しできる:
`G ⊴ Γ` なら `⁅G, A⁆ ≤ G` なので延長部分の条件は自動的に満たされる。 -/

/-- 有限の鎖 `1 = H₀ ⊆ ⋯ ⊆ H_m = G` を上端 `G` で延長すると `StabilizesChain` になる. -/
theorem stabilizesChain_min {G A : Subgroup Γ} [G.Normal] {H : ℕ → Subgroup Γ} {m : ℕ}
    (hbase : H 0 = ⊥) (hGm : H m = G) (hstep : ∀ i < m, ⁅H (i + 1), A⁆ ≤ H i) :
    StabilizesChain (fun i => H (min i m)) A := by
  refine ⟨by simpa using hbase, fun i => ?_⟩
  rcases Nat.lt_or_ge i m with hi | hi
  · rw [show min (i + 1) m = i + 1 by omega, show min i m = i by omega]
    exact hstep i hi
  · rw [show min (i + 1) m = m by omega, show min i m = m by omega, hGm]
    exact commutator_le_of_le_normalizer (le_normalizer_of_normal G A)

/-! ### Problem 4C.1: 部分正規部分群の鎖への取り替え -/

/-- 反復交換子列は添字について単調減少 (`commIterate_succ_le` の一般段). -/
theorem commIterate_le_commIterate_of_le {N A : Subgroup Γ}
    (hA : A ≤ Subgroup.normalizer (N : Set Γ)) {a b : ℕ} (hab : a ≤ b) :
    commIterate N A b ≤ commIterate N A a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine le_trans ?_ ih
    rw [show a + (k + 1) = a + k + 1 by omega]
    exact commIterate_succ_le hA (a + k)

/-- **反復交換子列 `⁅G, A; j⁆` の各項は `Γ` で部分正規**。

`⁅L, A⁆` は `L` に正規化される (`le_normalizer_commutator_left`, Problem 4A.9) ので,
`⁅G, A; j+1⁆ ⊴ ⁅G, A; j⁆`。`⁅G, A; 0⁆ = G ⊴ Γ` から帰納。 -/
theorem isSubnormal_commIterate (G A : Subgroup Γ) [G.Normal] (j : ℕ) :
    (commIterate G A j).IsSubnormal := by
  have hA : A ≤ Subgroup.normalizer (G : Set Γ) := le_normalizer_of_normal G A
  induction j with
  | zero => exact ‹G.Normal›.isSubnormal
  | succ j ih =>
    refine Subgroup.IsSubnormal.step _ (commIterate G A j) (commIterate_succ_le hA j) ih ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (commIterate_succ_le hA j)]
    exact le_normalizer_commutator_left _ _

/-- 反復交換子列の各段は部分正規段: `⁅G, A; j+1⁆ ⊴ ⁅G, A; j⁆`. -/
theorem normal_subgroupOf_commIterate_succ (G A : Subgroup Γ) [G.Normal] (j : ℕ) :
    ((commIterate G A (j + 1)).subgroupOf (commIterate G A j)).Normal := by
  have hA : A ≤ Subgroup.normalizer (G : Set Γ) := le_normalizer_of_normal G A
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (commIterate_succ_le hA j)]
  exact le_normalizer_commutator_left _ _

/-- 安定化された鎖は反復交換子列を上から押さえる: `⁅G, A; j⁆ ≤ H (m - j)`. -/
theorem commIterate_le_of_stabilizesChain {G A : Subgroup Γ} {H : ℕ → Subgroup Γ}
    (hs : StabilizesChain H A) {m : ℕ} (hGm : H m = G) (j : ℕ) :
    commIterate G A j ≤ H (m - j) := by
  induction j with
  | zero => rw [commIterate_zero, Nat.sub_zero, hGm]
  | succ j ih =>
    rw [commIterate_succ]
    refine le_trans (Subgroup.commutator_mono ih le_rfl) ?_
    have hst := hs.commutator_le_pred (m - j)
    rwa [show m - j - 1 = m - (j + 1) by omega] at hst

/-- **Isaacs Problem 4C.1**: `A` が `G ⊴ Γ` の部分群の鎖 `H` (長さ `m`) を stabilize するなら,
`A` は **部分正規部分群の鎖**も stabilize する。

具体的な鎖は反復交換子 `M i = ⁅G, A; m - i⁆` (`commIterate`, Problem 4A.9)。得られる鎖は
`⊥` から `G` まで単調増加で, 各項は `Γ` でも `G` (`subgroupOf`) でも部分正規, さらに
各項が次の項で正規という強い形の部分正規鎖になっている。 -/
theorem exists_stabilizes_isSubnormal_chain {G A : Subgroup Γ} [G.Normal]
    {H : ℕ → Subgroup Γ} (hs : StabilizesChain H A) {m : ℕ} (hGm : H m = G) :
    ∃ M : ℕ → Subgroup Γ, StabilizesChain M A ∧ M m = G ∧ Monotone M ∧
      (∀ i, M i ≤ G) ∧ (∀ i, (M i).IsSubnormal) ∧
      (∀ i, ((M i).subgroupOf G).IsSubnormal) ∧
      (∀ i, ((M i).subgroupOf (M (i + 1))).Normal) := by
  have hA : A ≤ Subgroup.normalizer (G : Set Γ) := le_normalizer_of_normal G A
  refine ⟨fun i => commIterate G A (m - i), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M 0 = ⁅G, A; m⁆ = ⊥`
    have hle := commIterate_le_of_stabilizesChain hs hGm m
    rw [Nat.sub_self, hs.base, le_bot_iff] at hle
    simpa using hle
  · -- `⁅M (i+1), A⁆ ≤ M i`
    intro i
    rcases Nat.lt_or_ge i m with hi | hi
    · have hidx : m - (i + 1) + 1 = m - i := by omega
      change ⁅commIterate G A (m - (i + 1)), A⁆ ≤ commIterate G A (m - i)
      rw [← commIterate_succ, hidx]
    · have hi1 : m - (i + 1) = 0 := by omega
      have hi0 : m - i = 0 := by omega
      change ⁅commIterate G A (m - (i + 1)), A⁆ ≤ commIterate G A (m - i)
      rw [hi1, hi0, commIterate_zero]
      exact commutator_le_of_le_normalizer hA
  · -- `M m = G`
    simp
  · -- monotone
    intro i j hij
    exact commIterate_le_commIterate_of_le hA (by omega)
  · exact fun i => commIterate_le_base hA _
  · exact fun i => isSubnormal_commIterate G A _
  · exact fun i => (isSubnormal_commIterate G A _).comap G.subtype
  · -- 各項が次の項で正規
    intro i
    rcases Nat.lt_or_ge i m with hi | hi
    · have hidx : m - i = m - (i + 1) + 1 := by omega
      change ((commIterate G A (m - i)).subgroupOf (commIterate G A (m - (i + 1)))).Normal
      rw [hidx]
      exact normal_subgroupOf_commIterate_succ G A _
    · have hi1 : m - (i + 1) = 0 := by omega
      have hi0 : m - i = 0 := by omega
      change ((commIterate G A (m - i)).subgroupOf (commIterate G A (m - (i + 1)))).Normal
      rw [hi0, hi1]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).mpr Subgroup.le_normalizer

/-! ### 有限鎖版 (Isaacs の文言に直接対応する形) -/

/-- **Isaacs Problem 4C.1** (有限鎖版): `A` が `G ⊴ Γ` の部分群の有限鎖
`1 = H₀ ⊆ ⋯ ⊆ H_m = G` を stabilize するなら, `A` は部分正規部分群の鎖も stabilize する. -/
theorem exists_stabilizes_isSubnormal_chain_of_finite
    {G A : Subgroup Γ} [G.Normal] {H : ℕ → Subgroup Γ} {m : ℕ}
    (hbase : H 0 = ⊥) (hGm : H m = G) (hstep : ∀ i < m, ⁅H (i + 1), A⁆ ≤ H i) :
    ∃ M : ℕ → Subgroup Γ, StabilizesChain M A ∧ M m = G ∧ Monotone M ∧
      (∀ i, M i ≤ G) ∧ (∀ i, (M i).IsSubnormal) ∧
      (∀ i, ((M i).subgroupOf G).IsSubnormal) ∧
      (∀ i, ((M i).subgroupOf (M (i + 1))).Normal) :=
  exists_stabilizes_isSubnormal_chain (stabilizesChain_min hbase hGm hstep)
    (by simpa using hGm)

/-- **Isaacs Problem 4C.2** (有限鎖版): `A` が `G ⊴ Γ` の**正規**部分群の有限鎖
`1 = H₀ ⊆ ⋯ ⊆ H_m = G` を忠実に stabilize するなら, `A` は冪零で class は `m - 1` 以下.

faithfulness は「`G` を中心化する `A` の元は `1` のみ」(`A ⊓ C_Γ(G) = 1`)。 -/
theorem nilpotencyClass_le_of_stabilizes_finite_normal_chain
    {G A : Subgroup Γ} [G.Normal] {H : ℕ → Subgroup Γ} {m : ℕ}
    (hbase : H 0 = ⊥) (hGm : H m = G) (hnorm : ∀ i ≤ m, (H i).Normal)
    (hstep : ∀ i < m, ⁅H (i + 1), A⁆ ≤ H i)
    (hfaithful : A ⊓ Subgroup.centralizer (G : Set Γ) = ⊥) :
    Group.nilpotencyClass ↥A ≤ m - 1 := by
  refine (stabilizesChain_min hbase hGm hstep).nilpotencyClass_le (m := m)
    (fun i => hnorm _ (min_le_right i m)) ?_
  simpa [hGm] using hfaithful

/-! ### Problem 4C.3 -/

/-- **Isaacs Problem 4C.3**: `A` が `N ⊴ G` に自明に作用する (`⁅N, A⁆ = 1`) なら,
`N` は `⁅G, A⁆` を中心化する。

three subgroups lemma を `(G, A, N)` に適用するだけ: `⁅⁅A, N⁆, G⁆ = 1` は仮定から,
`⁅⁅N, G⁆, A⁆ ≤ ⁅N, A⁆ = 1` は `N ⊴ G`。 -/
theorem commutator_commutator_eq_bot_of_trivial_on_normal {G A N : Subgroup Γ}
    (hN : G ≤ Subgroup.normalizer (N : Set Γ)) (htriv : ⁅N, A⁆ = ⊥) :
    ⁅N, ⁅G, A⁆⁆ = ⊥ := by
  have h1 : ⁅⁅A, N⁆, G⁆ = ⊥ := by
    rw [Subgroup.commutator_comm A N, htriv, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅N, G⁆, A⁆ = ⊥ := by
    have hle : ⁅⁅N, G⁆, A⁆ ≤ ⁅N, A⁆ :=
      Subgroup.commutator_mono (commutator_le_of_le_normalizer hN) le_rfl
    rw [htriv] at hle
    exact le_bot_iff.mp hle
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := G) (H₂ := A) (H₃ := N) h1 h2
  rw [Subgroup.commutator_comm]
  exact h3

/-- **Isaacs Problem 4C.3** (中心化群の形): `N ⊴ G` に `A` が自明に作用するなら
`N ≤ C_Γ(⁅G, A⁆)`. -/
theorem le_centralizer_commutator_of_trivial_on_normal {G A N : Subgroup Γ}
    (hN : G ≤ Subgroup.normalizer (N : Set Γ)) (htriv : ⁅N, A⁆ = ⊥) :
    N ≤ Subgroup.centralizer ((⁅G, A⁆ : Subgroup Γ) : Set Γ) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_trivial_on_normal hN htriv)

end

end OddOrder.Isaacs.Ch04
