/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.OrderIsoNat
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.GroupTheory.ThompsonSubgroup

/-!
# BG Appendix B: The Puig Subgroup `L(S)`

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Appendix B (pp. 139-144), mmd L4517-4642.

本ファイルは **定義 (L4532-4542) + Lemma B.1 (L4544-4588) + Lemma B.2 (L4590-4642)** を扱う.
Lemma B.3 / Theorem B.4 (= Thm 6.2 代替, `thmA5` 依存) は A.5 完成後の別ファイル.

## 役割

Isaacs FGT は Glauberman `Z(J)`-定理 (= BG Thm 6.2) を明示的に省く (Isaacs p.217). no-Gorenstein
方針下では **App.B (Puig `L(S)`) こそが Thm 6.2 の唯一の自己完結代替**. Lemma B.1-B.2 はその基盤.
mini-roadmap: [`appB_puig.md`](../../notes/bg/appB_puig.md),
routing: [`bg_s6_appAB_route_2026_05_28.md`](../../notes/meta/bg_s6_appAB_route_2026_05_28.md).

## 設計: 相対版 `…In` を primitive にする

教科書の `L_n(H)` は「`H` を群とみなした」部分群列だが, Lemma B.3 は `L_*(S) ⊆ L_*(T) ⊆ …`
のように **`G` の異なる部分群 `S`, `T` に対する `L`-列を比較**する. これを `G` の部分群として
直接型付けるため, 本ファイルは **`H` 内で計算し `G` の部分群として実現する相対版**
`lRelIn H X`, `lNIn H n`, `lOddIn H`, `lStarIn H` を primitive とし, 教科書の `L_G(X)`,
`L_n(G)`, `L(G)`, `L_*(G)` を `H = ⊤` の特殊化 `lRel`, `lN G`, `lOdd G`, `lStar G` で与える.

`H` 内の abelian 部分群 ⇔ `G` の部分群で `≤ H` なるもの. normalized-by 条件は `G`-normalizer で
表現する (`X ≤ H` の文脈で `H`-normalizer と一致).

## Main definitions

* `OddOrder.BG.AppB.lRelIn H X` — `L_H(X)` (`L4532`): `X` で正規化される `H` 内 abelian 部分群の上限.
* `OddOrder.BG.AppB.lNIn H n` — `L_n` 列 (`L4536`): `L_0 = ⊥`, `L_{n+1} = L_H(L_n)`.
* `OddOrder.BG.AppB.lOddIn H` / `lStarIn H` — `L(H) = ⨅ L_{2n+1}` / `L_*(H) = ⨆ L_{2n}` (`L4542`).
* `lRel`, `lN G`, `lOdd G`, `lStar G` — 絶対版 (`H = ⊤`).

## Main results (Lemma B.1, B.2)

* `lRelIn_anti_right` — **B.1(a)** (`L4546`): `X ⊆ Y ⇒ L_H(Y) ⊆ L_H(X)`.
* `lNIn_even_mono` / `lNIn_odd_anti` / `lNIn_even_le_odd` — **B.1(b)** (`L4547`): 偶増加・奇減少・偶 ≤ 奇.
* `lStarIn_le_lOddIn` — **B.1(d)** (`L4549`): `L_*(H) ⊆ L(H)`.
-/

namespace OddOrder.BG.AppB

variable {G : Type*} [Group G]

/-! ### 定義 (BG App.B, L4532-4542) -/

/-- **`L_H(X)`** (BG App.B notation, L4532, `H` 相対版): `X` に正規化される `H` 内 abelian
部分群すべての上限. 「`X → Y` (`Y` は `X` に正規化される abelian 部分群で生成) なる最大の `Y`」を
`H` 内 (= `G` の部分群で `≤ H`) に制限したもの. `lRel X := lRelIn ⊤ X` が教科書の `L_G(X)`. -/
def lRelIn (H X : Subgroup G) : Subgroup G :=
  ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ A ≤ H ∧
      X ≤ Subgroup.normalizer (A : Set G)}, A

/-- **`L_n(H)`** (BG App.B, L4536): `L_0 = ⊥`, `L_{n+1}(H) = L_H(L_n(H))`. -/
def lNIn (H : Subgroup G) : ℕ → Subgroup G
  | 0 => ⊥
  | (n + 1) => lRelIn H (lNIn H n)

/-- **`L(H)`** (BG App.B, L4542): odd-indexed limit `⨅_n L_{2n+1}(H)`. -/
def lOddIn (H : Subgroup G) : Subgroup G := ⨅ n, lNIn H (2 * n + 1)

/-- **`L_*(H)`** (BG App.B, L4542): even-indexed limit `⨆_n L_{2n}(H)`. -/
def lStarIn (H : Subgroup G) : Subgroup G := ⨆ n, lNIn H (2 * n)

/-- **`L_G(X)`** (BG App.B, L4532): 絶対版 `lRelIn ⊤ X`. -/
def lRel (X : Subgroup G) : Subgroup G := lRelIn ⊤ X

/-- **`L_n(G)`** (BG App.B, L4536): 絶対版 `lNIn ⊤ n`. -/
def lN (G : Type*) [Group G] (n : ℕ) : Subgroup G := lNIn (⊤ : Subgroup G) n

/-- **`L(G)`** (BG App.B, L4542): 絶対版 `lOddIn ⊤`. -/
def lOdd (G : Type*) [Group G] : Subgroup G := lOddIn (⊤ : Subgroup G)

/-- **`L_*(G)`** (BG App.B, L4542): 絶対版 `lStarIn ⊤`. -/
def lStar (G : Type*) [Group G] : Subgroup G := lStarIn (⊤ : Subgroup G)

/-! ### 構造 API (定義の展開補題) -/

@[simp] theorem lNIn_zero (H : Subgroup G) : lNIn H 0 = ⊥ := rfl

theorem lNIn_succ (H : Subgroup G) (n : ℕ) : lNIn H (n + 1) = lRelIn H (lNIn H n) := rfl

/-- `H` 内 abelian で `X` に正規化される部分群 `A` は `L_H(X)` に含まれる (上限の下界性). -/
theorem le_lRelIn {H X A : Subgroup G} (hcomm : IsMulCommutative ↥A) (hAH : A ≤ H)
    (hnorm : X ≤ Subgroup.normalizer (A : Set G)) : A ≤ lRelIn H X := by
  unfold lRelIn
  exact le_iSup₂ (f := fun A _ => A) A ⟨hcomm, hAH, hnorm⟩

/-- `L_H(X) ≤ K` は「`X` に正規化される `H` 内 abelian がすべて `≤ K`」から従う (上限の最小性). -/
theorem lRelIn_le {H X K : Subgroup G}
    (h : ∀ A : Subgroup G, IsMulCommutative ↥A → A ≤ H →
      X ≤ Subgroup.normalizer (A : Set G) → A ≤ K) : lRelIn H X ≤ K := by
  unfold lRelIn
  exact iSup₂_le fun A hA => h A hA.1 hA.2.1 hA.2.2

theorem lRelIn_le_self (H X : Subgroup G) : lRelIn H X ≤ H :=
  lRelIn_le fun _A _ hAH _ => hAH

theorem lNIn_le_self (H : Subgroup G) (n : ℕ) : lNIn H n ≤ H := by
  cases n with
  | zero => exact bot_le
  | succ n => exact lRelIn_le_self H _

/-! ### Lemma B.1(a): 反変単調性 (L4546) -/

/-- **BG Lemma B.1(a)** (L4546): `L_H(−)` は包含について反変単調. `X ⊆ Y ⇒ L_H(Y) ⊆ L_H(X)`. -/
theorem lRelIn_anti_right {H : Subgroup G} {X Y : Subgroup G} (h : X ≤ Y) :
    lRelIn H Y ≤ lRelIn H X :=
  lRelIn_le fun _A hcomm hAH hnorm => le_lRelIn hcomm hAH (le_trans h hnorm)

/-- `H` について単調 (より大きい `H` ほど多くの abelian を許す). -/
theorem lRelIn_mono_left {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (X : Subgroup G) :
    lRelIn H₁ X ≤ lRelIn H₂ X :=
  lRelIn_le fun _A hcomm hAH hnorm => le_lRelIn hcomm (le_trans hAH h) hnorm

/-! ### Lemma B.1(b): 偶奇交互の単調性 (L4547) -/

/-- 偶奇交互の基本不等式 `L_{2n} ⊆ L_{2n+2} ⊆ L_{2n+1}` (BG App.B, L4566 の帰納核).
`L_H(−)` の反変単調性 (B.1(a)) から `n` についての帰納で従う. -/
theorem lNIn_interleave (H : Subgroup G) :
    ∀ n, lNIn H (2 * n) ≤ lNIn H (2 * n + 2) ∧ lNIn H (2 * n + 2) ≤ lNIn H (2 * n + 1)
  | 0 => ⟨bot_le, lRelIn_anti_right bot_le⟩
  | (n + 1) => by
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
      obtain ⟨h1, h2⟩ := lNIn_interleave H n
      have hodd : lNIn H (2 * n + 2 + 1) ≤ lNIn H (2 * n + 1) := lRelIn_anti_right h1
      have hmid : lNIn H (2 * n + 2) ≤ lNIn H (2 * n + 2 + 1) := lRelIn_anti_right h2
      exact ⟨lRelIn_anti_right hodd, lRelIn_anti_right hmid⟩

/-- **BG Lemma B.1(b)** (L4547, 偶部分列): `n ↦ L_{2n}(H)` は単調増加. -/
theorem lNIn_even_mono (H : Subgroup G) : Monotone fun n => lNIn H (2 * n) :=
  monotone_nat_of_le_succ fun n => by
    show lNIn H (2 * n) ≤ lNIn H (2 * (n + 1))
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
    exact (lNIn_interleave H n).1

/-- **BG Lemma B.1(b)** (L4547, 奇部分列): `n ↦ L_{2n+1}(H)` は単調減少. -/
theorem lNIn_odd_anti (H : Subgroup G) : Antitone fun n => lNIn H (2 * n + 1) :=
  antitone_nat_of_succ_le fun n => by
    show lNIn H (2 * (n + 1) + 1) ≤ lNIn H (2 * n + 1)
    rw [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 from by ring]
    exact lRelIn_anti_right (lNIn_interleave H n).1

/-- **BG Lemma B.1(b)** (L4547, 偶 ≤ 奇): すべての偶 index は任意の奇 index 以下. -/
theorem lNIn_even_le_odd (H : Subgroup G) (m n : ℕ) :
    lNIn H (2 * m) ≤ lNIn H (2 * n + 1) := by
  have e1 : lNIn H (2 * m) ≤ lNIn H (2 * max m n) := lNIn_even_mono H (le_max_left m n)
  have e3 : lNIn H (2 * max m n + 1) ≤ lNIn H (2 * n + 1) := lNIn_odd_anti H (le_max_right m n)
  have e2 : lNIn H (2 * max m n) ≤ lNIn H (2 * max m n + 1) :=
    (lNIn_interleave H (max m n)).1.trans (lNIn_interleave H (max m n)).2
  exact e1.trans (e2.trans e3)

/-! ### Lemma B.1(d): `L_*(H) ⊆ L(H)` (L4549) -/

/-- **BG Lemma B.1(d)** (L4549): `L_*(H) ⊆ L(H)`. `L_*(H)` は構成上 (`iSup`) `Subgroup`. -/
theorem lStarIn_le_lOddIn (H : Subgroup G) : lStarIn H ≤ lOddIn H := by
  change ⨆ m, lNIn H (2 * m) ≤ ⨅ n, lNIn H (2 * n + 1)
  exact iSup_le fun m => le_iInf fun n => lNIn_even_le_odd H m n

end OddOrder.BG.AppB
