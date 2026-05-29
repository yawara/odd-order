/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.OrderIsoNat
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.DQSDRecognition
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

/-! ### Lemma B.1(c)(g): 停留と双対性 (L4548, L4552; `[Finite G]`) -/

/-- 単調列 `f : ℕ → Subgroup G` が `k` 以降一定なら `⨆ f = f k`. -/
private theorem iSup_eq_of_monotone_stable {f : ℕ → Subgroup G} (hf : Monotone f) {k : ℕ}
    (hk : ∀ m, k ≤ m → f k = f m) : ⨆ n, f n = f k := by
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup f k)
  rcases le_total n k with h | h
  · exact hf h
  · exact (hk n h).ge

/-- 反単調列 `f : ℕ → Subgroup G` が `k` 以降一定なら `⨅ f = f k`. -/
private theorem iInf_eq_of_antitone_stable {f : ℕ → Subgroup G} (hf : Antitone f) {k : ℕ}
    (hk : ∀ m, k ≤ m → f k = f m) : ⨅ n, f n = f k := by
  refine le_antisymm (iInf_le f k) (le_iInf fun n => ?_)
  rcases le_total n k with h | h
  · exact hf h
  · exact (hk n h).le

/-- 偶部分列の停留 (有限性). -/
theorem exists_even_stable [Finite G] (H : Subgroup G) :
    ∃ k, ∀ m, k ≤ m → lNIn H (2 * k) = lNIn H (2 * m) := by
  obtain ⟨k, hk⟩ :=
    WellFoundedGT.monotone_chain_condition ⟨fun n => lNIn H (2 * n), lNIn_even_mono H⟩
  exact ⟨k, hk⟩

/-- 奇部分列の停留 (有限性). -/
theorem exists_odd_stable [Finite G] (H : Subgroup G) :
    ∃ k, ∀ m, k ≤ m → lNIn H (2 * k + 1) = lNIn H (2 * m + 1) := by
  obtain ⟨k, hk⟩ := WellFoundedLT.antitone_chain_condition (lNIn_odd_anti H)
  exact ⟨k, hk⟩

/-- `L_*(H) = L_{2j}(H)` for `j ≥` 停留点. -/
theorem exists_lStarIn_eq [Finite G] (H : Subgroup G) :
    ∃ k, ∀ j, k ≤ j → lStarIn H = lNIn H (2 * j) := by
  obtain ⟨k, hk⟩ := exists_even_stable H
  have h0 : lStarIn H = lNIn H (2 * k) := iSup_eq_of_monotone_stable (lNIn_even_mono H) hk
  exact ⟨k, fun j hj => h0.trans (hk j hj)⟩

/-- `L(H) = L_{2j+1}(H)` for `j ≥` 停留点. -/
theorem exists_lOddIn_eq [Finite G] (H : Subgroup G) :
    ∃ k, ∀ j, k ≤ j → lOddIn H = lNIn H (2 * j + 1) := by
  obtain ⟨k, hk⟩ := exists_odd_stable H
  have h0 : lOddIn H = lNIn H (2 * k + 1) := iInf_eq_of_antitone_stable (lNIn_odd_anti H) hk
  exact ⟨k, fun j hj => h0.trans (hk j hj)⟩

/-- **BG Lemma B.1(c)** (L4548): ある `k` 以降 `L_{2n}(H) = L_*(H)` かつ `L_{2n+1}(H) = L(H)`. -/
theorem exists_lNIn_stable [Finite G] (H : Subgroup G) :
    ∃ k, (∀ n, k ≤ n → lNIn H (2 * n) = lStarIn H) ∧
      (∀ n, k ≤ n → lNIn H (2 * n + 1) = lOddIn H) := by
  obtain ⟨k1, h1⟩ := exists_lStarIn_eq H
  obtain ⟨k2, h2⟩ := exists_lOddIn_eq H
  refine ⟨max k1 k2, fun n hn => ?_, fun n hn => ?_⟩
  · exact (h1 n (le_trans (le_max_left _ _) hn)).symm
  · exact (h2 n (le_trans (le_max_right _ _) hn)).symm

/-- **BG Lemma B.1(g)** (L4552): `L_H(L_*(H)) = L(H)`. -/
theorem lRelIn_lStarIn [Finite G] (H : Subgroup G) : lRelIn H (lStarIn H) = lOddIn H := by
  obtain ⟨k1, h1⟩ := exists_lStarIn_eq H
  obtain ⟨k2, h2⟩ := exists_lOddIn_eq H
  rw [h1 (max k1 k2) (le_max_left _ _), h2 (max k1 k2) (le_max_right _ _)]
  exact (lNIn_succ H (2 * max k1 k2)).symm

/-- **BG Lemma B.1(g)** (L4552): `L_H(L(H)) = L_*(H)`. -/
theorem lRelIn_lOddIn [Finite G] (H : Subgroup G) : lRelIn H (lOddIn H) = lStarIn H := by
  obtain ⟨k1, h1⟩ := exists_lStarIn_eq H
  obtain ⟨k2, h2⟩ := exists_lOddIn_eq H
  set K := max k1 k2 with hK
  rw [h2 K (le_max_right _ _), h1 (K + 1) (le_trans (le_max_left _ _) (Nat.le_succ _)),
    show 2 * (K + 1) = 2 * K + 1 + 1 from by ring]
  exact (lNIn_succ H (2 * K + 1)).symm

/-! ### `L_1(H) = H` と Lemma B.1(e) (L4556, L4550) -/

/-- `L_1(H) = H` (BG App.B, L4556: 各元が cyclic 群に属するため). -/
theorem lNIn_one (H : Subgroup G) : lNIn H 1 = H := by
  refine le_antisymm (lNIn_le_self H 1) ?_
  intro x hx
  have hle : Subgroup.zpowers x ≤ lNIn H 1 := by
    rw [lNIn_succ]
    exact le_lRelIn (Subgroup.zpowers_isMulCommutative x) (Subgroup.zpowers_le.mpr hx) bot_le
  exact hle (Subgroup.mem_zpowers x)

/-- **BG Lemma B.1(e) 一般化**: `A` abelian で `A ≤ H` かつ `H ≤ N_G(A)` (= `A` が `H` で正規化される)
なら, すべての `i > 0` で `A ⊆ L_i(H)`. 相対 B.1(f) / B.3 で `A` が `H`-正規 (G-正規でない) の場合に使う. -/
theorem abelian_le_lNIn {A H : Subgroup G} (hcomm : IsMulCommutative ↥A) (hAH : A ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (A : Set G)) {i : ℕ} (hi : 0 < i) : A ≤ lNIn H i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  rw [lNIn_succ]
  exact le_lRelIn hcomm hAH ((lNIn_le_self H j).trans hnorm)

/-- **BG Lemma B.1(e)** (L4550): `G` の abelian normal 部分群 `A` (with `A ≤ H`) は,
すべての `i > 0` について `L_i(H)` に含まれる. (`H = ⊤` で教科書の `A ⊆ L_i(G)`.) -/
theorem abelian_normal_le_lNIn {A H : Subgroup G} (hcomm : IsMulCommutative ↥A)
    (hnormal : A.Normal) (hAH : A ≤ H) {i : ℕ} (hi : 0 < i) : A ≤ lNIn H i :=
  abelian_le_lNIn hcomm hAH
    (le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hnormal).symm) hi

/-! ### Lemma B.1(f): p-群での自己中心性 (L4551; `[Finite G]`)

教科書の `G` が `p`-群の場合 (= `H = ⊤`). 部分群 `H` が `p`-群の相対版 (B.3 で `T = O_p(G)`,
`S ∈ Syl_p` に適用) は subtype `↥H` 経由の transport を要するため B.3 着手時に別途用意する. -/

/-- **BG Lemma B.1(f)** 核 (L4551): `G` が `p`-群なら `i > 0` で `C_G(L_i(G)) ⊆ L_i(G)`.
極大 normal abelian `M ⊆ L_i` (B.1(e)) と self-centralizing `C_G(M) = M`
(Isaacs Thm 5.3.12 = `Ch06.centralizer_eq_of_maximal_normal_isMulCommutative`) から従う. -/
theorem centralizer_lNIn_le [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    {i : ℕ} (hi : 0 < i) :
    Subgroup.centralizer (lNIn (⊤ : Subgroup G) i : Set G) ≤ lNIn (⊤ : Subgroup G) i := by
  obtain ⟨M, hM_normal, hM_comm, hM_max⟩ :=
    OddOrder.Isaacs.Ch06.exists_maximal_normal_isMulCommutative (P := G)
  haveI : M.Normal := hM_normal
  have hM_le : M ≤ lNIn (⊤ : Subgroup G) i := abelian_normal_le_lNIn hM_comm hM_normal le_top hi
  have hCent : Subgroup.centralizer (M : Set G) = M :=
    OddOrder.Isaacs.Ch06.centralizer_eq_of_maximal_normal_isMulCommutative hG hM_comm hM_max
  have hanti : Subgroup.centralizer (lNIn (⊤ : Subgroup G) i : Set G)
      ≤ Subgroup.centralizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    exact fun h hh => hg h (hM_le hh)
  exact hanti.trans (hCent.le.trans hM_le)

/-- `Z(G) ⊆ C_G(L_i(G))` (中心は何でも中心化する; B.1(f) の `⊇ Z(G)` 部分). -/
theorem center_le_centralizer_lNIn (i : ℕ) :
    Subgroup.center G ≤ Subgroup.centralizer (lNIn (⊤ : Subgroup G) i : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  exact fun h _ => Subgroup.mem_center_iff.mp hg h

/-- **BG Lemma B.1(f)** (L4551): `G` が `p`-群なら `i > 0` で `Z(G) ⊆ L_i(G)`. -/
theorem center_le_lNIn [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    {i : ℕ} (hi : 0 < i) : Subgroup.center G ≤ lNIn (⊤ : Subgroup G) i :=
  (center_le_centralizer_lNIn i).trans (centralizer_lNIn_le hG hi)

/-- **BG Lemma B.1(f)** (`L_*` 版, L4551): `G` p-群で `C_G(L_*(G)) ⊆ L_*(G)`. -/
theorem centralizer_lStarIn_le [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    Subgroup.centralizer (lStarIn (⊤ : Subgroup G) : Set G) ≤ lStarIn ⊤ := by
  obtain ⟨k, hk⟩ := exists_lStarIn_eq (⊤ : Subgroup G)
  rw [hk (k + 1) (Nat.le_succ k)]
  exact centralizer_lNIn_le hG (by omega)

/-- **BG Lemma B.1(f)** (`L` 版, L4551): `G` p-群で `C_G(L(G)) ⊆ L(G)`. -/
theorem centralizer_lOddIn_le [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    Subgroup.centralizer (lOddIn (⊤ : Subgroup G) : Set G) ≤ lOddIn ⊤ := by
  obtain ⟨k, hk⟩ := exists_lOddIn_eq (⊤ : Subgroup G)
  rw [hk k (le_refl k)]
  exact centralizer_lNIn_le hG (by omega)

/-- `Z(G) ⊆ L_*(G)` (`G` p-群). -/
theorem center_le_lStarIn [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    Subgroup.center G ≤ lStarIn (⊤ : Subgroup G) := by
  obtain ⟨k, hk⟩ := exists_lStarIn_eq (⊤ : Subgroup G)
  rw [hk (k + 1) (Nat.le_succ k)]
  exact center_le_lNIn hG (by omega)

/-- **BG Lemma B.1(f)** 帰結 (L4551): `G ≠ 1` p-群なら `L_*(G) ≠ 1`. -/
theorem lStarIn_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] [Nontrivial G] (hG : IsPGroup p G) :
    lStarIn (⊤ : Subgroup G) ≠ ⊥ := by
  intro h
  have hc : Subgroup.center G ≤ ⊥ := h ▸ center_le_lStarIn hG
  exact hG.bot_lt_center.ne' (le_bot_iff.mp hc)

/-- **BG Lemma B.1(f)** 帰結 (L4551): `G ≠ 1` p-群なら `L(G) ≠ 1`. -/
theorem lOddIn_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] [Nontrivial G] (hG : IsPGroup p G) :
    lOddIn (⊤ : Subgroup G) ≠ ⊥ := fun h =>
  lStarIn_ne_bot hG (le_bot_iff.mp ((lStarIn_le_lOddIn ⊤).trans h.le))

/-! ### Lemma B.2: `L(G) ⊆ H ⇒ L(H) = L(G)` (L4590-4642; `[Finite G]`) -/

/-- 偶 index は `L(H)` 以下: `L_{2m}(H) ⊆ L(H)`. -/
theorem lNIn_even_le_lOddIn (H : Subgroup G) (m : ℕ) : lNIn H (2 * m) ≤ lOddIn H :=
  le_iInf fun n => lNIn_even_le_odd H m n

/-- B.2 証明核 (mmd L4604-4616, L4626-4638 共通; ambient `H₁` 相対版):
`L_{H₁}(W) ⊆ H₂` かつ `W' ⊆ W` なら `L_{H₁}(W) ⊆ L_{H₂}(W')`.
`L_{H₁}(W)` を張る abelian `A` は `A ⊆ L_{H₁}(W) ⊆ H₂` で `W' ⊆ W ⊆ N(A)`. -/
theorem lRelIn_le_lRelIn {H₁ W W' H₂ : Subgroup G} (hW' : W' ≤ W)
    (hsub : lRelIn H₁ W ≤ H₂) : lRelIn H₁ W ≤ lRelIn H₂ W' := by
  refine lRelIn_le fun A hcomm hAH hnorm => le_lRelIn hcomm ?_ (le_trans hW' hnorm)
  exact le_trans (le_lRelIn hcomm hAH hnorm) hsub

/-- B.2 Step 1 偶段 (mmd L4604-4608, ambient `H₀`): `L_{2n+1}(H) ⊆ L_{2n+1}(H₀)` から
`L_{2n+2}(H₀) ⊆ L_{2n+2}(H)`. -/
private theorem b2_even_le {H₀ H : Subgroup G} (hH₀H : lOddIn H₀ ≤ H) {n : ℕ}
    (hodd : lNIn H (2 * n + 1) ≤ lNIn H₀ (2 * n + 1)) :
    lNIn H₀ (2 * n + 2) ≤ lNIn H (2 * n + 2) := by
  have hev_le : lNIn H₀ (2 * n + 2) ≤ lOddIn H₀ := by
    have h := lNIn_even_le_lOddIn H₀ (n + 1)
    rwa [show 2 * (n + 1) = 2 * n + 2 from by ring] at h
  exact lRelIn_le_lRelIn hodd (hev_le.trans hH₀H)

/-- B.2 Step 1 奇段 (mmd L4612-4616, ambient `H₀`): `L_{2n+2}(H₀) ⊆ L_{2n+2}(H)` から
`L_{2n+3}(H) ⊆ L_{2n+3}(H₀)`. -/
private theorem b2_odd_le {H₀ H : Subgroup G} (hHH₀ : H ≤ H₀) {n : ℕ}
    (hev : lNIn H₀ (2 * n + 2) ≤ lNIn H (2 * n + 2)) :
    lNIn H (2 * n + 3) ≤ lNIn H₀ (2 * n + 3) :=
  (lRelIn_mono_left hHH₀ (lNIn H (2 * n + 2))).trans (lRelIn_anti_right hev)

/-- **BG Lemma B.2 Step 1(a)** (mmd L4594, ambient `H₀`): `L_{2n+1}(H) ⊆ L_{2n+1}(H₀)`. -/
theorem b2_step1 {H₀ H : Subgroup G} (hHH₀ : H ≤ H₀) (hH₀H : lOddIn H₀ ≤ H) :
    ∀ n, lNIn H (2 * n + 1) ≤ lNIn H₀ (2 * n + 1)
  | 0 => by
      have e1 : lNIn H (2 * 0 + 1) = H := lNIn_one H
      have e2 : lNIn H₀ (2 * 0 + 1) = H₀ := lNIn_one H₀
      rw [e1, e2]; exact hHH₀
  | (n + 1) => by
      have hodd := b2_odd_le hHH₀ (b2_even_le hH₀H (b2_step1 hHH₀ hH₀H n))
      rwa [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]

/-- B.2 Step 2 偶段 (mmd L4626-4630, ambient `H₀`): `L(H₀) ⊆ L_{2n+1}(H)` から
`L_{2n+2}(H) ⊆ L_*(H₀)`. -/
private theorem b2_star_le {H₀ H : Subgroup G} [Finite G] (hHH₀ : H ≤ H₀) {n : ℕ}
    (hIH : lOddIn H₀ ≤ lNIn H (2 * n + 1)) :
    lNIn H (2 * n + 2) ≤ lStarIn H₀ := by
  rw [← lRelIn_lOddIn H₀]
  exact (lRelIn_mono_left hHH₀ (lNIn H (2 * n + 1))).trans (lRelIn_anti_right hIH)

/-- B.2 Step 2 奇段 (mmd L4632-4638, ambient `H₀`): `L_{2n+2}(H) ⊆ L_*(H₀)` から
`L(H₀) ⊆ L_{2n+3}(H)`. -/
private theorem b2_odd_ge {H₀ H : Subgroup G} [Finite G] (hH₀H : lOddIn H₀ ≤ H)
    {n : ℕ} (hstar : lNIn H (2 * n + 2) ≤ lStarIn H₀) :
    lOddIn H₀ ≤ lNIn H (2 * n + 3) := by
  rw [← lRelIn_lStarIn H₀]
  exact lRelIn_le_lRelIn hstar ((lRelIn_lStarIn H₀).le.trans hH₀H)

/-- **BG Lemma B.2 Step 2(a)** (mmd L4620, ambient `H₀`): `L(H₀) ⊆ L_{2n+1}(H)`. -/
theorem b2_step2 {H₀ H : Subgroup G} [Finite G] (hHH₀ : H ≤ H₀) (hH₀H : lOddIn H₀ ≤ H) :
    ∀ n, lOddIn H₀ ≤ lNIn H (2 * n + 1)
  | 0 => by
      have e : lNIn H (2 * 0 + 1) = H := lNIn_one H
      rw [e]; exact hH₀H
  | (n + 1) => by
      have hodd := b2_odd_ge hH₀H (b2_star_le hHH₀ (b2_step2 hHH₀ hH₀H n))
      rwa [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]

/-- **BG Lemma B.2 一般版** (mmd L4590): `H ⊆ H₀` かつ `L(H₀) ⊆ H` なら `L(H) = L(H₀)`.
B.4 Step3 末尾 `L(C∩S) = L(S)` (H = C∩S, H₀ = S) に使う. -/
theorem lOddIn_eq_of_lOddIn_le_relative {H₀ H : Subgroup G} [Finite G]
    (hHH₀ : H ≤ H₀) (hH₀H : lOddIn H₀ ≤ H) : lOddIn H = lOddIn H₀ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_lOddIn_eq H
    obtain ⟨k', hk'⟩ := exists_lOddIn_eq H₀
    rw [hk (max k k') (le_max_left _ _), hk' (max k k') (le_max_right _ _)]
    exact b2_step1 hHH₀ hH₀H (max k k')
  · obtain ⟨k, hk⟩ := exists_lOddIn_eq H
    rw [hk k (le_refl k)]
    exact b2_step2 hHH₀ hH₀H k

/-- **BG Lemma B.2** (L4590): `L(G) ⊆ H` なら `L(H) = L(G)`
(`lOddIn ⊤ = L(G)`, `lOddIn H = L(H)`; `H₀ = ⊤` 特殊化). -/
theorem lOddIn_eq_of_lOddIn_le {H : Subgroup G} [Finite G]
    (hLGH : lOddIn (⊤ : Subgroup G) ≤ H) : lOddIn H = lOddIn (⊤ : Subgroup G) :=
  lOddIn_eq_of_lOddIn_le_relative le_top hLGH

/-! ### Lemma B.3 / Theorem B.4 準備 (A.5 非依存の L-API 拡張)

B.3/B.4 (issue 2001) は A.5 (`thmA5`) を消費するため本体は別ファイル `AppB_PuigB3B4.lean`。
ここには A.5 に依存しない L-API の拡張 (thmA5 橋渡し / 相対 B.1(f) / φ-同変 + characteristic) のみを置く. -/

/-- **thmA5 橋渡し**: `H` が `p`-群なら `L_H(X)` は「`P` (≤ X) に正規化される abelian **p-群** で生成
される部分群」の上限以下. これにより B.3/B.4 が `lRelIn`/`lNIn` を `thmA5` の `hX` 仮説へ渡せる. -/
theorem lRelIn_le_iSup_pgroup_normalized {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) {P X : Subgroup G} (hPX : P ≤ X) :
    lRelIn H X ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧
        P ≤ Subgroup.normalizer (A : Set G)}, A := by
  refine lRelIn_le fun A hcomm hAH hnorm => ?_
  exact le_iSup₂ (f := fun A _ => A) A ⟨hcomm, hH.to_le hAH, le_trans hPX hnorm⟩

end OddOrder.BG.AppB
