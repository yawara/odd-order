---
id: 1039
slug: split-extension-uniqueness-3-1
title: "Isaacs Lem 3.1 の two-abstract-groups 形 (特殊化債務)"
created: 2026-07-18
---

# Isaacs Lem 3.1 の two-abstract-groups 形 (特殊化債務)

## 背景

Isaacs Ch.3 の残作業は**特殊化債務のみ**で、Lem 3.11 は 2026-07-18 に解消済
(`3cff7a105`)。残るのが本件 Lem 3.1。

**現状** (`Ch03_SplitExtensions/Basic.lean:106` `mulEquivSubgroupOfComplement`):
`N ◁ G` が `K` で補われるとき `N ⋊ K ≃* G` という **internal form** のみ。
mathlib `SemidirectProduct.mulEquivSubgroup` に φ を固定して渡しただけ。

**書籍の形** (p. 70, Lem 3.1): 分裂拡大は「`N`, `H` と作用」で**同型を除き一意**。
すなわち 2 つの抽象群を比較する形:

> `N ◁ G`, `H` が `N` の complement; `N₀ ◁ G₀`, `H₀` が `N₀` の complement。
> 同型 `α : N ≅ N₀`, `β : H ≅ H₀` が作用と両立
> (`α (h n h⁻¹) = β h · α n · (β h)⁻¹`) するなら、
> `α` と `β` を延長する同型 `γ : G ≅ G₀` が**一意に**存在する。

internal form は `G₀ = N ⋊ H` に固定した特殊形にあたる。

## やること

- [ ] 述語を用意する: `IsSplitExtensionData G N H` 相当
      (`N.Normal`, `N.IsComplement' H`) と、作用の両立条件
      `∀ h ∈ H, ∀ n ∈ N, α ⟨h*n*h⁻¹⟩ = β h * α n * (β h)⁻¹`。
- [ ] **存在**: `γ` を `n * h ↦ α n * β h` で定義する
      (`IsComplement'` の一意分解 `Subgroup.IsComplement'.equiv` 系を使う)。
      準同型性が両立条件そのもの。
- [ ] **一意性**: `N ⊔ H = ⊤` なので `N` と `H` 上で一致すれば全体で一致。
      `Subgroup.eq_of_eqOn_sup` 系 / 生成による外延性。
- [ ] 既存の `mulEquivSubgroupOfComplement` を新定理の系として位置づける
      (⚠ CLAUDE.md ラッパー方針: 純粋リネームは作らない。
      internal form が下流で使われているなら残し、docstring で関係を記す)。
- [ ] 下流確認: `mulEquivSubgroupOfComplement` の呼び出し元を grep してから触る。

## 完了条件

書籍 p.70 の two-abstract-groups 形が sorry-free/axiom-clean で landing。
full build green + AxiomsCheck OK。

## 参照

- references/isaacs/finite-group-theory.pdf 書籍 p.70 (PDF page 83; offset +13)
- OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean:100-110
- mathlib `SemidirectProduct.mulEquivSubgroup`, `Subgroup.IsComplement'`
- 先行例: Lem 3.11 の一般化 (`3cff7a105`) — 環境の仮定を落として書籍形に寄せた

---

## 完了 (2026-07-19)

書籍 p.70 の two-abstract-groups 形を新 leaf
`OddOrder/Isaacs/Ch03_SplitExtensions/SplitExtensionUniqueness.lean` に実装。

| 宣言 | 役割 |
|---|---|
| `conjAutHom N H : H →* MulAut N` | `N ◁ G` への `H` の共役作用 (mathlib `normalizerMonoidHom` の仮定特殊化) |
| `closure_union_eq_top_of_isComplement'` | `closure (N ∪ H) = ⊤` |
| `monoidHom_eq_of_eqOn_isComplement'` | 一意性部分 (補集合対上で一致する `G →* G₀` は一致) |
| `existsUnique_mulEquiv_of_isComplement'` | **Lem 3.1 完全形** (`∃! θ : G ≃* G₀`, `α`/`β` を延長) |

- 存在 = `G ≃* N ⋊ H ≃* N₀ ⋊ H₀ ≃* G₀` (`SemidirectProduct.mulEquivSubgroup` ×2 +
  `SemidirectProduct.congr`; congr の仮説が両立条件そのもの)。
- 一意性 = `IsComplement'.sup_eq_top` → `MonoidHom.eq_of_eqOn_dense`。
- チェックリスト「既存 `mulEquivSubgroupOfComplement` の位置づけ」: 下流参照 0 件かつ
  mathlib `SemidirectProduct.mulEquivSubgroup` と引数・型が同一の純粋リネームだったので
  **削除** (CLAUDE.md ラッパー方針)。対応は新 leaf の docstring と `Basic.lean` の注記に記録。
- AxiomsCheck に `existsUnique_mulEquiv_of_isComplement'` を登録。sorry-free / 標準 3 公理のみ。
