---
id: 3026
slug: bg-thm64-invariant-pi-conjugacy
title: "BG Thm 6.4: H-不変な π-部分群 J₁,J₂ の共役合成 — ⟨J₁^x,J₂⟩ が π-群かつ x が H を中心化"
created: 2026-07-19
---

# BG Thm 6.4: H-不変な π-部分群 J₁,J₂ の共役合成 — ⟨J₁^x,J₂⟩ が π-群かつ x が H を中心化

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 状態 (2026-07-19 実測)

**完全に未形式化**。survey L481 で refutation 済 (repo 内の "Thm 6.4"/"Theorem 6.4" hit は
すべて **Isaacs** Thm 6.4 = Frobenius 群の四同値で別物)。本 session でも
`H-invariant` / conjugation 系の grep で該当なしを再確認。

BG §6 の残り最後の 1 件 (6.1 ✅ / 6.2 は issue 3024 に blocked / 6.3 ✅ / 6.5,6.6,6.7 ✅)。

## 原文 (mmd L2011)

> **Theorem 6.4.** Suppose `G` is a group, `π` is a set of primes, `H` is a `π'`-subgroup of `G`,
> and `G₀` is a normal Hall subgroup of `G`. Assume that `G₀/F(G₀)` and `(G/G₀)/F(G/G₀)` are
> nilpotent. Assume further that `H` normalizes two `π`-subgroups `J₁` and `J₂` of `G`.
> Then there exists an element `x ∈ ⟨J₁, J₂⟩` such that `⟨J₁ˣ, J₂⟩` is a `π`-group and
> `x` centralizes `H`.

⚠ **BG は証明を本文に持っている** (mmd L2015 以降、`|G| + |H|` の帰納法)。Thm 6.2 のように
Gorenstein への引用で済ませてはいない ⟹ **本 issue は形式化労力であって research gap ではない**
([[verify-port-state-by-number-not-coq-name]])。

証明の骨格 (mmd L2015-):
- `|G| + |H|` に関する帰納法。`G ≠ 1` としてよい。`M := G₀` (`G₀ ≠ 1` のとき)、さもなくば `M := G`。
  `L := ⟨J₁, J₂⟩`。
- (6.1) `M` は `G` の非自明 normal Hall 部分群で `M/F(M)` は冪零。
- `H` は `J₁,J₂` を正規化するので `L` も正規化 ⟹ `G = LH` としてよい。`G/L` は `π'`-群で、
  (6.2) `L` は `G` の任意の `π`-部分群を含む。
- `π(F(G)) ⊄ π(H)` の場合: `p ∈ π(F(G)) ∖ π(H)` を取り、`O_p(F(G))` 内の極小正規部分群 `N` へ
  帰納法。以下続く (原文参照)。

## 見積・注意

- **M** (survey 評価)。帰納法の各分岐で Hall/Fitting/冪零商の道具を使う。
- 前提は repo に揃っているはず (Hall 部分群・`fittingInAmbient`・冪零性・π-群 API)。
  着手時に **実測で確認**すること (名前一致の罠に注意 — 本 session で 5 回踏みかけた)。
- Coq 対応は **無い**: math-comp は「revised proof に不要」として §6 の一部を落としている。
  repo にも consumer は無い。⚠ **これは deprioritize の理由にならない**
  (CLAUDE.md「進捗の測り方」— consumer 0 / gate 無しは着手判断の基準ではない)。

## 参照

- BG mmd `references/bg/local-analysis.mmd` L2011 (statement) 以降 (proof)。
- survey `notes/meta/three_books_full_survey_2026_07_16.md` L481 (refutation 記録)。
- `notes/bg/s06_additional.md` (§6 全体の状況)。
