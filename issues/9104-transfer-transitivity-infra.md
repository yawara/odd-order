---
id: 9104
slug: transfer-transitivity-infra
title: "shared infra claim: transfer transitivity (Isaacs 10.8) leaf"
created: 2026-07-17
---

# shared infra claim: transfer transitivity (Isaacs 10.8) leaf

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## Claim (lane c)

**Transfer transitivity** (Isaacs Thm 10.8) を一般群論の shared leaf として新設:
`OddOrder/GroupTheory/TransferTransitivity.lean`

- 主定理: `H ≤ K ≤ G`, `[H.FiniteIndex]`, `ϕ : ↥H →* A` (`A` 可換) に対し
  `MonoidHom.transfer (MonoidHom.transfer ϕ̃) = MonoidHom.transfer ϕ`
  (`ϕ̃ := ϕ ∘ subgroupOfEquivOfLe`)。mathlib 完全未収載 (`transfer_comp` 等なし、
  2026-07-17 grep 確認)。upstream 候補。
- 証明戦略: section-built transversal (`isComplement_range_left`) の積構成 +
  `quotientEquivProdOfLE'` fibration での diff 分解
  (`diff ϕ (T·S) (T'·S) = diff W T T'`)、`transfer_def` 2 回。
- consumer: Isaacs 10.9, 10.28 (Alperin–Kuo)、Yoshida 10.1 経路。

事前検索: repo 内 `transfer` transitivity/comp 該当なし。mathlib Transfer.lean
に diff/leftTransversal API はあるが tower 合成なし。
