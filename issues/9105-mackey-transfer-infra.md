---
id: 9105
slug: mackey-transfer-infra
title: "shared infra claim: Mackey transfer (Isaacs 10.10) leaf"
created: 2026-07-17
---

# shared infra claim: Mackey transfer (Isaacs 10.10) leaf

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## Claim (lane c)

**Mackey transfer** (Isaacs Thm 10.10) を一般群論 shared leaf として新設:
`OddOrder/GroupTheory/MackeyTransfer.lean`

- 主定理 (mathlib 左剰余類 mirror): `H K : Subgroup G`, `[H.FiniteIndex]`,
  `ϕ : ↥H →* A` (`A` 可換), `k ∈ K` に対し
  `transfer ϕ k = ∏_{x : (K,H)-double coset reps} transfer ψ_x ⟨k⟩`
  — `ψ_x : ↥((x•H•x⁻¹ ⊓ K).subgroupOf K) →* A`, `w ↦ ϕ(x⁻¹ w x)`。
- 証明戦略 (TransferTransitivity と同型): `G ⧸ H` の section を double coset
  quotient 上に fiber 化 (fiber = `K ⧸ (K ∩ H^x).subgroupOf K`)、
  `diff` の積分解。mathlib `DoubleCoset.Quotient` + `disjoint_out` +
  `iUnion_quotToDoubleCoset` を使用。
- 事前補題: `(x•H•x⁻¹ ⊓ K).subgroupOf K` の FiniteIndex (fiber 有限性)。
- consumer: Isaacs 10.1 Yoshida (10.11 と併用)。

事前検索: mathlib `Doset`/Transfer に Mackey 公式なし (2026-07-17 grep)。
repo 内該当なし。

## 状態

- [x] claim (2026-07-17)
- [ ] skeleton (statement + design, sorried)
- [ ] 証明本体
