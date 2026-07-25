---
id: 9502
slug: prime-degree-two-transitive
title: "shared infra: degree-p faithful transitive |G|=p(p-1) は sharply 2-transitive"
created: 2026-07-25
---

# shared infra: degree-p faithful transitive |G|=p(p-1) は sharply 2-transitive

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 内容 (claim: hub/2053 用共有 infra)

新 leaf `OddOrder/GroupTheory/PrimeDegreeTwoTransitive.lean`:

**主張**: `G` finite, `Ω` finite, faithful + transitive `MulAction G Ω`,
`|Ω| = p` (素数), `|G| = p·(p−1)` ⟹ `IsMultiplyPretransitive G Ω 2`。

**証明**: Cauchy で位数 p の σ → Sylow 第3定理 (n_p ∣ p−1, ≡1 mod p) で
⟨σ⟩ ⊴ G → σ は固定点なし (固定点があれば正規性+推移性で全点固定 → faithful
矛盾) → i ↦ σ^i•a が ZMod p ≃ Ω → 2 点固定元 g は gσ^ig⁻¹ = σ^i を強制され
σ と可換 → 全点固定 → g = 1 → pair-stabilizer 自明 → 軌道数え上げで
pair-transitive。

**消費者**: Pf II step (12) 終盤 (issue 2053) — N_G(R)/R ↷ 𝒜 (m=1: degree p,
位数 p(p−1)) の 2-推移性 = RankOneHypothesis.doubly_transitive field。
