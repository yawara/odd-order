---
id: 35
slug: bg-s02-odd-two-dim-repr
title: "BG §2 OddTwoDimRepr shared module (Thm 2.6)"
created: 2026-05-26
---

# BG §2 OddTwoDimRepr shared module (Thm 2.6)

## 結果 (closed, 2026-05-28)

**Thm 2.6 の数学的ゴールは別の場所で達成済み。本 issue は陳腐化につき close。**

- **BG Thm 2.6 は `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean` で実装済・sorry-free**:
  `odd_two_dim_abelian` (L4627) / `odd_two_dim_sylow_abelian` (L4680)。しかも **体一般**
  (`{F : Type*} [Field F]`) で、本 issue が想定していた「complex (ℂ) のみ」より強い。
- 本 issue が作ろうとした shared module `OddOrder/GroupTheory/RepresentationTheory/OddTwoDimRepr.lean`
  は **34 行の空 skeleton**(宣言ゼロ、namespace のみ)で、docstring が Thm 2.6 を
  「faithful two-dimensional **complex** representation」と**誤記**していた(実際は体一般)。
  どこからも import されていない。⇒ **本 close と同時に削除**(misleading なため)。
- 当初の「complex 2-dim faithful 表現を持たない」という goal 設定自体が、BG Thm 2.6 の
  正しい statement(体 `F` 上 2-dim faithful ⇒ Sylow-`p` abelian ∧ `G' ≤ P` 等)と
  ずれていた。S02 実装が正。

将来 App.A の A.1/A.2(issue **#0041**)で 2-dim 表現の道具が要る場合は、S02 の
`odd_two_dim_*` を直接呼ぶ(必要なら App.A 新規ファイルに置く)。`OddTwoDimRepr.lean`
を再生する必要はない。

## (元の) 背景

BG §2 Thm 2.6 is the odd-order 2-dimensional faithful representation result.
`OddOrder/GroupTheory/RepresentationTheory/OddTwoDimRepr.lean` does not exist yet.

## 完了条件 (満たされた形)

- BG Thm 2.6 が sorry-free で存在(✅ S02 `odd_two_dim_sylow_abelian` / `odd_two_dim_abelian`)。
- 空 skeleton `OddTwoDimRepr.lean` を削除(✅ 本 close と同時)。

## 参照

- 実装: [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](../../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) L4627 / L4680
- 後継: [issue #0041](../closed/0041-bg-appa-a2-dim-reduction.md)(App.A A.2 次元縮約 — Thm 2.6 を A.1 で使う)
- `notes/bg/s02_representations.md`
- 関連: #34 (Thm 2.5 ExtraspecialFaithful — これも skeleton 状態、別途)
