---
id: 9505
slug: iwasawa-simplicity-criterion
title: "Iwasawa simplicity criterion (shared infra claim, hub) — mathlib に既存で撤回"
created: 2026-08-02
---

# Iwasawa simplicity criterion (shared infra claim, hub) — ❌ 撤回 (mathlib に既存)

## 結論 (2026-08-02, 即日クローズ)

**mathlib が既に持っていた**: `Mathlib/GroupTheory/GroupAction/Iwasawa.lean`
(Antoine Chambert-Loir, 2024)。

```
MulAction.IwasawaStructure M α          -- T : α → Subgroup M, is_comm / is_conj / is_generator
MulAction.IwasawaStructure.commutator_le  -- 準原始的なら自明でなく作用する正規部分群は commutator M を含む
MulAction.IwasawaStructure.isSimpleGroup  -- + faithful + Nontrivial + perfect ⟹ IsSimpleGroup M
```

⟹ 自作 leaf は不要。書きかけの `OddOrder/GroupTheory/GroupAction/Iwasawa.lean` は削除した
(commit されていない)。

## ⚠ 教訓 — claim-before-build の検索は mathlib も見る

repo 側 (`grep -rn Iwasawa OddOrder/`) はヒットゼロだったので「新規 shared infra」と
判断したが、**mathlib を検索していなかった**。既存エンジン
`PerfectQuasiprimitive.lean` が「点安定化群が可解」版しか持っていなかったことが
「repo には無い ⟹ どこにも無い」という誤った推論を補強した。

**claim-before-build のチェックリストに `.lake/packages/mathlib` の grep を含めること。**
本件は 1 ファイル分の書き損じで済んだ (build 前に `Unknown constant` の解決で発覚)。

## 背景 (元の動機は有効)

[issue 1055](1055-isaacs-problems-campaign.md) の Isaacs Ch.8 残件 **8C.6** (p. 257):

> Let `A` be an abelian group.  Show that `Aut(A)` is simple if and only if `A` has order
> 3 or `A` is an elementary abelian 2-group of order at least 8.

「⟸」の主要部 =「初等可換 2-群 `E` (位数 `≥ 8`) について `Aut(E)` が単純」で、標準証明は
Iwasawa 判定。既存の `isSimpleGroup_of_isPerfect_of_isQuasiPreprimitive_of_isSolvable_stabilizer`
は**点安定化群が可解**を要求し `GL(n, 2)` (`n ≥ 4`) では使えない、という診断は正しい。

⟹ 残作業は Iwasawa 判定そのものではなく、**`Aut(E)` の Iwasawa 構造を組むこと**。
計画は issue 1055 の 8C.6 節に移した。

## 参照

* mathlib = `.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Iwasawa.lean`
* 8C.6 の現状 = `OddOrder/Isaacs/Ch08_PermutationGroups/Problems8C/AbelianAut.lean`
