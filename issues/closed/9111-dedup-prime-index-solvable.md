---
id: 9111
slug: dedup-prime-index-solvable
title: "exists_normal_index_prime_of_solvable の private(S07)/public(FongSwan) 重複を共有 leaf へ統合"
created: 2026-07-18
---

# exists_normal_index_prime_of_solvable の private/public 重複を共有 leaf へ統合

## 背景

「finite solvable nontrivial group ⟹ ∃ N ◁ G, N.index prime」の同一 ~30 行証明が 2 箇所:
- `OddOrder.BG.Ch2.S07.exists_normal_index_prime_of_solvable` (**private**,
  `OddOrder/BG/Ch2_Uniqueness/S07_Hypothesis75.lean:50`)
- `OddOrder.RepresentationTheory.exists_normal_index_prime_of_solvable` (**public**,
  `OddOrder/GroupTheory/RepresentationTheory/FongSwan.lean`) — private は import 不可ゆえ
  BG Lem 2.3 (issue 3008) 用に複製したもの (docstring に flag 済)。

mathlib に該当なし (一般 solvable の prime-index normal subgroup)。汎用 group theory の基本事実。

## やること

- [ ] 公開共有 leaf (例 `OddOrder/GroupTheory/SolvablePrimeIndex.lean`) に 1 本だけ置く。
- [ ] S07 の private 版を削除して共有版を import (S07 は BG Ch2 = 別レーン territory の可能性 →
      hub 経由 or owner 合意で)。
- [ ] FongSwan.lean の複製を削除して共有版を import。

## 完了条件

`exists_normal_index_prime_of_solvable` が repo 内 1 箇所 (public 共有 leaf) のみ、
S07 と FongSwan が両方それを import、build green。

## 参照

- consumer: [[3008]] BG Lem 2.3 (FongSwan)、S07_Hypothesis75
- 優先度低 (機能的には現状で正しく動作、純粋な DRY 整理)
