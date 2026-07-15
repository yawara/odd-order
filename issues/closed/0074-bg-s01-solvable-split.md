---
id: 74
slug: bg-s01-solvable-split
title: "BG S01_Solvable.lean split (2984行, spine-root ゆえ可読性目的・低優先)"
created: 2026-06-20
---

# BG S01_Solvable.lean split (2984行, spine-root ゆえ可読性目的・低優先)

## 背景

`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` が 2984 行と粒度規約 (1,500 行) を超過。
merge_monitor サイズ watch (2026-06-20 tick, lane-f Thm 15.2 step 3 の +8 行追記) で検出。

⚠ **他の size-flag 対象 (S08/S15 系) と性質が異なる**:
- S01_Solvable は BG §1 = **spine の ROOT** で、§1→§16 + Peterfalvi の全 closure が依存する。
- そのため **分割しても import fan-out は不変** = build 速度改善はゼロ (2026-06-20 実測: S01 への
  +8 行追記で full build が ~379s に膨張したのは S01 の位置が原因で、ファイルサイズが原因ではない)。
  cf. CLAUDE.md「FT spine の深い base closure を共有するファイル群では minimal-import の速度改善は
  ほぼ無い」。
- frontier でもない (foundational solvable-group theory、ほぼ凍結; 今回の +8 は Thm 15.2 向けの
  incidental な support lemma)。

⟹ 分割の価値は **可読性 + DAG 衛生 + upstream 適性のみ**、速度メリットなし。**低優先**。

## やること

- [ ] (低優先・任意) topic-coherent な凍結境界で prefix-split (例: 基本 solvable API / Fitting 補題 /
      p-length 系 等の主題で分割)。root closure (OddOrder.lean) + AxiomsCheck 追記を保つ。
- [ ] 急がない: active frontier でないため、他の優先作業を圧迫しない範囲で。

## 完了条件

S01_Solvable.lean が ≤1,500 行の topic-coherent な複数ファイルに分割され、full build green + AxiomsCheck OK。
または「spine-root ゆえ分割不要 (速度メリットなし・主題が単一)」と判断して意図的に close。

## 参照

- merge_monitor サイズ watch: notes/meta/merge_monitor.md step 4
- 同種 (frontier 系) の S08/S15 split: issues/0073 (S08 cluster), issues/0071 (S15_MF)
- 検出 commit: 69c51ef7 (Merge 'lane-f' S15 Thm 15.2 step 3)

## ✅ CLOSED (hub 裁定 2026-07-15 tick #8): S01_Solvable 1426行 (<1500), split 完了 (sibling S01_FrattiniBurnside)。実施 owner=hub の split 完了確認済。
