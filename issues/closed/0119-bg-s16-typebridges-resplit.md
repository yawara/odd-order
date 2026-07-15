---
id: 119
slug: bg-s16-typebridges-resplit
title: "BG S16 TypeBridges 1542行を凍結境界で再分割"
created: 2026-07-15
---

# BG S16 TypeBridges 1542行を凍結境界で再分割

## 背景

2026-07-15 の hub 20 分 tick で lane c の固定 SHA `9b9986b9` を merge
(`72847361`)。`OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeBridges.lean`
は c-2 の vestigial surface 整理により `+8/-7`、現在 **1542 行**となり、
`notes/meta/merge_monitor.md` の size watch (既存 1500 行超 leaf への追記) が発火した。

旧 issue 0078 で `S16_MainResults.lean` のディレクトリ化は完了済みだが、現在の
`TypeBridges.lean` 自体を再分割する open issue は無いことを確認済み。c-2 の BG 整理は
完了し、次 frontier は Peterfalvi S16 側なので、この BG leaf は凍結境界を取れる。

同 tick で 1500 行を超えていた他の touched leaf はいずれも非成長
(`TheoremsAE.lean` 1628 行, net -31 / `TypeP1Criteria.lean` 1574 行, net 0 /
`S15_BridgeCharacter.lean` 1677 行, net -2) のため、本 trigger の対象外。

## やること

- [ ] 宣言クラスタを確認し、topic-coherent な凍結 prefix を記述的英語名の sibling leaf へ移す
- [ ] `TypeBridges.lean` の module 名と下流 import を不変に保ち、新 leaf を import する
- [ ] 分割前後の宣言名 multiset・signature・`sorry` 数が一致することを機械確認する
- [ ] `lake build OddOrder OddOrder.AxiomsCheck` を通す

## 完了条件

分割後の各実装 leaf が 1500 行以下になり、root closure・全体 build・AxiomsCheck が green、
新 `axiom`・`sorry` regression・signature drift が無い。実施 owner は hub。

## 参照

- `notes/meta/merge_monitor.md` step 4 (size watch)
- `issues/closed/0078-s16-mainresults-split.md`
- `issues/closed/0118-lane-redesign-2026-07-15-endgame.md` (c-2)
- merge commit `72847361`

## ✅ 完了 (2026-07-15)

- c-2 完了後の凍結条件を再確認し、type-V forward cluster を安全な宣言境界で分割。
- `S16_MainResults/TypeVSinger.lean` (605 行) に Singer structure と Prop. 16.1(d) forward bridge を移した。
- 親 `TypeBridges.lean` は reverse classification / Theorem A cluster を保持して 977 行。
- 分割前後の宣言名 multiset は完全一致し、機械移動により signature と下流 module 名を保存。
- 当該 cluster の実 `sorry` は 0 → 0、BG hub・Peterfalvi downstream の import closure も維持。
- focused build 3208 jobs、`lake build OddOrder OddOrder.AxiomsCheck` 4246 jobs 完走・AxiomsCheck OK。
