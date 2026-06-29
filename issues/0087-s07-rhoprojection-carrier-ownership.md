---
id: 87
slug: s07-rhoprojection-carrier-ownership
title: "S07_RhoProjection.lean を lane b 所有として carve-out (§7 ρ 機構)"
created: 2026-06-29
---

# S07_RhoProjection.lean を lane b 所有として carve-out (§7 ρ 機構)

## 背景

2026-06-29 の区切り合流で、lane b (β = Pf §12 Dade tower, 所有 = S14_MaximalI) が
`OddOrder/Peterfalvi/S07_RhoProjection.lean` を**新規作成**した (§7 ρ projection の
(7.1) averaging value 構成、axiom-clean、build-green)。

lane b の (12.16) endgame が「真の gate = §7 ρ 機構」に bottom-out したため、ρ 機構を
S07 namespace の新規独立ファイルとして構築したもの。S07 namespace は原則 lane a 所有
(Peterfalvi/S0[3-9]|1[0-3]) だが、S07_RhoProjection.lean は **新規独立ファイルで lane a は
不接触**ゆえ衝突リスクは最小 (lane d/S10 の bgTheoremE_cover_data 同型だが、こちらは
co-edited file でなく単独新規ファイルのため一層クリーン)。

ユーザー裁可 (2026-06-29): **承認合流 + S07_RhoProjection を lane b 所有に carve-out** を選択
→ commit `c9e6a7bc` で hub 承認合流済。

## やること

- [x] lane b の S07_RhoProjection.lean を hub 承認で合流 (commit `c9e6a7bc`)
- [x] merge_monitor.md の 🔒 所有マップに carve-out 記載 (S07_RhoProjection.lean = lane b 所有)
      → 監視の範囲逸脱チェックで除外
- [ ] 将来 §7 ρ 機構が拡張し複数ファイル化するなら、§7 ρ サブトピック全体の所有を
      lane b に明示する (or lane a と協調); 現状は単一ファイル carve-out で足りる

## 完了条件

S07_RhoProjection.lean の所有が監視マップ上で明確 (carve-out 済) で、lane a / lane b の
S07 編集が衝突しない運用が確立していること。

## 参照

- merge_monitor.md 🔒 所有マップ (carve-out 追記先)
- `OddOrder/Peterfalvi/S07_RhoProjection.lean` (lane b 新規作成)
- issue 0086 (lane d/S10 bgTheoremE_cover_data 同型の carve-out 先例)
- issue 0081 (lane b §12 本体), commit `2da3ac95` (作成), `c9e6a7bc` (hub 承認合流)
