---
id: 86
slug: s10-bgtheoreme-carrier-ownership
title: "S10 の bgTheoremE_cover_data 共有 carrier 所有を明確化 (lane d 例外)"
created: 2026-06-29
---

# S10 の bgTheoremE_cover_data 共有 carrier 所有を明確化 (lane d 例外)

## 背景

2026-06-29 の合流 tick で、lane d (δ = BG/** + FeitThompson carrier 所有) が
`OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` (lane a 所有) 内の
`bgTheoremE_cover_data` (Pf 8.17, BG Theorem E carrier) の body を実装した
(commit `46505972`、sorry → 9/11 field 実証 + deep gate 2、build-green)。

これは strict には permanent な所有ポリシー (各レーンは自所有ファイルのみ編集) への抵触で、
監視ループは一旦 STOP した。実体は「**lane d の carrier が物理的に lane a の spine ファイル
S10 に同居している**」という所有境界のミスマッチで、内容は genuine・build-green・line 570
の単一宣言に局所化 (lane a が触る他の S10 部分には不接触)。

`bgTheoremE_cover_data` / `BGTheoremECoverData` は **b/c/d が consume する cross-lane
共有 carrier** (consumer: S10 / S14_MaximalI / S15_SAndT / S16_MainResults)。

ユーザー裁可 (2026-06-29): **承認合流 + 所有明確化 issue** を選択 → commit `e28908aa` で
hub 承認合流済。本 issue は所有境界の恒久的な明確化を追跡する。

## やること

- [x] lane d の bgTheoremE_cover_data 実装を hub 承認で合流 (commit `e28908aa`)
- [x] merge_monitor.md の 🔒 所有マップに carve-out 記載 (S10 の bgTheoremE_cover_data /
      BGTheoremECoverData / BGTheoremETypeICovering / BGTheoremENonTypeICovering ブロックは
      lane d 所有 = 監視の範囲逸脱チェックで除外) → 監視ループ再開
- [ ] 恒久解の選択 (将来):
  - 案 X: 現状維持 (S10 内 carve-out で運用; lane a は line 493-570 周辺を編集しない)
  - 案 Y: carrier を lane d 所有ファイル (BG or FeitThompson carrier area) へ移設 +
    4 consumer の参照更新 (境界は最もクリーンだが cross-lane refactor)
- [ ] 残 deep gate 2 個 (bgTheoremE_cover_data の 11 field 中 2) を lane d が genuine に埋める

## 完了条件

bgTheoremE_cover_data の所有が監視マップ上で曖昧でなくなり (carve-out 記載済)、
かつ将来の lane a / lane d の S10 編集が衝突しない運用が確立していること。
理想的には carrier の物理配置 (案 X 維持 or 案 Y 移設) を確定する。

## ✅ CLOSE (2026-07-02 3 レーン再編) — carve-out 解消、carrier は file owner (lane a) に fold

lane d 退役に伴い本 carve-out は**解消**。bgTheoremE carrier (`BGTheoremECoverData` /
`BGTheoremETypeICovering` / `BGTheoremENonTypeICovering` / `bgTheoremE_cover_data`) の所有 =
S10 file owner **lane a** (merge_monitor 🔒 3 レーンマップ更新済)。恒久解は「案 X 相当
(S10 内に残置、所有は file owner)」で確定。残 deep gate (TypeICovering 分岐 = route B) は
issue 8022 で追跡 (§8 Dade-support 前提は issue 0096 carve-out = lane b)。
(2026-07-02 hub、ユーザー委任レビュー)

## 参照

- merge_monitor.md 🔒 所有マップ (carve-out 追記先)
- `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean:493,570` (BGTheoremECoverData 構造 + bgTheoremE_cover_data 定理)
- issue 8020 (BG signalizer functor port, lane d 本体)
- commit `46505972` (lane d 実装), `e28908aa` (hub 承認合流)
