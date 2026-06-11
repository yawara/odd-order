---
id: 64
slug: s05-narrowpgroups-resplit
title: "S05_NarrowPGroups (4,039 行) の再分割 — E frontier (4.20 API) 凍結後に prefix-split"
created: 2026-06-11
---

# S05_NarrowPGroups (4,039 行) の再分割 — E frontier (4.20 API) 凍結後に prefix-split

## 背景

粒度規約のサイズ watch (merge_monitor 手順 4) が merge `3f4909c4` (Lane E, Thm 4.20(c) 系 +
S05b 新設) で発火: `S05_NarrowPGroups.lean` は **4,039 行** (閾値 1,500 超)。今回の変更自体は
S05b への engine 抽出 refactor (純増 +93 行) で分割**方向**だが、本体の超過は未解消。

S05 は過去に一度分割済み (`954408b2`) だが、その後 Thm 4.20 cluster の成長で再肥大。
**E の現 frontier (Thm 11.7) が 4.20 降順 tower API を消費中**のため、4.20 producer 周辺は
活性 — hub が今 prefix-split すると lane と衝突しうる。

## やること

- [x] E の §11.7 着地 (2026-06-11 merge `77ab5173`; E 退役で S05 全凍結)
- [x] topic 境界の特定 (3 カット: L1394/L2134/L3126 = 5.3, 5.5, 5.6 の各開始) (候補: 先頭の凍結クラスタ [narrow p-group 基礎 API] を上流ファイルへ
      prefix-split し、活性な 4.20 cluster を leaf に残す。S05b_Thm420Hall.lean は既に別 leaf)
- [x] prefix-split 実施 (4 ファイル chain) (手順 = CLAUDE.md「分割の owner と trigger」; 前例 = S08/S12_E/S05
      split commits `1c03ec60`/`b2416203`/`954408b2` の python 境界 assert パターン)
- [x] full build + AxiomsCheck green (OddOrder.lean 登録不要 — chain は S05_NarrowPGroups 経由で root closure 内)
- [x] 下流 import / AxiomsCheck guard 名の不変確認 (module 名 S05_NarrowPGroups 保持; S05b/S09×4/AxiomsCheck 不変)

## 完了条件

S05_NarrowPGroups.lean (および分割後の各 leaf) が 1,500 行未満、full build + AxiomsCheck green、
下流 import 不変。

## 参照

- merge `3f4909c4` (発火点), 前回分割 `954408b2`
- issues/0063-s10-locallemmas-split.md (同型の issue, S10 用)
- CLAUDE.md「分割の owner と trigger」/ notes/meta/merge_monitor.md 手順 4

## ✅ DONE (2026-06-11, hub)

4,039 行 → 4 ファイル prefix-split chain (topic 境界 3 カット):

- `S05_NarrowSCN.lean` (1,369 行): Lem 5.1/5.2 + omega1Center helper 層
- `S05_NarrowCharacterization.lean` (769 行): Thm 5.3 / Cor 5.4
- `S05_NarrowAutomorphisms.lean` (1,021 行): Thm 5.5
- `S05_NarrowPGroups.lean` (976 行): Thm 5.6/5.7 + Thm 4.20(c) — module 名保持で下流不変

cross-boundary private 9 件を de-private (omega1Center 系 4 + witness/card_prime 系 5;
規約: private はファイル内限定)。S05 全凍結後の安全窓で実施。
