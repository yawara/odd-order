---
id: 103
slug: split-phase-directory-first
title: "分割フェーズ (bump 後即実施): ディレクトリ化優先で 6k+ 行 11 files を解体"
created: 2026-07-09
---

# 分割フェーズ (bump 後即実施): ディレクトリ化優先で 6k+ 行 11 files を解体

## 背景

- mathlib v4.32.0-rc1 / 360da6fa bump (branch `mathlib-v432`) の green 達成 + main 合流の**直後に hub が実施**する分割フェーズの実行計画。bump branch には分割を混ぜない (diff の review/revert 可能性と lane conflict 面の限定のため)。
- **ユーザー指示 (2026-07-09)**: 巨大ファイルの分割は単純な兄弟 flat 分割でなく、**ディレクトリ化** (Isaacs「1 章 = 1 dir + 入口 Main.lean」パターンの節版、hub .lean + 同名 dir 内 topic leaves) を第一候補にする。単一主題の 2 分割程度のみ flat prefix-split 可。memory 正本 = `feedback-split-prefer-directory`。
- 分割 owner = hub、凍結境界 prefix-split の手順 = `notes/meta/merge_monitor.md` (下流は hub import のまま不変)。

## やること (優先順 = サイズ順、各項は対応 issue の実施)

- [ ] `Peterfalvi/S11_MaximalII_III_IV.lean` 14.3k → dir 化 (II/III/IV の型別クラスタ境界) — #0077
- [ ] `BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` 12.3k → dir 化 — #0069
- [ ] `BG/Ch4_FamilyOfMaximal/S15_MF.lean` 11.4k → dir 化 — #0071
- [ ] `Peterfalvi/S15_SAndT_Setup.lean` 9.4k → dir 化 — #0094
- [ ] `Peterfalvi/S14_MaximalI.lean` 8.5k → dir 化 — #0084
- [ ] `Peterfalvi/S16_NonExistenceG.lean` 8.4k (+ Core 4.9k) → dir 化 — #0072
- [ ] `Peterfalvi/S09_NonexistenceCertain.lean` 6.9k → dir 化 — #0095
- [ ] `BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` 6.8k → dir 化 — #0078
- [ ] `Peterfalvi/S07_Coherence.lean` 6.8k → S08 クラスタと合わせて dir 化検討 — #0085/#0073/9005
- [ ] `Peterfalvi/S12_MaximalIII_IV_V_Core.lean` 6.7k (+ S12 4.8k) → dir 化 — #0076
- [ ] `Isaacs/Ch04_Commutators/Main.lean` 6.3k → 既に dir 内 → topic leaf 切り出し — #0097
- [ ] 各実施時: 対応 issue に「ディレクトリ化優先」方針を確認・記録してから着手。lane frontier と衝突しない凍結境界で切る。
- [ ] AxiomsCheck.lean 7.2k は対象外検討 (機械生成的な列挙ファイル — 分割益が薄い)

## 完了条件

- 上記チェックボックスの完走 (= 実装 .lean で 6k 行超が原則消滅、frontier leaf は 1.5k 行以下に復帰)、各分割ごとに full build green + first-parent commit。

## 参照

- memory: `feedback-split-prefer-directory` / CLAUDE.md「ファイル粒度」「分割の owner と trigger」
- open 分割 issues: 0068 0069 0070 0071 0072 0073 0074 0076 0077 0078 0079 0084 0085 0094 0095 0097 0100 0102 9005
