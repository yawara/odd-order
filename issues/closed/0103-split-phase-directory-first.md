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

- [x] `Peterfalvi/S11_MaximalII_III_IV.lean` 14.3k → dir 化 (II/III/IV の型別クラスタ境界) — #0077
- [x] `BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` 12.3k → dir 化 — #0069
- [x] `BG/Ch4_FamilyOfMaximal/S15_MF.lean` 11.4k → dir 化 — #0071
- [x] `Peterfalvi/S15_SAndT_Setup.lean` 9.4k → dir 化 — #0094
- [x] `Peterfalvi/S14_MaximalI.lean` 8.5k → dir 化 — #0084
- [x] `Peterfalvi/S16_NonExistenceG.lean` 8.4k (Core 4.9k は未) (+ Core 4.9k) → dir 化 — #0072
- [x] `Peterfalvi/S09_NonexistenceCertain.lean` 6.9k → dir 化 — #0095
- [x] `BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` 6.8k → dir 化 — #0078
- [x] `Peterfalvi/S07_Coherence.lean` 6.8k (S08 クラスタは別途 0073/9005) → S08 クラスタと合わせて dir 化検討 — #0085/#0073/9005
- [x] `Peterfalvi/S12_MaximalIII_IV_V_Core.lean` 6.7k (S12 本体 4.8k は 0076 に残) (+ S12 4.8k) → dir 化 — #0076
- [x] `Isaacs/Ch04_Commutators/Main.lean` 6.3k → 既に dir 内 → topic leaf 切り出し — #0097
- [ ] 各実施時: 対応 issue に「ディレクトリ化優先」方針を確認・記録してから着手。lane frontier と衝突しない凍結境界で切る。
- [ ] AxiomsCheck.lean 7.2k は対象外検討 (機械生成的な列挙ファイル — 分割益が薄い)

## 完了条件

- 上記チェックボックスの完走 (= 実装 .lean で 6k 行超が原則消滅、frontier leaf は 1.5k 行以下に復帰)、各分割ごとに full build green + first-parent commit。

## 参照

- memory: `feedback-split-prefer-directory` / CLAUDE.md「ファイル粒度」「分割の owner と trigger」
- open 分割 issues: 0068 0069 0070 0071 0072 0073 0074 0076 0077 0078 0079 0084 0085 0094 0095 0097 0100 0102 9005

## 第 1 パス完了 (2026-07-09)

11 files 全て dir 化分割済 (機械分割 tool = lean_split.py、宣言 namespace 文脈 + decl 名 multiset +
sorry 数の保存検証、full build green 3m59s、AxiomsCheck sorryAx 0)。

**残 (第 2 パス)**: mathlib 実測基準 (longFile linter 上限 1500 行、2000 超ゼロ) に照らすと
leaves の多く (1.5k-4.2k) がまだ超過。>3k の 4 leaves (S14_TPC/TypePDuality 4.1k、
S15_MF/Corollary155 4.2k、S15_MF/TIFailure 3.8k、S11/SummandComplementKernel 4.0k) を優先に
再分割するか、上限値 (1500 vs 2000) の裁定待ち。`weak.linter.style.longFile` の lakefile 有効化も
候補 (mathlib 方式の機械的 enforcement)。

## 第 2 パス完了 (2026-07-09) — issue close

上限 2000 行 (ユーザー裁定) で全 file 適合完了。55 files を flat prefix-split、
lakefile に weak.linter.style.longFile/longFileDefValue = 2000 を有効化 (mathlib 方式の
機械的 enforcement)。例外 = S03f_Thm36 (4000、単一巨大宣言) / AxiomsCheck (7400、機械列挙)。
検証: 宣言 multiset 保存 / sorry 81 / AxiomsCheck clean / full build green。
tool = scratchpad の lean_split.py (map/auto/split/splitflat/verify)。
残: S12 本体は 0076 で S12_Props109To1011/S12_HypothesisLayer に分割済 — 0076 も close 可。
