---
id: 7
slug: isaacs-ch01-03-linter-warnings
title: "Ch.1-3 + 関連 Mathlib 補助モジュールの linter 警告クリーンアップ"
created: 2026-05-24
---

# Ch.1-3 + 関連 Mathlib 補助モジュールの linter 警告クリーンアップ

## 背景

`lake build OddOrder.AxiomsCheck` で発生する linter 警告が累積しており可読性に響く.
ビルドエラーではないが, Ch.1-3 本体が概ね完成した今のタイミングで整理しておきたい.

確認できている主な警告 (2026-05-24 時点, 網羅ではない):

| ファイル | 警告内容 | 数 |
|---|---|---|
| `OddOrder/Mathlib/Subgroup.lean` | `show` → `change` | 1 |
| `OddOrder/Isaacs/Ch01_Sylow/Main.lean` | `simp at` flexible tactic | 2 |
| `OddOrder/Isaacs/Ch02_Subnormality/Main.lean` | `show` → `change`, `push_neg` deprecated, 100 文字超 | 7-8 |
| `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` | `show`, `simpa` → `simp`, unused simp args | 10+ |
| `OddOrder/Mathlib/SchurZassenhausConj.lean` | `show`, unused section vars, `push_neg` deprecated, 100 文字超, unused simp args | ~20+ |

合計 ~40 件規模.

## やること

- [x] `show` → `change` 置換 (ゴールを書き換えるなら `change`, 表示だけなら `show` のまま OK だが
      Lean が「書き換えてる」と判定したケースが警告対象)
- [x] `push_neg` → `push Not` (mathlib v4.29.1 で `push_neg` が deprecated)
- [x] `simpa` → `simp` で済む箇所
- [x] unused simp args の除去
- [x] 100 文字超の改行
- [x] `automatically included section variable(s) unused` の解消 (variable 宣言を section 範囲縮小 or 明示 `omit`)

## 完了条件

- [x] `lake build OddOrder.AxiomsCheck` 実行時の `warning:` 行数が現状 (~40+) から大幅減少
- [x] 該当 5 ファイル群で warning 0

## 完了メモ

`lake build OddOrder.AxiomsCheck` で以下の 0007 対象ファイルから warning が消えたことを確認:
`OddOrder/Mathlib/Subgroup.lean`, `OddOrder/Isaacs/Ch01_Sylow/Main.lean`,
`OddOrder/Isaacs/Ch02_Subnormality/Main.lean`, `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`,
`OddOrder/Mathlib/SchurZassenhausConj.lean`.

残る warning は Ch.4/Ch.5 側で, 本 issue の対象外.

## 参照

- [OddOrder/Isaacs/Ch01_Sylow/Main.lean](../../OddOrder/Isaacs/Ch01_Sylow/Main.lean)
- [OddOrder/Isaacs/Ch02_Subnormality/Main.lean](../../OddOrder/Isaacs/Ch02_Subnormality/Main.lean)
- [OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean](../../OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean)
- [OddOrder/Mathlib/Subgroup.lean](../../OddOrder/Mathlib/Subgroup.lean)
- [OddOrder/Mathlib/SchurZassenhausConj.lean](../../OddOrder/Mathlib/SchurZassenhausConj.lean)
