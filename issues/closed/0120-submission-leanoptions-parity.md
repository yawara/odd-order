---
id: 120
slug: submission-leanoptions-parity
title: "feit_thompson 提出: FeitThompson 閉包の leanOptions parity (autoImplicit=false 化 + maxSynthPendingDepth 局所化)"
created: 2026-07-15
---

# feit_thompson 提出: FeitThompson 閉包の leanOptions parity (autoImplicit=false 化 + maxSynthPendingDepth 局所化)

## 背景

lean-eval `feit_thompson` への提出（`../odd-order-submission`, 方針 = そこの
`SUBMISSION_STRATEGY.md`）では、`OddOrder.feitThompson` の import 閉包（起点から推移的に辿った
**565 ファイル**, 同 §5.2）を提出 workspace の `Submission/` 配下へ vendoring する。

問題は **提出側 lakefile が trusted scaffold で編集不可**（採点時に pristine な
`generated/feit_thompson/` から取り直される）で、その `[leanOptions]` は **`autoImplicit = false` の
1 行のみ**である点。一方 odd-order の lakefile は:

```toml
[leanOptions]
relaxedAutoImplicit = false
maxSynthPendingDepth = 3
# autoImplicit は未設定 = 既定 true
# 他に pp.unicode.fun / weak.linter.* (これらは build 非致命)
```

Lean のビルド結果はソースだけでなく有効な option に依存し、option は import を跨がない。よって閉包を
提出側の option 集合でそのままビルドすると、**odd-order 固有の global option に依存していたファイルが
落ちる**（同 §5.6）。従来案は「コピー各ファイル冒頭に `set_option` を注入」だが、抽出を機械作業
（import 行の書換のみ）に留めるため、**odd-order 本体側でこれらの option に非依存化しておく**方が堅牢
（ユーザ方針 2026-07-15）。autoImplicit=false 化は mathlib 標準への整合という独立の価値もある。

現状: local `set_option maxSynthPendingDepth` / `set_option autoImplicit` は **0 箇所**（挙動は完全に
lakefile global に依存）。

### option 別分析（odd-order → 提出 の方向）

1. **autoImplicit** — odd-order 既定 `true` / 提出 `false`。裸の未束縛識別子を暗黙引数へ自動昇格する
   箇所があると、提出側 `autoImplicit=false` で「unknown identifier」。→ **odd-order lakefile を
   `autoImplicit = false` に**し、fallout を明示バインダ化。`weak.linter.mathlibStandardSet = true` が
   既に効いているので実依存は少ない見込みだが**要計測**。
2. **relaxedAutoImplicit** — odd-order `false`（厳格）/ 提出 既定 `true`（緩和）。厳格→緩和は緩める
   方向で、かつ `autoImplicit=false` 化後は完全に無効化されるので **単独対応は不要**（1 に吸収）。
3. **maxSynthPendingDepth** — odd-order `3` / 提出 既定（< 3）。深さ 3 を要する typeclass 合成の宣言が
   あると提出側で「型クラス合成失敗」。→ 閉包を既定深さでビルドして**必要箇所を特定**し、その宣言に
   `set_option maxSynthPendingDepth 3 in` を局所付与（コピーに随伴）。global は除去（or 局所被覆を確認）。

## やること

- [ ] **計測**: `[leanOptions]` を `autoImplicit = false` のみに差し替えた lakefile で
      `OddOrder.feitThompson` 閉包をビルドし、fallout（autoImplicit 依存 / depth 依存）を列挙。
      （global `maxSynthPendingDepth 3` が実際に load-bearing かも同時に判明する。）
- [ ] **autoImplicit=false 化**: `lakefile.toml [leanOptions]` に `autoImplicit = false` を追加し、
      エラー箇所を明示バインダ（`{G : Type*}` 等）へ修正。以後の new code も autoImplicit-clean を維持
      （parity drift の恒久防止）。
- [ ] **maxSynthPendingDepth 局所化**: 深さ 3 を要する宣言に `set_option maxSynthPendingDepth 3 in` を
      付与し、global を lakefile から除去（局所被覆を確認のうえ）。
- [ ] **relaxedAutoImplicit**: autoImplicit=false 化後の余剰確認。不要なら lakefile から除去（残置も無害）。
- [ ] **回帰 + drift 検出**: `lake build OddOrder` green。可能なら「提出相当の leanOptions
      （`autoImplicit=false` のみ）で閉包をビルドする」ローカル/CI チェックを追加し、以後の parity 崩れを
      検出できるようにする。

## 完了条件

- `OddOrder.feitThompson` の import 閉包が、**`[leanOptions] autoImplicit = false` のみ**（提出 scaffold と
  同一）の lakefile で **green build**。
- odd-order 本体の `lake build OddOrder` が green（autoImplicit=false ＋ maxSynthPendingDepth 局所化後）。
- 結果として、提出時の vendoring が **per-file `set_option` 注入を要さず import 行の書換だけ**で済む
  （`SUBMISSION_STRATEGY.md` §5.3 の最小 re-root がそのまま成立）。

## 注記（スコープ・段取り）

- 本件は FT 数学スパインの積み上げではない submission-prep infra（`CLAUDE.md` の FT 経路限定・issue 0050 で
  submission 系は park 扱い）だが、ユーザ明示指示による。autoImplicit=false 化は mathlib 整合として
  **単独価値**もある。
- global lakefile option の変更は 3 レーン a/b/c 全体に波及するため、**hub 調整点（各レーンが当該境界で
  idle なタイミング）で実施**するのが安全。autoImplicit=false は「以後も維持」の規律として入れておくと
  parity drift を恒久的に防げる。
- `maxSynthPendingDepth` の局所化は、まず「global を外して閉包が green か」を試し、落ちた宣言にだけ
  局所付与する**最小介入**でよい（不要に多く付けない）。

## 参照

- 提出方針: `../odd-order-submission/SUBMISSION_STRATEGY.md` §5.6 (lean option parity) / §5.2 (閉包 565) /
  §5.3 (最小 re-root)
- issue [0050](0050-lean-eval-submission-candidates.md)（lean-eval 提出候補・park）,
  `notes/meta/lean_eval_baer_suzuki.md`（前例）
- `notes/meta/mathlib_v432_migration.md`（option 関連の既往）
- 対象: `lakefile.toml [leanOptions]`（現状 `relaxedAutoImplicit=false` / `maxSynthPendingDepth=3` /
  `autoImplicit` 未設定）
