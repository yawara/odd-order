---
id: 185
slug: lean-panic-expr-appargs
title: "ビルド中に 180 件の PANIC (Lean.Expr.appArg!) — Algebra/BrauerSuzukiEndgame:195"
created: 2026-08-20
---

# フルビルド中に 180 件の PANIC が出る (非致命だがログを埋める)

## 事実 (2026-08-20 実測)

`lake build OddOrder OddOrder.AxiomsCheck` のログに

```
info: OddOrder/Algebra/BrauerSuzukiEndgame.lean:195:0: PANIC at Lean.Expr.appArg! Lean.Expr:936:15: application expected
backtrace:
  <libleanshared.so の C スタックが 30 行ほど>
```

が **180 回**出る。全て**同一の宣言** `exists_eq_of_columns`
([Algebra/BrauerSuzukiEndgame.lean:195](../OddOrder/Algebra/BrauerSuzukiEndgame.lean)) 由来で、
`Lean.Expr.appArg!` と `Lean.Expr.appFn!` が交互に出る。

- **非致命**: `info` レベルで、ビルドは green・警告 0・`#print axioms` も clean。
  `bin/check-warnings --strict` にも引っかからない (warning ではないため)。
- **本セッションの変更とは無関係**: 当該 file は `ec5bfad6f..HEAD` で一切触っていない
  (最終変更は `25af7b69b`、issue 9506 の modular 段 366)。
- **提出物にも伝播する**: `odd-order-submission/brauer_suzuki` の抽出コピーでも
  同じ 180 件が同じ file/line から出る (件数完全一致)。lean-eval CI のログも同様に埋まる。

## なぜ潰したいか

正しさの問題ではないが、**フルビルドのログに 180 件のスタックトレースが混ざると本物の
異常が埋もれる**。実際このセッションでは `grep -E "^error|warning:"` では見えず、
提出ビルドのログを読んでいて偶然見つけた (= 既存の gate を素通りしていた)。

## やること

- [ ] `exists_eq_of_columns` の証明本体を二分して、PANIC を出す tactic を特定する
      (`omega` / `simpa` / linter のいずれか。宣言は仮説 20 本超・証明数百行)
- [ ] 回避できるなら書き換える (tactic 置換 or 補題分割)。
      Lean 側のバグなら最小再現を作って upstream に報告し、ここには回避策と参照を残す
- [ ] gate に「PANIC を検出したら赤」を足すか検討 (`bin/check-warnings` は warning しか見ない)

## 参照

- 発見の経緯: [0184](0184-brauer-suzuki-eval-submit.md) の submission build 検証
- 当該宣言の数学: Navarro pp.142–145 (issue 9506 の modular 段 336–366)
