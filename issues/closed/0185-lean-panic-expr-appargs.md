---
id: 185
slug: lean-panic-expr-appargs
title: "ビルド中に 180 件の PANIC (Lean.Expr.appArg!) — Algebra/BrauerSuzukiEndgame:195"
created: 2026-08-20
---

# フルビルド中に 180 件の PANIC が出る (非致命だがログを埋める)

## 状態: ✅ **CLOSED (2026-08-20)** — 発生源を特定して解消

発生源は `exists_eq_of_columns` 内の **`(by simpa using hpair 0 2)` の 1 箇所**。
`simp` を使わない形に置換して **PANIC 0 件**、フルビルド green (5491 jobs / 3m2s)、
警告 0、AxiomsCheck 全件 OK。詳細は下記「消化記録」。

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

- [x] `exists_eq_of_columns` の証明本体を二分して、PANIC を出す tactic を特定する
- [x] 回避できるなら書き換える
- [x] gate に「PANIC を検出したら赤」を追加 — `bin/check-warnings` が `PANIC at <fn>` を
      拾い、直前の `info: <path>:L:C:` から file を帰属させて集計。gate / `--strict` では
      **1 件でも exit 1** (baseline は持たない = 常にゼロ要求)。CI の
      `bin/check-warnings --strict` がそのまま拾う。
      検証 = 直した `simpa` を一時的に戻すと `PANIC: 180 件 / 2 箇所` を検出して exit 1

## 消化記録 (2026-08-20)

**切り分け**: 単体 file を `lake build` して 180 件を再現 → statement だけを残した probe を
`lake env lean` に食わせると **0 件** ⟹ 証明本体が原因。本体を top-level tactic step 単位で
二分 (prefix + `sorry`) すると、step 19 まで 0 件・step 20 で 180 件。

**犯人**: `(by simpa using hpair 0 2)`。**index 1 の同形 step (`hpair 0 1`) では起きず、
index 2 でだけ起きる**。`hpair 0 2 : ∑ k, ![u₁,u₂,u₃] 0 k * ![u₁,u₂,u₃] 2 k =
1 + 2 * (if (0 : Fin 3) = 2 then 1 else 0)` なので、`simp` が
`![u₁, u₂, u₃] 2` を潰す (`Matrix.cons_val` 系 simproc) か
`if (0 : Fin 3) = 2` を決定するあたりで Lean 4.33 の内部が非適用項に
`Expr.appArg!` を当てている。⚠ 誤った proof が出るわけではない (証明項は正しく、
kernel も通る) — 出力が汚れるだけ。

**対処** (commit で本文参照):

```lean
(by have h : (∑ k, u₁ k * u₃ k) = 1 + 2 * (if (0 : Fin 3) = 2 then 1 else 0) := hpair 0 2
    rwa [if_neg (by decide), mul_zero, add_zero] at h)
```

`have … := hpair 0 2` は行列リテラルを defeq で通すので `simp` を呼ばない。
隣の `hpair 0 1` 側も同形に揃え、「`simpa` に戻すな」の理由をコメントで残した。
ついでに同宣言の no-op rewrite `rw [Finset.sum_congr rfl fun k _ => rfl]` 2 箇所も削除。

**upstream 報告は保留**: 最小再現は「大きな文脈での `simpa` + `![_,_,_] 2`」で、
そのまま切り出すと再現しない可能性が高い。回避策が 1 行で済み実害が無いので、
Lean 側への報告はコスト対効果で見送る (再発したらここに追記)。

## 参照

- 発見の経緯: [0184](0184-brauer-suzuki-eval-submit.md) の submission build 検証
- 当該宣言の数学: Navarro pp.142–145 (issue 9506 の modular 段 336–366)
