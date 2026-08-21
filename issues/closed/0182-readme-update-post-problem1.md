---
id: 182
slug: readme-update-post-problem1
title: "README 更新 — Problem 1 解決と 3 冊逐条監査完了を反映 (英日両方)"
created: 2026-08-13
---

# README 更新 — Problem 1 解決と 3 冊逐条監査完了を反映 (英日両方)

## 背景

[README.md](../../README.md) / [README.ja.md](../../README.ja.md) に、その後の 2 つの大きな
マイルストーンが未反映のまま残っている:

1. **BG App.C Problem 1 (Péterfalvi 1993) の否定的全面解決 + 完全機械検証**
   (2026-08-13、[issue 0180](0180-bg-appc-problem1-p-eq-three.md) /
   [0181](0181-skew-calculus-lean-formalization.md) closed)。33 年 open だった
   問題への `Problem1.hypothesisB_false` (全 `q`・`G` 無限可・追加仮定ゼロ・axiom-clean)。
   README は「教科書の形式化」としての記述のみで、**プロジェクト発の新規数学的成果**
   (形式化を超えた original result) に一切触れていない。
2. **3 冊逐条監査の完了** (2026-08-08、全 775 件: Peterfalvi 284 =
   [0172](0172-peterfalvi-full-formalization.md) / Isaacs 305 =
   [0176](0176-isaacs-full-formalization.md) / BG 186 =
   [0177](0177-bg-full-formalization.md)、番号付き結果の真の未形式化 = 0 件)。
   README の Coverage 段落は 2026-07-16 survey (815 件・213 remaining) のスナップショット
   + 「later spot checks found labels unreliable」で止まっており、完了した監査の存在を
   伝えていない。

また細部の数値も既に古い: OddOrder/ は実測 **1,705 files / ~841k 行** (README は
~1,680 / ~830,000)、フルビルド jobs 数 (README は ~5,450) も要再実測。

## やること

- [ ] **Status 節に Problem 1 の解決を追加**: 何が問題だったか (1 段落)、
      `hypothesisB_false` の statement、正本 =
      [`notes/bg/appC_problem1_resolution.md`](../../notes/bg/appC_problem1_resolution.md)、
      俯瞰 = [`notes/bg/appC_problem1_summary.md`](../../notes/bg/appC_problem1_summary.md)。
      「Beyond the Feit–Thompson theorem」の並びに独立の小節を立てるか Status に追記するかは
      書き手判断 (README の現行トーン = 抑制的・検証可能な事実のみ、に合わせる)。
- [ ] **Coverage 段落を逐条監査完了に置換**: 監査 3 本 (0172/0176/0177、計 775 件、
      2026-08-08 完了) を一次情報にし、2026-07-16 survey は歴史的出発点としての言及に
      格下げ (現行の「unreliable」注記の枠組みはそのまま使える)。
      ⚠ **「3 冊 done」とは書かない** — 監査が言うのは「番号付き結果の未形式化 0」であり、
      残債の正確な言い回し (特殊化の一般化残り等) は**更新時に closed 0172/0176/0177 の
      最終集計を読み直して取る** ([[verify-port-state-by-number-not-coq-name]] の精神で
      README に書く数字は全て一次情報から再取得)。
- [ ] **数値の再実測**: `find OddOrder -name '*.lean' | wc -l` / 総行数 /
      フルビルド jobs 数 (`lake build OddOrder` の表示)。sorry-free 主張 (2026-08-07 付)
      が現在も真か `grep` で再確認してから日付を残す。
- [ ] **外部文献リストの検討**: 「Three bodies of proof come from outside」の並びに
      Glauberman–Norton 1993 (Problem 1 の原論文、`references/glauberman-norton/`) を
      追加するか検討 — Problem 1 節を立てるならそちらに置く方が自然かもしれない。
- [ ] **README.ja.md を同内容に同期** (英日は必ず同時更新、片方だけの commit にしない)。

## 完了条件

README.md と README.ja.md の両方が上記 4 点を反映し、記載の数値 (files / 行数 / jobs /
監査件数) がすべて更新時点の実測または一次情報 (closed issue の最終集計) と一致していること。
docs-only なのでビルド gate は不要だが、リンク切れが無いことを確認して commit。

## 消化記録 (2026-08-14, close)

4 項目すべて実施 (英日同時):

1. **Problem 1**: Status に ★ blockquote + 独立節「An open problem resolved: Problem 1 of
   Appendix C」/「未解決問題の解決: Appendix C の Problem 1」を新設 (Building の直前)。
   問題の出自 (Péterfalvi 提起、GN 1993 PAMS 119 p.1094 初出、BG p.152 再掲)、条件 (B) の内容、
   `p = 2` 実現 / `p ≥ 5` 排除 / `p = 3` open の文脈、`hypothesisB_false` の statement、
   全 `q`・`G` 無限可・axiom-clean、14 leaf ≈ 8,700 行、正本 2 note へのリンクを記載。
   **Glauberman–Norton 1993 の書誌はこの節に置いた** (「Three bodies of proof」リストではなく —
   役割が「外部証明の形式化元」でなく「問題の出自 + Prop 7」なので)。
2. **Coverage 段落置換**: 逐条監査 3 本 (0172/0176/0177、775 件、2026-08-08) を一次情報化。
   最終集計どおり「書籍強度 statement (sorry-free ゆえ証明済) or mathlib カバー、特殊化債務 0」。
   「3 冊 done」とは書かず、番号無し素材 (章末問題・Remark) が別トラックである旨を明記。
   2026-07-16 survey は歴史的スナップショットに格下げ。Status にも ✅ blockquote 追加。
3. **数値再実測** (2026-08-14): 1,705 files / 840,973 行 (→ ~841,000) / フルビルド 5,470 jobs
   (実測、AxiomsCheck OK 出力確認)。sorry = 0 を comment-strip census + `bin/count-sorry` の
   両方で再確認 (2026-08-07 の日付は初達成日として保持)。
4. **リンク検査**: 両 README の相対リンク全数 + in-page anchor を機械検査、全通過。

## 参照

- [issue 0180](0180-bg-appc-problem1-p-eq-three.md) (Problem 1 経緯 + 最終総括) /
  [0181](0181-skew-calculus-lean-formalization.md) (Lean 化)
- [`notes/bg/appC_problem1_resolution.md`](../../notes/bg/appC_problem1_resolution.md) (統合証明文書) /
  [`appC_problem1_summary.md`](../../notes/bg/appC_problem1_summary.md) (俯瞰まとめ)
- 逐条監査: [0172](0172-peterfalvi-full-formalization.md) /
  [0176](0176-isaacs-full-formalization.md) /
  [0177](0177-bg-full-formalization.md)
- 現行 README の該当箇所: Status 節 (l.12–31) / Coverage 段落 (l.72–79) /
  Repository layout の数値 (l.100) / Building の jobs 数 (l.94)
