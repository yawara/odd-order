---
id: 50
slug: lean-eval-submission-candidates
title: "lean-eval への proof 提出 (tracker)"
created: 2026-05-30
---

# lean-eval への proof 提出 (tracker)

> **正本 = [`notes/meta/lean_eval_submission.md`](../notes/meta/lean_eval_submission.md)** (単一ドキュメント)。
> 提出 playbook・候補全表 (Tier A/B/C)・reject 記録・eval 側仕様は**全てそこ**。
> 本 issue は actionable checklist のみを持つ tracker。個別提出は per-problem sub-issue (0042 型) を切る。
>
> 2026-07-22 に旧 3 note (baer_suzuki / candidates_2026_07_19 / forward_list_2026_07_22) を
> 1 本に統合 (「proof を submit する」観点)。

## 背景 (要点)

`leanprover/lean-eval` は comparator 方式の公式 formal-math ベンチ。本リポ (3 冊の形式化) は
「mathlib 未収録の研究級有限群論定理」を量産できる立場。**既提出 2 件**: `baer_suzuki`
(2026-05-29, #118) / `feit_thompson` (2026-07-16, #828)。良い候補 3 軸 = 有名 / statement が
self-contained / 証明が難しく mathlib 未収録。詳細と全候補は正本 note。

## やること

- [ ] **🆕 (提案) Glauberman ZJ 定理** — 2026-07-22 完成 (`GlaubermanZJ.lean`、伝説級・mathlib/eval
      双方に無い)。⚠ AxiomsCheck 未登録 → 提出前に `#print axioms` で axiom-clean 確定
- [ ] **🆕 (提案) B.H.Neumann 位数 3** (`lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three`、
      登録済・bespoke≈0) + **一般 Hall–Petresco** (`HallPetresco.exists_hallPetresco`、登録済、旧 class≤3 を差替)
- [ ] **🎯 (解答) `brauer_suzuki` = issue 9318 完走** — Tier B 唯一の「既存未解決を解答」経路 (≈38%、lane c)
- [ ] **(提案) Jordan の定理** — mathlib が `proof_wanted` で明示、bespoke 0。
      `lake exe lean-eval validate-manifest` + `check-problem-build` で検証してから PR
- [ ] **(提案) Chermak–Delgado / Furtwängler / Thompson FPF-nilpotency** を続けて提案 PR。
      提案先 merge、solver は他者開放 (`feit_thompson` 前例)
- [ ] **(整備) AxiomsCheck 未登録の strong 候補を登録** — ZJ / Replacement / Galois–Burnside /
      Ch08 Jordan / PSL 単純性 / `isCritical_exists` / `transfer_transfer` / Ch01 Fitting /
      `span_range_representation_eq_top` (いずれも `#print axioms` で clean 実測済)
- [ ] **(整備) stale docstring 掃除** — `burnside_p_pow_q_pow`「local axiom 封じ込め」/
      `Ch07.normal_J`「Remaining local axioms」/ `AppC_NormSet`「to be formalized」/
      `brauer_permutation_lemma'`「Isaacs Thm 6.32」誤引用ほか (正本 note §8)

## 完了条件

- アンブレラ tracker。提案 PR がそれぞれ per-theorem sub-issue (0042 型) に落ちきったら close。
- 単発の提出そのものは各 sub-issue 側の完了条件 (eval submit 可能形 + `AxiomsCheck` pass) に従う。

## 参照

- **正本**: [`notes/meta/lean_eval_submission.md`](../notes/meta/lean_eval_submission.md)
- lean-eval: https://github.com/leanprover/lean-eval / 提出先 https://github.com/leanprover/lean-eval-submissions / 公開面 https://lean-lang.org/eval/
- 先行 issue: 0042 (Baer–Suzuki, closed), 0120 (feit_thompson leanOptions parity, closed)
- 文献: 100 定理未形式化は幾何/解析中心で群論の低い果実は無い
  (https://leanprover-community.github.io/100-missing.html); research-level は SOTA でも
  pass 率 ~10% (RLMEval, https://arxiv.org/pdf/2510.25427)

## 🧾 履歴

- 2026-07-02 hub レビューで「off-FT-path につき park」→ **2026-07-16 に FT 本体 axiom-clean 完成 →
  全 3 冊フェーズ移行**で park 前提失効、再び active。
- 2026-07-19 候補表を実測で全面差し替え。
- 2026-07-22 lean-eval 関連 3 note を [`lean_eval_submission.md`](../notes/meta/lean_eval_submission.md)
  に統合、本 issue を tracker 化。ZJ 定理の reject を撤回 (完成確認)。
