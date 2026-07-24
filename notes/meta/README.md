# notes/meta — index (正本の一覧)

> issue 0139 (正本/ログ分離、2026-07-24) で整理。**このディレクトリ直下 = 生きた規約・参照**、
> [`log/`](log/) = 日付付きの handoff / audit / 旧計画 / 旧 tick ログ (更新されない歴史)。
> 新しい dated 記録は書いた時点で `log/` に置くこと。

## 運用の正本 (hub / lane 規約)

| file | 内容 |
|---|---|
| [`merge_monitor.md`](merge_monitor.md) | ★ hub 合流モニターの手順 + 直近 tick (旧 tick は `log/merge_monitor_ticks.md`) |
| [`ft_path_policy.md`](ft_path_policy.md) | 作業順序 (上流優先+文書順)・frontier 自律の正本 (§0) |
| [`lane_reallocation_2026_07_16.md`](lane_reallocation_2026_07_16.md) | レーン配分の正本 (全 3 冊フェーズ、a/b/c) |
| [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md) | レーン運用原則の完全正本 (4 原則 + STOP 条件) |
| [`issue_management.md`](issue_management.md) | file-based issue 運用 (採番レンジ・状態遷移) |
| [`worktree_setup.md`](worktree_setup.md) | 並行 worktree の作成・main 同期・撤収 |
| [`lane_loop_policy.md`](lane_loop_policy.md) / [`lane_self_resume.md`](lane_self_resume.md) | lane の /loop 自走・自己復帰 |
| [`lint_gate_2026_07_22.md`](lint_gate_2026_07_22.md) | lint ゼロ警告 gate (--strict) の lane 周知 |
| [`subagent_orchestration.md`](subagent_orchestration.md) | subagent 並列の運用注意 |
| [`codex_ops.md`](codex_ops.md) / [`chatgpt_consult_via_chrome.md`](chatgpt_consult_via_chrome.md) | 外部モデル運用 (codex lane / ChatGPT 相談) |

## 形式化の正本 (数学・Lean)

| file | 内容 |
|---|---|
| [`lean_formalization_tips.md`](lean_formalization_tips.md) | Lean 形式化の技法集 (ラッパー方針 §2.7 含む) |
| [`scaffold_opaque_prop_convention.md`](scaffold_opaque_prop_convention.md) | opaque-Prop scaffold の規約 |
| [`forward_dep_policy.md`](forward_dep_policy.md) | forward 依存 (章跨ぎ) の規約 |
| [`mathlib_coverage.md`](mathlib_coverage.md) | mathlib 被覆の記録 (欠落 = 本リポ実装済) |
| [`coq_odd_order_reference.md`](coq_odd_order_reference.md) | Coq odd-order 併読の対応表・grep レシピ |
| [`chapter_investigation_framework.md`](chapter_investigation_framework.md) | 章調査の汎用手順 |
| [`nougat_missing_page_recovery.md`](nougat_missing_page_recovery.md) | mmd MISSING page の復元手順 |
| [`phase2_cross_refs.md`](phase2_cross_refs.md) | 3 冊間の定理引用クロス参照表 |
| [`q8_modular_char_theory_frozen_project.md`](q8_modular_char_theory_frozen_project.md) | 【凍結】Q₈ modular character theory 長期計画 (issue 0147) |
| [`lean_eval_submission.md`](lean_eval_submission.md) | lean-eval 提出の正本 (issue 0050 tracker) |
| [`mathlib_v432_migration.md`](mathlib_v432_migration.md) / [`mathlib_rc2_migration.md`](mathlib_rc2_migration.md) | toolchain bump の手順記録 |

## スナップショット (降格済み・参照時注意)

| file | 状態 |
|---|---|
| [`three_books_full_survey_2026_07_16.md`](three_books_full_survey_2026_07_16.md) (+`.json`) | ⚠ **DEMOTED** (裁定 9154) — scope 一次情報にしない。着手前に実測必須 |

## log/ (歴史 — 更新されない)

2026-05〜07 の章 audit・handoff・旧ロードマップ・旧 frontier 計画・旧 tick ログ。
一覧は [`log/`](log/) を直接見る。代表: `merge_monitor_ticks.md` (hub 旧 tick 全量) /
`ft_master_roadmap_2026_05_29.md` / `ch0*_audit_2026_05_2*.md` / `handoff_2026_06_*.md`。
