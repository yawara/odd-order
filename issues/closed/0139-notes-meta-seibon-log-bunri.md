---
id: 139
slug: notes-meta-seibon-log-bunri
title: "notes/meta の正本/ログ分離 — 40+ ファイル混在の整理"
created: 2026-07-21
---

# notes/meta の正本/ログ分離 — 40+ ファイル混在の整理

## 背景

iut リポジトリの文書構造設計 (2026-07-21) の際に odd-order の notes/meta を全量精査した
副産物の指摘。`notes/meta/` は 40+ ファイルで、性質の異なる 3 種が同じ平面に混在している:

1. **生きた規約 (正本)**: `issue_management.md` / `worktree_setup.md` /
   `lean_formalization_tips.md` / `ft_path_policy.md` / `merge_monitor.md` /
   `scaffold_opaque_prop_convention.md` / `forward_dep_policy.md` など —
   CLAUDE.md から参照され、常に最新であるべきもの
2. **日付付き handoff / audit ログ**: `handoff_2026_06_0*.md` / `*_audit_2026_05_23.md` /
   `peterfalvi_overnight_2026-05-30.md` など — 書かれた時点の記録で、更新されない
3. **陳腐化しうる調査スナップショット**: `three_books_full_survey_2026_07_16.md` は
   CLAUDE.md 自身が「scope の一次情報にしない」と降格済み (Ch.8 の実態と食い違い等)

コスト: 正本を探すのに毎回 40+ ファイルの中から見分ける必要があり、降格済み
スナップショットを誤って一次情報として拾うリスクが実在する (降格の経緯自体が実害の記録)。
`merge_monitor.md` は正本手順と 292KB の running log が同一ファイルに同居しており、
読むだけで context を大きく食う。

## やること

- [ ] `notes/meta/README.md` (index) を新設 — 正本規約の一覧と「これが正本」の明示
- [ ] 日付付き handoff / audit / スナップショットを `notes/meta/log/` (または
      `archive/`) へ `git mv` — 参照リンクは追従修正
- [ ] `merge_monitor.md` を「手順 (正本)」と「running log」に分割
- [ ] 降格済みスナップショット (`three_books_full_survey_*`) に冒頭 1 行の
      降格注記を入れる (CLAUDE.md の裁定 9154 への参照)

## 完了条件

正本規約が index から 1 hop で引け、日付付きログと物理的に分離されている。
CLAUDE.md からのリンクが全て生きている。

## 参照

- CLAUDE.md「スコープ」節 (survey 降格の経緯、hub 裁定 9154)
- iut 側の設計判例: `/home/ywr/iut/CLAUDE.md`「文書管理」(1 ディレクトリ = 1 機能、
  正本/下書きの分離と cite 規律)

---

## ✅ 2026-07-24 close — 4 項目全て実施 (hub)

1. **`notes/meta/README.md` index 新設** — 正本 22 file を運用/形式化/スナップショットの
   3 区分で列挙、log/ の位置づけを明記。
2. **`notes/meta/log/` へ 25 file を git mv** (05-22〜07-10 の audit/handoff/旧計画/旧状態メモ)。
   inbound 参照は repo 全 .md を機械修正 (61 file、full path・相対リンク・移動先内相対の 3 形態)、
   broken link 0 を検証。`ft_lane_reallocation_2026_06_28` / `lane_reallocation_2026_07_16` /
   `phase2_cross_refs` は dated でも正本/生きた索引ゆえ残置。
3. **`merge_monitor.md` 分割**: 437KB → 93KB (手順 + 直近 5 tick)。旧 quote-tick 73 本 +
   旧世代 list 形式「現状メモ」全量を `log/merge_monitor_ticks.md` (345KB) へ退避、
   双方向 pointer 設置。以後溜まったら hub が同様に退避する運用を log 側冒頭に明記。
4. **survey 降格ヘッダ**: `three_books_full_survey_2026_07_16.md` 冒頭の「正本」自称を
   ⚠ DEMOTED (裁定 9154) + 実測必須の注記に置換。

完了条件 (index から 1 hop / 物理分離 / リンク生存) 達成。close。
