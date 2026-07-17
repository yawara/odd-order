---
id: 123
slug: linter-warnings-cleanup
title: "hub: 既存 linter warnings 全面解消 (mathlibStandardSet、census 4761 件)"
created: 2026-07-17
---

# hub: 既存 linter warnings 全面解消 (mathlibStandardSet、census 4761 件)

## 背景

ユーザー指示 (2026-07-17): レーン監視と並行して既存 linter warnings を解消する。
lakefile.toml の `weak.linter.mathlibStandardSet = true` は意図的 (mathlib 互換規約) ゆえ
warnings は本物の解消対象。census は full build log (`lake build` は cached module の
warning も replay する) を `sort -u` で unique 化して取得 (2026-07-17, 4761 件)。

**進め方 (hub 実施、レーン衝突回避)**:
- active frontier ファイルは触らない — 現行: b = `Peterfalvi/Appendices/Suzuki.lean`
  (+NearFields 追従), c = `Algebra/{AugmentationIdeal,PrincipalIdealTheorem}.lean` +
  Isaacs Ch10_MoreTransfer, a = Isaacs Ch05/Ch06 近傍。これらの warning はレーンの
  frontier が移ってから、または lane 自身が解消。
- 凍結ゾーン (BG/**、Pf S01–S16、Isaacs 完了章、GroupTheory/Mathlib の安定 leaf) から
  wave 単位で解消。各 wave = 1 commit、build green 必須。
- 修正は意味保存のみ: statement を変える「修正」(未使用仮説の削除等) は不可 —
  教科書 faithful な statement の未使用仮説は `_`-prefix リネームで対応。

## カテゴリ census (2026-07-17 unique)

| 件数 | linter | 修正方針 |
|---|---|---|
| 2741 | style.longLine (>100 桁) | 手動改行 (wave 4、dir 単位)。機械列挙 file は per-file disable |
| 869 | style.show (`show` tactic) | 意味調査後に方針決定 (wave 5) — 一律 `change` 置換は不可、要検証 |
| 125 | simp argument unused | 該当引数削除 (wave 1) |
| 152 | 未使用 section variable 自動 include | `omit` 追記 or variable 整理 (wave 2) |
| 60 | style.header "Copyright too short!" | ヘッダを標準 4 行形式に (wave 3) |
| 44+9 | maxHeartbeats コメント無し/unscoped | 理由コメント追加 + `in` scope 化 (wave 3) |
| 38 | simpa→simp | 機械置換 (wave 1) |
| ~70 | Variable name not explicitly referenced | `_`-prefix リネーム (wave 2) |
| 18 | `<;>` → `;` | 機械置換 (wave 1) |
| 17 | tactic is never executed | dead branch 削除 (wave 1、意味確認付き) |
| 14 | open (scoped) Classical 回避 | 個別判断 (wave 5) — decidability 明示 or classical tactic |
| 11+7+4 | do-nothing tactic (Subsingleton.elim/push_cast/congr!) | 削除 (wave 1) |
| 7+ | module doc-string 位置 | docstring を imports 直後へ移動 (wave 3) |
| 18 | declaration uses sorry | 対象外 (本物の frontier、レーン管轄) |

## やること

- [x] wave 0: AxiomsCheck.lean 359 件 — `import Lean` → `Lean.Elab.Command`+
      `Lean.Util.CollectAxioms` narrow / docstring を最初のコマンドに / file-scoped
      `linter.style.longLine false` (機械列挙の明示例外)。leaf build green 検証済。
- [ ] wave 1: no-op/dead tactic + unused simp args + simpa/`<;>` (~230 件、意味非依存)
- [ ] wave 2: binder 衛生 (unused section vars / Variable name) (~220 件)
- [ ] wave 3: header/docstring/maxHeartbeats (~120 件)
- [ ] wave 4: longLine 2741 件 — dir 単位 (BG → Pf S* → Isaacs 完了章 → shared)
- [ ] wave 5: style.show 869 件 + open scoped Classical 14 件 (要方針調査)

## 完了条件

full build の warning が `declaration uses 'sorry'` (本物の frontier) のみになる。
active frontier ファイル分はレーン合流後に追补で解消。

## 参照

- census log: hub session scratchpad `warnings_unique.txt` (2026-07-17 full build replay)
- lakefile.toml `[leanOptions]` / issues/closed/0120 (leanOptions parity)
- CLAUDE.md「ファイル粒度」(longFile 2000 上限は別トラック = 分割 issue)
