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
- [x] wave 1: no-op/dead tactic + unused simp args + simpa/`<;>` — **247 件解消**
      (commit e14a69de、3 subagent + hub cascade 追补 4)。warnings 4761→4174。
      残置 1 件: `S07_Coherence/PsiDecomposition.lean:191` (sole-arg `simp only [if_pos rfl]`、
      個別攻略要)。Isaacs Ch06 の 11 件は a の active 領域ゆえ除外 (frontier 移動後に追补)。
- [x] wave 5a: `show`→`change` batch 1 = **812 sites / 214 files** 解消
      (commit c9feaf83、列精密スクリプト、applied 812 / skipped 0)。除外 57 sites =
      active 近傍 (Ch05/Ch06/Ch10/NearFields) → batch 2 で frontier 移動後。
      同 commit で wave-1 取りこぼし (FeitThompsonCharacterData:441 unused simp arg、
      `git add 'OddOrder/**/*.lean'` glob が top-level を漏らした) も回収。
      ⚠ **glob 教訓**: commit は `git add -A -- 'OddOrder/'` を使う (top-level ファイルを
      漏らさない) — cron prompt にも反映済。warnings 4761→3363。

## 進捗 (2026-07-17、Opus hub)

- [x] wave 3: header "Copyright too short!" 60 件 (commit 3b36723e)。3 バケット
      (PREPEND 23 / INSERT Authors 36 / LICENSE+Authors 1)。
- [x] wave 2: 未使用 section var (omit) + 未参照 binder (_prefix) + maxHeartbeats
      コメント (commit 2d40988d)。varname 189→17・hbcomment 44→0・sectionvar 152→110。
      build-break 5 ラウンド修正 (omit 型 `↑(Nat.card G)`→`(…:ℂ)` 29件・doc-comment 後
      誤配置 7件移動・VARNAME が dot-notation/named-arg で実使用の revert 数件)。
- [x] wave 4a: docstring/コメント長行の折返し 1135 行 (commit 056901e1)。backtick span
      atomic 保持で分断回避。
- [~] wave 4b **部分 landing** (2026-07-17 Fable hub tick #29): 計画 659 件/172 files の
      Workflow 12 並列が Opus セッション終了で**中断** → 55 .lean files 分 (+719/-356、
      >100 バイト行 323 解消) を build gate 後に commit。**残り ~116 files は wave 4b
      継続で** (再 census → 同スクリプト再実行)。
- [ ] wave 5: `show`→`change` batch 2 (active 近傍) + open scoped Classical 14 件。

## 残キュー (概算)

| 件数 | linter | 対応 |
|---|---|---|
| ~336 | longLine コード行 (残) | wave 4b 継続 (部分 landing 済 323/659) |
| ~830 | longLine docstring 残 (単一長 span) | 折返し不可、留保 (低価値) |
| 110 | 未使用 section var (partial) | wave 2b (複数未使用 var の残り) |
| ~57 | `show`→`change` active 近傍 | wave 5b |
| 24 | longLine markdown 表 | 対象外 (折返すと表破壊) |
| 18 | declaration uses sorry | 対象外 (frontier) |
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
