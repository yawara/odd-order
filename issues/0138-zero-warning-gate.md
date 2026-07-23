---
id: 138
slug: zero-warning-gate
title: "ゼロ警告 gate (check-warnings) の導入と現存 172 lint 警告の解消"
created: 2026-07-21
---

# ゼロ警告 gate (check-warnings) の導入と現存 172 lint 警告の解消

## 背景

lint 警告は build を止めないため溜まり続け、後からの一括訂正が高くつく
(本リポでは issue 0123 = linter-warnings-cleanup が既存。moore57 では 5031 件まで
膨らんだ — moore57 issue 0056)。ユーザー方針 (2026-07-21、iut 立ち上げ時):
**警告はその commit で直す**を機械で強制する。

iut (`/home/ywr/iut/bin/check-warnings`) に実装済みの gate:
`lake build` 出力の `warning:` 行のうち **sorry 警告以外が 1 件でもあれば exit 1**
(sorry は正常系ゆえ許容; Lake の log replay により増分 build でも既存警告を検出)。

**現存警告の実測 (2026-07-21、main の no-op build)**: 総数 174 = sorry 2 +
**lint 172**。内訳の大どころ:

- `linter.flexible` 約 70 件 — ほぼ全て `OddOrder/BG/AppE_FiliformGroup.lean`
  (240/326/419/452 行の `simp ... at h1 h2 ...`)
- `open scoped Classical` 警告 9+ 件 (Peterfalvi S04/S08/S09 ほか)
- 未使用変数名・未使用仮定・`Mathlib.Tactic` 丸 import・maxHeartbeats コメント無し・
  longLine 1 件 など少数多種

## やること

- [ ] iut の `bin/check-warnings` を移植 (`OddOrder` 読み替えのみ; sorry 許容フィルタは
      issue 0137 の引用符非依存パターンで)
- [ ] 現存 172 件を解消 (AppE_FiliformGroup の flexible 集中は `simp?` 置換 or
      理由コメント付き per-decl `set_option linter.flexible false in` の裁定)
- [ ] CI (`lean_action_ci.yml`) に gate step を追加
- [ ] issue 0123 との統合 — 0123 のスコープを本 issue が包含するなら 0123 を close

## 完了条件

`bin/check-warnings` が exit 0、CI green、以後の警告は commit 時点で止まる。

## 参照

- iut 実装: `/home/ywr/iut/bin/check-warnings` + CLAUDE.md「ビルド・検証規律」
- 実測ログの取り方: main で `lake build 2>&1 | grep -E "warning: "` (replay で全件出る)
- 関連: issue 0123, 0137 / moore57 issue 0056

---

## 📐 実装 + 一掃 master plan (2026-07-22, Opus hub)

ユーザー指示「gate 整備 + backlog 一掃を計画立てて」に基づく。iut は day-1 ゼロ gate
だが odd-order は既に **230 件の backlog** を持つ (下記) ので、iut 式の純ゼロ gate は
初手で CI を赤にする。そこで **ratchet 方式**を採る: backlog を baseline として grandfather
し、**baseline を超える新規/増加のみ gate**。cleanup wave が baseline を下げ、空になったら
`--strict` の純ゼロ gate へ移行する。

### Phase 0 — gate 基盤 (本 commit、完了)

- **`bin/check-warnings`** (Python、`bin/count-sorry` と同スタイル):
  - `bin/check-warnings` … ratchet gate (baseline 超過で exit 1)
  - `--report` … 現況をカテゴリ×ファイルで表示 / `--diff` … baseline との差分
  - `--update-baseline` … cleanup 後に現況を baseline へ / `--strict` … 純ゼロ gate
  - 分類は警告ブロック末尾の `note: … set_option linter.X false` から **linter 名を直接
    抽出**するので **行番号非依存** (レーンの編集で行がずれても signature が安定)。
    deprecation 等 note 無しはメッセージ本文で分類。sorry は常に無視。
- **`bin/lint-baseline.tsv`** … `count<TAB>relpath<TAB>category` を 84 組ぶん記録。
- ⚠ **baseline は fresh full build で取り直すのが authoritative**。本 commit の baseline は
  main の増分 replay 由来ゆえ、CI の初回 fresh run で数件ずれる可能性がある (replay 取りこぼし、
  issue 0123)。CI enforcement 開始後の初回 fresh baseline で確定させる。

### 現況 census (2026-07-22 main、非 sorry 230 件 / 84 組)

| 件数 | linter | 主な所在 | 担当・手法 | track |
|---|---|---|---|---|
| 74 | `flexible` | AppE_FiliformGroup 67 / Counterexample 6 | `simp`→`simp only` は過去 revert 実績 ⟹ `simp?` 出力採用 or 理由付き per-decl disable。**要 full build + 敵対的検証** | lane c (AppE) 通過後 / hub |
| 59 | `style.show` | AppE_*, NearFields, Suzuki, Higman | `show`→`change` (goal を変える show は個別確認、一律不可) | owner lane / hub (frozen) |
| 17 | `style.longLine` | AppE_*, NearFields, FeitSibley, Opicore | 折返し (markdown 表・長識別子は skip) | owner / hub |
| 17 | `deprecation` | Higman/Suzuki 中心 | push_neg→`push Not` / push_cast 削除 / ncard rename (機械的・安全) | **hub 即** |
| 14 | `unusedSimpArgs` | ModelCenters 6 ほか | 該当引数削除 (機械的) | **hub 即** |
| 11 | `style.openClassical` | Pf S04/S08/S09, Repr | statement 依存 (decidability 明示は API 変更) | **issue 0133** |
| 9 | `unusedSectionVars` | CaseSplitBCD ほか | `omit … in` (型注意、0123 wave 2 の罠) | hub |
| 9 | `unusedVariables` | 各所 | `_`-prefix (named-arg 罠は恒久 skip) | hub |
| 6 | `unusedFintypeInType` | | `Fintype`→`Finite` = genuine 一般化 | hub (0123 RULING) |
| 5 | `style.header` | | 標準 4 行ヘッダ | **hub 即** |
| 3 | `unusedTactic` | | dead branch 削除 (意味確認) | hub |
| 2+2+1+1 | maxHeartbeats / seqFocus / missingEnd / simpa | | 個別・機械的 | hub |
| — | `import.mathlibTactic` (S05) | | 下流 import 補完とセット、**要 full build** | **issue 0136** |
| — | 長すぎる宣言名 longLine (S08) | | 構造体名 rename | **issue 0132** |

大半が **active-lane 領域** (AppE_*=c 近傍 / Higman・Suzuki=b / S11_*=a、直近 24-36h touch)。
hub が今触れるのは **frozen zone の機械カテゴリのみ** (deprecation / unusedSimpArgs / header /
maxHeartbeats / seqFocus 等で active file を除いた分)。

### Phase 1 — CI enforcement + lane 周知 (⚠ owner 確認待ち)

- **`lean_action_ci.yml` に ratchet step 追加**:
  ```yaml
        - name: Lint warning ratchet (bin/check-warnings)
          run: bin/check-warnings   # backlog は baseline で grandfather、新規警告のみ赤
  ```
  backlog は grandfather ゆえ現 CI は緑のまま。**新規 lint 警告を導入した push/PR のみ赤**。
- **各レーンへの周知** (notes + 本 issue、cross-lane-sync-via-notes):
  1. 自 commit で **新規 lint 警告を増やさない**。増えたら直すか、意図的なら
     `bin/check-warnings --update-baseline` で justify 更新。
  2. 自領域の **frontier が通過したら残 baseline を消す** (owner が一番安全に直せる)。
  3. commit 前ローカル確認は `bin/check-warnings` (増分 replay の近似で速い)。

### Phase 2 — backlog 一掃 (multi-tick、hub + lane 分担)

安全規律 (issue 0123 の教訓を全継承):
- hub は **active-lane ファイルを触らない**。owner lane が frontier 通過時に解消。
- **flexible / import / instance 系は full build 必須** (leaf build で検出不能な cascade =
  0123 で main を 2 回壊した実績)。
- 書式 wave は **fix + 敵対的検証の 2 段** (0123 で 3 件の誤「FIXED」を検出)。
- 各 wave 後に `--update-baseline` で baseline を下げ、1 commit = 1 wave。
- サブエージェントに **full build も leaf build もさせない**。検証は hub が最後に 1 回。

hub の即着手候補 (frozen zone × 機械カテゴリ、~40 件が理論上の上限だが active 除外後は要再測):
deprecation 17 → push_neg/push_cast/ncard の frozen 分、unusedSimpArgs の frozen 分、header 5、
maxHeartbeats 2、seqFocus 2。⚠ 着手前に各サイトの owner-active 判定 (直近 commit + lane 先行) を取る。

### Phase 3 — ゼロ gate 化 (baseline≈0)

- baseline が空 (sorry のみ) になったら CI step を `bin/check-warnings --strict` に切替。
- CLAUDE.md「開発規約」に **「commit 前に `bin/check-warnings`」** を明記。
- issue **0123 を本 issue に統合して close** (0123 のスコープを本 issue が包含)。

### 完了条件 (改訂)

`bin/check-warnings --strict` が exit 0 (非 sorry 警告ゼロ)、CI に gate step、
CLAUDE.md 明記、0123 close。

---

## ✅ 2026-07-22 実施 (Opus hub) — Phase 0-1 landing + frozen wave 12 件

- **Phase 0 (commit `2b9ce8bba`)**: `bin/check-warnings` + `bin/lint-baseline.tsv` (230 件)。
- **frozen wave (commit `d7f772527`)**: provably-cold (lane c→BrauerSuzuki / lane b→Suzuki-
  FirstCase、両者非 dirty を worktree status で確認) の非カスケード機械 12 件を解消
  (deprecation 10 = push_neg/coeFn_sum/ncard rename + unusedSimpArgs 2)。230→**218**。
  増分 green (下流込み)。baseline を 218 に更新。
- **Phase 1 (本 commit)**: `lean_action_ci.yml` に ratchet step 追加 (backlog は
  grandfather、新規のみ赤)。lane 周知 = `notes/meta/lint_gate_2026_07_22.md`。
- **baseline の authoritativeness**: 218 は増分 replay 由来。ratchet は自己補正 (baseline が
  低すぎれば既存警告が「regression」で出るので +bump するだけ) ゆえ CI 初回 fresh run で
  ずれても軽微。

### 残 218 の所有 (frontier 通過時に owner が解消; hub は active-lane を触らない)

- lane c: `AppE_FiliformGroup` flexible 67 (⚠ simp only 化は要 full build + 敵対検証) ほか
- lane b: Higman/Suzuki2Groups・Pf Appendices Suzuki の show/simpArgs/sectionVar/残 deprecation
- lane a: S11_* maxHeartbeats / FeitSibley 系 simpArgs・show
- 別トラック: openClassical (0133) / Mathlib.Tactic import (0136) / 長宣言名 (0132)

---

## ✅ 2026-07-23 実施 (d = hub 代行) — frozen 機械 wave 19件 (218→199)

commit `975a387e1` (10 files, +15/-29)。real hub 稼働中 (a/b/c を合流・tick で「d lint」明記) ゆえ
**main へ直接 push せず d に commit → hub が forward merge** する分担。full build (5m54s) + `--diff`
で regression ゼロ、AxiomsCheck OK (`OddOrder.lean:484` が import)、sorry 8 非退行を確認。

**解消 19件 (frozen × 純機械のみ; active-lane は全除外)**:
- deprecation 3: ModelCenters `push_neg at hall` → `push Not at hall`
- unusedSimpArgs 9: ModelCenters 6 (zero_add/zero_mul) / MixedEigenweights `Fin.val_mk` /
  XiLengthFromCard・QuotientPlaneModel `AddSubgroup.mem_toZModSubmodule`
- unusedTactic 3: CaseDispatch no-op `push_cast` ×2 (a:=r/s 単項時のみ) / AppE_AbelianCentralizer no-op `change`
- unnecessarySeqFocus 2: AppE_FiliformCounterexample・AppE_FiliformGroup 2 段目 `<;>` → `;`
- style.maxHeartbeats 2: MixedEigenweights・S11_NineElevenCaseAResidual に理由コメント

**このwaveで踏んだ罠 (次 wave 用)**:
- ⚠ **`style.maxHeartbeats` のコメントは `set_option … in` の *直後* (次 cmd の前) に置く**。
  linter (`DeprecatedSyntaxLinter.getSetOptionMaxHeartbeatsComment`) は `in` と cmd の間の trivia
  を見る。前に置くと不成立で 1 往復した。例: `set_option maxHeartbeats n in` → `-- 理由` → `theorem …`。
- ⚠ **同一 simp 行トラップ**: ModelCenters 189-190(eq1) と 196-197(eq2) は byte 一致だが 190 のみ
  unused。`replace_all` 厳禁、`have h := hadd (γ,0)` 等 context で個別特定 (Python の count==1 assert で担保)。
- ⚠ **baseline に stale あり**: S05_GridTrichotomy は baseline で `style.header` だが実体は
  `import.mathlibTactic` (0136 track)。着手判断は census 実測で。

### 残 199 の大どころ (hub は active-lane を触らない; owner が frontier 通過時に解消)
- **flexible 74** (AppE_FiliformGroup 67 / Counterexample 6) — 要 `simp?` + full build + 敵対検証。lane c or hub 専用 wave。
- **style.show 59** — goal 変更 show の個別確認要。owner lane 通過時。
- longLine 17 / unusedVariables・unusedSectionVars 17 / openClassical 11 (0133) ほか。
- FieldAction `simpa`→`simp` 1 は owner 判断で defer。

---

## 🧭 2026-07-23 — per-lane 分割 issue 化 + d の第2 frozen wave

ユーザー指示「各レーン向けの指示も issue に / こちらでできることはやる」に基づき、
残 backlog を **territory 所有レーン別に issue 化** (fresh full build 実測 206 件 = 増分 baseline 199 +7、
replay 取りこぼし分。所有は `--first-parent main` の Merge 'x' で確定):

- **[0144](0144-lint-lane-a-owned.md)** — lane a (Pf FeitSibley / S11 / S13)。a は Isaacs Problems へ
  移動済ゆえ Pf 側は**凍結** → d が機械分を先行解消 (下記)。残 = Fintype 判断 + show 4 + longLine 1。
- **[0145](0145-lint-lane-b-owned.md)** — lane b (Higman/Suzuki2Groups / Pf Suzuki App / PrimeTIResidue)、45 件。
  b の active zone ゆえ owner 解消 (show 31 が最多)。
- **[0146](0146-lint-lane-c-owned.md)** — lane c (BG AppE / NearFields / BrauerSuzuki / BG Ch4)、123 件。
  **flexible 73** が最重量 (full build + 敵対検証)。c の active zone。

### d の第2 frozen wave (本 tick、9 件 / baseline 199→190、full build EXIT=0 検証)

lane a の **凍結** Pf 領域 (a は Isaacs へ移動、worktree status で uncommitted 無しを確認) +
frozen BG Ch1 の **純機械カテゴリのみ**を先行解消 (active-lane の b/c は一切触らず):
- deprecation 1: `FeitSibley` `push_neg`→`push Not`
- unusedSimpArgs 3: `FeitSibley` α-equiv の `Subgroup.coe_mk` (452/453 は `group` 単独化、455 は coe_mk 削除)
- unusedVariables 5: `FeitSibley` `_h1A`/`_hdegMem`/`_hχdeg` (named-arg caller 無しを確認) /
  `S11_NineElevenSubcoherentBridge` `_htau` (7 出現中 L944 のみ、3 行 block で特定) /
  `S03g_Thm310General` `caseB_transfer` の dead implicit `K` 削除 (caller L427 の `(K := K)` も協調除去)

**踏んだ罠**:
- ⚠ `S13_SixTwoBridge` `A'` (`{A' B : Subgroup ↥M}` の dead implicit) は **同 file L853 が
  `(A' := ...)` で named 呼び出し**していた (grep で取りこぼし) → `_A'` rename が caller を壊し
  full build が S13 で error。**revert して owner (0144) へ委譲**。S03g `K` と同型だが K は caller が
  1 箇所で協調除去できた一方、A' は 1 警告のため risk を取らず defer。
- ⚠ full build の **incremental replay は取りこぼす**: postbuild は S13 error で中断、FeitSibley は
  独立 DAG ゆえ未到達 = 未検証だった。revert 後の全 pending rebuild (EXIT=0) で FeitSibley が
  `⚠ Built` (残 unusedFintypeInType 3 のみ) を確認して初めて green 確定。

⚠ **`unusedFintypeInType` (FeitSibley 75/1017/1033・S11_RFamily 780) は d が触らず owner (0144) へ** —
どの instance が flagged か / body が Fintype を要求するかは proof 文脈判断が最も安全 (誤ると body 破壊)。
