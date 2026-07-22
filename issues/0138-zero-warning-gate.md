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
