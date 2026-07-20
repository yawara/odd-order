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
- [x] wave 4b **完了** (2026-07-17 夜 Fable hub, commit 24872aae): 中断分の残り 118 files
      (+606/-303、空白のみ変更を tr -d ハッシュ比較で全数検証) を build gate 後に回収。
      Layer.lean は lane a active frontier と交差ゆえ reflow 破棄 (本方針どおり)。
      **⚠ 折り返しスクリプトの構文破壊 2 件を修正** (CaseBXi.lean:1094 /
      OrderDetermination.lean:386-389): **same-line `by` のタクティク列末尾 term を
      ぶら下げ折り返しすると、継続行が by-block のコラム基準より浅くなり block が閉じて
      壊れる** (行末が完結可能な term のときのみ発症; `exact`/`<;>` 等で行が終わる強制継続
      形は無事)。修正形 = `by` / `fun h =>` 直後で改行。今後の折り返しスクリプトは
      same-line `by` を含む行を skip 対象にする。
- [ ] wave 5: `show`→`change` batch 2 (active 近傍) + open scoped Classical 14 件。
- [x] 2026-07-19 夕 (Opus hub, commit `e5c32e00`): deprecation 5 件 (`push_neg`→`push Not` ×4、
      `Set.ncard_image_of_injOn`→`Set.InjOn.ncard_image` ×2) + 未参照 binder `_`-prefix 3 件。
      full build green で検証。同 tick で**残キューを実測し直し 650 → 192 に訂正** (下記)。

## 残キュー (2026-07-17 夜再 census、green full build unique 1245 件)

| 件数 | linter | 対応 |
|---|---|---|
| 608 | longLine 残 (docstring 単一長 span 主体 + markdown 表 24) | 折返し不可分は留保 (低価値)。コード行の残余は wave 4c で個別 |
| 334 | **unused instance in type** (255 単数 + 65 複数 + 14 outside-proofs) | **✅ 方針決定済 (hub 裁定 2026-07-17、下記 RULING)** — wave 6。「教科書 faithful な仮説削除」問題では**なかった** (誤読訂正)|
| 113 | 未使用 section var | **wave 2b (次)** — `omit … in` 挿入、42 files |
| 59 | style.show | wave 5b (goal を変える show → change、要個別確認) |
| 18 | declaration uses sorry | 対象外 (frontier) |
| 17 | Variable name 未参照 | wave 2c (`_`-prefix) |
| 14 | open scoped Classical | wave 5 (個別判断) |
| 12 | class 型 def の abbrev/instance マーク | 小物 wave (要挙動確認) |
| 9+9+6+5 | maxHeartbeats unscoped / overlapping instances / def→theorem / simpa→simp | 小物 wave (overlapping は instance 引数削除 = signature 接触、要個別) |

## 🔄 2026-07-19 夕 hub tick: 残キューを実測し直した — **650 ではなく 192**

上の「残キュー」表 (1245 件) も下の「650 サイト」も**過大**だった。green full build 後の
実測 (全レーン合流済 main、commit `e5c32e00` 時点) は **warning 総数 192 行**:

| 件数 | linter | 対応 |
|---|---|---|
| 121 | style.longLine | 残キュー最大。ソース側実測は 130 行 (差分 = scoped `set_option … in` で無効化されている分) |
| 23 | declaration uses sorry | **対象外** (本物の frontier = AppE 9 / FeitSibley 5 / Suzuki2Groups 4 / AppD 2 / NearFields 2 / CNGroupStructure 1) |
| 14 | open scoped Classical | wave 5 (個別判断) |
| 9+1 | unused instance in type | 旧表の 334 → **10**。うち 7 が `S06_CertainTypeClifford` = 下記 pitfall 1 の cascade 実績あり、要 full build |
| 8+1 | 上記の継続行 (`* 'X':`) | — |
| 4 | Variable name 未参照 | 旧表 17 → 4。うち 2 は named-arg、2 は証明本体で実使用 (下記) ⟹ **実質すべて対応困難** |
| 3 | 自動 include された section variable 未使用 | `omit … in` |
| 3+2+1 | `change` 系 / `show` tactic / try-instead | 小物 |
| 1 | mathlib フォルダ全体 import | 個別 |

**残キューが縮んだ理由**: 旧 census (2026-07-17 夜) 以降の wave に加え、レーンの通常作業
(leaf 化・実証明・リファクタ) が warning ごとコードを置き換えたため。⟹ **wave 着手前に必ず
census を取り直す** — 古い件数で計画すると存在しないサイトを探すことになる。

### ⚠ census の取り方 (罠あり)

`lake build OddOrder` は cached module の warning を replay するが、**取りこぼすことがある**。
実例: `TheoremIIPackaging.lean:496` の `push_neg` は replay に現れなかったが、実際には
deprecation warning を出しており、修正後に leaf build すると消えた (= 本物だった)。
⟹ **replay の件数は下限として扱う**。カテゴリによってはソース側で直接数える方が確実
(例: longLine = `awk 'length>100'`、ただし file/scoped の `linter.style.longLine false` を除外)。

## 2026-07-19 wave (hub, 並列 6 エージェント) — 792 → 650 サイト

commit: `chore(lint): 並列 wave で warning 142 サイト解消`。maxHeartbeats wave (9 件) と
機械的 wave (12 件) を含めるとこの日で 812 → 650。

### ⚠ 実測で判明した 3 点 (以後の wave はこれを前提にすること)

1. **instance binder 削除は cascade する**。`[DecidableEq ι]` を削ると下流の `def` が
   instance 依存を失い、**census に無かった warning が下流ファイルに新規発生**する。
   さらに `S06_CertainTypeClifford` の 822→869→926→941→966 の連鎖は、最終的に
   **一度も触っていない** `S08_CaseBCoherence2/ConstituentPinning.lean:62-113` の
   instance 合成を壊した (`failed to synthesize`)。各段が warning 数として net-zero
   (1 つ直すと 1 つ湧く) でもあったため、担当が 4 件とも手で revert し原状復帰。
   ⟹ **このカテゴリは leaf build では安全性を担保できない**。1 サイトずつ full build
   するか、下流を含めた影響範囲を先に grep で確定してから触ること。
2. **varname (`_`-prefix) は named argument で実渡しされていると壊れる**。今回の 5 件中 2 件が該当:
   `caseB_transfer (K := K)` (S03g_Thm310General:423) /
   `sixTwoMemberDatum_of_reducible_member (A' := A')` (S13_SixTwoBridge:856)。
   いずれも「型で未使用な implicit binder を named arg でしか渡せない」形ゆえ、
   呼び出し側を書き換えない限り不可 → skip が正。wave 2 の revert と同じ罠。
3. **longLine の「留保」裁定 (下表 608 件) は部分的に誤りだった**。571 件を実測分類すると
   **折返し可 493 / コード行 50 / 真に不能 28** (markdown 表 25 + 100 桁以下に分割点なし 3)。
   「docstring の分割不能な長 span が主体」ではない。今回 56 件処理、**437 件が残キュー**。
   ⚠ `by` を同一行に含む行は wave-4b の構文破壊 pitfall ゆえ引き続き skip。

### 運用上の教訓 (並列 wave の設計)

- 並列エージェントへの分割は **ファイル単位で排他**にすること。「JSON の前半/後半」で割ると、
  同一ファイルに複数エージェントが到達して衝突した (今回実際に発生、実害は自主停止で回避)。
- エージェントに **full build を禁止しても守られないことがある**。同一 worktree で並行 full build が
  走ると olean が churn し、無関係な上流モジュールで `failed to open ….olean` が続発して
  leaf build の green 判定ができなくなる。次回は build 自体を hub 側に集約する。

## RULING: "unused hypothesis in type" 334 件 = **instance binder であって数学的仮説でない** (hub 裁定 2026-07-17)

**誤読の訂正**: 上表の旧記載「修正 = 仮説削除 = signature 変更。教科書 faithful statement は
保持が正 → per-decl 判定が必要」は**誤り**。linter 実体を読んで確定した事実:

- 発生源 = `Mathlib/Tactic/Linter/UnusedInstancesInType.lean` の **2 linter のみ**:
  **`linter.unusedDecidableInType`** と **`linter.unusedFintypeInType`**。message 文字列
  (`Lean.Name.unusedInstancesMsg`) は両者専用ゆえ、334 件は**全てこの 2 つ**。
- 両 linter は `Mathlib/Init.lean:108-109` で **`linter.mathlibStandardSet` に所属** (個別の
  `defValue := false` は set 経由で on になる) ⟹ **mathlib 自身が課している標準**であり、
  本リポジトリの `weak.linter.mathlibStandardSet = true` は意図どおり。
- **発火条件が決定的**: `binderInfo.isInstImplicit` **かつ**型が `Decidable*` / `Fintype` の
  binder に**限る** (`isDecidableVariant` / `isAppOrForallOfConst \`Fintype`)。
  ⟹ 対象は **typeclass instance binder** であって、`(h : R ≠ ⊥)` のような**数学的仮説では
  一切ない**。「教科書 faithful な仮説を削るか」という論点は**そもそも発生しない**。
- 対象は `theorem`/`lemma`/Prop-class `instance` のみ (`logUnusedInstancesInTheoremsWhere`)
  ⟹ 計算可能性の懸念なし (`Fintype.ofFinite` が noncomputable でも Prop なので無害)。

**⟹ 方針 (wave 6)**: 両者とも **statement の一般化**であり、CLAUDE.md「特殊化債務はできる限り
一般化する」に**積極的に合致**する。docstring 注記や per-decl 保留で逃げない。

| linter | 修正 | 効果 |
|---|---|---|
| `unusedDecidableInType` | instance binder を**削除** + 証明に `classical` (term なら `open scoped Classical in` を**term レベル**に) | statement が真に一般化。`Decidable` 名前空間の decl は linter 自身が除外 |
| `unusedFintypeInType` | `[Fintype X]` → **`[Finite X]`** + 証明で `Fintype.ofFinite` (or 完全削除) | `Fintype` → `Finite` は genuine な一般化 |

**call-site 互換性**: どちらも**仮説を弱める**方向ゆえ既存 consumer は無変更で通る
(`Fintype X` から `Finite X` は instance 導出可能; 削除した `DecidableEq` は単に不要になる)。
⟹ 下流追従は原則不要。ただし **build で必ず検証** (wave 2 の omit 挿入と同じく、
「型で未使用」= 「証明で未使用」ではないため証明側に `classical` 補充が要る)。

⚠ **`Fintype` を statement が実際に使う場合は発火しない** (linter は型内の出現を見る) ゆえ、
`Nat.card` vs `Fintype.card` のような**意味のある** `Fintype` 依存は誤爆しない。

## 完了条件

full build の warning が `declaration uses 'sorry'` (本物の frontier) のみになる。
active frontier ファイル分はレーン合流後に追补で解消。

## 参照

- census log: hub session scratchpad `warnings_unique.txt` (2026-07-17 full build replay)
- lakefile.toml `[leanOptions]` / issues/closed/0120 (leanOptions parity)
- CLAUDE.md「ファイル粒度」(longFile 2000 上限は別トラック = 分割 issue)

## 2026-07-20 昼 (Opus hub, commit `44b9b2a93`): longLine wave — **133 → 42**

再 census (main `c58168265` の green full build replay) は **warning 総数 233** で、
2026-07-19 の 192 から**増えていた** (レーンが新コードを積む速度 > hub の解消速度)。
うち longLine 133 件を **8 並列エージェント / 59 files** で処理し **42 件**まで削減
(warning 総数 233 → 142)。

### 今回の設計 (過去の失敗を全て潰した)

- **エージェントにビルドを一切させない**。2026-07-19 wave の教訓「full build を禁止しても
  守られない / 同一 worktree の並行ビルドで olean が churn」を、**leaf build も含めて全面禁止**
  に強化。検証は hub が最後に 1 回のフルビルドで行う。実際に破られず、churn も起きなかった。
- **ファイル単位で排他分割** (前回「JSON の前半/後半」で割って同一ファイル衝突)。8 バケットに
  件数バランスで配分。衝突ゼロ。
- **git の mutating 操作を全面禁止** ([[concurrent-subagents-share-git-state]])。
- skip ルールを事前に明文化 (markdown 表 / 同一行 `by` / 分割点なし)。

### 検証手順 (今後の書式 wave の標準にする)

「空白のみの変更か」の素朴な検査は **誤検出する** — `--` 行コメントを折り返すと新しい `--`
マーカーが増えるため。正しい検査は **2 段**:

1. **実コードのトークン列**: `/- -/` と `--` を除去 → 空白除去 → HEAD と比較。
   **これが 0 件差分であることが本質的な安全条件** (今回 39/39 file で一致)。
2. docstring の `/--` `-/` 開閉数が不変であること。

⚠ 「コメント本文の比較」を `--[^\n]*` で作ると **`type II--IV` のような本文中の `--` を
コメント開始と誤認**して偽陽性を出す。本文の同一性は上記 1+2 で十分。

### 残 42 件 = 実質的な下限 (機械的には直せない)

| 型 | 例 | なぜ直せないか |
|---|---|---|
| docstring 内の markdown 表の行 | `S01_FrattiniBurnside` 16 件、`S02_RepresentationsBasic`、`Isaacs Ch03/Ch04/Ch06` | 折ると表が壊れる |
| 100 桁を超える単一識別子 | `apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient` (101 文字) が 4 箇所、`Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_frobenius` (106 文字) | 列 0 に置いても超過。識別子短縮はトークン変更 |
| 同一行に `by` を含むタクティク行 | `S05_GridTrichotomy` 2 件 (`rw [show … by linear_combination …]`) | wave 4b で 2 件の構文破壊実績 |

⟹ **longLine トラックはここで実質完了**とし、以後は「新規に増えた分を tick で拾う」運用に切り替える。

### ⚠ census の line number は編集時点でずれる

複数エージェントが「割り当て行番号が現ファイルの長行でない」と報告した (例
`OpicoreCentralizer` 割当 246/545/943 に対し実際は 51/257/472、`S08_CoherenceWeighted` は
割当 1027 がファイル末尾を超過)。原因は build log の replay が**その module を最後に
elaborate した時点**の行番号を保持するため (レーンがその後ファイルを編集していると乖離する)。
⟹ **行番号は当たりを付ける用途に留め、エージェント側で `awk 'length>100'` を取り直させる**
(今回はその指示があったので全エージェントが自力で正しい行を見つけて処理できた)。

### 次の候補 (未着手)

| 件数 | linter | 難度 |
|---|---|---|
| 14 | `open scoped Classical` 回避 | 中 (decidability 明示 or classical tactic、個別判断) |
| 4 | 未使用 simp 引数 | 低 (機械的) |
| 4+3 | `show` / `change` | 中 (goal を変える show は要確認) |
| ~7 | unused `Decidable`/`Fintype` in type | ⚠ 高 — 下流 cascade 実績あり、1 件ずつ full build |
| 4 | Overlapping instance parameters | ⚠ 高 — signature 接触 |
