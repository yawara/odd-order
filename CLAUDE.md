# odd-order — エージェント向け指示書

> このファイルは **CLAUDE.md** が正本. `AGENTS.md` は CLAUDE.md への symlink (Claude Code / codex 共通).

このリポジトリ (`odd-order`) は **Feit-Thompson 定理 (奇数位数定理) の Lean 4 完全形式化**を AI エージェント駆動で長期的に進めるプロジェクト。詳細な計画とチェックリストは [ROADMAP.md](ROADMAP.md) を参照。

## スコープ: 3 冊を全部形式化する

1. **Isaacs**, _Finite Group Theory_ (AMS GSM 92, 2008) — 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, F\*)
2. **Bender–Glauberman**, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994) — FT 局所解析 + 最終矛盾
3. **Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000) — FT 指標理論

PDF と Nougat 抽出 Markdown (`.mmd`) は `references/` 配下 (別 private リポ、本リポでは gitignore)。教科書本文を読む必要があるときは PDF を直接読まず、まず該当の `.mmd` を grep / Read してトークン効率を上げる。

## やらないこと (重要)

- **leanblueprint は使わない** — TeX 依存グラフ方式は採用しない。教科書 (PDF/mmd) → Lean を直接書く。「blueprint を立てよう」「TeX で証明概略を…」等の提案は不可。
- **mathlib 本体への PR は当面しない** — 汎用補題 (Fitting, Hall, Frobenius 群, ZJ 等) も `OddOrder` namespace 配下に書く。理由は速度優先で手元で完結させたいから。将来の upstream は視野に入れるので、mathlib 互換のスタイル・命名は常に維持する。
- **Gorenstein 1968 _Finite Groups_ は形式化対象ではない**(2026-05-28 refinement)— 「使わない」のではなく「**全形式化はしない**」。形式化対象は上記 3 冊(Isaacs / BG / Peterfalvi)に限定し、Gorenstein は **BG の行間を埋めるためにのみ原文参照する**(`references/gorenstein/finite-groups.{pdf,mmd}`)。具体的には BG が "**G**, Thm X.Y.Z" として証明本体を省略する箇所(典型: BG App.A の A.2/A.3/A.4 が "follow the proof of **G** Thm 3.8.1 / §6.5" と書く部分)で Gorenstein 原文を読み Lean に書き起こす。**Gorenstein 本体の章節を独立に形式化することはしない**。BG 中の "**G**, Thm X.Y.Z" 引用は、まず Isaacs に対応定理があれば Isaacs に読み替え、Isaacs が欠く場合(典型: ZJ / p-stability 周り = **G** Ch.3 §8 / Ch.6 §5 / Ch.8 §2)のみ Gorenstein を参照。なお同名タイトルの Gorenstein "Classification of Finite Simple Groups I" (BAMS 1979) は教科書ではなくサーベイ論文で、別物・対象外。

## 開発規約

### ファイル粒度

- **Isaacs: 1 章 = 1 ディレクトリ**。入口は `Main.lean` (例: `OddOrder/Isaacs/Ch01_Sylow/Main.lean`)
- **BG / Peterfalvi: 1 節 (§) = 1 ファイル** (例: `OddOrder/BG/Ch1_Preliminary/S03_FrobeniusActions.lean`)
- **分割は行数でなく「編集局所性 + 再ビルドレイテンシ」で判断する**。`lake build` はファイル単位で全再 elaboration するので、コストは 1 edit-cycle のレイテンシ (≈ 5s 固定 + ~2ms/行、証明密度で変動)。トリガーは「**今まさに伸ばしている章** かつ **leaf 再ビルドが痛い** (目安 >~4000 行 or rebuild >~12-15s)」。**休眠中の巨大ファイルは行数だけでは割らない** (キャッシュされ無害、今割るのは 先回り分割)。割るときは **active frontier を小さな leaf `Main.lean` に残し、完成・凍結した subsection を上流ファイルへ押し出す** (`Ch01_Sylow/Main.lean` → 凍結部を `A_Existence.lean` 等に出し `Main` が import)。細分化 (<~800-1000 行が乱立) は固定 5s/ファイルが効いて逆効果。詳細は [ROADMAP.md#ファイル粒度とトレーサビリティ](ROADMAP.md) と memory `build-perf-bottleneck`。

### トレーサビリティ (3 層)

各 Lean ファイルは「教科書のどこの形式化か」が一目で追える状態に:

1. **ファイル冒頭 `/-! # ... -/`** で本・章・ページ範囲を明示
2. **`section /- 1A: ラベル (pp. 1-10) -/ ... end`** で教科書の subsection 構造をミラー
3. **theorem の docstring 冒頭に `**Isaacs Thm 1.4** (慣用名)`** 形式の本での名前

定理名 (Lean 識別子) には番号を入れない (`thm_1_4` 等は不可)。**mathlib 互換のため記述的命名** (`sylowExistence`, `fittingSubgroup` 等)。本での番号は docstring 内のみ。詳細は [ROADMAP.md#ファイル粒度とトレーサビリティ](ROADMAP.md) 参照。

### namespace

階層: `OddOrder.Isaacs.Ch01`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04`。汎用補題は将来 `Subgroup.fitting` のように mathlib 階層へリネーム可能な形で書く。

### ラッパー方針

mathlib に直接対応がある定理の **薄いラッパー** (`theorem foo := mathlib_bar`、引数も型も同じ純粋なリネーム) は書かない。維持負担のみで価値が無いから (mathlib API 変更時の追従、同事実が 2 名で呼ばれて証明が分裂、将来 upstream するときどうせ消す)。

同じ原則は **本リポジトリ内の既存 theorem** にも適用する。たとえば BG/Peterfalvi で使うためだけに, 既存の `OddOrder.Isaacs.*` 定理を引数・型そのままで純粋リネームする wrapper は書かない。教科書間対応 (BG/Peterfalvi ↔ Isaacs) は section docstring または `notes/` の対応表に記録し、Lean 本体では既存 theorem を直接呼ぶ。

教科書名 ↔ mathlib 名 / repo 内 theorem 名の対応は **section 冒頭の docstring** または **`notes/` の対応表** で記録する。書く価値がある例外:

- **引数順 / convention 適応** — mathlib が `Disjoint M N` を明示引数で取るところを instance + positional で並べ替える等
- **仮定特殊化** — `[Finite G]` などで mathlib の汎用版を狭く取り直す
- **章内で 2 回以上呼ぶ慣用名** — Isaacs Thm 1.7 を `sylowExistence` として呼びたい等

詳細は [`notes/meta/lean_formalization_tips.md`](notes/meta/lean_formalization_tips.md) §2.7 参照。

### commit の区切り

作業の論理的な単位ごとに git commit を作る. 1 セッション分を最後にまとめて 1 コミットで上げるのは避ける.

- 定理 1 つを `sorry` 無しで証明できたら → すぐコミット (次の定理に進む前に)
- ノート整備 / 対応表更新が独立な意味を持つなら → 単独コミット
- 同質なリファクタ (例: ラッパー削除 N 件) は **同質単位ならまとめてよい**, 異質な作業 (リファクタ + ノート + 新定理) は分ける
- どうしてもまとめる場合, commit message で各単位を明示

理由: 履歴を細かく追え, 並列エージェントの cherry-pick / revert / rebase 単位が揃い, 失敗時の巻き戻しが楽.

## ノート・小ロードマップの管理

章節単位のミニロードマップ・調査結果・設計決定は `notes/` 配下:

```
notes/
├── isaacs/ch01_sylow.md       # 章単位
├── bg/s08_fitting.md          # 節単位
├── peterfalvi/s04_dade.md
└── meta/                       # 章節に紐づかない横断調査・設計決定
```

ROADMAP のチェックリストから対応する `notes/` にリンクして掘り下げる。

## Issue 管理

単発の作業項目 (1 つの sorry を埋める, 1 つの設計を決める, etc.) は `issues/` 配下のファイルベース issue で追跡する。GitHub Issues は使わない (local-first)。詳細は [`notes/meta/issue_management.md`](notes/meta/issue_management.md)。

- 採番 + scaffold: `bin/new-issue [--base N] <slug> "<title>"` → `issues/NNNN-<slug>.md` を作って `git add`。並行セッションは `--base`/`ODD_ISSUE_BASE` で採番レンジを分けて衝突回避 (main=0, **Peterfalvi=1000 固定**, その他=2000…; 既定 0)
- 状態 = 配置ディレクトリが source of truth: `issues/` (open) / `issues/pending/` / `issues/closed/`
- 遷移は `git mv`. frontmatter に `status:` は持たない

## 並行作業 (worktree)

章 / 節を別エージェントセッションで並行進行させるときは `git worktree` を使う。詳細手順は [`notes/meta/worktree_setup.md`](notes/meta/worktree_setup.md)。

- worktree path = `/Users/ywr/odd-order-<slug>` (sibling), branch 名も `<slug>` (例: `isaacs-ch05`, `bg-s03`)
- `.lake/packages` と `references` は main から **symlink で共有** (mathlib 6.5GB + 初回ビルド数分を節約)
- `.lake/build/` は worktree ごとに独立 (並行 `lake build` 安全)
- **`lake update` は worktree で走らせない** (共有 mathlib rev を壊す)
- forward axiom 経由で章をまたぐ並行作業は合流時の名前衝突に注意 ([`notes/meta/forward_dep_policy.md`](notes/meta/forward_dep_policy.md))
- 並行 worktree には **issue 採番レンジ**を割り当てる (`export ODD_ISSUE_BASE=N`、base は 1000 の倍数; main=0, **Peterfalvi=1000 固定**, その他の並行=2000…)。採番衝突を予防 ([`notes/meta/issue_management.md`](notes/meta/issue_management.md) 「並行セッションの採番レンジ」)

## 主要パス

| パス | 内容 |
|---|---|
| [ROADMAP.md](ROADMAP.md) | 長期計画、フェーズ、依存グラフ、章節チェックリスト |
| `OddOrder/` | Lean ソース本体 |
| `notes/` | ミニロードマップ・調査メモ |
| `issues/` | ファイルベース issue (open は直下, `pending/` `closed/` で状態管理) |
| `bin/` | 雑用スクリプト (`new-issue` 等) |
| `references/` (gitignored) | PDF + Nougat 抽出 Markdown — 別 private リポ `odd-order-references` |
| `references/{isaacs,bg}/*.{pdf,mmd}` | 教科書原典と抽出物 (フラット) |
| `references/peterfalvi/pdf/*.pdf`, `references/peterfalvi/*.mmd` | Peterfalvi だけ章別 PDF を `pdf/` に集約 |
| `references/README.md` | Nougat セットアップ・抽出手順 (GPU マシン用) |

## ツールチェイン

- Lean: [`lean-toolchain`](lean-toolchain) (現状 `leanprover/lean4:v4.30.0-rc2`、2026-05-27 に v4.29.1 から bump; 手順 [`notes/meta/mathlib_rc2_migration.md`](notes/meta/mathlib_rc2_migration.md))
- mathlib: [`lakefile.toml`](lakefile.toml) の `[[require]]` 参照
- ビルド: `lake build OddOrder`
- mathlib キャッシュ: `lake exe cache get` (mathlib 更新時に再取得)

## mathlib カバレッジ

詳細は [`notes/meta/mathlib_coverage.md`](notes/meta/mathlib_coverage.md) に集約。概要: Sylow / `IsPGroup` / `IsSolvable` / `IsNilpotent` / Frattini / Transfer / Schur-Zassenhaus / 表現論・指標の基本は既存。Fitting `F(G)` / `F*(G)` / 一般 π-Hall / Frobenius 群 / ZJ / Thompson subgroup `J(P)` / Dade isometry / Peterfalvi coherence は新規実装が必要。

## mathlib API 探索方針 (3 層運用)

mathlib lemma の名前 / 署名を調べるときは, 闇雲に `grep -rn` を叩かず以下の順:

1. **概念は明確で名前が未知** → **Web 検索** (`WebFetch https://leansearch.net/?q=<query>` / `WebSearch "mathlib4 <concept>"`). leansearch.net / moogle.ai が mathlib 専用のセマンティック検索. 候補名は必ず local で確認 (v4.29.1 pin との drift 注意)
2. **不慣れなモジュールの API 把握** → **該当ファイルを `Read` で通読**. 個別 grep を 3 回以上叩くなら通読の方が早い (例: `SemidirectProduct.lean`, `Nilpotent.lean`)
3. **名前細部 (namespace, 引数順) が不確か** → **自然名で書いて `lake build` のエラー任せ**. ~12 秒で決着

`grep -rn` は「使用例を本プロジェクト内で探す」 (Ch.1 等で類似 proof パターンの確認) には引き続き有用. mathlib 名前探索とは目的を分けて運用.

詳細は memory `feedback_mathlib_api_3layer_lookup.md`.
