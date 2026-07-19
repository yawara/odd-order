# Issue 管理

**確定**: 2026-05-24

## 背景

ROADMAP.md は長期計画 (フェーズ・章節チェックリスト) を持ち, `notes/` は章節
単位のミニロードマップ・調査メモを持つ. 一方で「単発の作業項目」 (1 つの sorry を
埋める, ある定理の証明をやり直す, 1 つの設計を決める, ...) を **追跡可能な単位**
として持つ場所がこれまで無かった. GitHub Issues は採用しない (local-first 方針)
ので, リポジトリ内に最小限のファイルベース issue システムを置く.

## いつ issue にするか (vs `notes/`)

軸を 1 つに絞るなら **「終わるか / 終わらないか」**:

| | `issues/` | `notes/` |
|---|---|---|
| ライフサイクル | open → closed で **終わる** | 成長する辞書 / **終わらない** |
| 内容 | やること (1 単位) | 知見・構造・設計判断 |
| Done | 完了条件が書ける | 完了の概念が無い |
| 例 | "Lem 1.7(b) sorry を埋める" / "依存を整理する" / "設計 Y を決める" | "Ch.1 の構造調査" / "mathlib API の罠集" / "BG → Isaacs 対応表" |

**判断のチェックリスト** (上から順):

1. **完了条件が書けるか?** → issue 候補
2. **タスクが終わっても後で参照したいか?** → note 候補
3. **両方 yes** → 両方持つ (issue を close する時に note へのリンクを残す)

**境界ケースの運用**:

- **調査タスク**: 着手の宣言は issue, 成果物は `notes/{book}/chXX_audit.md` 等. 調査が終わったら issue を close (中身に note へのリンク). issue は「やったか」, note は「何が分かったか」.
- **設計判断**: 議論と決定は issue (背景 / 選択肢 / 決定理由を書く), 確定後の参照ポイントは `notes/meta/<topic>.md`. 後から読むのは note の方.
- **章全体の進行**: ROADMAP のチェックリスト → 個別 sorry / refactor は issue → 章の構造理解は note. 3 層使い分け.

**ありがちな迷い**:

- "これ note に書こうかな" と思ったが, 後で何かアクションを期待している → 実は issue.
- "これ issue に書こうかな" と思ったが, close する条件が思いつかない → 実は note.
- どちらか分からない時は **issue で起こして close 時に判断** で良い. note 化すべき内容なら note へ移して issue close, 単発作業ならそのまま close.

## ディレクトリ構造

```
issues/
├── SEQUENCE             # 整数 1 行. main レンジ (base 0) の採番カウンタ.
├── SEQUENCE.1000        # 並行レンジの採番カウンタ (base 1000, 2000, ... 使用時のみ)
├── 0001-<slug>.md       # open: top-level に置く
├── 0002-<slug>.md
├── pending/
│   ├── .gitkeep
│   └── 0003-<slug>.md   # pending: 一時停止中 / ブロック中
└── closed/
    ├── .gitkeep
    └── 0004-<slug>.md   # closed: 完了 / 取り下げ
```

## 採番

- **SEQUENCE ファイル**に整数を持ち, 新規発行ごとに +1.
- `bin/new-issue [--base N] <slug> "<title>"` がロックを取って採番 → scaffold 作成 → `git add`
  までを 1 ステップで行う.
- ⚠ **採番は SEQUENCE 単独ではない** (2026-07-18 hub 裁定 9150 以降):
  `max(SEQUENCE, 当該 range に実在する issue ファイルの最大番号) + 1` を採る。
  `issues/` + `issues/pending/` + `issues/closed/` を走査するので、SEQUENCE が巻き戻っても
  既存ファイルと衝突しない.
- ロックは **`mkdir` 原子操作**で実装. macOS は `flock(1)` を持たないので
  POSIX 標準で済む方式を選んだ. 5 秒 (50 × 100ms) 取れなければエラー終了.

### 並行セッションの採番レンジ (確定 2026-05-29)

並行する複数セッション (worktree / 別ブランチ) が 1 個のグローバルカウンタを
共有すると同じ番号を取って衝突する (2026-05-29 に main の BG 系と `peterfalvi-s09`
ブランチが 0041-0043 で衝突, 手動リナンバで解決した). これを **採番レンジの分割**で
予防する:

| base | レンジ | 用途 (確定割当) | SEQUENCE ファイル |
|---|---|---|---|
| 0 | 0000-0999 | main / trunk セッション | `issues/SEQUENCE` |
| **1000** | **1000-1999** | **lane a** (Isaacs 本文 + Pf 本文) | `issues/SEQUENCE.1000` |
| **2000** | **2000-2999** | **lane b** (Suzuki チェーン) | `issues/SEQUENCE.2000` |
| **3000** | **3000-3999** | **lane c** (BG 残 + Pf Appendices 非 Suzuki 系) | `issues/SEQUENCE.3000` |
| 4000+ | (1000 ごと) | 追加の ad-hoc 並行セッション | `issues/SEQUENCE.N` |
| ~~9000~~ | 9000-9199 | shared-infra claim の**歴史的レンジ** (共有カウンタ、2026-07-19 に凍結) | `issues/SEQUENCE.9000` |
| **9200** | **9200-9299** | **shared-infra claim — lane a** | `issues/SEQUENCE.9200` |
| **9300** | **9300-9399** | **shared-infra claim — lane b** | `issues/SEQUENCE.9300` |
| **9400** | **9400-9499** | **shared-infra claim — lane c** | `issues/SEQUENCE.9400` |
| **9500** | **9500-9599** | **shared-infra claim — hub/main** | `issues/SEQUENCE.9500` |
| 9600+ | (100 ごと) | 将来レーン / サブバンド枯渇時の再割当 | `issues/SEQUENCE.N` |

**Peterfalvi の並行作業は base 1000 に固定**(`ODD_ISSUE_BASE=1000`)。これは予約済みなので
他の並行セッションには使わない。Peterfalvi 以外の ad-hoc な並行作業は 2000 以降を割り当てる。

- base は **`--base N` 引数** または **環境変数 `ODD_ISSUE_BASE`** で渡す (既定 0).
  base は **100 の倍数のみ** (レンジ重複防止のため `new-issue` が検証).
  **1000 の倍数ならレンジ幅 1000** (レーン本体)、**それ以外は幅 100** (9000 番台の
  shared-infra claim サブバンド).
- **レンジごとに別 SEQUENCE ファイル** (`SEQUENCE.N`) を使うので, 採番もマージも
  衝突しない (異なるファイル = git は両方そのまま残す). `SEQUENCE.N` は初回
  `new-issue --base N` 時に遅延作成 (初期値 N-1, 最初の issue = N).
- **Peterfalvi の並行作業は base 1000 に固定** (`export ODD_ISSUE_BASE=1000` または
  `--base 1000`)。それ以外の **並行 worktree を切るとき**は 2000 以降の未使用 base を
  1 つ割り当てる (手順は [`worktree_setup.md`](worktree_setup.md)).
- 既存の 0001-0046 は全て main レンジ (base 0). **移行不要**.
- レンジ幅 1000 を使い切ると `new-issue` がエラーで知らせる = **採番レンジを
  再分割 / 幅を見直すタイミング** (issue が増えてきたら再考).

### shared-infra claim (9000 番台, 確定 2026-07-01 / レーン別サブバンド化 2026-07-19)

> **🔢 2026-07-19 hub 裁定 (issue 0130): 9000 は共有カウンタをやめ、レーン別サブバンドにする。**
> `SEQUENCE.9000` は「1 レンジ = 1 書き手」の前提を唯一破っており、2026-07-18 の
> 「max(SEQUENCE, 実在ファイル最大) + 1」補強でも**未マージのレーン同士の同時採番は防げない**
> (実害: 同日 2 度 — 9163 = b が 23 commits 遅れの stale checkout で二重採番 / 9164 = a と b が
> main 取り込み直後にそれぞれ次番号を引いて衝突)。
> ⟹ **claim も自レーン専用バンドから採る**: **9200=a / 9300=b / 9400=c / 9500=hub**
> (`--base 9200` 等、幅 100)。SEQUENCE ファイルが別なので**構造的に衝突しない**。
> 9000-9199 は既存 claim の歴史的レンジ (改番しない)。**「9xxx = shared claim」の grep 規約は不変**
> (`ls issues/9*.md` で全レーンの open claim を走査できる)。

**未所有 leaf**（`OddOrder/Algebra|GroupTheory/**` 等、どのレーンも所有しない共有 infra）を
新設して genuine FT math を積むとき（`ft_path_policy.md` §0 policy 5(A)(B) の「gated → 上流 ungated
infra に降りる」で発生）、**複数レーンが同じ上流 infra を同時並行で構築する重複を防ぐ**ための
着手宣言プロトコル。所有 file 内の作業には不要。

1. **検索**（着手前・必須）: repo を「教科書番号 + descriptive 名 2 案以上 + import grep」で検索し、
   既存を確認（[[verify-port-state-by-number-not-coq-name]] [[s09-is-section7-chirho-complete]]）。
   既に在れば cite（再構築しない）。
2. **claim**: 不在確認後、`bin/new-issue --base <自レーンの claim バンド> <slug> "claim: <leaf> —
   <補題名/教科書 ref> (lane X)"` で 9xxx issue を 1 件切り、**着手の最初のコミットで main に乗せる**
   （バンド = a:9200 / b:9300 / c:9400 / hub:9500。`export ODD_ISSUE_BASE=9300` 等）。
   本文に target leaf・提供する補題（署名）・consumer・lane を書く。
3. **scan**（着手前・必須）: 全レーンは shared infra 着手前に `issues/` の **open 9000 番台**を読む
   （定期 main 同期にフック）。同一 ref の claim が在れば重複回避（cite する / その lane に委ねる）。
4. **完了/放棄で `git mv` closed**。hub (merge_monitor) は重複 claim / 台帳に無い新 shared-infra leaf を
   検出して STOP flag（[`merge_monitor.md`](merge_monitor.md)）。
5. **grandfather**: プロトコル制定 (2026-07-01) 前に landing 済の shared leaf
   （`OddOrder/Algebra/GaloisRationalInteger.lean` = [Is] 3.14 等）は事後 claim 不要
   （既に main 上で全レーン可視ゆえ重複リスク解消済）。
- 万一 **同一レンジ内**で衝突した場合 (同 base の 2 セッション等) のみ, 従来どおり
  マージ時に手動リナンバ + 該当 SEQUENCE 解決 (Django migrations と同じ割り切り).

## ファイル名

```
issues/NNNN-<slug>.md
```

- **NNNN**: 4 桁ゼロパディング (9999 まで). `ls` で自然順ソート.
- **slug**: 小文字英数字 + ハイフン. 正規表現 `^[a-z0-9]+(-[a-z0-9]+)*$`. **必須**.
  - 日本語タイトルを slug 化するのは罠 (ローマ字化, 特殊文字, 切り捨て...)
    が多すぎるので, slug は明示的に書いてもらう. 自由形式 title は frontmatter
    と H1 で表現する.
- 例: `issues/0042-bg-s1-lem-1-7b-sorry.md`

## Frontmatter / scaffold

`bin/new-issue` が作る scaffold:

```markdown
---
id: 42
slug: bg-s1-lem-1-7b-sorry
title: "BG §1 Lem 1.7(b) sorry を埋める"
created: 2026-05-24
---

# BG §1 Lem 1.7(b) sorry を埋める

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->
```

- **`status:` フィールドは持たない**. 状態は配置ディレクトリが source of truth
  (後述).
- title は YAML ダブルクォート文字列としてエスケープ (`"` と `\` のみ). 日本語は
  そのまま入る.
- `created` は発行日 (YYYY-MM-DD).

## 状態 (open / pending / closed)

**配置ディレクトリが source of truth**. frontmatter には `status` を持たない
(二重管理による drift を避ける).

| 状態 | 配置 | 意味 |
|---|---|---|
| open | `issues/NNNN-<slug>.md` | 着手可 / 着手中 |
| pending | `issues/pending/NNNN-<slug>.md` | 一時停止 (外部待ち, 別 issue 待ち, 検討凍結 等) |
| closed | `issues/closed/NNNN-<slug>.md` | 完了 / 取り下げ / 重複 |

### 遷移は `git mv`

```bash
# open → closed (完了)
git mv issues/0042-bg-s1-lem-1-7b-sorry.md issues/closed/

# open → pending (外部依存待ち)
git mv issues/0042-bg-s1-lem-1-7b-sorry.md issues/pending/

# pending → open (再開)
git mv issues/pending/0042-bg-s1-lem-1-7b-sorry.md issues/

# closed → open (再オープン)
git mv issues/closed/0042-bg-s1-lem-1-7b-sorry.md issues/
```

`git mv` で履歴が繋がる (`git log --follow` で追える).

### 一覧

```bash
ls issues/*.md          # open
ls issues/pending/      # pending
ls issues/closed/       # closed
```

### grep

```bash
grep -lr "frobenius" issues/         # 全状態を対象
grep -lr "frobenius" issues/*.md     # open のみ
```

## やらないこと

- **GitHub Issues 連携はしない**. ローカル完結を優先.
- **`status:` frontmatter の追加**. 配置ディレクトリと冗長になり drift する.
- **slug の自動生成**. 日本語ローマ字化 / 切り捨ては底なし沼.
- **issue templates の分岐** (bug / task / design / ...). 1 種類で運用する.
  scaffold セクションが「背景 / やること / 完了条件 / 参照」 で全種を吸収できる.
- **`bin/issue-close` 等の状態遷移スクリプト**. `git mv` が十分シンプルなので
  ヘルパー無し. 入れるべき副作用 (ラベル更新等) が出てきた時に検討.

## なぜこの構造か (設計メモ)

- **ファイル名に slug を入れる理由**: `ls issues/` した時点で内容が分かる.
  `0001.md`, `0002.md`, ... では全部開く羽目になる. 5-6 件で破綻する.
- **slug を必須にした理由**: 採番後すぐにファイル名を確定したいので, タイトル
  決め打ちと slug 決め打ちを 1 コマンドで揃える. 後付け slug 化は名前変更が
  必要で履歴も汚れる.
- **状態を配置で表す理由**: source of truth が 1 つに定まる. frontmatter と
  両持ちにすると, frontmatter だけ書き換えてディレクトリ移動を忘れる事故が
  必ず起きる.
- **`pending` を入れた理由**: 「外部待ち」「自分の判断待ち」を closed と区別
  したい. closed は「もう触らない」, pending は「条件が変わったら戻す」.

## ライフサイクル例

```
1. bin/new-issue bg-s1-lem-1-7b-sorry "BG §1 Lem 1.7(b) sorry を埋める"
   → issues/0042-bg-s1-lem-1-7b-sorry.md 作成 + git add
   → git commit -m "issues/0042: 新規 (BG §1 Lem 1.7(b) sorry)."

2. 作業着手. 進捗を issues/0042 の「やること」「参照」に追記.
   関連コミットの hash をぶら下げる.

3. (a) 完了:
      git mv issues/0042-bg-s1-lem-1-7b-sorry.md issues/closed/
      git commit -m "issues/0042: closed (sorry 解消, commit abc1234)."

   (b) ブロック発生 (例: 別 issue 待ち):
      git mv issues/0042-bg-s1-lem-1-7b-sorry.md issues/pending/
      # 参照セクションにブロック原因を書く
      git commit -m "issues/0042: pending (issue #38 待ち)."

   (c) 取り下げ:
      git mv issues/0042-bg-s1-lem-1-7b-sorry.md issues/closed/
      git commit -m "issues/0042: closed (不要と判断, 理由は本文)."
```
