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
├── SEQUENCE             # 整数 1 行. 次回採番用カウンタ.
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
- `bin/new-issue <slug> "<title>"` がロックを取って SEQUENCE 読み出し → +1 →
  書き戻し → scaffold 作成 → `git add` までを 1 ステップで行う.
- ロックは **`mkdir` 原子操作**で実装. macOS は `flock(1)` を持たないので
  POSIX 標準で済む方式を選んだ. 5 秒 (50 × 100ms) 取れなければエラー終了.
- **ブランチ越しの衝突**は許容. 別ブランチで同じ番号を取った場合は
  マージ時に手動でリナンバ + SEQUENCE 解決. 発行頻度が低ければ実用上問題ない
  という割り切り (Django migrations と同じトレードオフ).

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
