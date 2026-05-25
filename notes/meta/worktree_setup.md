# 並行作業用 git worktree のセットアップ

**確定**: 2026-05-25

## 背景

`odd-order` は 1 セッションで章全部を進めるには大きすぎる. 同時に複数の章 / 節を別エージェントセッション (Claude Code / codex / ralph-loop) で進めたい場面がある.

愚直に worktree を切ると以下のコストが二重になる:

- `.lake/packages/mathlib` = **6.5 GB** (mathlib ソース + `lake exe cache get` で取得した olean)
- `lake exe cache get` 再実行 = **~5 min + ~3 GB DL**
- `references/` (gitignored 別 private リポ) も再取得

mathlib は `lakefile.toml` で `v4.29.1` に pin されており worktree 間で drift しないので, **mathlib パッケージと references を main worktree から symlink で共有**するのが最適.

## セットアップ手順

### 1. 命名

- worktree path = `/Users/ywr/odd-order-<slug>` (main の sibling)
- branch 名 = `<slug>` (同じ)
- slug は作業範囲を表す:
  - 章単位: `isaacs-ch05`, `bg-s03`, `peterfalvi-s04`
  - 単一 issue 攻略: `issue-0002-pcomplement` 等
- 衝突確認: `ls -d /Users/ywr/odd-order*`

### 2. 作成 + symlink (4 コマンド)

```bash
git worktree add /Users/ywr/odd-order-<slug> -b <slug>
mkdir -p /Users/ywr/odd-order-<slug>/.lake
ln -s /Users/ywr/odd-order/.lake/packages /Users/ywr/odd-order-<slug>/.lake/packages
ln -s /Users/ywr/odd-order/references /Users/ywr/odd-order-<slug>/references
```

### 3. references symlink の untracked 抑制 (1 回だけ)

`.gitignore` の `references/` は trailing slash でディレクトリのみマッチ. symlink ファイルは素通りするので `git status` に出る. 修正:

```bash
echo "references" >> /Users/ywr/odd-order/.git/info/exclude
```

`.git/info/exclude` は worktree 共有だが main では `references/` が実ディレクトリで既にマッチ済なので無害. 既に追加済なら再実行不要.

### 4. 初回ビルド

新 worktree 内で `lake build OddOrder.Isaacs.ChXX_...` を直接実行. mathlib olean は symlink 経由で既存キャッシュを利用するので `lake exe cache get` は **不要**. Ch.01-Ch.04 等の本プロジェクト olean だけビルドが走る (数分).

## 共有 / 独立 の境界

| パス | 状態 | 理由 |
|---|---|---|
| `.lake/packages/` | symlink (共有) | mathlib pin 固定で drift しない. 6.5 GB 節約 |
| `.lake/build/` | 独立 (worktree ごと) | 本プロジェクト olean. 並行 `lake build` 衝突回避 |
| `references/` | symlink (共有) | gitignored, 別 private リポで重い |
| `.git/info/exclude` | 共有 (主 `.git` 直下) | `references` 行は worktree 共通で害なし |

## 安全性 / 注意

- **`lake update` を worktree で走らせない**. 共有 `.lake/packages` の mathlib rev が書き換わって main 側もビルド不能になる. mathlib バージョン更新は main で 1 回だけ.
- **並行 `lake build` は OK**: `.lake/build/` が per-worktree なので衝突しない.
- **意味的依存に注意**: 例えば Ch.05 で `_root_.OddOrder.Isaacs.Ch04` namespace に forward axiom を置いた状態で main 側で Ch.04 本体実装が進むと, 後で merge 時に名前衝突する. これは worktree 問題ではなく合流時の人間判断 (axiom 削除タイミング合意) で扱う. forward dep の扱いは [`forward_dep_policy.md`](forward_dep_policy.md) 参照.

## 片付け

```bash
# main 側から
git worktree remove /Users/ywr/odd-order-<slug>
git branch -d <slug>          # 未マージなら -D
```

symlink は worktree 削除で一緒に消える. `.git/info/exclude` の `references` 行はそのままで OK (再利用される).

## 関連

- [`subagent_orchestration.md`](subagent_orchestration.md): 並行作業を切るか判断する基準.
- [`forward_dep_policy.md`](forward_dep_policy.md): 章間 forward dep の扱い (worktree 合流時の名前衝突回避).
- CLAUDE.md "並行作業 (worktree)" セクションから参照.
