# 並行作業用 git worktree のセットアップ

**確定**: 2026-05-25

## 背景

`odd-order` は 1 セッションで章全部を進めるには大きすぎる. 同時に複数の章 / 節を別エージェントセッション (Claude Code / codex / ralph-loop) で進めたい場面がある.

愚直に worktree を切ると以下のコストが二重になる:

- `.lake/packages/mathlib` = **6.5 GB** (mathlib ソース + `lake exe cache get` で取得した olean)
- `lake exe cache get` 再実行 = **~5 min + ~3 GB DL**
- `references/` (gitignored 別 private リポ) も再取得

mathlib は `lakefile.toml` で **exact SHA** (`rev = "360da6fa…"`) に pin されており worktree 間で drift しないので, **mathlib パッケージと references を main worktree から symlink で共有**するのが最適.
(toolchain は `lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`、2026-07-09 bump。pin は toolchain tag でなく mathlib の SHA で効く。)

## セットアップ手順

### 1. 命名

- worktree path = `/home/ywr/odd-order-<slug>` (main の sibling)
- branch 名 = `<slug>` (同じ)
- slug は作業範囲を表す:
  - 章単位: `isaacs-ch05`, `bg-s03`, `peterfalvi-s04`
  - 単一 issue 攻略: `issue-0002-pcomplement` 等
  - 現行 (2026-07-19) の常設レーンは slug = `a`/`b`/`c` (`/home/ywr/odd-order-{a,b,c}`; 配分の正本 = [`lane_reallocation_2026_07_16.md`](lane_reallocation_2026_07_16.md)。旧 `ft_lane_reallocation_2026_06_28.md` は 2026-07-16 に SUPERSEDED)
- 衝突確認: `ls -d /home/ywr/odd-order*`

### 2. 作成 + symlink + olean warm-start コピー (5 コマンド)

```bash
git worktree add /home/ywr/odd-order-<slug> -b <slug>
mkdir -p /home/ywr/odd-order-<slug>/.lake
ln -s /home/ywr/odd-order/.lake/packages /home/ywr/odd-order-<slug>/.lake/packages
ln -s /home/ywr/odd-order/references /home/ywr/odd-order-<slug>/references
# 本プロジェクト olean を main から warm-start コピー (symlink は不可 = 並行ビルド衝突).
# `cp -a` で mtime を保つと lake の trace fast-path が効く. 新 worktree の HEAD が main と
# 近い (= 共有コミットが多い) ほど初回ビルドはほぼ no-op、離れていても stale 分だけ再ビルドで無害.
cp -a /home/ywr/odd-order/.lake/build /home/ywr/odd-order-<slug>/.lake/build
```

### 3. references symlink の untracked 抑制 (1 回だけ)

`.gitignore` の `references/` は trailing slash でディレクトリのみマッチ. symlink ファイルは素通りするので `git status` に出る. 修正:

```bash
echo "references" >> /home/ywr/odd-order/.git/info/exclude
```

`.git/info/exclude` は worktree 共有だが main では `references/` が実ディレクトリで既にマッチ済なので無害. 既に追加済なら再実行不要.

### 4. 初回ビルド

新 worktree 内で `lake build OddOrder` (または leaf) を直接実行. mathlib olean は symlink 経由で既存キャッシュを利用するので `lake exe cache get` は **不要**. **手順 2 で `.lake/build` を main からコピー済なら, HEAD 一致時は初回ビルドが warm cache で数秒の no-op** (trace 検証 + 最終リンクのみ); コピーしなければ本プロジェクト olean が全て再ビルド (数分). 実測: HEAD 一致の worktree で `cp -a` 後の `lake build OddOrder` = 3411 jobs / 約 3 秒。

### 5. issue 採番レンジの割り当て (並行発行の衝突予防)

並行セッションが `bin/new-issue` で同じ番号を取らないよう, この worktree に
**採番 base** を割り当てる (1000 の倍数; main = 0)。⚠ **base は「本」でなく「レーン」に固定**
(2026-07-16 配分、2026-07-19 再確認): **a = 1000 / b = 2000 / c = 3000**。
旧記載「Peterfalvi 系は base 1000 で固定・2000 以降は未使用値」は失効 — 2000/3000 は
新規 ad-hoc worktree に払い出してよい空き値ではない:

```bash
# 例: Peterfalvi worktree (base 1000 固定) — セッション冒頭で
export ODD_ISSUE_BASE=1000
# あるいは発行ごとに明示: bin/new-issue --base 1000 <slug> "<title>"
```

レンジごとに別 `SEQUENCE.N` を使うので採番もマージも衝突しない. 詳細・レンジ表は
[`issue_management.md`](issue_management.md) 「並行セッションの採番レンジ」.

## 共有 / 独立 の境界

| パス | 状態 | 理由 |
|---|---|---|
| `.lake/packages/` | symlink (共有) | mathlib pin 固定で drift しない. 6.5 GB 節約 |
| `.lake/build/` | 独立 (worktree ごと) — ただし作成時に main から **コピー**して warm-start | 本プロジェクト olean. 並行 `lake build` 衝突回避のため symlink 不可. コピーは HEAD 一致時に初回ビルドをほぼ no-op 化 (mtime 保持に `cp -a`) |
| `references/` | symlink (共有) | gitignored, 別 private リポで重い |
| `.git/info/exclude` | 共有 (主 `.git` 直下) | `references` 行は worktree 共通で害なし |

## 安全性 / 注意

- **`lake update` を worktree で走らせない**. 共有 `.lake/packages` の mathlib rev が書き換わって main 側もビルド不能になる. mathlib バージョン更新は main で 1 回だけ.
- **並行 `lake build` は OK**: `.lake/build/` が per-worktree なので衝突しない.
- **意味的依存に注意**: 例えば Ch.05 で `_root_.OddOrder.Isaacs.Ch04` namespace に forward axiom を置いた状態で main 側で Ch.04 本体実装が進むと, 後で merge 時に名前衝突する. これは worktree 問題ではなく合流時の人間判断 (axiom 削除タイミング合意) で扱う. forward dep の扱いは [`forward_dep_policy.md`](forward_dep_policy.md) 参照.

## 片付け

```bash
# main 側から
git worktree remove /home/ywr/odd-order-<slug>
git branch -d <slug>          # 未マージなら -D
```

symlink は worktree 削除で一緒に消える. `.git/info/exclude` の `references` 行はそのままで OK (再利用される).

## 関連

- [`subagent_orchestration.md`](subagent_orchestration.md): 並行作業を切るか判断する基準.
- [`forward_dep_policy.md`](forward_dep_policy.md): 章間 forward dep の扱い (worktree 合流時の名前衝突回避).
- CLAUDE.md "並行作業 (worktree)" セクションから参照.
