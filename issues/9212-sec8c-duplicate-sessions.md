
## 追記 (2026-07-27 22:20) — 同一 worktree・同一ブランチでの並行コミットを確認

当初は「別セッションが main 側で並行して同じ問題を解いている」と理解していたが、
**実際には同じ worktree `/home/ywr/odd-order-a`・同じブランチ `a` に、別のセッションが
同時にコミットしている**ことが確認できた。

観測 (すべて branch `a`、`main..HEAD`):

| 時刻 | commit | 備考 |
|---|---|---|
| 22:08:33 | `aaa886bd3` docs(1055) 8C.6 設計 | **当セッション** |
| 22:13:25 | `5ee9d4c8f` feat 8D.1 | 当セッションではない |
| 22:18:05 | `c3d9db3db` refactor(pf) issue 0160 | **Peterfalvi** — 当セッションは触れていない |
| 22:19:15 | `9719ab3d1` Merge main into a | 当セッションではない |
| 22:20:02 | `d0c66fdb5` feat 8D.2 | 当セッションが検証中に出現 |

決定的なのは `c3d9db3db` (Peterfalvi の refactor)。当セッションは本 session を通じて
Isaacs Problems しか触っておらず、Peterfalvi のファイルを開いてもいない。
また 8D.2 は当セッションが `#print axioms` で検証している最中にコミットされ、
その後の `git add -A && git commit` が "nothing to commit" を返した。

## リスク

同一 worktree での並行セッションは git 状態 (index / HEAD / stash) を共有するため、
片方の `git add -A` や `git stash` がもう片方の未コミット作業を巻き込みうる
(既知の failure mode)。現時点で実害 (作業消失・build 破壊) は観測していないが、
**継続すると高確率で衝突する**。

## 当セッションの対応

CLAUDE.md の escalation 条件 (iii)「想定外 git 状態 = merge-safety STOP、halt + 報告」
に該当すると判断し、**このセッションは新規のコミットを止めてユーザーに報告する**。
再開の可否 (どちらのセッションを残すか / worktree を分けるか) の指示を待つ。
