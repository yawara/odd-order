# main 合流モニター — A/B/D レーン自動合流の運用手順

> 横断運用ドキュメント。`/loop 15m` から参照される。main worktree = `/home/ywr/odd-order`。
> ユーザー方針 (2026-06-08): **「検証通過は自動合流」**。build green + axiom-clean + sorry 不増を
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` して報告。

## レーン

| レーン | branch | 内容 | 自動合流 |
|---|---|---|---|
| **A** | `a-keystone` | rep-theory keystone (BG Thm 2.5→3.4) | ✅ 対象 |
| **B** | `b-peterfalvi` | Peterfalvi §6 coherence + §5 TICyclic | ✅ 対象 |
| **D** | `bg-s10-fwd` | BG §10→16 **forward-axiom scaffold** | ❌ **報告のみ** |

**D を自動合流しない理由**: forward-axiom = 未証明の仮定。main に入れると FT 形式化の健全性を
損なう ([[scaffold-sorry-free-not-done]])。A が BG Thm 3.6 を landed して de-axiomatize された後、
**手動で**合流する。D に未マージがあれば「N commits 待機中（forward-axiom, Thm 3.6 待ち）」と報告のみ。

## 各イテレーションの手順

1. 各レーンの未マージ確認: `git log --oneline main..<branch>`。
   **全レーン 0 なら「変化なし」1行報告で即終了**（build を走らせない）。
2. **A → B の順**で（A=keystone が下流の根）、未マージがあれば自動合流:
   - マージ前の実 sorry 数を記録:
     `grep -rnE '(^|[^a-zA-Z-])sorry' OddOrder/ | wc -l`
     （コメント "sorry-free" 等の誤カウント回避に `(^|[^a-zA-Z-])sorry` を使う — [[memory: grep sorry]]）
   - `git merge --no-ff --no-commit <branch>`
   - **コンフリクト時**:
     - `AxiomsCheck.lean` / `OddOrder.lean` の**独立追記衝突** = 両ブロック保持で解決して続行
       （A=keystone 系の `#assert_only_allowed_axioms`、B=Peterfalvi 系の同コマンドは別定理ゆえ両方有効）
     - それ以外・内容が絡む衝突 = `git merge --abort` で**報告**（自動解決しない）
   - **staged が全て `notes/` 配下なら build 省略**(Lean 不変ゆえ結果不変)し直接 commit へ。
   - **`.lean` を含む場合 — sorry 先行チェックで build 短絡**: build は重い (~3600 jobs) ので**先に**
     `grep -rnE '(^|[^a-zA-Z-])sorry' OddOrder/ | wc -l` を取る。マージ前から増えていれば下記ゲートの ⚠ 手順で
     真の tactic sorry か判定し、**真の sorry 増なら build せず即 `git merge --abort`**(build が通っても sorry
     ゲートで落ちるため無駄)。増えていなければ `lake build OddOrder OddOrder.AxiomsCheck`(background, 完了待ち)へ。
   - **合格条件**（全て満たす）:
     - build exit 0 かつ最終行 "Build completed successfully (N jobs)"
     - AxiomsCheck OK（`#assert_only_allowed_axioms` 由来のエラーなし）
     - 実 sorry 数がマージ前**以下**（増えていない。main は既に ~144 の scaffold sorry を持つので絶対数でなく増分で判定）
       - ⚠ **count 増加でも即 abort しない**: `(^|[^a-zA-Z-])sorry` は docstring の「`(sorry-free`」を
         直前 `(` ゆえ誤マッチする（偽陽性）。増分があれば `git diff --cached` で新規マッチ箇所を特定し、
         真の tactic sorry か確認（`grep -nwE 'sorry' <file> | grep -vE 'sorry-(free|ax)'`、コメント/docstring 内なら偽陽性）。
         真の sorry 増のみ不合格。実例: BG Thm 3.4 keystone landing は「完全証明済 (sorry-free, axiom-clean)」comment で +1 偽陽性が出た。
   - 合格 → `git commit`:
     `Merge '<branch>' (<topic>): <要約>` + 本文に各単位 + 末尾
     `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
   - 不合格 → `git merge --abort` で**報告**（何が落ちたか・どのファイルか）
3. **D** (`bg-s10-fwd`): 未マージがあれば報告のみ（上記理由）。
4. **サマリ報告**: 各レーン {マージ済 N commits / コンフリクト abort / 待機 / 変化なし} + 未マージ残数。

## 注意

- A と B は `AxiomsCheck.lean` 末尾を共有 hotspot として両方追記 → **マージ毎にコンフリクトしうる**が、
  独立ブロック（別定理の axiom ガード）なので両保持で機械的に解決可。先頭 import 部も同様。
- `git merge --abort` は `--no-commit` で止めた状態でもコンフリクト状態でも有効。
- `lake update` 禁止（共有 mathlib rev を壊す）。コミットは **main のみ**。
- 各レーンの worktree (`/home/ywr/odd-order-<slug>`) には**触らない**（`git log main..<branch>` で読むだけ）。
- loop は同一セッション継続。マージ済みコミットは git が source of truth ゆえ状態ファイル不要
  （`main..<branch>` が毎回「まだ取り込んでいない分」を正しく返す）。
- **`git diff main..<branch>`（2-dot=端点差分）でマージ内容を判断しない**。各レーンは他レーンの成果を
  恒久的に持たない（例: B=b-peterfalvi は A=a-keystone の RepresentationTheory/Extraspecial 系を持たない）ので、
  端点差分は「他レーンファイルの大量削除」という**幻**を見せる（実測 4149 deletions に見えたことがある）。
  実マージは merge-base からの 3-way ゆえ、それらは「main 側のみ追加」扱いで保持される。マージ内容の確認は
  必ず `git merge --no-ff --no-commit` 後の `git diff --cached --stat`（=実際に staged される加算分）で行う。
- **前セッションがマージ途中で死んだ場合**: 新セッション開始時に `git status` が staged 変更 + `MERGE_HEAD`
  を持ち、`git merge` が `fatal: ... MERGE_HEAD exists` を返す。これは「コンフリクト解決・staged 済みだが
  build/検証/commit 前」の状態。対処: (1) `cat .git/MERGE_HEAD` がどのレーン branch HEAD と一致するか確認、
  (2) `git grep -lE '^(<<<<<<<|=======|>>>>>>>)'` でコンフリクトマーカー残存なしを確認、(3) 通常の
  build + AxiomsCheck + sorry 不増ゲートを通し、(4) 合格なら `git commit` で完結（不合格は `git merge --abort`）。
  注意: 真の pre-merge sorry 数は既にマージ適用後なので、`git show main:<file>` で touched .lean を main HEAD と比較する。

## 現状メモ

- **2026-06-09 — A=現状維持 (ユーザー判断)**: Lane A が初めて Thm 3.5 の `.lean`
  (`OddOrder/BG/Ch1_Preliminary/S03e_Thm35.lean`) を持ち込んだが、`thm35_aux` の **faithful 枝に
  hard-core sorry**(steps 3.4/3.5/Clifford)が 1 個残る(non-faithful 枝は COMPLETE、BG Thm 3.4 は
  既に main に landed 済)。ユーザー判断は **sorry 不増ゲート堅持・A は faithful 枝が sorry-free になるまで
  報告のみ**。⟹ A が ahead でも、上記「sorry 先行チェック」でこの sorry を検出したら build せず即 abort し、
  「A: faithful 枝 sorry 残り報告のみ」と報告する(scaffold を main に入れない)。A が sorry-free になったら通常合流に戻す。
