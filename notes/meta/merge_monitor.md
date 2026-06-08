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
   - **staged が全て `notes/` 配下なら build 省略**(Lean 不変ゆえ結果不変)し直接 commit へ。`.lean` を含むなら `lake build OddOrder OddOrder.AxiomsCheck`（background, 完了待ち）
   - **合格条件**（全て満たす）:
     - build exit 0 かつ最終行 "Build completed successfully (N jobs)"
     - AxiomsCheck OK（`#assert_only_allowed_axioms` 由来のエラーなし）
     - 実 sorry 数がマージ前**以下**（増えていない。main は既に ~144 の scaffold sorry を持つので絶対数でなく増分で判定）
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
