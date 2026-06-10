# main 合流モニター — A/B/D レーン自動合流の運用手順

> 横断運用ドキュメント。`/loop 15m` から参照される。main worktree = `/home/ywr/odd-order`。
> ユーザー方針 (2026-06-08): **「検証通過は自動合流」**。build green + axiom-clean + sorry 不増を
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` して報告。

## レーン (2026-06-11 再編成)

| レーン | branch | 内容 | 推奨モデル | 自動合流 |
|---|---|---|---|---|
| **B** | `b-peterfalvi` | Pf §6 certain-type (4.4)→(4.9) → S08 case-B → (6.8) | Opus 4.8 (1M); (4.4) kernel と停滞時は Fable 5 | ✅ 対象 |
| **E** | `bg-local` | BG 局所解析: Lem 10.4(b)→de-axiom→Lem 10.13→§11.5-7 | Fable 5 (1M); §11.5-7 以降は Opus 4.8 可 | ✅ 対象 |

旧 **A** (`a-keystone`) / **D** (`bg-s10-fwd`) は 2026-06-11 退役 — 全量 main 合流済みを検証の上、
worktree・branch とも削除済み (旧 `c-bg-s10` branch も同時削除。履歴は main の merge commit に全残存)。
10.13 着地後に **Lane F** (`bg-s12`, §12 残 14 件→§13) を増設予定。

**forward-axiom ポリシー**: 残存 axiom = Lem 10.4(b) 1 本 (E が消滅させる)。レーンが**新規の**
forward axiom を導入する commit は自動合流しない — 報告してユーザー承認を待つ
([[scaffold-sorry-free-not-done]])。island は縮小方向のみ自動合流可。

## 各イテレーションの手順

1. 各レーンの未マージ確認: `git log --oneline main..<branch>`。
   **全レーン 0 なら「変化なし」1行報告で即終了**（build を走らせない）。
2. **E → B の順**で（独立レーンゆえ順序は形式的; BG=E を先に固定）、未マージがあれば自動合流:
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
3. **新規 forward axiom を含む commit** (`axiom ` 宣言の追加を `git diff --cached` で確認) は
   自動合流せず abort → 報告（上記ポリシー）。
4. **サイズ watch (粒度規約の enforcement, 2026-06-11)**: 合流後に
   `git diff HEAD^ --stat -- '*.lean'` で touched .lean の現在行数を `wc -l` 確認。
   **1,500 行超の既存ファイルへの追記**を検出したら: 合流は維持しつつ ⚠ flag をサマリに含め、
   分割 issue が未起票なら起票する（分割の実施 owner = hub。lane の frontier と衝突しない
   凍結境界で prefix-split する）。lane 側のデフォルト（新主結果番号 = 新 leaf）は LAUNCH.md に記載。
5. **サマリ報告**: 各レーン {マージ済 N commits / コンフリクト abort / 待機 / 変化なし} + 未マージ残数
   + サイズ flag。

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
- **worktree の working-tree grep (`cd <wt> && grep -rnE … OddOrder/`) は未コミット WIP も数える** →
  sorry 増の**誤報源**。lane が draft 中の未追跡/未コミット `.lean`（実例: Thm 3.6 stub `S03f_Thm36.lean`）の
  sorry も拾うため、worktree では +N に見えても branch HEAD（コミット済）は不変なことがある。**merge が運ぶのは
  コミット済状態のみ**ゆえ、sorry ゲートの authoritative 判定は **trial merge 後に main 側で `grep -rnE … OddOrder/`**
  （= 実際に staged されるコミット済加算分）で行う。staged が notes のみ/該当 .lean を含まなければ worktree の +N は誤報。
- **前セッションがマージ途中で死んだ場合**: 新セッション開始時に `git status` が staged 変更 + `MERGE_HEAD`
  を持ち、`git merge` が `fatal: ... MERGE_HEAD exists` を返す。これは「コンフリクト解決・staged 済みだが
  build/検証/commit 前」の状態。対処: (1) `cat .git/MERGE_HEAD` がどのレーン branch HEAD と一致するか確認、
  (2) `git grep -lE '^(<<<<<<<|=======|>>>>>>>)'` でコンフリクトマーカー残存なしを確認、(3) 通常の
  build + AxiomsCheck + sorry 不増ゲートを通し、(4) 合格なら `git commit` で完結（不合格は `git merge --abort`）。
  注意: 真の pre-merge sorry 数は既にマージ適用後なので、`git show main:<file>` で touched .lean を main HEAD と比較する。

## 現状メモ

- **2026-06-11 — レーン再編成 (B+E の 2 レーン体制)**: A/D 退役 (worktree 削除・branch 残置)、
  B は main へ fast-forward 同期 (`f608143c`) + LAUNCH.md を session-22 現在地に刷新、
  **E (`bg-local`) 新設** (issue base **6000**, LAUNCH.md 配置済み): Lem 10.4(b)→de-axiom→
  Lem 10.13→§11.5-7。モデル配分 = E: Fable 5 (1M) / B: Opus 4.8 (1M) ((4.4) kernel と停滞時は
  Fable 5) / hub: Fable 5。10.13 着地後に F (`bg-s12`, base 7000) 増設予定。
- **2026-06-10 — Thm 3.6 完成 → D 合流 → de-axiom 完了。D の「報告のみ」規約は役目を終了**:
  Lane A が BG Thm 3.6 を完成 (`18a12a88`) → main 合流 (merge `36eb07db`)。ユーザー承認のもと
  **D (`bg-s10-fwd`) 全 67 commits を合流** (merge `2794232f`) し、`S10_ForwardFromKeystone.lean` の
  Thm 3.6 forward axiom を `Ch1.S03f.thm36` への bridge theorem に置換 (de-axiom, `fabd8efd`)。
  §10 spine の island は **Lem 10.4(b) axiom 1 本のみ**に縮小 (AxiomsCheck 1343 checks green)。
  **以後 D に新規 commit が来た場合の auto-merge 可否はユーザー未決** — 条件付き定理は引き続き
  10.4(b) island になるため、当面は従来どおり報告して指示を仰ぐ。同日 B も (4.3.b)→(4.3) COMPLETE
  →(4.4) anchor を連続合流 (`404d8814`/`1368e8fb`/`7c7045cc`/`f3eb00eb`/`4752484d`)。
  監視 loop はユーザー指示で停止中 (再開時は CronCreate 再作成)。
  ⚠ 実務知見: (1) `lake build … | tail` は exit code をマスクする — 判定には
  `; exit ${PIPESTATUS[0]}` を付ける。(2) de-axiom で S03f を import すると
  `OddOrder.GroupTheory.IsZGroup` が closure に入り、`open OddOrder.GroupTheory` 下の bare
  `IsZGroup` が mathlib 版と ambiguous になる → `_root_.IsZGroup` 修飾で解消 (型不変)。
- **2026-06-09 (後刻) — A: BG Thm 3.5 landed, 通常合流に復帰**: faithful 枝が sorry-free に到達
  (`S03e_Thm35.lean` real sorry = 0, commit `f51e4e85` "faithful-branch assembly COMPLETE
  (thm35_algClosed done)")。**BG Thm 3.5 を任意体で完全形式化**し main へ合流済 (merge `e42f4260`,
  build 3616 green / AxiomsCheck 違反なし / 実 sorry 273 不増)。⟹ 下の「A=報告のみ」特例は**失効**。
  A は通常の自動合流対象に戻る。**次の A frontier = BG Thm 3.6** (これが landed されると §10.6 keystone
  + Lane D の forward-axiom de-axiom が解禁され、D を手動合流できる)。それまで D は従来どおり報告のみ。
- ~~**2026-06-09 — A=現状維持 (ユーザー判断)**: faithful 枝に hard-core sorry 1 個ゆえ報告のみ~~
  (上記で解消・失効)。
