# main 合流モニター — A/B/D レーン自動合流の運用手順

> 横断運用ドキュメント。`/loop 15m` から参照される。main worktree = `/home/ywr/odd-order`。
> ユーザー方針 (2026-06-08): **「検証通過は自動合流」**。build green + axiom-clean + sorry 不増を
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` して報告。
> **2026-06-11 追加**: 合流 commit が成立したら最後に `git push origin main` (cron job `a8824a71`;
> 変化なし/全 abort 時は push しない)。

## レーン (2026-06-14: B+F+G+H、branch = lane-b/f/g/h、FT spine pipeline)

| レーン | branch | 内容 | 推奨モデル | 自動合流 |
|---|---|---|---|---|
| **B** | `lane-b` | Pf §6: (4.x) certain-type → case-B → (6.8) capstone (`S08_CoherenceTheorems:59` 唯一実 sorry) | Opus 4.8 (1M) | ✅ 対象 |
| **F** | `lane-f` | **Wielandt (9.1) I-1 critical path** (2026-06-16 夜³ reactivate, issue 7004): `CoprimeAction`/`RepresentationTheory/*` のボトムアップ。on-path lead-up (I-3→step2→系(i)→I-2) を loop、I-1 modular Brauer hard wall で escalate。**producing** (F=0 は first commit 後なら stall 候補) | Opus 4.8 (1M) | ✅ 対象 |
| **G** | `lane-g` | **§16 skeleton pre-positioning** (2026-06-17 夜² ユーザー裁可で §15→§16 転換): `S16_MainResults` 主結果 (proposition_type_classification → theoremI_type_dichotomy_of_inputs → theoremII_tame_embedding_of_inputs) を `_of_inputs` skeleton 化。§15.2 は depleted。**S16_MainResults editable 部を G に再 grant** (F は Wielandt) | Opus 4.8 (1M) | ✅ 対象 |
| **H** | `lane-h` | **long pole 単独**: Lem 12.17 TI clause (`S12_E`) → Prop 14.2 (g) `S14:1796` → Thm 14.7 `typeP_duality` `S14:1964` (Thm 3.10(a) は完了済) | Opus 4.8 (1M) | ✅ 対象 |

**G 固有の取り決め (2026-06-12)**: (1) G は **S12_E.lean を編集しない** (F の active ファイル)。
(2) G の §12 依存は sorry'd statement の引用で賄う — **新規 `axiom` 宣言が G から来たら従来どおり
abort+ユーザー承認**。(3) `notes/bg/s13_prime_action.md` は G 所有 (F は触らない)。
(4) issue base: B=1000 / F=7000 / **G=8000** / **H=2000**。
マージ順 = **F → G → B → H** (独立レーンゆえ順序は形式的)。

**H 固有の取り決め (2026-06-12)**: (1) H は **Lane B の §4–§9 coherence/certain-type ファイル
(`S04_*`〜`S09_*`) を編集しない** (cite のみ)。(2) §10–13 は BG↔Pf interface (BG Thm A–E/I–II)
に gate されるため、H が interface を **新規 forward axiom 化する commit は従来どおり
abort+ユーザー承認** (G の issue 8000 と同型; H の issue base = 2000)。(3)
`notes/peterfalvi/s10_13_maximal_structure.md` は H 所有。

**📌 一時例外 (issue 8001, 2026-06-12): G の S12_ECore de-private を許容合流**。
G の履歴に `chore(s12): de-private sylow_le_derived_of_mem_tau3` (commit `4b92778f`, S12_ECore.lean
5 行, **user裁可 issue 8001**) が含まれる。G が de-axiom 後にマージする際、上記「G が S12_E 系を
編集 → abort」ゲートがこれに hit するが、**この de-private のみなら例外的に合流許可**
(`git diff main..bg-s13 -- '*S12_E*'` の差分が `private` 削除 + cite 1 箇所のみなら OK)。
それ以外の S12_E/S12_ECore 内容変更が混じれば通常どおり abort。

**📌 一時例外 (issue 0065, 2026-06-12): F の cor12.16 statement +2 sorry を許容合流**。
hub→F 依頼で F が S12_E に BG Cor 12.16(a)(b) の **faithful statement 2 個を sorry'd で追加**する
(`sigma_subgroup_pRank_normalizer_le_one` + `sigma_subgroup_not_mem_primeFactors_derived_of_tau1`)。
これは G の forward axiom `cor1216×2` を de-axiom するための健全化ゆえ、**通常の sorry 増=abort の
例外として +2 を許容してマージする**。判定: F の commit message に「issue 0065」があり、増えた sorry が
上記 2 statement のみなら合格。それ以外の sorry 増は通常どおり abort。完了後 G が de-axiom すれば
forward axiom が消え G の HOLD も解除 (issue 0065 のハンドシェイク参照)。

**E (`bg-local`) は 2026-06-11 退役** — 任務完遂 (Lem 10.4(b) de-axiom / Lem 10.13 / Thm 11.5 /
Cor 11.6 / **Thm 11.7 = §11 完結**)。全量 main 合流 (merge `77ab5173`) を検証の上 worktree・
branch とも削除済み。旧 **A** / **D** も同様に退役済み (履歴は main の merge commit に全残存)。

**forward-axiom ポリシー**: 残存 forward axiom **0 本** (10.4(b) は E が実証明化済)。レーンが
**新規の** forward axiom を導入する commit は自動合流しない — 報告してユーザー承認を待つ
([[scaffold-sorry-free-not-done]])。island は縮小方向のみ自動合流可。

## 各イテレーションの手順

1. 各レーンの未マージ確認: `git log --oneline main..<branch>`。
   **全レーン 0 なら「変化なし」1行報告で即終了**（build を走らせない）。
2. **F → G → B → H の順**で（独立レーンゆえ順序は形式的）、未マージがあれば自動合流:
   - マージ前の実 sorry 数を記録: `bin/count-sorry`
     （prose 偽陽性 [sorry-free / sorryAx / `sorry'd` / backtick 引用] を除外する判定器。
       旧 `grep '(^|[^a-zA-Z-])sorry'` は 259 と過大計上したが count-sorry は 146 ≈ 実 141。
       絶対数の ground truth は build 警告 `lake build OddOrder 2>&1 | grep -c 'uses .sorry.'`）
   - `git merge --no-ff --no-commit <branch>`
   - **コンフリクト時**:
     - `AxiomsCheck.lean` / `OddOrder.lean` の**独立追記衝突** = 両ブロック保持で解決して続行
       （A=keystone 系の `#assert_only_allowed_axioms`、B=Peterfalvi 系の同コマンドは別定理ゆえ両方有効）
     - それ以外・内容が絡む衝突 = `git merge --abort` で**報告**（自動解決しない）
   - **staged が全て `notes/` 配下なら build 省略**(Lean 不変ゆえ結果不変)し直接 commit へ。
   - **`.lean` を含む場合 — sorry 先行チェックで build 短絡**: build は重い (~3800 jobs) ので**先に**
     `bin/count-sorry` を取る。増えていれば `git diff --cached` で **regression か scaffold か**判定し、
     **regression（証明済→sorry）or 新規 axiom なら build せず即 `git merge --abort`**。
     scaffold（新 decl statement）or 不増なら `lake build OddOrder OddOrder.AxiomsCheck`(background, 完了待ち)へ。
   - **合格条件**（全て満たす）:
     - build exit 0 かつ最終行 "Build completed successfully (N jobs)"
     - AxiomsCheck OK（`#assert_only_allowed_axioms` 由来のエラーなし）
     - **sorry ポリシー（2026-06-15 改定: scaffold 許可, ユーザー裁可）**: `bin/count-sorry` の増加を即不合格にしない。
       hold するのは (a) **regression**（既存の証明済 decl が `sorry` に退化）と (b) **新規 axiom** のみ。
       **新 decl の faithful scaffold statement 追加（`theorem/lemma … := sorry`）は許可**（§13→§14→§16 interface-building の正常進行）。
       - 判定: count 増加時は `git diff --cached -- '*.lean' | grep -E '^[+-].*sorry'` を確認。
         追加 `+… sorry` が同 hunk の追加 `+theorem/+lemma`（=新 decl）に属すれば scaffold ⟹ **ALLOW**。
         既存 decl の proof が `+sorry` に置換（新 decl 行が伴わない）なら regression ⟹ **HOLD+報告**。
       - count-sorry は prose 偽陽性（sorry-free / sorryAx / `sorry'd` / backtick 引用）を除外済（残差 +5 は安定 prose）。
         絶対数 ground truth は build 警告 `uses .sorry.`。
   - 合格 → `git commit`:
     `Merge '<branch>' (<topic>): <要約>` + 本文に各単位 + 末尾
     `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
   - 不合格 → `git merge --abort` で**報告**（何が落ちたか・どのファイルか）
3. **新規 forward axiom を含む commit** (`axiom ` 宣言の追加を `git diff --cached` で確認) は
   自動合流せず abort → 報告（上記ポリシー）。
3b. **root closure 検査 (2026-06-11 追加, E の発見)**: 新規追加 `.lean` ファイル
   (`git diff --cached --name-only --diff-filter=A -- '*.lean'`) は **root closure から到達可能**
   でなければならない — `OddOrder.lean` に import 行があるか、closure 内の他 `.lean` が import
   している (例: hub の prefix-split で旧 module 名ファイルが新 Core を import する場合は追記不要)。
   どちらも無いと `lake build OddOrder` の対象外でゲートをすり抜ける (実例: S05b /
   S11_MsigmaANormal が closure 外で未検証だった)。孤立時 = hub が `OddOrder.lean` に import 行を
   追記してから build (機械的修正、abort 不要)。
4. **サイズ watch (粒度規約の enforcement, 2026-06-11)**: 合流後に
   `git diff HEAD^ --stat -- '*.lean'` で touched .lean の現在行数を `wc -l` 確認。
   **1,500 行超の既存ファイルへの追記**を検出したら: 合流は維持しつつ ⚠ flag をサマリに含め、
   分割 issue が未起票なら起票する（分割の実施 owner = hub。lane の frontier と衝突しない
   凍結境界で prefix-split する）。lane 側のデフォルト（新主結果番号 = 新 leaf）は LAUNCH.md に記載。
5. **push**: 合流 commit が 1 件以上成立していれば最後に `git push origin main` (exit 0 確認、
   失敗は報告)。変化なし/全 abort なら push しない。
6. **サマリ報告**: 各レーン {マージ済 N commits / コンフリクト abort / 待機 / 変化なし} + 未マージ残数
   + サイズ flag + push 結果。
7. **LOOP GATE VERDICT 維持 (2026-06-17 追加, [`lane_loop_policy.md`](lane_loop_policy.md))**: 各 worktree の
   `LAUNCH.md` 冒頭「▶ LOOP GATE」ブロックは各レーンが起動時に `/loop` を自己選択する判定材料。**毎 tick で
   再監査はしない** (重い)。代わりに、今 tick のマージが**他レーンの gate を解いた**ときだけ VERDICT を見直す:
   - `typeP_duality` (lane-h) が proved → G の conjunct 2/assembly + F の §16/POLE-2 が解禁 → G/F の VERDICT を
     `STOP`→`LOOP`/`LOOP_THEN_STOP` に更新しうる。
   - σ-gap (`C_M(Q)≤M_σ`, issue 8012) が proved → G の conjunct 3-5 が unconditional 化。
   - (6.8) capstone (`S08_CoherenceTheorems:59`) が閉じた → B を次タスクへ。
   判定 = マージ差分に上記 gate statement の `sorry` 除去が含まれるか。含まれれば該当レーンの LAUNCH.md VERDICT
   行を更新 (worktree LAUNCH.md は git-excluded ゆえ直接編集可・build 不要)、含まれなければ触らない。サマリに
   「VERDICT 更新: \<lane\> \<old\>→\<new\>」を 1 行。**新規レーン投入時や VERDICT が古い疑いがあれば** 単発で
   loop-readiness 監査 (read-only、frontier ファイル + cite 先 sorry 有無を grep) を回して VERDICT を引き直す。

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
- **lane が merge 済み commit を amend した場合** (実例 2026-06-11, `b582007f`→`9581665d`):
  ff 同期が "Diverging branches" で落ちる。対処: (1) `git log --oneline -3 <branch>` +
  `git merge-base main <branch>` で amend (親が main の merge 前 HEAD) を確認、(2) 通常の
  `--no-ff --no-commit` trial merge — 内容が上位集合なら自動解決またはファイル単位 theirs、
  (3) `git diff main <branch> -- <file>` = 0 なら実差分は付随物 (guard 等) のみ。通常ゲートで commit。
  予防 = 各 LAUNCH.md に「commit 後の amend/rebase 禁止」を明記済み。
- **前セッションがマージ途中で死んだ場合**: 新セッション開始時に `git status` が staged 変更 + `MERGE_HEAD`
  を持ち、`git merge` が `fatal: ... MERGE_HEAD exists` を返す。これは「コンフリクト解決・staged 済みだが
  build/検証/commit 前」の状態。対処: (1) `cat .git/MERGE_HEAD` がどのレーン branch HEAD と一致するか確認、
  (2) `git grep -lE '^(<<<<<<<|=======|>>>>>>>)'` でコンフリクトマーカー残存なしを確認、(3) 通常の
  build + AxiomsCheck + sorry 不増ゲートを通し、(4) 合格なら `git commit` で完結（不合格は `git merge --abort`）。
  注意: 真の pre-merge sorry 数は既にマージ適用後なので、`git show main:<file>` で touched .lean を main HEAD と比較する。
- **⚠ cron × 手動マージの競合 (2026-06-11 実害)**: cron が**並行発火**して、進行中の `--no-commit`
  trial merge を `MERGE_HEAD exists` 検出 → `git merge --abort` で**消す**事故が発生 (F の 12.18
  staged merge が tree-clean に巻き戻り、952 行の取込が消えた)。対策 2 つを cron prompt に組込み済:
  (1) **cron 冒頭ガード**: `.git/MERGE_HEAD` 存在時は「前マージ進行中, skip」で即終了、**絶対に
  abort しない**。(2) **手動マージは atomic**: merge→build→commit を 1 ターンで完結し staged のまま
  長時間放置しない (放置中に次 tick が衝突)。加えて merge 出力は `> /tmp/merge.log 2>&1` へ退避
  (S12_Lemma1218 の大量 hunk で「Auto-merging」が 100+ 行出て端末が壊れ、誤診の元になった)。
  マージ結果の正否は `git show :<file> | wc -l` で**期待行数**を実値確認するのが確実
  (索敵: theirs が取り込まれたか。base==ours で theirs 変更なら theirs 採用が正)。

## 現状メモ

- **2026-06-18 (後刻) — POLE-1 設計訂正 + option-1 再タスク + 4 レーン合流**: cron 再消滅 (`/model` 切替) →
  新 cron `9fb5aff8` (`4,19,34,49 * * * *`, session-only, push なし) 再作成。**4 レーン合流** (f→g→b→h, clean,
  build 緑 3859 jobs / AxiomsCheck OK / 実 sorry **141→140**): 目玉 = **lane-g が `section16MaximalPair`
  producer 証明** (`651a2bae`, issue 8014 close, POLE-1 §16 obligation 1 本 discharge)。
  **🔑 POLE-1 設計判断**: lane-f が「`section16TypePStructure_of_isMinimalSimpleOdd` は現仕様で型レベル充足不能」
  と指摘 (issue 7005) → **hub 独立検証 (3レンズ高確度 CONFIRMED)**: 出力が `W_eq_inter : W = mp.S ⊓ mp.T`
  cyclic を要求するが入力 `Section16MaximalPair` は W を持たず公理が共役不変 (共役 partner `Mstar^g` が全公理
  充足の反例)。真の missing math = **逆包含 `M⊓Mstar ≤ K⊔Kstar` = BG Thm I clause(2) `S∩T=W`** (Lean の
  `theoremI`/`maximalSubgroup_type_dichotomy` `S16_MainResults:950` が drop した unfaithful transcription;
  forward `K⊔Kstar≤M⊓Mstar` は `typeP_duality` `S14:7961` から既出)。姉妹 `section16MaximalPair` は非ブロック。
  **ユーザー裁可 = option 1 (難所に正面)**: ① lane-f が逆包含を新 leaf `S16_PairIntersection.lean` で形式化
  (caveat: 上流 §16 prereq=Prop 16.1 等に bottom-out したら sorry 退避せず STOP+報告) → ② lane-g が `S∩T=W`
  clause を dichotomy に復活 + `Section16MaximalPair` を W で enrich → ③ lane-f が typeP producer を discharge。
  両 LAUNCH (f/g) に REASSIGN #2 記載済。フィードバック「並列化は適度な粒度で」([[feedback-reasonable-parallelism-granularity]]) 記録。
- **2026-06-18 (監視再開) — cron 再作成 + f/g stall flag**: `/model` 切替で旧 cron (`8922498c`) 消滅
  ([[cron-dies-on-model-switch]]) → 新 cron `aa439f22` (`3,18,33,48 * * * *`, session-only, **push なし**=
  2026-06-18 standing policy) を再作成。tick 時点: **全レーン未マージ 0** (b/f/g/h の成果は main 合流済、
  main HEAD `10dcec96`、実 sorry `bin/count-sorry`=141)。FT critical path は `Section16Inputs` の 3 producer
  skeleton (`FeitThompson.lean:267` section16MaximalPair=G / `:274` section16TypePStructure=F / `:282`
  section16CharacterData=B) + POLE-2 (`S16_NonExistenceG` field_normalizer_structure=H) に底打ち。
  - **lane-b**: 稼働中 (S08_CaseBAnchoredSeed.lean 編集, 83min 前 commit `2ef62cc8`)。(6.8) capstone case-B 継続。
  - **lane-h**: POLE-2 tractable 部 (`field_normalizer_structure` sorry-free + cyclotomic 算術核 `e7cc9ddc`) を
    landing し**自己 VERDICT=STOP**(残 14.7 finite-field model は §10-13 char theory gate=明示 stop trigger)。正常停止。
  - **⚠ lane-f / lane-g = 3h 静止**: 再配分 `a79a331b` 以降コミット・ファイル編集とも無し (b/h は同点以降に前進)。
    sessions 未起動 or 即ブロックの疑い。g=section16MaximalPair (§16 main results が type-data construction
    4-bridge に gate=大物)、f=section16TypePStructure (g の `mp` 入力前提)。要ユーザー判断 (再起動 or 再割当)。
- **2026-06-17 (夜²) — G を §16 skeleton pre-positioning に転換 (ユーザー裁可 + feasibility audit `a8b3835fd`)**:
  §15.2 の §14-非依存 skeleton が depleted (conjunct 3 landing 済 `d2961075`、残 conjunct 2/4/5 は σ-gap/§14
  gated で空転) とコード検証 (audit `lane-g 監査`) で確定 → ユーザー裁可で **G を §16 (`S16_MainResults.lean`) に
  転換**。F が Wielandt I-1 へ pivot して §16 が空いたため衝突なし (F は §16 復帰せず Wielandt 継続; H が
  typeP_duality landing で F が §16/POLE-2 復帰する際に ownership 再調整)。G の objective = §16 主結果を `_of_inputs`
  skeleton 化、価値順 3 ユニット: (1) `proposition_type_classification` (`S16_MainResults:495`, typeP_duality
  非依存, ~1 session, 最初の一手) (2) `theoremI_type_dichotomy_of_inputs` (`:527-635`, typeP_duality named-hyp,
  FT path 直結, ~1-2 session) (3) `theoremII_tame_embedding_of_inputs` (`:685-803`, ~1 session)。⚠ G は
  **editable 部のみ** (frozen `S16_NonExistenceGCore` は不可)、F 既済 skeleton
  (`theoremD_..._of_inputs`/`theoremII_conjunct1_of_inputs`) は複製しない。**「G = §15 専念 / S16_MainResults
  編集禁止」の旧取り決めは G に限り解除** (F が Wielandt にいる間)。G VERDICT: STOP→LOOP_THEN_STOP。
- **2026-06-17 (夜) — レーン自律 loop ポリシー導入 ([`lane_loop_policy.md`](lane_loop_policy.md))**: ユーザー要望で
  「各レーンが LAUNCH.md の記述を見て妥当なタイミングで自律的に `/loop` を選べる」仕組みを構築。各 worktree の
  `LAUNCH.md` 冒頭に「▶ LOOP GATE」ブロック (VERDICT = LOOP / LOOP_THEN_STOP / STOP + objective + develop leaf +
  stop-when + gates) を配置。判定の正本 = `lane_loop_policy.md`。**ハブは他セッションに loop を注入できない**
  (`send_message` は承認必須 + unsupervised 不可) ゆえ判定を外在化し、レーン自身が起動時に評価する。初回 VERDICT
  (8-agent code-verified + 敵対的検証 audit `woudrwk45`): **H**=LOOP_THEN_STOP (>½|G| count + 補題抽出) /
  **B**=LOOP_THEN_STOP (brick 3→4、S08:59 で停止) / **G**=STOP (conjunct 2-5 は σ-gap+§14 gated、連続 loop は
  σ-gap ローカル discharge で空転 — 残務は条件付き `_of_inputs` skeleton 離散ユニットのみ) / **F**=STOP→**LOOP_THEN_STOP**
  (ユーザー裁可 2026-06-17 で **I-1 critical path に pivot**; off-path の step 3 は後回し、build order
  I-3→step2→系(i)→I-2 を loop、I-1 modular Brauer hard wall ~6-9 session で escalate=最強モデル+ChatGPT)。
  ハブは上記手順 7 で gate 解除時に VERDICT を更新。
- **2026-06-17 — B の (6.8) §6 gap ブロッカーはユーザー直接対応 (再 flag しない)**: B の session 49 RECON で
  (6.8) capstone の最終 obligation `hXanchored` が「純 wiring」でなく未形式化の §6 certain-type structure
  theory (5 gap: p-group reduction / selection positivity / weight identity / hXmixed all-y / A/B dispatch)
  と判明し B が loop STOP。hub が方向を AskUserQuestion したところ、ユーザーは「**B レーンが直接やりとりする
  から大丈夫**」と回答。⟹ **B の停滞は既知・ユーザー管理下ゆえ、merge tick の stall 検出で B を再 thumbs-down
  しない**（commit が notes のみ/0 でも黙って合流継続）。B が Lean を再開したら通常合流に戻る。

- **2026-06-16 (夜³) — F REACTIVATED → Wielandt (9.1) (ユーザー裁可, hub code-verified)**: ユーザー問
  「F はまだ standby が正着か」を受け hub が実コード再検証。2 long pole（H `typeP_duality`
  `S14:4729` / B `(6.8)` `S08_CoherenceTheorems`）は**両方とも未達を確認**（standby の前提は真）。
  だが「F に ungated 作業不在」は誤りと判明: **Wielandt (9.1) `CoprimeAction.lean` の 3 実 sorry**
  （`wielandt_fixedPoint_frobenius`/`_trivial_E_fixed`/`_trivial_U_fixed`）は FT closure 内・依存的に
  ungated（入力=`IsFrobeniusGroup`+coprime のみ）・非衝突（消費側 Pf §11 は docstring 参照のみ、term 未配線）。
  ⟹ ユーザー裁可で **F を Wielandt (9.1) に reactivate**（issue 7004, base 7000, hard 多 session）。
  **⚠ cron の「F=0 は STANDBY ゆえ正常」は失効** — F は今後 producing。次 cron で F-status 行を訂正
  （reactivate 直後 1-2 tick は F=0 でも stall でない＝first commit まで）。再開トリガー = H が
  `typeP_duality` landing → §16 解禁で F を §16/POLE-2 に呼び戻し（Wielandt 進捗 commit して pivot）。

- **2026-06-16 — F STANDBY (ユーザー裁可, 2 scout で code-verified) [上で superseded]**: F は §16 集約後 POLE-1 +
  Thm II hDsub/Conjunct1 skeleton を landing したが、残 §16 はすべて上流 gated (S16 Thm A-E/II = §14/§15、
  POLE-2 = Pf §10-13 char theory) と確定 → **ungated FT-critical task 無し ⟹ STANDBY**。**merge tick で F=0 は正常、
  flag しない**。再開トリガー: H が §14 Thm A-E feeder/14.7 を landing (→S16 解禁) / B が (6.8)+Pf §10-13 char API
  (→POLE-2 解禁)。hub はこれを検出したら F を reactivate。B/G/H は継続活発 (sorry 142, Prop 14.2 完了済)。

- **2026-06-15 (夜²) — §16 集約 re-split (F↔G, ユーザー裁可) + Prop 14.2 COMPLETE**:
  H が **BG Prop 14.2 `typeP_structure` を sorry-free + axiom-clean で COMPLETE** (`f031f7bc`, (g) discharge,
  issue 2007 close) = long pole funnel keystone。実 sorry 144→143。次 long-pole gate = Thm 14.7 `typeP_duality`
  (§16 structure = Mstar ∃!/M̃/Lem 14.6 に cross-lane gated)。
  - **F の POLE-2 は deeply gated 判明** (F deep-dive: arith cascade 既証明、全 dispatch が sorried producer
    funnel) → scout で ungated task 精査 → 唯一 = Thm II cite-compress だが G の file (collision)。
  - **⟹ §16 を F に集約 (ownership re-split, ユーザー裁可)**: **F = BG §16 全体** (`S16_MainResults` +
    `S16_NonExistenceG` + `FeitThompson` POLE-1)。即時 = Thm II cite-compress (issue 8009, G→F 移管)。
    POLE-2 は §16 character cascade landing 後に同所有で再開。**G = §15 専念** (`S15_MF` のみ)。
    G は今後 `S16_MainResults` を触らない (cite のみ)。clean handoff (G の §16 WIP は合流済・残無し)。

- **2026-06-15 (夜) — レーン再配分 (11-agent code-verified review + ユーザー裁可) + S16 prefix-split**:
  全レーン synced + warm (main `b66af8aa`)。再配分レビューで判明・確定:
  - **✅ Thm 3.10(a) は完了済** (`S03g_Thm310.lean:75` `prime_card_complement_of_frobenius_conj`、
    Core/Module とも 0 sorry)。「真の long pole = 3.10(a) §3 rep-theory」は **stale**。
  - 真の binding long pole = **§14 funnel** = Lem 12.17 TI clause → Prop 14.2 (g) `S14:1796` →
    Thm 14.7 `typeP_duality` `S14:1964` (~2-3.5 session の §12/§14 wiring)。`typeP_duality` は下流
    (S15_MF:785/795/1976, S16:437) が consume する唯一の §14 定理。
  - **配分**: H = long pole 単独 (別 lane 投入は S14:1796/S12_E 衝突ゆえ不可)。B = Pf §6 (6.8) 継続。
    G = §15/§16 `_of_inputs` skeleton 前倒し (cite-compress drift 停止)。F = POLE-1 skeleton
    (`FeitThompson.lean:70`, hub split 不要) + POLE-2 secondary。
  - **⚠ S12_E 一時 grant → H**: H が Lem 12.17 TI clause を `S12_E*.lean` に追加する (F が §12 から
    退いたため実質 unowned)。従来「G/他レーンは S12_E 編集禁止」は維持、**H に限り 12.17 clause 追加を許可**
    (issue 2007 / base 2000)。それ以外の S12_E 変更は通常どおり abort+承認。
  - **hub split 実施済**: `S16_NonExistenceG.lean` (6860→1979) を `end FieldNormalizerData` で prefix-split
    → 凍結 Core `S16_NonExistenceGCore.lean` (4917 行) + F の POLE-2 tail (1979 行)。de-private 1 件
    (`p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq`)。merge `b66af8aa`、build 3830 green。
  - **deferred hub task**: `S14_TypePCounting.lean` (2069 行) split は H が (g) から離れるまで保留 (issue 0069)。
    `S16_NonExistenceG.lean` tail (1979 行 >1500) は F の coherent frontier ゆえ現状維持。
  - cron はこの再配分後に再作成 (`/model` 切替で旧 session cron 消滅 [[cron-dies-on-model-switch]])。

- **2026-06-11 (夜) — §11 完結・E 退役・F 再開 (12.18 先行)**: E の最終成果 Thm 11.7
  (`S11_MsigmaANormal.lean` 977 行 leaf) を合流 (merge `77ab5173`, 実 sorry 266→264) し
  **BG §1-§11 が proof レベル完結**。E は worktree+branch 削除で退役 (ユーザー裁可)。
  B (4.5.b) Brauer counting bound も合流 (merge `cc81837b`)。**F 再開方針 (ユーザー裁可) =
  12.18 先行**: skeleton (notes/bg/s12_subgroup_e.md「Lane F session 1」) が鮮度の高いうちに
  Fable 5 (1M) で組立 → 着地後 cascade 12.3→12.16 (Thm 11.7 着地で全解禁済) を Opus 4.8 で回収
  → §13 Prime Action (notes/bg/s13_prime_action.md, S13 ファイル新設 ~800-1100 行)。
  cron は B+F 監視に更新 (job 旧 `a8824a71` → 新 `d87f439a`; F→B 順, push 込み)。ゲートに root closure 検査 (手順 3b)
  を追加 — E の「root 登録ギャップ」gotcha のメカニズム化。hub 保留タスク = 分割 issue
  0063 (S10_LocalLemmas 2364 行) / 0064 (S05_NarrowPGroups 4039 行) の実施 (全 BG §4/§5/§10
  ファイルが凍結済みの今が安全窓)。
- **2026-06-11 (cron 再開) — 監視 loop 再開、自動合流対象 = B・E のみ**: ユーザー指示で
  15min cron (`2,17,32,47 * * * *`, session-only/durable=false, 7 日 auto-expire, job `a8824a71`,
  合流成立時 `git push origin main` 込み — 2026-06-11 ユーザー指示で追加)
  を再作成。再開巡で B (`d9d2b9da` Pf (4.5.b) 土台) と F (`6f6d7afc` BG 12.18 infra) を各 1 commit
  合流 (merge `004f6ae3` / `3336dc31`; build 3632 緑 / AxiomsCheck OK / 実 sorry 266 不増)。
  **F (bg-s12) は今回 1 回だけ手動合流し、以降の cron 監視対象からは外す** (ユーザー選択)。
  E (bg-local) は未マージ 0。⚠ サイズ flag: `S10_LocalLemmas.lean` 2364 行 (>1500) →
  分割 issue `0063-s10-locallemmas-split.md` 既起票済み (新規起票不要; E の active frontier ゆえ
  凍結境界が定まるまで実施は保留)。
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
