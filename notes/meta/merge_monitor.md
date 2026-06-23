# main 合流モニター — A/B/D レーン自動合流の運用手順

> 横断運用ドキュメント。`/loop 15m` から参照される。main worktree = `/home/ywr/odd-order`。
> ユーザー方針 (2026-06-08): **「検証通過は自動合流」**。build green + axiom-clean + sorry 不増を
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` して報告。
> **2026-06-11 追加**: 合流 commit が成立したら最後に `git push origin main` (cron job `a8824a71`;
> 変化なし/全 abort 時は push しない)。

## レーン (2026-06-21 最新⁵: **B+F+H+C の 4 レーン体制**、branch = lane-b/f/h/c — FT frontier の大セグメント分割)

**4-lane 再編 (ユーザー裁可 2026-06-21)**: FT spine が深い線形チェーン (BG §14→16 → Pf §10→16) で char API
(Pf §3-9) は完成済みと判明 → FT frontier (102 sorry) を **signature-first で大セグメントに分割**。隣接ファイルの
重なり (旧 B/H が両方 Pf §10-16) を解消し、各レーンを contiguous な非重複セグメントに。

| レーン | branch | セグメント | 所有ファイル | 自動合流 |
|---|---|---|---|---|
**⚠ 2026-06-22 最小修正 (ユーザー裁可、機能再割当)**: lane-c issue 4002 + S11 衝突 ×2 → hub 深掘り
([`lane_functional_split_analysis.md`](lane_functional_split_analysis.md)) → §-分割が 3 機能 (群構造/Dade char/assembly)
を散乱させていたと判明。ユーザー選択「最小修正」(file-split なし、機能で再割当): **S11 を H 単独所有に
変更** (Wielandt §9 は H の連結 chunk、§11 衝突解消)、B は §10/§12/§13 char grid に専念、C は §16 char
endpoint を自走所有 (B 待ちにしない)。

**⚠ 2026-06-22 frontier-cluster 再配置 (ユーザー裁可、issue 4005 監査結果)**: 4-territory read-only audit で
「節区切りは starve を生むが実害は lane-c (§16 終点 = pure consumer) のみ。F/H/B は productive frontier 上、
lane-h 領域に ~16 独立 workable leaf 集中」と判明 → **lane-c を §16 から Pf §11 (Wielandt §9 / Clifford
9.6-9.10 = Pf 最上流の独立 5-leaf cluster) に再配置**。**S11 を H → C に移譲** (H は §14_MaximalI+§15 に集中)。
**§16 (S16_NonExistenceG) + §10 (S10) は driver 化** = 常駐レーンを置かず、上流 (BG §16 / S15) landing 時に
機会的に閉じる (実施 owner = hub、または上流を landing させたレーンが続けて driver で close)。各レーンを
productive な独立クラスタに乗せ、上流優先方針 (CLAUDE.md) にも合致。

| レーン | branch | 機能 (frontier クラスタ) | 所有ファイル | 自動合流 |
|---|---|---|---|---|
| **F** | `lane-f` | **BG §14-16 構造** | `S14_TypePCounting`/`S15_MF`/`S16_MainResults`/`S16_PairIntersection` + `FeitThompson.lean` の §16 producer。Theorem A-I / Prop 16.1 | ✅ |
| **B** | `lane-b` | **Pf §12 Dade char-grid + cd assembly** | `S12_MaximalIII_IV_V` + `section16CharacterData` (POLE-1 cd, §3-§13 束ね)。**`S13` を H 移譲 (2026-06-23)、`S10` は driver** | ✅ |
| **H** | `lane-h` | **Pf §13 char-grid (type III/IV)** | `S13_MaximalIII_IV` (active, 8 sorry) + `S14_MaximalI` (driver, (12.9) は Prop16.1 待ち=自己復帰)。**S15/S11/S12 は触らない** | ✅ |
| **C** | `lane-c` | **Pf §15 S&T** | **`S15_SAndT` (S&T 構造、36 sorry、2026-06-23 H→C 移譲)**。依存 §15→§14 ゆえ §14 を cite のみ。**`S11`/`S16_NonExistenceG` は driver (上流 landing 時に機会的 close)、常駐しない** | ✅ |

> **⚠ 2026-06-23 relane (ユーザー裁可、issue 4007)**: lane-c の §11 ungated 枯渇 (9.1-9.7 完了) を受け hub が
> frontier 再監査 → 「負荷は H/F に偏在 (各 51 sorry)、3 が並列限界でない」と判明。**H の 51-sorry 負荷
> (S14_MaximalI 15 + S15_SAndT 36) を 2 レーンに分割**: **S15_SAndT を H→C 移譲**、H は S14_MaximalI に集中。
> S15_SAndT は S14_MaximalI を import (依存方向 §15→§14) ゆえ signature-first 境界がクリーン (co-edit なし)。
> §11 は driver 化 ((9.8)-(9.11) は lane-b char 待ち)。各 LAUNCH.md 更新済。

> **⚠ 2026-06-23 relane #2 (hub 判断、issue 8018+2017、レーン等価方針)**: F と H が同時に ungated 枯渇を報告 →
> hub が **価値+独立性**で再配置 (レーンに専門/強みは無く等価 [[lanes-are-equivalent-no-specialty]])。
> **lane-f = hderF deep 投資** (Prop 16.1 hP2II 主 gate、ユーザー裁可)。**lane-h = §13 (S13_MaximalIII_IV) を
> lane-b→H 移譲** (§13 は §12 下流・lane-b 非編集 ⟹ signature-first 独立、§13→POLE-1 cd で critical path)。
> lane-h の S14_MaximalI は driver 化 ((12.9) は Prop 16.1 landing で自己復帰 close)。B は §12 + cd assembly に集中。

> **⚠ 2026-06-23 relane #3 (ユーザー裁可、issue 4008)**: lane-c の §15 が全 cross-lane gated (carrier=lane-f POLE-1)
> で2度目の starve → ユーザー裁可 (A) = **POLE-1 tp producer carrier を lane-f→C 移譲**。C は `S14_TypePComplement`
> (complement 露出) + `FeitThompson.lean` の tp 系 def (`Section16TypePStructure`/`section16TypePStructure_*`/
> `Section16Inputs` tp) を編集し、指定 complement を持つ `TypePData` を構成 (→ 自身の §15 unblock + POLE-1 前進)。
> F は hderF/Prop16.1 に集中・tp carrier は cite のみ・mp は F のまま。FeitThompson.lean は def 単位で F=mp+Prop16.1 /
> B=cd / C=tp の 3 者共有。lanes 等価ゆえ carrier 作業も C 可 [[lanes-are-equivalent-no-specialty]]。

**signature-first interface**: 上流が sorried signature を export → 下流が cite。真の cross-lane 依存は narrow。
signature 不足は notes/issue 経由。**driver (§16/§10)**: 常駐レーンを当てず、上流が landing したとき hub or
担当レーンが続けて opportunistic に close する (pure consumer ゆえ常駐は starve)。

**🔁 lane 自己復帰 (2026-06-23 導入)**: lane が hub 判断待ちで停止したら、自セッションで resume-monitor
cron を arm し、hub の解決 (LAUNCH.md 変化 or 起票 issue の closed/ 移動) を検知して `git merge main` +
作業再開する ([`lane_self_resume.md`](lane_self_resume.md))。**hub の合流手順は不変** — lane の自己復帰は
通常の作業再開ゆえ区別不要。hub は「停止していた lane が自走で戻ることがある」と認識するだけでよい。

**取り決め**: (1) 各レーンは**自所有ファイルのみ編集**、他は cite のみ (要望は notes/issue 経由)。
**S15_SAndT は C のみ・S14_MaximalI は H のみ** (2026-06-23 relane)、**S11/§16/§10 は driver (常駐なし)**。
(2) **新規 `axiom` 宣言は abort+ユーザー承認**。
(3) issue base: **B=1000 / H=2000 / C=4000 / F=7000**。(4) `notes/bg/*`=F、`notes/peterfalvi/*`=B/H/C。
マージ順 = **F → B → H → C** (独立レーンゆえ順序は形式的)。
**(5) 起動時 main 同期 = `git merge main` (ユーザー方針 2026-06-22, 全 LAUNCH 統一)**:
各レーンはセッション開始時に **`git merge main`** (実 3-way、merge commit 可) で main 最新を取り込んでから
作業する。**旧 `git merge --ff-only main` は廃止** — 自前 commit が 1 つでもあると ff 不能で失敗し、レーンが
main に遅れ続ける (2026-06-22 実害: 全レーン 15-47 commits 遅れ → 古い文脈・2-dot 誤検出の原因)。
コンフリクトは自所有ファイルなら解決、他レーン由来なら notes/issue で hub へ。`lake update` は禁止のまま。

**🧭 方向性・cross-lane 判断は issue 起票 → hub 解決 (ユーザー方針 2026-06-22, 永続)**:
レーンが (a) **方向性に迷った**とき (どの sorry を攻めるか・route 選択・faithfulness 解釈の迷い等)、
または (b) **レーンをまたぐ判断**が要るとき (他レーン所有ファイルの signature 変更要望・所有境界の移動・
cross-lane gate・割当変更等) は、**独断で進めず／他レーンのファイルを触らず**、`bin/new-issue` で
**HUB 宛 issue を起票**する (title に "HUB:" を冠する、宛先と判断内容と選択肢を明記)。
**hub が解決する** (issue 4005 relane の前例; hub はユーザー裁可が要る構造判断はユーザーに上げる)。
- **hub 側の責務**: 各 tick の merge で **新規 HUB 宛 issue** (`issues/` 直下に "HUB:" タイトル or
  `4002/4005` 系の hub-ask) が入ったら、サマリで**別枠報告**し、hub が解決する (read-only 監査 +
  必要ならユーザーへ AskUserQuestion)。黙って merge し続けない。
- これは [[cross-lane-sync-via-notes]] (lane↔lane の軽い sync は notes 追記) の**上位版** = 判断を要する
  ものは issue 化して hub に集約。軽微な signature 不足通知は従来どおり notes でよい。

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

> **⛔ 問題発生時はループ停止（ユーザー方針 2026-06-22, 永続）**: 下記のいずれかが起きたら、
> 進行中マージを `git merge --abort`（**冒頭ガード = 他マージ進行中の場合を除く**）し、
> **`CronList` で監視 cron の id を確認 → `CronDelete` でその場で停止** + 問題内容を明示報告し、
> **以降のレーン処理・次 tick を行わない**（ユーザーが解消・再開指示するまで待つ）。黙って次 tick で
> 同じ問題を繰り返さない。**問題 = ** build 失敗 / 内容コンフリクト（AxiomsCheck.lean・OddOrder.lean
> の独立追記**以外**）/ sorry regression（証明済→sorry）/ 新規 `axiom` / push 失敗 / 想定外の git 状態
> / **レーン範囲逸脱（下記 step 1.5 = 自所有外の Pf/BG S-ファイルを編集; ユーザー方針 2026-06-22）**。
> **非問題（通常継続）= ** 「変化なし」/ 新 decl の faithful scaffold sorry 増 / 独立追記コンフリクトの両保持解決
> / 共有ファイル編集（AxiomsCheck.lean 追記・OddOrder.lean import・`OddOrder/GroupTheory/**` 共有 infra・notes・issues）。
>
> **♻ 問題解決後はループ自動再開（ユーザー方針 2026-06-23, 永続）**: 上記 ⛔ で停止した監視ループは、
> **問題が解決したら必ず再開する**。具体的には: (a) 停止した問題（build 失敗 / コンフリクト / sorry
> regression / 新規 axiom / push 失敗 / 想定外 git 状態 / レーン範囲逸脱）が、**ユーザーの指示か hub の
> 修正で解消したことを確認したら**、(b) **監視 cron を `CronCreate` で再作成し**（停止時に `CronDelete`
> したものを復活）、(c) 通常の tick に復帰する。「停止しっぱなし」にしない。再開時はサマリに
> 「監視ループ再開（cron id <new-id>）」を 1 行記録する。**この stop→resolve→resume サイクルが監視ループの
> 正規ライフサイクル**であり、停止は一時退避でしかない。

> **🔒 レーン所有マップ（step 1.5 範囲逸脱チェック用、2026-06-22 frontier-cluster relane）**:
> | lane | 所有 .lean（これ以外の Pf/BG S-ファイル編集 = 逸脱→停止） |
> |---|---|
> | **F** (lane-f) | `OddOrder/BG/**`（BG 全体）+ `OddOrder/FeitThompson.lean` |
> | **B** (lane-b) | `OddOrder/Peterfalvi/S0[3-9]*` + `S10*` + `S12*`（Pf char API + §12 + cd assembly; **S11/S13 除く**, 2026-06-23 S13 を H 移譲） |
> | **H** (lane-h) | `OddOrder/Peterfalvi/S13*` (active) + `S14_MaximalI*` (driver)（type III/IV char-grid + type I driver; 2026-06-23 S13 受領, S15 を C 移譲） |
> | **C** (lane-c) | `OddOrder/Peterfalvi/S15*` (S&T, consumer) **+ POLE-1 carrier (2026-06-23 relane #3, issue 4008)**: `S14_TypePComplement.lean` + `FeitThompson.lean` の **tp 系 def** (`Section16TypePStructure`/`section16TypePStructure_*`/`Section16Inputs` tp) |
> | **共有（全 lane 可）** | `OddOrder/AxiomsCheck.lean` / `OddOrder.lean` / `OddOrder/GroupTheory/**` / **`OddOrder/FeitThompson.lean`** (def 単位 F=mp+Prop16.1 / B=cd / C=tp) / `notes/**` / `issues/**` |

1. 各レーンの未マージ確認: `git log --oneline main..<branch>`。
   **全レーン 0 なら「変化なし」1行報告で即終了**（build を走らせない）。
1.5. **レーン範囲逸脱チェック（ユーザー方針 2026-06-22, 永続）**: 未マージがあるレーンについて、
   **マージ前**に**そのレーンが実際に変更したファイル**を取得し、上記 🔒 所有マップに照らす。
   **⚠ 必ず 3-dot `main...<branch>`（merge-base からの branch 側差分）を使う** — 2-dot `main..<branch>`
   は端点差分で「レーンが main に遅れている分（他レーンの merge で main 側だけ進んだ S05/S06/S11 等）」を
   **誤検出**する（line 192 の罠と同根; 2026-06-22 実害 = lane-f/b が 2-dot で false-positive 逸脱判定）。
   **自所有でも共有でもない `.lean`（典型: 他レーンの Pf/BG S-ファイル）を含むなら範囲逸脱** → そのレーンは
   **マージせず（trial merge も開始しない）**、⛔ に従いループ停止（abort 不要 = まだ merge していない、
   `CronDelete` + 報告 + 以降の tick を行わない）。報告には逸脱ファイル名 + lane + 所有者を明記。例 (lane=$b):
   ```
   owned_re='…'   # 🔒 マップから (F=^OddOrder/BG/|^OddOrder/FeitThompson; B=^OddOrder/Peterfalvi/S(0[3-9]|10|12); H=^OddOrder/Peterfalvi/S(13|14_MaximalI); C=^OddOrder/Peterfalvi/S15|^OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement)
   shared_re='^OddOrder/AxiomsCheck\.lean$|^OddOrder\.lean$|^OddOrder/GroupTheory/|^OddOrder/FeitThompson'  # FeitThompson は F/B/C 共有 (def 単位協調)
   git diff --name-only main...$b -- '*.lean' | grep -vE "$owned_re" | grep -vE "$shared_re" | grep . && echo "範囲逸脱 → STOP"
   ```
   逸脱なし（空）→ step 2 へ。共有ファイル・notes・issues のみの差分は逸脱でない。
2. **F → B → H → C の順**で（独立レーンゆえ順序は形式的、上流→下流の自然順）、未マージがあれば自動合流:
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
  **step 1.5 の範囲逸脱チェックも同じ罠**: マージ前の「レーンが変更したファイル」は必ず 3-dot
  `git diff --name-only main...<branch>`（merge-base からの branch 側）で取る（2-dot だと遅れている分を誤検出）。
- **`axiom` 判定 grep は必ず `.lean` に scope する**: `git diff --cached | grep '^\+\s*axiom '` は
  **issue/notes の markdown 中の散文（"axiom footprint = …" 等）を誤検出**する（2026-06-22 実害）。
  正しくは `git diff --cached -- '*.lean' | grep -E '^\+axiom [A-Za-z_]+ *[:({]'`（行頭 `axiom <ident>` の
  実宣言のみ; staged が markdown のみなら空）。sorry +/- 判定も同様に `-- '*.lean'` scope。
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

- **2026-06-23 (続⁵〜続¹⁴, セッション総括) — 監視継続 + 実 sorry 130→125 + HUB issue 2 件解決 + worktree 同期**:
  単一監視セッションで複数 tick を回し、全レーンが活発に前進。cron = `cf031d2e` (`4,29,54 * * * *`, stop-on-problem)。
  main HEAD = `c96ef7ba`。**実 sorry 130→125** (全 tick build 3881 green / AxiomsCheck OK / 新規 axiom 0 / 範囲逸脱 0):
  - **F**: BG **Cor 14.12 全 conjunct 完成** (sorry-free + axiom-clean)。conjunct 1 (IsTypeF H) / 2 (U≤M_σ(H)) /
    3 (M⊓H=U⊔K) / 4 (¬(N_H(U)≤M)) + defUK (⁅U,K⁆=U) + kappa_conj_smul + Thm A(4)/A(5) を S16→S14 移設。
    次 frontier = Thm C conjunct 2 (matched (U,K) を Cor 14.12 cite 用に要する)。
  - **B**: §6 conjugate を Hypothesis 一般化 (issue 1010) → §10 conjugate-column + σ-grid orthonormality +
    **(5.5) for column μ_j → image family + (5.5) チェーン完成**。残 = (10.6.a) σ-endgame final step。
  - **H**: (12.9) honest assembly → **(8.17.a) exists_second_maximal discharge** (cover data + 5-type conj) →
    (12.9) residual = (8.12.a) のみ。**(12.12) combined FPF rep-theory core** (Case A/B 統合)。
  - **C**: Pf (9.7) Clifford engine steps 1-7 (chief-factor dim → orbit → dichotomy → Singer → (8.5.b) Ū-abelian
    → (9.7)(b) u∣(p^q-1)/(p-1) を FPF coprime に還元)。
  - **HUB issue 2 件解決** (cross-lane 調停が実証明前進に直結): **1010** (§6→Hypothesis 一般化, 案 1 採用, lane-b 実装) +
    **2015** (5-type HasPeterfalviType conj infra, lane-h が shared `MaximalSubgroupTypeConj.lean` に実装 → 同 infra で
    (8.17.a) discharge)。両 CLOSED。
  - ⚠ **サイズ flag 深刻化**: `S14_TypePCounting` **10037 行** (issue 0069)。lane-f が Cor 14.12 完成 = 自然な凍結境界 →
    **次の F-idle tick で hub が prefix-split 実施推奨**。他 S12 4440 (0076) / S11 2162 (0077)。
  - 🔸 **push 全保留**: `git push origin main` が auto-mode classifier に拒否され続け (default branch 直 push = PR
    review 迂回、ユーザー指示は監視のみ)。全 merge は **local main に commit 済** (HEAD c96ef7ba)。push はユーザー明示許可待ち。
  - **worktree 同期 (ユーザー指示)**: lane-f/h/c を `git merge --ff-only main` で main HEAD (c96ef7ba) に揃え + warmup
    build (各 3881 green)。lane-b は稼働中ゆえ未変更。
- **2026-06-22 (続⁴) — 監視再開 + 4 レーン全合流 (5 merge) + cron 再作成**: ユーザー「各レーンを監視します」で再開。前 cron は session 変化で消滅 (`CronList` 空) → 新 cron **`cf031d2e`** (`4,29,54 * * * *`, stop-on-problem prompt 入り) 再作成。全レーン範囲逸脱なし (3-dot 確認)、build 各 3881 green / AxiomsCheck OK / 新規 axiom 0。**実 sorry 130→128** (lane-f が -2):
  - **lane-f** (2 merge): `8c98a1e9` BG Cor 14.12 conjunct 1 = `IsTypeF H` proven (notMGH + msigma_inf_partner_eq_kstar + defMsMstar kernel, 実 sorry -2) → セッション中追加バッチ `7eb88d6c` Thm A(4)/A(5) centralizer lemmas 再配置 S16→S14 (105 行純粋移動)。
  - **lane-b** (`a5a2b1ae`): Pf (5.8) σ-level full-column endgame (Fourier 復元+σ-wrapper) + (10.6.a) reduction (ζ^τ₁⊥ζ̄^τ₁ / ⊥μ_k^τ₁)。sorry 不変。
  - **lane-h** (`e52187d1`): Pf (12.12) Case-A core = faithful 1-dim ⟹ cyclic ∧ e∣p-1 → (12.12) ungated rep-theory 2 core 完成 (Case A+B)。sorry 不変。
  - **lane-c** (`ad48a7de`): Pf (9.7) Clifford engine steps 1-2 (chief-factor dim |H̄|=p^q + orbit-span)。sorry 不変。
  - ⚠ サイズ flag (>1500, 全 active frontier、分割 issue 既起票): S14_TypePCounting **9395** (0069) / S12_MaximalIII_IV_V 3830 (0076) / S11_MaximalII_III_IV 1641 (0077)。
  - ⚠ **push 保留**: `git push origin main` が auto-mode classifier に拒否 (default branch 直 push = PR review 迂回、ユーザー指示は監視のみ)。merge は local main に commit 済 (HEAD `7eb88d6c`)。push はユーザー明示許可待ち。
  - HUB 宛 issue: `4002-hub-feedback-lane-allocation` は既出 (lane-c starve diagnosis) で issue 4005 relane が substantive response 済 ⟹ 新規 ask なし。
- **📌 レーン範囲逸脱 = ループ停止ルール追加 (ユーザー方針 2026-06-22, 永続)**: 各レーンが**自所有外の Pf/BG S-ファイルを編集**したら ⛔ stop-on-problem に従いループ停止 (CronDelete + 報告 + 待機)。検出 = step 1.5 (マージ前に **3-dot** `git diff --name-only main...<branch>` を 🔒 所有マップに照合; 2-dot は遅れ分を誤検出)。共有ファイル (AxiomsCheck.lean 追記 / OddOrder.lean import / GroupTheory/** / notes / issues) は逸脱でない。cron prompt にも内蔵。
- **📌 lane-c を §11 に再配置 (frontier-cluster relane, ユーザー裁可 2026-06-22, issue 4005)**: §16 監査で「starve は lane-c (§16 終点 consumer) のみ、lane-h 領域に ~16 独立 leaf」と判明 → lane-c を §16 から **Pf §11 (S11_MaximalII_III_IV, Wielandt §9 / Clifford 9.6-9.10)** へ。**S11 を H→C 移譲**、H は §14_MaximalI+§15 に集中、§16/§10 は driver 化 (常駐させず上流 landing 時に機会的 close)。レーン表・取り決め更新済。各レーン LAUNCH.md も更新 (git-excluded)。次 tick 以降この割当で運用。
- **📌 標準監視ペース (定期取り込み) = 15 分（恒久、ユーザー指示 2026-06-23 で 25→20→15 分に更新）**: cron 式 **`8,23,38,53 * * * *`**（:08/:23/:38/:53、:00・:30 + lane 自己復帰の /5 マークを回避）を**標準合流ペースとして恒久化**。ユーザーが各レーンを稼働 → 本ペースで監視・自動合流する。⚠ **cron 自体は本環境で session-scoped**（`durable: true` を渡しても runtime は session-only と報告; [[cron-dies-on-model-switch]]）→ **ペースの正本はこの行**。新セッション開始時・`/model` 切替後は `CronList` 確認の上、消えていれば同式・同 prompt で**即再作成**する（prompt は「各イテレーションの手順」を要約したもの、本ファイルが authority）。7 日 auto-expire 後も同様に再作成。
  - **lane 自己復帰 timer = だいたい 5 分（恒久、ユーザー指示 2026-06-23）**: lane が hub に判断を移譲して停止したときの resume-monitor cron は **5 分間隔** (`2-59/5 * * * *` = :02/:07/…/:57、:00・:30 回避)。hub の解決を素早く拾って自動再開する。正本 = [`lane_self_resume.md`](lane_self_resume.md)。
- **2026-06-22 (続³) — 問題時ループ停止ルール化 + cron `24df1fb4` 再作成**: ユーザー「問題が起きたらループ止めて・永続化」→「各イテレーションの手順」冒頭に ⛔ banner 追加（commit `13ed2a87`）+ cron prompt に内蔵。旧 `b9df9002` を CronDelete → 新 cron **`24df1fb4`**（同式・stop-on-problem prompt 入り）。
- **2026-06-22 (続²) — tick: lane-b/c 合流**: lane-b (1, merge `c6c7de1b`): s05 norm-2 σ-coeff bounds (Pf (10.5) endgame) + §6 DRY。lane-c (2, merge `15c014f6`): s16 (14.6) caseB_for_S + (14.11) K_eq_V index-pq half close。**実 sorry 131→129**, build 3881 green / AxiomsCheck OK / 新規 axiom 0, push 済 (`13ed2a87`)。⚠ サイズ flag: S16_NonExistenceG 3394 行（issue 0072 既起票）。
- **2026-06-22 (続) — 25 分 cron 再作成**: 新 cron `b9df9002`（→ 続³ で `24df1fb4` に置換）。当初 4 レーンは全合流済み・worktree main ff 同期、実 sorry 131。
- **2026-06-22 — 監視再開 + 4 レーン backlog 合流 + cron 再作成 + `coq/` submodule 追加**: ユーザー指示で
  監視再開。前 cron `e3dcf75f` は session 変化で消滅 → 新 cron `8e80cc9d` (`4,29,54 * * * *` = 25分間隔,
  session-only, push なし, 7日 auto-expire) 再作成。**4 レーン全合流** (F→B→H→C, build 各 3881 jobs green /
  AxiomsCheck OK / 新規 axiom 0, 実 sorry **134→133**):
  - **lane-f** (3, merge `5566f34f`): BG Thm 15.7 `fitting_not_ti_cases` close — type-F conjunct (c) を
    印刷版 `M'=F(M)` でなく faithful な `M'≤F(M)` に弱め sorry-free+axiom-clean (issue 7007; MathComp
    `nonTI_Fitting_structure` 交差検証)。sorry -1。
  - **lane-b** (1 実質, merge `b7f9a9eb`): Pf (10.5) ψ-vanish precursor (ψ が V 上で消える, issue 1007)。
  - **lane-h** (5, merge `491cc249`): Pf §11 (9.4) chief-factor kernel `exists_chiefFactor_kernel`
    (Maschke+Wielandt) → `exists_chiefFactorData` assembled (残=elementary-abelian seed) + `eq_top_of_forall_sylow_le`
    (Sylow 生成補題)。**import 帯の独立追記衝突を union 解決** (main: MaximalSubgroupTypeConj/AInvariantPiSubgroups +
    lane-h: OperatorMaschke)。
  - **lane-c** (1 実質, merge `648740b9`): Pf §16 MHypothesis carrier de-opacify (e_eq_index + (14.11.2/.3) bound)。
  - **⚠ サイズ flag** (>1500, 全て active frontier、分割 issue 0068-0075 既起票・凍結境界待ち、新規起票なし):
    S15_MF 7955 / S16_NonExistenceG 3265 / S12_MaximalIII_IV_V 3258 / S16_MainResults 2124。
  - **`coq/` submodule 追加** (`a69da089`, main 直下): [math-comp/odd-order](https://github.com/math-comp/odd-order)
    を教科書の行間補完参照用に取込 (CeCILL-B 公開, pin master 6afa795b; `notes/meta/coq_odd_order_reference.md`)。
    BG §N / Pf §N の原文を読む際に `coq/theories/{BG,PF}sectionN.v` のコメントを併読。レーンは coq/ を非編集ゆえ合流に影響なし。

- **2026-06-21 (後刻) — 4-lane 再編 (ユーザー裁可): FT frontier を大セグメント分割 + lane-c 新設**:
  ユーザー問「もっと並列化できるか (大きな分割・signature-first で衝突回避)」を受け hub が FT 構造を実地調査。
  判明: (1) FT spine は深い線形チェーン (BG §14→16 → Pf §10→16)、(2) char API (Pf §3-9) は完成済 (S04-S08
  全 0 sorry, (6.8) capstone complete)、(3) FT frontier 102 sorry = BG §14-16(18) + Pf §10-13(34) + Pf §14-16(50)。
  → ユーザー選択 = **4 レーン (Pf §14-16 を §15↔§16 で分割)**。F=BG §14-16 / B=Pf §10-13 / H=Pf §14-15 /
  **C=Pf §16+POLE-2 (新設)**。§15→§16 cut は clean (S16 が S15 を named cite、調査済)。**新 worktree
  `/home/ywr/odd-order-lane-c` 作成** (branch lane-c @ main `8da2766c`、lake/references symlink + olean warm-start、
  build 3881 green 確認)。LAUNCH.md: lane-c 新規 + lane-b/h に再編ブロック prepend (lane-f 不変)。issue base
  C=4000。handoff: H の §11 (9.3) → B、H の §16 → C。**cron は 4 レーン (F→B→H→C) で要再作成**
  (ユーザーが lane-c セッションを起動したら稼働開始)。
- **2026-06-21 — 監視再開 + 固定 25分 cron (ユーザー要望「25分おきで」) + dead-merge 復旧**:
  ユーザー指示で監視再開。**動的 15-30 分 (2026-06-18) を固定 25 分間隔に上書き**。cron job
  `e3dcf75f` (`4,29,54 * * * *` = 25分間隔 + :54→:04 の 10分 wrap、session-only、push なし、7日
  auto-expire)。/model 切替で消えるのは従来同様 ([[cron-dies-on-model-switch]])。
  - **開始時に前セッションの dead-merge を復旧**: `.git/MERGE_HEAD` = `c5fc73a5` (lane-f の**古い**状態、
    現 lane-f HEAD は 8 commits 先行) の stale な mid-merge が残存 (コンフリクト解決・staged 済だが
    未 commit)。コンフリクトマーカー残存なしを確認 → 混在していた未ステージ issue doc 変更
    (`2013-s1317-...md`、既コミット作業の trailing 記録) を退避 → `git merge --abort` で
    クリーン main へ → issue doc を standalone commit (`040fae9d`) → lane-f を**現 HEAD から fresh
    full merge** (古い MERGE_HEAD でなく) で S14+S15+S16 を一括取込。
  - **4 レーン backlog 合流** (F→B→H、build 各 3872/3872/3876/3876 jobs green / AxiomsCheck OK /
    新 axiom 0、実 sorry **137→135**):
    - **lane-f** (4 合流): BG Thm A faithful monolith complete (A(2)-(7) + 11-conjunct assembly,
      issue 8017 CLOSED) + Cor 15.3(a)/de-axiom A(8) FittingIsTI (issue 8016 CLOSED) + Prop 14.2(e)
      core + C_M(M_σ)=κ(M)'-group。
    - **lane-b** (1 合流): Pf §12 (10.3) δ_j-independence 完成 + (10.2)/(10.3) producer materialize
      + (10.5) support half `Supp(α_ij)⊆A_0(M)` (dade0-free)。sorry net -2。
    - **lane-h** (1 合流): **Wielandt (9.1) 群論層 完全完成** — 新 leaf 4 本 (CoprimeFixedPoints /
      MinimalInvariantNormal / WielandtElabBridge[OddOrder root 配線] / WielandtAssembly)、全 sorry-free。
      残 = (†) module wiring (`wielandt_fixedPoint_frobenius` CoprimeAction:156)、消費側 Pf §11 未配線。
  - **⚠ サイズ flag**: `S12_MaximalIII_IV_V.lean` 1847 行 (>1500) — lane-b の active frontier
    ((10.x) Dade 加筆中) ゆえ分割は凍結境界待ちで**起票保留**。なお S14 (8525)/S15 (7788) 等の巨大
    frontier が筆頭で、分割 issue 0068-0075 が既に滞留。
- **2026-06-18 (最新⁴) — 監視間隔を動的化 (15-30分、ユーザー要望「うざいから動的に」)**: 固定 15分
  recurring cron を廃止し、**活動量に応じた動的間隔の自己再スケジュール式**に変更。各 tick の末尾で
  次回をスケジュール: **合流あり→15分後 / 変化なし(or 全 skip)→30分後**。実装 = one-shot cron
  (`recurring:false`) を `date -d '+N minutes'` で now+N に作成し、プロンプト末尾に「同一プロンプトで
  次 one-shot を作る」自己再スケジュール step を埋め込む (チェーンが自走)。⚠ チェーンが切れると停止する
  (one-shot は recurring と違い自動継続しない) ので、tick で再スケジュールに失敗したら手動で再作成。
  /model 切替で消えるのは従来同様。push なしは不変。
- **2026-06-18 (最新³) — lane-g 退役 → BG を F に集約 (ユーザー裁可)**: レーン分担が「B,H=Peterfalvi /
  F,G=BG」に整理された後、F↔G の BG 内分割 (G=§16 main results / F=§14+POLE-1 構造) が
  ハンドシェイク待ち (issue 7006 の enrich を G が、producer discharge を F が担当) で **3h 停滞**して
  いたため、ユーザー裁可で **lane-g を退役し BG 全域を F に集約**。手順: (1) G 最終 commit `f492e046`
  (forward-half `kappa_join_kstar_le_pair_inf` 削除、lane-f の `typeP_pair_inf_eq` が supersede) を合流
  (merge `0c2470fd`, build 緑 3860 jobs / AxiomsCheck OK / 実 sorry 140 不変)、(2) `git worktree remove`
  + `git branch -d lane-g` (全成果 main 合流済を確認の上)。**F が BG §16 option-1 チェーンを端から端まで
  単独で回せる** (②`Section16MaximalPair` enrich + dichotomy clause 復活 → ③`section16TypePStructure`
  producer discharge)。issue 7006 (旧 lane-g/hub) は F に移管、8000 番 issue も F が継承。lane table +
  F LAUNCH.md REASSIGN #3 更新済。残レーン = **B + F + H** の 3 体制。cron は session-only ゆえ要再作成
  (B/F/H、push なし)。
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
