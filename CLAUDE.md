# odd-order — エージェント向け指示書

> このファイルは **CLAUDE.md** が正本. `AGENTS.md` は CLAUDE.md への symlink (Claude Code / codex 共通).

このリポジトリ (`odd-order`) は **Feit-Thompson 定理 (奇数位数定理) の Lean 4 完全形式化**を AI エージェント駆動で長期的に進めるプロジェクト。詳細な計画とチェックリストは [ROADMAP.md](ROADMAP.md) を参照。

## スコープ: 3 冊を全部形式化する

1. **Isaacs**, _Finite Group Theory_ (AMS GSM 92, 2008) — 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, F\*)
2. **Bender–Glauberman**, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994) — FT 局所解析 + 最終矛盾
3. **Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000) — FT 指標理論

PDF と Nougat 抽出 Markdown (`.mmd`) は `references/` 配下 (別 private リポ、本リポでは gitignore)。教科書本文を読む必要があるときは PDF を直接読まず、まず該当の `.mmd` を grep / Read してトークン効率を上げる。

**Coq 形式化の併読 (`coq/` submodule)**: [math-comp/odd-order](https://github.com/math-comp/odd-order) (Gonthier et al. の Coq/mathcomp FT 完全形式化, CeCILL-B, 公開) を `coq/` に submodule として取り込んでいる。各 `.v` の**コメントが教科書 (BG / Peterfalvi) の行間を埋めている**。**BG §N / Peterfalvi §N の原文 (`.mmd`/PDF) を読むタイミングで、対応する `coq/theories/{BG,PF}sectionN.v` のコメントを併読する** (ファイル名が教科書構成と 1:1 対応; 対応表・grep レシピ・コメント規約は [`notes/meta/coq_odd_order_reference.md`](notes/meta/coq_odd_order_reference.md))。形式化対象は 3 冊のまま; Coq は**行間補完の参照専用**で Lean に直訳するソースではない (証明戦略のヒント・前提の所在確認に使う)。Coq ツールチェインは不要 (`.v` を Read/grep するだけ)。fresh clone では `git submodule update --init coq` で取得。

## 進捗の測り方 — FT への実質的証明の積み上げ (sorry 数ではない)

このプロジェクトの目的は **Feit–Thompson 定理の honest な証明を積み上げること**。**短期的に `sorry` の数を減らすことは目的でも指標でもない。** 進捗は「honest な FT 証明がいずれ推移的に必要とする本物の数学を前進させたか」で測る。

- **sorry カウントで進捗を測らない (両方向で誤る)**:
  - hard content を未充足の仮説や free field (opaque な構造フィールド) に hoist すれば、何も証明せずに `sorry` は消える。「sorry-free」「AxiomsCheck OK」は doneness を意味しない。doneness は **仮説・carrier の構成可能性**で判定する。
  - 逆に、本物の上流前提を「上の carrier が今は free field で bypass しているから、閉じても `feitThompson` の sorry は今は減らない」と評価して deprioritize / hedge するのも**同じ誤り**。それは「上に scaffold が何枚あるか」を測っているだけで、その仕事が本物の必要な数学かどうかとは無関係。**この種の "FT-orphaned"・"閉じても sorry 減らない" という言い回しは使わない** (誤解を招く自家製ジャーゴン; 本物の prerequisite を「孤児・不要」と誤読させる)。
- **判定基準 (これが本当の進捗)**: opaque な carrier / posited data を実際に**構成**したか、free field・仮説を**実証明に置換**したか、spine がいずれ cite すべき本物の定理を**証明**したか。満たせば、その commit が headline の sorry を今減らすかは問わない。
- assigned な honest-architecture prerequisite は、今 FT critical path から外れて見えても hedge せず淡々と完遂する。「deferred-payoff (報酬が後払い) だから」「今 consumer 0 だから」は deprioritize の理由にならない。
- **「quick win / shallow entry / 難易度」は着手判断の基準でない (ユーザー 2026-06-30)**。各レーンは**その目的 (= 担当クラスタの FT 経路を閉じる) にかなう work** を、難しくても・clean な近道が無くても・1 iteration で landing しなくても**正面から進める**。「quick win が無い」「shallow entry が無い」「deep char で多反復」は**手を止めて flag/ask する理由にならない**(調査偏重に逃げるのも同断)。frontier が deep なら deep なまま engage し、本物の数学 (norm estimate・coherence・char body) を実際に**証明**する。止めてよいのは「想定違反 (unsound carrier・新 axiom・signature 無断変更)」「真に判断を要する設計分岐」のみ ([[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]])。
  - **同様に「gated かどうか・token/session コスト・infra 規模・payoff の遠さ」も一切の着手/継続判断基準でない (ユーザー 2026-07-06、本規約からの推論を明示要求)**。複数 downstream を unblock する genuine な**未形式化 prerequisite** (例: mathcomp prime-TI residue API の port) は、**規模が大きく・多 session を要し・token を消費しても、方向性確認せず淡々と build する**。「~N session の major infra 投資だから ask/pause」「token 重いから確認」「de-opacify で headline sorry が減らないから」は**すべて誤り**。**「真に判断を要する設計分岐」= 相互排他的で不可逆な設計選択のみ** (どの carrier 設計を採るか等) を指し、**コスト・規模・難易度・gated・payoff の遠さは一切含まない**。判断は毎回**本規約から推論**し、規約が不完全/ミスリードなら**規約自体を訂正する** (本項がその実施例) ([[feedback-cost-scope-not-a-criterion]])。
- **FT 経路限定**は維持 (FT を閉じるのに無関係な「3 冊網羅」の残りは当面しない; 上記スコープは長期目標であり続けるが別フェーズ)。ただし「FT 経路の中で何を優先するか」も sorry 削減量でなく**実質的証明の積み上げ**で測る。
- **作業順序 = 上流優先 + 文書順タイブレーク** (全レーン共通の標準方針, ユーザー 2026-06-22)。各レーンは依存の**上流から**進める。着手可能な選択肢が複数あるときは、**教科書 (BG / Peterfalvi) 上で出現が早いもの**(番号の若い §/定理/補題) から着手する。対象は **FT 経路上のものに限る**(上記)。下流の gated endpoint を先回りで skeleton 化するのは上流が真に block されているときの保険に留め、基本は上流 prerequisite を先に埋める。正本 = [`notes/meta/ft_path_policy.md`](notes/meta/ft_path_policy.md) §0。
- **レーン内 frontier 選択は自律判断する — 聞きに来ない** (ユーザー裁定 2026-07-01, 正本 `ft_path_policy.md` §0 policy 5-6)。「次に何を触るか」は上流優先+文書順で一意に決まる → hub/ユーザーに frontier 選択で聞かない・報告して止まらない (停止は STOP 条件・真の設計分岐のみ)。**(A)** 自レーン最上流 sorry が他レーンに gated でも、**さらに上流の ungated な genuine math (未所有 shared infra を含む) に降りて実証明する** (gated endpoint は sorried-cite skeleton で前倒し)。**(B)** 未所有 leaf (`OddOrder/Algebra|GroupTheory/**`) の新設は consumer が他レーンでも in-scope (territorial なのは所有 file のみ)。**(C)** shared infra は **claim-before-build**: 着手前に検索 (既存を再構築しない) → 9000 番台 issue で claim → 全レーンは着手前に open 9000 issue を scan → hub が重複検出 ([[feedback-quick-win-not-a-criterion]] [[verify-port-state-by-number-not-coq-name]])。
- **hub は cross-lane の食い違い・レーン方針を自律裁定する — ユーザーに聞きに来ない** (ユーザー 2026-07-06)。レーンが frontier を自律判断するのと対称。hub は **(a) レーン間の診断の食い違い** (「X は repo に在るか」「どちらの grep/診断が正しいか」等) と **(b) レーン方針・cross-lane 設計判断** (carve-out 付与・ファイルの keep/delete・所有/優先順位・重複解消) を、**自ら必要な調査を行って** (code-level grep・Coq trace・subagent fan-out — 調査もユーザーに投げない) 裁定し、結果を issue/notes に記録する。**この種の裁定に AskUserQuestion を使わない** (「食い違いがある/方針が割れている」自体は escalation 理由でない — 調査して裁定せよ)。ユーザー escalation は narrow に予約: (i) 新 `axiom` 宣言、(ii) unsound carrier・signature 無断変更、(iii) build 破壊・sorry regression・想定外 git 状態 (= merge-safety STOP、halt+報告)、(iv) 既存規約+徹底調査を尽くしてなお真に underdetermined かつ不可逆・影響大の戦略選択 (稀)。判断は本規約から推論し、規約が不完全なら訂正する。正本 = `merge_monitor.md` 🧭 節 ([[hub-arbitrates-cross-lane-autonomously]])。
- **レーンの genuine output は役割逸脱時も無駄にしない — 軌道修正で保全する (ユーザー 2026-07-06)**。レーンが自律進行で**本物の成果** (実証明・実構成・sorry-free work) を出したが割当役割/territory を**はみ出した**場合、hub の対応は **trajectory 修正で成果を保全する**こと: 正しい file/leaf へ**移設** / **carve-out 付与** / **owner 再割当** / 下流**再配線**。**discard・revert・「作り直せ」ではない**。役割逸脱の是正は「どこに置くか・誰が持つか」の修正であって genuine な math の破棄でない (territorial ルールは coordination 保護のためで、成果を gate-keep するためでない)。**「軌道修正できれば十分」**。⚠ **これは保全でなく STOP の別カテゴリ**: unsound carrier・新 `axiom`・sorry regression (証明済→sorry)・signature 無断改変 は genuine problem ゆえ halt+報告 (そもそも保全すべき成果でない)。実例 (2026-07-06 lane b の役割逸脱を全て保全): `S07_Subcoherent` = carve-out / `mu2Grid` = S05→PrimeTIResidue 移設 / `PrimeTIResidue` 削除 = 撤回。[[hub-arbitrates-cross-lane-autonomously]] [[feedback-cite-sorried-lemmas-if-signature-correct]]

## やらないこと (重要)

- **leanblueprint は使わない** — TeX 依存グラフ方式は採用しない。教科書 (PDF/mmd) → Lean を直接書く。「blueprint を立てよう」「TeX で証明概略を…」等の提案は不可。
- **mathlib 本体への PR は当面しない** — 汎用補題 (Fitting, Hall, Frobenius 群, ZJ 等) も `OddOrder` namespace 配下に書く。理由は速度優先で手元で完結させたいから。将来の upstream は視野に入れるので、mathlib 互換のスタイル・命名は常に維持する。
- **Gorenstein 1968 _Finite Groups_ は形式化対象ではない**(2026-05-28 refinement)— 「使わない」のではなく「**全形式化はしない**」。形式化対象は上記 3 冊(Isaacs / BG / Peterfalvi)に限定し、Gorenstein は **BG の行間を埋めるためにのみ原文参照する**(`references/gorenstein/finite-groups.{pdf,mmd}`)。具体的には BG が "**G**, Thm X.Y.Z" として証明本体を省略する箇所(典型: BG App.A の A.2/A.3/A.4 が "follow the proof of **G** Thm 3.8.1 / §6.5" と書く部分)で Gorenstein 原文を読み Lean に書き起こす。**Gorenstein 本体の章節を独立に形式化することはしない**。BG 中の "**G**, Thm X.Y.Z" 引用は、まず Isaacs に対応定理があれば Isaacs に読み替え、Isaacs が欠く場合(典型: ZJ / p-stability 周り = **G** Ch.3 §8 / Ch.6 §5 / Ch.8 §2)のみ Gorenstein を参照。なお同名タイトルの Gorenstein "Classification of Finite Simple Groups I" (BAMS 1979) は教科書ではなくサーベイ論文で、別物・対象外。

## 開発規約

### ファイル粒度

**基準は mathlib のファイル粒度** (2026-06-05 方針化)。

- **1 ファイル = 1 つの数学的トピック** (定義+API、または 1 定理とその支持補題群)。行数や「1 節」単位そのものでなく**主題の結束**で分ける。`§` が複数の独立した定理クラスタを含むなら複数ファイルに割ってよい (むしろ割る)。
- **Isaacs: 1 章 = 1 ディレクトリ** (入口 `Main.lean`、例 `OddOrder/Isaacs/Ch01_Sylow/Main.lean`)。ディレクトリ内は topic 別ファイル。
- **BG / Peterfalvi**: 小さい節は 1 節 = 1 ファイルでよいが、大きい節は **topic-coherent な複数ファイル + hub** に分ける。例: `S09_Uniqueness.lean` (4440 行) を `S09_Theorem91` / `S09_Corollaries` / `S09_Lemma95` / hub `S09_Uniqueness` に分割 (下流は hub を import するだけで不変)。**active frontier を小さな leaf に残し、凍結クラスタを上流ファイルへ押し出して hub が束ねる**。
- **分割の粒度・形式も mathlib 準拠 (2026-07-09 明文化、ユーザー指示; 上限値は同日実測に基づき裁定)**:
  - **mathlib 実測 (2026-07-09、8191 files)**: 中央値 185 行 / p90 641 / p99 1274 / 最大 1602。`linter.style.longFile` linter が **1500 行を hard 上限**として強制 (超過は per-file の明示例外、現在 4 files のみ)。2000 行超はゼロ。
  - **本リポジトリの上限 = 2000 行** (ユーザー裁定 2026-07-09、mathlib の 1500 より緩め)。目安は mathlib と同じ **1 ファイル ≈ 300–1,500 行・1 トピック**で、**2000 行超は分割必須** (単一定理クラスタでも helper 層を切り出す)。意図的例外 (`AxiomsCheck.lean` 等の機械列挙 file) は per-file `set_option linter.style.longFile N` で明示。
  - **巨大節の解体はディレクトリ化を第一候補**: `<節名>.lean` を **pure re-export の hub** (mathlib の `Mathlib/Tactic.lean` 型 — import 行のみ) として残し、実体は `<節名>/<Topic>.lean` の topic leaves に置く。module 名が不変なので**下流 import は無変更**。⚠ pure re-export hub は mathlib では稀 (Tactic.lean のみ; mathlib 流は leaf 直 import + `deprecated_module` redirect) — 本リポジトリは「FT spine の直列依存で minimal-import の速度益なし + 並列レーン中の下流 import 書換回避」を理由に**意図的に逸脱**する。upstream 時は leaf 直 import に置換。
  - leaf の 2000 行超過は **flat な兄弟 prefix-split** (先頭クラスタを新 sibling module へ、元 file が import) で解消してよい (module 名不変・下流不変)。
  - **leaf 命名は mathlib 互換の記述的英語** (`TypePDuality`, `NormEstimates` 等)。`Part1`/`Part2` 等の無内容な名前は不可。
  - 機械分割の道具と手順 (preamble 再現・private public 化・sorry/宣言/namespace 文脈保存検証) は issue 0103 と `notes/meta/merge_monitor.md` を参照。
- **最小 import (mathlib の衛生)**: 各ファイルは必要な module だけ import する。一般には import DAG を浅くし full build 並列化 + fan-out 縮小に効く。**ただし FT の spine (§1→§16 が直列依存) のように深い base closure を共有するファイル群では推移閉包が不変ゆえ速度改善はほぼ無い** (2026-06-05 実測: S09 4分割を minimal-import 化しても full build 3580 jobs 不変)。よって本リポジトリでの minimal-import の価値は **DAG 衛生 + 可読性 + upstream 適性**が主で、速度ではない。**注意: `lake exe shake` は本リポジトリで誤判定が多い** (実使用中の import を removable と誤報する) ので鵜呑みにせず必ず build/grep で検証する。
- **`private` をファイル跨ぎで使わない**: 複数ファイルで使う補題は適切な namespace 付き public にする (mathlib は `private` を真に局所な helper に限定)。
- **計測事実 (2026-06-05)**: `lake build` はファイル単位で全再 elaboration するが、1 ファイルの再 elaboration は **import closure 読み込み固定費 (~5s) が支配的**で行数差は小さい (S09 4440 行 ≈5.5s、分割後 leaf 2544 行 ≈4.7s)。よって**ファイル分割の主目的は速度でなく minimal-import による DAG 衛生 + 可読性 + upstream 適性**。速度の主レバーは「**開発中は leaf build で回し、full build は commit 直前のみ**」。過度な細分化 (<~300 行が乱立) は固定 ~5s/ファイルが効いて逆効果。詳細は [ROADMAP.md#ファイル粒度とトレーサビリティ](ROADMAP.md)。**ただし行数が elaboration を支配し始める例外もある** (2026-06-11 実測: S08 11.8k 行 ≈21s、S03f_Thm36 3.8k 行 ≈50s) — frontier ファイルがこの域に入ると編集ループを直撃する。
- **分割の owner と trigger (2026-06-11 メカニズム化)**: 上記原則は 2026-06-05〜06-11 の 6 日間に ~170 commits / +13k 行すり抜けられた (S08 5.5k→11.8k、S05 は制定後誕生で 4k 化)。文言でなく以下のメカニズムが正:
  - **lane (書き手) の trigger**: 教科書の**次の主結果番号**に着手するときは**新 leaf を切るのがデフォルト**。同一ファイル追記は「現に証明中の定理の helper」のみ。frontier ファイルが **1,500 行超**になったら停止して分割 (または hub に委任)。
  - **hub (合流側) の gate**: 合流 tick で 1,500 行超ファイルへの追記を検出 → ⚠ flag 報告 + 分割 issue 起票。**分割の実施 owner は hub** (lane の frontier と衝突しない凍結境界で prefix-split: 先頭 K 宣言を上流ファイルへ、残りが import する。前方参照は構文上不可能ゆえ任意の宣言境界で安全)。手順詳細 = [`notes/meta/merge_monitor.md`](notes/meta/merge_monitor.md)。

### トレーサビリティ (3 層)

各 Lean ファイルは「教科書のどこの形式化か」が一目で追える状態に:

1. **ファイル冒頭 `/-! # ... -/`** で本・章・ページ範囲を明示
2. **`section /- 1A: ラベル (pp. 1-10) -/ ... end`** で教科書の subsection 構造をミラー
3. **theorem の docstring 冒頭に `**Isaacs Thm 1.4** (慣用名)`** 形式の本での名前

定理名 (Lean 識別子) には番号を入れない (`thm_1_4` 等は不可)。**mathlib 互換のため記述的命名** (`sylowExistence`, `fittingSubgroup` 等)。本での番号は docstring 内のみ。詳細は [ROADMAP.md#ファイル粒度とトレーサビリティ](ROADMAP.md) 参照。

### namespace

階層: `OddOrder.Isaacs.Ch01`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04`。汎用補題は将来 `Subgroup.fitting` のように mathlib 階層へリネーム可能な形で書く。

### ラッパー方針

mathlib に直接対応がある定理の **薄いラッパー** (`theorem foo := mathlib_bar`、引数も型も同じ純粋なリネーム) は書かない。維持負担のみで価値が無いから (mathlib API 変更時の追従、同事実が 2 名で呼ばれて証明が分裂、将来 upstream するときどうせ消す)。

同じ原則は **本リポジトリ内の既存 theorem** にも適用する。たとえば BG/Peterfalvi で使うためだけに, 既存の `OddOrder.Isaacs.*` 定理を引数・型そのままで純粋リネームする wrapper は書かない。教科書間対応 (BG/Peterfalvi ↔ Isaacs) は section docstring または `notes/` の対応表に記録し、Lean 本体では既存 theorem を直接呼ぶ。

教科書名 ↔ mathlib 名 / repo 内 theorem 名の対応は **section 冒頭の docstring** または **`notes/` の対応表** で記録する。書く価値がある例外:

- **引数順 / convention 適応** — mathlib が `Disjoint M N` を明示引数で取るところを instance + positional で並べ替える等
- **仮定特殊化** — `[Finite G]` などで mathlib の汎用版を狭く取り直す
- **章内で 2 回以上呼ぶ慣用名** — Isaacs Thm 1.7 を `sylowExistence` として呼びたい等

詳細は [`notes/meta/lean_formalization_tips.md`](notes/meta/lean_formalization_tips.md) §2.7 参照。

### commit の区切り

作業の論理的な単位ごとに git commit を作る. 単位は **feature / subsection 粒度** — 主定理とそれを支える補助補題群をまとめて 1 コミット (定理 1 つ・証明ステップ 1 つごとには刻まない). ただし 1 セッション分を最後にまとめて 1 コミットで上げるのは避ける (下限と上限の両方を守る).

実務上は「後から単独で revert / cherry-pick / review したい最小の意味単位」を 1 commit とする。同じ主定理や同じ subsection frontier を支える小補題群はまとめる。別の主定理・別章節・独立リファクタ・運用ドキュメント更新は分ける。

- **主定理 + その helper 補題群 = 1 コミット** (例: Lemma 5.2 と支える ~10 helper で 1 つ). 中間ステップでは刻まない
- subsection / 独立 feature の境界で区切る (例: §5 の Lemma 5.2 と Thm 5.3 は別, BG §10 の各 Prop は機能単位でまとめる)
- ノート整備 / 対応表更新が独立な意味を持つなら → 単独コミット (Lean 変更と混ぜない)
- 同質なリファクタ (例: ラッパー削除 N 件) はまとめてよい, 異質な作業 (リファクタ + ノート + 新定理) は分ける
- まとめる場合, commit message 本文で各単位を明示
- 別ブランチ (worktree / 並列セッション) の取り込みは `--no-ff` merge → first-parent に lane = 大単位が残り, 内部の細かいコミットは詳細ビューに温存される

理由: feature 単位なら revert / cherry-pick / レビューが一貫した塊で効き, 「1 補題 = 1 コミット」のノイズを避けられる. 各コミットは build-green を維持.

## ノート・小ロードマップの管理

章節単位のミニロードマップ・調査結果・設計決定は `notes/` 配下:

### notes 更新頻度

`notes/` は handoff / 設計決定 / frontier 変更を残すための場所であり、細かい補題や micro-step ごとには更新しない。更新するのは原則として次のときに限る:

- 証明 frontier・依存関係・残り `sorry` の形が実質的に変わった
- 後続セッションが迷いそうな設計判断、API 対応、原文解釈を記録する必要がある
- 章節単位の handoff / ロードマップ更新として意味がある

小さな helper の追加や局所的なリファクタは、通常は commit message と Lean の docstring で十分。notes-only の微小更新を頻発させない。

```
notes/
├── isaacs/ch01_sylow.md       # 章単位
├── bg/s08_fitting.md          # 節単位
├── peterfalvi/s04_dade.md
└── meta/                       # 章節に紐づかない横断調査・設計決定
```

ROADMAP のチェックリストから対応する `notes/` にリンクして掘り下げる。

## Issue 管理

単発の作業項目 (1 つの sorry を埋める, 1 つの設計を決める, etc.) は `issues/` 配下のファイルベース issue で追跡する。GitHub Issues は使わない (local-first)。詳細は [`notes/meta/issue_management.md`](notes/meta/issue_management.md)。

- 採番 + scaffold: `bin/new-issue [--base N] <slug> "<title>"` → `issues/NNNN-<slug>.md` を作って `git add`。並行セッションは `--base`/`ODD_ISSUE_BASE` で採番レンジを分けて衝突回避 (hub/main=0、**lane 別に 1000 の倍数 base** — 現行 a=1000/b=2000/c=3000、shared-infra claim 専用=9000; 正本 = merge_monitor.md レーン表; 既定 0)
- 状態 = 配置ディレクトリが source of truth: `issues/` (open) / `issues/pending/` / `issues/closed/`
- 遷移は `git mv`. frontmatter に `status:` は持たない

## 並行作業 (worktree)

章 / 節を別エージェントセッションで並行進行させるときは `git worktree` を使う。詳細手順は [`notes/meta/worktree_setup.md`](notes/meta/worktree_setup.md)。

- **🔄 起動時 + 定期の main 同期 (最重要・全レーン必須, ユーザー方針 2026-06-22/06-23)**: worktree レーンの各セッションは
  **(1) 開始時にまず `git merge main`** (実 3-way; merge commit 可) で main 最新を取り込んでから作業に入る。
  **`git merge --ff-only main` は使わない** (自前 commit が 1 つでもあると ff 不能で失敗し、レーンが main に
  遅れ続ける)。**(2) 長く走るセッションは「次の leaf に着手する前」「commit する前」にも `git merge main` で
  再同期**する (開始時 1 回きりだと他レーンの合流で drift し、古い文脈・cite ずれ・2-dot 誤検出の原因になる)。
  **(3) 取り込んだら `git rev-list --count HEAD..main` が 0 を確認**。コンフリクトは自所有ファイルなら解決、
  他レーン由来なら notes/issue で hub へ。これは LAUNCH.md の「🔄 起動時 main 同期」ブロックの上位正本
  (LAUNCH.md は git-excluded ゆえ、常時ロードされる本規約が確実な拠り所)。
- worktree path = `/home/ywr/odd-order-<slug>` (sibling), branch 名も `<slug>` (現行 = 単文字レーン `a`/`b`/`c`; 正本 = [`notes/meta/ft_lane_reallocation_2026_06_28.md`](notes/meta/ft_lane_reallocation_2026_06_28.md))
- `.lake/packages` と `references` は main から **symlink で共有** (mathlib 6.5GB + 初回ビルド数分を節約)
- `.lake/build/` は worktree ごとに独立 (並行 `lake build` 安全)
- **`lake update` は worktree で走らせない** (共有 mathlib rev を壊す)
- forward axiom 経由で章をまたぐ並行作業は合流時の名前衝突に注意 ([`notes/meta/forward_dep_policy.md`](notes/meta/forward_dep_policy.md))
- 並行 worktree には **issue 採番レンジ**を割り当てる (`export ODD_ISSUE_BASE=N`、base は 1000 の倍数; hub/main=0、現行 a=1000/b=2000/c=3000、9000=shared-infra claim)。採番衝突を予防 ([`notes/meta/issue_management.md`](notes/meta/issue_management.md) 「並行セッションの採番レンジ」)
- **レーン再開プロンプト単体で `/loop` 自走に自動で入る (ユーザー 2026-06-17「loop が使えるタイミングは自動で使ってほしい」、2026-07-12 明文化)**。「Xレーンを再開します」等の再開・継続指示だけで、レーンは起動時 main 同期 → frontier 確認 (issue/notes) の後、明示の `/loop` 入力を待たず**自ら `/loop` self-pacing を起動して連続作業に入る** (外部ゲート無しの通常のレーン形式化作業が対象)。自走に入らない例外 = STOP 条件該当・真の設計分岐 pending・ユーザーの単発質問に答えるだけで完結する turn。⚠ 2026-06-18 凍結の旧「LAUNCH.md LOOP GATE」(ユーザー prompt 無しの投機自走) とは別物 — 再開プロンプトという明示 opt-in がある。
- **レーンの `/loop` self-pacing wakeup = 60s (最短固定、ユーザー 2026-07-06)**。各レーンが `/loop` で自走する (self-pacing、interval 無指定 → ScheduleWakeup dynamic mode) とき、次 iteration の wakeup は **必ず `delaySeconds: 60`** (runtime clamp 下限) にする。理由: レーンは actively 本物の数学を証明中ゆえ**即再開**が正しく、60s は prompt cache を warm に保つ (300s+ は cache miss)。**⚠ 間違えやすい典型ミス**: ScheduleWakeup の「idle polling default 1200–1800s」を active-work レーンに適用すること — それは**外部状態待ち polling 専用**で、証明を進めるレーンには不適 (無駄な待機で throughput 激減)。レーンが止まってよいのは STOP 条件 (unsound/新 axiom/想定外) と context 枯渇時のみ。context 枯渇なら subagent handoff or 停止+報告 (最小 iteration での compaction 待ち空転は誤り)。hub 監視 cron (**現行ユーザー指定 = 15分 `7,22,37,52` (2026-07-15)**。明示指定がない場合はモデル依存: Fable=30分 `13,43` / Opus=15分 `7,22,37,52`; 正本 = merge_monitor.md 冒頭) とは別物 (hub は合流ポーリングゆえ長間隔でよい)。正本 = [[feedback-loop-short-wakeup]]。

## 主要パス

| パス | 内容 |
|---|---|
| [ROADMAP.md](ROADMAP.md) | 長期計画、フェーズ、依存グラフ、章節チェックリスト |
| `OddOrder/` | Lean ソース本体 |
| `coq/` (submodule) | [math-comp/odd-order](https://github.com/math-comp/odd-order) — Coq/mathcomp FT 形式化。`.v` コメントで教科書の行間を併読 ([`notes/meta/coq_odd_order_reference.md`](notes/meta/coq_odd_order_reference.md)) |
| `notes/` | ミニロードマップ・調査メモ |
| `issues/` | ファイルベース issue (open は直下, `pending/` `closed/` で状態管理) |
| `bin/` | 雑用スクリプト (`new-issue` 等) |
| `references/` (gitignored) | PDF + Nougat 抽出 Markdown — 別 private リポ `odd-order-references` |
| `references/{isaacs,bg}/*.{pdf,mmd}` | 教科書原典と抽出物 (フラット) |
| `references/peterfalvi/pdf/*.pdf`, `references/peterfalvi/*.mmd` | Peterfalvi だけ章別 PDF を `pdf/` に集約 |
| `references/README.md` | Nougat セットアップ・抽出手順 (GPU マシン用) |

## ツールチェイン

- Lean: [`lean-toolchain`](lean-toolchain) (現状 `leanprover/lean4:v4.30.0-rc2`、2026-05-27 に v4.29.1 から bump; 手順 [`notes/meta/mathlib_rc2_migration.md`](notes/meta/mathlib_rc2_migration.md))
- mathlib: [`lakefile.toml`](lakefile.toml) の `[[require]]` 参照
- ビルド: `lake build OddOrder`
- mathlib キャッシュ: `lake exe cache get` (mathlib 更新時に再取得)

## mathlib カバレッジ

詳細は [`notes/meta/mathlib_coverage.md`](notes/meta/mathlib_coverage.md) に集約。概要: Sylow / `IsPGroup` / `IsSolvable` / `IsNilpotent` / Frattini / Transfer / Schur-Zassenhaus / 表現論・指標の基本は mathlib 既存。Fitting `F(G)` / `F*(G)` / 一般 π-Hall / Frobenius 群 / ZJ / Thompson subgroup `J(P)` / Dade isometry / Peterfalvi coherence は mathlib に無く、**本リポジトリ (`OddOrder/**`) で実装済み** (coverage doc は mathlib 欠落の記録であり残作業リストではない)。

## mathlib API 探索方針 (3 層運用)

mathlib lemma の名前 / 署名を調べるときは, 闇雲に `grep -rn` を叩かず以下の順:

1. **概念は明確で名前が未知** → **Web 検索** (`WebFetch https://leansearch.net/?q=<query>` / `WebSearch "mathlib4 <concept>"`). leansearch.net / moogle.ai が mathlib 専用のセマンティック検索. 候補名は必ず local で確認 (現行 pin = [`lean-toolchain`](lean-toolchain) との drift 注意)
2. **不慣れなモジュールの API 把握** → **該当ファイルを `Read` で通読**. 個別 grep を 3 回以上叩くなら通読の方が早い (例: `SemidirectProduct.lean`, `Nilpotent.lean`)
3. **名前細部 (namespace, 引数順) が不確か** → **自然名で書いて `lake build` のエラー任せ**. ~12 秒で決着

`grep -rn` は「使用例を本プロジェクト内で探す」 (Ch.1 等で類似 proof パターンの確認) には引き続き有用. mathlib 名前探索とは目的を分けて運用.
