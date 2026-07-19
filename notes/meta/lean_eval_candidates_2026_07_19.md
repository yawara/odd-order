# lean-eval 提出候補 — 実測棚卸し (2026-07-19)

> **この note の位置づけ**: [issue 0050](../../issues/0050-lean-eval-submission-candidates.md) の
> 候補表の**詳細版・正本**。2026-07-19 に 79 エージェントの fan-out (発掘 4 スライス + 既存 11 件の再測
> + lean-eval 側 recon → 候補 77 件を敵対的検証 → 68 件通過 / 4 件 reject) で作成した。
> 判定はすべて実測 (`grep` による実在確認 / `OddOrder/AxiomsCheck.lean` の
> `#assert_only_allowed_axioms` または `#print axioms` の直接実行 / mathlib 側 grep)。
>
> ⚠ **旧 0050 表 (2026-05-30 作成) のラベルは全て無効**。特に次の 3 点は事実誤認だった:
> Frobenius 核存在は repo に**不在** / Burnside 正規 p-補群は **mathlib 収録済** /
> Brauer–Fowler は repo に**不在** (Gorenstein 由来ゆえ恒久スコープ外)。
>
> 元データ: 本 note は生成物であり、再生成するときは同じ workflow を回すより
> **AxiomsCheck.lean の実測を優先**すること。

---

# lean-eval 現行仕様調査レポート (2026-07-19 時点)

## 0. 先行実績 (repo 側)

- `/home/ywr/odd-order/notes/meta/lean_eval_baer_suzuki.md` — Baer–Suzuki 提出メモ。**方針の要点 = self-contained 提出** (`import OddOrder` は却下。理由は依存閉包経由で未公開の FT 形式化構造が露出するため。`../baer_suzuki/` に必要最小コードを rebrand してコピー)。
- `/home/ywr/odd-order/issues/closed/0042-lean-eval-baer-suzuki-p-core.md` — 同 issue (2026-05-28 close)。
- 実際の受理状況 (`results/yawara.json` を確認):

| problem | 提出日 | model 表記 | issue |
|---|---|---|---|
| `baer_suzuki` | 2026-05-29 | Claude Opus 4.7 + GPT-5.5 (human-in-the-loop) | #118 |
| `feit_thompson` | 2026-07-16 | Codex 5.5/5.6, Claude Code (Opus 4.7 / 4.8 / Fable 5) | #828 |

`feit_thompson` は 2026-07-17 に @rishistyping (Stealth Model) も解いており、現在 solver 2 名。

---

## 1. `leanprover/lean-eval` — リポジトリ構成

```
LeanEval/            trusted な問題文 (topic フォルダ)
manifests/problems/  1 problem = 1 TOML (<id>.toml)
generated/           comparator workspace (CI が自動生成)
scripts/             生成・検証・採点ユーティリティ
PLAN.md              今後のキュレーション方針
```

**topic フォルダ (API 実測、21 件)**: Algebra, AlgebraicGeometry, Analysis, CategoryTheory, Combinatorics, ComplexAnalysis, ConvexGeometry, Dynamics, GameTheory, Geometry, GroupTheory, KnotTheory, LinearAlgebra, ModelTheory, NumberTheory, Physics, ProgramVerification, RepresentationTheory, Sandbox, Topology + `EasyProblems.lean`。

**workspace の構造** (`generated/<id>/`):

| 種別 | ファイル | 権限 |
|---|---|---|
| trusted (読み取り専用) | `Challenge.lean` (ベンチ文), `Solution.lean` (comparator への橋), `config.json`, `lakefile.toml` | solver は編集不可 |
| solver 所有 | `Submission.lean`, `Submission/Helpers.lean` ほか `Submission/` 配下 | ここに証明を書く |

採点は **comparator が受理するか否かのみ** (「a problem counts as solved iff comparator accepts」)。ローカル検証は `lake test` (`landrun` サンドボックス + `lean4export` + `comparator` の 3 ツールを駆動)。Mathlib は自由に使える。Mathlib に無い補助は submission workspace 内に同梱する。

manifest の実例 (`manifests/problems/baer_suzuki.toml`, 逐語):

```toml
id = "baer_suzuki"
title = "Baer–Suzuki theorem"
test = false
module = "LeanEval.GroupTheory.BaerSuzuki"
holes = ["baer_suzuki"]
submitter = "Kim Morrison"
notes = "... Introduces a small Defs/PCore.lean defining the p-core O_p(G) as the supremum of normal p-subgroups (Mathlib has no `pCore` operation)."
source = "..."
informal_solution = "..."
```

---

## 2. GroupTheory / RepresentationTheory の現行 problem 一覧と solved 状況

`LeanEval/GroupTheory/` (API 実測 16 ファイル + `Defs/{PCore,OddCore}.lean`)。status は lean-lang.org の per-problem ページで個別確認済み。

| problem id | 内容 | status |
|---|---|---|
| `baer_suzuki` | Baer–Suzuki (p-core 単元版) | **Solved** (7 名。@yawara が最初 2026-05-29) |
| `feit_thompson` | 奇数位数定理 | **Solved** (@yawara 2026-07-16、@rishistyping 2026-07-17) |
| `brauer_fowler` | \|G\| ≤ f(\|C_G(t)\|) | **Solved** (6 名) |
| `frobenius_kernel_isNormal` | Frobenius 核の正規性 | **Solved** (6 名) |
| `finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow` | Burnside p^a q^b | **Solved** (8 名) |
| `commProb_closed` | 交換確率の集合が閉 | **Solved** (2 名、2026-07-15) |
| `golod_shafarevich_inequality` | d(Q)² < 4r(Q) | **Solved** (4 名) |
| `boone_higman_embedding` | Boone–Higman 易方向 | **Solved** (5 名) |
| `boone_higman_simple` | Kuznetsov (有限表示単純群の語問題可解) | **Solved** (7 名) |
| **`glauberman_zStar`** | Glauberman Z*-定理 (孤立対合) | **未解決** (solver 0) |
| **`brauer_suzuki`** | 一般四元数 Sylow 2 ⇒ 唯一の対合が G/O(G) の中心 | **未解決** (solver 0) |
| **`gorenstein_walter`** | 二面体 Sylow 2 の単純群分類 (A₇ or PSL₂(q)) | **未解決** (solver 0) |
| **`schreier_conjecture`** | Out(S) 可解 | **未解決** (solver 0、CFSG 依存) |
| **`five_transitive_card_classification`** | 5-可移群の位数分類 | **未解決** (solver 0、CFSG 依存) |
| **`higman_infinite_simple`** | 無限有限表示単純群の存在 | **未解決** |
| **`novikov_unsolvable`** | 語問題非可解な有限表示群 | **未解決** |

RepresentationTheory (7 ファイル): `brauer_character_in_cyclotomic` **Solved** (10 名)、`frobenius_group_determinant` **Solved** (5 名)、**`brauer_splitting_field` 未解決** (ℚ(ζₙ) 上への表現の降下)。`compact_group_semisimple` / `schur_weyl` / `e8_irrep_tensor_square_decomp` / `g2_...` / `m23_...` は個別未確認。

⚠ 全 problem 数は約 200 (manifests 実測)。全リストの逐語取得は fetch が途中で切れる (ページの生 HTML が 10MB 超) ため、本レポートでは GroupTheory / RepresentationTheory のみ API 実測ベースで確定させた。他 topic の網羅リストが要るなら `https://api.github.com/repos/leanprover/lean-eval/contents/manifests/problems` を per_page 付きで 2 ページに分けて取ること (1 回の要約 fetch では後半が捏造される事故を実際に踏んだ)。

---

## 3. `leanprover/lean-eval-submissions` — 提出フロー (解答側)

- 提出 = **リポジトリに「Submit benchmark solution」issue を立てる**。
- 提出物には **problem id と一致する名前の `lakefile.toml`** と **`Submission.lean`** が必要。
- ソースは 3 通り可: (a) 生成済み workspace、(b) `leanprover/lean-eval` の fork で `generated/` 配下を変更したもの、(c) **public gist**。
- **評価・公開されるのは `Submission.lean` と `Submission/` 配下のみ**。
- private repo から出す場合は `lean-eval-bot` GitHub App をインストールして CI にアクセス権を与える。
- 結果は `results/<github-login>.json` に記録され、**sticky** (一度解けば以後の提出が再現しなくても消えない)。現在 30 アカウント分の結果ファイルが存在 (`yawara.json` を含む)。
- リーダーボードは lean-lang.org/eval が `results/` をレンダリングしたもの。Lean FRO 自身はモデルを走らせない (全て外部提出)。

---

## 4. 新規 problem の「提案」— 可能。手順は確立している

README の "Adding a new problem" が正式経路。**外部コントリビュータの problem 追加 PR は実際にマージされている** (例: PR #430/#431/#432 by @CoolRmal = Analysis の 3 問、いずれも merged。PR #140 by @alreadydone = Mostow rigidity は未マージ)。

手順:

1. `lake exe cache get && lake build` で依存を用意。
2. `LeanEval/<Topic>/` 配下のモジュールに `@[eval_problem]` を付けた定理を追加:
   ```lean
   @[eval_problem]
   theorem my_new_problem : ... := by
     sorry
   ```
3. `manifests/problems/<id>.toml` を作る:
   ```toml
   id = "my_new_problem"
   title = "My new problem"
   test = false
   module = "LeanEval.SomeModule"
   holes = ["my_new_problem"]
   submitter = "Your Name"
   notes = "Optional notes."
   source = "Optional citation or URL."
   informal_solution = "Optional proof sketch or reference."
   ```
   必須 = `id`(ファイル名 stem と一致) / `title` / `test` / `module` / `holes` / `submitter`。`holes` は「そのモジュール内で当該 problem が所有する `@[eval_problem]` 宣言を全部」列挙する。**multi-hole 問題** (def / instance / theorem を束ねる) が許されており、instance にも名前を付けて `holes` に入れる。単一宣言でも `holes` を使う。
4. ローカル検証: `lake exe lean-eval validate-manifest` と `lake exe lean-eval check-problem-build`。
5. PR を出す。CI が `generated/` の workspace を再生成する。

**重要な自由度**: 「Mathlib に無い定義」は `LeanEval/<Topic>/Defs/*.lean` に小さく持ち込んでよい (`baer_suzuki` が `Defs/PCore.lean` で O_p(G) を、`brauer_suzuki` が `Defs/OddCore.lean` で O(G) を導入している)。つまり **Suzuki 群・Thompson 部分群・F*(G)・Dade isometry のように mathlib に無い概念を要する定理も提案可能**。

`PLAN.md` によれば、キュレーション上の関心事は (i) topic とdifficulty の網羅性、(ii) **frontier モデルに飽和された easy すぎる問題の retire/差し替え**、(iii) 手薄領域の穴埋め。明文の受理基準は無いが、「mathlib の既存定義で述べられる」「現行モデルには難しい」が事実上の選定基準。

---

## 5. 我々の repo に既に在る「提案候補」(AxiomsCheck 済 = 完全証明済)

`OddOrder/AxiomsCheck.lean` は 3348 件の `#assert_only_allowed_axioms` を持つ。lean-eval に無く、mathlib にも無く、かつ我々が axiom-clean で持っている代表:

- `OddOrder.Isaacs.Ch06.IsFrobeniusGroup.isNilpotent_kernel` — **Thompson: Frobenius 核は冪零** (Isaacs Thm 6.24)。lean-eval には `frobenius_kernel_isNormal` (既に 6 名が解決) しか無く、その自然な次段。難易度は明確に一段上 (Thompson の学位論文)。
- `OddOrder.GroupTheory.SpecificGroups.Suzuki.standardPermGroup_isSimpleGroup` — **Suzuki 群 Sz(q) の単純性**。mathlib に Suzuki 群は無いので `Defs/` 持ち込みが必要 (前例あり)。
- `OddOrder.Isaacs.Ch07.normal_J` — Isaacs Thm 7.6 (Glauberman/Goldschmidt 流の normal-J)、`Subgroup.thompsonJ` を要する。
- `OddOrder.Isaacs.Ch09.thompsonWielandt`, `Ch03.hall_higman_1_2_3`, `Ch05.hasNormalPComplement_iff_controlsOwnFusion` など。

(ただし `Ch07.burnside_p_pow_q_pow` は既存 problem と重複するので提案対象外。)

---

## 6. 結論 — 2026-07 時点で我々が取るべき具体的経路

**(A) 解答側 (既存 problem を解く) — 主戦線は「GroupTheory の未解決 3 問」**

我々の repo が実質的に唯一の優位を持つのは、CFSG 非依存の局所解析系 3 問:

1. **`glauberman_zStar` (Z*-定理)** — 最有力。Brauer 指標・principal 2-block が要るが、我々は `OddOrder/RepresentationTheory/**` に指標理論基盤 (111 件 axiom-clean) と Peterfalvi 系の coherence/isometry 機構を持つ。ただし奇数位数世界と違い 2-局所解析が必要で、そのままの再利用ではない。
2. **`brauer_suzuki` (四元数 Sylow 2)** — Z* の下位互換的に近縁。`Defs.oddCore` は我々の `opCore`/`oPiCore` から橋渡し可能。
3. **`gorenstein_walter`** — 3 問中最重量 (Bender method + signalizer functor + Z* を要し、Z* に依存)。順序としては最後。

`schreier_conjecture` / `five_transitive_card_classification` は CFSG 依存で現実的でない。`higman_infinite_simple` / `novikov_unsolvable` は組合せ群論で我々のスタックと無関係。RepresentationTheory の `brauer_splitting_field` は指標理論基盤の再利用が効きうるので副次候補。

**提出の実務** (0042 の方針をそのまま踏襲する):

- 別 workspace (`../<problem_id>/`) を切り、**`import OddOrder` は絶対にしない**。必要最小コードを `Submission.lean` + `Submission/*.lean` に rebrand してコピーする (公開されるのはこの 2 箇所だけなので、逆に言えばここに入れたものは全部公開される)。
- ローカル `lake test` で comparator 受理を確認 → `leanprover/lean-eval-submissions` に「Submit benchmark solution」issue を立てる。gist / fork / 生成 workspace のいずれでもよい。
- model 表記は `feit_thompson` と同様「使用モデル列挙 + human-in-the-loop」で正直に書く。

**(B) 提案側 (新規 problem を出す) — 並行して低コストで実施可能**

`leanprover/lean-eval` に PR を出す経路は開いており外部 PR も merge 実績あり。**推奨は「Thompson: Frobenius 核の冪零性」1 本**:

- mathlib に無い / lean-eval に無い / Freek リスト級の古典 / **新定義を一切要さない** (`IsFrobeniusGroup` 相当の仮説は既存 `MulAction` 語彙で書ける — 既存 `frobenius_kernel_isNormal` の述べ方をそのまま流用すればよい)。
- `frobenius_kernel_isNormal` が 6 名に解かれて飽和気味なので、`PLAN.md` の「飽和問題の差し替え・穴埋め」方針に合致し受理されやすい。
- 我々は `OddOrder.Isaacs.Ch06.IsFrobeniusGroup.isNilpotent_kernel` を axiom-clean で持っているので、**提案 (submitter) と解答 (solver) を同時に出せる**。ただし提案直後に自分で解くとベンチとして意味が薄れるので、提案 PR を先に merge させ、solver 側は他者に開放するのが benchmark への貢献としては筋が良い (submitter ≠ solver は `feit_thompson` の前例どおり正常)。
- 第 2 候補として **Suzuki 群 Sz(q) の単純性** (`Defs/Suzuki.lean` 持ち込み。`Defs/PCore.lean` が前例)。ただし定義の持ち込み量が大きく、レビューコストが高いので後回し。

**(C) やらないこと**

- `import OddOrder` 直提出 (機密性、0042 で既に却下済み)。
- CFSG 依存問題 (`schreier_conjecture`, `five_transitive_card_classification`) への着手。
- lean-eval 作業を FT 3 冊フェーズの frontier より優先すること — 0042 の scope 注記どおり、これはオプショナル・トラック。

Sources:
- [leanprover/lean-eval](https://github.com/leanprover/lean-eval)
- [leanprover/lean-eval-submissions](https://github.com/leanprover/lean-eval-submissions)
- [Lean AI formalization leaderboard](https://lean-lang.org/eval/)
---

# lean-eval 提出候補 — 更新版まとめ (2026-07-19 実測ベース)

> 本節は issue 0050 の旧「提出候補一覧」表を全面差し替えるもの。判定はすべて **実測** (`grep` による実在確認 / `AxiomsCheck.lean` の `#assert_only_allowed_axioms` または `#print axioms` の直接実行 / mathlib 側 grep) に基づく。旧表の 🚧🔭 ラベルは全て無効 (0011/0012 は既に closed、Frobenius 核存在は repo に不在、Burnside 正規 p-補群は mathlib 収録済 など)。

## 0. lean-eval 側の前提 (実測)

- 提出 = `leanprover/lean-eval-submissions` に「Submit benchmark solution」issue。公開されるのは `Submission.lean` + `Submission/` のみ。**`import OddOrder` は不可** (依存閉包経由で未公開部が露出するため。issue 0042 の裁定を踏襲し、必要最小コードを rebrand コピー)。
- 新規 problem の**提案**は `leanprover/lean-eval` への PR で可能 (`@[eval_problem]` + `manifests/problems/<id>.toml`)。外部コントリビュータの problem 追加 PR は merge 実績あり。`Defs/*.lean` に mathlib 非収録の定義を持ち込む前例もある (`Defs/PCore.lean`, `Defs/OddCore.lean`)。
- GroupTheory の**未解決** problem: `glauberman_zStar` / `brauer_suzuki` / `gorenstein_walter` / `schreier_conjecture` / `five_transitive_card_classification` / `higman_infinite_simple` / `novikov_unsolvable`。RepresentationTheory は `brauer_splitting_field` が未解決。
- 我々の既提出: `baer_suzuki` (2026-05-29)、`feit_thompson` (2026-07-16)。
- ⚠ **要再確認の食い違い**: 入力 1 の per-problem ページ確認では `finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow` (Burnside p^a q^b) は **Solved (8 名)**。一方 Matsuyama 候補の検証者は `LeanEval/GroupTheory/Burnside.lean` の本体が `sorry` であることから「未解決」と記述した (Challenge 側は常に `sorry` なので推論が誤り)。**per-problem ページ側 (Solved) を正とする**が、提出前に 1 度確認すること。

---

## 1. ランキング表

### 1-A. verdict = strong (そのまま / ごく軽い加工で提出できる)

推奨度: ★★★ = 最優先 / ★★ = 有力 / ★ = 出せるが優先度低。並びは self-contained × 知名度。

| # | 定理 | repo の Lean 名 | file | axiom-clean | self-contained | mathlib | 知名度 | 推奨度 |
|---|---|---|---|---|---|---|---|---|
| 1 | Jordan の定理 (素数長サイクルを含む原始群 ⊇ Aₙ) | `OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` | `OddOrder/Isaacs/Ch08_PermutationGroups/PCycleJordan.lean:352` | ✅ (`#print axioms` 実測。AxiomsCheck 未登録) | high (bespoke 0) | **partial — mathlib に `proof_wanted` が同一 signature で存在** | 高 | ★★★ |
| 2 | Chermak–Delgado 定理 (Isaacs 1.41) | `Subgroup.chermakDelgado` | `OddOrder/GroupTheory/ChermakDelgado.lean:528` | ✅ (AxiomsCheck:921 + `#print axioms` 実測) | high (bespoke 0) | absent | 高 | ★★★ |
| 3 | Furtwängler 主イデアル定理 (Isaacs 10.18) | `OddOrder.Isaacs.Ch10.transfer_commutator_eq_one` | `OddOrder/Isaacs/Ch10_MoreTransfer/PrincipalIdeal.lean:44` | ✅ (AxiomsCheck:10525 + 実測) | high (bespoke 0) | absent | 伝説級 | ★★★ |
| 4 | Thompson: FPF 作用 ⇒ 冪零 (Isaacs 6.24 / Thompson 1959) | `OddOrder.Isaacs.Ch06.isNilpotent_of_isFrobeniusAction` | `OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean:365` | ✅ (AxiomsCheck:1130) | high (1 行 def をインライン) | absent | 高 | ★★★ |
| 5 | PSL(n,K) の単純性 (Isaacs 8.33) | `OddOrder.Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup` | `OddOrder/Isaacs/Ch08_PermutationGroups/PSLSimple.lean:355` | ✅ (`#print axioms` 実測。AxiomsCheck 未登録) | high (bespoke 0) | partial (Iwasawa 判定と PSL の定義は mathlib 有、単純性は無) | 伝説級 | ★★★ |
| 6 | Dietzmann の補題 (Isaacs 5.10) | `OddOrder.Isaacs.Ch05.dietzmann` | `OddOrder/Isaacs/Ch05_Transfer/Dietzmann.lean:254` | ✅ (AxiomsCheck:1045) | high (bespoke 0) | absent | 高 | ★★ |
| 7 | 既約表現の次数は群位数を割る (Frobenius) | `OddOrder.RepresentationTheory.finrank_dvd_card` | `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean:296` | ✅ (AxiomsCheck:2312 + 実測) | high (bespoke 0) | absent | 高 | ★★ |
| 8 | Burnside の定理 (既約表現の包絡環 = End V) | `OddOrder.RepresentationTheory.span_range_representation_eq_top` | `OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean:192` | ✅ (`#print axioms` 実測。AxiomsCheck 未登録) | high (bespoke 0) | partial (Jacobson density は mathlib 有、表現論形は無) | 高 | ★★ |
| 9 | Alperin–Kuo 系 `g^[G:G'∩Z(G)] = 1` (Isaacs 10.28) | `OddOrder.Isaacs.Ch10.pow_index_commutator_inf_center_eq_one` | `OddOrder/Isaacs/Ch10_MoreTransfer/PrincipalIdeal.lean:90` | ✅ (AxiomsCheck:10526) | high (bespoke 0) | absent | 中 | ★★ (#3 と資産共有。**両方は出さない**) |
| 10 | Horoševskii (自己同型の位数 < \|G\|) | `OddOrder.Isaacs.Ch03.horosevskii_aut_order_lt` | `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean:124` | ✅ (AxiomsCheck:950) | high (bespoke 0) | absent | 中 | ★★ |
| 11 | Lucchini (巡回部分群の core 指数、Isaacs 2.20) | `OddOrder.Isaacs.Ch04.lucchini_index_normalCore_lt_index` | `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean:1084` | ✅ (AxiomsCheck:941) | high (bespoke 0) | absent | 中 | ★★ (#10 と 2 段階の階段にできる) |
| 12 | Isaacs 10.25 (transfer の指数消滅) | `OddOrder.Algebra.transfer_pow_relindex_eq_one` | `OddOrder/Algebra/PrincipalIdealTheorem.lean:1320` | ✅ (AxiomsCheck:10525 + 実測) | high (bespoke 0) | absent | 中 | ★★ (#3 の上流。片方に絞る) |
| 13 | 単純群の冪零極大部分群は p-群 (Isaacs 5.24) | `OddOrder.Isaacs.Ch05.exists_isPGroup_of_isCoatom_of_isNilpotent` | `OddOrder/Isaacs/Ch05_Transfer/NilpotentMaximal.lean:249` | ✅ (AxiomsCheck:1065) | high (bespoke 0) | absent | 中 | ★★ |
| 14 | transfer の推移律 (Isaacs 10.8) | `OddOrder.GroupTheory.transfer_transfer` | `OddOrder/GroupTheory/TransferTransitivity.lean:366` | ✅ (`#print axioms` 実測。AxiomsCheck 未登録) | high (`transferRes` 1 行のみ) | absent | 中 | ★★ |
| 15 | BG Prop 3.9 (奇 p-群の FPF 作用 ⇒ 巡回) | `OddOrder.BG.Ch1.S03.isCyclic_of_isPGroup_of_isFrobeniusAction` | `OddOrder/BG/Ch1_Preliminary/S03g_Thm310.lean:55` | ✅ (AxiomsCheck:5763) | high (1 行 def) | absent | 高 | ★★ |
| 16 | Hall–Petrescu collection 公式 (BG E.1, class ≤ 3) | `OddOrder.BG.AppE.hallCollection_of_class_le_three` | `OddOrder/BG/AppE_FurtherResults.lean:218` | ✅ (AxiomsCheck:10575) | high (1 行 def) | absent | 高 | ★★ (**一般版 `hallCollection` は sorry。class ≤ 3 版のみ**) |
| 17 | 可解群の既約表現次数は \|G\| を割る (BG 2.3 / Fong) | `OddOrder.RepresentationTheory.finrank_dvd_card_of_isAlgClosed_of_irreducible` | `OddOrder/GroupTheory/RepresentationTheory/FongSwan.lean:201` | ✅ (AxiomsCheck:5425 + 実測) | high (bespoke 0) | absent | 中 | ★★ (#7 と重複気味。片方) |
| 18 | BG Thm 3.4 (奇数位数可解の coprime 作用) | `OddOrder.BG.Ch1.S03d.thm34` | `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean:1075` | ✅ (AxiomsCheck:5587) | high (bespoke 0) | absent | 中 | ★ (難度が上限側) |
| 19 | BG Prop 4.4(b) = Gorenstein 7.6.5 (SCN の中心化群分解) | `OddOrder.GroupTheory.centralizer_eq_dprod_of_isSCN_of_sylow` | `OddOrder/BG/Ch1_Preliminary/S04_Prop44b.lean:105` | ✅ (AxiomsCheck:5450 + 実測) | high (`IsSCN` 3 フィールド→仮説 3 本に展開可) | absent | 高 | ★★ |
| 20 | BG App.C Lemma C.1 (ノルム集合 ⇒ p ≤ q) | `OddOrder.BG.AppC.NormSet.lemmaC1` | `OddOrder/BG/AppC_NormSet.lean:1459` | ✅ (AxiomsCheck:5390 + 実測) | high (2 def) | absent | 中 | ★ |
| 21 | Huppert V.8.15 特別版 (定常点安定化群 ⇒ 巡回 + FPF) | `OddOrder.Peterfalvi.Appendices.Huppert.pGroup_cyclic_fixedPointFree` | `OddOrder/Peterfalvi/Appendices/Huppert.lean:720` | ✅ (AxiomsCheck:8090) | medium (3 def、各 1–3 行) | absent | 中 | ★ |
| 22 | Peterfalvi 付録 I Prop 2 (半線形性つき体構造) | `OddOrder.Peterfalvi.Appendices.Huppert.exists_field_semilinear` | `OddOrder/Peterfalvi/Appendices/SemilinearField.lean:199` | ✅ (AxiomsCheck:8870 + 実測) | high (2 def、各 1 行) | absent | 中 | ★ (**`exists_field_of_irreducible` (:133) は出さない。理由は §3**) |
| 23 | 忠実既約表現をもつ群の中心は巡回 (Gorenstein 3.2.2) | `OddOrder.RepresentationTheory.isCyclic_center_of_faithful_irreducible` | `OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean:239` | ✅ (AxiomsCheck:5481 + 実測) | high (bespoke 0) | absent | 中 | ★ (**易しめ枠**として意図的に使うなら) |
| 24 | \|SL(2,q)\| = q(q−1)(q+1) | `OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.natCard_specialLinearGroup_fin_two` | `OddOrder/GroupTheory/SpecificGroups/ProjectiveSpecialLinear/RootGroupSylow.lean:106` | ✅ (AxiomsCheck:355 + 実測) | high (bespoke 0) | absent | 中 | ★ (提出時は vestigial な `[CharP F 2]` を外す) |
| 25 | Thompson critical subgroup (Gorenstein 5.3.11 の (i)部分/(ii)/(iii)) | `OddOrder.GroupTheory.isCritical_exists` | `OddOrder/GroupTheory/CriticalSubgroup.lean:434` | ✅ (`#print axioms` 実測。AxiomsCheck 未登録) | medium (`IsCritical` 1 行連言) | absent | 高 | ★★ (docstring の過大表現を引き写さないこと) |
| 26 | Hall の定理 E / C / D (可解群) | `OddOrder.Isaacs.Ch03.hall_E_exists` / `hall_C` / `hall_D` | `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean:1002 / :1375 / :1675` | ✅ (AxiomsCheck:954 / 1690 / 1694) | medium (`IsHallSubgroup` 2 行、展開すれば mathlib 語彙 100%) | absent | 伝説級 | ★★★ |
| 27 | Thompson: Frobenius 核は冪零 (subgroup-pair 形) | `OddOrder.Isaacs.Ch06.IsFrobeniusGroup.isNilpotent_kernel` | `OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean:382` | ✅ (AxiomsCheck:1131) | medium (5 フィールド structure) | absent | 伝説級 | ★ (**#4 の action 形を優先**) |
| 28 | Huppert: metacyclic Sylow (Isaacs 10.12) | `OddOrder.Isaacs.Ch10.dvd_index_commutator_of_metacyclic_sylow` | `OddOrder/Isaacs/Ch10_MoreTransfer/HuppertMetacyclic.lean:751` | ✅ (AxiomsCheck:10516 + 実測) | medium (`IsMetacyclic` 1 行) | absent | 中 | ★★ |
| 29 | BG Thm 3.5 (Frobenius 群作用、1 次元不動点空間) | `OddOrder.BG.Ch1.S03e.thm35` | `OddOrder/BG/Ch1_Preliminary/S03e_Thm35.lean:1685` | ✅ (AxiomsCheck:5672) | high 相当 (`IsFrobeniusGroup` 1 個) | absent | 中 | ★ (難度が上限側) |
| 30 | BG Thm 6.4 (正規 Hall 下の中心化共役) | `OddOrder.BG.Ch1.S06.exists_centralizing_conj_sup_isPiGroup_of_normalHall` | `OddOrder/BG/Ch1_Preliminary/S06_Thm64Case2.lean:483` | ✅ (AxiomsCheck:2703) | medium (1 行 def × 3) | absent | 中 | ★ |
| 31 | BG Thm 4.20(a) (r(F(G)) ≤ 2 ⇒ G' ≤ F(G)) | `OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two` | `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean:763` | ✅ (AxiomsCheck:2800) | medium (1 行 def × 6。⚠ mathlib の `Group.rank` と名前衝突) | absent | 中 | ★ |

**既提出 / 既解決 (再提出の限界価値なし)**

| 定理 | Lean 名 | 状況 |
|---|---|---|
| Feit–Thompson | `OddOrder.feitThompson` (`OddOrder/FeitThompson.lean:575`) | `feit_thompson` として 2026-07-16 提出済 (#828)。axiom-clean・bespoke 0・statement 1 行 |
| Baer–Suzuki (p-core) | `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` (`.../Theorem211Wielandt.lean:885`) | `baer_suzuki` 提出済 (2026-05-29, #118)。workspace は `/home/ywr/lean-eval-submissions/baer_suzuki` (note のパス `../../../baer_suzuki/` は stale) |
| Burnside p^a q^b | `OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow` (`.../Ch07_ThompsonSubgroup/Main.lean:910`) | 定理は strong (axiom-clean、bespoke 0、statement 完全 mathlib 語彙)。ただし eval 側 problem は **Solved (8 名)** — §0 の食い違い注記を確認のうえ判断。提出時は stale docstring (「local axiom に封じ込め」) を落とす |

### 1-B. verdict = viable (bespoke def の焼き込み等が必要 / 価値か難度に留保)

| 定理 | repo の Lean 名 | file | axiom-clean | self-contained | mathlib | 知名度 | 備考 |
|---|---|---|---|---|---|---|---|
| Fitting 部分群 F(G) の冪零性・最大性 (Isaacs 1.28) | `OddOrder.Isaacs.Ch01.fitting.isNilpotent` / `nilpotent_normal_le_fitting` | `OddOrder/Isaacs/Ch01_Sylow/Basic.lean:1108 / :963` | ✅ (`#print axioms` 実測。**AxiomsCheck に Ch01 は未登録**) | medium (`fitting`/`opCore` 各 1 行) | absent | 高 | 焼き込み 2 行。実質 strong 寄り |
| Wielandt の自己同型塔定理 (Isaacs 9.10) | `OddOrder.Isaacs.Ch09.exists_card_autTowerType_le` | `OddOrder/Isaacs/Ch09_MoreSubnormality/AutTower.lean:364` | ✅ (AxiomsCheck:1191) | medium (`GroupPkg`/`autTowerPkg`/`autTowerType` ~10 行、universe 跨ぎ) | absent | 高 | 正答率はほぼ 0 想定 |
| Thompson 正規 p-補群 (Isaacs 7.1) | `OddOrder.Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses` | `OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplementFinal.lean:35` | ✅ (AxiomsCheck:1630) | medium (bespoke 5 個、計 ~8 行) | absent | 高 | 実質 strong 寄りの viable |
| Glauberman normal-J (Isaacs 7.6 完全形) | `OddOrder.Isaacs.Ch07.normal_J` | `OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean:1425` | ✅ (AxiomsCheck:1569) | low (bespoke 9 個、うち再帰 def 1) | absent | 高 | **reduced case ではなく Thm 7.6 そのもの** (旧メモの誤り)。docstring の「local axiom 残」は stale |
| Matsuyama (Isaacs 2.13) | `OddOrder.Isaacs.Ch02.matsuyama` | `OddOrder/Isaacs/Ch02_Subnormality/Theorem211Wielandt.lean:768` | ✅ (AxiomsCheck:933) | medium (`opCore` 1 行) | absent | 中 | eval の `pCore` (sSup 版) と defeq でないので橋渡し補題が要る |
| Hall–Higman 型 (BG 6.1 / A.4(b)) | `OddOrder.BG.Ch1.S06.le_oPiPrimePiCore_of_abelian_normal_in_sylow` | `OddOrder/BG/Ch1_Preliminary/S06_Thm61.lean:47` | ✅ (AxiomsCheck:2541) | medium (bespoke 3) | absent | 高 | repo 内では `AppA.thmA4b` の 20 行ラッパー。「Hall–Higman 定理」と称するのは過大 |
| BG Thm A.4(a) (O_p(G)=1 ⇒ p-stable) | `OddOrder.BG.AppA.thmA4a` | `OddOrder/BG/AppA_PStability.lean:818` | ✅ (AxiomsCheck:2527 + 実測) | medium (`IsPStable`/`opCore`) | absent | 高 | 教科書より仮説が弱い (solvable を落としている) |
| BG Thm 3.6 (⁅H,R⁆ の p-length one) | `OddOrder.BG.Ch1.S03f.thm36` | `OddOrder/BG/Ch1_Preliminary/S03f_Thm36.lean:3812` | ✅ (AxiomsCheck:5760) | medium (bespoke 5、4 段連鎖) | absent | 中 | 支持 ~5,700 行。事実上解答不能側 |
| BG Thm 3.10 (\|M\| = \|C_M(R)\|^\|R\|) | `OddOrder.BG.Ch1.S03g.bgThm310_nilpotent` | `OddOrder/BG/Ch1_Preliminary/S03g_Thm310Nilpotent.lean:289` | ✅ (AxiomsCheck:5455) | medium (2 def, ~15 行) | absent | 高 | 結論が (b) ∧ (c) の連言。分割提出が望ましい |
| BG Cor 1.12 (Ω₁-剛性) | `OddOrder.BG.Ch1.S01.corollary_1_12` | `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:474` | ✅ (AxiomsCheck:2822) | medium (`IsElementaryAbelian`) | absent | 中 | 本体は 15 行の系。重い前提 2 本 (Baer trick / BG Prop 1.10) に全面依存 |
| BG App.C Lemma C.2 | `OddOrder.BG.AppC.NormSet.lemmaC2` | `OddOrder/BG/AppC_LemmaC2.lean:25` | ✅ (AxiomsCheck:5400 + 実測) | medium (2 def) | absent | 中 | **条件 (A) 仮説 `_hA` は未使用** (repo 版は書籍より強い)。出題時に残すか落とすか要判断 |
| Huppert (Peterfalvi 付録 I Prop 1) | `OddOrder.Peterfalvi.Appendices.Huppert.fitting_cyclic_fixedPointFree` | `OddOrder/Peterfalvi/Appendices/Huppert.lean:1305` | ✅ (AxiomsCheck:8093) | medium (bespoke 4、うち 12 行の bundled Subgroup) | absent | 高 | 焼き込めば実質 strong |
| Peterfalvi 付録 I Prop 2(b) | `OddOrder.Peterfalvi.Appendices.Huppert.exists_injective_semilinear_companion` | `OddOrder/Peterfalvi/Appendices/SemilinearField.lean:520` | ✅ (AxiomsCheck:8885) | high (bespoke 0) | absent | 中 | 本体が仮説 `hsemi`/`hdim` に hoist され、実質 35 行の bookkeeping。**単独提出は不可、#22 とセット** |
| Peterfalvi 付録 C Prop 2 既約性段 | `OddOrder.Peterfalvi.Appendices.NearFields.rightMulAction_irreducible_of_index_two` | `OddOrder/Peterfalvi/Appendices/NearFields.lean:405` | ✅ (AxiomsCheck:8901) | medium (bespoke 4、~40 行) | absent | 中 | 近体系を出すならこちら (下の `nearField_field_structure_of_index_two` は §3 で見送り) |
| Suzuki 群 Sz(q) の単純性 | `OddOrder.GroupTheory.SpecificGroups.Suzuki.standardPermGroup_isSimpleGroup` | `OddOrder/GroupTheory/SpecificGroups/Suzuki/Simplicity.lean:268` | ✅ (AxiomsCheck:918 + 実測) | low (証明込み preamble 600–700 行) | absent | 伝説級 | **`∧ Nat.card ... = q²(q²+1)(q−1)` と併記して出す**と statement が自己証明的になる (位数側も clean) |
| \|Sz(q)\| = q²(q²+1)(q−1) | `OddOrder.GroupTheory.SpecificGroups.Suzuki.natCard_standardPermGroup` | `OddOrder/GroupTheory/SpecificGroups/Suzuki/Bruhat.lean:673` | ✅ (実測。⚠ AxiomsCheck:852。同名の ProjectiveUnitary 版が :587 にあり要区別) | low | absent | 高 | 単純性と Bruhat 分解を共有し独立でない |
| PSU(3,q) (q=2ⁿ>2) の単純性 | `OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.standardPermGroup_isSimpleGroup` | `OddOrder/GroupTheory/SpecificGroups/ProjectiveUnitary/Simplicity.lean:337` | ✅ (AxiomsCheck:608 + 実測) | low (~25 def + 証明) | absent | 高 | Suzuki 版と構造が同型 → 両方出さない |
| 第二 (列) 直交関係 (Isaacs 2.18) | `OddOrder.RepresentationTheory.column_orthogonality_diagonal` | `OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean:91` | ✅ (AxiomsCheck:1927 + 実測) | medium (5–6 個の def/instance) | absent | 高 | `Fintype (IrreducibleCharacter G)` を仮説に置く必要あり |
| ∑ χ(1)² = \|G\| | `OddOrder.RepresentationTheory.sumIrreducibleDegreeSq` | `.../ColumnOrthogonality.lean:137` | ✅ (AxiomsCheck:1942) | medium (def 4 + Fintype) | absent | 高 | 上と資産共有 |
| \|Irr G\| = \|ConjClasses G\| (Isaacs 2.8) | `OddOrder.RepresentationTheory.card_irreducibleCharacter_eq` | `.../CharacterCompleteness.lean:658` | ✅ (AxiomsCheck:1919) | medium (def 4–5) | absent | 高 | `IsIrreducibleCharacter` が `V : Type 0` 制限という非標準エンコード |
| Irr(G) は CF(G) の基底 | `OddOrder.Peterfalvi.S05.classFunction_span_irreducibleCharacter_eq_top` | `OddOrder/Peterfalvi/S05_NormThree.lean:54` | ✅ (AxiomsCheck:5681) | medium (def ~40 行) | absent | 高 | 難度が preamble 設計で大きく振れる |
| Brauer の置換補題 | `OddOrder.RepresentationTheory.brauer_permutation_lemma'` | `.../BrauerPermutationUnconditional.lean:196` | ✅ (AxiomsCheck:1966 + 実測) | medium (実際は ~10 def) | absent | 高 | docstring の「Isaacs Thm 6.32」は *Finite Group Theory* に無い (別書 *Character Theory* の Lemma 6.32) → 出題文に書くなら訂正 |
| Burnside: 奇数位数群に非自明実既約指標なし | (推奨差替) `OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'` `.../BrauerPermutationUnconditional.lean:233` | 同上 | ✅ (AxiomsCheck:1970) | low (def 8) | absent | 伝説級 | 元候補 `OddOrder.Peterfalvi.S03.hasNoRealCharacters_nontrivialIrreducibleClassFunctions` (`S03_PreliminaryCharacter.lean:126`) は 2 行のラッパで包装 def が 2 個増えるだけ → **上流に差し替える** |
| Peterfalvi (3.5.1) ノルム 3 分解 | `OddOrder.Peterfalvi.S05.exists_signedTriple_of_inner_self_three` | `OddOrder/Peterfalvi/S05_SignedTripleGrid.lean:73` | ✅ (AxiomsCheck:5580) | low (def 8) | absent | 中 | Fourier 補題を与えると残る数学が薄い |
| Wielandt の不動点公式 (Peterfalvi (9.1)) | `OddOrder.GroupTheory.wielandt_fixedPoint_frobenius` | `OddOrder/GroupTheory/WielandtFixedPoint.lean:52` | ✅ (AxiomsCheck:9046 + 実測) | medium (structure 焼き込み ~9 仮説) | absent | 中 | AxiomsCheck:8944 付近の「sorried Wielandt を cite」コメントは stale |
| 可解 CN 群の構造定理 (Gorenstein 1.5) | `OddOrder.GroupTheory.solvableCN_nilpotent_or_frobenius_or_threeStep` | `OddOrder/GroupTheory/CNGroupStructure.lean:1048` | ✅ (AxiomsCheck:10688 + 実測) | low (bespoke 8、structure 2) | absent | 中 | 教科書 1.5 の弱化版 (補元分類を省略) である旨を明示すること |

---

## 2. トップ 5 の推し所

### ① Jordan の定理 — `OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`
- **mathlib 側が `proof_wanted` として明示的に欲しがっている** (`Mathlib/GroupTheory/GroupAction/Jordan.lean:462`、ファイル冒頭 TODO にも記載)。しかも repo の引数リストが proof_wanted と**文字単位で一致**。ベンチ問題として理想形。
- bespoke def ゼロ・statement 100% mathlib 語彙・repo 内 import 閉包は `CycleCommutators.lean` 1 本だけ (def/structure を含まない補題のみ) → **preamble 焼き込み不要**。
- mathlib には 3-cycle 版だけが証明済み (`..._of_isThreeCycle_mem`) なので、素数長サイクル一般版は真に未収録。
- 障害: repo 側 `AxiomsCheck.lean` に未登録 (Ch08 全体が未登録) → 提出前に登録 issue を起こすと良い。提出可否には影響しない (`#print axioms` で clean 実測済)。
- statement 素案 (そのまま):
  `theorem jordan_prime_cycle {α} [DecidableEq α] [Fintype α] {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α) {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α) {g : Equiv.Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p) (hg : g ∈ G) : alternatingGroup α ≤ G`

### ② Chermak–Delgado 定理 — `Subgroup.chermakDelgado`
- statement が 1 行・完全 mathlib 語彙 (`Subgroup.Characteristic` / `IsMulCommutative` / `Subgroup.index`)、**Challenge への def 焼き込みゼロ**。証明側の CD measure 機構は全部本文外なので理想的な分離。
- mathlib は大文字小文字無視・upstream master の module 一覧まで確認して "chermak"/"delgado" ゼロ。等価な別名定理も無し。
- 抜け道が無いことを確認済み: `N = ⊥` は `A = ⊤` で破綻、`N = ⊤` は可換群でしか通らない。実証明は Isaacs 1.42–1.45 (CD 格子 + 等号条件) をフルに要する。
- statement 素案:
  `theorem chermak_delgado {G} [Group G] [Finite G] : ∃ N : Subgroup G, N.Characteristic ∧ IsMulCommutative N ∧ ∀ A : Subgroup G, IsMulCommutative A → N.index ≤ A.index ^ 2`

### ③ Furtwängler 主イデアル定理 — `OddOrder.Isaacs.Ch10.transfer_commutator_eq_one`
- 知名度が最上位 (類体論の Hauptidealsatz の群論版)。statement は `MonoidHom.transfer` + `Abelianization.of` + `commutator` のみで **3 行・repo def ゼロ**。実際に repo を一切 import しない scratch ファイルで statement が通ることを確認済み。
- mathlib の `GroupTheory/Transfer.lean` を全宣言列挙して不在を確認 (`transfer_eq_pow` / `transfer_center_eq_pow` / Burnside `ker_transferSylow_isComplement'` まで)。`Hauptidealsatz` / `capitulation` 等の別名でもゼロ。
- 証明側は `OddOrder/Algebra/PrincipalIdealTheorem.lean` (1351 行) + `AugmentationIdeal.lean` (1164 行) の群環 Witt 型計算で、mathlib からの短絡路が無い = 「statement は 3 行、証明は極めて重い」という eval 的に美味しい形。
- 注意: 上流の `OddOrder.Algebra.transfer_pow_relindex_eq_one` (#12) と 系 `pow_index_commutator_inf_center_eq_one` (#9) は証明資産をほぼ完全に共有する。**3 本のうち 1 本に絞るか、難易度階段として明示的に組で出す**。
- statement 素案:
  `theorem furtwaengler {G} [Group G] [Finite G] (g : G) : MonoidHom.transfer (Abelianization.of : commutator G →* Abelianization (commutator G)) g = 1`

### ④ Thompson: FPF 作用 ⇒ 冪零 — `OddOrder.Isaacs.Ch06.isNilpotent_of_isFrobeniusAction`
- lean-eval には既に `frobenius_kernel_isNormal` (6 名解決) があり、**その自然な次段**。飽和した既存問題の穴埋めという `PLAN.md` のキュレーション方針に合致。
- `IsFrobeniusAction` は 1 行 def (`∀ a ≠ 1, ∀ n ≠ 1, a • n ≠ n`) なのでインラインすれば statement は 100% mathlib 語彙。plain def なので defeq で `exact` が通る。**旧メモの「`MonoidHom.FixedPointFree` 語彙への橋渡しが要る」は誤り** (橋渡しは不要、しかも古典形は一般形の特殊化なので弱くなるだけ)。
- mathlib は `GroupTheory/FixedPointFree.lean` に involution 系の初等結果しか持たず、Frobenius 群論自体が皆無 ("Thompson" は mathlib 全体で 0 hit)。
- repo 版は素数位数 FPF 自己同型に限らない**任意の非自明有限 A の Frobenius 作用**という一般形。提出は action 形 (:365) を推奨 (subgroup-pair 形 :382 は 5 フィールド structure が要る)。
- statement 素案:
  `theorem thompson_fpf_nilpotent {A N} [Group A] [Finite A] [Nontrivial A] [Group N] [Finite N] [MulDistribMulAction A N] (h : ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n) : Group.IsNilpotent N`

### ⑤ PSL(n,K) の単純性 — `OddOrder.Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup`
- 有限単純群論の古典的頂点の一つ。statement は `Matrix.ProjectiveSpecialLinearGroup` (mathlib 収録の定義) と `IsSimpleGroup` だけで、**bespoke def ゼロ**。import 閉包も PSLSimple + TransvectionGeneration の 833 行で閉じ、補助宣言は全て private。
- mathlib は PSL の定義・射影空間への作用・`IsPreprimitive` instance・Iwasawa 判定を持つが、**単純性そのものは無い** (mathlib で単純性が証明済みの群は交代群と素数位数巡回群のみ)。判定は厳しめに partial。
- 難点: Iwasawa 仮説の一部 (忠実性・前原始性) が mathlib 既製なので「完全にゼロから」よりは易しい。ただし root subgroup 族の構成・Gaussian elimination による transvection 生成 (Thm 8.31)・SL perfect (Thm 8.32) は全部自前で ~830 行。
- statement 素案 (そのまま):
  `theorem psl_simple {ι} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {K} [Field K] (h : 3 ≤ Nat.card ι ∨ ∃ β : K, β ≠ 0 ∧ β ^ 2 ≠ 1) : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι K)`

**次点**: Hall E/C/D (#26、知名度は最上位だが `IsHallSubgroup` の展開が要る)、Dietzmann (#6)、`finrank_dvd_card` (#7)。

---

## 3. reject / 見送りの記録 (再調査しないこと)

| 対象 | 判定 | 理由 (実測) |
|---|---|---|
| **Glauberman ZJ 定理 (literal J(S) 一般形)** | **reject — repo に存在しない** | 唯一近い `S06_Thm62JS.lean:69 zCenterThompsonJ_sup_oPiCore_normal_of_reduced` は **ZJ 本体を仮説 `hZJ` として受け取る**条件付き補題。AxiomsCheck に該当なし。`normal_J` からの導出は同ファイル docstring が反例つきで否定。障害は Gorenstein Ch.8 §2 (pp.270–279) 全面移植 (open issue 3024、3017 は blocked) |
| **Frobenius の定理 (核の存在)** | **reject — repo に存在しない** | 3 通りの grep で不在確認。古典 Frobenius の核 `notConjugateSet` (`FrobeniusActionTI.lean:490`) が**部分群/正規部分群であるという定理が 1 本も無い**。repo の `IsFrobeniusGroup` は核を仮定する structure。代替 `Ch06.exists_isComplement'_of_centralizer_le` は N の正規性を仮定する別定理 |
| **Burnside 正規 p-補群 (Isaacs 5.13)** | **reject — mathlib 収録済** | `Mathlib/GroupTheory/Transfer.lean:276` に `MonoidHom.ker_transferSylow_isComplement'` が同一仮説・docstring 明記で存在。repo 版 (`Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer`, `Basic.lean:477`) は 12 行で mathlib を呼ぶだけ (docstring 自身が adapt と自認)。**旧 0050 表の「Isaacs 7.8 = Burnside 正規 p-補群 ✅ 0032」は誤り** — 0032 は p^a q^b 可解性 |
| **Brauer–Fowler** | **reject — スコープ外かつ不在** | repo 全体で 0 hit。references でも Gorenstein 1968 (Thm 1.6/1.8, Ch.9 §1) にしか現れず、Isaacs/BG/Peterfalvi の 3 冊に無い。CLAUDE.md の「Gorenstein 本体は形式化しない」方針により恒久的に対象外 (旧表の 🔭 は誤り) |
| BG Thm 6.2 Puig L(S) 版 (`OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal`) | weak — 見送り | 実在・clean だが、これは B.4 Step 1 の中間主張で書籍が名を与えた statement ではない。同クラスタの `zCenter_lOdd_normal_of_oPiCore_eq_bot` (AxiomsCheck:2752) の方が literal。Puig L(S) 自体の知名度も低い |
| `NearFields.nearField_field_structure_of_index_two` (および `exists_field_structure_of_cyclic_index_two`) | weak — 見送り | **仮説 `A`/`hcomm`/`hidx` が結論に一切効いていない**。実際に 3 仮説を全部削った版を scratchpad で書き下しコンパイル成功 (`#print axioms` clean、77 行、標準有限体プラミングのみ)。近体論と無関係に解けてしまう |
| `Huppert.exists_field_of_irreducible` (付録 I Prop 2(a)) | weak — 見送り | 同様に `ψ`/`hirr` が結論に現れず、`GaloisField` 経由 30–60 行で解ける。**`exists_field_semilinear` (#22) に差し替え済** |
| `NearFields.exists_aInvariant_complement_of_elementaryAbelian` (演算子群 Maschke) | weak — 見送り | 数学の核は mathlib の `MonoidAlgebra.Submodule.exists_isCompl` にあり、repo 分は束転送の packaging。repo 内に同内容が 4–5 本重複するルーチン infra。⚠ 元候補名 `...Huppert.exists_aInvariant_complement_of_elementaryAbelian` (`Huppert.lean:609`) は **AxiomsCheck 未登録** — 機械検証済みなのは `NearFields.lean:298` の twin |
| `AppC.NormSet.normOneFrobenius_isFrobeniusGroup` | weak — 単独提出せず | 番号なしの補助構成で fame ほぼゼロ。5 フィールド中 3 つが数行、カード計算も回避可能。C.2 系を出す場合の付属定義として同梱 |
| `Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot` ((1.2)) | weak — 見送り | 証明が列直交 + inflation 全単射に全面依存し、両方 mathlib に皆無。支持 ~3,936 行。前提を与えないと解不能、与えると残りは ~90 行の帳簿仕事 |
| `Peterfalvi.S07.coherent_of_constant_degree` ((5.7)) | weak — 見送り | bespoke 15+ 個・6 ファイルの framework 焼き込みが必要。かつ statement が書籍 (5.2.d) の一般 R(χ) を 2 元にハードコードした**特殊化版**で、「(5.7)」と称すると過大表示。より忠実な `S07.uniform_degree_coherence_of_families` (`S07_PivotCoherence.lean:794`) は AxiomsCheck 未登録 |
| `Peterfalvi.Appendices.Suzuki.Hypothesis.sylowTwo_isMulCommutative_or_isSuzuki2Group` | weak — 参考枠 | statement 全体が 20 フィールドの bespoke 仮説束にパラメータ化され、独立した定理として読めない。上流 ~3,000 行が全て repo 独自。有名なのは Suzuki の 2 重推移群定理/Higman の概念であって本命題ではない |
| `AppE.hallCollection` (Hall collection 一般版) | 提出不可 | 130 行が `sorry`、AxiomsCheck 未収載。**class ≤ 3 版 (#16) のみ提出可** |

---

## 4. 次のアクション

1. **(提案側・最優先) Jordan の定理を `leanprover/lean-eval` に problem 提案 PR で出す。** mathlib 側が `Jordan.lean:462` で `proof_wanted` として明示しており、signature をそのまま `LeanEval/GroupTheory/` に `@[eval_problem]` で置き、`manifests/problems/jordan_prime_cycle.toml` を作る。bespoke def ゼロなので `Defs/` 追加も不要。`lake exe lean-eval validate-manifest` + `check-problem-build` で検証してから PR。
2. **(提案側) 続けて Chermak–Delgado / Furtwängler / Thompson FPF-nilpotency の 3 本を提案 PR にする。** いずれも def 焼き込み不要 (Thompson は 1 行 def をインライン)。`frobenius_kernel_isNormal` が 6 名に解かれて飽和気味なので、Thompson 版は `PLAN.md` の「飽和問題の差し替え・穴埋め」方針に直接合致する。**提案 PR を先に merge させ、solver 側は他者に開放**する (submitter ≠ solver は `feit_thompson` の前例どおり正常)。
3. **(解答側) GroupTheory の未解決 3 問への着手判断を行う。** 順序は `glauberman_zStar` → `brauer_suzuki` → `gorenstein_walter` (最後は Bender method + signalizer functor + Z\* 依存で最重量)。`brauer_suzuki` の `Defs.oddCore` は repo の `opCore`/`oPiCore` から橋渡し可能。`schreier_conjecture` / `five_transitive_card_classification` は CFSG 依存で着手しない。
4. **(整備) AxiomsCheck 未登録の strong 候補を登録する issue を起こす** — `Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` / `Ch08.isSimpleGroup_projectiveSpecialLinearGroup` / `GroupTheory.isCritical_exists` / `GroupTheory.transfer_transfer` / `Isaacs.Ch01.fitting.isNilpotent` 系 / `RepresentationTheory.span_range_representation_eq_top` (いずれも `#print axioms` では clean 実測済)。提出可否には影響しないが、repo 側の機械監査に載せる価値がある。
5. **(整備) stale な docstring を掃除する issue を起こす** — `burnside_p_pow_q_pow` の「local axiom に封じ込め」、`Ch07.normal_J` の「Remaining local axioms」、`Ch03_SplitExtensions/Basic.lean:122` の「K=⊥ axiom 残」、`AppC_NormSet` の「Proof (to be formalized)」、`AxiomsCheck.lean:8944` 付近の「sorried Wielandt を cite」、`CNGroupStructure.lean:975` の「only remaining sorry」、`brauer_permutation_lemma'` の「Isaacs Thm 6.32」誤引用、`CriticalSubgroup.lean` の「C/Z(C) elementary abelian は導出可能」(一般には偽)。提出物にそのまま写すと誤解を招く。
6. **(整備) `notes/meta/lean_eval_baer_suzuki.md` のパス修正** — 提出 workspace は `../../../baer_suzuki/` ではなく `/home/ywr/lean-eval-submissions/baer_suzuki`。あわせて `issues/0050` の旧候補表を本まとめで差し替え、per-theorem sub-issue (0042 型) は上記 1–2 の 4 本から起票する。