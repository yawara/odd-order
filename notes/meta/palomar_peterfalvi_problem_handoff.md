# Palomar 提出用リポジトリ `peterfalvi-problem` — 引き継ぎ (2026-09-27)

BG App.C Problem 1 (= Glauberman–Norton 1993 の "Problem (Péterfalvi)") の解決
(`hypothesisB_false`) を別リポジトリに切り出し、Palomar (palomar-registry.org) に登録する作業の
引き継ぎ。前セッションは usage limit 直前で中断した。

## 0. 進捗 (2026-09-27 更新 — 後続セッションはここから読む)

- **A–H と J は完了**。新リポ main = `698b7ae` (8 commit) を push 済。ローカルの
  `python3 scripts/check.py` は全段通過 (metadata・Challenge 本文・build 警告ゼロ・Challenge は
  `sorry` 2 件のみ・`mk_all --check`・`lake lint`・`Tests/TextLint.lean`・`Tests/Axioms.lean`
  = 538 宣言が標準 3 axiom のみ)。ライブラリは 19 file・約 5,800 行 (抽出時 7,023 行)。
- 主定理 = `PeterfalviProblem/Main.lean` の `not_hypothesisB_three` (p = 3 の否定解) と
  `hypothesisB_two` (GN Example 10、SL(2, 2^q))。`comparator.json` はこの 2 つを選ぶ。
- 計画からの変更点: 条件 (A) は Witness に `q_not_dvd : ¬ q ∣ p - 1` として持たせ、使うのは
  「q が奇数」(`q_odd`) だけになった。BG Lemma C.3 の生成元・関係式の機構と「P char PU」は不要に
  なり消した。`Tests/` と `scripts/check.py` は t3 の型を non-module 用に直したもの。
- **J** = odd-order `5e6fabda4` (README 英日の Problem 1 節と ★ 囲みを新リポへの案内に縮めた)。
- **I も完了 (2026-09-27 01:25–02:02 JST)**。CI run `36254471548` (check + comparator、3 kernel 受理) と
  preflight run `36254706697` (`status: pass`、errors/warnings 空) を確認 → ユーザーが提出内容
  (repo・commit・`comparator.json`・relationship `maintainer`) に明示同意 → gh 経路 5 手順で提出。
  **submission id = `ycfw25g98032`**。公式検証 run `36255377900` 成功 → 自動査読 (`codex:gpt-6-sol`)
  = **blocking なし・警告なし・コメントなし** (review digest `aafeb84c…`) → ユーザーが登録を決定 →
  `POST /register` 受理 (17:02:21 UTC)。
- **登録完了 = `PALOMAR-2026-09-27-000006` version 1** (2026-09-27 02:24:07 UTC、
  https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-27-000006&version=1)。
  Palomar 側の登録工程が 26 日 13:32 UTC から約 11 時間止まっていたため、同意 (17:02) から
  9 時間余り待った。保存用 fork = `PalomarArchive/yawara--peterfalvi-problem--a99f0c3a84ab`、
  不変タグ `palomar/PALOMAR-2026-09-27-000006-v1/698b7ae…`。新しい版を出すときは
  `existing_id: PALOMAR-2026-09-27-000006` を付ける (同じ repo・同じ `comparator.json` パス)。
- access token は登録完了後に破棄した。再び必要なら**ユーザーが**
  https://submit.palomar-registry.org/submissions (Find my submissions) から取り直す
  (エージェントがブラウザ復旧をしてはいけない)。状態確認の頻度は `review-ready` 中 5 分に 1 回まで。
- API の罠: Python urllib の User-Agent は Cloudflare に弾かれる (error 1010、何も消費されない)。
  curl なら通る。ブラウザの UA は偽装しない。
- 登録後の候補: 新リポ README (英日) に Palomar ID を載せる (ユーザー確認のうえ)。

## 1. ユーザー裁定・前提

- リポジトリ = **`yawara/peterfalvi-problem`** (public、ユーザーが 2026-09-26 に作成)。
  ローカル = `/home/ywr/peterfalvi-problem` (remote `origin` = SSH)。2 commit を push 済
  (ユーザー指示「とりあえず push もしてね」)。
- README は英日 (`README.md` / `README.ja.md`) を書き直す。**英語は平易に** (短文・一文一事・
  よく使う語)。odd-order の README の Problem 1 節 (英日) は、新リポ公開後に案内へ縮める。
- mathlib 更新に伴って変わるファイルの周辺は一緒にリファクタリングする (ユーザー)。持ち出す
  ファイルは名前空間変更で全部触るので、全部をリファクタリング対象とする方針で合意済。
- Palomar の要件 (2026-09-26 に実測): Lean **v4.35.0-rc2 以上** (PalomarSubmission
  `toolchains.json` の `minimum`; `lake comparator` と NanoDa・con-ron は rc2 以降の toolchain に
  だけ同梱)、toolchain は mathlib 側と完全一致、**submodule 禁止**、root licence Apache-2.0、
  `Challenge.lean` の推移的 import は Mathlib のみ。Comparator は定理の型から辿れる宣言を
  **Challenge 側とライブラリ側で同一**であることまで検査する
  (PalomarSubmission `docs/comparator-declaration-closure.md`)。
- 手本 = `/home/ywr/t3-model-companion` (同アカウント、PALOMAR-2026-09-26-000004 として登録済)。
  CI は `.github/workflows/lean.yml` (build + comparator、bwrap installer の SHA256 固定) と
  `palomar-preflight.yml` (`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml`
  @ `a59f25bd8a66bf6faf3a4f4260d412989c0185ea` を workflow_dispatch で呼ぶ)。
  `scripts/verify-comparator.sh`、`formalization.yaml` (v0.4) も流用できる。
- ローカルの bubblewrap は 0.9.0 で comparator の sandbox を満たさない → comparator は CI で回す。

## 2. 現状 (新リポの main)

- `09d1266` **Extract the proof of hypothesisB_false from odd-order** — odd-order
  `82e8b66fe` から、`hypothesisB_false` と p = 2 の例 (`hypothesisBAbstract_sl2`) が実際に使う
  宣言だけを機械的に抽出 (17 file、約 6,900 行)。名前空間 `OddOrder.BG.AppC.{Problem1,NormSet}`
  と `OddOrder.BG.AppC` を `PeterfalviProblem` に、module を `PeterfalviProblem/` 以下に改名。
  Lean/mathlib は **v4.35.0-rc2** (mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`)。
  `lake build` 成功 (2,409 jobs)、両定理とも axiom は標準 3 つのみ。
  警告 = 非推奨 9 件 (`if_pos`/`if_neg`/`dif_pos` → `ite_eq_left`/`ite_eq_right`/`dite_eq_left`;
  `Algebra/FrobeniusCyclicModule`・`Proof/FrobeniusExponent`・`Proof/Endgame`) と
  `Proof/CommutingSubgroup.lean:26` の longLine 1 件。**docstring はまだ odd-order 前提のまま**
  (issue 番号・notes のパス・"Section 16"・"Theorem 1/2"・"superseded" など)。
- `4b35130` **Add the statement module (not yet wired in)** —
  `PeterfalviProblem/Statement.lean` に文の定義を置いた: `additiveFieldGroup`・`normOneUnits`・
  `normOneMulAction`・`normOneFrobeniusGroup`・`normOneFrobeniusComplement`・`primeLine`
  (**新定義**: `𝔽_p` の像。旧定義は `span {1}` 経由)・`HypothesisB` (Prop、本の向き
  `σ(P₀)^y = y⁻¹ σ(P₀) y`)。単体でコンパイル可だが**まだどこからも import されていない**。
  旧定義 (`Basic/NormOneUnits.lean`・`Basic/Witness.lean`) が現役。
- `.lake/packages` は t3 から `cp -a` した (8.4 GB)。**`lake update` は走らせない**
  (mathlib の cache get が走る)。`lake build` はそのまま動く。

## 3. 残作業 (この順)

A. **Basic 層の組み替え**
   - `Basic/NormOneUnits.lean`: `Statement` を import。Statement に移った定義と
     `normOneFrobeniusSubspaceKernel` (+ `mem_…_inl`) を削除。`conditionA` の定義をここへ
     (`Basic/Witness.lean` から)。H 上の事実 (`normOneFrobeniusKernel`・`normOneMulAction_apply`・
     `normOneFrobenius_generatorRelation_step2_primeLine`) は FrobeniusGroup へ。逆に
     `exists_normOneUnit_ne_one`・`normOneUnits_card_coprime_p` (FrobeniusGroup から) と
     `mem_normOneUnits_iff_isSquare` (Proof/Layers から) をここへ。
   - `Basic/FrobeniusGroup.lean`: `primeLineElement`/`primeLineGenerator` の定義をここへ。
     `inl_mem_primeLine_iff` を追加し、`primeLineGenerator_mem` の証明を新しい `primeLine` に
     合わせて直す (`SL2Example.lean:369` の `rw [primeLine, normOneFrobeniusSubspaceKernel]` も)。
   - `Basic/Witness.lean`: `HypothesisBAbstract` を平坦化して **`structure Witness`** に
     (`FieldNormalizerData` → `Witness` を全置換、`W2` → `P0`、`sigma_P0_eq_W2` →
     `sigma_P0_eq_P0`、`s_mem_W2` → `s_mem_P0`、`W2_normalizes_Q` → `P0_normalizes_Q`、
     `W2_conj_y_normalizes_U` → `P0_conj_y_normalizes_U`)。`Basic/WitnessSetup.lean` と
     `Basic/WitnessQ.lean` (`Q_mul_comm` のみ) を併合。Witness 内部は従来の向き
     `MulAut.conj y • σ(P₀)` のまま残し、橋 `HypothesisB.nonempty_witness (hB) (hq : q.Prime)
     (hp : Odd p) (hA : conditionA p q) : Nonempty (Witness p q G)` で `y⁻¹` を渡す
     (`MulAut.conj y⁻¹ • K.map σ = K.map ((MulAut.conj y⁻¹).toMonoidHom.comp σ)` の補題が要る)。
B. **改名** (順番に注意): `false_of_witness` → `false_of_ne_three`、`false_of_exotic` →
   `false_of_odd_cube_exponent`、`hypothesisB_false` → `false_of_witness`。
C. **Proof 層の配置**: `Proof/Layers.lean` を群の恒等式 (Lemma A′・C・semilinear) と層の話に
   分ける。`Proof/Collision.lean` (旧 Trace) は `PairComposition` への併合を検討。
   `Proof/Endgame.lean` (1,294 行) を `MasterFormula` (sqSelect・MasterFormula・
   exchange_relation・anchor) と `Endgame` に分ける。空になった section (TheoremTwo・
   CosetSeparation・FieldSide・"collision-span"・"Theorem N1" など) を消す。
D. **`PeterfalviProblem/Main.lean`**:
   `theorem not_hypothesisB_three (q : ℕ) (hq : q.Prime) (hA : ¬ q ∣ 3 - 1) (G : Type*)
   [Group G] : ¬ HypothesisB 3 q G` (`conditionA_iff_not_dvd` + `nonempty_witness` +
   `false_of_witness`) と `theorem hypothesisB_two (q : ℕ) (hq : q ≠ 0) :
   HypothesisB 2 q (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q))` (SL2Example の
   構成を ∃ 形に直す; 定義が空でない証拠として載せる)。
E. **`Challenge.lean`** (Statement.lean と同じ import・同じ定義 + 2 定理を `sorry`)、
   **`Solution.lean`** (`import PeterfalviProblem`)、**`comparator.json`**
   (`theorem_names` = 上の 2 つ)、Challenge と Statement の定義部分が一字一句同じかを調べる
   スクリプト。Challenge を lakefile の `defaultTargets` に入れない (t3 と同じ; sorry 警告のため)。
F. **docstring の書き直し** (平易な英語、odd-order への言及を除く)、非推奨と longLine の修正、
   mathlib standard linter で警告ゼロ。`set_option backward.isDefEq.respectTransparency false in`
   (2 か所) が不要になっていないか試す。証明の骨格 (英語で書くための材料) は
   `notes/bg/appC_problem1_resolution.md` と `notes/bg/appC_problem1_summary.md`。
G. **リポ文書**: `README.md` / `README.ja.md`、`formalization.yaml` (sources: `type:
   original-proof` + `relationship: other` の項、GN 1993 (DOI
   `10.1090/S0002-9939-1993-1160299-X`) と BG 1994 は `background`/`other`、Péterfalvi は
   contributor `problem-proposer`; automation は agent (Claude Code / Codex) と ChatGPT 相談
   (summary §5 の 4 回); review は agent-reviewed; 分類は arXiv `math.GR` ほか)、
   `CITATION.cff`、CI、`scripts/verify-comparator.sh`。
H. **検証**: `lake build` 警告ゼロ、2 定理の `#print axioms`。comparator は CI (push 後) で。
I. ユーザーに中身を見てもらう → push → CI と preflight → Palomar のフォームへの提出
   (外向きの操作なのでユーザーが行うか、明示の許可を得る)。
J. odd-order の README (英日) の Problem 1 節を新リポへの案内に縮める。

## 4. 参考になる実測

- 素朴な import 閉包 = 48 file / 37,254 行 (うち Isaacs Ch.1–4 が 28 file、`AppC_LemmaC3_ConjugateLine`
  の import 1 本経由; 使うのは `Q_mul_comm` だけ)。証明が実際に使うのは 16 file・259 宣言・
  本体約 5,100 行。
- 抽出時、`simp` が項に痕跡を残さずに使う rfl 補題 (`normOneVal_mul`・`legWeight_true`/`_false`・
  `SL2.upperHom_apply`/`torusHom_apply`) は使用集合から漏れたので手で戻した。
- Isaacs 側は rc2 で 2 file が壊れる (`IsSimpleGroup.eq_bot_or_eq_top_of_normal` と
  `isMulCommutative_closure` の API 変更) が、持ち出さないので無関係。
