# 章節 dependency 調査 framework

新規に章/節を調査して per-chapter/section note を書くとき, あるいは既存ノートを再点検する
ときの **4 視点 framework**. 2026-05-22 Isaacs Ch.4-7 を 4 視点で並列再調査した際にこの構造を
抽出した — その時点で既に per-chapter ノートは存在していたが, **4 視点が初回調査の時点で
立てられていれば再調査は不要だった** 部分が多い. ⇒ **本 framework の primary use は per-chapter/
section note の初回調査時テンプレート**, secondary use は既存ノートの欠落補強 (=audit).

## 4 視点 (per-chapter/section note の必須内容)

### 視点 1: forward to later chapters/sections

> その章節に登場するが, **形式化は後続の章節に forward** する事項

per-note に書く形:

- **Statement だけ書かれて proof が後ろ** の定理を列挙 + axiom 化方針.
  例: Isaacs Ch.6 Thm 6.23 (statement) → Ch.7 §7C で proof. `axiom`/`sorry` 1 箇所のみ.
- **概念が紹介されて後で一般化** される箇所.
  例: Ch.4 `[G,A]` for A ⊆ Aut G が Ch.6 Frobenius action と機械を共有.
- **後の章/本での `OddOrder/GroupTheory/` shared module 化** が必要そうな def の予告.
  例: Isaacs `J(P)` は BG App.A も使用 ⇒ Ch.7 専用 namespace ではなく shared module.
- mmd 内 prose の "see Chapter/Section X" / "we will show in §Y" を grep:
  ```bash
  grep -nE "Chapter [0-9]+|Section [0-9]+|see (later|below|chapter)" <mmd>
  ```

### 視点 2: 章節内部の定理依存

> 章/節内部の hub-and-spoke + 連鎖

per-note に書く形:

- 章内自己引用頻度表:
  ```bash
  awk 'NR>=START && NR<=END' <mmd> \
    | grep -oE "(Theorem|Lemma|Corollary|Proposition) X\.[0-9]+" \
    | sort | uniq -c | sort -rn
  ```
  ここで X = 章番号. **頻度上位 5-10 が hub**.
- **物理順序 (mmd 出現順) vs 論理順序 (証明依存順) の差** を flag.
  例: Ch.6 6.11 は mmd で 6.12 より前に登場するが 6.12 の corollary (L3519). 実装順序は逆.
- FT クリティカル leaves について **後ろから前へ** citation chain を辿る.

### 視点 3: mathlib status (証明内 API 含む)

> statement 単位の有無だけでなく, **証明本体で呼ぶ mathlib API** まで列挙

per-note に書く形 (これが最大価値で per-chapter ノートで weakest になりやすい):

- 各定理を 3 bucket に分類:
  - **(a) statement そのまま mathlib にある** (exact match).
  - **(b) proof tools は mathlib, statement が新規**. wrapper / specialization で書ける.
  - **(c) 完全新規**. statement, proof tools ともに未収載.
- **(b) 型について proof 内で呼ぶ mathlib API の具体名** を列挙. 例:
  - Thm 7.4 (SL(2,q)): `Matrix.SpecialLinearGroup.fin_two_induction`, `Matrix.det_fin_two`.
  - Thm 5.6 (central transfer): `MonoidHom.transfer_center_eq_pow`, `transferCenterPow`.
- mathlib のずれを flag:
  - codomain mismatch (e.g. mathlib `transferFocal` codomain `H/H*` vs Isaacs `H/H'`).
  - 仮定の緩急 (`IsCommutative` instance upgrade 等).
  - 名前が違う / 存在しない (e.g. mathlib に `Subgroup.IsMaximal` なし → `IsCoatom` 使用).
- **新規 helper 候補** を抽出: `OddOrder/GroupTheory/` 配下 (将来 mathlib upstream) に置くべき
  小定理を列挙. 例: `commutatorElement_mul_left`, `pow_mul_class2_formula`,
  `Aut(elem ab) ≃* GL(n, ZMod p)` bridge.

### 視点 4: 先行する章節への定理依存

> 先行章節の どの定理を どこで利用 するか (per-target)

per-note に書く形:

- mmd grep ベースで先行章 cite を全列挙:
  ```bash
  awk 'NR>=START && NR<=END' <mmd> \
    | grep -nE "(Theorem|Lemma|Corollary|Proposition) [0-9]+\.[0-9]+"
  ```
- per-target table を作る (利用元定理 X.Y → 利用先 Z.W, mmd line, 状態).
- **prose の言及 vs proof body の cite を区別**. 前者は無視, 後者だけ依存に立てる.
- 未実装 stub の transitive blocker を flag.
  例: Cor 3.28 が未実装 ⇒ 4.26, 4.28-4.30, 4.34-4.36, 4.38 が blocked.

## 初回調査 (primary use): per-chapter/section note を書く

新規に章/節を調べて `notes/<book>/<scope>.md` を書く時. 通常の per-chapter/section note 構造の
**必須セクション** として 4 視点を取り込む:

```markdown
# <Book> <Scope> — mini-roadmap

**スコープ**: <書誌情報, pp.X-Y, mmd 行範囲>
形式化先 (予定): <Lean ファイルパス>

## TL;DR
<状況, 重要発見の 1-3 行>

## 章節分割と全結果一覧
<table: # / 種別 / 内容 / mmd line>

## 視点 1: forward to later chapters/sections
<このスコープから後続への forward dep 一覧>

## 視点 2: 章節内部の依存
<hub-and-spoke + 論理 vs 物理順序の差>

## 視点 3: mathlib status (証明内 API 含む)
<per-target table: bucket / statement API / proof-internal API / glue 工数 / 新規 helper>

## 視点 4: 先行章節への依存 (per-target)
<table: 利用元定理 → 先行章節, mmd line, 実装 stub 状態>

## 着手順 (提案)
<FT クリティカル度 + 章内依存 + mathlib カバレッジで並べる>

## 開発時の注意点 / 未解決の疑問
<設計判断点, 既知 gotcha>

## 関連ノート
<上流, 下流, 横断>
```

**実行手順** (単体 chapter/section, 1-2 時間, 人手):
1. mmd 行範囲を確定 (章境界 / `##`/`###` ヘッダ).
2. mmd を通読 + section ヘッダ抽出失敗 (Nougat ミス) を補正.
3. 章内自己引用頻度 + 先行章 cite を grep (視点 2, 4 の準備).
4. 視点 1, 2, 3, 4 を順に書く. 視点 3 を最も深く.
5. 着手順 + 注意点を最後にまとめる.
6. ROADMAP のチェックリストから新ノートにリンク.

## 並列調査 (本 1 冊規模, 半日)

新規に本 1 冊全章/節を調べる時 (e.g. BG 全 16 §, Peterfalvi 全 16 §). 並列 sub-agent で各章/節
1 つずつ per-chapter/section note を書く:

1. 各章/節につき general-purpose sub-agent を起動 (4-6 並列まで).
2. 各 agent には **self-contained prompt** で:
   - mmd 行範囲
   - 既存 per-chapter/section ノートが**ある場合は path**, ない場合は「新規調査」と明示
   - mathlib path
   - 4 視点 + 必須 section 構造
   - 出力先 path (e.g. `notes/bg/sNN_*.md`)
   - 出力 word cap (~1500-2000 words/agent が ideal で per-chapter ノート 1 本に相当)
3. 全 agent 完了後, **横断観察** (本ごとの cross-chapter forward / shared concept) を別途
   `notes/<book>/_overview.md` に書く.
4. ROADMAP に進捗ログ 1 行.

### sub-agent prompt template (新規調査用)

```text
You are writing a per-chapter/section investigation note for
<BOOK> <SECTION> for a Lean 4 formalization project (Feit-Thompson,
repo `/Users/ywr/odd-order`).

**Sources:**
- mmd: `<mmd path>`, lines <RANGE>
- Mathlib: `/Users/ywr/odd-order/.lake/packages/mathlib/Mathlib/<relevant subdirs>`
- 横断参照: `notes/meta/phase2_cross_refs.md` (本間の cite 対応),
  `notes/meta/mathlib_coverage.md` (全体カバレッジ)
- 既存 per-chapter/section note (validate 対象): <path or "none">

**4 viewpoints (mandatory sections in output):**

1. **Forward to later chapters/sections** — statement-only theorems whose
   proof goes later, concepts introduced here but generalized later,
   shared defs that warrant `OddOrder/GroupTheory/` placement. Cite mmd
   lines.

2. **Internal dependencies** — Hub-and-spoke + non-obvious deps +
   physical-vs-logical order mismatches. Use `awk + grep` on mmd line
   range for self-citation frequency.

3. **Mathlib status, including proof-internal API** — For each theorem,
   bucket (a/b/c) + statement-level API + proof-internal API specific
   names + glue work. Flag new helpers to put in
   `OddOrder/GroupTheory/`. Spend hardest here — usually weakest part.

4. **Preceding-chapter dependencies** — Re-grep mmd for `(Theorem|Lemma|
   Corollary|Proposition) [0-9]+\.[0-9]+` and produce per-target table
   (citing thm → preceding thm, mmd line, stub status). Distinguish
   prose mention vs proof body cite.

**Output**: write to `notes/<book>/<scope>.md`. Markdown, ~1500-2000
words, structure per the framework template at
`notes/meta/chapter_investigation_framework.md`. Sections in order:
TL;DR / 章節分割 + 結果一覧 / 視点 1 / 視点 2 / 視点 3 / 視点 4 / 着手順 / 注意点 / 関連ノート.

After writing, summarize key findings in <200 words for the parent.
```

## 再調査 (secondary use, "audit")

既存 per-chapter/section note が 4 視点を十分にカバーしていないとき, あるいは事実誤認が
疑われるとき. 出力先が異なる:

- 既存 note は **最小 Edit で訂正** (rewrite 避ける), 訂正タグ `(YYYY-MM-DD audit 訂正)` を残す.
- 横断観察と新発見は **別 file** `notes/meta/<scope>_audit_<date>.md` に統合 doc として書く.
  ロードマップ的に強い signal を持つ (e.g. 実装順序 revision, shared module 化推奨).
- sub-agent prompt template は **再調査用** で:
  - "existing notes are detailed; your job is a **fresh re-investigation**"
  - "validate the existing notes; where they are correct, say so briefly and move on; spend
    depth on **gaps**, **sharpened sub-deps**, and **proof-internal mathlib usage**"
  - "Do **not** edit any files. Report only."

2026-05-22 Isaacs Ch.4-7 の例: [`ch04_07_audit_2026_05_22.md`](ch04_07_audit_2026_05_22.md) が
このパターンの初出力. これは既存 per-chapter ノート (`ch0{4,5,6,7}_*.md`) が初回調査の時点で
4 視点を十分にカバーしていなかったための補強. **次回からは初回調査時点で 4 視点を立てる**
ことで, audit pass を不要にする.

## 本ごとの適応

framework は本に依らないが, 視点 1, 4 で本ごとに **追加チェック項目** が要る:

### Isaacs (chapter-level: 1 章 = 1 file)

- 視点 1: 後続章への forward + **後の本 (BG/Peterfalvi) で shared module 化必要な def** も flag.
  e.g. `J(P)` は BG App.A も使用 ⇒ `OddOrder/GroupTheory/` 配下推奨.
- 視点 4: 先行章のみで完結 (Ch.1-X-1).

### BG (section-level: 1 § = 1 file)

- 視点 1: BG 内 §X → §Y forward + **BG App.C ≡ Peterfalvi §9** の同期チェック
- 視点 3: BG が `**G**` (= Gorenstein 1968) として引く外部参照を **Isaacs FGT に読み替え**:
  - `notes/meta/phase2_cross_refs.md` §5 "BG 主要結果の Isaacs 読み替え" 表を参照
  - 各 BG §X.Y 定理について Isaacs 対応 Z.W の実装状態を確認
- 視点 4: **Phase 1 Isaacs への依存** = mmd 内 "**G**, Thm X.Y.Z" cite を grep + Isaacs 読み替え:
  ```bash
  grep -oE "Theorem [0-9]+\.[0-9]+\.[0-9]+" bg.mmd | sort | uniq -c
  ```

### Peterfalvi (section-level)

- 視点 1: Peterfalvi §X → §Y + **BG App.C ≡ §9, BG §16 → §10 Type I-V** の出力受け取り
- 視点 3: Peterfalvi が引く `[Is]` (Isaacs *Character Theory of Finite Groups* 1976; **本プロジェクト
  Isaacs FGT とは別書**), `[BG]`, `[HB]` (Huppert-Blackburn), `[H]` (Huppert) を区別.
  - `[Is]` は当面 mathlib `RepresentationTheory.Character` で代用
  - `[BG]` は Phase 2a 出力に依存
- 視点 4: **Phase 2a BG + Phase 1 Isaacs FGT 両方への依存** cross-check:
  ```bash
  grep -oE "\[(BG|Is|HB|H)\][^,]*Theorem [0-9]+\.[0-9]+" peterfalvi.mmd | sort | uniq -c
  ```

## 既存 BG / Peterfalvi per-section note (2026-05-22 作成済) の扱い

BG 全 §1-§16 + App.A-E (22 ファイル) と Peterfalvi 全 §1-§16 + App.A-E (18 ファイル) は
2026-05-22 に作成済. これらは TL;DR / 結果表 / Isaacs/BG 対応 / mathlib カバレッジ / Phase 2
着手順 / 未解決 TODO の 6 セクションで構成され, 4 視点を **部分的に** カバー:

- **視点 1 forward**: 結果表 + Phase 2 着手順 で散発的にカバー. **整理推奨**.
- **視点 2 internal**: 結果表で線形的にカバー. **hub-and-spoke + 順序差は弱い**.
- **視点 3 mathlib (proof-internal)**: mathlib カバレッジ section は statement-level 中心で
  **proof-internal API は薄い**. 着手前に深掘り推奨.
- **視点 4 preceding**: Isaacs/BG 対応 + 未解決 TODO で部分カバー. **per-target table 化推奨**.

⇒ Phase 2a / 2b の節着手の **直前** に, 該当 § について 4 視点で **既存ノート補強** (= 軽い
re-audit) を実施するのが推奨運用. 大規模再調査は不要.

## Lessons learned (2026-05-22 Isaacs Ch.4-7 から)

- **並列 4 agents** で十分. 5+ は synthesis オーバーヘッドが増える.
- **agent prompt 約 1200-2000 words 出力枠** が ideal. 600 words だと表が薄い, 3000+ で冗長.
- agent には **mmd line 範囲を明示**で精度が大幅向上.
- 再調査時, agent に **既存ノートを「validate 対象」と明示**: "validate the existing notes;
  where they are correct, say so briefly and move on; spend depth on gaps". これで agent が
  既知の情報を冗長に並べず, 新発見を浮き上がらせる.
- **視点 3 (proof-internal API) が最も価値**: per-chapter ノートが statement-level に偏る
  ため. agent prompt で "spend hardest here" と明示.
- **factual errors が必ず複数見つかる**: 既存ノートが手書き mmd grep ベースで作られている
  以上数件のミスは避けられない. 再調査でこれを catch.
- **音 (silence) は signal**: agent が「既存ノートで confirmed」と短く済ませる箇所は実際
  正しいことが多い. 既存ノート全体を再生成する必要は無い.
- **synthesis step (統合 meta doc)** が再調査の成果物本体. agent output 単体は raw material.
- **初回調査時に 4 視点を立てる** ことで, 後の audit pass を減らせる. ⇒ **本 framework の
  primary use は初回調査時のテンプレート**.

## 関連ノート

- [`forward_dep_policy.md`](forward_dep_policy.md): 視点 1 の forward dep を Lean 構造に
  落とす規約.
- [`phase2_cross_refs.md`](phase2_cross_refs.md): BG / Peterfalvi 視点 1, 4 適応の参照表.
- [`mathlib_coverage.md`](mathlib_coverage.md): 視点 3 全体像.
- [`lean_formalization_tips.md`](lean_formalization_tips.md): mathlib API 探索 (3 層運用).
- [`subagent_orchestration.md`](subagent_orchestration.md): 並列 agent 起動の汎用方針.
- [`ch04_07_audit_2026_05_22.md`](ch04_07_audit_2026_05_22.md): 再調査 (audit) flow の初出力例.

---

*Phase 2a (BG) / 2b (Peterfalvi) 着手時に節単位で適用予定. その際の lessons learned で
本ファイル update.*
