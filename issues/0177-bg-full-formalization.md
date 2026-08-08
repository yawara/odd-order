---
id: 177
slug: bg-full-formalization
title: "BG 完全形式化キャンペーン (逐条監査)"
created: 2026-08-08
---

# BG 完全形式化キャンペーン (逐条監査)

## 位置づけ

3 冊スコープ (Isaacs / BG / Peterfalvi) の逐条監査の**最後**。

| 書籍 | 件数 | 状態 | issue |
|---|---|---|---|
| Peterfalvi | 284 | ✅ 完了 (補充 ~20、誤判定 9) | [closed/0172](closed/0172-peterfalvi-full-formalization.md) |
| Isaacs | 305 | ✅ 完了 (補充 5、stale 注記訂正 7) | [closed/0176](closed/0176-isaacs-full-formalization.md) |
| **BG** | 下記 | ⬜ **本 issue** | 0177 |

方法論は 0172 / 0176 と同一:

> 番号の参照地図で当たりを付ける → file header の対応表と `theorem` 一覧で実体確認
> → 書籍ページ画像で条項確定 → 部分被覆/特殊化/packaging 差を補充

## ⚠ BG は番号体系が前 2 冊と違う

Isaacs / Peterfalvi は `N.M.` を行頭に置く形式だったが、**BG は 2 系統ある**:

1. **`(N.M)` を単独行に置くラベル** — これは**証明内の主張ラベル**であって定理番号ではない。
   例: §3 の証明中に `(3.6)` `(3.7)` `(3.8)` が並び、後段が「by (3.6)」と参照する。
   ⚠ **これを定理番号と取り違えると件数が数倍に膨らむ**。
2. **`Kind N.M.` / `Kind N.M (帰属).`** — こちらが**番号付き結果**。
   `Theorem` / `Proposition` / `Lemma` / `Corollary` の 4 種。

さらに BG は **Theorems A–E** (章番号を持たない主定理) と **Appendix A–E** を持つ。

## 実測ベースライン (2026-08-08)

`references/bg/local-analysis.pdftotext.txt` から機械抽出。
抽出パターン (⚠ `N.M.K` 形は Gorenstein の引用なので除外する):

```python
pat = re.compile(r'^(Theorem|Proposition|Lemma|Corollary)\s+(\d{1,2})\.(\d{1,2})(?!\.\d)\s*(\(|\.)', re.M)
```

| 節 | 件数 | 欠番 |
|---|---|---|
| §1 | 22 | なし |
| §2 | 7 | なし |
| §3 | 10 | なし |
| §4 | 19 | ⚠ 4.1 (OCR で header 行が崩れている。本文中には `Lemma 4.1` の引用あり) |
| §5 | 7 | なし |
| §6 | 7 | なし |
| §7 | 5 | ⚠ 7.1 (同上) |
| §8 | 1 | — |
| §9 | 6 | なし |
| §10 | 14 | なし |
| §11 | 7 | なし |
| §12 | 19 | なし |
| §13 | 13 | なし |
| §14 | 12 | ⚠ 14.11 |
| §15 | 9 | なし |
| §16 | 1 | — |
| **小計** | **159** | 欠番 3 (いずれも OCR 由来、実在は本文引用で確認済) |

種別内訳: Theorem 71 / Lemma 69 / Proposition 35 / Corollary 34
(重複カウント込み — 章頭の再掲があるため)。

**補章**: `Kind X.N` (X ∈ A-E) が **15 件**。

⬜ **要確定**: (a) 欠番 3 件の実際の statement (ページ画像で確認)、
(b) Theorems A-E の扱い、(c) 補章の正確な件数。

## ⚠ この census が測っていないもの (0172 / 0176 と同じ)

1. **特殊化債務** — 書籍より狭い仮説
2. **部分被覆** — 多条項の一部だけ / TFAE の条項数不足
3. **packaging 差** — 条項はすべて在るが書籍の statement の形になっていない
4. **mathlib 被覆の未記録** — Isaacs で主役だった型。BG は FT 固有の内容が多いので
   前 2 冊より少ないと予想されるが、§1 (Preliminary Results) は標準的な有限群論なので要確認。

## 作業手順

- [x] **ステップ 1 (大半完了、2026-08-08)**: 欠番 3 件のうち **2 件を解決**。
      - **7.1** — OCR が `L e m m a 7.1.` と**文字分解**。空白許容パターンで解決。
      - **4.1** — OCR が `Lemma-4.1.` と**ハイフン**を入れており空白許容でも漏れる。
        ⟹ §4 は 20 件。
      - ⬜ **14.11 は未発見**。ページ画像で要確認。
      - **Theorems A–E**: 5 件すべて所在確認 (`Theorem A` L6615 / `B` L6602 / `C` L6653 /
        `D` L6669 / `E` L6692)。⚠ `Theorem B.4` (補章 B) と混同しないこと。
      - **補章**: `Kind X.N` が 14 件。⬜ 各補章の `.1` が未発見で要確認。
- [x] **census note を新設 (2026-08-08)**:
      [`notes/bg/full_formalization_census_2026_08_08.md`](../notes/bg/full_formalization_census_2026_08_08.md)
- [ ] **ステップ 2 (進行中)**: §1 から文書順に逐条監査。
      - **§1 監査完了 (2026-08-08)**: 全 22 件被覆・**補充ゼロ**。
        ⚠ **stale 注記 2 件を訂正** — `S01_FrattiniBurnside.lean` の対応表が Thm 1.8 と
        Thm 1.11 を「**Phase 1 待ち**」のまま残していた (どちらも実装済)。
        🚨 とくに **1.8 は同一ファイル内で矛盾**していた (:63 が「Phase 1 待ち」、
        :152 が「⭐ sorry-free」)。
        ⚠ **1.11 は Isaacs 側のディレクトリに在る** (owner chapter 規則、通算 4 回目)。
      - **§2 監査完了 (2026-08-08)**: 全 7 件被覆・**未形式化ゼロ**。
        補充 = **packaging 差 1 件** (Lem 2.7 の群形 `elemAbelian_aut_action_group`)。
        ⚠ **自己訂正**: 本 issue は一度「Lem 2.7 = §1-§2 で唯一の真の未形式化」と
        **誤判定した**。実体は 2 系統・独立に 2 回 (issue **0150** と **3009**、
        いずれも close 済) 形式化されており、`AxiomsCheck.lean` には
        「**BG Lemma 2.7(a)/(b)**」と明示コメント付きで登録されていた。
        ⚠ **stale 注記 4 件を訂正** (`S02_RepresentationsBasic.lean` の
        Lem 2.3 / Prop 2.4 / Thm 2.5 の「stub 未配置」+ 「全 6 結果」という件数)。
      - **§3 監査完了 (2026-08-08)**: 全 10 件被覆・**未形式化ゼロ**。実収穫 3 件:
        1. **特殊化債務 2 件** (Lem 3.2 / Thm 3.5 — どちらも**書籍自身の Note** が
           「`K` が可解という仮説は不要」と書いているのに repo が `IsSolvable ↥K` を
           持っていた。Thompson は repo に在るので discharge 可能)。
           ⟹ `S03_WithoutSolvableKernel.lean` (`bgLemma32` / `bgThm35`)。
        2. **部分被覆 1 件 = Thm 3.10 の (a)** — capstone `bgThm310_nilpotent` は (b)+(c) しか
           返しておらず、(a) は module leaf 止まりだった。docstring は「(a) は elsewhere」と
           書いていたがその実体は**可換 kernel 専用**で書籍の (a) を満たさない。
           ⟹ (a) を dévissage に通し、書籍パッケージ `S03g.bgThm310` を新設。
        3. **BG の大域規約 2 本を確定** (下記 ⚠)。
        ⚠ **Lem 3.1 の条項 (b) は pdftotext が丸ごと落としていた** — ページ画像
        `references/bg/pages/bg-p017.png` (PDF = 書籍 + 13) で `C_K(x) = 1 (x ∈ R^#)` と確定。
        ✅ **Prop 3.9 は書籍より強い** (書籍の「`H` は `p'`-群」を落としている)。
      - 1 節ぶん終えるごとに census note を更新して commit。
      - ⬜ **次 = §4 (20 件)**。

## 📌 BG の大域規約 (2026-08-08 §3 で確定 — 全節の判定に効く)

**これを知らないと偽の特殊化債務を起票する**:

| 規約 | 出典 | 意味 |
|---|---|---|
| 「All groups considered in this work will be **finite** except when explicitly stated otherwise」 | 書籍 p.4 (pdftotext L612) | `[Finite G]` は書籍強度 |
| 「we consider representations … by **finite-dimensional** linear transformations. … By module we will always mean **finite-dimensional** right module」 | 書籍 p.9, §2 冒頭 (L961-967) | **`[FiniteDimensional F V]` は書籍強度** — module 系 statement (Thm 3.4 / 3.5 等) に付いていても債務でない |

⚠ 個々の statement 本体には書かれていないので、**節冒頭の規約を読まないと
「repo が書籍より狭い」と誤判定する**。

## 完了条件

BG の全番号付き結果が**書籍強度**の Lean statement を持つか、**mathlib 被覆として対応が
記録されている**。特殊化債務ゼロ・部分被覆ゼロ・packaging 差ゼロ。
各節の監査結果を census note に記録する。

## 🔎 逐条監査の走査手順 (2026-08-08 §2 で確定 — 順に全部やる)

§2 で「実体が在るのに無いと判定した」ので、走査対象を固定する。**(4) だけでは足りない**。

1. **`OddOrder/AxiomsCheck.lean` を書籍番号で grep** — ここが **書籍番号 ↔ Lean 実体の最良の
   索引**。`grep -n "Lemma 2.7\|Lem 2.7" OddOrder/AxiomsCheck.lean` で一発で当たった。
2. **`issues/closed/` を番号で grep** — 過去に閉じた形式化 issue が残っている
   (`0150-bg-lemma-2-7-*`, `3009-lem27-*`)。
3. **結論の形 (概念名) で repo 全体 grep** — 書籍ラベルでの grep は他書と衝突するうえ、
   実体のファイル名は概念名 (`ElemAbelianAutAction` / `SingerReducibility`) なので当たらない。
4. 節ディレクトリの file header 対応表 + `theorem` 一覧。

## ⚠ 誤判定様式 (前 2 冊で計 16 件の実例)

正本 = memory `textbook-coverage-audit-failure-modes` (11 型)。とくに:

* **「計画表の欠落 ≠ 実体の欠落」** (§2 Lem 2.7, 2026-08-08)。`S02_RepresentationsBasic.lean`
  の §2A-§2F 区分に Lem 2.7 が無いのは事実だが、実体は BG ディレクトリの**外**
  (`GroupTheory/RepresentationTheory/`) に在った。区分表の穴は**当たりを付ける道具**であって
  不在の証拠ではない。

* 🚨 **書籍の Note / Remark を statement と一緒に読む** — BG は Lem 3.2 と Thm 3.5 の直後に
  「`K` が可解という仮説は不要」という Note を置いており、それを読まずに statement だけ
  写した結果 5 宣言に**書籍が明示的に不要と言った仮説**が入っていた (2026-08-08)。
  **番号付き結果の直後の Note/Remark は statement の一部として扱う**。
* **注記は当たりを付ける道具であって判定の証拠ではない** — Isaacs では stale 注記の訂正
  (7 件) が実際の補充 (5 件) を上回った。
* 🚨 **AxiomsCheck の「(a)+(b)」表記も条項被覆の証拠にならない** (§3 Thm 3.10, 2026-08-08)。
  注記が「BG Theorem 3.10 **(a)+(b)**, elementary-abelian GROUP case」と書いていても、
  それは「その周辺で (a) も証明済」の意で、**endpoint の結論の型に (a) が入っている
  保証ではない**。実際 group form は (a) を捨てて (b)+(c) だけ返していた。
  ⟹ **条項照合は注記でなく `theorem` の結論の型を読む**。
* 🚨 **「(x) は M-independent ゆえ elsewhere で提供」型の docstring は行き先を確認する**
  — Thm 3.10 の "elsewhere" は**可換 kernel 専用**の特殊形で、書籍の条項を満たさなかった。
* **grep は種別語の略記も含める / 番号だけで引く** — Isaacs 7.4 を `Lem` 略記で取りこぼした。
* **内部段の名前が先に当たっても file の endpoint を確認する** — Pf (9.11) / Isaacs 3.34 / 9.23。
* **検索範囲を章のディレクトリに絞らない** — owner chapter 規則で他章に在る (Isaacs 2.20 / 3.15 / 3.23)。
* **`⊴` と `<` は pdftotext で区別不可** — ページ画像が必須 (Isaacs 1.24)。
* **TFAE/iff は書籍の条項数と一致するか確認** — Isaacs 5.26 は 3 条件中 (1)⇔(3) だけだった。

## 参照

- 前身: [issue 0172](closed/0172-peterfalvi-full-formalization.md) / [issue 0176](closed/0176-isaacs-full-formalization.md)
- 書籍: `references/bg/local-analysis.pdf`
- Coq 併読: `coq/theories/BGsectionN.v` (ファイル名が BG の節構成と 1:1 対応)
