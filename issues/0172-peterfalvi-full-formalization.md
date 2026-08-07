---
id: 172
slug: peterfalvi-full-formalization
title: "Peterfalvi 完全形式化キャンペーン (次フロンティア)"
created: 2026-08-07
---

# Peterfalvi 完全形式化キャンペーン

**ユーザー裁定 2026-08-07**: Q₈ Brauer–Suzuki 完了 (repo 全体 sorry 0) を受け、
**Peterfalvi *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) の完全形式化を
次のフロンティアに定める**。

⚠ **sorry 0 は「完了」ではない** — 未形式化の番号付き結果は `sorry` を生まない。本キャンペーンは
`sorry` カウントでなく**書籍の番号付き結果を書籍強度で被覆したか**で測る (CLAUDE.md「進捗の測り方」)。

## 実測ベースライン (2026-08-07)

正本 = [`notes/peterfalvi/full_formalization_census_2026_08_07.md`](../notes/peterfalvi/full_formalization_census_2026_08_07.md)。
⚠ 2026-07-16 の 3 冊 survey は**使わない** (降格済 + 3 週間分 stale)。

### Part I (§1–§16 = 書籍 result 番号 (1.x)–(14.x))

書籍テキストから番号を機械抽出 (各章 1..max が**欠番なし**で連続) → **全 169 件**。
repo の docstring cite と突合:

| 層 | 件数 | 内容 |
|---|---|---|
| cite あり | **169 / 169** | 番号または sub-part `(N.M.x)` 形で repo に出現 |
| **cite ゼロ** | **0** | (8.9) は 2026-08-07 に形式化済 (下記ステップ 1) |

### Part II (Suzuki の定理 A) / 補章

Part II は `Proposition N` / `Lemma N` の**章内リセット番号**で、Part I と同じ機械 census が
効かない。補章 (Huppert / Near-Fields / Suzuki 2-Groups / Feit–Sibley) も同様。
**census 第 2 弾として別途実施する** (下記ステップ 2)。

## ⚠ この census が測っていないもの

「cite あり」= **その番号が docstring に現れる**であって、**書籍強度の statement が存在する**
ことではない。実際の残債は次の 3 種で、いずれも番号 grep では検出できない:

1. **特殊化債務** — 書籍より狭い仮説で述べている (2026-07-16 時点で Pf に 26 件と記録)。
2. **部分被覆** — (a)(b)(c) のうち一部だけ形式化、bundled statement が条項を運搬していない
   (実例: BG 15.7 の (b)(e) が `∃ X` decoupling で準恒真だった = issue 3022)。
3. **言及のみ** — 「(8.5) は §14 で使う」のような散文 cite で、statement が無い。

⟹ **本キャンペーンの本体は「番号を埋める」ことでなく、1 件ずつ statement を書籍と逐条照合する
監査**。上流優先 + 文書順 (CLAUDE.md) で (1.1) から順に当たる。

## 作業手順

- **ステップ 1 ✅ 完了 (2026-08-07、commit `39bfc2831`)**: **(8.9)** — 唯一の cite ゼロ。
  `OddOrder/Peterfalvi/S10_Theorem88CaseB.lean` に形式化 (axiom-clean):
  `Theorem88CaseBData.derivedInG_inf_centralizer_W1_eq` (内在形 `C_{S'}(W₁) = W₂`) と
  `Theorem88CaseBData.typePData_W2_eq` (書籍そのままの形)。証明は書籍 pp.46-47 を逐条で追う。

  **副産物 — (8.8.b) の条項欠落を発見・補充**: `Theorem88CaseBData` (旧 `S12_MaximalIII_IV_V`)
  は (b1) の半分と (b2)(b3) しか持たず、(8.9) が要求する (8.4.e)・`S ∩ T = W`・直積性・
  非自明性・(b4) を**欠いていた**。書籍 p.46 と逐条照合して 6 フィールドを追加し、生産側
  2 箇所 (`S14.theorem88_dichotomy` / `FeitThompsonSection16Core`) を実データで充足した
  (仮説への hoist ではない)。これは §2「部分被覆 — bundled statement が条項を運搬していない」
  の実例で、**番号 grep では検出できなかった**。以降の逐条監査で同型を探すこと。

  書籍 p.46:
  > Suppose that case (b) of Theorem (8.8) holds. Then the group denoted by `W₂` in Theorem (8.8)
  > coincides with the group denoted by `W₂` in (8.4.d) with `M = S`.

  証明 (書籍 pp.46–47): `W₂ ⊆ W ⊆ S`、`W` cyclic ゆえ `|W₁|` と `|W₂|` は互いに素 ⟹ `W₂ ⊆ S'`。
  よって `W₂ ⊆ C_{S'}(W₁)`。(8.4.d) を `M = S` に適用して `W₁C_{S'}(W₁)` は可換 ⟹
  `C_{S'}(W₁) ⊆ C(W)`。`W` は (8.4.e) を満たすので `C_{S'}(W₁) ⊆ W`、ゆえに `C_{S'}(W₁) = W₂`。

  Coq 対応 = **`typeP_pairW`** (`coq/theories/PFsection8.v:466`、`of_typeP` 述語で述べる形)。
  (8.8)+(8.9) の合成 `FTtypeP_pair_witness` が同ファイル :712 にある。

- **ステップ 2**: Part II + 補章の census (章内リセット番号なので手作業寄り)。
- **ステップ 3 (進行中)**: Part I の逐条監査を (1.1) から文書順に。1 章ぶん終えるごとに census note を更新。
  - **2026-08-07 時点: §1-§5 完了 (全 55 件)、§6 は (6.4)(6.5)(6.6) 済**。
    正本 = [census note](../notes/peterfalvi/full_formalization_census_2026_08_07.md) §3.5 の各表。
  - **次の入口**: §6 の残り ((6.1)/(6.2)/(6.3)/(6.7)/(6.8) の条項突合、書籍 pp.30/32-37。
    (6.1)-(6.3) の条項は書籍 p.30 を読了済で census note に記録) → §7 = repo `S09`
    ((7.1)-(7.11)、書籍 pp.38-43。ページ画像 p038-p043 の有無を要確認)。
  - **監査手順の正本** = memory `textbook-coverage-audit-failure-modes`。
    **(1) AxiomsCheck の番号コメント → (2) 書籍ページ画像 → (3) 結論の突合** の順。
    🚨「実体が見つからない」を結論にしない (本セッションで 3 回誤判定しかけた)。
  - **未形式化として残るもの**: **(1.7)(b)** (重複度 `e` 付き一般形。可換 inertia 商への
    拡張定理が前提で、巡回版は済・合成列に沿う反復が未実施) の 1 件のみ。
  - **低優先の繰延 2 件**: (3.8) の packaging 差 / (5.6) の書籍仮説 (b)(c) ⟹ 分解存在 の橋渡し。

## 完了条件

Peterfalvi の全番号付き結果 (Part I 169 + Part II + 補章) が**書籍強度**の Lean statement を
持ち、特殊化債務ゼロ。各章の監査結果を census note に記録する。

## 参照

- census 正本: `notes/peterfalvi/full_formalization_census_2026_08_07.md`
- 書籍テキスト: `references/peterfalvi/pdftotext/*.txt` (⚠ 数式は OCR 崩れ → `pages/*.png` を読む)
- Coq 併読: `coq/theories/PFsection<N>.v` (N = 書籍 result 章番号)
