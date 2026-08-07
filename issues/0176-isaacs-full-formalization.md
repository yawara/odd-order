---
id: 176
slug: isaacs-full-formalization
title: "Isaacs 完全形式化キャンペーン (逐条監査)"
created: 2026-08-08
---

# Isaacs 完全形式化キャンペーン (逐条監査)

## 位置づけ

[issue 0172](closed/0172-peterfalvi-full-formalization.md) (Peterfalvi 全 284 件) が
2026-08-08 に完了したので、**同じ逐条監査を Isaacs に適用する**。3 冊スコープの文書順
(Isaacs → BG → Peterfalvi) に従い、次は最上流の Isaacs。

方法論は 0172 と同一:

> 書籍ページ画像で条項を確定 → repo の statement と突合 → 部分被覆/特殊化/言及のみを補充

## 実測ベースライン (2026-08-08)

### 書籍側の番号 census

`references/isaacs/finite-group-theory.pdftotext.txt` から機械抽出
(⚠ OCR が `T h e o r e m` / `2 . 1 4 .` のように文字・数字を分解するので、**空白許容の
正規表現が必須**。素朴な `^\d+\.\d+\.\s*(Theorem|...)` だと 29 件取りこぼす)。

| 章 | 件数 | 欠番 |
|---|---|---|
| Ch.1 Sylow | 46 | なし |
| Ch.2 Subnormality | 20 | なし |
| Ch.3 Split Extensions | 36 | なし |
| Ch.4 Commutators | 38 | なし |
| Ch.5 Transfer | 30 | なし |
| Ch.6 Frobenius Actions | 24 | なし |
| Ch.7 Thompson Subgroup | 8 | なし |
| Ch.8 Permutation Groups | 44 | なし |
| Ch.9 More on Subnormality | 31 | なし |
| Ch.10 More Transfer | 28 | なし |
| **合計** | **305** | **各章 1..max が連続、欠番ゼロ** |

種別は全件 **Theorem / Lemma / Corollary** (Theorem 135 / Lemma 105 / Corollary 65)。
Definition / Example / Notation は別番号系ではなく同じ連番に混ざらない。

### repo 側の cite 突合

`OddOrder/**/*.lean` の docstring を grep (`OddOrder/Isaacs/**` は素の `N.M`、それ以外は
同一行に "Isaacs" を要求):

| 層 | 件数 |
|---|---|
| cite あり | **292 / 305** |
| **cite ゼロ** | **13** — すべて Ch.8 |

cite ゼロ 13 件 = **8.11, 8.12, 8.13, 8.14, 8.15, 8.17, 8.19, 8.20, 8.21, 8.22, 8.27, 8.28, 8.30**
= block / primitivity / Jordan set のクラスタ + `Aₙ` 単純性。

⚠ **cite ゼロ ≠ 未形式化** (0172 の最大の教訓)。実際、**mathlib に
`MulAction.IsBlock` / `IsPreprimitive` / `Mathlib/GroupTheory/GroupAction/Jordan.lean` が在り**、
repo の `Ch08_PermutationGroups` も既に `IsPreprimitive` を使っている。⟹ 多くは
**mathlib 被覆**の可能性が高く、その場合の正しい対処は CLAUDE.md のラッパー方針どおり
「薄いラッパーを書かず、**対応表を section docstring か `notes/` に記録**」。

## ⚠ この census が測っていないもの (0172 と同じ)

「cite あり」= 番号が docstring に現れるだけ。番号 grep で検出できない残債:

1. **特殊化債務** — 書籍より狭い仮説で述べている
2. **部分被覆** — (a)(b)(c) の一部だけ / bundled statement が条項を運搬しない
3. **言及のみ** — 散文 cite で statement が無い
4. **mathlib 被覆の未記録** — Isaacs 固有 (Peterfalvi には無かった型)。書籍の結果が
   mathlib にそのまま在る場合、repo に実体が無くても**被覆済**だが、対応が記録されていないと
   監査で「未形式化」に誤分類される

⟹ 本体は番号埋めでなく逐条照合。

## 作業手順

- [x] **ステップ 1 ✅ 完了 (2026-08-08)**: cite ゼロ 13 件を分類した。対応表の正本 =
      [`notes/isaacs/ch08_permutation.md`](../notes/isaacs/ch08_permutation.md)。

      | 分類 | 件数 | 内訳 |
      |---|---|---|
      | **mathlib 被覆** | **12** | 8.11-8.15, 8.17, 8.19-8.22, 8.27, 8.30 |
      | **真の未形式化** | **1** | 8.28 → **2026-08-08 に形式化済** (下記) |

      ⭐ **8.20 は mathlib のほうが一般** — 書籍は「部分群 `H` の軌道 `X` で `H` が原始的、
      `|X| > |Ω|/2`」だが mathlib の `IsPreprimitive.of_card_lt` は**任意の同変写像**
      `f : X →ₑ[φ] Y` で `|Y| < 2·|range f|`。
      ⚠ **8.21 は mathlib のほうが狭い** — 書籍は任意の 2 つの Jordan 集合 `X, Y` だが
      mathlib の `is...ofFixingSubgroup_inter` は 2 つ目を `g • s` (translate) に限定。
      消費点 (8.22) は translate 版で足りるので実害は無いが、**mathlib 側の特殊化債務**。

- [x] **8.28 を形式化 (2026-08-08)**。`OddOrder/Isaacs/Ch08_PermutationGroups/SymmetricNormalSubgroups.lean`:
      ```
      center_perm_eq_bot                        Z(Sym Ω) = 1  (|Ω| ≥ 3)
      normal_perm_eq_bot_or_alternating_or_top  (8.28) 本体
      ```
      ⚠ `Z(Sym Ω) = 1` も mathlib に無かった (mathlib の
      `Equiv.Perm.alternatingGroup.center_eq_bot` は**交代群**の中心)。両方 axiom-clean。
- [x] **census note を新設 (2026-08-08)**:
      [`notes/isaacs/full_formalization_census_2026_08_08.md`](../notes/isaacs/full_formalization_census_2026_08_08.md)
- [ ] **ステップ 2 (進行中)**: Ch.1 から文書順に逐条監査。
      - **Ch.1 の第 1 パス完了 (2026-08-08)**: 46/46 に cite あり。docstring の**アンカー位置**
        (`**Isaacs Thm 1.N**`) に cite が無い 9 件 (1.1, 1.5, 1.6, 1.7, 1.10, 1.11, 1.17,
        1.24, 1.25) を調査し、**9 件すべて mathlib 被覆**と確定 (対応表は census note §3)。
      - ⚠ **1.24 の「正規」条項は要確認** — 書籍は `L ⊴ P` を主張。mathlib の
        `exists_subgroup_card_pow_prime` が正規性まで返すかは未確認。
      - ⬜ **残り 37 件の条項ごとの突合は未実施**。とくに 1.12-1.15 / 1.18-1.22 / 1.30-1.31 は
        **1 つの file-header docstring が複数番号を列挙**しているだけなので、番号ごとの
        statement の有無を個別確認する (Peterfalvi の「file docstring の散文が定理の代わり」型)。
      - 1 章ぶん終えるごとに census note を更新して commit。

## 完了条件

Isaacs の全 305 件が **書籍強度**の Lean statement を持つか、**mathlib 被覆として対応が
記録されている**。特殊化債務ゼロ・部分被覆ゼロ。各章の監査結果を census note に記録する。

## 参照

- 前身: [issue 0172](closed/0172-peterfalvi-full-formalization.md) (Peterfalvi、完了)
- 書籍: `references/isaacs/finite-group-theory.pdf` (⚠ **PDF ページ = 書籍ページ + 13**)、
  ページ画像は `references/isaacs/pages/`
- ⚠ 誤判定様式は 0172 で 9 件検出済 — 番号表記の揺れ / assembly を endpoint と誤認 /
  stale な自己注記の連鎖。**自分の過去の「未形式化」ラベルを一次証拠にしない**。
