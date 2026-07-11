---
id: 9084
slug: tgapcross-beta-support-redirect
title: "S16 TGapCross の (13.18.a) β-support 系 3 定理を S15 正本へ redirect (hub 裁定)"
created: 2026-07-12
---

# S16 TGapCross の (13.18.a) β-support 系 3 定理を S15 正本へ redirect (hub 裁定)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# 背景 (lane b、2026-07-12、/loop iter 4)

(13.18.a) の 2 つの μ-値入力が S15 で proven 化した (hmuW1 = `mu_row0_apply_eq_one_of_mem_W1`
[CountingLayer]、hmuD = `mu_row0_apply_eq_zero_of_mem_derived_not_mem_P` [OrderDetermination])
のに伴い、b は S15_SAndT の sorried grid form `betaGrid_support` を Coq-faithful exact form
(PVSbeta: supp(β_j) ⊆ P^#∪V_S^S) に修正して**仮説なしで完全証明**した (commit 400e8649)。

この際、S16_NonExistenceG/TGapCross.lean (lane c の成果、commit f686612e 系) にあった
S15-level の 3 定理と**一時重複**が生じている:

| S16 TGapCross (hypothesis-parametrized) | S15_SAndT (新正本、仮説なし) |
|---|---|
| `PW1_index_eq_u` (S15.Hypothesis 直取り) | `PW1_index_eq_u` (同一 statement/証明) |
| `betaGrid_apply_one_eq_zero` (同上) | `betaGrid_apply_one_eq_zero` (同一) |
| `betaGrid_support_sharpP_union_typePV_of_values` (hone/hmuD/hmuW1 仮説) | `betaGrid_support` (仮説なし、証明同構造) |
| `betaGrid_support_sharpP_union_typePV_of_mu_values` (hmuD/hmuW1 仮説) | (同上に包含) |

## hub への裁定依頼

- **(a) redirect**: TGapCross の 4 定理を S15 正本の cite に置換 (namespace S16 → S15、
  仮説 hmuD/hmuW1 は proven 供給で discharge)。TGapCross:652 の
  `…_of_mu_values` caller と AxiomsCheck:3437 の assert の追従込み。実施 owner は
  c (self) or hub。b は S15 側正本を保守。
- **(b) (14.9) endpoint の仮説 discharge**: TGapCross の (14.9) cross-Dade 系
  (`tSideDadeMap_inner_tauSbetaGrid_eq_zero…` :778 近辺) が hmuD/hmuW1 を仮説で取る形の
  まま — S15 の proven 2 補題で discharge した corollary 化が可能になった (これも c-side)。

## 参照
- S15 正本: OddOrder/Peterfalvi/S15_SAndT.lean (commit 400e8649)
- 2 入力: CountingLayer `mu_row0_apply_eq_one_of_mem_W1` / OrderDetermination
  `mu_row0_apply_eq_zero_of_mem_derived_not_mem_P` (commits 09914a59 / a3895f0e)
- 経緯: issues/2038-bfrontier-shift-bg-done.md 2026-07-12 節
