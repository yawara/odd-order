---
id: 62
slug: bg-thm106-p-length-one
title: "BG Thm 10.6 proper subgroups have p-length one"
created: 2026-06-06
---

# BG Thm 10.6 proper subgroups have p-length one

## 背景

BG §10 の次 frontier。issue 0061 で reduced Thm 10.2 (`isHall_Msigma_Malpha`) が完成し、
Thm 10.6 (`proper_hasPLengthOne`) が解禁された。これは §11-§13 で p-length one 仮定を供給する
BG 本体 critical path の gateway。

対象 Lean surface:
`OddOrder.BG.Ch3.S10.proper_hasPLengthOne`
(`OddOrder/BG/Ch3_MaximalSubgroups/S10_MalphaMsigma.lean`)。

## 現状 (2026-06-06)

- [x] **maximal subgroup の `p∉α(M)` branch 完成**:
  `maximal_hasPLengthOne_of_not_mem_alpha` を追加。
  `p∈π(M)` なら `p∉α(M)` から `pRank M p≤2` を出し、BG Thm 4.18(e)
  (`solvable_structure_of_pRank_le_two`) で `hasPLengthOne`。
  `p∉π(M)` なら `|M/O_{p',p}(M)| ∣ |M|` から直接 `hasPLengthOne`。
  `lake build OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma` green、axioms =
  `[propext, Classical.choice, Quot.sound]`。
- [x] **`p∈α(M)` hard branch の Hall-α support 完成**:
  `sylow_le_Malpha_of_mem_alpha_of_isHall` により `p∈α(M)` の Sylow-p subgroup of `M` は
  `M_α` に吸収される。
  `not_dvd_card_quotient_Malpha_of_mem_alpha_of_isHall` により `p∈α(M)` なら
  `p∤|M/M_α|`。既存 `rank_quotient_Malpha_le_two_of_isHall` もこの public lemma を使う形に整理。
  S10 leaf build green、axioms = `[propext, Classical.choice, Quot.sound]`。

## やること

- [ ] `proper_hasPLengthOne` の maximal reduction を実装する:
  `H<⊤` から `H≤M`, `M∈maximalSubgroups G` を取り、`M` の p-length one を `H` へ降ろす
  subgroup-closure が必要。
- [ ] `p∈α(M)` hard branch を実装する:
  BG proof は complement `K` to `M_α` in `M` を取り、Thm 10.2 の `M_α≤M'` と Lemma 6.3(a) で
  `M_α=[M_α,K]`、さらに Lemma 10.4 と BG Thm 3.6 で `[M_α,K]` の p-length one を得る。
- [ ] 必要に応じて Lemma 10.4 の該当 fragment
  (`∃ x∈Q` order `q` with `C_{M_α}(x)` a Z-group) を先に切り出す。
- [ ] `proper_hasPLengthOne` の `sorry` を削除し、S10 leaf build と axiom check を通す。

## 完了条件

`proper_hasPLengthOne` の `sorry` が消え、
`lake build OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma` が成功し、主要 theorem の axioms が
標準3公理 `[propext, Classical.choice, Quot.sound]` のみであること。

## 参照

- notes: `notes/bg/s10_malpha_msigma.md` Theorem 10.6 section。
- closed prerequisite: `issues/closed/0061-bg-thm102-hall-structure.md`。
- source: `references/bg/local-analysis.mmd` L2779-L2783。

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

Thm 10.6 landed: `proper_hasPLengthOne` (S10_BetaRadicalCore.lean:39) 証明済、ファイル実 sorry 0 (検証 2026-07-02)。
置き場所は issue 記載の S10_MalphaMsigma でなく `S10_BetaRadicalCore.lean` に移動 (10.6→10.7→10.8 直列スパインの起点)。
