---
id: 2034
slug: caseb-chardata-wside-restate
title: "CharacterDegreeData の W-side restate — lambda_mem (Sset=∅ で反証可能) 除去 + free Prop の honest 化"
created: 2026-07-05
---

# CharacterDegreeData の W-side restate — lambda_mem (Sset=∅ で反証可能) 除去 + free Prop の honest 化

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->
## 判定 (hub 裁定 2026-07-02 の「到達時に W-side restate or retire」を執行)

**結論 = restate** (retire 不可: (13.3)/(13.4) は `T_side_caseB_facts` (S16) 経由で on-path、
(13.10) の λ-package も Pf 原文が (13.6) の λ を直接使う)。

## 発見 (soundness bug)

`CharacterDegreeData.lambda_mem : lambda ∈ hyp.Sset` — spine
(`section16CharacterData_of_isMinimalSimpleOdd`) は **`Sset := ∅`** (vestigial placeholder,
issue 1004 裁定) を供給するため、spine の hyp では `CharacterDegreeData hyp` が
**uninhabited** → `character_degree_analysis : ∃ data, …` は**反証可能** (unprovable)。
grep 検証: `chars.lambda_mem` の cite は **0** (S16_PairingCoherence の `typeIHyp.Sset` は
別構造)。

## やること

- [x] `lambda_mem` field 除去 (0 cites、純 soundness fix)
- [x] `lambda_irreducible : Prop` (free) → `IsIrreducibleCharacter lambda` に materialize
- [x] `lambda_induced_from_PC_linear : Prop` (free) → 実 ∃-statement
      (∃ linear θ : CF(H.subgroupOf S), degree-1 irreducible ∧ lambda = Ind θ) に materialize
      — consumers は `hlam` を opaque に持ち回るだけなので signature 影響ゼロ、
      construct するのは sorried `character_degree_analysis` のみ
- [ ] 残 free Props (`mu_j_linear_induced` / `no_lambda_forces_caseB_S` / `mu_tau1_formula` /
      `sign_flip_exception`) の honest 化 — (13.3.a/c/d) の τ₁↔η-grid formula 設計と一体
      (tau1S の W-side 意味論: μⱼ^{τ₁} = δ Σᵢ η_{i1} 型の formula field 群)。
      (13.3)-cluster atom 群 (exists_lambda_index / lambda_tau1_norm_one /
      lambda_tau1_apply_mul_eq_zero / eta10_cCoeff_orthogonal) の実証明もこの設計に乗る。

## 参照

- notes/peterfalvi/s16_w4_char_cascade.md「HUB 裁定 (2026-07-02 全体レビュー)」§2
  (S-side τ₁ 形の処分) + cont.⁴⁴ (T_side_caseB_facts route 検証)
- closed/2033 (この判定に到達した (1.10)-合同層 real 化の後続)
