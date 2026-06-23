---
id: 2022
slug: general-six-two-cross-lane
title: "general six_two (6.2 bound for reducible induced members) — cross-lane gate for §6 producer"
created: 2026-06-23
---

# general six_two (6.2 bound for reducible induced members) — cross-lane gate for §6 producer

## 背景

lane-h relane #7 (issue 2021 RESOLVED) で §6 coherence producer を生産。Pf §11/§13 consumer
(`S13.coherent_S_of_coherent_SH0C` (6.3) / `S13.coherent_quotient_bound` (6.2)) が要求する
**general Hypothesis (6.1) 形** (K=M' solvable, H=HC nilpotent, K≠H) の (6.2)/(6.3) 標準形 assembly を
新 leaf `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` に生産した (commit `27019099`, `0aec0d82`):

- `S07.IsCoherent.subset` (coherence monotonicity) ✅ sorry-free
- `S08.six_three_descent` (general (6.3) minimal-A descent, K≠H) ✅ sorry-free
- `S08.six_three_index_bound_general` (general (6.3) per-step index bound) ✅ sorry-free

**両 consumer obligation は単一の gate `general six_two` に reduce 済**。

調査の結論 (notes/peterfalvi/s06_standalone_62_63_producer.md §4):
general (6.2)/(6.3) の PIECES は既に general 形で `S08_CoherenceCorePart1/2` に存在し
(`coherentDegreeSumBound_of_not_coherent` = (5.6) contrapositive over `S04.Hypothesis`、
`theta_degree_le_index_mul_sqrt_index` = θ-bound、degree-sum、nilpotent-central、√-arithmetic 全 general)、
フル assembled な `six_two`/`six_three` (CorePart2) は SibleyDadeHypothesis (K=H) 上。lane-h は K≠H 分離の
assembly を完了した。**唯一残る深い gate が general `six_two`**。

## やること

- [ ] **general `six_two`** を生産: K solvable normal + induced family `S = {Ind_K^L θ}` (可約 member 含む)
      に対する (6.2) bound `|K:A| − 1 ≤ 2|L:C|√|C:D|` (および C=D 特殊化 `|K:A|−1 ≤ 2|L:C|`)。
- [ ] これを `six_three_index_bound_general` に食わせて `six_three_descent` の `h62` を discharge、
      lane-c の §11 obligation を完全 unblock。

## なぜ cross-lane か

general `six_two` の核 = `coherentDegreeSumBound_of_not_coherent` ((5.6) contrapositive、general 既存) の
**orthonormality / support / generation 仮説を induced family の可約 member について discharge** すること。

- Sibley 版 (`six_two_index_bound`) は `hF : IsFrobeniusGroup L H W₁` で "Ind_K^L θ は irreducible" を保証し
  これらの仮説を `sMember_index_le_two_psi` で discharge する。
- §11 設定 (K=M' solvable) では family に可約 member (μⱼ column 等) が含まれ、その (5.2.d) R(χ) 構造は
  **§10-12 の muGrid / columnSum 機構** (S10/S12, lane-b/c 領域) で扱われる。
- ⟹ general `six_two` は §5 ((5.6) hyps) + §10-12 (family の可約 member 構造) に entangle し、
  lane-h の §6/§8 単独スコープでは閉じない。

## 完了条件

- general `six_two` (上記) が sorry-free で landed し、`six_three_index_bound_general` 経由で
  `six_three_descent` の `h62` が実 discharge される。
- lane-c が `S13.coherent_S_of_coherent_SH0C` / `coherent_quotient_bound` を本 producer cite で閉じられる
  (別途 lane-c 側で SOf/Sset の pin = §6 への bridge が要; notes §6 参照)。

## 参照

- producer note: `notes/peterfalvi/s06_standalone_62_63_producer.md` (§4 design question RESOLVED, §6 bridge, §7-8 残作業)
- producer leaf: `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean`
- general pieces: `OddOrder/Peterfalvi/S08_CoherenceCorePart1.lean`
  (`coherentDegreeSumBound_of_not_coherent`:2451, `theta_degree_le_index_mul_sqrt_index`:557,
  `sum_div_normSq_induce_kernelFilter_eq`:2526, `exists_coherentBreakPair`:952)
- Sibley assembled: `OddOrder/Peterfalvi/S08_CoherenceCorePart2.lean` (`six_two`:3786, `six_three`:3924)
- consumer: `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean` (`coherent_S_of_coherent_SH0C`:188, `coherent_quotient_bound`:215)
- relane #7 / lane state: issue 2021 (RESOLVED), [[lane-h-driving-wielandt-91]]

## 2026-06-23 HUB 応答 — cite-policy で進行、reassignment 不要

hub 監査: 本件は reassignment あおぎでなく cross-lane 依存の文書化と判断。**lane-h は relane #7 継続のまま
general six_two を自 leaf (S08_Theorem62_63_Standalone) で生産**する。方針:
1. **§10-12 muGrid/columnSum (S10/S12) の既存 lemma を cite** して可約 member の R(χ) / orthonormality /
   support / generation 仮説を discharge ([[feedback-cite-sorried-lemmas-if-signature-correct]]; sorried sig でも可)。
2. 必要な §10-12 signature が **未 export / 未 stated** なら、lane-b (S12 owner) / lane-c に **targeted な
   signature 要請 issue** を立て、当面は sorried cite で general six_two の assembly を先に積む (手を止めない)。
3. 既存 S10/S12/S05-S08 本体は触らず cite のみ・生産は自 leaf 隔離 (lane-b/c 復帰時の衝突回避)。
本 issue は tracking として open 維持 (general six_two landing で close)。
