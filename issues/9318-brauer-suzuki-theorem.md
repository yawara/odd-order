---
id: 9318
slug: brauer-suzuki-theorem
title: "Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)"
created: 2026-07-21
---

# Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)

## 背景

Peterfalvi Appendix C Prop 1 (`rankOne_affine_nearField`, NearFields.lean:741)
は honestly-stated sorry で、その未形式化前提の最大物が **Brauer–Suzuki 定理**
(Sylow 2-subgroup が一般化四元数なら G = O_{2'}(G)·C_G(u)、u は中心的 involution;
系として G は単純でない)。Ch.II Theorem B (issue 2053 step (2)) が App C Prop 1
を消費するため、lane b が claim する。

他の前提 2 つは軽い: Huppert III 8.2 (2-rank 1 → Sylow-2 cyclic or
generalized quaternion) と Huppert II 3.2 (normal complement)。

Brauer–Suzuki の証明は指標理論 (block theory or 例外指標)。Isaacs FGT には
無い (Ch.7 の quaternion 関連は別)。文献: Gorenstein Ch.12? / Isaacs
Character Theory Ch.7 (block-free proof by Glauberman?)。repo の指標 infra
(Peterfalvi S04 Dade isometry 系) との接続を調査してから証明戦略を決める。

## やること

- [ ] 証明戦略調査 (Gorenstein §12.1 / Glauberman の block-free 証明 /
      Coq odd-order に相当物があるか grep)
- [ ] cyclic Sylow-2 case (Cayley normal 2-complement で軽い) の確認
- [ ] generalized quaternion case の形式化
- [x] ~~Huppert III 8.2 / II 3.2 の form 化~~ → **lane c が完了 (2026-07-22)**:
      II 3.2 = `GroupTheory/SolvableTwoTransitive.lean`
      `exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` (issue 9404 closed)、
      III 8.2 = `NearFields.lean` `RankOneHypothesis.sylow_two_isCyclic_or_quaternion`
      (two_rank_one → Isaacs Thm 6.11 橋)。いずれも axiom-clean。
- [ ] rankOne_affine_nearField の sorry 解消 (残 gate は BS 本体のみ)

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->
