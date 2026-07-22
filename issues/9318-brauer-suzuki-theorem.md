---
id: 9318
slug: brauer-suzuki-theorem
title: "Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)"
created: 2026-07-21
---

# Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)

## 🎯 HUB RULING (2026-07-22, ユーザー裁可): claim owner **b → c 移管**

本 issue の owner を **lane c** に移管する。c の primary frontier = 本 issue。根拠:

1. **b は未着手** (2026-07-22 実測: main..b に BS 関連 commit 0、調査 checkbox 未チェック)
   かつ issue 2053 Theorem B の 17-step campaign 進行中 — b は 2053 に専念する。
2. **c は既に前提 2 件を完了済** (下記 checkbox、issue 9404 closed) で文脈を持っている。
3. **消費点 `rankOne_affine_nearField` (NearFields.lean) は c 所有ファイル** — 自所有の
   gate を自分で外す形になり、gated-frontier 問題も同時に解消。
4. c の BG scope は closed (Thm A(6)/(7) landing、実 sorry 0) で live frontier が空だった。

b 側は Theorem B step (2) で App C Prop 1 を **sorried-cite** してよい (signature は
`rankOne_affine_nearField` で確定済、[[feedback-cite-sorried-lemmas-if-signature-correct]])。
BS 本体の置き場所は一般有限群論ゆえ `OddOrder/GroupTheory/**` (shared) を第一候補とし、
新 leaf は claim-before-build どおり本 issue が claim を兼ねる (c は 9400 番台で追加
claim を切ってもよい)。step 1.5 の所有 regex 変更は不要 (shared_re / c_re で被覆)。

## 背景

Peterfalvi Appendix C Prop 1 (`rankOne_affine_nearField`, NearFields.lean:741)
は honestly-stated sorry で、その未形式化前提の最大物が **Brauer–Suzuki 定理**
(Sylow 2-subgroup が一般化四元数なら G = O_{2'}(G)·C_G(u)、u は中心的 involution;
系として G は単純でない)。Ch.II Theorem B (issue 2053 step (2)) が App C Prop 1
を消費するため、lane b が claim する。~~(claim 経緯)~~ → **2026-07-22 に c へ移管
(冒頭 HUB RULING 参照)**。

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
