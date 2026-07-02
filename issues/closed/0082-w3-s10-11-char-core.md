---
id: 82
slug: w3-s10-11-char-core
title: "W3 (lane-b): §10–11 中心 char 核 (11.9.b card_kappaHall + no_typeV)"
created: 2026-06-25
---

# W3 (lane-b): §10–11 中心 char 核 (11.9.b card_kappaHall + no_typeV)

## 背景

FT フロンティア再設計 (2026-06-25 relane #9、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`)
の **フロント W3** = lane-b 担当。Arm A の **臨界路最狭点・最深** — `feitThompson` の **唯一の bare sorry**
を含む。issue 2020 を保持。上流 coherence producer 完成済ゆえ actionable-now。

## やること

- [ ] **唯一の bare FT sorry**: `card_kappaHall_lt_of_isTypeIIIorIV` (`OddOrder/FeitThompson.lean:426`,
      Pf (11.9.b)) の honest 証明 — §11 coherence/Dade-norm engine を要する。Type III/IV maximal S で
      `|K*| < |K|` (q>p) を強制。
- [ ] `no_typeV_maximal` (Pf (10.10)) を `S_not_coherent` (S12_MaximalIII_IV_V.lean:5484, 10.8) +
      `typeV_forces_coherence` (S12:5786, 10.10) から締める (§7 ρ-machinery + (8.8) Type-II partner)。
- [ ] §10 Dade-support: `dadeSupportHypotheses_typeP` (S10_MinimalSimpleStructure.lean:310, 8.15)、
      `exists_typeII_maximal_with_w2_of_typeP` (S10:148, 8.8 partner)。

## 完了条件

`card_kappaHall_lt_of_isTypeIIIorIV` + `no_typeV_maximal` が sorry-free。**`FeitThompson.lean` の
bare sorry が消える** (POLE-1 char 核完了)。

## ⚠ on/off-path 精密区別

(11.9.b) の証明が cite する §11/§13 の coherence/Dade-norm **補題は on-path** (構築/再利用可)。だが
Peterfalvi **内部の §13 type-III/IV 矛盾 endpoint** (`S13_MaximalIII_IV` の `final_typeIII_conclusions` 系)
は honest 構成が **App.C/W4 経由を採ったため off-path** (FeitThompson が import すらしない代替路)。
**内部矛盾 endpoint を目標にしない。**

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W3)
- 主所有: `OddOrder/Peterfalvi/{S10,S11,S12,S13}*.lean` + `FeitThompson.lean:426` + §3–9 char supply
- 関連: issue 2020 (この core の旧 issue)、`notes/peterfalvi/s10_13_maximal_structure.md`

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

W3 charter superseded: `FeitThompson.lean` は comment-strip で実 sorry 0 (検証 2026-07-02) — 本文の「:426 唯一の
bare sorry」は現状と不一致。現実の bare spine sorry = `S12.exists_zeta_residual_not_orthogonal`
(S12_MaximalIII_IV_V.lean:2645、lane a の Pf 11.8 frontier)。「内部矛盾 endpoint を目標にしない」の注意のみ引き継ぎ有効。
canonical = notes/meta/ft_lane_reallocation_2026_06_28.md。
