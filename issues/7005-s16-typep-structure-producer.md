---
id: 7005
slug: s16-typep-structure-producer
title: "Section16Inputs: section16TypePStructure producer (BG §14, lane-f)"
created: 2026-06-18
---

# Section16Inputs: section16TypePStructure producer (BG §14, lane-f)

## 背景

2026-06-18 post-§14 監査で判明した真の long pole = `Section16Inputs` producer の分配
(skeleton commit `80f9aa39`)。本 issue は BG §14 type-P duality 担当ブロック。
**`typeP_duality` は既に proved** (`S14_TypePCounting.lean:7961`, sorry-free + axiom-clean)
ゆえ、本 producer はその proved 定理を cite して構成できる見込み = 良い lead-in。

## やること

- [ ] `section16TypePStructure_of_isMinimalSimpleOdd hG mp : Section16TypePStructure mp`
      (`OddOrder/FeitThompson.lean:272`, 現 `sorry`) を実証明化する。
- [ ] 入力 = 極大対 `mp : Section16MaximalPair G` (lane-g が構成)。
- [ ] 内容 = 型 P 双対構造: `W1 W2 W U V : Subgroup G`、`W = mp.S ⊓ mp.T = W1 ⊔ W2` cyclic、
      `W1 ⊓ W2 = ⊥`、`W1`/`W2` の可換性、導来部分群分解 `S_deriv_eq_PU`/`T_deriv_eq_QV`、
      `W1`/`W2` の正規化条件、素数 `q p` と counting params `u v c d` + 位数等式 + `q_lt_p`。
- [ ] feeder = BG §14 `typeP_duality` (`S14_TypePCounting.lean:7961`) — W cyclic, W₁/W₂,
      補 U/V, counting を供給。`q_lt_p` は (14.1) 由来。

## 完了条件

`section16TypePStructure_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:196` (`structure Section16TypePStructure mp`),
  `:272` (producer)
- 既証明 input: `OddOrder.BG.Ch4.S14.typeP_duality` (`S14_TypePCounting.lean:7961`)
- 関連: 8014 (maximalPair, lane-g, 上流) / 1004 (character_data, lane-b, 下流) / 2009 (POLE-2, lane-h)
- 旧タスク Wielandt (9.1) `CoprimeAction.lean` は orphaned 判定で park (issue 7004 は据え置き)
