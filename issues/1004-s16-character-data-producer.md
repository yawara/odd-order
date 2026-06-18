---
id: 1004
slug: s16-character-data-producer
title: "Section16Inputs: section16CharacterData producer (Pf §13, lane-b)"
created: 2026-06-18
---

# Section16Inputs: section16CharacterData producer (Pf §13, lane-b)

## 背景

2026-06-18 post-§14 監査で判明した真の long pole = `Section16Inputs` producer の分配
(skeleton commit `80f9aa39`)。本 issue は **character 側 (Peterfalvi §13 coherent Dade grid)**
担当ブロック。これが lane-b の (6.8) coherence が最終的に payoff する地点
([[ft-path-policy]] の "deferred-payoff prerequisite") = (6.8) は orphaned ではなく本 producer
の上流前提。**当面は deferred** ((6.8) capstone と Pf §10-13 char API が landing するまで埋められない)。

## やること

- [ ] `section16CharacterData_of_isMinimalSimpleOdd hG mp tp : Section16CharacterData mp tp`
      (`OddOrder/FeitThompson.lean:280`, 現 `sorry`) を実証明化する。
- [ ] 入力 = 極大対 `mp` + 型 P 構造 `tp` (lane-g/lane-f が構成)。
- [ ] 内容 = Dade 指標 grid: `Sset`/`Tset`/`A0S`/`A0T`、`tauS`/`tauT`/`tau3`
      (`IntegralCharacterMap`)、`omega`/`mu`/`nu` grid (`Fin tp.q → Fin tp.p → ClassFunction …`)、
      符号 `delta`/`deltaPrime`、誘導恒等式 `mu_definition`/`nu_definition` (Pf (13.1.d/e))。
- [ ] feeder = Peterfalvi §13 coherent set theory ← (6.8) coherence
      (`S08_CoherenceTheorems.lean:59` `sibleySetup_is_coherent`) + Pf §3-9 char API + §10-13。

## 完了条件

`section16CharacterData_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。
(深い character theory 依存ゆえ最後発の見込み。)

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:235` (`structure Section16CharacterData mp tp`),
  `:280` (producer)
- 上流前提: (6.8) `sibleySetup_is_coherent` (`S08_CoherenceTheorems.lean:59`, lane-b 現タスク)
- 関連: 8014 (maximalPair) / 7005 (typeP_structure) / 2009 (POLE-2)
