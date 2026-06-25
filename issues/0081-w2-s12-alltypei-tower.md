---
id: 81
slug: w2-s12-alltypei-tower
title: "W2 (lane-c): §12 all-Type-I 非存在 tower → theorem88_caseB_holds"
created: 2026-06-25
---

# W2 (lane-c): §12 all-Type-I 非存在 tower → theorem88_caseB_holds

## 背景

FT フロンティア再設計 (2026-06-25 relane #9、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`)
の **フロント W2** = lane-c 担当。Arm A の mp 側。§12 char cluster。上流 coherence producer
((5.7)/(6.2)/(6.3)/(6.8)) は完成済ゆえ **consumer 側を埋める段階** — lane-c が直前まで作った
(5.7) `coherent_of_constant_degree` がここで消費される見込み (供給→消費 wiring)。

## やること

- [ ] `theorem88_caseB_holds` (`OddOrder/Peterfalvi/S14_MaximalI.lean:1040`) を埋める
      = mp 構成で all-Type-I 枝を排除 ((8.8) の全 Type-I ケースが impossible)。
- [ ] `typeI_frobenius` (S14_MaximalI.lean:189, Pf (12.7)) = 各 Type-I maximal は kernel M_F の Frobenius。
      (W4 の §15 が cite する partner でもある。)
- [ ] 背後の §12 tower 12.2–12.16 (14 sorry: Dade isometry / coherence / ρ-congruence) を上流から順に。

## 完了条件

`theorem88_caseB_holds` が sorry-free + axiom-clean。mp producer の all-Type-I 排除が解消。

## 進捗ログ

### 2026-06-25 (lane-c 再開): §12 型 I Dade foundation を de-opacify + 構成子

調査 (2 Explore agent + 原文 `04.14_*.mmd` = 書籍 §12 精読) で §12 tower の actionability を確定:
深い char leaves ((12.2)-(12.5),(12.14),(12.15)) は Clifford 分解 + lane-b char API gate、
群論 tower ((12.10)-(12.12)) は (11.9.c)/(9.7.b)/(8.6.a) un-isolated/char-gate。
**ungated で最上流の honest 起点 = 型 I `Hypothesis` の foundation 化**と判断 (S12 の
`exists_hypothesis_of_typeIIIorIVorV` を template に、完成署名の `dadeSupportHypotheses_typeI`
= (8.15) を使用)。

**landed (commit 予定)**:
- `S14.Hypothesis` を de-opacify: free field `tau`(Dade isometry=最も hard な hoisted
  content)/`Sset`/`A`/`R` + opaque Prop 5 個を除去 → genuine carrier
  `{finiteG, maximal, typeI, dadeData : (8.15) DadeSupportHypothesisData, hconj}`。
  `tau`/`Sset`/`A`/`H`/`Hprime` は genuine derived def 化 (`dadeIntegralCharacterMap` /
  L_F からの誘導 / `supportInSubgroup`)。
- `exists_typeI_hypothesis` (sorry-free 本体、(8.15) を cite ゆえ axiom = sorryAx; 型 P
  アナログと同 honest status、AxiomsCheck 非登録)。→ carrier 構成可能性を実証。
  **S15 `TypeIOrthogonalityData.typeISetup` の構築を unblock (W4 を補助)**。
- (12.4)/(12.5) の opaque Prop 仮説を genuine 直交性 `∀χ∈S, ∀α∈R(χ), ⟨ψ,α⟩=0` に置換。
- helper `conj_smul_centralizer_singleton`/`supportKernel_conj_invariant` を S14 に複製
  (S12 で private; cross-lane 編集回避)。
- full build 3884 green。

**残 (downstream, 引き続き W2)**: (12.6) coherence dispatch (Sibley/(5.7)/(6.5.c) carrier)、
群論 tower (12.10)-(12.12) (lane-b char/un-isolated §8 gate)、char leaves (12.2)-(12.5),
(12.14)-(12.16)、エンドポイント `typeI_frobenius` (12.7) / `theorem88_caseB_holds` (12.17, +(7.11))。

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W2)
- 主所有: `OddOrder/Peterfalvi/S14_MaximalI.lean`
- 関連: `notes/peterfalvi/s10_13_maximal_structure.md`、issue 2018 (§13 char direction)
