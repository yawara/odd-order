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

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W2)
- 主所有: `OddOrder/Peterfalvi/S14_MaximalI.lean`
- 関連: `notes/peterfalvi/s10_13_maximal_structure.md`、issue 2018 (§13 char direction)
