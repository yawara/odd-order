---
id: 2010
slug: pf-s10-13-maximal-cite-split
title: "H cite-split chunk: Peterfalvi §10-13 maximal-subgroup structure (cite深char)"
created: 2026-06-19
---

# H cite-split chunk: Peterfalvi §10-13 maximal-subgroup structure (cite深char)

## 背景

2026-06-19 cite-split で H を POLE-2 から再配向。POLE-2 (`field_normalizer_structure`) は
dispatch + 両主枝 sorry-free 化済で残は §13 char (Lane B) に bottom-out ゆえ parked
([[ft-endgame-two-poles]] issue 2009)。H は深い char を cite で切り、強み(構造群論)が効く
**Peterfalvi §10-13 maximal-subgroup 構造**(~37 sorry)を大チャンクで取る。
設計正本 = `notes/meta/cite_split_three_lanes.md`。

## やること

構造論で H が証明 (深い char 入力に当たったら証明せず named obligation に hoist して cite):

- [ ] **§10** (`S10_MinimalSimpleStructure.lean`):
  - [ ] `hall_maxNilpotentNormalHall_and_mainSubgroup`
  - [ ] `typeF_frobenius_of_card_eq_exponent` / `typeF_card_U0_eq_exponent`
  - [ ] `typeII_A_sets_TI` / `typeII_A_sets_normalizer`
  - [ ] `typeI_or_typeII_centralizer_unique`
  - [ ] `escapingCentralizers_control`
  - [ ] `bgTheoremE_cover_data`
- [ ] **§11-12** (`S11_MaximalII_III_IV.lean` / `S12_MaximalIII_IV_V.lean`):
  - [ ] maximal type II/III/IV/V 分類
  - [ ] `no_typeV_maximal` (10.10) — `IsCoherent` を cite
  - [ ] `theorem88_caseB_prime_orders` (10.11)
- [ ] **§13** (`S13_MaximalIII_IV.lean`): 構造部

## cite で切る (B 供給, named obligation / 既存 sorried producer の cite)

- `dadeSupportHypotheses_typeI` / `dadeSupportHypotheses_typeP` (Dade isometry)
- `typeV_forces_coherence` の `IsCoherent` 結論 (= S07 coherence, ultimately (6.8))
- `support_mutual_exclusion`

## 完了条件

§10-13 の構造系 sorry が landing (深い char は named obligation として残置・cite)。
full build green + axiom-clean。leverage: 10.10/10.11 が POLE-1 tp producer (F) を unblock。

## 参照

- 設計: `notes/meta/cite_split_three_lanes.md`
- parked: issue 2009 (POLE-2 field_normalizer_structure)
- leverage 先: [[s16-typep-producer-unfillable]] (10.11 → tp producer prime tail)
- 上流 char gate: issue 1004 (characterData) / Lane B (6.8)
