---
id: 2009
slug: s16-field-normalizer-pole2
title: "POLE-2: field_normalizer_structure (Pf 14.2, lane-h)"
created: 2026-06-18
---

# POLE-2: field_normalizer_structure (Pf 14.2, lane-h)

## 背景

feitThompson は 2 本の独立 bare sorry に bottom-out する ([[ft-endgame-two-poles]])。POLE-1 は
`Section16Inputs` producer (skeleton `80f9aa39` で 8014/7005/1004 に分配)。**POLE-2 = 本 issue**:
`field_normalizer_structure` (`OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965`, bare `sorry`)。
2026-06-18 にユーザー裁可で **lane-h に割当** (typeP_duality 完了で idle 化したため)。POLE-1 側
(lane-g/f/b) と非衝突で並行可能。

## やること

- [ ] `field_normalizer_structure (hG) (hyp : Hypothesis) : Nonempty (FieldNormalizerData hyp)`
      (`S16_NonExistenceG.lean:1965`, 現 `sorry`) を実証明化する = Peterfalvi (14.2)。
- [ ] 既存 scaffold を活用: `field_normalizer_of_L_conj_M` (`:1030`)、`LHypothesis`/`MHypothesis`/
      `NonConjugateHypothesis`、producer 群 (`:137`/`:196`/`:714`/`:949`/…)。
      残務 = producer の配線 + L-vs-M 比較の closing (Pf §14.12-14.16 assembly)。
- [ ] 完了後 `nonexistence_of_G` (`:1971`) が BG App.C 経由で矛盾を出す閉路が unconditional 化。

## 完了条件

`field_normalizer_structure` の `sorry` が消え、`lake build OddOrder OddOrder.AxiomsCheck` 緑。
可能なら `#assert_only_allowed_axioms` に登録 (sorry 消滅後)。

## 参照

- POLE-2: `OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965` (`field_normalizer_structure`),
  `:1030` (`field_normalizer_of_L_conj_M` scaffold)
- 既証明 expertise: lane-h の BG §14 type-P 構造 (typeP_duality `S14_TypePCounting.lean:7961`)
- 関連: 8014 / 7005 / 1004 (POLE-1)。caveat: 本件は Peterfalvi §14 (field automorphism/Dade) で
  BG §14 とは別物 — lane-h は territory 学習が要る
