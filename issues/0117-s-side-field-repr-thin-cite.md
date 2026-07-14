---
id: 117
slug: s-side-field-repr-thin-cite
title: "HUB: s_side_field_repr の proof-only thin cite (9102 follow-up、供給 chain 明記)"
created: 2026-07-15
---

# HUB: s_side_field_repr の proof-only thin cite (9102 follow-up、供給 chain 明記)

## 背景

lane a が claim 9102 (`issues/closed/9102-s-side-galois-field-model.md`) で
`S15_SSideGaloisFieldModel.lean` を landing (tick 59, merge 28c05aab)。
(14.6) S-side Clifford dichotomy dispatcher
`S15.sSide_galoisField_repr_of_parameters_and_typeIOverNormalizerData` が sorry-free で
存在し、c 所有の bare-sorry gate
`S16.s_side_field_repr` (`S16_NonExistenceG/SubgroupM.lean:170`) への thin-cite probe
(`simpa using …`) の **shape 適合**を a が確認済み。

**hub 裁定 (tick 59)**: probe は shape 適合の確認であり closed-term 放電ではない —
dispatcher の 4 引数の**供給自体が genuine lane work** ゆえ hub は代行しない (下記)。
c 停止中につき、実施 owner = **a の campaign 継続** (パラメータ源 = a 所有
OrderDetermination) or **c 再開時の初手**。

## 残る供給 (thin cite に必要な 4 引数)

`s_side_field_repr` の文脈 (`hG : IsMinimalSimpleOdd G`, `hyp : S16.Hypothesis`) から:

1. `hc : hyp.base.c = 1` — 供給源 `S15.c_eq_one`
   (`S15_SAndT_Setup/OrderDetermination.lean:845`, a 所有 0115 移管)
2. `hq : hyp.base.q = 3` — 同 OrderDetermination (13.11)/(13.13) 系
3. `hu : hyp.base.u = (hyp.base.p - 1)^2 / 4` — 同 (13.13) 系
4. `data : TypeIOverNormalizerData hyp.base` — canonical 供給は
   `S15.typeII_overNormalizer_frobenius` (`S15_SAndT.lean:1131`) 経由で
   side conditions (hnoV / hSTypeII / hTTypeII / hT2 / hqp / hNUS) の組み上げが必要。
   T-side には `S16_NonExistenceG/TSideTypeP.lean:44` の `typeI_data` field 前例あり

1-3 は OrderDetermination の定理から (それ自体 sorried でも signature-correct なら
sorried-cite 可)。4 は S16 文脈での側条件放電が本体。

## やること

- [ ] (a: campaign 継続 or c: 再開時) S16 site で 4 引数を組み上げ、
      `s_side_field_repr` の `sorry` を
      `simpa using S15.sSide_galoisField_repr_of_parameters_and_typeIOverNormalizerData
      hG hyp.base hc hq hu data` に置換 (statement 不変・proof-only)
- [ ] census −1 を tick 記録で確認

## 完了条件

`S16_NonExistenceG/SubgroupM.lean` の `s_side_field_repr` が bare sorry でなくなり
build green / AxiomsCheck OK。

## 参照

- issues/closed/9102-s-side-galois-field-model.md (a の non-dup audit + probe 報告)
- issues/closed/1038-case-a-final-arithmetic-contradiction.md (case (a) 排除側)
- notes/meta/merge_monitor.md tick 59 エントリ
- `OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean` (dispatcher 本体)
