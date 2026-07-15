---
id: 117
slug: s-side-field-repr-thin-cite
title: "HUB: s_side_field_repr の proof-only thin cite (9102 follow-up、供給 chain 明記)"
created: 2026-07-15
---

# HUB: s_side_field_repr の proof-only thin cite (9102 follow-up、供給 chain 明記)

## 背景と owner 裁定

lane a が claim 9102 で (14.6) S-side Clifford dichotomy dispatcher を landing し、
c 所有の bare-sorry gate `S16.s_side_field_repr` への shape 適合を確認した。

**hub 裁定 (tick 59)**: 引数供給は genuine lane work なので hub は代行しない。
c 停止中は **lane a の campaign 継続**として実施してよい。lane a がこの割当を採用し、
statement 不変の proof-only carve-out として完了した。

## 供給 chain（lane a 実装）

初版 issue の「`q = 3` と `u = (p - 1)^2 / 4` を無条件に供給する」という診断は
強すぎた。(13.13) は actual Clifford case-(a) certificate の下でだけ両等式を与える。
claim 9102 の follow-up commit は、その正しい契約を
`S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters` として公開した。

`hG : IsMinimalSimpleOdd G`, `hyp : S16.Hypothesis` から実装した closed-term chain は:

1. `hnoV` := `S12.no_typeV_maximal_unconditional hG`（(10.10)）。
2. `hncH0C` := `fun s13 => S13.S_H0C_not_coherent_unconditional hG s13`（(11.3)）。
3. `exists_LHypothesis hG hnoV hncH0C hyp` から canonical
   `Ldata.typeI_data : TypeIOverNormalizerData hyp.base`（(14.3)/(14.5)）。
4. `S15.c_eq_one hG hyp.base`（(13.12)）と、case-(a) branch 内だけ
   `S15.caseA_parameters hG hyp.base caseA`（(13.13)）。
5. 上記を条件付き dispatcher へ渡し、既存 S16 target へ `simpa`。

## 完了

- [x] `S16.s_side_field_repr` の bare `sorry` を上記 closed-term cite に置換
      （signature 不変、proof-only）。
- [x] direct `SubgroupM.lean` elaboration green。
- [x] 通常の `lake build OddOrder.AxiomsCheck` green。
- [x] repo census **36 → 35**。

### 公理監査上の注意

この thin cite は local bare `sorry` を閉じるが、現時点では `sorryAx`-free ではない。
個別 `#print axioms` で `c_eq_one`、`caseA_parameters`、`exists_LHypothesis` がそれぞれ
既存 upstream `sorryAx` を持つことを確認した。前二者は issue 0116 の analytic relayer、
後者は T-side/hub chain の既知 gate に対応する。したがって clean な explicit-input
dispatcher は AxiomsCheck 登録済みだが、S16 closed-term consumer 自体を clean endpoint として
追加 assert はしていない。これは初版 hub 指示の「signature-correct sorried-cite 可」と整合し、
upstream の de-opacification は各 owner の既存 issue に残る。

## 参照

- issues/closed/9102-s-side-galois-field-model.md
- issues/closed/1038-case-a-final-arithmetic-contradiction.md
- issues/closed/0116-s15-normestimates-relayer.md
- notes/meta/merge_monitor.md tick 59
- `OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean`
