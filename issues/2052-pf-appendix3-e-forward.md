---
id: 2052
slug: pf-appendix3-e-forward
title: "Appendix III Theorem (e) ⟹ 方向: type B の同型 summands"
created: 2026-07-21
---

# Appendix III Theorem (e) ⟹ 方向: type B の同型 summands

## 背景

Peterfalvi Appendix III Theorem (e) の同値
「summands が K-同変同型 ⟺ Q は type B」のうち、
⟸ 方向 (認識半分) は issue 2048 で完成
(`isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube`,
TypeBRecognition.lean)。⟹ 方向 (type B ならば任意の invariant
two-summand split の summands が同型) は **Lemma 5 が使わないため**
2048 では低優先繰延とした (2048 の設計メモ 2026-07-21 参照)。
Appendix III の番号付き結果としての完全性のために残す。

## やること

- [ ] TypeBModel の座標で `F × 0` / `0 × F` の invariant summand 対を
      構成し、swap (または Frobenius twist) で K-同変同型を与える
- [ ] Lemma U (`OrderQModuleSplit.nonempty_summandEquiv_of_isomorphic`,
      SplitUniqueness.lean) により任意の split へ輸送する
- [ ] (e) 後半の actor 座標同一視は QuotientPlaneModel
      (`exists_planeCoordinates_of_isomorphicSplit`) が実装済 —
      (e) 全文の statement を組むときはこれを cite する

## 完了条件

- `IsTypeB Q → Nonempty (IsomorphicOrderQModuleSplit …)` 形の定理が
  sorry-free で landing し、AxiomsCheck 登録済み

## 参照

- issues/closed/2048-pf-suzuki-lemma5.md (設計メモ・⟸ 方向)
- OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/TypeBRecognition.lean
- OddOrder/Peterfalvi/Appendices/Suzuki2Groups/SplitUniqueness.lean
- OddOrder/Peterfalvi/Appendices/Suzuki2Groups/Types.lean (TypeBModel)
- references/peterfalvi/pdf/08.0_pp_139_143_On_Suzuki_2-Groups.pdf
