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

> **✅ CLOSED 2026-07-24 (hub)** — `TypeBIsomorphicSplit.lean` で完遂:
> `IsTypeB.exists_isomorphicOrderQModuleSplit` =
> `IsTypeB P → ∃ K : Subgroup (MulAut P), Nonempty (IsomorphicOrderQModuleSplit
> K.subtype (center P) …)`。sorry 0・axiom-clean・AxiomsCheck 5 assert。
> 経路: ① `exists_diagonalAut` (Lemma 1(c) sufficiency + `q(xv) = xφ(x)q(v)`
> で対角 automorphism を各 x ∈ F* に構成) ② actor = `diagonalAuts` 部分群
> (対角誘導全体 — 積閉なので zpow 帰納不要) ③ 一般 engine
> `nonempty_isomorphicOrderQModuleSplit_of_diagAction` (χ : G/Z ≅ F×F +
> 対角性 + |Z| = |F| だけから座標線 split + swap 同変を構成) ④ model 形は
> ③ の instance、抽象形は `QuotientGroup.congr` + `map_center_mulEquiv` +
> `Subgroup.centerCongr` で輸送。
> Lemma U 経由の「任意 split への輸送」は本 issue の存在形には不要
> (freeness/card 仮定つきで Lemma U がそのまま合成可能 — 使用側で cite)。

## やること

- [x] TypeBModel の座標で `F × 0` / `0 × F` の invariant summand 対を
      構成し、swap (または Frobenius twist) で K-同変同型を与える
      (✅ swap のみで足りた — 作用が対角なので)
- [x] Lemma U (`OrderQModuleSplit.nonempty_summandEquiv_of_isomorphic`,
      SplitUniqueness.lean) により任意の split へ輸送する
      (→ 存在形には不要と判明; equivModel 直輸送で landing。任意 split
      強化は Lemma U の仮定 (freeness/card) が揃う使用側で合成)
- [x] (e) 後半の actor 座標同一視は QuotientPlaneModel
      (`exists_planeCoordinates_of_isomorphicSplit`) が実装済 —
      (e) 全文の statement を組むときはこれを cite する (note のまま有効)

## 完了条件

- `IsTypeB Q → Nonempty (IsomorphicOrderQModuleSplit …)` 形の定理が
  sorry-free で landing し、AxiomsCheck 登録済み ✅

## 参照

- issues/closed/2048-pf-suzuki-lemma5.md (設計メモ・⟸ 方向)
- OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/TypeBRecognition.lean
- OddOrder/Peterfalvi/Appendices/Suzuki2Groups/SplitUniqueness.lean
- OddOrder/Peterfalvi/Appendices/Suzuki2Groups/Types.lean (TypeBModel)
- references/peterfalvi/pdf/08.0_pp_139_143_On_Suzuki_2-Groups.pdf
