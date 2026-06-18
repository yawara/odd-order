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

- [x] `field_normalizer_structure : Nonempty (FieldNormalizerData hyp)` を **sorry-free 化** (`d22e2cd8`)。
      教科書結論「By (14.12), (14.16), (14.7)」の忠実 assembly (下記 LANDING)。
- [x] L-vs-M closing: (14.16) `H_eq_U` を配線、(14.7)/(14.12)/(14.16) の 3 ルート case 分析。
- [x] opaque `U_characteristic_in_H` を concrete `(U.subgroupOf H).Characteristic` に materialize
      + (14.16)→(14.7) bridge を実証明 (`d901a183`)。
- [ ] **genuine 残務 (§13/Dade gate)**: `exists_LHypothesis` (14.3, `:1969`) / `exists_MHypothesis`
      (14.10, `:1978`) — L/M over N_G(U)/N_G(V) + Dade data 構成 (Pf (13.17) + Dade isometry)。
- [ ] **irreducible hard core**: `field_normalizer_of_U_characteristic` (14.7, `:199`) = 有限体モデル
      σ: PU↪G of (14.2)(a)。§13 type-I + Dade + GaloisField 構成に深く gate (大物)。
- [ ] 完了後 `nonexistence_of_G` が BG App.C 経由で矛盾を出す閉路が unconditional 化 (上記が全て埋まれば)。

## 2026-06-18 LANDING (assembly + bridge COMPLETE, 残務 gated)

`field_normalizer_structure` (Pf 14.2) は **sorry-free**。stop 条件「sorry 消滅」達成。残務 (14.7 有限体
モデル + L/M producers + 14.4-14.16 char cascade) はすべて Pf §10-13 char theory / Dade / 有限体モデルに
gate = LAUNCH の明示 stop trigger。real sorry 140→141。詳細 = LANDING block in lane-h LAUNCH.md。
ステータス = pending (genuine 残務は §13/Dade unblock 待ち)。

## 完了条件

`field_normalizer_structure` の `sorry` が消え、`lake build OddOrder OddOrder.AxiomsCheck` 緑。
可能なら `#assert_only_allowed_axioms` に登録 (sorry 消滅後)。

## 参照

- POLE-2: `OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965` (`field_normalizer_structure`),
  `:1030` (`field_normalizer_of_L_conj_M` scaffold)
- 既証明 expertise: lane-h の BG §14 type-P 構造 (typeP_duality `S14_TypePCounting.lean:7961`)
- 関連: 8014 / 7005 / 1004 (POLE-1)。caveat: 本件は Peterfalvi §14 (field automorphism/Dade) で
  BG §14 とは別物 — lane-h は territory 学習が要る
