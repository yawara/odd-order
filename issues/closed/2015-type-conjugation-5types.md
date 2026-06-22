---
id: 2015
slug: type-conjugation-5types
title: "HUB: 5型 HasPeterfalviType 共役 infra (II/III/IV/V) — Pf (8.17.a)/exists_second_maximal の unblock"
created: 2026-06-23
---

# HUB: 5型 HasPeterfalviType 共役 infra (II/III/IV/V) — Pf (8.17.a)/exists_second_maximal の unblock

## 背景

lane-h の Pf (12.9) honest assembly (S14_MaximalI, 2026-06-23) で、残る §8 obligation
`exists_second_maximal` ((8.17.a): `∃ L Lt, L maximal ∧ L ≠ M ∧ HasPeterfalviType Lt L ∧
P₀ ⊆ mainSubgroup L Lt`) を discharge しようとしたところ、**一般の 5型 HasPeterfalviType
共役同変性**が必要と判明。

(8.17.a) の証明骨子:
1. `bgTheoremE_cover_data` (BG §16, sorried) で `p ∈ π(G)` を covering する maximal `L₀ = reps i`
   (型 `tau i` = **任意の 5 型**) を取る (p ∣ |mainSubgroup L₀ (tau i)|)。
2. (8.11) Hall + Sylow 共役で `L₀` を共役して `P₀ ⊆ (conj g • L₀)_s` にする。
3. このとき `HasPeterfalviType (tau i) (conj g • L₀)` が要る — `tau i` は任意型ゆえ
   **全 5 型の共役同変性**が必須。

**現状の `OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean` には F/I しか無い**:
- `TypeFData.conj`, `TypeIData.conj`, `isTypeI_pointwise_smul`, `isTypeI_of_conj` ✓
- `isTypeII/III/IV/V_pointwise_smul`, `TypeIIData.conj`/`TypeIIIData.conj`/`TypeIVData.conj`/
  `TypeVData.conj` ✗ (ABSENT)

これは shared/lane-f infra (lane-h owned でない) ゆえ HUB issue として起票。

## やること

- [ ] `MaximalSubgroupTypeConj.lean` に `TypeIIData.conj` / `TypeIIIData.conj` / `TypeIVData.conj` /
  `TypeVData.conj` を追加 (`TypeFData.conj`/`TypeIData.conj` と同パターン、既存の equivariance toolkit
  `card_pointwise_smul`/`isFrobeniusGroup_subgroupOf_pointwise_smul`/`derivedInG` 共役同変 等を使用)。
- [ ] `isTypeII/III/IV/V_pointwise_smul` + 一般 `hasPeterfalviType_pointwise_smul (φ) (tau)
  (h : HasPeterfalviType tau M) : HasPeterfalviType tau (φ • M)` (tau で case split)。
- [ ] (任意) `mainSubgroup_pointwise_smul (φ) (M) (tau) : φ • mainSubgroup M tau =
  mainSubgroup (φ • M) tau` (case split + `maxNilpotentNormalHall_pointwise_smul` [✓] /
  `derivedInG` 共役同変 [S13_PrimeAction の private `smul_derivedInG_conj` を public 化])。

## 完了条件

`hasPeterfalviType_pointwise_smul` (一般) が landing。これで lane-h は (8.17.a)
`exists_second_maximal` を `bgTheoremE_cover_data` (BG §16) + (8.11) Hall + Sylow 共役で
proof 化できる (cover data 自体は BG §16 sorry に bottom-out)。

## 参照

- `OddOrder/Peterfalvi/S14_MaximalI.lean` の `exists_second_maximal` (sorried obligation)
- `OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean` (F/I conj 既存、II–V 欠落)
- `OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` `maxNilpotentNormalHall_pointwise_smul`
- `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean` private `smul_derivedInG_conj`
- notes/peterfalvi/s14_maximalI.md 「(12.9) honest assembly LANDED」

## hub 解決 (2026-06-23)

**判断: lane-h が実装する (shared infra `GroupTheory/MaximalSubgroupTypeConj.lean` への type-II/III/IV/V
共役同変 infra 追加)。** 根拠:
- `OddOrder/GroupTheory/**` は**共有所有 (全 lane 編集可)** → lane-h は越境せず実装できる。lane-h は本 infra の
  consumer ((8.17.a) `exists_second_maximal` in S14_MaximalI) ゆえ最も文脈を持つ自然な実装者。
- 既存 `TypeFData.conj`/`TypeIData.conj`/`isTypeI_pointwise_smul`/`isTypeI_of_conj` が template。
  II/III/IV/V は同パターンの機械的拡張 (equivariance toolkit `card_pointwise_smul`/
  `isFrobeniusGroup_subgroupOf_pointwise_smul`/`derivedInG` 共役同変 を流用)。新規数学なし。
- (8.17.a) は §8 obligation = honest FT 経路上の genuine な上流前提 (cover data 自体は BG §16 sorry に
  bottom-out するが、共役同変 infra は unconditional に積める実証明)。

**スコープ分割**:
1. **core (lane-h が今すぐ実装可)**: `TypeIIData/IIIData/IVData/VData.conj` + `isTypeII/III/IV/V_pointwise_smul`
   + 一般 `hasPeterfalviType_pointwise_smul (φ) (tau) (h) : HasPeterfalviType tau (φ • M)` (tau で case split)。
   **全て shared `MaximalSubgroupTypeConj.lean` 内で完結** → lane-h 単独・越境なし。
2. **optional (後回し可)**: `mainSubgroup_pointwise_smul` は `smul_derivedInG_conj` (S13_PrimeAction の
   **private**、**B 所有**) の de-private を要する → これは別 issue で **B に依頼** (小さな de-private、
   `MaxNilpotentNormalHall` の de-private 前例と同型)。core だけで `hasPeterfalviType_pointwise_smul` は
   landing でき、(8.17.a) の型同変部分は unblock される。mainSubgroup の φ-同変が必要になった時点で
   B に de-private 依頼を起票。

**hub 側の合流条件**: 通常ゲート。shared infra への追記ゆえ自動合流可。lane-f も BG §14-16 で TypeXData を
扱うが、`MaximalSubgroupTypeConj.lean` の**共役同変補題は新規追加**ゆえ衝突しない (既存宣言の改変でない)。
万一 lane-f が同ファイルを同時編集して内容衝突したら通常どおり abort+報告。

**lane-h への指示**: core (項目 1) を実装してよい。完了後 (8.17.a) `exists_second_maximal` を進める。
de-private が要る optional は B 宛 issue を起票 (cross-lane、独断で S13 を触らない)。

## ✅ DONE (2026-06-23, lane-h)

実装完了 (commit `1255e479` infra + `c0c11d1b` consumer):
- `MaximalSubgroupTypeConj.lean` に core 全実装: `TypePData.conj`/`typePNontrivialCore_conj`/
  `TypeII/III/IV/VData.conj`/`isType{II..V}_pointwise_smul`/一般 `hasPeterfalviType_pointwise_smul`/
  `mainSubgroup_pointwise_smul` + helper (`derivedInG_pointwise_smul`/`secondDerivedInAmbient_…`/
  `isNilpotent_…`/`fitting_map_subtype_…`/`normalizer_image_…`)。全 sorry-free + axiom-clean。
- **de-private 不要だった**: `derivedInG_pointwise_smul` を local に再証明 (S13 の private に非依存) →
  optional の B 依頼 issue は不要に。
- consumer: Pf (8.17.a) `exists_second_maximal` (S14_MaximalI) を discharge (commit `c0c11d1b`、
  cited `bgTheoremE_cover_data`/`hall_…` に還元、body sorry-free)。`exists_sylow_le_of_hall`
  (Hall→Sylow、reusable、axiom-clean) も新規。
- full build 3881 green、AxiomsCheck 登録 (`hasPeterfalviType_pointwise_smul`/`mainSubgroup_pointwise_smul`/
  `exists_sylow_le_of_hall`)。
