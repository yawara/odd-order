---
id: 9078
slug: semilinear-fieldmodel-leaf
title: "shared-infra claim (lane c): SemilinearFieldModel leaf — F_{q^p}⋊V* 実現 (9000 scope note item 2 / 0098 再活性)"
created: 2026-07-08
---

# shared-infra claim (lane c): generic semilinear (9.7.b) field-model package

**claim-before-build (CLAUDE.md (C))**. Lane c claims the **generic semilinear field-model
realization** = 新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean`
(+ その S16 consumer 側 T-side producer)。これは issue **9000 の HUB scope note (2026-07-07, 0098
レーン再点検) item 2** の実施であり、**hub が既に lane c の scope として carve-out 済** (新規判断でなく
既決の再活性化、hub RULING 9077 で確認)。姉妹 item 1 (typeP_pair port = 9073) は closed、item 2 が未着手。

## 何を build するか (genuine 未構築 gap)

**目標**: `F_{q^p} ⋊ V*` semilinear group を実現する module-level generic interface + その T-side 実体化。

現状 (2026-07-08 code-level 確認):
- `FieldNormalizerData` (S16_NonExistenceGCore:620、11 field) / `TFieldModelData` (S16_G0Coprime:800、
  4 field `sigma`/`sigma_injective`/`sigma_Q_eq_Q`/`sigma_V_eq_V`) = **構造体は定義済** (lane-c 所有)。
- 両 transport `FieldNormalizerData.derived_inf_centralizer_le_P` / `TFieldModelData.derived_inf_centralizer_le_Q`
  = **proven sorry-free** (T-side engine は commit 5fb560bd/485e0e4a で landed)。
- **S-side producer** = `fieldNormalizerData_of_repr` (S16:2415) / `field_normalizer_of_U_characteristic_of_inputs`
  (S16:2938) は sorry-free gated engine (`exists_pu_field_repr` S16:2630 経由、char body gated)。
- **T-side producer** = **未構築** (`Nonempty (TFieldModelData hyp)` を作る項が repo に存在しない)。
- generic building block = App.B `exists_field_semilinear` (`Appendices/SemilinearField.lean:191`, COMPLETE) 既存。
- `SemilinearFieldModel.lean` = **未存在**。

## やること

- [ ] 新 leaf `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean` — module-level generic な
      `F_{q^p} ⋊ V*` 実現 interface (App.B `exists_field_semilinear` + a の SingerField structure を **cite**、
      `SemidirectProduct.lift` で σ-embedding を組む)。S-side (a の S12/S13) と T-side (c の S16) の両方が instantiate。
- [ ] T-side producer = `TFieldModelData hyp` の構成 (S-side `exists_pu_field_repr`→`fieldNormalizerData_of_repr`
      chain の dual、~550 行相当)。gated input (V-abelian/cyclic = (9.7.b) char body) は **parameter/hypothesis** で受ける。
- [ ] `t_side_frobenius_kernel` (S16:4528) を新 producer で discharge (V-abelian input modulo)、S-side を symmetrize。

## 分担境界 (dup 回避、hub RULING 9077)

- **c = field-model realization** (σ-embedding = `SemidirectProduct.lift`、`SemilinearFieldModel` leaf、
  T-side `TFieldModelData` producer)。a の Singer 結果を **cite** する consumer。
- **a = §9 block-decomposition + (11.9) char body** (`acts_irreducibly → cyclic V` の証明 = typeP_Galois 本体、
  9000 で a 保持)。**c は `|U| ∣ p^q−1` Singer bound を再導出しない** (`GroupTheory/RepresentationTheory/` に
  frozen sorry-free で既存、cite のみ)。→ 2026-07-02 の a-vs-d Singer dup を再演しない。
- **interface guard**: module-level generic only、両 side が instantiate、S11 の thin `singerAdapter` パターンを再利用。

## gated-endpoint skeleton (承認パターン)

realization は (9.7.b) char body の下流 (σ 構成に V-abelian = a の typeP_Galois output を **input** として要する)。
∴ 本 leaf は **gated-endpoint skeleton**: V-abelian を hypothesis 化した engine + assembly skeleton を今 build し、
a の char body landing で完全 close ([[feedback-gated-endpoint-skeleton-pattern]])。「gated / payoff の遠さ」は
着手基準でない (CLAUDE.md、[[feedback-cost-scope-not-a-criterion]])。DORMANT idle より genuine 前進。

## 完了条件

`SemilinearFieldModel.lean` が module-level generic な `F_{q^p}⋊V*` 実現を sorry-free (gated input は hypothesis)
で提供、T-side `TFieldModelData` producer が構成され、`t_side_frobenius_kernel` が V-abelian input modulo で
discharge、full build green・AxiomsCheck OK・新 axiom なし。

## 参照

- 親裁定: [9077](9077-lane-c-frontier-exhausted-reallocation.md) HUB RULING (B)。
- scope 元: [9000](9000-sigma-theory-typep-galois-foundation.md) HUB scope note 2026-07-07 item 2 / closed [0098](closed/0098-lane-rebalance-c-reactivation.md)。
- gate map: `notes/peterfalvi/s16_nonexistence_gate_map.md`。
- 既存 building block: `Appendices/SemilinearField.lean:125/191`、S-side chain S16:2415-2953。
- 他レーンは着手前に本 issue を scan (claim-before-build、policy 6/8)。
