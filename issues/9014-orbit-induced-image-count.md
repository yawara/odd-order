---
id: 9014
slug: orbit-induced-image-count
title: "shared: induced-image cardinality (G/H-orbit count) for irreducibly-inducing families"
created: 2026-07-06
kind: shared-infra
lanes: [c]
---

# shared: induced-image cardinality (G/H-orbit count) for irreducibly-inducing families

## 背景

Peterfalvi (14.9) の `calT1` 濃度 `size calT1 = (v−1)/p` (Coq `PFsection14.v` `FTtypeP_min_typeII`
L836–845, `size_irr_subseq_seqInd` / `card_imset_Ind_irr` 経由) は「共役不変な誘導元族 `T ⊆ Irr H`
(`H ⊴ G`) が各元 irreducibly 誘導するとき、像 `{Ind_H^G θ}` の濃度 = `|T| / [G:H]`」という
**一般の orbit-count** を必要とする。M-side (`InducedDegreeSum` の
`card_index_mul_sum_induced_family_degree_sq`) は degree-square 和を数えるが濃度そのものは残していた
(構造も full-`Irr(M')` fiber 前提で `calT1` の quotient-restricted 族と異なる)。既存の
`InducedIrreducible.card_filter_induce_eq_index_inertia` (fiber = `[G:I_G(θ)]`) を土台に、濃度版を
新規 shared leaf として landing した (claim-before-build の retro claim; 既存 open 9000 に重複なし
— 9007=Frobenius 共役直交, 9011=TI 共役計数, 9002=Clifford, いずれも別物)。

## やること

- [x] 新規 leaf `OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean`:
  - `card_image_induce_mul_index_eq` : `|T.image (Ind_H^G)| · [G:H] = |T|`
    (共役不変 `T ⊆ Irr H`, `∀ θ∈T, I_G(θ) = H`).
  - `card_image_induce_eq_div` : 除算形 `|T.image (Ind)| = |T| / [G:H]`.
  - `OddOrder.lean` に import 追加。
- [x] `S16_NonExistenceG.lean` の (14.9) blocker map を更新 (item 2c = DONE、残差を item 2b
  = Frobenius-kernel inertia `I_T(inflate θ) = QV` に絞り込み)。

## 完了条件

`lake build OddOrder.GroupTheory.RepresentationTheory.OrbitOnIrr` green + full build green +
AxiomsCheck OK。→ **DONE** (この commit)。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean` (新規)
- `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean:377`
  (`card_filter_induce_eq_index_inertia` = fiber count 土台)
- `OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean:187`
  (M-side degree-square 版、構造比較用)
- `OddOrder/Peterfalvi/S16_NonExistenceG.lean:167-` ((14.9) blocker map, item 2c 更新)
- Coq `coq/theories/PFsection14.v` L836–845 (`size calT1 = (v.-1) %/ p`)

## 未消化の下流残差 (item 2b — この issue の範囲外)

`calT1` 濃度を実際に `|V|` に接続するには、非自明 `θ ∈ Irr(QV/Q)` に対する inertia
`I_T(inflate θ) = QV` が要り、これは (b1) 商 Frobenius `T/Q = (QV/Q) ⋊ (W₂Q/Q)` (kernel `QV/Q ≅ V`;
現在は部分群 Frobenius `V ⋊ W₂ ≤ T` のみ、`S15.isMulCommutative_V` 内 local `have`) と (b2)
inertia/inflation 可換補題 `I_G(inflate_N χ̄) = comap (mk' N) (I_{G/N}(χ̄))` (repo に inertia-商 補題
無し) の 2 つの未形式化 rep-theory brick を要する。加えて `V` abelian が現状 `IsTypeII T` gated
(`S15.isMulCommutative_V`) ゆえ type-III 分岐で再導出が要る。→ 別 issue / lane-b (9013 T-side) と
協調。
