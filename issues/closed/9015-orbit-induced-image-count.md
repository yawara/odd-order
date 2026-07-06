---
id: 9015
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
— 9007=Frobenius 共役直交, 9011=TI 共役計数, 9002=Clifford, 9014=prime-TI-reducible coherence,
いずれも別物)。

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

## item 2b の 2 brick — **両方 landing 済** (2026-07-06 追記)

`calT1` 濃度を `|V|` に接続する非自明 `θ ∈ Irr(QV/Q)` の inertia `I_T(inflate θ) = QV` が要する 2 つの
一般 rep-theory brick は、いずれも shared-infra として**利用可能**になった:

- **(b1) 商 Frobenius** — 「Frobenius 群を kernel の正規部分群で割る」(一般には偽) ではなく、
  **Frobenius 群の同型による transport** として正しく定式化・実証明:
  `OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv`
  (`OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient.lean`, 新規 leaf, sorry 0)。
  部分群 Frobenius `V ⋊ W₂ ≤ T` (`S15.isMulCommutative_V`) を、`(V ⊔ W₂) ⊓ Q = ⊥` で `mk' Q` が
  そこで単射になることから得られる同型 `V ⋊ W₂ ≅ (QV/Q) ⋊ (W₂Q/Q)` で `T/Q` へ運ぶ。
- **(b2) inertia/inflation 可換** — **既存だった** (prior agent の「repo に inertia-商 補題無し」は
  stale): `OddOrder.RepresentationTheory.mem_inertia_compHom_iff`
  (`OddOrder/GroupTheory/RepresentationTheory/ConjugationBrauer.lean`)、
  `g ∈ I_T(compHom q θ̄) ↔ mk' Q g ∈ I_{T/Q}(θ̄)` = `I_T(inflate θ) = comap (mk' Q) (I_{T/Q}(θ̄))`。
  既に S08 `inertia_eq_H_of_c2` が消費している。

**組み立て = (6.8)(c2) テンプレ `S08.inertia_eq_H_of_c2` の直訳** (`H = QV`, `W₁ = W₂`,
`M = Q.subgroupOf QV`): (b1) の商 Frobenius を `inertia_eq_of_frobeniusGroup` に食わせ
`I_{T/Q}(θ̄) = QV/Q`、(b2) で `I_T(inflate θ) = QV` に引き戻す。

**残る 1 点 (Bonus b3, 別レーン協調)**: `V` abelian が現状 `IsTypeII T` gated
(`S15.isMulCommutative_V`; Coq `cVV` は type-P ungated)。type-III 分岐での再導出は
`S15_SAndT_Setup.lean` の型-P Hall-derived-abelian data (`typeP_hall_derived_eq_and_abelian`,
BG 15.1(b)) を type-III 経路に通す必要があり lane-b (S15) 領域 → 別 issue / lane-b (9013 T-side) と協調。

## 2026-07-06 lane-d closure

Current-state audit: the stated shared orbit-count API is landed in
`OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean`. The remaining `V`-abelian/type-III
reconciliation is tracked by lane-b/c coordination (`9013`) and is not part of this shared orbit-count
claim. Move to `issues/closed/`.
