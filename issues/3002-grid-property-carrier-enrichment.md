---
id: 3002
slug: grid-property-carrier-enrichment
title: "§15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)"
created: 2026-06-29
---

# §15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)

**Lane:** c (γ §15/§16 POLE-2) raising; fix = **cross-lane** (lanes B grids / D carrier + FT spine).

## 背景

§15/§16 の Dade norm-cascade wrapper 定理 ((13.5)-(13.10)、(14.11)-(14.12)、norm cascade) は
`∃ data : NormCascadeData hyp, data.<opaqueProp>` 形で、`NormCascadeData`/`CharacterDegreeData` は
`Hypothesis` の **opaque grid** (`omega`/`eta`/`mu`/`nu` + `tauS`/`tauT`/`tau3`) に依存。これらが
**τ-isometry / η-直交性 / 指標次数** を *property* として carry していないため、wrapper は faithful 化
できず carrier-gated のまま (`scaffold_opaque_prop_convention`)。

lane c は 2026-06-29 に **carrier-free な norm-cascade arithmetic toolkit を完成** (S15_SAndT_Setup.lean):
`sum_normSq_erase_one_ge_of_const_on_subgroup` (13.5.c)・`innerSum_self_eq_sum_normSq`+
`sum_normSq_eq_card_mul_inner` (Parseval)・`caseB_quadratic_nonneg` (13.6/13.8)・`caseB_eta_norm_core`
(13.7)・`caseB_u_bound_arith` (13.2.c)。**残るのは grid 性質を Hypothesis に carry させること**だけ
— それが入れば各 wrapper を toolkit から faithful に組める。

## やること

- [ ] `S15.Hypothesis` に grid 性質 field 追加 (consumer-side で先に sorried contract として pin 可):
  - `tau3_isometry` (τ₃ が Dade isometry = `FullDadeIsometryData`、§5 `S05_IntegralSigma` の σ-isometry)
  - `omega_orthonormal` / `eta_orthogonality` ((3.2)/(5.3.b) の grid 直交性、§5 `S05_*Grid` producer)
  - `mu_degree` / `Sset_nonempty` (μ_j(1)=uq、Sset が誘導指標族 = (9.8)/(9.9))
- [ ] FeitThompson の 2 constructor (`sectionSixteenHypothesis_of_inputs` 他) + `Section16Inputs` /
  §16 carrier に thread (lanes B=grids `cd` / D=carrier; FT spine は prefix-split 共有)。producer は
  no-gates 方針で sorry 可。
- [ ] grid 性質が入ったら lane c が faithful wrapper を toolkit から組む (13.6/13.7/13.8 → 13.10 assembly)。

## 完了条件

§15/§16 の norm-cascade wrapper が opaque-Prop でなく実 inequality を述べ、lane-c toolkit + carried grid
性質から sorry-free に証明される。

## 参照

- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` — carrier-free toolkit (上記) + `induce_one_apply`
- `notes/peterfalvi/s15_s_and_t.md` — LIVE STATUS (2026-06-29、toolkit + 2 work-streams)
- `OddOrder/FeitThompson.lean:1828` — `sectionSixteenHypothesis_of_inputs` (constructor)
- issue 3001 (Sdata.W2 reconciliation、同系の carrier 不足)
