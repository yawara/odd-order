---
id: 3002
slug: grid-property-carrier-enrichment
title: "§15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)"
created: 2026-06-29
---

# §15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)

**Lane:** c (γ §15/§16 POLE-2) raising; fix = **cross-lane**。
🧾 fix-owner 更新 (2026-07-02 hub, 3 レーン再編 — 正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`):
**S15 grid 性質 fields (`S15.Hypothesis` 変更) = lane c** / **FeitThompson.lean threading
(constructor 供給) = lane a** / **grid producers (§5 grid / cd 系) = lane b**。旧「lanes B grids /
D carrier」表記は stale (lane D 退役)。
検証 (2026-07-02): `tau3_isometry` / `omega_orthonormal` / `eta_orthogonality` / `mu_degree` は
`OddOrder/**.lean` に **0 hits** — field 追加は未実施で本 issue は live。

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

## 🔎 2026-07-03 (lane c) 精査確定: char frontier 全体が本 issue に収束 + cross-lane 分担の詳細

再開時の §13/§16 全数精査で、**lane-c char frontier 全体が本 grid carrier に gated** と確定:
- **norm cascade (13.6-13.10)**: `NormCascadeData.{lambda,eta10,eta01}_norm_lower` は opaque `Prop`
  scaffold。parameterized 算術 engine (`caseB_lambda_norm_core`/`caseB_eta_norm_core`/
  `caseB_quadratic_nonneg`/`analytic_inequality` の (13.10) 算術核) は**完備・sorry-free**。残は
  grid 性質を carry して wrapper を engine に wire するだけ。
- **`c_eq_one` (13.12, S16 が 14× cite)**: 構造部 proven、残 sorry は (13.10) analytic 経由 = grid gated。
- **`exists_MHypothesis` の `betaGrid` field** ((13.1.d)/(3.9) `1_G+Δ=Σε_ij η_ij`): honest η-grid 要求。

**構成可能性 = GENUINE 確認 (hoist でない)**: spine (`FeitThompson.lean:1727+`) は
`omega := Section16CharacterData.omegaS` = honest な `S05.TICyclicHypothesis.omegaProdChar` から構成。
∴ 性質は `S05_TICyclic.lean:733/740` (ω orthonormal) + `S07_CoherenceGalois` (τ isometry
`extension_inner_eq`) から**導出可能**。placeholder でない。

**cross-lane 分担 (確定)**: `S15.Hypothesis` (S15_SAndT_Setup:81) と `Section16Inputs`
(`FeitThompson.lean:96`) は共に `omega`/`tau3` を **bare field** で持ち性質を carry せず。
- **lane c**: `S15.Hypothesis` に grid 性質 field 追加 (下記) + wire で norm cascade wrapper を honest 化。
- **lane a**: `Section16Inputs` に同 field 追加 + `sectionSixteenHypothesis_of_inputs` で S15 へ渡す +
  `section16Inputs_of_isMinimalSimpleOdd` で `omegaS` orthonormal / `tau3W` isometry から supply (sorried 可)。
- ∴ **lane c 単独で build-green 不可** (field 追加が spine を壊す、lane a threading 必須)。

**追加すべき field (signature 案、S15.Hypothesis)**:
- `eta_orthonormal : ∀ i j k l, ClassFunction.inner (eta i j) (eta k l) = if (i,j)=(k,l) then 1 else 0`
  (τ₃ isometry + ω orthonormal から導出; parity/expansion core が消費)。
- `eta_intCast_on_G0 : ∀ (g) (hg : g ∈ G0-型), ∃ n : ℤ, eta i j g = (n:ℂ)` ((3.9.c) 整数値; parity core の `n`)。
- `eta_conj_neg : eta (-i) (-j) g = conj (eta i j g)` ((3.9.a) 共役ペア involution; parity core の `hpair`)。
- (13.19.c betaM 側 odd parity は betaM_expansion 側で別途)。

正確な形は consumer (parity core `one_le_norm_signed_paired_sum` / sum-of-squares core
`all_pm_one_and_card_of_odd_sq_sum_le`, issue 4001) の入力に合わせる。

## 参照

- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` — carrier-free toolkit (上記) + `induce_one_apply`
- `notes/peterfalvi/s15_s_and_t.md` — LIVE STATUS (2026-06-29、toolkit + 2 work-streams)
- `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁴⁶ (2026-07-03 frontier 収束の記録)
- `OddOrder/FeitThompson.lean:1861` — `sectionSixteenHypothesis_of_inputs` (constructor) / `:96` `Section16Inputs`
- issue 3001 (Sdata.W2 reconciliation、同系の carrier 不足)、issue 4003 (η-値性質、統合対象)
