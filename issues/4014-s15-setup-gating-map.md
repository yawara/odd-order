---
id: 4014
slug: s15-setup-gating-map
title: "S15_SAndT_Setup 残 14 sorry の gating map + basic_structure_gated 分解ルート"
created: 2026-07-01
---

# S15_SAndT_Setup 残 14 sorry の gating map + basic_structure_gated 分解ルート

## 背景

lane d 精査 (2026-07-01)。§8 TI-subset pair (`H_sharp_isTISubset`/`S_normalizes_H_sharp`) は
carrier の `TypePData.fitting_eq` (= Pf (8.5.a)) で closed (issue 4013、commit `2a0ec49`)。
残 14 sorry は下記の通り深く gated。次 iteration の効率化のため gating を記録。

## 残 14 sorry の分類

### A. `basic_structure_gated` (13.2.b,c,e) — **lane c が 12× cite = 最高価値**、carrier reconciliation gated

`BasicStructureGated hyp` の 4 concrete field + 2 opaque Prop:

| field | 供給元 | 状態 |
|---|---|---|
| `U_commutative : IsMulCommutative ↥U` | BG §15 `typeP_hall_derived_eq_and_abelian` (sorry-**free**、Lemma 15.1.b) | `hyp.U` が `(κ(S)∪σ(S))ᶜ`-Hall である reconciliation が要 (S15 hyp field に不在) |
| `P_order : |P| = p^q` | `card_P_eq` (this file) | `Sdata.W2 = W2` reconciliation が要 (issue 3001、S15 hyp field に不在) |
| `P_elementaryAbelian` | **lane a** `S13_MaximalIII_IV.H_elementaryAbelian` (Pf 11.7) | 当該定理が **sorried** (+ sibling `core_structure` も sorried) かつ `S13.Hypothesis S` 構築 (chief/base/s11Setup… 大構造) が要 = 二重に gated |
| `u_bound : u ≤ (p^q-1)/(p-1)` | Pf (9.7) Singer field (`|Ū| ∣ (p^q-1)/(p-1)`, S11) + arith bridge `(p-1)^{q-1} ≤ (p^q-1)/(p-1)` | (9.7) 部が lane a S11 で case-split 済だが単一 citable 形でない。arith bridge のみ mine で proof 可 (未使用) |
| `A0S_TI` / `tauS_eq_induction` (opaque Prop) | scaffold convention | 真の内容 (`IsTISubset A_0(S) S`) は `typeP_structure` conjunct で近いが `hyp.A0S` と F(S)^# の関係が hyp に不在 |

**共通根**: S15.Hypothesis の abstract field (U/P/W2 + `S_deriv_eq_PU`/`C_eq`/`P_eq_SF`) が
**intrinsic BG type-P/Hall 構造に紐づいていない**。reconciliation (U-Hall / W2 一致 / S13.Hyp) は
**§16-carrier 構築時の仕事** (`Section16TypePStructure` / hyp 構築 = `FeitThompson.lean` +
`Peterfalvi/S16_NonExistenceGCore.lean`)。

**分解ルート案 (要 cross-lane 判断 — signature 変更)**: `S15.Hypothesis` に reconciliation field を
追加 (`U_isHall`, `Sdata_W2_eq`, できれば `Sdata` を `TypeIIData` 化 or `S_elementaryAbelian` 直持ち)。
→ 追加 field は全 construction site (FeitThompson=α/δ, S16_NonExistenceGCore=lane c) が供給要 =
**signature contract 変更 = STOP 条件 (d) = hub/ユーザー裁定案件**。construction site は type-P₂
構造を既に建てているので供給は軽い可能性大 (要確認)。

### B. char/numeric spine (13.5–13.15、10 sorry) — **character grid + coherence gated**

`tiSubset_character_orthogonality` (13.5) / `lambda_norm_lower` (13.6) / `eta10_norm_lower` (13.7) /
`eta01_norm_lower` (13.8) / `global_character_bound` (13.9) / `analytic_inequality` (13.10) /
`numeric_bounds` q=3 枝 (13.11) / `c_eq_one` (13.12) / `caseA_parameters` (13.13) / `caseB_order_u` (13.15)。

- **arith/number-theory core は全部 sorry-free 済** (`analytic_inequality_arith`, `sum_ge_card_of_one_le_prod`,
  `caseB_numeric_forces_q_three`, `m_value_*`, `cyclotomic_divisor_facts`, `caseB_eta01_norm_bound`, …)。
- 残 producer は **具体 character value** (ω/η/μ/ν grid の値) と **coherence datum** (`H_sharp_hypothesis76`
  が要 = `S_coherent` = `sibleyTarget_S` (13.2.d) = (6.8) Sibley setup = lane B territory) に gated。
- chain: sibleyTarget_S/grid → (13.5) → (13.6-9) → (13.10) → (13.11-15)。base gate = grid + coherence。

### C. `sibleyTarget_S` (13.2.d、1 sorry) — §14 Sibley/coherence gated

(6.8) の `SibleyTarget` 構造 witness = lane B の (6.8) + §14 structure。B クラスタ frontier。

## 完了条件

このマップは調査記録。個別 sorry の closure は A/B/C の gate 解除に従う (別 issue/lane)。

## 次手 recommendation (lane d)

1. **A の carrier reconciliation** が最高 ROI (12× cite) だが signature 変更で cross-lane 裁定要。
   → hub/ユーザーに「S15.Hypothesis に U-Hall / W2 / P-elab reconciliation field を足し、
   construction site (FeitThompson + S16_NonExistenceGCore) で供給する」案の可否を確認。
2. それまで lane d は BG/** dormant の genuine-need 部か、A の construction-site 供給可否の実地調査へ。

## 参照

- commit `2a0ec49` (§8 TI-subset pair)、issue 4013 (closed、fitting_eq = 8.5.a)
- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` (basic_structure_gated:284、char spine:1195–1682)
- `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean:806` (`typeP_hall_derived_eq_and_abelian`, U abelian)
- `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean:425` (`H_elementaryAbelian`, sorried, Pf 11.7)
- issue 3001 (`Sdata.W2 = W2` reconciliation)
