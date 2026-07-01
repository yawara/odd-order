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

### ⚠ on-path / off-path 精査 (2026-07-01 lane d、grep 検証)

S16_NonExistenceG が cite する S15 producer (= **on-path**):
- `basic_structure` (13.2) **16×** — done 2/4 (U_comm/P_order)、残 P_elab(§11)/u_bound(§9)=lane a。
- `c_eq_one` (13.12) **14×** — bare sorry。S16 が `c = 1` の rewrite で多用。
- `caseB_order_u` (13.15) **2×** — sorry (`caseB_order_u_data` 経由)。

S15_SAndT_Setup 外で **0 cite (= off-path、issue 1004 verified)**:
- `S_coherent`/`sibleyTarget_S` (13.2.d 一致 isometry) — S16 は η=τ₃∘ω (W-side grid) で迂回、
  S/T-side maximal-coherent Dade (tauS/tauT) を読まない (user decision 2026-06-24, issue 1004)。
- `character_degree_analysis`(13.3)/`lambda_forces_T_caseB`(13.4)/`tiSubset_character_orthogonality`(13.5)/
  norm cascade (13.6–10 `*_norm_lower`/`global_character_bound`/`analytic_inequality`)/`caseA_parameters`(13.13) — 全 0 cite。

**route 精査完了 (Coq PFsection13.v 読解)**: `c_eq_one`(13.12) は **structural + on-path analytic**、
off-path tauS cascade 非依存:
- Coq `FTtypeP_Ind_Fitting_reg_Fcore`: (i) `semiregular C W₁` (W₁ が `C ⊆ U` に fpf、
  `UW₁` Frobenius の `Frobenius_reg_ker` から) → **`2q ∣ c−1`** (`regular_norm_dvd_pred` +
  oddness/Gauss)。(ii) `m` の上界 `ub_m` (13.10 analytic、W-side cyclicTI = on-path η grid、
  tauS 非依存)。(iii) numeric elimination → q=3,p≥5 → 矛盾。
- `u_bound`(13.2.c) も **structural**: Coq `FTtypeP_facts` は `typeP_Galois` 二分岐
  (Galois: `u ∣ (p^q−1)/(p−1)`; 非 Galois: `u ≤ (p−1)^{q−1}` semilinear/matrix bound)。char 非依存。

⟹ **`c_eq_one`/`u_bound` は in-territory で closeable** (off-path char でない)。lane d の次 on-path build:
1. **`c ≡ 1 mod q`** (→ `2q ∣ c−1`) を `typeP_uW1_frobenius` (W₁ fpf on U⊇C) + `IsFrobeniusAction.card_modEq_one`
   から構築 (S15_SAndT_Setup、structural、Coq route 上)。
2. (13.10) analytic の W-side (cyclicTI/η) route を assemble (arith core `analytic_inequality_arith` 済)。
3. numeric elimination で c_eq_one 完成。
(P_elab/u_bound は lane a §11 structural type-P σ-theory = `H_elementaryAbelian`/typeP_Galois に cite。)

### c_eq_one (13.12) 進捗 (2026-07-01 loop、structural part 完成)

Coq `FTtypeP_Ind_Fitting_reg_Fcore` の route を実装:
- ✅ `W1_fpf_C` — W₁ が C 上 fpf 共役作用 (typeP_uW1_frobenius transfer)。
- ✅ `W1_le_normalizer_C` — W₁ ≤ N_G(C)。
- ✅ `c_modEq_one` — **c ≡ 1 (mod q)** (q-group 類等式 + fpf ⟹ C_C(W₁)={1})。
- ✅ `two_mul_q_dvd_c_pred` — **2q ∣ c−1** (= Coq `dv_2q_c1`、c 奇 + Gauss)。
- ✅ `c_eq_one` restructure — c>1 枝で **c ≥ 2q+1** を structural に確立。

**残 c_eq_one deep 部** (α cluster、multi-turn): (i) (13.10) analytic inequality `ub_m`
(W-side character norm cascade、grid gated) + (ii) `typeP_Galois` 二分岐 (σ-structure、lane a §11)
+ (iii) `u ∣ 31` (Galois case) + (iv) `Fcore_max` structural contradiction (PC nilpotent normal
Hall ⊋ P=S_F の矛盾)。arith core (`caseB_numeric_forces_q_three`/`m_value_*`) は済だが、char/σ 部が
deep。次: (13.10) の grid 供給可否を assess。

## B. char/numeric spine (13.5–13.15、10 sorry) — **character grid + coherence gated**

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

## construction-site 実地調査 (2026-07-01, lane d) — **in-territory と判明**

`S15.Hypothesis` の **唯一の constructor は `FeitThompson.lean`** (δ = lane d dormant territory):
- `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (:1740、`tp`=`Section16TypePStructure` menu 経由)
- `sectionSixteenHypothesis_of_inputs` (:1817、`inp`=`Section16Inputs` 経由)
- menu builder `section16TypePStructure_of_isMinimalSimpleOdd` (:795)
- `S14_MaximalI:3427` は **S12 Hypothesis** 構築 (S15 でない) → lane B touch 不要。
- `S16_NonExistenceGCore` は `base : S15.Hypothesis` を **受け取るだけ** (base field 構築せず) → 不変。

⟹ **carrier 拡張は S15_SAndT_Setup (mine) + FeitThompson carrier宣言群 (δ dormant = mine) で完結、
cross-lane でない**。α の `:426` (feitThompson 本体) には非接触。

**供給元も在庫確認済** (`section16TypePStructure_of_isMinimalSimpleOdd` :795 の scope 内):
- Hall `(κ∪σ)'`-subgroup `U₀` を `hall_E_exists` で既取得 (:800)。
- W-side は `typeP_pair_W_structure` (BG 14.7)、W₂ = `mp.Kstar`。
- U-side は `exists_kappaHall_invariant_complement_to_MF` (BG §1 Prop 1.5.b invariant Schur–Zassenhaus)。

## 具体 拡張プラン (in-territory、lane d 実施可)

S15.Hypothesis + menu chain (`Section16MaximalPair`/`Section16TypePStructure`/`Section16Inputs`) に
reconciliation field を足し、`section16TypePStructure_of_isMinimalSimpleOdd` で供給:

| 追加 field | close する basic_structure_gated field | 供給 supply-proof | 状態 |
|---|---|---|---|
| ✅ `S_U_commutative : IsMulCommutative ↥U` | `U_commutative` | `(typeP_hall_derived_eq_and_abelian hG mp.S_maximal mp.K_le_S hUM hKne mp.K_hall hUhall).2` (BG§15、hUhall = U が (κ∪σ)'-Hall、構築 scope 内) | **DONE** (commit `d20c02d`) |
| ✅ `Sdata_W2_eq : Sdata.W2 = W2` | `P_order` (`card_P_eq` 即適用) | 新 helper `typePData_of_kappaHall_hallComplement_W2` = `centralizer_W1` + `typeP_derivedInG_inf_centralizer_kappaElement_eq` (`Sdata.W2 = mp.Kstar`)、`mp.Kstar_eq` 供給 | **DONE** (本 commit) |
| (`P_elementaryAbelian`) | `P_elementaryAbelian` | lane a `H_elementaryAbelian` (Pf 11.7) cite = **sorried** + `S13.Hypothesis S` 構築 (重) | lane a §11 に残 gated |

**BG/** dormant genuine-need part** (Option 1 並行作業): 上表の supply-proof が要求する reconciliation
lemma (`Sdata.W2 = Kstar` / `U = Hall U₀`) が BG §14/§16 に在庫か確認 → 無ければ BG/** で実証明
(typeP_duality 周辺、mine dormant territory)。これが extension の genuine upstream math。

## 進捗 (2026-07-01, lane d)

- ✅ §8 TI-subset pair (`H_sharp_isTISubset`/`S_normalizes_H_sharp`) — carrier `fitting_eq` (commit `2a0ec49`)。
- ✅ `basic_structure_gated.U_commutative` — BG§15 経由 carrier 拡張 (commit `d20c02d`)。
- ✅ `basic_structure_gated.P_order` — `card_P_eq` + `Sdata_W2_eq` carrier 拡張 (commit `eac53c3`)。

**basic_structure_gated 残 2 sorry (両方 lane a 上流 gated)**:
- `P_elementaryAbelian` — Pf (11.7) = lane a `S13_MaximalIII_IV.H_elementaryAbelian` (sorried) +
  `S13.Hypothesis S` 構築 (chief/base/s11Setup 大構造)。sorried-cite skeleton は可だが genuine math は
  lane a §11 待ち (S13.Hyp bridge が重く、cite しても sorry は lane a へ移るだけ)。
- `u_bound` — Pf (9.7) Singer `u ∣ (p^q-1)/(p-1)` (lane a §9、case-split)。arith bridge
  `(p-1)^{q-1} ≤ (p^q-1)/(p-1)` は mine で proof 可だが (9.7) 本体が要 = lane a。

**char/numeric spine (13.5–15、10 sorry)** は依然 grid + coherence (`sibleyTarget_S`=lane B) gated
(§B 参照)。lane d の S15 in-territory ungated frontier は上記 4 close で一巡。次は char grid /
coherence の genuine upstream (要 lane B/§3-5 調整) か、lane a §11/§9 の待ち解除後の残 2 field。

## 参照

- commit `2a0ec49` (§8 TI-subset pair)、issue 4013 (closed、fitting_eq = 8.5.a)
- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` (basic_structure_gated:284、char spine:1195–1682)
- `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean:806` (`typeP_hall_derived_eq_and_abelian`, U abelian)
- `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean:425` (`H_elementaryAbelian`, sorried, Pf 11.7)
- issue 3001 (`Sdata.W2 = W2` reconciliation)
