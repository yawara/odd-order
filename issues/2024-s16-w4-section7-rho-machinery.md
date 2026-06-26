---
id: 2024
slug: s16-w4-section7-rho-machinery
title: "W4 char endpoints: §16 MHypothesis → S09 §7 ρ-machinery bridge (cite 可)"
created: 2026-06-25
---

# W4 char endpoints: §16 MHypothesis → S09 §7 ρ-machinery bridge

## 背景

**重要訂正 (2026-06-25)**: 当初「W4 foundation = §7 Dade ρ-machinery を新規形式化 (lane-c §7 重複)」
と評価したが、**誤り**。§7 ρ-machinery (7.1)-(7.8) は **`OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
に既にほぼ完全 sorry-free で形式化済み** (全ファイルで実 sorry 1 個):

- `Hypothesis71` / `chiRho` (ρ map) / `chiRho_norm_sq_le` / `chiRho_integral_inequality` — (7.1)-(7.3)
- `FamilyHypothesis71` / `family_inequality` — **(7.5) 完全 sorry-free**
- `Hypothesis76` / `chiRho_norm_sq_double_sum` — (7.6)/(7.7)
- `Hypothesis78` / `beta` / `beta_def` / (7.8.a) expansion — **(7.8) 完全 sorry-free**

S09 は S10→...→S16 で**推移的 import 済み = S16 から cite 可能**。lane-c の §7 は **coherence**
(S07_*、(5.7)/(6.8)) で別ファイル → **衝突なし**。よって W4 char endpoint の残作業は lane-c 協調不要な
**lane-h 自身の §16 bridge work**。

## やること

§16 の char endpoint を S09 §7 ρ-machinery の cite で de-opacify する。鍵 = MHypothesis (S16) の
abstract carrier (`tau : S07.IntegralCharacterMap`, `psi`, `betaM`, `G0`) を S09 の `Hypothesis71` /
`Hypothesis78` (concrete `S04.Hypothesis` + `S04.DadeMap` を要求) に橋渡し:

- [~] **bridge carrier** (betaM 側着手済): `Hypothesis78 G A M` → `BetaMExpansionData` の bridge lemma
      `betaMExpansionData_of_hypothesis78` を axiom-clean 実装 (S09 (7.8.a) cite で `betaM_seven_eight` 導出)。
      残: `Hypothesis71 G (A M) M` / `FamilyHypothesis71 G 1` の供給 (normCascadeBound 側で要、type-I M の
      Dade extension 14.10 から faithful)。
- [ ] **`normCascadeBound_of_charData` (14.11.4)**: `family_inequality` (7.5, cite) + `generic_character_bound`
      (|ψ^τ₁|≥1 on G_0、landed) + (7.7) 内積式で rational 不等式 `normCascadeBound` を導く。
- [x] **`betaM_expansion` (14.11.2)** ✅: `BetaMExpansionData` faithful carrier ((7.8.a) `β_M=1_G−χ+Δ` +
      η-grid id `1_G+Δ=Σεη`, χ generic で 2 branch 忠実) + `betaM_expansion_data` producer + axiom-clean
      bridge `betaMExpansionData_of_hypothesis78` (S09 `beta_eq_constOne_sub_zetaImage_add_delta` cite)。
      本体は実 Lean 証明 (`e=pq`=field cite、grid 展開=`abel`)。bare sorry → faithful producer のみ isolate。
- [x] **(14.16) dual** `caseB_character_contradiction_of_gap_inequalities` ✅: `CaseBContradictionData`
      faithful carrier (β_L=Σ±η−χ_L 展開 + η/χ_L ⊥ ψ^τ₁ 直交性 + (β_L,ψ^τ₁)≠0 case-b) + `caseB_contradiction_data`
      producer + `inner_finset_sum_left` helper。本体は実 inner 計算 `(β_L,ψ^τ₁)=Σε·0−0=0` で pairing≠0 と矛盾。

## 完了条件

`normCascadeBound_of_charData` / `betaM_expansion` が S09 cite による honest assembly になり、
直接 sorry が bridge carrier (faithful) のみに帰着。**betaM_expansion 達成済** (2026-06-26)。

## 参照

- 正本: `notes/peterfalvi/s16_w4_char_cascade.md`、`notes/meta/ft_frontier_remap_2026_06_25.md` §2 W4
- S09 §7 API: `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean` (Hypothesis71:110 / family_inequality:687 /
  Hypothesis78:1433 / beta:1487)
- 本セッション: generic_character_bound de-opacify (commit `483a5716`)
