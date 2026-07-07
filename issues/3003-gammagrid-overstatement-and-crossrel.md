---
id: 3003
slug: gammagrid-overstatement-and-crossrel
title: "gammaGrid_independent overstatement 修正 + (5.3) cross-relation 分離 (Pf 13.18.c/d faithful 化)"
created: 2026-07-08
---

# lane c: `gammaGrid_independent` overstatement 修正 + (5.3) cross-relation 分離

## 発見 (2026-07-08 lane c, item 3 (B) 着手時)

`S15_SAndT.lean` の `BetaData` carve-out (c 所有、issue 0098 item 3) の **2 フィールドが
Peterfalvi (13.18) の overstatement**。教科書原文 (`04.15_pp_75_86` line 292-300) + Coq
`FTtypeP_bridge_facts` (PFsection13.v:1792-1802) の statement と照合して確定:

### (13.18) 正文 (Coq `FTtypeP_bridge_facts` + 教科書)
- **(a)** `Supp(β_j) ⊆ P^# ∪ (W−(W₁∪W₂))^S ⊆ A₀(S)` (2 形: A₀(S) と P^#∪V_S)
- **(b)** `‖β_j‖² = (u−1)/q + 2` ✅ **実証明済** (`betaGrid_norm`, commits cc01d946/dcda9592)
- **(c)** `Γ = β_j^τ − 1_G + η_{0j}` は **(i) j に非依存 (independent of j)** ∧ (ii) `⟨Γ,1⟩=0` ∧ (iii) real
- **(d)** `Γ = X + Y` (X = η_{ik} の線形結合, Y ⊥ η_{ik}) とおくと **`‖Y‖² ≤ (u−1)/q`**
- tail: `q ∣ u−1`

### Lean scaffold の 2 overstatement
1. **`Gamma_independent : ∀ i k, ⟨Γ, η_{ik}⟩ = 0`** (S15_SAndT.lean:3594, thm :3995) —
   **FALSE**。(13.18.c) の "independent of **j**" は「列 index j に非依存」= `defGamma`
   (`∀ j≠0, τ_S(β_j) − 1 + η_{0j} = Γ`) の意味であって「grid 直交」ではない。
   docstring は (13.18.a) と誤ラベル (実際 (a) は support)。**反証**: Coq (13.18.d) は
   `Γ = X+Y` (X ∈ span grid, Y ⊥ grid) の非自明分解で `‖Y‖²` を bound する
   (PFsection13.v:1915 `pose a := '[Gamma, eta01]` を**一般の非零整数**として使用)。
   Γ が grid 直交なら X=0 で (d) は自明 = 矛盾。
2. **`Y_norm_bound : Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1`** (S15_SAndT.lean:3604, thm :4033) —
   genuine (13.18.d) でない。`‖Γ‖² = ‖X‖²+‖Y‖²` で X (grid 成分) 次第。genuine は
   grid-**直交成分** Y のみの `‖Y‖² ≤ (u−1)/q`。現 ‖Γ‖² proxy は a=⟨Γ,η01⟩ 依存で
   **偽の可能性** (X≠0 で ‖Γ‖² > (u−1)/q+1 になり得る)。

### 現状 consumer = 0 (vestigial as wired) — ただし on-path
`beta_support_norm_and_remainder` / `BetaData` / `betaData_of_grid` は **repo 全体で consumer 0**。
ただし Coq では (13.18) = `FTtypeP_bridge_facts` を §14 (PFsection14.v:541/713/763) が consume
= **genuine on-path** (Lean consumer は 0098 item 4 §14 Γ-bridge assembly で予定、未配線ゆえ
現状 vestigial に見えるだけ)。∴ 破棄でなく **faithful 修正**が正 (doneness 原則)。

## やること (このセッション)

- [ ] **(1) `BetaData` faithful 化**: `Gamma_independent` (偽) → `Gamma_def` (defGamma per-column
      `τ_S(betaGrid j) − constOne + η_{0j} = Gamma`); `Y_norm_bound` → genuine (13.18.d) X+Y form。
- [ ] **(2) defGamma 実証明 modulo 分離 cross-relation**: glue (linearity) は実証明、deep 部分を
      **単一 named sorried theorem** `tauS_mu_row0_cross` に isolate:
      `τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` (Pf (4.8)/(5.3), Coq `prDade_sub_TIirr` PFsection4.v:870,
      FT context で δ_j=1 via `FTprTIsign`)。
- [ ] **(3) `gammaGrid_norm_bound` → genuine (13.18.d)** 文faithful restate (sorried、deep: isometry+support gated)。
- [ ] notes/peterfalvi/s15_s_and_t.md に finding 追記。

## 残る deep obligation — ★全て §3 cyclicTI rigidity に bottom-out (issue 9076 に claim 済)

**2026-07-08 精査確定**: 下記 4 obligation は**全て同一 gate = §3 cyclicTI rigidity
`eq_signed_sub_cTIiso` (Coq PFsection3.v:1681) → `prDade_sub_TIirr` (PFsection4.v:870)** に還元。
= issue **9076** (shared-infra claim、§4/§10/§11/§13 broad consumer) で multi-piece port を追跡。

- `tauS_mu_row0_cross` = (4.8) cross-relation `τ_S(μ_0j−μ_01)=η_0j−η_01`。Coq defGamma が
  `prDade_sub_TIirr` で discharge → `eq_signed_sub_cTIiso` 適用。**repo 不在** (9076 piece 4)。
- `betaGrid_support` (13.18.a) = Frobenius `gammaW1` cancellation (Coq `PVSbeta` PFsection13.v:1833)
  も `cfRes_prTIirr`/`prTIirr_id` prime-TI 値を使用 → 同じ cyclicTIiso stack。
- `gammaGrid_orthogonal_one` (⟨Γ,1⟩=0) = Dade=Ind bridge (`sInstance_dade_eq_induce` 既存) +
  `betaGrid_support` gated (∴ 間接的に 9076 gated)。
- `gammaGrid_real` = conjugation-commutation (Coq `cfAutInd`/`prTIirr_aut`) → 同 stack。

**σ-isometry 土台は既存** (`S05.TICyclicHypothesis.sigmaIntegral`、旧 lane d)。9076 = その image の
**rigidity** (norm-2 characterization、9014 residue API とは別層だが同 provenance)。着手前に lane-a
(§10-13 consumer) と coordination 要 (2026-07-02 dup 予防、9076 interface guard)。

## 完了条件
- overstatement 2 フィールドが genuine (13.18) statement に置換され、build green + AxiomsCheck OK。
- defGamma が isolated cross-relation cite で実証明 (glue sorry-free)。
- 残 sorry は上記 4 deep obligation に限定 (opaque でなく named + docstring で性質明示)。

## 参照
- 教科書 (13.18): `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd` line 292-300。
- Coq `FTtypeP_bridge_facts` = PFsection13.v:1792 (defGamma :1905, prDade_sub_TIirr 使用 :1908)。
- cross-relation `prDade_sub_TIirr` = PFsection4.v:870 (`τ(μ2_ij − μ2_ik) = δ_j(η_ij − η_ik)`, 要 degree 等)。
- issue 0098 (lane c package item 3), 9074 (closed, (13.18.b) betaGrid_norm)。
