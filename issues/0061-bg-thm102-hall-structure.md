---
id: 61
slug: bg-thm102-hall-structure
title: "BG Thm 10.2 Hall structure of M_sigma/M_alpha (§10 MAIN)"
created: 2026-06-05
---

# BG Thm 10.2 Hall structure of M_sigma/M_alpha (§10 MAIN)

## 背景

Thm 10.1 (`fusion_control_of_mem_sigma`) 完成 (commit c18ab13、issue 0060 closed) で解禁。
**Thm 10.2 = §10 の MAIN result**: これが通れば Thm 10.6 → Cor 10.7 → Lem 10.8 / Cor 10.9 /
Prop 10.10-14 が次々解禁される gateway。mmd L2713-2743。

**Target**: `OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha` (S10_MalphaMsigma.lean)。
scaffold は **reduced 版** (原典 (d) の `r(M/M_α)≤2 ∧ M'/M_α nilpotent` は quotient Normal instance
整備後に追加予定、として省略済):
```
IsHallSubgroup (sigma M) (Msigma M) ∧ IsHallSubgroup (alpha M) (Malpha M) ∧
Malpha M ≤ Msigma M ∧ Msigma M ≤ derivedInG M ∧ Msigma M ≠ ⊥
```

## 依存状況 (2026-06-05 検証済)

| 依存 | 状態 | repo 名 |
|---|---|---|
| Thm 9.6 (Uniqueness) | ✅ | `Ch2.S09.uniquenessTheorem` |
| Thm 10.1 (fusion) | ✅ | `S10.fusion_control_of_mem_sigma` (本ファイル) |
| Focal Subgroup Thm | ✅ (要接続) | `Ch05.focalSubgroupTheorem` (`commutator G ⊓ P = P.focalSubgroup` 形; BG の `⟨x⁻¹y⟩` 形と接続要) |
| Thm 4.20 | ✅ (package) | `S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two` + `S04g/S05.derived_le_fitting_of_rank_fitting_le_two` |
| Hall π-部分群 存在 (solvable) | ✅ | `Ch03` `∃ H, IsHallSubgroup π H` (Main.lean:838 等) / `S01_Solvable:634` |
| σ⟹Sylow of G in M | ✅ | `S10.exists_sylow_le_of_mem_sigma` (private, 本ファイル) |
| **商 F(M/M_α) の rank/Fitting/normal-Hall 機械** | ⚠️ **未整備の可能性** | quotient `M ⧸ Malpha`, `fittingInG` of quotient, rank of quotient — (a)/(b) の核心、要調査 |

## 証明構造 (BG 忠実, mmd L2721-2743)

1. M(α) = Hall α(M)-部分群 of M (存在 ✅)。任意の非自明 Sylow P of M(α) で r(P)≥3 ⟹ Thm 9.6 で
   P∈𝒰 ⟹ N_G(P)⊆M ∧ P Sylow of G ⟹ **α(M)⊆σ(M)** ∧ M(α)⊆M(σ)=Hall σ-部分群 of G。
2. 任意 p∈σ(M): P Sylow-p of M ⟹ N_G(P)⊆M ⟹ P Sylow-p of G。Focal Thm + **Thm 10.1 (X=⟨x⟩)**
   で全 G-fusion が M-fusion ⟹ P=P∩M'⊆M' ⟹ **M(σ)⊆M'**。
3. ⟹ M(α)⊆M(σ)⊆M' (10.3)。
4. F(M/M_α) は α(M)'-group で rank≤2 (α 定義)。M_α⊆M(α)。Thm 4.20 で M(σ)/M_α⊆M'/M_α=(M/M_α)'⊆F(M/M_α)
   ⟹ M(σ)/M_α は α'-group ⟹ (10.3 と) **M(α)=M_α** [(a)]。M(σ) Hall ⟹ M(σ)/M_α は F(M/M_α) の Hall
   かつ M/M_α に normal ⟹ M(σ)⊴M ⟹ **M(σ)=M_σ** [(b)]。(c)=10.3。
5. (e): M_α=1 と仮定 ⟹ r(M)≤2。q=|M| 最大素因子。Thm 4.20 で O_q(M)=Sylow-q of M。N_G(O_q(M))=M
   ⟹ q∈σ(M) ⟹ **M_σ≠1**。

## やること

- [x] **`alpha_subset_sigma`** (α(M)⊆σ(M)): Step 1 の核。Thm 9.6 + 𝒰⟹N_G(P)⊆M (10.1 の r(P)≥3
  分岐と同パターン)。商不要・自己完結。**⟹ `Malpha M ≤ Msigma M`** も従う (opiCore monotone)。✅ commit 7af327a
- [x] **`sylow_le_derived_of_mem_sigma`** (per-Sylow, Step 2 の核): p∈σ で Sylow-p P̄⊆M'。
  `ControlsFusionIn`(=Thm 10.1(a) を X=⟨x⟩ で適用)+ `focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn`
  (Isaacs Cor 5.22) + Focal Thm + `commutator_eq_top`(G'=G)。axiom-clean。helper:
  `commutator_eq_top` / `isSylow_sylowMap_of_mem_sigma`(全 Sylow-p of M は G の Sylow)。✅
- [x] **`Msigma_le_derived` / `hallSigmaSubgroup_le_derived`** (Step 2: Hall σ-subgroup ⊆ M'):
  Focal + Thm 10.1 の per-Sylow proof `sylow_le_derived_of_mem_sigma` から、finite Sylow-generation
  で `M_σ⊆M'` を完成 (commit 970e458)。さらに任意の Hall `σ(M)`-subgroup `S≤M` について
  `S≤M'` へ一般化済み。これは後続の `M(σ)/M_α ≤ M'/M_α` に直接使う。
- [x] **conditional Hall transport support**: `opiCoreInG_subgroupOf_isHall_of_isHall` /
  `piSubgroup_le_opiCoreInG_of_isHall` を一般形として追加し、`Malpha_*` / `Msigma_*`
  specializations を公開。G-level の `IsHallSubgroup π O_π(M)` から `↥M` 内 Hall 性と
  「M 内の π-subgroup は `O_π(M)` に吸収される」を切り出し、§11 の重複 proof を削減。
- [x] **conditional quotient rank part of (d)**: §4 の既存 lemma
  `Ch1.S04.pRank_quotient_le_of_coprime` を public 化し、`rank_quotient_Malpha_le_two_of_isHall`
  を追加。Hall `α(M)` 連言が得られれば、BG 10.2(d) の `rank(M/M_α)≤2` は完成済み。
- [x] **Hall `α(M)` transport / existence of `M(α)`**: `not_dvd_index_of_mem_sigma` で
  `p∈σ(M) ⇒ p∤[G:M]` を公開し、`hallAlphaSubgroup_isHallInG` /
  `exists_hallAlphaSubgroup_isHallInG` により Hall-E で得た `M` 内の `α(M)`-Hall subgroup を
  `G` 内の `α(M)`-Hall subgroup として使えるようにした。残る `M(α)=M_α` 同定後、
  target の G-level Hall `α(M)` 連言へ直結する。
- [ ] **`Msigma_ne_bot`** (M_σ≠1, (e)): easy branch `Msigma_ne_bot_of_Malpha_ne_bot`
  (M_α≠⊥ ⇒ M_σ≠⊥) は完成。残りは M_α=⊥ なら r(M)≤2
  (Thm 4.20/(d) 要) + O_q Sylow + N_G(O_q)=M。`q∈σ(M) ∧ O_q(M)≠⊥ ⇒ M_σ≠⊥`
  の最終bridgeは `Msigma_ne_bot_of_opiCoreInG_singleton_ne_bot_of_mem_sigma` として切り出し済み。
  さらに `P.map = O_q(M)` と `N_G(O_q(M))≤M` から直接 `M_σ≠⊥` を返す
  `Msigma_ne_bot_of_sylowMap_eq_opiCoreInG_singleton` も追加済み。
  `Msigma_ne_bot_of_normal_local_sylow` / `Msigma_ne_bot_of_characteristicSylowSeriesPackage` /
  `Msigma_ne_bot_of_rank_fittingInG_le_two` / `Msigma_ne_bot_of_rank_le_two` により、§4.20(c)
  package、`rank F(M)≤2`、`rank M≤2` の入力からも `M_σ≠⊥` まで接続済み。
  `IsMinimalSimpleOdd.ne_bot_of_mem_maximalSubgroups` により `M` の非自明性は最大部分群仮定から
  自動生成済み。`rank_le_two_of_Malpha_eq_bot_of_isHall` /
  `Msigma_ne_bot_of_Malpha_eq_bot_of_isHall` により、Hall `α(M)` 連言が得られれば
  `M_α=⊥` hard branch も `rank M≤2` bridge に接続済み。
  **残りは Hall `α(M)` / `σ(M)` の2連言を作り、capstoneで `M_α=⊥`/`≠⊥` を場合分けする配線**。
- [ ] **商 F(M/M_α) の機械** (a)/(b) の Hall-ness: `IsHallSubgroup` 2 連言。**最重**。
  `rank(M/M_α)≤2` は Hall `α(M)` 仮定の下で `rank_quotient_Malpha_le_two_of_isHall` により
  接続済み。`fitting_quotient_oPiCore_isPiGroup_compl` /
  `fitting_quotient_Malpha_isPiGroup_alphaCompl` により BG の
  **`F(M/M_α)` is an α'-group** は Hall `α(M)` 仮定なしで完成。さらに
  `rank_fitting_quotient_Malpha_le_two` により **`rank F(M/M_α)≤2`** も Hall 仮定なしで完成し、
  `derived_quotient_Malpha_le_fitting` / `Msigma_quotient_Malpha_le_fitting` /
  `Msigma_quotient_Malpha_isPiGroup_alphaCompl` により `M'/M_α≤F(M/M_α)`、
  `M_σ/M_α≤F(M/M_α)`、および `M_σ/M_α` の α'-性も Hall 仮定なしで接続済み。
  さらに `hallSigmaSubgroup_quotient_Malpha_le_fitting` /
  `hallSigmaSubgroup_quotient_Malpha_isPiGroup_alphaCompl` により任意の Hall `σ(M)`-subgroup
  `S≤M` の像も `F(M/M_α)` 内の α'-group になり、
  `alphaSubgroup_le_Malpha_of_le_hallSigmaSubgroup` で `A≤S` なる α-subgroup は
  すでに `M_α` に入るところまで接続済み。
  残りは
  `M(α)=M_α`・`M(σ)=M_σ` を同定して Hall 2連言を作る部分。
- [ ] capstone `isHall_Msigma_Malpha` 配線。

## 完了条件

`isHall_Msigma_Malpha` の sorry が消え、build-green + axiom-clean ([propext,choice,Quot.sound])。
→ Thm 10.6 (`proper_hasPLengthOne`) 解禁。

## 参照

- notes: `notes/bg/s10_malpha_msigma.md`。
- Thm 10.1: issue `issues/closed/0060-bg-thm101-fusion-control.md`。
- mmd: `references/bg/local-analysis.mmd` L2713-2743。
