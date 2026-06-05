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
  分岐と同パターン)。商不要・自己完結。**⟹ `Malpha M ≤ Msigma M`** も従う (opiCore monotone)。← まず landable
- [ ] **`Msigma_le_derived`** (M_σ⊆M', Step 2): Focal `focalSubgroup` 形 ⟷ fusion 接続 + Thm 10.1。商不要。
- [ ] **`Msigma_ne_bot`** (M_σ≠1, (e)): Thm 4.20 package から O_q Sylow 抽出 + r(M)≤2 case。商ほぼ不要。
- [ ] **商 F(M/M_α) の機械** (a)/(b) の Hall-ness: `IsHallSubgroup` 2 連言。**最重・要 quotient infra 調査**。
  - M(α)=M_α: M(σ)/M_α が α'-group + M(α) Hall。
  - M(σ)=M_σ: M(σ)/M_α normal Hall in F(M/M_α) char ⟹ M(σ)⊴M。
- [ ] capstone `isHall_Msigma_Malpha` 配線。

## 完了条件

`isHall_Msigma_Malpha` の sorry が消え、build-green + axiom-clean ([propext,choice,Quot.sound])。
→ Thm 10.6 (`proper_hasPLengthOne`) 解禁。

## 参照

- notes: `notes/bg/s10_malpha_msigma.md`。
- Thm 10.1: issue `issues/closed/0060-bg-thm101-fusion-control.md`。
- mmd: `references/bg/local-analysis.mmd` L2713-2743。
