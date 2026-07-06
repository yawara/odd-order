---
id: 9017
slug: bg-15-9-centralizer-escape-multi-consumer
title: "shared-infra: BG Cor 15.9 (centralizer_escape_final_local) + Thm 15.8 — S16 escape package + Pf §13 S-instance TI-set の multi-consumer gate"
created: 2026-07-06
---

# shared-infra claim: BG §15 Cor 15.9 (Sibley/FT escape package) — S16 + Pf §13 の multi-consumer gate

> **claim-before-build (lane b, issue 1017 /loop から派生)**。BG §15 の残 bare sorry
> `centralizer_escape_final_local` (BG Cor 15.9) が **2 クラスタ**から consume される cross-cluster
> gate と判明。lane b (Pf §13 coherence) と lane c (S16) が共に下流。**現状どのレーンも未 claim** (9000 scan 済)。
> owner/分担は hub 裁定。本 issue = gate の可視化 + dedup。

## 何が gate か

**`centralizer_escape_final_local` (`OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean:9407`) = BG Cor 15.9**
(mmd L4240、"final local landing point for a centralizer escaping M — Sibley/Feit–Thompson package used by §16")。
現状 **bare `sorry`** (L9421)。statement: escaping `x ∈ σ-sharp(M)` (`C_G(x) ⊄ M`)、signalizer `N`
(¬type-F) から `IsTypeF M ∧ ¬FittingIsTI M ∧ IsTypeP2 N ∧ ∃ Frobenius complement E, r ∈ tau2 N, …`。

隣接: **`tau2_transfer_constraint` (`S15_MF.lean:9397`) = BG Thm 15.8** (mmd L4264) も **bare sorry** — Cor 15.9 の
上流 (tau2 transfer)。

## 2 consumer (cross-cluster)

1. **BG side (lane c 領域)**: `exists_RData_escape_structure` (`S16_MainResults.lean:5695`) が L5764 で
   `centralizer_escape_final_local` を直接 cite → S16 の RData escape 構造 (`#print axioms` sorryAx-tainted)。
2. **char side (lane b 領域、issue 1017)**: Pf §13 S-instance coherence の `tau1S_apply_induce_sub` (dade=Ind on
   A(S)) は `IsTISubset (honestTypeP2ASet S) S` に還元 (Rung B、commit d375f39c、sorry-free)。その
   escaping-exclusion (Coq `FTtypeP_facts` (e) PFsection13.v:224-234 port) の **case IsTypeP2 N** が
   `exists_RData_escape_structure` 経由で本 sorry に gated。

⟹ **本 gate を閉じると S16 の escape package と Pf §13 coherence の dade=Ind が同時に honest 化** (high-leverage)。

## やること

- [ ] **BG Thm 15.8 `tau2_transfer_constraint`** (S15_MF:9397) を build (mmd L4264、tau2(H) nonempty ⟹
      tau2(M)=∅ ∧ q=|K| prime ∧ tau2(H)={q})。
- [ ] **BG Cor 15.9 `centralizer_escape_final_local`** (S15_MF:9407) を build (mmd L4240、Sibley package)。
      依存: Thm 15.8 + §15 の他 machinery (要 scope)。
- [ ] **`FTtype1_Frobenius` kernel-regularity analogue** (case IsTypeF N): repo type-F `N` は
      `frobenius_HU0 : IsFrobeniusGroup (H⊔U0) H U0` のみ (global Frobenius 無) → Coq FT-type-1 の
      kernel-regularity 矛盾に対応する repo 補題を build (or type-F ⟹ global Frobenius bridge)。
- [ ] ⟹ Pf §13 側 (issue 1017 G2): 上を IsTISubset(A(S)) の escaping-exclusion に wire →
      `∀a, dadeHypS.H a=⊥` → bridge (A₁=A(S)) で dade=Ind → tau1S_apply_induce_sub honest 化。

## 完了条件

`centralizer_escape_final_local` + `tau2_transfer_constraint` の sorry が消える (S16 escape package honest 化)
かつ Pf §13 側で `IsTISubset (honestTypeP2ASet S) S` が sorry-free に landing (issue 1017 G2 解消)。

## 参照

- mmd: BG Cor 15.9 (L4240)、Thm 15.8 (L4264)。Coq: `BGsummaryII` / `FTsupport_facts` (c4) /
  `Frobenius_of_typeF` / `typePF_exclusion` (PFsection13.v:224-234)。
- repo landed (char-side wiring 完備): `sInstance_dade_eq_induce_of_supported_trivial_H` (bridge, cd6beac7)、
  TI-set reduction 4 lemma (d375f39c)、`signalizer_structure_of_mem_sigmaSharp` (S16:271 sorry-free)、
  `isTypeF_iff_not_isTypeP` (S14:169 sorry-free)。
- issue 1017 更新 #20-#23 (full trace)。
