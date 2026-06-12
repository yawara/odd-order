---
id: 8001
slug: s13-tau3-sylow-derived
title: "§13 (a) gate: τ₃ Sylow⊆M' (sylow_le_derived_of_mem_tau3) が private+E専用"
created: 2026-06-12
---

# §13 (a) gate: τ₃ Sylow⊆M' が private + E 専用

## 背景

Lane G (`bg-s13`) の Lemma 13.1 結論 **(a)** (`M∩M*` の全 `p`-部分群が `M_σ∩M*` を中心化) の
証明 (mmd L3542) は `P ⊆ K_a = O_{α(M*)∪{p}}(M*') ⊴ M*` を経由する。`K_a ⊆ M*'` ゆえ
`P ⊆ K_a` は **`P ⊆ M*'`** を要する。

Lemma 13.1 の設定で `p ∈ σ(M*) ∪ τ₃(M*)` (結論 (b) で τ₂ 除外)。よって**全 Sylow `p` ⊆ M*'**
(subgroup 包含) が必要:
- **σ(M*)**: Sylow `p` ⊆ M*_σ ⊆ M*' — `S13_Lemma131.mem_primeFactors_derived_of_not_tau1_tau2`
  の σ-branch (`sigma_subgroup_le_Msigma_of_isHall` + `Msigma_le_derived`) が既に subgroup 版で
  確立済み。流用可。
- **τ₃(M*)**: `p ∉ σ(M*)` ゆえ Sylow `p` of M* = Sylow `p` of complement E* ⊆ E*' ⊆ M*'。
  これは **`sylow_le_derived_of_mem_tau3` (S12_ECore.lean:548)** が与える事実だが、現状
  **`private` かつ E (complement) 専用**。Lane G から呼べない。

結論 (c) (`mem_idealPrime_of_tau1_of_interaction`, 完成済) は `p ∈ π(M*')` (cardinality
`p ∣ |M*'|`) だけで足り Burnside を回避できたが、(a) は **subgroup 包含 `P ⊆ M*'`** ゆえ
回避不能。

## やること

- [ ] `sylow_le_derived_of_mem_tau3` (S12_ECore.lean:548) を **de-private (public 化)**。
      `private` を外すだけ (証明本体不変, build/AxiomsCheck 不変)。namespace
      `OddOrder.BG.Ch3.S12`。実施 owner = **hub / Lane F** (S12_ECore = §12 域)。
      現状シグネチャ:
      ```lean
      theorem sylow_le_derived_of_mem_tau3 [Finite G] (hG : IsMinimalSimpleOdd G)
          {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
          (hp : p ∈ tau3 M) (P : Sylow p ↥E) :
          (P : Subgroup ↥E).map E.subtype ≤ derivedInG E ∧
          Subgroup.centralizer (E : Set G) ⊓ (P : Subgroup ↥E).map E.subtype = ⊥
      ```
- [ ] (任意) より直接的な公開補題 `sylow_le_derivedInG_of_mem_sigma_union_tau3`
      (maximal M, p∈σ∪τ₃ ⟹ Sylow p of M ⊆ derivedInG M) を §12/§10 に追加してもよいが、
      de-private のみで Lane G 側は組める (`exists_subgroupESetup` で E* を取り、
      `Sylow p of M* = Sylow p of E*` [p∉σ] + 上記補題 ⟹ `Sylow p of M* ⊆ E*' ⊆ M*'`)。

## 代替 (de-private 不可なら)

Lane G が S13 で τ₃ Burnside transfer を再証明 (~40 行, `sylow_le_derived_of_mem_tau3` の複製;
DRY 違反だが即時 unblock)。

## 完了条件

`sylow_le_derived_of_mem_tau3` が public になり、Lane G が cite して Lemma 13.1 (a) を証明できる。

## 参照

- 論法: `notes/bg/s13_prime_action.md`「step 5 = (a) centralization」
- repo: `S12_ECore.lean:548` (private 補題), `S13_Lemma131.lean`
  (`mem_primeFactors_derived_of_not_tau1_tau2` の σ-branch = subgroup 版 template)
- mmd: `references/bg/local-analysis.mmd` L3542
- 関連: issue 8000 (§13→§12 forward axiom bridge)
