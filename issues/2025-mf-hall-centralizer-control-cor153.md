---
id: 2025
slug: mf-hall-centralizer-control-cor153
title: "Cor 15.3 mf_hall_centralizer_control = 次の FT-path W1 target [deep, 3 inputs]"
created: 2026-06-26
---

# Cor 15.3 `mf_hall_centralizer_control` = 次の FT-path W1 target [deep, 3 inputs]

## 背景 (2026-06-26 lane-c scoping)

lane-c は W1 寄与で (12.9) Hall complement (issue 2016) を着地後、**次の非衝突 FT-path W1 target**
を精査。orphaned な §14/§15 sorry (`sigmaLength_one_frobenius_type`/`exists_sigmaDecomposition_length_le_two`/
`typeP1_conjugate_and_typeP_twoClasses`/`centralizer_escape_final_local` = 全 0 consumer、off-path)
を除外し、**唯一の FT-path 接続を持つ §14/§15 sorry = `mf_hall_centralizer_control`** (Cor 15.3,
`S15_MF.lean:2483`) を同定。

### FT-path 接続 (重要)
```
mf_hall_centralizer_control (Cor 15.3)
  → theoremI_nilpotentHall_conjugacy_and_type_dichotomy (BG Thm I, S16:2852,
     "the BG output consumed by Peterfalvi (8.8)") [first assertion = fusion control; consumes hfusion @S16:2890]
  → Peterfalvi (8.8) dichotomy (Thm I second assertion = all-type-I ∨ case-(b))
  → theorem88_caseB_holds (Pf S14_MaximalI:1396, FT endpoint, FeitThompson:361)
```
⟹ lane-c の (12.7) `typeI_frobenius` work と**同じ endpoint に収束**。`ha` (part a 分解) も
`sylow_le_Msigma_of_le_centralizer_sylow` (S15:2756) → Cor 15.4 (`nilpotent_hall_embeds_in_msigma`)
→ Thm I 経由で FT-path。非衝突: `S15_MF.lean` は lane-f の hot file (S16_MainResults/NonExistenceG) と別。

## 構造 (tractability)

`mf_hall_centralizer_control_of_inputs` (S15:2424) は **sorry-free gated-endpoint skeleton**。
wrapper `mf_hall_centralizer_control` (S15:2483, sorry) は 3 input を discharge して skeleton 適用:

| input | 内容 | provenance (docstring L2411-2419) | 状態 |
|---|---|---|---|
| `ha` | `C_M(H) = (C_M(H)⊓M_σ) ⊔ X`, X cyclic τ₂ | Prop 14.2(b1)(e) + Lemma 15.1(c) | **deep** — H=M_σ 版 (`mf_centralizer_msigma_decomp`, sorry-free) は template だが、一般 Hall H 版は **`C_M(H)` が κ'-群** を要し M_σ 版 (`centralizer_msigma_isPiSubgroup_kappa_compl`) は一般化不可 (x が H を中心化しても M_σ を中心化しない) ⟹ 新 math |
| `hconj` | G-共役 H-元は M 内で共役 (∃ m∈M) | Theorem 14.4 + `normalizer_eq_self_of_mem_maximalSubgroups` (S15:2635, proven) | **deep** — Theorem 14.4 (∃ c∈C_G(x), M^{gc}=M) が citeable lemma として **未発見** |
| `hfratt` | H⋬M で Frattini factorization M=N_M(H)·Q | Theorem 15.2 の normal Q=O_q(M) + Frattini | **deep** — Theorem 15.2 O_q 要確認 |

## やること

- [ ] `ha` 一般 Hall H 版: `C_M(H)` κ'-群 lemma (新規) → SZ 分解 (H=M_σ template `mf_centralizer_msigma_decomp` を一般化)。
- [x] **`hconj`: 完了 (2026-06-26)** — `mf_hall_conj_realized_in_M` (S14_TypePCounting, sorry-free + axiom-clean)。
      Theorem 14.4 = `sigmaLength_one_centralizer_structure` (proven) は sharp transitivity を持つが
      conjugator の C_G(x) 所属を捨てていた → 新 helper `exists_conj_centralizer_of_mem_maximalSigma`
      で C_G(x)-witness を保持 → `normalizer_eq_self_of_mem_maximalSubgroups` で `cg⁻¹∈M` を導出。
      D は param 化 (caller が `dummySigmaDecomposition G` 等を供給)。
- [ ] `hfratt`: Theorem 15.2 O_q + Frattini argument。
- [ ] 3 input を `mf_hall_centralizer_control_of_inputs` に wire → wrapper sorry-free 化。
- [ ] ⚠ **wrapper signature gap**: `mf_hall_centralizer_control` (S15:2483) は `H ≤ M_σ` を欠く
      (`hH : IsHallSubgroup (piSet H) (H.subgroupOf M_σ)` からは導出不可)。hconj/ha は `H ≤ M_σ` 要 →
      wrapper に `hHMσ : H ≤ Msigma M` を追加要 (consumer S16:2890 [lane-f hot] + S15:2795 [lane-c] の
      call site に 1 引数追加; S16 編集 = lane-f 調整要)。

## 完了条件

`mf_hall_centralizer_control` が sorry-free ⟹ BG Theorem I (first assertion) の fusion gate 解消
→ Pf (8.8) dichotomy → `theorem88_caseB_holds` (FT endpoint) の (8.8) 入力に前進。

## 参照

- 主所有: `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean` (`mf_hall_centralizer_control` 2483 /
  `_of_inputs` 2424 / `mf_centralizer_msigma_decomp` 2509 template)。
- 消費: `S16_MainResults.lean:2890` (Thm I)。FT endpoint = `S14_MaximalI.lean:1396`。
- 関連: issue 0080 (W1 Prop 16.1 bridges, lane-f)、2016 (CLOSED, (12.9) Hall compl)、0081 (W2 §12)。
- ⚠ multi-session deep。lane-f の S16 hot file と非衝突 (別 file S15_MF)。
