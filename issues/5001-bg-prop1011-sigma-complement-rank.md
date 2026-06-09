---
id: 5001
slug: bg-prop1011-sigma-complement-rank
title: "BG Prop 10.11 sigma_complement_rank_le_one (a)(b)(c) (forward-conditional)"
created: 2026-06-10
---

# BG Prop 10.11 sigma_complement_rank_le_one (a)(b)(c) (forward-conditional)

## 背景

`OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean:451` (`sigma_complement_rank_le_one`) =
§10 で残る sorry (Lemma 10.13 を除く D-lane 対象)。**(b) は Prop 10.10 (`normalizer_factorization`,
commit `de75651e` で完成) を使う** ので依存解消済 → 着手可能。

mmd 出典: `references/bg/local-analysis.mmd` L2856-2880 (Prop 10.11 statement + proof)。

## statement (既存・変更不要)

`M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群 (`Subgroup.IsPiSubgroup (sigma M)ᶜ K`, `K ≤ M`) とすると:
- (a) `K ∉ 𝒰` (`¬ IsUniquelyMaximal K`)
- (b) `r(C_K(M_σ)) ≤ 1` (`rank ↥(C_G(M_σ) ⊓ K) ≤ 1`)
- (c) `C_K(M_σ) ∩ M'` は cyclic で `M` に normal
  (`IsCyclic ↥(C_G(M_σ) ⊓ K ⊓ M') ∧ M ≤ N_G(C_G(M_σ) ⊓ K ⊓ M')`)

原典 (d) は別 theorem `sigma_complement_commutator_cyclic_normal` に分離済 (本 issue 対象外)。

## BG 証明 (mmd L2860-2880)

- **(a)**: `E` を `K` を含む Hall `σ(M)'`-subgroup of `M`。`p` = `|E|` の最大素因子。
  `α(M) ⊆ σ(M)` ゆえ `r(E) ≤ 2`。**Theorem 4.20** で `P = O_p(E)` が `E` の (ゆえ `M` の)
  Sylow `p`。`p ∉ σ(M)` ⟹ `N_G(P) ⊄ M`。よって `K ⊆ E ⊆ M ∩ N_G(P)` から `K ∉ 𝒰`。
- **(b)**: `r_p(C_K(M_σ)) ≥ 2` なる `p` を仮定 (背理法)。`A ∈ ℰ_p²(C_K(M_σ))`, `q ∈ σ(M)`,
  `Q` = Sylow q of `M_σ`。すると `Q ∈ ℋ_G*(A;q)`, `q ∈ π(C_G(A))`, `N_G(Q) ⊆ M`。
  (a) で `A ∉ 𝒰` ⟹ **Uniqueness Theorem** で `r(C_G(A)) ≤ 2` かつ `A ∈ ℰ_p*(G)`。
  `M_α ⊆ M_σ ⊆ C_G(A)` ⟹ `M_α = 1`。**Theorem 10.2** で `M'/M_α` nilpotent ⟹ `M'` nilpotent。
  **Proposition 10.10** ✅ で ある Sylow p `P` が `N_G(Q)' ⊆ M'` に入る ⟹ `P = O_p(M') ⊴ M`,
  `M = N_G(P)`, `p ∈ σ(M)`。しかし `p ∈ σ(K) ⊆ σ(M)'`。矛盾。
- **(c)**: (b) を `Z = O_{σ(M)'}(F(M))` に適用 (`[Z,M_σ] ⊆ Z ∩ M_σ = 1`) ⟹ `Z` cyclic。
  `M' ⊆ C_M(Z)` かつ `C_K(M_σ) ∩ M' ⊆ C_M(M_σ Z) ⊆ C_M(F(M)) ⊆ F(M)`。

## やること / 依存の現状

- [ ] **(a)**: **Theorem 4.20** (「`E` 可解, `r(E)≤2`, `p` 最大素因子 ⟹ `O_p(E)` が Sylow p」)
      の正確な Lean 形を同定。`S04g_Thm418.lean` に 4.20(c) machinery はあるが capstone 形を要確認。
      `α(M) ⊆ σ(M)` (`alpha_subset_sigma`) で `r(E) ≤ 2`。`N_G(P) ⊄ M` は `p ∉ σ(M)` から。
- [ ] **(b)**: **Uniqueness Theorem** の必要方向 = 「`A ∉ 𝒰` ⟹ `r(C_G(A)) ≤ 2` ∧ `A ∈ ℰ_p*(G)`」。
      S09 capstone は対偶 (`r ≥ 3 ⟹ 𝒰`)。`isUniquelyMaximal_of_three_le_rank_of_lt_top` の対偶 +
      `A ∈ ℰ_p*` の導出を要確認。**Thm 10.2 の M_α 形**: 現状 `derivedQuotientMbeta_isNilpotent`
      は M'/M_β。M_α=1 のケースでは M_β=M_α=1 で M' nilpotent が出るか要確認 (or M_α 版を別途)。
      Prop 10.10 適用部は `normalizer_factorization` (✅) を直接呼ぶ。
- [ ] **(c)**: `Z = O_{σ(M)'}(F(M))`, `[Z, M_σ] ⊆ Z ⊓ M_σ = 1`, Fitting/centralizer 包含チェーン。
- [ ] forward-axiom island (Prop 10.10 / Cor 10.7 経由) を AxiomsCheck に登録 (同 keystone island)。

## 完了条件

`sigma_complement_rank_le_one` の sorry が消え、leaf + full build green、`#print axioms` =
standard 3 + `pLengthOne_commutator_of_zgroupCentralizer` +
`exists_prime_orderOf_zgroupCentralizer_of_complement` ちょうど。

## 参照

- Prop 10.10 完成: commit `de75651e`, `notes/bg/s10_spine_blockers.md` 2026-06-10 更新節。
- §10 残 sorry: 本 Prop 10.11 + Lemma 10.13 (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`,
  `S10_LocalLemmas.lean:1063`, group-level Additive diamond で D 対象外)。
