---
id: 5000
slug: bg-prop1010-normalizer-factorization
title: "BG Prop 10.10 normalizer_factorization (forward-conditional, §7-gated)"
created: 2026-06-09
---

# BG Prop 10.10 normalizer_factorization (forward-conditional, §7-gated)

## 背景

`OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadical.lean:2660` (`normalizer_factorization`) =
§10 で残る唯一の sorry。Cor 10.7 (`sylow_structure`) 完成 (commit `a1767214`) で part (b) の
前提 `P ⊆ N_G(P)'` は供給可能になった。本体は §7 (Thompson transitivity) に依存。

mmd 出典: `references/bg/local-analysis.mmd` L2874-2884。

## statement (既存・変更不要)

`p ≠ q`, `A ∈ ℰ_p²(G)∩ℰ_p*(G)` (= `elemAbelianOfRank G p 2` ∧ `IsMaximalElementaryAbelian p A`),
`Q ∈ ℋ_G*(A;q)` (= `hInvariantStar ⊤ A {q}`), `q ∈ π(C_G(A))` ⇒ ∃ Sylow p `P ⊇ A` で:
- (a) `N_G(P) = O_{p'}(C_G(P)) · (N_G(P) ∩ N_G(Q))` (Lean: 任意 `n ∈ N_G(P)` が `c·m` 形,
  `c ∈ opiCoreInG {p}ᶜ (C_G(P))`, `m ∈ N_G(P) ⊓ N_G(Q)`)
- (b) `P ≤ derivedInG (N_G(Q))`
- (c) `Q` cyclic ∨ `ℰ²(Q)∩ℰ*(Q) ≠ ∅` ⇒ `P ≤ C_G(Q)`

## BG 証明 (mmd L2880-2884)

1. **(a)**: Prop 7.5 で `A` が Hypothesis 7.1 を満たす。Thm 7.3 + Thm 7.4 が `A ⊆ P` なる
   Sylow p `P` を与え (a) を満たす。**= 本 issue の hard core**。
2. **(b)**: Cor 10.7 (✅ `sylow_structure`.1) で `P ⊆ N_G(P)'`。(a) + **Lem 6.5** で (b)。
3. **(c)**: (c) 仮定下で `N_G(Q)'/C_{N_G(Q)'}(Q)` は q-群 (**Thm 5.5(a)**)。よって `P ≤ C_G(Q)`。

## やること

- [ ] §7 API 精査: `transitive_of_two_le_rank_center_of_dvd` (S07:958, A∈ℰ_p² 系の transitivity),
      `thompsonTransitivity` (S07:3657, scn3 系), `hypothesis71_of_*` (Prop 7.5), Thm 7.4 propagation
      (`transitivity_propagates` S07:2139) のどれが (a) の Sylow-P-存在 + factorization を供給するか同定。
- [ ] (a) の factorization は transitivity からの **Frattini 論法**で導く必要がある可能性大
      (O_{p'}(C_G(P)) が ℋ_P*(A;q) 上推移的 ⟹ N_G(P) = stab · transitive-part)。§7 capstone が
      この形を直接出すか、新たに組むかを判断。
- [ ] (b): `sylow_structure hG P |>.1 V ... ` から `P ≤ derivedInG (N_G(P))`; Lem 6.5
      (`inf_commutator_eq_of_coprime` S06 系) で `N_G(P)' → N_G(Q)'` へ。
- [ ] (c): Thm 5.5(a) (`narrow_sylow_solvable_structure` 系 or §5) で q-群、`P ≤ C_G(Q)`。
- [ ] forward-axiom island (Cor 10.7 経由 ⟹ 2 forward axiom) を AxiomsCheck に登録。

## 完了条件

`normalizer_factorization` の sorry が消え、leaf + full build green、`#print axioms` =
standard 3 + `pLengthOne_commutator_of_zgroupCentralizer` +
`exists_prime_orderOf_zgroupCentralizer_of_complement` ちょうど (Cor 10.7 経由の §10 keystone island)。

## 参照

- Cor 10.7 完成: commit `a1767214`, notes `notes/bg/s10_spine_blockers.md`「Cor 10.7 COMPLETE」節。
- §7: `OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean` (全 sorry-free)。
- consumer: Prop 10.11 (mmd L2901 が Prop 10.10 を引用), §13。
