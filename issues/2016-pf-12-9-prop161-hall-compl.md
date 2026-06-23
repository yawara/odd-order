---
id: 2016
slug: pf-12-9-prop161-hall-compl
title: "Discharge (12.9) Hall-complement obligation once Prop 16.1 lands"
created: 2026-06-23
---

# Discharge (12.9) Hall-complement obligation once Prop 16.1 lands

## 背景

`(12.9) counterexample_P0_K_structure` (`OddOrder/Peterfalvi/S14_MaximalI.lean`) is now a
gated-endpoint skeleton (commit `96c793b0`): it cites the **proven** BG Theorem B(1)
(`OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two`) + `two_le_rank_of_noncyclic_pSubgroup`
to get `P₀` abelian of rank `2`. The earlier note "(8.12.a) absent from repo" was **stale** —
Theorem B(1) is proved.

The sole remaining gap is the new sorried obligation `exists_sigmaKappaCompl_hall_ge_P0`
(`S14_MaximalI.lean`):

> the type-`I` minimal-counterexample `M` has a `(κ(M) ∪ σ(M))ᶜ`-Hall complement `U ⊇ P₀`.

This is the precise **Proposition 16.1** bridge: the type-data complement of `M_F` is
`π(M_F)ᶜ`-Hall (ungated — `M_F` is a normal Hall subgroup), and Prop 16.1's type-`I`
classification (`κ(M) = ∅`, `σ(M) = π(M_σ)`, `M_F = M_σ`) identifies `π(M_F)ᶜ` with `(κ ∪ σ)ᶜ`.

## やること

- [ ] Discharge `exists_sigmaKappaCompl_hall_ge_P0` once BG Proposition 16.1
  (`proposition_type_classification`, lane-f) is proved (or its type-`I` clauses κ=∅ / σ=π(M_σ) /
  M_F=M_σ are citeable). Route: take the type-`I` complement `U` (from `IsTypeI M` →
  `TypeIData.typeF.U`), show it is `π(M_F)ᶜ`-Hall (from `complement` + `M_F` Hall), rewrite
  `π(M_F)ᶜ = (κ∪σ)ᶜ` via Prop 16.1, and place `P₀` in it (Sylow `p`, `p ∤ |M_F|`, into a complement).

## 完了条件

`exists_sigmaKappaCompl_hall_ge_P0` is sorry-free ⟹ `(12.9) counterexample_P0_K_structure` and
hence `(12.9) exists_rankTwoWitness` become unconditional (axiom-clean modulo the rest of §16).

## 参照

- `OddOrder/Peterfalvi/S14_MaximalI.lean` — `exists_sigmaKappaCompl_hall_ge_P0`,
  `counterexample_P0_K_structure`.
- `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` — `theoremB_U_sylow_abelian_rank_le_two`
  (proven), `proposition_type_classification` (Prop 16.1, lane-f frontier).
- `notes/peterfalvi/s14_maximalI.md` — "(12.9) status (resume¹²)".
- **Trigger**: lane-f lands Prop 16.1 (its active frontier per `ft-endgame-two-poles`).
