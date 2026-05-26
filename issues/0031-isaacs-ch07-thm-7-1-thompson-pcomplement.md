---
id: 31
slug: isaacs-ch07-thm-7-1-thompson-pcomplement
title: "Isaacs Thm 7.1 Thompson normal p-complement"
created: 2026-05-26
---

# Isaacs Thm 7.1 Thompson normal p-complement

## 背景

**Isaacs Thm 7.1** (Thompson, mmd L3721):

> p ≠ 2, P ∈ Syl_p(G), C_G(Z(P)) and N_G(J(P)) both have normal p-complements
> ⇒ G has a normal p-complement.

7-step counterexample-minimum proof using Thm 7.6 normal-J + Thm 5.26 Frobenius
normal p-complement + Lem 7.7 (N/C `p'`-quotient).

`HasNormalPComplement p G` already defined in
`OddOrder/Isaacs/Ch05_Transfer/Main.lean:310`.  Lem 7.7 both halves already proved in
`OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:2515-2643`.

## やること

- [ ] Resolve Thm 7.6 first (issue #30).
- [ ] Implement 7-step proof (mmd L3913-L3949):
  1. Reduce to minimum counterexample.
  2. Use Lem 7.7 to pass through O_{p'}(G).
  3. Apply normal-J theorem 7.6 in reduced group.
  4. Combine with N_G(J(P)) normal p-complement hypothesis.
  5. Combine with C_G(Z(P)) normal p-complement hypothesis (via Thm 5.26).
  6. Derive contradiction in minimum counterexample.
- [ ] Add top-level theorem `OddOrder.Isaacs.Ch07.thompson_normal_p_complement…`.

## 2026-05-26 update — sub-agent feasibility analysis

**Feasible AFTER Thm 7.6 (#30) lands**. Medium effort ~300-450 LOC. All other dependencies sorry-free:

- **Thm 5.26 Frobenius normal p-complement**:
  `OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer`
  at `Ch05_Transfer/Main.lean:2533` (both directions sorry-free).
- **Lem 7.7 (a)(b)**: `normalizer_and_centralizer_map_of_coprime_kernel` at L2623 (sorry-free).
- **`HasNormalPComplement` subgroup inheritance**: `hasNormalPComplement_of_subgroup` (Lem 5.27 Part 1) at L1983 (sorry-free).
- **`lt_normalizer_of_pgroup_of_lt_top`** : 既存 Ch.5.

Step breakdown:
- Step 1 (U = O_p(G), "normalizers grow"): ~60 LOC
- Step 2 (G/U has normal p-complement): ~50 LOC (needs new `HasNormalPComplement` **quotient inheritance** helper, ~30 LOC standalone — not yet present)
- Step 3 (O_{p'}(G) = 1): ~40 LOC (uses Lem 7.7)
- Step 4 (P maximal via Hall-Higman 1.2.3): ~30 LOC
- Step 5 (`C_G(Z(P)) = P`): ~15 LOC
- Step 6 (G/U's complement abelian): ~50 LOC
- Step 7 (apply normal-J 7.6 → contradiction): ~30 LOC
- +1 helper (quotient inheritance): ~30-50 LOC

候補識別子: `thompson_normal_p_complement` (no existing definition).

## 完了条件

- Top-level theorem matching goal-grep `^theorem thompson_normal_p_complement…`.
- Proof sorry/axiom-free.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7C
- `references/isaacs/finite-group-theory.mmd` L3721, L3913-L3949
- Issue #30 (Thm 7.6 — prerequisite)
