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

## 完了条件

- Top-level theorem matching goal-grep `^theorem thompson_normal_p_complement…`.
- Proof sorry/axiom-free.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7C
- `references/isaacs/finite-group-theory.mmd` L3721, L3913-L3949
- Issue #30 (Thm 7.6 — prerequisite)
