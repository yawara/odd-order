---
id: 29
slug: isaacs-ch07-thm-7-5-normal-p
title: "Isaacs Thm 7.5 normal-P top-level theorem + minimum counterexample"
created: 2026-05-26
---

# Isaacs Thm 7.5 normal-P top-level theorem + minimum counterexample

## 背景

Isaacs Thm 7.5 (mmd L3783) is the normal-P theorem:

> G p-solvable, p ≠ 2, Sylow-2 abelian, G acts faithfully on p-group V,
> |V : C_V(P)| ≤ p for some P ∈ Syl_p(G) ⇒ P ⊴ G.

It is Thm 7.6 normal-J theorem の中核 step. In the current
`Ch07_ThompsonSubgroup/Main.lean`, both branches are proved (cyclic and elementary p²):

- `subgroup_normal_of_injective_mulAut_of_isCyclic` (line 1653) — cyclic branch
- `sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful` (line 1568) — elementary p² branch
- `false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal` (line 2409)
- `false_of_quotient_isCyclic_of_sylow_not_normal` (line 2449)

**What's missing**: the minimum-counterexample / chief-factor reduction that turns the
general hypothesis `|V:C_V(P)| ≤ p` into one of these two branches.

The book argument (Isaacs pp.207-208) uses:
1. Reduce to minimum counterexample (P not normal).
2. Reduce to faithful action by quotienting out the kernel of the action.
3. Take chief factor V/U of G acting on V (since G is p-solvable).
4. V/U is cyclic or elementary abelian of order dividing p².
5. Apply the corresponding `false_of_quotient_*` theorem.

## やること

- [ ] Prove chief-factor existence: from a faithful action of a p-solvable group G
      on a finite p-group V with `|V : C_V(P)| ≤ p`, exists G-invariant `U ⊴ V` such
      that `V/U` is cyclic or elementary abelian of order `p²`. Hall-Higman 1.2.3
      (Ch.3 Thm 3.21) is the standard tool.
- [ ] Assemble top-level theorem `OddOrder.Isaacs.Ch07.sylow_normal_of_elementary_*`
      using the chief-factor reduction + existing branches.
- [ ] Trace to `**Isaacs Thm 7.5** (normal-P theorem)` in docstring header.

## 完了条件

- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean` contains a top-level theorem
  matching goal-grep `^theorem sylow_normal_of_elementary…` with full Thm 7.5 hypotheses.
- Proof has no `sorry`/`axiom`.
- `lake build OddOrder` green.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7A
- `references/isaacs/finite-group-theory.mmd` L3783-L3826
- `OddOrder.Isaacs.Ch03.IsPiSeparable` — p-separability bridge
- Issue #30 (Thm 7.6 normal-J — depends on this)
