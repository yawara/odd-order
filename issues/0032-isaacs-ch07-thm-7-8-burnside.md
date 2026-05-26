---
id: 32
slug: isaacs-ch07-thm-7-8-burnside
title: "Isaacs Thm 7.8 Burnside p^a q^b solvability (character-free)"
created: 2026-05-26
---

# Isaacs Thm 7.8 Burnside p^a q^b solvability (character-free)

## 背景

**Isaacs Thm 7.8** (mmd L3955):

> |G| = p^a q^b ⇒ G solvable.

**character 不使用** (Goldschmidt-Bender-Matsuyama, 9-step proof).

mathlib does NOT have this result (only Burnside normal p-complement Thm 5.13 +
Burnside orbit lemma).

## やること

- [ ] Resolve Thm 7.6 first (issue #30 — required at step 8).
- [ ] Confirm Ch.2 Thm 2.13 Baer (already ✅) and Ch.4 Thm 4.33 (p-local) available.
- [ ] Implement 9-step proof (mmd L3955-L4053):
  - 1-3. Maximal subgroup p/q-type dichotomy.
  - 4. Each p-subgroup p-central-centralized.
  - 5-6. q-central elements normalize no nontrivial p-subgroup.
  - 7. p ≠ 2 ∧ q ≠ 2 (via Thm 2.13).
  - 8. p-type maximal: apply normal-J 7.6 to get J(S) ⊴ M.
  - 9. Thompson factorization contradiction.
- [ ] Add top-level theorem `OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow…`.

## 完了条件

- Top-level theorem matching goal-grep `^theorem burnside_p_pow_q_pow…`.
- Proof sorry/axiom-free.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7D
- `references/isaacs/finite-group-theory.mmd` L3955-L4053
- Issue #30 (Thm 7.6 — prerequisite at Step 8)
- BG L2633 — references this as application of normal-J
