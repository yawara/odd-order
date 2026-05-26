---
id: 30
slug: isaacs-ch07-thm-7-6-normal-j
title: "Isaacs Thm 7.6 normal-J theorem (= BG Thm 6.2 odd-order) - FT critical"
created: 2026-05-26
---

# Isaacs Thm 7.6 normal-J theorem (= BG Thm 6.2 odd-order) - FT critical

## 背景

**Isaacs Thm 7.6** (mmd L3832) normal-J theorem:

> (i) G p-solvable, (ii) p ≠ 2, (iii) Sylow-2 abelian, (iv) O_{p'}(G) = 1,
> (v) P = C_G(Z(P)) ⇒ J(P) ⊴ G.

**= BG Theorem 6.2 odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8, §9,
App.A で 7 ヶ所超で直接引用 (L2456, L2480, L2482, L2511, L2515, L5014, L5032).

## やること

- [ ] Resolve Thm 7.5 first (issue #29).
- [ ] Confirm Ch.4 Thm 4.35 (Ω₁ fixed) is available.
- [ ] Confirm Ch.6 Thm 6.20 (abelian coprime ⟨C_N(a)⟩=N) is available.
- [ ] Confirm Hall-Higman Ch.3 Thm 3.21 is available.
- [ ] Implement 8-step proof (mmd L3832-L3896):
  1. Minimum counterexample G with J(P) not normal.
  2. O_{p'}(G) = 1 (by hypothesis).
  3. V := Z(J(P)). Abelian and characteristic in P.
  4. Apply Ch.6 Thm 6.20: action of G on V via P-conjugation.
  5. Apply Ch.4 Thm 4.35 to find P-invariant element.
  6. Apply Hall-Higman 3.21 to control rank.
  7. Apply Thm 7.5 (normal-P) in subquotient.
  8. Conclude J(P) ⊴ G.
- [ ] Add top-level theorem `OddOrder.Isaacs.Ch07.normal_J_*`.

## 完了条件

- Top-level theorem matching goal-grep `^theorem normal_J…`.
- Proof sorry/axiom-free.
- `lake build OddOrder` green.
- AxiomsCheck passes for this flagship theorem.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7B
- `references/isaacs/finite-group-theory.mmd` L3832-L3896
- BG §App.A Thm A.4(b) — equivalent statement
- Issue #29 (Thm 7.5 — prerequisite)
- `OddOrder.GroupTheory.ThompsonSubgroup` — `J(P)` def
