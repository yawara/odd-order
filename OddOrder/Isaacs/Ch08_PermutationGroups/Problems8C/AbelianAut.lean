/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum.Prime

/-!
# Isaacs, Finite Group Theory — Problem 8C.6 (p. 257)

**Problem 8C.6**: 可換群 `A` について `Aut(A)` が単純 ⟺ `|A| = 3` または `A` が位数 8
以上の初等可換 2-群。

本 leaf は「⟸」の片方 (`|A| = 3`) を扱う。もう片方 (初等可換 2-群 ⟹
`Aut(A) ≅ GL(n, 2)` が単純) と「⟹」は未形式化。

## Main results

- `isSimpleGroup_mulAut_of_card_eq_three` — 位数 3 の群の自己同型群は単純
  (`Aut(Z₃) ≅ Z₂`)。
-/

namespace OddOrder.Isaacs.Ch08

section /- Problem 8C.6 (p. 257) -/

/-- **Isaacs Problem 8C.6** の「⟸」その 1: 位数 3 の群 `A` の自己同型群は単純。

`A` は素数位数なので巡回で, `|Aut(A)| = φ(3) = 2` (`IsCyclic.card_mulAut`)。
位数 2 は素数なので単純。 -/
theorem isSimpleGroup_mulAut_of_card_eq_three {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 3) : IsSimpleGroup (MulAut A) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic A := isCyclic_of_prime_card hA
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine isSimpleGroup_of_prime_card (p := 2) ?_
  rw [IsCyclic.card_mulAut, hA, Nat.totient_prime (by norm_num)]

end

end OddOrder.Isaacs.Ch08
