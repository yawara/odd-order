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

本 leaf は「⟸」の片方 (`|A| = 3`) を扱う。残り (初等可換 2-群の側と「⟹」) は
`Problems8C/AbelianAutSimple.lean` の `isSimpleGroup_mulAut_iff` が双方向で運んでいる
(そこで書籍の分類が訂正され, 正しくは「位数 `3`, `4`, `6` の巡回群, または位数 `8` 以上の
初等可換 `2`-群」— 書籍は `ℤ/4` と `ℤ/6` を落としている)。

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
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic A := isCyclic_of_prime_card hA
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine isSimpleGroup_of_prime_card (p := 2) ?_
  rw [IsCyclic.card_mulAut, hA, Nat.totient_prime (by norm_num)]

end

end OddOrder.Isaacs.Ch08
