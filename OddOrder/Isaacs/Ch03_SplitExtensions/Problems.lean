/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# Isaacs Chapter 3 — Problems §3A (Split Extensions)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 "Split Extensions" の章末演習 §3A
(pp. 74-75)。半直積 (`SemidirectProduct`) を扱う。

方針は Ch.1/Ch.2 の `Problems.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch03

section /- Problems 3A: Split extensions (pp. 74-75) -/

/-- **Isaacs Problem 3A.5**. 有限群 `G` について、`G` の自身への共役作用で作った半直積 `G ⋊ G` は
直積 `G × G` に同型。同型 `(n, g) ↦ (n·g, g)` は準同型: 半直積の積 `(a.left · a.right·b.left·a.right⁻¹,
a.right·b.right)` を写すと `(a.left·a.right·b.left·b.right, a.right·b.right)` = 直積の積の像。 -/
def semidirectConjEquivProd (G : Type*) [Group G] :
    SemidirectProduct G G MulAut.conj ≃* G × G where
  toFun x := (x.left * x.right, x.right)
  invFun p := ⟨p.1 * p.2⁻¹, p.2⟩
  left_inv x := SemidirectProduct.ext (by simp) rfl
  right_inv p := by simp
  map_mul' a b := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, MulAut.conj_apply,
      Prod.mk_mul_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> group

end

end OddOrder.Isaacs.Ch03
