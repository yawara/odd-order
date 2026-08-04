/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockIdempotent
import OddOrder.Algebra.CornerInverse

/-!
# Inverting in the corner of a block — the characteristic-`p` half of Navarro (5.5)

**Navarro (5.5)** produces, from a central element `x` with `λ_B(x) = 1`, an inverse of `x` in the
corner cut out by the block idempotent.  Over the residue field the reason is that

`e_B x - e_B = e_B (x - 1)`

is killed by *every* block character — by `λ_B` because `λ_B(x) = 1`, and by the others because
they kill `e_B` — hence is nilpotent, and `exists_corner_inverse_of_isNilpotent` applies.

Note how little is used: only that the block idempotent is recognised by
`blockCharacterPi e = Pi.single B 1`, and the nil-kernel hypothesis that already accompanies the
block idempotents.

## Main results

* `OddOrder.MatrixModule.exists_corner_inverse_of_blockCharacter_eq_one`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] [Finite ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable {A : Type*} [Ring A] [Algebra k A]
variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)

omit [Finite ι] in
/-- **The characteristic-`p` half of Navarro (5.5).**  If `e` is the idempotent of the block `c`
and `x` is central with `λ_c(x) = 1`, then `e x` has a two-sided inverse in the corner cut out
by `e`. -/
theorem exists_corner_inverse_of_blockCharacter_eq_one
    (hnil : ∀ z : Subalgebra.center k A,
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    [DecidableEq (Block π hπ hlin)] {c : Block π hπ hlin} {e : Subalgebra.center k A}
    (he : IsIdempotentElem e) (hec : blockCharacterPi π hπ hlin e = Pi.single c 1)
    {x : Subalgebra.center k A} (hx : blockCharacter π hπ hlin c x = 1) :
    ∃ y : Subalgebra.center k A,
      y = e * y * e ∧ (e * x) * y = e ∧ y * (e * x) = e := by
  have hee : e * e = e := he
  have hcorner : e * x = e * (e * x) * e := by
    rw [← mul_assoc, hee, mul_comm (e * x) e, ← mul_assoc, hee]
  refine exists_corner_inverse_of_isNilpotent he hcorner (hnil _ ?_)
  funext d
  rw [map_sub, map_mul, hec]
  by_cases hd : d = c
  · subst hd
    rw [Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply,
      blockCharacterPi_apply, hx, sub_self]
  · rw [Pi.sub_apply, Pi.mul_apply, Pi.single_eq_of_ne hd, zero_mul, Pi.zero_apply, sub_zero]

end OddOrder.MatrixModule
