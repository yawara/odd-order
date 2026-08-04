/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSum
import OddOrder.Mathlib.MonoidAlgebra
import OddOrder.GroupTheory.PFactorPairCount

/-!
# `Ĝ_p · Ĝ⁰` counts the factorisations `g = x y`

The coefficient of `Ĝ_p · Ĝ⁰` at `g` is the number of ways to write `g = x y` with `x` a
`p`-element and `y` `p`-regular:

`(Ĝ_p · Ĝ⁰)(g) = |Ω(g)|*`,  `Ω(g) = {(x, y) : x a p-element, y p-regular, x y = g}`.

This is the counting side of Külshammer's formula (Navarro (6.14)): combined with
`|G⁰|* e_{B_0} = π(Ĝ_p Ĝ⁰)` it says `e_{B_0}(g) = |G⁰|*⁻¹ |Ω(g)|*` for `p`-regular `g`, and
Problem (6.1) then compares that count with the one taken inside `C_G(Q)`.

## Main results

* `OddOrder.GroupAlgebra.coeff_pElementSum_mul` — `(Ĝ_p · w)(g) = ∑_{x ∈ G_p} w(x⁻¹ g)`
* `OddOrder.GroupAlgebra.coeff_pElementSum_mul_pRegularSum` — `(Ĝ_p · Ĝ⁰)(g) = |Ω(g)|`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {R : Type*} [Semiring R] {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- **`(Ĝ_p · w)(g) = ∑_{x ∈ G_p} w(x⁻¹ g)`.** -/
theorem coeff_pElementSum_mul (w : MonoidAlgebra R G) (g : G) :
    (pElementSum p R * w).coeff g
      = ∑ x ∈ Finset.univ.filter (fun x : G => IsPElement p x), w.coeff (x⁻¹ * g) := by
  classical
  rw [pElementSum, Finset.sum_mul, MonoidAlgebra.coeff_finsetSum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]

open scoped Classical in
/-- **`Ω(g)` as a subtype of `G`**: a factorisation `g = x y` is determined by its `p`-part. -/
def pFactorPairsEquivPElement (g : G) :
    {x : G // IsPElement p x ∧ IsPRegular p (x⁻¹ * g)} ≃ PFactorPairs p g where
  toFun x := ⟨((x : G), (x : G)⁻¹ * g), x.2.1, x.2.2, by group⟩
  invFun q := ⟨(q : G × G).1, q.2.1, by
    have h : (q : G × G).1⁻¹ * g = (q : G × G).2 := (eq_inv_mul_of_mul_eq q.2.2.2).symm
    rw [h]; exact q.2.2.1⟩
  left_inv x := rfl
  right_inv q := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact (eq_inv_mul_of_mul_eq q.2.2.2).symm

open scoped Classical in
/-- **`(Ĝ_p · Ĝ⁰)(g) = |Ω(g)|`.**  The counting side of Külshammer's formula. -/
theorem coeff_pElementSum_mul_pRegularSum (g : G) :
    (pElementSum p R (G := G) * pRegularSum p R).coeff g
      = (Nat.card (PFactorPairs p g) : R) := by
  classical
  rw [coeff_pElementSum_mul]
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : G => IsPElement p x),
      (pRegularSum p R (G := G)).coeff (x⁻¹ * g)
        = if IsPRegular p (x⁻¹ * g) then (1 : R) else 0 := fun x _ => coeff_pRegularSum _
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Nat.card_congr (pFactorPairsEquivPElement (p := p) g).symm, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end OddOrder.GroupAlgebra
