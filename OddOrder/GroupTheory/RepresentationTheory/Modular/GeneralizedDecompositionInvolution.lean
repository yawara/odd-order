/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BasicSetDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionOrthogonality

/-!
# Navarro (5.13)(b) at an involution

For a `p`-element `x`, Navarro (5.13)(b) reads

`∑_{χ ∈ Irr(G)} d^{x⁻¹}_{χμ} d^x_{χφ} = c_{μφ}`,

and the numbers at `x⁻¹` are supplied as a separate family (`dinv`) satisfying the defining
expansion read inside `C_G(x)`.  When `x = t` is an **involution** the two families coincide:
`t⁻¹ = t`, so the numbers at `t⁻¹` *are* the numbers at `t`, and the identity becomes a sum of
squares,

`∑_{χ ∈ Irr(G)} (d^t_{χφ})² = c_{φφ}`.

Verifying the hypothesis `hdinv` is one group computation: for `y ∈ C_G(t)`,
`(t y)⁻¹ = y⁻¹ t⁻¹ = y⁻¹ t = t y⁻¹`, so the defining expansion at `y⁻¹` is exactly the required
expansion of `χ((t y)⁻¹)`.

This is the form the Brauer–Suzuki argument uses: with `t` an involution whose centraliser has a
normal `2`-complement, `c_{φ_0 φ_0} = |C_G(t)|_2` (Navarro (6.13),
`card_mul_cartanMatrix_principalBlock`) and the left side is a sum of squares of *integers*.

## Main results

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumberInv_eq_of_mul_self_eq_one`
  — the two families literally coincide
* `OddOrder.RepresentationTheory.Modular.sum_sq_generalizedDecompositionNumber_of_involution`
* `OddOrder.RepresentationTheory.Modular`
  `.sum_mul_basicDecompositionNumber_eq_cartanMatrix_of_involution` — Navarro (7.5)(c) at an
  involution, in the form the "analysis at `t`" reads as `(D^t_i, D^t_j)`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
variable [Invertible (Nat.card G : K)]
variable (hpC : p.Prime) {ω : 𝒪}
  (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)

omit [Finite G] in
/-- **`(t y)⁻¹ = t y⁻¹` for `y ∈ C_G(t)` and `t` an involution.**  Inverting reverses the product,
`t⁻¹ = t`, and `y⁻¹` commutes with `t`. -/
theorem inv_mul_eq_mul_inv_of_mul_self_eq_one (ht : x * x = 1) (y : ↥(centralizerOf x)) :
    (x * (y : G))⁻¹ = x * ((y⁻¹ : ↥(centralizerOf x)) : G) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right ht
  have hcomm : (y : G) * x = x * (y : G) :=
    ((Subgroup.mem_centralizer_iff.mp y.2) x rfl).symm
  have hcomm' : ((y : G))⁻¹ * x = x * ((y : G))⁻¹ := by
    rw [← mul_left_cancel_iff (a := (y : G)), ← mul_assoc, mul_inv_cancel, one_mul,
      ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [_root_.mul_inv_rev, hxinv, hcomm']
  rfl

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (5.13)(b) at an involution**: `∑_{χ ∈ Irr(G)} (d^t_{χφ})² = c_{φφ}`.

`t⁻¹ = t`, so the family of numbers at `t⁻¹` required by (5.13)(b) is the family at `t` itself:
its defining expansion at `y⁻¹` computes `χ(t y⁻¹) = χ((t y)⁻¹)`. -/
theorem sum_sq_generalizedDecompositionNumber_of_involution
    (ht : x * x = 1) (hx : IsPElement p x) (φ : ι) :
    (∑ j : J, (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG j).character)
        (fun _ _ h => character_eq_of_isConj _ h) φ) ^ 2)
      = (cartanMatrix hpC hω hω' hπ hlin hkerJ e φ φ : K) := by
  classical
  rw [← sum_mul_generalizedDecompositionNumber_eq_cartanMatrix hpC hω hω' hπ hlin hkerJ e eG hx φ φ
    (fun j => generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
      ((wedderburnRepresentation eG j).character)
      (fun _ _ h => character_eq_of_isConj _ h))
    (fun j y hy => by
      rw [sum_generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ _ _ (y := y⁻¹) hy.inv,
        inv_mul_eq_mul_inv_of_mul_self_eq_one ht y])]
  exact Finset.sum_congr rfl fun _ _ => sq _

omit [Invertible (Nat.card G : K)] in
include hpC hω' hπ hlin hkerJ in
/-- **At an involution the two families of generalized decomposition numbers coincide.**
`x⁻¹ = x`, so the defining expansions of `d^{x⁻¹}_{χ·}` and `d^x_{χ·}` are the same equation, and
uniqueness (Navarro (5.1)) identifies them.

This is what makes the *basic-set* form of (7.5)(c) usable at `t`: that statement pairs the column
of `d^{x⁻¹}` with the column of `d^x`, and here both are `D^t`. -/
theorem generalizedDecompositionNumberInv_eq_of_mul_self_eq_one (ht : x * x = 1) (χ : G → K)
    (hχ : ∀ g h : G, IsConj g h → χ g = χ h) :
    generalizedDecompositionNumberInv (x := x) hpC hω' hπ hlin hkerJ χ hχ
      = generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ :=
  (eq_generalizedDecompositionNumberInv hpC hω' hπ hlin hkerJ χ hχ fun y hy => by
    rw [sum_generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ hy,
      inv_eq_of_mul_eq_one_right ht]).symm

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (7.5)(c) at an involution.**  The pairing of two basic-set columns at `t` is
`UᵗCU`, `C` the Cartan matrix of `C_G(t)`.  This is the identity the "analysis at `t`" reads as
`(D^t_i, D^t_j)` on p. 141; combined with `UᵗC_{C_G(t)}U = 2(1 + δ)` (issue 9506, 段 322) it gives
Navarro's (3). -/
theorem sum_mul_basicDecompositionNumber_eq_cartanMatrix_of_involution {ι₂ : Type*}
    (u : ι → ι₂ → K) (ht : x * x = 1) (hx : IsPElement p x) (φ η : ι₂) :
    (∑ j : J, basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u φ *
      basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u η)
      = ∑ μ : ι, ∑ τ : ι, u μ φ
          * (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ τ : K) * u τ η := by
  rw [← sum_mul_basicDecompositionNumber_eq_cartanMatrix hpC hω hω' hπ hlin hkerJ e eG u hx φ η]
  exact Finset.sum_congr rfl fun j _ => by
    rw [generalizedDecompositionNumberInv_eq_of_mul_self_eq_one hpC hω' hπ hlin hkerJ ht _ _]

end OddOrder.RepresentationTheory.Modular
