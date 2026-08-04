/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSum
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralCharacterTrace
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockKernel

/-!
# The block characters of `Ĝ⁰`

Navarro's proof of Külshammer's formula (6.14) feeds `z = Ĝ⁰` — the sum of the `p`-regular
elements — into (4.23), so it needs the values `λ_B(Ĝ⁰)`.

* For the **principal block** the answer is immediate: `λ_{B_0}` is the augmentation, so
  `λ_{B_0}(Ĝ⁰) = |G⁰|*`, which is nonzero because `p ∤ |G⁰|`.
* For the **other blocks** Navarro's Lemma (3.32) gives `λ_B(Ĝ⁰) = 0`.  Written out, `Ĝ⁰ = u_{1_G}`
  in the notation of (3.32) and the central character is

  `ω_χ(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g)`,

  so what has to vanish is `∑_{g ∈ G⁰} χ(g)` for `χ ∉ Irr(B_0)`.  This is Navarro's Lemma (3.20)
  ("for `χ ∈ Irr(B)`, the extension by zero of `χ|_{G⁰}` is a `ℤ`-combination of `Irr(B)`") applied
  to `χ = 1_G`, which lies in `Irr(B_0)`.

This file records the two halves that need no block theory: the identification of `ω_χ(Ĝ⁰)` and
the principal-block value.

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_pRegularSum_mul_character_one`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_principalBlock_pRegularSum`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

section CentralScalar

variable {K G : Type*} [Field K] [Group G] [Fintype G]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι') (p : ℕ)

open scoped Classical in
/-- **`ω_χ(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g)`.**  The coefficients of `Ĝ⁰` are the indicator of the
`p`-regular elements, so Burnside's trace identity collapses to a sum over `G⁰`. -/
theorem centralScalar_pRegularSum_mul_character_one :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (pRegularSum p K)
        * (wedderburnRepresentation e i).character 1
      = ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
          (wedderburnRepresentation e i).character g := by
  classical
  rw [centralScalar_mul_character_one e i _ pRegularSum_mem_center, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [coeff_pRegularSum]
  split <;> simp

end CentralScalar

section PrincipalBlock

variable {k G : Type*} [Field k] [Group G] [Fintype G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)]
  [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable (p : ℕ)

open scoped Classical in
/-- **`λ_{B_0}(Ĝ⁰) = |G⁰|*`.**  The central character of the principal block is the augmentation,
and the augmentation counts the `p`-regular elements. -/
theorem blockCharacter_principalBlock_pRegularSum :
    blockCharacter π hπ hlin (principalBlock π hπ hlin hnil)
        ⟨pRegularSum p k, pRegularSum_mem_center⟩
      = ((Finset.univ.filter (fun g : G => IsPRegular p g)).card : k) := by
  classical
  rw [blockCharacter_principalBlock, OddOrder.GroupTheory.CenterSimplesOrbit.aug_apply]
  change OddOrder.Algebra.augmentation k G (pRegularSum p k) = _
  rw [pRegularSum, map_sum]
  rw [Finset.sum_congr rfl fun g (_ : g ∈ _) => OddOrder.Algebra.augmentation_single k G g 1]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end PrincipalBlock

end OddOrder.RepresentationTheory.Modular
