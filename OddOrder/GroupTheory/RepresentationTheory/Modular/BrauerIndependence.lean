/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SplitSemisimpleCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularCount

/-!
# The block traces are independent on the `p`-regular classes

The modular half of the linear independence of the irreducible Brauer characters.  For a
splitting datum `π : kG ↠ B ≅ ∏_{i ∈ ι} M_{n_i}(k)` the block traces
`τ_i(x) = tr (e (π x) i)` are functionals on `kG` which

* kill the `p`-radical `T'` (`ker_blockTrace`), so they descend to `kG ⧸ T'`;
* are the coordinates of an isomorphism `kG ⧸ T' ≃ₗ[k] (ι → k)` (`blockTraceQuotientEquiv`).

Since the `p`-regular classes span `kG ⧸ T'` (`PRegularCount`), a linear relation among the
`τ_i` that holds at the `p`-regular group elements holds identically, hence is trivial.

This is what makes the irreducible Brauer characters independent: reducing a relation among them
modulo the maximal ideal of `𝒪` gives a relation among the `τ_i`
(`residue_irreducibleBrauerCharacter`).

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_zero_of_sum_blockTrace_pRegular_eq_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupTheory

variable {k G ι : Type*} [Field k] [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {p : ℕ}

/-- **The block traces are linearly independent as functions on the `p`-regular elements.** -/
theorem eq_zero_of_sum_blockTrace_pRegular_eq_zero
    (hp : p.Prime) (hk : (p : k) = 0) (hchar : (p : MonoidAlgebra k G) = 0)
    {B : Type*} [Ring B] [Algebra k B] (hB : (p : B) = 0)
    {π : MonoidAlgebra k G →ₐ[k] B} (hπ : Function.Surjective π)
    {N : ℕ} (hker : ∀ y : MonoidAlgebra k G, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[k] ∀ i, Matrix (nn i) (nn i) k) (c : ι → k)
    (h : ∀ g : G, IsPRegular p g →
      ∑ i, c i * OddOrder.blockTrace nn π e (single g (1 : k)) i = 0) :
    c = 0 := by
  classical
  -- the relation, as a functional on `kG`
  let f : (ι → k) →ₗ[k] k :=
    { toFun := fun v => ∑ i, c i * v i
      map_add' := fun u v => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by simp [Finset.mul_sum, mul_left_comm] }
  set L : MonoidAlgebra k G →ₗ[k] k := f.comp (OddOrder.blockTrace nn π e) with hL
  -- it kills the `p`-radical, hence descends to `kG ⧸ T'`
  have hLker : OddOrder.commutatorRadical (k := k) hp hchar ≤ LinearMap.ker L := by
    intro x hx
    have hbt : OddOrder.blockTrace nn π e x = 0 :=
      (OddOrder.ker_blockTrace hp hk hchar hB hπ hker e).ge hx
    simp [hL, hbt, f]
  set L' : (MonoidAlgebra k G ⧸ OddOrder.commutatorRadical (k := k) hp hchar) →ₗ[k] k :=
    Submodule.liftQ _ L hLker with hL'
  -- it vanishes on the `p`-regular classes, which span the quotient
  have hL'zero : L' = 0 := by
    refine LinearMap.ext_on (span_range_mkQ_pRegular_eq_top hp hchar) ?_
    rintro _ ⟨C, rfl⟩
    simpa [hL', hL, f] using h (C : ConjClasses G).out (isPRegular_out C.2)
  -- so the whole functional vanishes, and the coefficients are the values on a basis
  have hLzero : ∀ x, L x = 0 := fun x => by
    have := congrFun (congrArg DFunLike.coe hL'zero)
      ((OddOrder.commutatorRadical (k := k) hp hchar).mkQ x)
    simpa [hL'] using this
  funext i
  obtain ⟨x, hx⟩ := OddOrder.surjective_blockTrace hπ e (Pi.single i (1 : k))
  have := hLzero x
  simp [hL, f, hx, Pi.single_apply] at this
  simpa using this

end OddOrder.RepresentationTheory.Modular
