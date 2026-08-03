/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerIndependence
import OddOrder.GroupTheory.RepresentationTheory.Modular.IrreducibleBrauerCharacter

/-!
# Relations among irreducible Brauer characters are divisible by `p`

A linear relation `∑_i c_i φ_i = 0` on the `p`-regular classes, with coefficients in `𝒪`,
reduces modulo the maximal ideal to a relation among the block traces
(`residue_irreducibleBrauerCharacter`), and those are independent
(`eq_zero_of_sum_blockTrace_pRegular_eq_zero`).  So every coefficient lies in the maximal ideal.

This is the whole content of the linear independence of `IBr(G)`: over a discrete valuation ring
one then divides by a uniformiser and repeats, so no nonzero relation survives.  The step
recorded here is the one that carries the representation theory; the descent is arithmetic.

## Main results

* `OddOrder.RepresentationTheory.Modular.mem_maximalIdeal_of_sum_irreducibleBrauerCharacter`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

/-- **A relation among the irreducible Brauer characters has all coefficients in the maximal
ideal.**  Reduce it modulo `𝔪` and use that the block traces are independent on the `p`-regular
classes. -/
theorem mem_maximalIdeal_of_sum_irreducibleBrauerCharacter (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {B : Type*} [Ring B] [Algebra (ResidueField 𝒪) B]
    {π : MonoidAlgebra (ResidueField 𝒪) G →ₐ[ResidueField 𝒪] B} (hπ : Function.Surjective π)
    {N : ℕ} (hker : ∀ y : MonoidAlgebra (ResidueField 𝒪) G, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[ResidueField 𝒪] ∀ i, Matrix (nn i) (nn i) (ResidueField 𝒪)) (c : ι → 𝒪)
    (h : ∀ g : G, IsPRegular p g →
      ∑ i, c i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0)
    (i : ι) : c i ∈ maximalIdeal 𝒪 := by
  classical
  have hk : ((p : ℕ) : ResidueField 𝒪) = 0 := CharP.cast_eq_zero _ p
  have hchar : ((p : ℕ) : MonoidAlgebra (ResidueField 𝒪) G) = 0 := by
    rw [← map_natCast (algebraMap (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)) p, hk,
      map_zero]
  have hB : ((p : ℕ) : B) = 0 := by rw [← map_natCast π p, hchar, map_zero]
  -- reduce the relation modulo the maximal ideal
  have hres : ∀ g : G, IsPRegular p g →
      ∑ j, residue 𝒪 (c j) * OddOrder.blockTrace nn π e (single g (1 : ResidueField 𝒪)) j = 0 := by
    intro g hg
    have := congrArg (residue 𝒪) (h g hg)
    rw [map_sum, map_zero] at this
    refine this ▸ Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul,
      residue_irreducibleBrauerCharacter (π := (e.toAlgHom.comp π).toRingHom) hp hω j hg]
    rfl
  have hzero := eq_zero_of_sum_blockTrace_pRegular_eq_zero hp hk hchar hB hπ hker e
    (fun j => residue 𝒪 (c j)) hres
  have hci : residue 𝒪 (c i) = 0 := congrFun hzero i
  exact Ideal.Quotient.eq_zero_iff_mem.mp hci

end OddOrder.RepresentationTheory.Modular
