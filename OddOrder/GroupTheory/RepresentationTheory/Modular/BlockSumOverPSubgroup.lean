/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishing

/-!
# Summing a block over a `p`-subgroup collapses to the identity

Navarro (4.19), page 93.  For a `p`-subgroup `P`, a `p`-regular `y` and a block `B`,

`∑_{x ∈ P} ∑_{χ ∈ Irr(B)} χ(y⁻¹) χ(x) = ∑_{χ ∈ Irr(B)} χ(y⁻¹) χ(1)`,

because weak block orthogonality kills every term with `x ≠ 1`: the `p`-part of `x` is `x`, the
`p`-part of `y⁻¹` is `1`, and those are conjugate only for `x = 1`.

This is the step that turns the multiplicity `[χ_P, 1_P]` appearing in Navarro (4.19) into the
class-sum coefficient of the block idempotent, so it is what closes the character side of
Külshammer's formula.

Weak block orthogonality is taken as a hypothesis on the elements of `P`, since
`sum_character_blockOfIrr_eq_zero` carries the splitting data of `C_G(x)`, which varies with `x`.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_pSubgroup_sum_block_character`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra MatrixModule OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

open scoped Classical in
/-- **Navarro (4.19), page 93.**  Summing a block's characters against a `p`-subgroup leaves only
the contribution of the identity. -/
theorem sum_pSubgroup_sum_block_character (P : Subgroup G) [Fintype ↥P]
    (B : Block πG hπG hlinG) (y : G)
    (hweak : ∀ x : ↥P, (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0) :
    ∑ x : ↥P, ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character (x : G)
      = ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character 1 := by
  classical
  rw [Finset.sum_eq_single (1 : ↥P)]
  · rw [OneMemClass.coe_one]
  · intro b _ hb
    exact hweak b fun h => hb (Subtype.ext (by simpa using h))
  · intro h
    exact absurd (Finset.mem_univ (1 : ↥P)) h

end OddOrder.RepresentationTheory.Modular
