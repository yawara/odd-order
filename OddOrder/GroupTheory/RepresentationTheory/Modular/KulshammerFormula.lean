/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularSumBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.SylowSumReduction

/-!
# Navarro (6.14): Külshammer's formula, the `z = Ĝ⁰` instance of (4.23)

`coeff_pElementSum_mul_classSum` is (4.23) for a single class sum.  `Ĝ⁰` is the sum of the class
sums of the `p`-regular classes (`pRegularSum_eq_sum_classSum`), so summing gives

`(Ĝ_p · Ĝ⁰)(x_C) = ∑_B λ_B(Ĝ⁰) · e_B(x_C)`.

Külshammer's formula is what this becomes once the two values of `λ_B(Ĝ⁰)` are inserted:
`λ_{B_0}(Ĝ⁰) = |G⁰|*` (`blockCharacter_principalBlock_pRegularSum`) and `λ_B(Ĝ⁰) = 0` for
`B ≠ B_0` (`blockCharacter_blockOfIrr_pRegularSum_eq_zero`), giving
`π(Ĝ_p Ĝ⁰) = |G⁰|* e_{B_0}`.

## Main results

* `OddOrder.RepresentationTheory.Modular.pRegularSum_eq_sum_classSum`
* `OddOrder.RepresentationTheory.Modular.coeff_pElementSum_mul_pRegularSum`
* `OddOrder.RepresentationTheory.Modular.coeff_pElementSum_mul_pRegularSum_principalBlock` —
  **Navarro (6.14)**
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory
  OddOrder.GroupTheory.CenterClassSum

section ClassSums

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {p : ℕ}

open scoped Classical in
/-- **`Ĝ⁰` is the sum of the `p`-regular class sums.**  It is central, and its coefficients are
the indicator of the `p`-regular elements. -/
theorem pRegularSum_eq_sum_classSum :
    pRegularSum p k (G := G)
      = ∑ C ∈ Finset.univ.filter (fun C : ConjClasses G => IsPRegular p C.out),
        classSum (k := k) C := by
  classical
  rw [center_eq_sum_classSum (pRegularSum_mem_center (p := p) (S := k) (G := G)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [coeff_pRegularSum]
  split <;> simp

end ClassSums

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
variable [HenselianLocalRing 𝒪] {p : ℕ} [IsPModularSystem p 𝒪] [Fintype (ConjClasses G)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

set_option maxHeartbeats 1600000 in
-- (4.23) for each class sum and the reassembly over `Ĝ⁰` share the same instance chains.
open scoped Classical in
/-- **Navarro (4.23) at `z = Ĝ⁰`.**  `Ĝ⁰` is a sum of class sums, and both sides of (4.23) are
additive in `z`. -/
theorem coeff_pElementSum_mul_pRegularSum [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G) (C : ConjClasses G)
    {F : MatrixModule.Block πG hπG hlinG → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {F' : MatrixModule.Block πG hπG hlinG →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : ∀ B, IsIdempotentElem (F B))
    (hf : ∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)))
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hweak : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character C.out⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0) :
    (pElementSum p (ResidueField 𝒪) (G := G) * pRegularSum p (ResidueField 𝒪)).coeff C.out
      = ∑ B : MatrixModule.Block πG hπG hlinG,
          MatrixModule.blockCharacter πG hπG hlinG B
              ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩
            * ((F' B : MonoidAlgebra (ResidueField 𝒪) G)).coeff C.out := by
  classical
  set T : Finset (ConjClasses G) :=
    Finset.univ.filter (fun D : ConjClasses G => IsPRegular p D.out) with hT
  -- the left side splits over the `p`-regular classes
  have hsplit : (pElementSum p (ResidueField 𝒪) (G := G)
      * pRegularSum p (ResidueField 𝒪)).coeff C.out
      = ∑ D ∈ T, (pElementSum p (ResidueField 𝒪) (G := G)
        * classSum (k := ResidueField 𝒪) D).coeff C.out := by
    rw [pRegularSum_eq_sum_classSum, ← hT, Finset.mul_sum, MonoidAlgebra.coeff_finsetSum]
  -- the block character splits too
  have hchar : ∀ B : MatrixModule.Block πG hπG hlinG,
      MatrixModule.blockCharacter πG hπG hlinG B
          ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩
        = ∑ D ∈ T, MatrixModule.blockCharacter πG hπG hlinG B
          ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩ := by
    intro B
    have hz : (⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ :
        Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G))
        = ∑ D ∈ T, ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩ := by
      refine Subtype.ext ?_
      rw [AddSubmonoidClass.coe_finsetSum]
      exact pRegularSum_eq_sum_classSum
    rw [hz, map_sum]
  rw [hsplit, Finset.sum_congr rfl fun D (_ : D ∈ T) =>
    coeff_pElementSum_mul_classSum e hπG hlinG hnilG S C D hidem hf hB hweak,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [hchar B, Finset.sum_mul]

set_option maxHeartbeats 1600000 in
-- The collapse of the block sum runs under the same instance chains as (4.23).
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Navarro (6.14), Külshammer's formula** (coefficient form).  Only the principal block
survives in `∑_B λ_B(Ĝ⁰) e_B`, with `λ_{B_0}(Ĝ⁰) = |G⁰|*`:

`(Ĝ_p · Ĝ⁰)(x_C) = |G⁰|* · e_{B_0}(x_C)`,

i.e. `π(Ĝ_p Ĝ⁰) = |G⁰|* e_{B_0}`.  Since `p ∤ |G⁰|` this determines the coefficients of the
principal block idempotent. -/
theorem coeff_pElementSum_mul_pRegularSum_principalBlock [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G) (C : ConjClasses G)
    {F : MatrixModule.Block πG hπG hlinG → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {F' : MatrixModule.Block πG hπG hlinG →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : ∀ B, IsIdempotentElem (F B))
    (hf : ∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)))
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hweak : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character C.out⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0)
    (hvanish : ∀ B : MatrixModule.Block πG hπG hlinG,
      B ≠ principalBlock πG hπG hlinG hnilG →
      MatrixModule.blockCharacter πG hπG hlinG B
        ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0) :
    (pElementSum p (ResidueField 𝒪) (G := G) * pRegularSum p (ResidueField 𝒪)).coeff C.out
      = ((Finset.univ.filter (fun g : G => IsPRegular p g)).card : ResidueField 𝒪)
        * ((F' (principalBlock πG hπG hlinG hnilG) :
            MonoidAlgebra (ResidueField 𝒪) G)).coeff C.out := by
  classical
  rw [coeff_pElementSum_mul_pRegularSum e hπG hlinG hnilG S C hidem hf hB hweak,
    Finset.sum_eq_single (principalBlock πG hπG hlinG hnilG)
      (fun B _ hBne => by rw [hvanish B hBne, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    blockCharacter_principalBlock_pRegularSum πG hπG hlinG hnilG p]

end OddOrder.RepresentationTheory.Modular
