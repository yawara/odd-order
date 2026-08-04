/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerTruncation
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlock

/-!
# `b^G` is defined when `P C_G(P) ≤ H ≤ N_G(P)` — Navarro (4.14)

The induced central character `λ_b^G` is only *a priori* linear, and the induced block `b^G` is
defined exactly when it happens to be multiplicative
(`OddOrder.RepresentationTheory.Modular.inducedBlock`).  Navarro (4.14) says this always happens
for `P C_G(P) ≤ H ≤ N_G(P)`, because there `λ_b^G = λ_b ∘ Br_P` and both factors are algebra
homomorphisms.

Both halves are now available:

* `blockCharacter_truncClassSumCenter_eq` — `λ_b^G(K̂) = λ_b(Br_P(K̂))` on the class-sum basis;
* `brauerTrunc_mul_of_mem_center` — `Br_P : Z(kG) → Z(kH)` is multiplicative.

Assembling them gives the algebra homomorphism `λ_b ∘ Br_P` and hence the block `b^G`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.brauerCenterHom` — `Br_P : Z(kG) →ₐ[k] Z(kH)`
* `OddOrder.RepresentationTheory.Modular.inducedCentralCharacterAlgHom` — `λ_b^G` as an `AlgHom`
* `OddOrder.RepresentationTheory.Modular.inducedBlockOfNormalizer` — the block `b^G`

## Main results

* `OddOrder.RepresentationTheory.Modular.inducedCentralCharacterAlgHom_toLinearMap` — it really is
  Navarro's `λ_b^G`, so `b^G` is defined
* `OddOrder.RepresentationTheory.Modular.blockCharacter_inducedBlockOfNormalizer` —
  `λ_{b^G}(K̂) = λ_b(Br_P(K̂))`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupAlgebra
open OddOrder.GroupTheory.CenterClassSum

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {P H : Subgroup G} [Fintype H]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (P : Set G)]

/-! ### `Br_P` as an algebra homomorphism of centres -/

variable (P H) in
/-- **The Brauer homomorphism on centres**, `Br_P : Z(kG) →ₐ[k] Z(kH)`.  Multiplicativity is
`brauerTrunc_mul_of_mem_center`, i.e. `brauerProj_mul_of_invariant` transported along the
injective inclusion `k[H] ↪ k[G]`. -/
noncomputable def brauerCenterHom {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₐ[k]
      ↥(Subalgebra.center k (MonoidAlgebra k ↥H)) :=
  AlgHom.mk'
    { toFun := brauerTruncCenter P H hHN
      map_one' := Subtype.ext brauerTrunc_one
      map_mul' := fun x y =>
        Subtype.ext (brauerTrunc_mul_of_mem_center Fact.out (CharP.cast_eq_zero k p)
          hP hCH x.2 y.2)
      map_zero' := Subtype.ext brauerTrunc_zero
      map_add' := fun _ _ => Subtype.ext (brauerTrunc_add _ _) }
    fun c _ => Subtype.ext (brauerTrunc_smul c _)

omit [DecidableEq (ConjClasses G)] in
@[simp]
theorem coe_brauerCenterHom_apply {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (x : ↥(Subalgebra.center k (MonoidAlgebra k G))) :
    ((brauerCenterHom P H hP hCH hHN x : ↥(Subalgebra.center k (MonoidAlgebra k ↥H))) :
        MonoidAlgebra k ↥H)
      = brauerTrunc P H (x : MonoidAlgebra k G) := rfl

/-! ### `λ_b^G` as an algebra homomorphism -/

variable [Fintype (ConjClasses G)]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (πH : MonoidAlgebra k ↥H →+* ∀ j, Matrix (nn j) (nn j) k)
  (hπH : Function.Surjective πH)
  (hlinH : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)

/-- **Navarro (4.14)**: `λ_b^G = λ_b ∘ Br_P`, *as an algebra homomorphism*. -/
noncomputable def inducedCentralCharacterAlgHom {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (b : Block πH hπH hlinH) :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₐ[k] k :=
  (blockCharacter πH hπH hlinH b).comp (brauerCenterHom P H hP hCH hHN)

/-- **The induced block `b^G` is defined** when `P C_G(P) ≤ H ≤ N_G(P)`: the algebra homomorphism
`λ_b ∘ Br_P` *is* Navarro's linear map `λ_b^G`.  Both sides are linear, so it is enough to compare
them on the class-sum basis of `Z(kG)`, which is
`blockCharacter_truncClassSumCenter_eq`. -/
theorem inducedCentralCharacterAlgHom_toLinearMap {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (b : Block πH hπH hlinH) :
    (inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN b).toLinearMap
      = inducedCentralCharacter H (blockCharacter πH hπH hlinH b).toLinearMap := by
  refine (centerBasis (k := k) (G := G)).ext fun C => ?_
  rw [centerBasis_apply, inducedCentralCharacter_classSumCenter]
  have hval : brauerCenterHom P H hP hCH hHN (classSumCenter (k := k) C)
      = centralizerTruncClassSumCenter hHN C :=
    Subtype.ext (brauerTrunc_classSum C)
  change blockCharacter πH hπH hlinH b
      (brauerCenterHom P H hP hCH hHN (classSumCenter (k := k) C)) = _
  rw [hval]
  exact (blockCharacter_truncClassSumCenter_eq πH hπH hlinH hP hPH hHN b C).symm

/-! ### The block `b^G` -/

variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k)
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
variable (hnilG : ∀ x : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi πG hπG hlinG x = 0 → IsNilpotent x)

/-- **The induced block `b^G`**, for `P C_G(P) ≤ H ≤ N_G(P)`.  Unlike `inducedBlock`, this needs
no hypothesis: Navarro (4.14) supplies the multiplicativity. -/
noncomputable def inducedBlockOfNormalizer {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hPH : P ≤ H)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (b : Block πH hπH hlinH) :
    Block πG hπG hlinG :=
  inducedBlock H πG hπG hlinG πH hπH hlinH hnilG b
    (inducedCentralCharacterAlgHom πH hπH hlinH hP hCH hHN b)
    (inducedCentralCharacterAlgHom_toLinearMap πH hπH hlinH hP hPH hCH hHN b)

/-- **The defining property of `b^G` in the normaliser case**: `λ_{b^G}(K̂) = λ_b(Br_P(K̂))`. -/
theorem blockCharacter_inducedBlockOfNormalizer {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p ↥P) (hPH : P ≤ H)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (b : Block πH hπH hlinH) (C : ConjClasses G) :
    blockCharacter πG hπG hlinG
        (inducedBlockOfNormalizer πH hπH hlinH πG hπG hlinG hnilG hP hPH hCH hHN b)
        (classSumCenter C)
      = blockCharacter πH hπH hlinH b (centralizerTruncClassSumCenter hHN C) := by
  rw [inducedBlockOfNormalizer, blockCharacter_inducedBlock_classSumCenter]
  exact blockCharacter_truncClassSumCenter_eq πH hπH hlinH hP hPH hHN b C

end OddOrder.RepresentationTheory.Modular
