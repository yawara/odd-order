/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacterBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.TruncClassSum

/-!
# The induced block `b^G` (Brauer correspondence)

**Navarro, before (4.13).**  Let `H ≤ G` and let `b` be a block of `H`, with central character
`λ_b : Z(kH) →ₐ[k] k`.  Extend it to a *linear* map on `Z(kG)` by

`λ_b^G(K̂) = λ_b( ∑_{x ∈ K ∩ H} x )`

(`TruncClassSum.inducedCentralCharacter`).  This need not be multiplicative; when it *is* — that
is, when it is the underlying linear map of an algebra homomorphism `Λ` — Navarro (3.11)
(`CentralCharacterBlock.existsUnique_blockCharacter_eq`) supplies a unique block `b^G` of `G` with
`λ_{b^G} = Λ`.  That block is the **induced block**.

The multiplicativity is carried as a hypothesis, exactly as in the textbook: `b^G` "is defined"
precisely when such a `Λ` exists.  Navarro (4.14) will show it always is when
`P C_G(P) ≤ H ≤ N_G(P)`.

⚠ There are several inequivalent notions of induced block in the literature (Brauer's, used here,
and Alperin–Burry's); they agree in the cases that matter.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.inducedBlock` — `b^G`

## Main results

* `OddOrder.RepresentationTheory.Modular.blockCharacter_inducedBlock_classSumCenter` — the
  defining property `λ_{b^G}(K̂) = λ_b(∑_{x ∈ K ∩ H} x)`
* `OddOrder.RepresentationTheory.Modular.eq_inducedBlock` — uniqueness
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable (H : Subgroup G) [Fintype H]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
  (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k) (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
variable {ιH : Type*} [Finite ιH] {nnH : ιH → Type*} [∀ j, Fintype (nnH j)]
  [∀ j, DecidableEq (nnH j)] [∀ j, Nonempty (nnH j)]
  (πH : MonoidAlgebra k H →+* ∀ j, Matrix (nnH j) (nnH j) k) (hπH : Function.Surjective πH)
  (hlinH : ∀ (c : k) (a : MonoidAlgebra k H), πH (c • a) = c • πH a)
variable (hnilG : ∀ x : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi πG hπG hlinG x = 0 → IsNilpotent x)

/-- **The induced block `b^G`.**  Defined when the induced central character `λ_b^G` is (the
linear map underlying) an algebra homomorphism `Λ`; then `b^G` is the unique block of `G` with
central character `Λ`. -/
noncomputable def inducedBlock (b : Block πH hπH hlinH)
    (lam : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    (_hlam : lam.toLinearMap
      = inducedCentralCharacter H (blockCharacter πH hπH hlinH b).toLinearMap) :
    Block πG hπG hlinG :=
  blockOfCentralCharacter πG hπG hlinG hnilG lam

omit [Finite ιH] in
/-- **The defining property of the induced block**: `λ_{b^G}(K̂) = λ_b(∑_{x ∈ K ∩ H} x)`. -/
theorem blockCharacter_inducedBlock_classSumCenter (b : Block πH hπH hlinH)
    (lam : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    (hlam : lam.toLinearMap
      = inducedCentralCharacter H (blockCharacter πH hπH hlinH b).toLinearMap)
    (C : ConjClasses G) :
    blockCharacter πG hπG hlinG (inducedBlock H πG hπG hlinG πH hπH hlinH hnilG b lam hlam)
        (classSumCenter C)
      = blockCharacter πH hπH hlinH b (truncClassSumCenter (k := k) H C) := by
  rw [inducedBlock, blockCharacter_blockOfCentralCharacter,
    show lam (classSumCenter C) = lam.toLinearMap (classSumCenter C) from rfl, hlam,
    inducedCentralCharacter_classSumCenter]
  rfl

omit [Finite ιH] in
/-- **Uniqueness**: `b^G` is the only block of `G` whose central character is `λ_b^G`. -/
theorem eq_inducedBlock (b : Block πH hπH hlinH)
    (lam : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    (hlam : lam.toLinearMap
      = inducedCentralCharacter H (blockCharacter πH hπH hlinH b).toLinearMap)
    {c : Block πG hπG hlinG} (hc : blockCharacter πG hπG hlinG c = lam) :
    c = inducedBlock H πG hπG hlinG πH hπH hlinH hnilG b lam hlam :=
  eq_blockOfCentralCharacter πG hπG hlinG hnilG hc

end OddOrder.RepresentationTheory.Modular
