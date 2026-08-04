/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacterBlock
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis

/-!
# The principal block

The **principal block** `B_0` of `kG` is the block containing the trivial character.  Its central
character is the **augmentation** `ε : kG → k` restricted to the centre — the trivial
representation acts on `k` by `ε` — so `λ_{B_0}(K̂) = |K|·1`.

Taking the augmentation as the *definition* avoids having to locate the trivial character inside a
Wedderburn splitting, and it is the form in which the third main theorem uses `B_0`: `b_0^G = B_0`
becomes the congruence `|K ∩ C_G(P)| ≡ |K| (mod p)`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.augmentation` — `ε : kG →ₐ[k] k`
* `OddOrder.RepresentationTheory.Modular.principalCentralCharacter` — `λ_{B_0}`
* `OddOrder.RepresentationTheory.Modular.principalBlock` — `B_0`

## Main results

* `OddOrder.RepresentationTheory.Modular.principalCentralCharacter_classSumCenter` —
  `λ_{B_0}(K̂) = |K|·1`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_principalBlock`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum

section Augmentation

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- **The augmentation** `ε : kG →ₐ[k] k`, the character of the trivial representation.

⚠ `OddOrder.augmentation` (`Algebra/AugmentationIdeal`) is the `ℤ` case of this, used for the
augmentation ideal; generalising it to an arbitrary base ring would subsume this definition, but
it has ~70 call sites and the refactor is deferred. -/
noncomputable def augmentation : MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G (1 : G →* k)

@[simp]
theorem augmentation_single (g : G) (r : k) : augmentation k (single g r) = r := by
  rw [augmentation, MonoidAlgebra.lift_single]
  simp

variable {k}

/-- **The central character of the principal block**: the augmentation, restricted to the
centre. -/
noncomputable def principalCentralCharacter :
    Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  (augmentation k).comp (Subalgebra.center k (MonoidAlgebra k G)).val

@[simp]
theorem principalCentralCharacter_apply (z : Subalgebra.center k (MonoidAlgebra k G)) :
    principalCentralCharacter z = augmentation k (z : MonoidAlgebra k G) := rfl

variable [Fintype G] [DecidableEq (ConjClasses G)]

open scoped Classical in
/-- **`λ_{B_0}(K̂) = |K|·1`.**  The augmentation of a class sum is the size of the class. -/
theorem principalCentralCharacter_classSumCenter (C : ConjClasses G) :
    principalCentralCharacter (classSumCenter (k := k) C)
      = ((Finset.univ.filter fun g : G => ConjClasses.mk g = C).card : k) := by
  classical
  rw [principalCentralCharacter_apply, classSumCenter_coe, classSum, map_sum]
  rw [Finset.sum_congr rfl fun g _ => show
      augmentation k (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0)
        = if ConjClasses.mk g = C then (1 : k) else 0 from by
    split
    · rw [MonoidAlgebra.of_apply, augmentation_single]
    · rw [map_zero]]
  rw [Finset.sum_boole]

end Augmentation

section PrincipalBlock

variable {k G : Type*} [Field k] [Group G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)]
  [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)

/-- **The principal block** `B_0`: the block whose central character is the augmentation. -/
noncomputable def principalBlock : Block π hπ hlin :=
  blockOfCentralCharacter π hπ hlin hnil principalCentralCharacter

/-- **The defining property of `B_0`.** -/
theorem blockCharacter_principalBlock :
    blockCharacter π hπ hlin (principalBlock π hπ hlin hnil) = principalCentralCharacter :=
  blockCharacter_blockOfCentralCharacter π hπ hlin hnil _

end PrincipalBlock

end OddOrder.RepresentationTheory.Modular
