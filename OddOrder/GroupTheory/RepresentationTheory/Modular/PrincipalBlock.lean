/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacterBlock
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.CenterSimplesOrbit

/-!
# The principal block

The **principal block** `B_0` of `kG` is the block containing the trivial character.  Its central
character is the **augmentation** `ε : kG → k` restricted to the centre — the trivial
representation acts on `k` by `ε` — so `λ_{B_0}(K̂) = |K|·1`.

Taking the augmentation as the *definition* avoids having to locate the trivial character inside a
Wedderburn splitting, and it is the form in which the third main theorem uses `B_0`: `b_0^G = B_0`
becomes the congruence `|K ∩ C_G(P)| ≡ |K| (mod p)`.

The augmentation itself is `OddOrder.Algebra.augmentation` and its restriction to the centre is
`OddOrder.GroupTheory.CenterSimplesOrbit.aug`; only the block is new here.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.principalBlock` — `B_0`

## Main results

* `OddOrder.RepresentationTheory.Modular.aug_classSumCenter` — `λ_{B_0}(K̂) = |K|·1`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_principalBlock`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum
open OddOrder.GroupTheory.CenterSimplesOrbit (aug aug_apply)

section Augmentation

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]

open scoped Classical in
/-- **`λ_{B_0}(K̂) = |K|·1`.**  The augmentation of a class sum is the size of the class. -/
theorem aug_classSumCenter (C : ConjClasses G) :
    aug (classSumCenter (k := k) C)
      = ((Finset.univ.filter fun g : G => ConjClasses.mk g = C).card : k) := by
  classical
  rw [aug_apply, classSumCenter_coe, classSum, map_sum]
  rw [Finset.sum_congr rfl fun g _ => show
      OddOrder.Algebra.augmentation k G
          (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0)
        = if ConjClasses.mk g = C then (1 : k) else 0 from by
    split
    · rw [MonoidAlgebra.of_apply, OddOrder.Algebra.augmentation_single]
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
  blockOfCentralCharacter π hπ hlin hnil aug

/-- **The defining property of `B_0`.** -/
theorem blockCharacter_principalBlock :
    blockCharacter π hπ hlin (principalBlock π hπ hlin hnil) = aug :=
  blockCharacter_blockOfCentralCharacter π hπ hlin hnil _

/-- **A Brauer character whose central character is the augmentation lies in `B_0`.**  This is the
converse reading of the definition, and it is how the trivial representation is recognised: the
group algebra acts on it through the augmentation (`asAlgebraHom_trivial`), so every irreducible
Brauer constituent of its reduction has central character `aug`. -/
theorem mk_eq_principalBlock_of_centralCharacterAlg_eq (i : ι)
    (h : centralCharacterAlg π i hπ hlin = aug) :
    Quotient.mk (blockSetoid π hπ hlin) i = principalBlock π hπ hlin hnil :=
  eq_blockOfCentralCharacter π hπ hlin hnil ((blockCharacter_mk π hπ hlin i).trans h)

end PrincipalBlock

end OddOrder.RepresentationTheory.Modular
