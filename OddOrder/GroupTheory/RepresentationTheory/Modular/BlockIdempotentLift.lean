/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockIdempotent
import OddOrder.Algebra.CenterGroupAlgebraAlgClosed
import OddOrder.GroupTheory.RepresentationTheory.Modular.PModularSystem

/-!
# Block idempotents over `𝒪`

`Algebra/BlockIdempotent` produces the block idempotent `e_B ∈ Z(kG)` of a block of the residue
algebra, and `Algebra/CenterIdempotentLift` lifts idempotents of `Z(kG)` uniquely to `Z(𝒪G)`.
Composing them gives Navarro's `f_B ∈ Z(𝒪G)`, which is what the second main theorem consumes.

The statement is packaged as bare existence: uniqueness is available from the two inputs, but the
consumers only ever need one such idempotent per block.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_isIdempotentElem_blockCharacterPi_eq_single`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix OddOrder.MatrixModule

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
variable {G : Type*} [Group G] [Finite G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)

/-- **Navarro's block idempotent `f_B ∈ Z(𝒪G)`.**  The block idempotent of `Z(kG)`
(`existsUnique_blockIdempotent`) lifted along the reduction
(`existsUnique_isIdempotentElem_mapRingHom_eq_of_isAlgClosed`). -/
theorem exists_isIdempotentElem_blockCharacterPi_eq_single
    (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    [DecidableEq (Block π hπ hlin)] (c : Block π hπ hlin) :
    ∃ f : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)), IsIdempotentElem f ∧
      blockCharacterPi π hπ hlin (OddOrder.centerReduce (residue 𝒪) f) = Pi.single c 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Finite (ConjClasses G) := Quotient.finite _
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  obtain ⟨e, ⟨hei, hec⟩, -⟩ := existsUnique_blockIdempotent π hπ hlin hnil c
  obtain ⟨f, ⟨hfi, hfr⟩, -⟩ :=
    OddOrder.existsUnique_isIdempotentElem_mapRingHom_eq_of_isAlgClosed
      (residue 𝒪) residue_surjective (ker_residue) inferInstance
      e.2 (congrArg Subtype.val hei)
  refine ⟨f, hfi, ?_⟩
  rw [show OddOrder.centerReduce (residue 𝒪) f = e from Subtype.ext hfr]
  exact hec

/-- **The whole family `(f_B)_B` of block idempotents in `Z(𝒪G)`.**  Choosing one for each block
packages the three hypotheses that Külshammer's formula and the third main theorem carry on the
`𝒪` side: the family is idempotent (`hidem`), its reduction is the named family of `Z(kG)`
(`hf`, which is `rfl` for `centerReduce`), and the block character picks out the block (`hB`). -/
theorem exists_blockIdempotentFamily
    (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    [DecidableEq (Block π hπ hlin)] :
    ∃ (F : Block π hπ hlin → ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)))
      (F' : Block π hπ hlin →
        ↥(Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G))),
      (∀ B, IsIdempotentElem (F B)) ∧
      (∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
        = ((F' B : MonoidAlgebra (ResidueField 𝒪) G))) ∧
      (∀ B, blockCharacterPi π hπ hlin (F' B) = Pi.single B 1) := by
  classical
  choose F hFi hFc using exists_isIdempotentElem_blockCharacterPi_eq_single π hπ hlin hnil
  exact ⟨F, fun B => OddOrder.centerReduce (residue 𝒪) (F B), hFi, fun _ => rfl, hFc⟩

end OddOrder.RepresentationTheory.Modular
