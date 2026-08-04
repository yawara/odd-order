/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.DefectNumber
import OddOrder.Algebra.GroupAlgebraDefectGroup
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock

/-!
# The defect of a block of `kG`

`Algebra/DefectNumber` attaches a defect to any `G`-fixed element of a `G`-algebra.  A block `B`
of `kG` has a canonical such element — its block idempotent `e_B` — so it has a defect `d(B)`.

This is the number the height of an ordinary character is measured against:
`ν(χ(1)) = ν(|G|) - d(B) + ht(χ)`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockIdempotentOf` — `e_B ∈ Z(kG)`
* `OddOrder.RepresentationTheory.Modular.blockDefect` — `d(B)`

## Main results

* `OddOrder.RepresentationTheory.Modular.blockCharacterPi_blockIdempotentOf` — the defining
  property of `e_B`
* `OddOrder.RepresentationTheory.Modular.card_defectGroup_blockIdempotentOf` — `|D| = p^{d(B)}`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.MatrixModule OddOrder.GAlgebra

open scoped OddOrder.Conjugation

variable {k G : Type*} [Field k] [Group G] [Finite G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)]
  [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable [DecidableEq (Block π hπ hlin)]

/-- **The block idempotent `e_B ∈ Z(kG)`.** -/
noncomputable def blockIdempotentOf (B : Block π hπ hlin) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  (existsUnique_blockIdempotent π hπ hlin hnil B).choose

omit [Finite G] in
theorem isIdempotentElem_blockIdempotentOf (B : Block π hπ hlin) :
    IsIdempotentElem (blockIdempotentOf π hπ hlin hnil B) :=
  (existsUnique_blockIdempotent π hπ hlin hnil B).choose_spec.1.1

omit [Finite G] in
/-- **The defining property of `e_B`**: its central characters are the indicator of `B`. -/
theorem blockCharacterPi_blockIdempotentOf (B : Block π hπ hlin) :
    blockCharacterPi π hπ hlin (blockIdempotentOf π hπ hlin hnil B) = Pi.single B 1 :=
  (existsUnique_blockIdempotent π hπ hlin hnil B).choose_spec.1.2

omit [Finite G] in
/-- `e_B` is fixed by conjugation, being central. -/
theorem forall_smul_blockIdempotentOf (B : Block π hπ hlin) (g : G) :
    g • ((blockIdempotentOf π hπ hlin hnil B : Subalgebra.center k (MonoidAlgebra k G)) :
      MonoidAlgebra k G) = (blockIdempotentOf π hπ hlin hnil B : MonoidAlgebra k G) :=
  OddOrder.GroupAlgebra.mem_center_iff_forall_smul_eq.mp
    (blockIdempotentOf π hπ hlin hnil B).2 g

/-- **The defect of a block** `d(B)`: the defect of its block idempotent. -/
noncomputable def blockDefect (p : ℕ) (B : Block π hπ hlin) : ℕ :=
  defect p (forall_smul_blockIdempotentOf π hπ hlin hnil B)

/-- **`|D| = p^{d(B)}`** for the chosen defect group of `B`.  The invertibility hypothesis holds
over a field of characteristic `p`, where an integer prime to `p` is a unit. -/
theorem card_defectGroup_blockIdempotentOf {p : ℕ} (hp : p.Prime)
    (hinv : ∀ n : ℕ, ¬ p ∣ n → ∃ v : MonoidAlgebra k G,
      (∀ g : G, g • v = v) ∧ (n • (1 : MonoidAlgebra k G)) * v = 1)
    (B : Block π hπ hlin) :
    Nat.card ↥(defectGroup (forall_smul_blockIdempotentOf π hπ hlin hnil B))
      = p ^ blockDefect π hπ hlin hnil p B :=
  card_defectGroup hp hinv _

end OddOrder.RepresentationTheory.Modular
