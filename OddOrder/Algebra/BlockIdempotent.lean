/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Idempotents
import OddOrder.Algebra.CentralCharacter
import OddOrder.Algebra.SeparatingSubalgebra

/-!
# Block idempotents

The blocks of `A` are the classes of indices that the centre cannot separate
(`CentralCharacter`).  Passing to the quotient, the central characters give an algebra map

`Φ : Z(A) →ₐ[k] (blocks → k)`,

which is *surjective*: its image separates the blocks by construction, and a separating
subalgebra of a finite product of copies of a field is everything
(`Subalgebra.eq_top_of_separates`).  Since the kernel of the splitting is nil — for `A = kG` it
is `J(kG)` — the indicator of a block lifts uniquely to an idempotent of `Z(A)`: the **block
idempotent** `e_B`.

## Main results

* `OddOrder.MatrixModule.surjective_blockCharacterPi`
* `OddOrder.MatrixModule.existsUnique_blockIdempotent`
* `OddOrder.MatrixModule.exists_completeOrthogonalIdempotents_block`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] [Finite ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable {A : Type*} [Ring A] [Algebra k A]
variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)

/-- **The block partition**: two indices are in the same block when the centre acts on them by
the same character. -/
def blockSetoid : Setoid ι where
  r i j := centralCharacterAlg π i hπ hlin = centralCharacterAlg π j hπ hlin
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The set of blocks of `A`. -/
abbrev Block : Type _ := Quotient (blockSetoid π hπ hlin)

/-- The central character of a block. -/
noncomputable def blockCharacter (c : Block π hπ hlin) : Subalgebra.center k A →ₐ[k] k :=
  Quotient.liftOn c (fun i => centralCharacterAlg π i hπ hlin) fun _ _ h => h

omit [Finite ι] in
@[simp]
theorem blockCharacter_mk (i : ι) :
    blockCharacter π hπ hlin (Quotient.mk (blockSetoid π hπ hlin) i)
      = centralCharacterAlg π i hπ hlin := rfl

/-- The central characters of all blocks, assembled. -/
noncomputable def blockCharacterPi :
    Subalgebra.center k A →ₐ[k] (Block π hπ hlin → k) :=
  Pi.algHom _ _ fun c => blockCharacter π hπ hlin c

omit [Finite ι] in
@[simp]
theorem blockCharacterPi_apply (z : Subalgebra.center k A) (c : Block π hπ hlin) :
    blockCharacterPi π hπ hlin z c = blockCharacter π hπ hlin c z := rfl

/-- **The central characters realise every function on the blocks.**  The image separates the
blocks by construction, and a separating subalgebra of `blocks → k` is everything. -/
theorem surjective_blockCharacterPi : Function.Surjective (blockCharacterPi π hπ hlin) := by
  haveI : Finite (Block π hπ hlin) := Quotient.finite _
  rw [← AlgHom.range_eq_top]
  refine Subalgebra.eq_top_of_separates fun c c' hcc => ?_
  induction c using Quotient.ind with | _ i =>
  induction c' using Quotient.ind with | _ j =>
  have hne : centralCharacterAlg π i hπ hlin ≠ centralCharacterAlg π j hπ hlin := fun h =>
    hcc (Quotient.sound h)
  obtain ⟨z, hz⟩ : ∃ z : Subalgebra.center k A,
      centralCharacterAlg π i hπ hlin z ≠ centralCharacterAlg π j hπ hlin z := by
    by_contra hcon
    push Not at hcon
    exact hne (AlgHom.ext hcon)
  exact ⟨blockCharacterPi π hπ hlin z, ⟨z, rfl⟩, hz⟩

/-- **The block idempotents.**  If the kernel of the splitting is nil — for `A = kG` it is the
Jacobson radical — then the indicator of each block lifts uniquely to a central idempotent. -/
theorem existsUnique_blockIdempotent
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    [DecidableEq (Block π hπ hlin)] (c : Block π hπ hlin) :
    ∃! e : Subalgebra.center k A,
      IsIdempotentElem e ∧ blockCharacterPi π hπ hlin e = Pi.single c 1 := by
  classical
  set f : Subalgebra.center k A →+* (Block π hπ hlin → k) :=
    (blockCharacterPi π hπ hlin).toRingHom with hf
  have hsurj : Function.Surjective f := surjective_blockCharacterPi π hπ hlin
  have hidem : IsIdempotentElem (Pi.single c 1 : Block π hπ hlin → k) := by
    funext d
    by_cases h : c = d
    · subst h; simp
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  exact existsUnique_isIdempotentElem_eq_of_ker_isNilpotent f
    (fun x hx => hnil x (RingHom.mem_ker.mp hx)) _ (hsurj _) hidem

/-- **The block idempotents are a complete orthogonal family**: `∑_B e_B = 1` and
`e_B e_{B'} = 0` for `B ≠ B'`.  This is the block decomposition of the centre, and through it of
`A` itself. -/
theorem exists_completeOrthogonalIdempotents_block
    [Fintype (Block π hπ hlin)] [DecidableEq (Block π hπ hlin)]
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x) :
    ∃ e : Block π hπ hlin → Subalgebra.center k A,
      CompleteOrthogonalIdempotents e ∧
      ∀ c, blockCharacterPi π hπ hlin (e c) = Pi.single c 1 := by
  set f : Subalgebra.center k A →+* (Block π hπ hlin → k) :=
    (blockCharacterPi π hπ hlin).toRingHom with hf
  have hsurj : Function.Surjective f := surjective_blockCharacterPi π hπ hlin
  obtain ⟨e, he, hfe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker f
    (fun x hx => hnil x (RingHom.mem_ker.mp hx))
    (CompleteOrthogonalIdempotents.single fun _ : Block π hπ hlin => k)
    (fun c => hsurj _)
  exact ⟨e, he, fun c => congrFun hfe c⟩

end OddOrder.MatrixModule
