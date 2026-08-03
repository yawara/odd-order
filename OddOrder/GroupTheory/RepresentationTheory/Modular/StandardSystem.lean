/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.SplittingSystem

/-!
# The standard `p`-modular system

The two sides of the theory ask different things of the residue field `k`:

* the *count* (`BrauerCount`) needs `k` to split every group algebra, for which algebraic
  closedness is the convenient sufficient condition;
* the *Brauer characters* (`BrauerCharacter`) need `k` to contain the `n`-th roots of unity for
  `n = |G|_{p'}`.

Both hold simultaneously for `𝕎(𝔽̄_p)`, the Witt vectors over an algebraic closure of `𝔽_p`:
the residue field is `𝔽̄_p` itself (`wittVectorResidueFieldEquiv`), which is algebraically closed
(`instIsAlgClosedResidueFieldWittVector`) and contains `GF(p ^ φ(n))`
(`hasEnoughRootsOfUnity_of_isAlgClosed`).  So the whole development is non-vacuous, and this file
records the instantiation.

## Main results

* `OddOrder.RepresentationTheory.Modular.StandardSystem`
* `OddOrder.RepresentationTheory.Modular.exists_isPrimitiveRoot_pRegularExponent_standardSystem`
* `OddOrder.RepresentationTheory.Modular.exists_surjective_blocks_card_eq_standardSystem`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing OddOrder.GroupTheory

variable (p : ℕ) [Fact p.Prime]

/-- **The standard `p`-modular system**: the Witt vectors over an algebraic closure of `𝔽_p`.
Its residue field is algebraically closed *and* has all roots of unity of order prime to `p`. -/
abbrev StandardSystem : Type := WittVector p (AlgebraicClosure (ZMod p))

theorem hasEnoughRootsOfUnity_residueField_standardSystem {n : ℕ} (hp : ¬ p ∣ n) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity (ResidueField (StandardSystem p)) n :=
  hasEnoughRootsOfUnity_of_isAlgClosed p n _ hp hn

/-- **A primitive `|G|_{p'}`-th root of unity exists in the residue field of the standard
system.**  This is the hypothesis `hω` that the Brauer character theorems carry. -/
theorem exists_isPrimitiveRoot_pRegularExponent_standardSystem
    (G : Type*) [Group G] [Finite G] :
    ∃ ω : ResidueField (StandardSystem p), IsPrimitiveRoot ω (pRegularExponent p G) := by
  have hpos : 0 < pRegularExponent p G := pRegularExponent_pos
  haveI : NeZero (pRegularExponent p G) := ⟨hpos.ne'⟩
  haveI := hasEnoughRootsOfUnity_residueField_standardSystem p
    (not_dvd_pRegularExponent (G := G) Fact.out) hpos.ne'
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

/-- **Brauer's theorem over the standard system.**  Nothing is assumed beyond `G` being a finite
group: the splitting datum, the identification of its blocks with the simple modules, and the
count are all supplied. -/
theorem exists_surjective_blocks_card_eq_standardSystem (G : Type*) [Group G] [Finite G] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : MonoidAlgebra (ResidueField (StandardSystem p)) G →+*
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) (ResidueField (StandardSystem p))),
      Function.Surjective π ∧
      RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField (StandardSystem p)) G) ∧
      n = Nat.card {C : ConjClasses G // IsPRegularClass p C} :=
  exists_surjective_blocks_card_eq Fact.out (CharP.cast_eq_zero _ p)

end OddOrder.RepresentationTheory.Modular
