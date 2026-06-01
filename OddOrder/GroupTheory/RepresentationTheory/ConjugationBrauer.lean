/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation
import OddOrder.GroupTheory.RepresentationTheory.Clifford

/-!
# Brauer's permutation lemma for ambient conjugation

This file starts the conjugation-specific packaging of Brauer's permutation lemma.
For a normal subgroup `H ⊴ G` and `g : G`, conjugation by `g` gives compatible
permutations of `Irr H` and of the conjugacy classes of `H`.  The general Brauer
permutation lemma then identifies their fixed-point counts.

This is the Layer B bridge needed by Peterfalvi (6.8): later files use the fixed
conjugacy-class side, together with Frobenius fixed-point-freeness, to prove
`ClassFunction.inertia θ = H` for nontrivial `θ`.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal]

namespace IrreducibleCharacter

/-- The permutation of `Irr H` induced by ambient conjugation by `g : G`. -/
noncomputable def conjByPerm (g : G) : Equiv.Perm (IrreducibleCharacter H) where
  toFun θ := conjBy (G := G) (H := H) g θ
  invFun θ := conjBy (G := G) (H := H) g⁻¹ θ
  left_inv θ := by
    exact conjBy_inv_conjBy (G := G) (H := H) g θ
  right_inv θ := by
    exact conjBy_conjBy_inv (G := G) (H := H) g θ

@[simp] theorem conjByPerm_apply (g : G) (θ : IrreducibleCharacter H) :
    conjByPerm (G := G) (H := H) g θ = conjBy (G := G) (H := H) g θ :=
  rfl

end IrreducibleCharacter

namespace ConjClasses

/-- The permutation of conjugacy classes of `H` induced by ambient conjugation by `g : G`. -/
noncomputable def conjByPerm (g : G) : Equiv.Perm (ConjClasses H) where
  toFun := ConjClasses.map (ClassFunction.conjByMulEquiv (G := G) (H := H) g : H →* H)
  invFun := ConjClasses.map (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ : H →* H)
  left_inv C := by
    rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
    change ConjClasses.mk
        (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹
          (ClassFunction.conjByMulEquiv (G := G) (H := H) g h)) = ConjClasses.mk h
    have hh :
        ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹
            (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) = h := by
      apply Subtype.ext
      simp only [ClassFunction.conjByMulEquiv_apply]
      group
    rw [hh]
  right_inv C := by
    rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
    change ConjClasses.mk
        (ClassFunction.conjByMulEquiv (G := G) (H := H) g
          (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ h)) = ConjClasses.mk h
    have hh :
        ClassFunction.conjByMulEquiv (G := G) (H := H) g
            (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ h) = h := by
      apply Subtype.ext
      simp only [ClassFunction.conjByMulEquiv_apply]
      group
    rw [hh]

@[simp] theorem conjByPerm_mk (g : G) (h : H) :
    conjByPerm (G := G) (H := H) g (ConjClasses.mk h) =
      ConjClasses.mk (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) :=
  rfl

end ConjClasses

/-- Compatibility of ambient conjugation on irreducible characters with ambient conjugation on
conjugacy classes, in the exact form consumed by `brauer_permutation_lemma_general'`. -/
theorem characterTableEntry_conjByPerm
    (g : G) (χ : IrreducibleCharacter H) (C : ConjClasses H) :
    characterTableEntry (IrreducibleCharacter.conjByPerm (G := G) (H := H) g χ) C =
      characterTableEntry χ (ConjClasses.conjByPerm (G := G) (H := H) g C) := by
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  rw [ConjClasses.conjByPerm_mk, characterTableEntry_mk, characterTableEntry_mk]
  change (ClassFunction.conjBy (G := G) (H := H) g (χ : ClassFunction H ℂ)) h =
    (χ : ClassFunction H ℂ) (ClassFunction.conjByMulEquiv (G := G) (H := H) g h)
  rfl

/-- Brauer's permutation lemma specialized to ambient conjugation by `g : G`. -/
theorem card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm
    [Finite H] (g : G) :
    Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)) =
      Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) :=
  brauer_permutation_lemma_general'
    (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)
    (ConjClasses.conjByPerm (G := G) (H := H) g)
    (characterTableEntry_conjByPerm (G := G) (H := H) g)

end OddOrder.RepresentationTheory
