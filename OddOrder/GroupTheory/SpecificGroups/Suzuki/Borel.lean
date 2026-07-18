/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.GeneratedAction
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The standard Borel subgroup of the Suzuki permutation group

The standard Borel subgroup is the image of the faithful semidirect-product
representation

`RootGroup m semidirect[TorusScaleHom m] TorusParameter m -> StandardPermGroup m`,

whose element `(u,c)` acts as the root-times-torus product `R(u) T(c)`.
The torus-root conjugation formula proves the homomorphism law.  Evaluating at
the affine origin recovers `u`, after which torus faithfulness recovers `c`;
this gives the unique normal form and the exact subgroup order.

This is shared infrastructure for the Suzuki target in **Peterfalvi, Part II,
Chapter I, Theorem A** (pp. 97-98).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

variable {m : ℕ}

/-- The abstract root-torus semidirect product underlying the standard Borel
subgroup. -/
abbrev BorelModel (m : ℕ) := RootGroup m ⋊[torusScaleHom m] TorusParameter m

/-- The root-torus semidirect product represented inside the standard Suzuki
permutation group, in root-times-torus order. -/
noncomputable def borelHom (m : ℕ) : BorelModel m →* standardPermGroup m :=
  SemidirectProduct.lift (rootHom m) (torusHom m) fun c => by
    apply MonoidHom.ext
    intro u
    change rootHom m (torusScale c u) =
      torusHom m c * rootHom m u * (torusHom m c)⁻¹
    exact (torusHom_mul_rootHom_mul_inv c u).symm

@[simp] theorem borelHom_apply (x : BorelModel m) :
    borelHom m x = rootHom m x.left * torusHom m x.right :=
  rfl

/-- The root-times-torus representation is faithful. -/
theorem borelHom_injective (m : ℕ) : Function.Injective (borelHom m) := by
  intro x y hxy
  have horigin := congrArg (fun g : standardPermGroup m => g • Ovoid.origin m) hxy
  have hleft : x.left = y.left := by
    apply Ovoid.affine_injective
    simpa only [borelHom_apply, mul_smul, Ovoid.origin,
      torusHom_smul_affine, map_one, rootHom_smul_affine, mul_one] using horigin
  apply SemidirectProduct.ext
  · exact hleft
  · apply torusHom_injective m
    have hprod :
        rootHom m x.left * torusHom m x.right =
          rootHom m y.left * torusHom m y.right := by
      simpa only [borelHom_apply] using hxy
    rw [hleft] at hprod
    exact mul_left_cancel hprod

/-- The standard Borel subgroup, defined as the range of the faithful
root-torus semidirect representation. -/
noncomputable def standardBorel (m : ℕ) : Subgroup (standardPermGroup m) :=
  (borelHom m).range

/-- Every standard root element belongs to the standard Borel subgroup. -/
theorem rootHom_mem_standardBorel (u : RootGroup m) :
    rootHom m u ∈ standardBorel m :=
  ⟨SemidirectProduct.inl u, SemidirectProduct.lift_inl _ _ _ _⟩

/-- Every standard torus element belongs to the standard Borel subgroup. -/
theorem torusHom_mem_standardBorel (c : TorusParameter m) :
    torusHom m c ∈ standardBorel m :=
  ⟨SemidirectProduct.inr c, SemidirectProduct.lift_inr _ _ _ _⟩

/-- Membership in the Borel subgroup is equivalent to a unique
root-times-torus normal form. -/
theorem mem_standardBorel_iff_existsUnique_root_torus (g : standardPermGroup m) :
    g ∈ standardBorel m ↔
      ∃! p : RootGroup m × TorusParameter m,
        g = rootHom m p.1 * torusHom m p.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x.left, x.right), rfl, ?_⟩
    intro p hp
    have hx : x = (⟨p.1, p.2⟩ : BorelModel m) := by
      apply borelHom_injective m
      exact hp
    exact Prod.ext (congrArg SemidirectProduct.left hx).symm
      (congrArg SemidirectProduct.right hx).symm
  · rintro ⟨p, hp, _⟩
    refine ⟨(⟨p.1, p.2⟩ : BorelModel m), ?_⟩
    exact hp.symm

/-- Every Borel element fixes the point at infinity. -/
theorem standardBorel_le_infinityStabilizer :
    standardBorel m ≤
      MulAction.stabilizer (standardPermGroup m) (Ovoid.infinity m) := by
  rintro _ ⟨x, rfl⟩
  rw [MulAction.mem_stabilizer_iff]
  change (rootHom m x.left * torusHom m x.right) • Ovoid.infinity m =
    Ovoid.infinity m
  rw [mul_smul, torusHom_smul_infinity, rootHom_smul_infinity]

/-- The exact order of the standard Borel subgroup is `q^2 * (q - 1)`, where
`q = 2^(2m+1)`. -/
theorem natCard_standardBorel (m : ℕ) :
    Nat.card (standardBorel m) =
      2 ^ (2 * (2 * m + 1)) * (2 ^ (2 * m + 1) - 1) := by
  calc
    Nat.card (standardBorel m) = Nat.card (BorelModel m) := by
      rw [standardBorel]
      exact (Nat.card_congr
        (MonoidHom.ofInjective (borelHom_injective m)).toEquiv).symm
    _ = 2 ^ (2 * (2 * m + 1)) * (2 ^ (2 * m + 1) - 1) := by
      rw [SemidirectProduct.card, RootGroup.natCard, Nat.card_units, natCard_field]

end OddOrder.GroupTheory.SpecificGroups.Suzuki
