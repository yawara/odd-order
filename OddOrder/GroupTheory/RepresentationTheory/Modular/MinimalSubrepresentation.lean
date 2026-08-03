/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OddOrder.GroupTheory.RepresentationTheory.Modular.AsModuleSimple

/-!
# A nonzero finite-dimensional representation has an irreducible subrepresentation

The decomposition of a Brauer character into irreducible ones is an induction on the dimension,
and each step splits off *one* irreducible constituent.  Splitting off a **minimal** nonzero
invariant subspace is more convenient than a maximal proper one: the invariant subspaces of a
subrepresentation are just the invariant subspaces of `V` contained in it, whereas for a quotient
one has to transport the lattice.

Combined with `isSimpleModule_asModule`, the minimal subrepresentation has simple `asModule`,
which is what `exists_irreducibleBrauerCharacter_eq` consumes.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_minimal_invariant`
* `OddOrder.RepresentationTheory.Modular.isSimpleModule_subrepresentation_of_minimal`
-/

namespace OddOrder.RepresentationTheory.Modular

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

/-- **A nonzero finite-dimensional representation has a minimal nonzero invariant subspace**:
take one of least dimension. -/
theorem exists_minimal_invariant [FiniteDimensional k V] [Nontrivial V] :
    ∃ W : Submodule k V, (∀ g : G, W ≤ W.comap (ρ g)) ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k V, (∀ g : G, U ≤ U.comap (ρ g)) → U ≤ W → U = ⊥ ∨ U = W := by
  classical
  have hex : ∃ n : ℕ, ∃ W : Submodule k V, (∀ g : G, W ≤ W.comap (ρ g)) ∧ W ≠ ⊥ ∧
      Module.finrank k W = n :=
    ⟨_, ⊤, fun _ => le_top, top_ne_bot, rfl⟩
  obtain ⟨W, hWinv, hWne, hWrank⟩ := Nat.find_spec hex
  refine ⟨W, hWinv, hWne, fun U hUinv hUle => ?_⟩
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  · right
    have h1 : Nat.find hex ≤ Module.finrank k U := Nat.find_le ⟨U, hUinv, h, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hUle (by omega)

/-- The invariant subspaces of a subrepresentation are the invariant subspaces of `V` inside it,
so a minimal one is irreducible: its `asModule` is simple. -/
theorem isSimpleModule_subrepresentation_of_minimal {W : Submodule k V}
    (hWinv : ∀ g : G, W ≤ W.comap (ρ g)) (hWne : W ≠ ⊥)
    (hmin : ∀ U : Submodule k V, (∀ g : G, U ≤ U.comap (ρ g)) → U ≤ W → U = ⊥ ∨ U = W) :
    IsSimpleModule (MonoidAlgebra k G) (ρ.subrepresentation W hWinv).asModule := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  refine isSimpleModule_asModule _ fun U' hU' => ?_
  set U : Submodule k V := U'.map W.subtype with hU
  have hUle : U ≤ W := by
    rw [hU]
    exact Submodule.map_subtype_le _ _
  have hUinv : ∀ g : G, U ≤ U.comap (ρ g) := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hU' g hu, rfl⟩
  rcases hmin U hUinv hUle with h | h
  · left
    exact Submodule.map_injective_of_injective W.injective_subtype
      (h.trans (Submodule.map_bot W.subtype).symm)
  · right
    exact Submodule.map_injective_of_injective W.injective_subtype
      (h.trans (Submodule.map_subtype_top W).symm)

end OddOrder.RepresentationTheory.Modular
