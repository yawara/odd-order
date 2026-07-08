/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Module.ZMod
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# `φ`-invariant subgroups as subrepresentations of `elabRepresentation`

Bridge for the imprimitive (non-Galois) branch of Peterfalvi (9.7)(a) (issue 9000): the
`U`-invariant order-`p` Clifford blocks `H₁^w` of the chief factor `H̄` become `Subrepresentation`s
of the descended `𝔽_p`-representation `elabRepresentation p φ`, so the generic block bound
`card_le_cyclotomicQuotient_of_blocks` (`TypePGaloisUBound`) can be applied to the imprimitive
decomposition.

The chief factor `H̄` is an elementary abelian `p`-group, written multiplicatively; the descended
`ZMod p`-representation lives on `Additive H̄` (`elabRepresentation`).  A `φ`-invariant subgroup `J`
of `H̄` corresponds (via `AddSubgroup.toZModSubmodule`/`toSubgroup'`, the same order-isomorphism
used in `elabRepresentation_isIrreducible`) to a `ZMod p`-submodule, and the invariance makes it a
subrepresentation.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03

variable {A K : Type*} [Group A] [CommGroup K] {p : ℕ} [Module (ZMod p) (Additive K)]
  {φ : A →* MulAut K}

/-- The subgroup ↔ `ZMod p`-submodule order-isomorphism `Submodule (ZMod p) (Additive K) ≃o
Subgroup K` (the composite of `AddSubgroup.toZModSubmodule` and `AddSubgroup.toSubgroup'`, exactly
the correspondence used inside `elabRepresentation_isIrreducible`). -/
def elabSubmoduleSubgroupEquiv (p : ℕ) [Module (ZMod p) (Additive K)] :
    Submodule (ZMod p) (Additive K) ≃o Subgroup K :=
  (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup'

theorem mem_elabSubmoduleSubgroupEquiv (W : Submodule (ZMod p) (Additive K)) (x : K) :
    x ∈ elabSubmoduleSubgroupEquiv p W ↔ Additive.ofMul x ∈ W := by
  simp only [elabSubmoduleSubgroupEquiv, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
    AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]

/-- Membership in the submodule attached to a subgroup `J`: `v ∈ Φ⁻¹ J ↔ Additive.toMul v ∈ J`. -/
theorem mem_symm_elabSubmoduleSubgroupEquiv (J : Subgroup K) (v : Additive K) :
    v ∈ (elabSubmoduleSubgroupEquiv p).symm J ↔ Additive.toMul v ∈ J := by
  have h := mem_elabSubmoduleSubgroupEquiv (p := p) ((elabSubmoduleSubgroupEquiv p).symm J)
    (Additive.toMul v)
  rw [OrderIso.apply_symm_apply] at h
  exact h.symm

/-- **A `φ`-invariant subgroup as a subrepresentation.**  A subgroup `J` of the elementary abelian
`p`-group `K` invariant under the action `φ : A →* MulAut K` gives a subrepresentation of
`elabRepresentation p φ`, carried on the submodule `Additive.ofMul '' J`.  The `apply_mem`
obligation is the invariance `φ a g ∈ J` (`IsAInvariant.smul_mem`) transported through the action
bridge `elabRepresentation_apply`. -/
def aInvariantSubrep {J : Subgroup K} (hJ : IsAInvariant φ J) :
    Subrepresentation (elabRepresentation p φ) where
  toSubmodule := (elabSubmoduleSubgroupEquiv p).symm J
  apply_mem_toSubmodule g v hv := by
    rw [mem_symm_elabSubmoduleSubgroupEquiv] at hv ⊢
    -- `toMul (elabRepresentation p φ g v) = φ g (toMul v)` by `rfl` (`elabRepresentation_apply`).
    exact hJ.smul_mem g hv

@[simp] theorem aInvariantSubrep_toSubmodule {J : Subgroup K} (hJ : IsAInvariant φ J) :
    (aInvariantSubrep hJ).toSubmodule = (elabSubmoduleSubgroupEquiv p).symm J := rfl

/-- The subrepresentation attached to a `φ`-invariant subgroup `J` has the same cardinality as `J`
(the carrier is `Additive.ofMul '' J`, in bijection with `J`).  Supplies the `hBcard` (each block
has order `p`) input of `card_le_cyclotomicQuotient_of_blocks`. -/
theorem card_aInvariantSubrep {J : Subgroup K} (hJ : IsAInvariant φ J) :
    Nat.card (aInvariantSubrep (p := p) hJ).toSubmodule = Nat.card J := by
  rw [aInvariantSubrep_toSubmodule]
  exact Nat.card_congr
    (Equiv.subtypeEquiv (Additive.toMul (α := K))
      (fun v => mem_symm_elabSubmoduleSubgroupEquiv J v))

end OddOrder.GroupTheory
