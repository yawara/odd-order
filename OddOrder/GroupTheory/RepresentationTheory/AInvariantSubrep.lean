/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Module.ZMod
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.GroupTheory.RepresentationTheory.LineScalarCharacter
import OddOrder.Mathlib.Subgroup

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

/-- **The kernel of a block's scalar character is the pointwise stabiliser of that block.**

For an order-`p` (hence `𝔽_p`-line) `φ`-invariant subgroup `J`, an element of the acting group `A`
acts on `J` by the scalar `1` exactly when it fixes `J` elementwise, i.e. when it lies in
`Subgroup.ptStabOfMulAut φ J`.

This is the bridge that turns Peterfalvi (9.7)(a)'s block-scalar order `|im φ_J| = |A : ker φ_J|`
into the book's index `a = |U : C_U(H₁)|`, and lets the `W₁`-conjugacy of the blocks be applied
through `Subgroup.index_ptStabOfMulAut_smul` (issue 0152). -/
theorem ker_lineScalarChar_aInvariantSubrep [Fact p.Prime] [Finite K] {J : Subgroup K}
    (hJ : IsAInvariant φ J)
    (hcard : Nat.card (aInvariantSubrep (p := p) hJ).toSubmodule = p) :
    (OddOrder.RepresentationTheory.lineScalarChar
        (aInvariantSubrep (p := p) hJ).toRepresentation
        (OddOrder.RepresentationTheory.finrank_eq_one_of_card_eq_prime hcard)).ker
      = Subgroup.ptStabOfMulAut φ J := by
  ext a
  rw [MonoidHom.mem_ker, OddOrder.RepresentationTheory.lineScalarChar_eq_one_iff,
    Subgroup.mem_ptStabOfMulAut]
  constructor
  · intro h x hx
    have hmem : Additive.ofMul x ∈ (aInvariantSubrep (p := p) hJ).toSubmodule :=
      (mem_symm_elabSubmoduleSubgroupEquiv (p := p) J (Additive.ofMul x)).mpr (by simpa using hx)
    have := congrArg Subtype.val (h ⟨Additive.ofMul x, hmem⟩)
    change elabRepresentation p φ a (Additive.ofMul x) = Additive.ofMul x at this
    rw [elabRepresentation_apply] at this
    exact Additive.ofMul.injective this
  · intro h x
    refine Subtype.ext ?_
    have hx : Additive.toMul (x : Additive K) ∈ J :=
      (mem_symm_elabSubmoduleSubgroupEquiv (p := p) J (x : Additive K)).mp x.2
    change elabRepresentation p φ a (x : Additive K) = (x : Additive K)
    have := h _ hx
    change (φ a) (Additive.toMul (x : Additive K)) = Additive.toMul (x : Additive K) at this
    exact congrArg Additive.ofMul this

end OddOrder.GroupTheory
