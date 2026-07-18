/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# Multiplicative equivalences between Sylow subgroups

This file packages Sylow conjugacy and transport across a group equivalence as
explicit multiplicative equivalences between the subgroup carriers.  The API
is used to compare the root subgroup of an abstract rank-one action with the
chosen root subgroup in a concrete standard model.
-/

set_option autoImplicit false

namespace Sylow

open scoped Pointwise

universe u v

variable {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]

/-- Any two Sylow subgroups are multiplicatively equivalent whenever the set
of Sylow subgroups is finite. -/
noncomputable def mulEquiv (P Q : Sylow p G) [Fact p.Prime]
    [Finite (Sylow p G)] : P ≃* Q := by
  classical
  let g := Classical.choose (MulAction.exists_smul_eq G P Q)
  have hg : g • P = Q := Classical.choose_spec (MulAction.exists_smul_eq G P Q)
  have hsub : MulAut.conj g • (P : Subgroup G) = (Q : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul]
    exact congrArg Sylow.toSubgroup hg
  exact (Subgroup.equivSMul (MulAut.conj g) (P : Subgroup G)).trans
    (MulEquiv.subgroupCongr hsub)

/-- Transport a Sylow subgroup across a multiplicative equivalence. -/
noncomputable def mapEquiv (e : G ≃* H) (P : Sylow p G) : Sylow p H :=
  P.comapOfInjective e.symm.toMonoidHom e.symm.injective (by
    intro x hx
    exact ⟨e x, by simp⟩)

/-- The subgroup underlying `mapEquiv` is the forward image under the supplied
group equivalence. -/
theorem coe_mapEquiv (e : G ≃* H) (P : Sylow p G) :
    (mapEquiv e P : Subgroup H) = (P : Subgroup G).map e.toMonoidHom := by
  ext y
  change e.symm y ∈ P ↔ ∃ x ∈ P, e x = y
  constructor
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Transport between arbitrary Sylow subgroups across a group equivalence. -/
noncomputable def transportMulEquiv (e : G ≃* H) (P : Sylow p G)
    (Q : Sylow p H) [Fact p.Prime] [Finite (Sylow p H)] : P ≃* Q :=
  (e.subgroupMap P).trans <|
    (MulEquiv.subgroupCongr (coe_mapEquiv e P).symm).trans <|
      mulEquiv (mapEquiv e P) Q

end Sylow
