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

It also records the order consequence used to see that a central extension is
*trivial at `p`*: if a group and one of its quotients have Sylow `p`-subgroups
of the same order, then `p` does not divide the order of the kernel
(`Sylow.not_dvd_natCard_of_natCard_eq`).
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

/-! ## A Sylow-order criterion for the kernel of a quotient -/

/-- If a finite group `G` and its quotient by a normal subgroup `N` have Sylow
`p`-subgroups of the same order, then `p` does not divide `|N|`.

`|G| = |S| · [G : S]` and `|G/N| = |T| · [G/N : T]` with both indices prime to
`p`; combined with `|G| = |N| · |G/N|` and `|S| = |T|` this makes `|N|` a
divisor of `[G : S]`. -/
theorem not_dvd_natCard_of_natCard_eq [Fact p.Prime] [Finite G]
    {N : Subgroup G} [N.Normal] (S : Sylow p G) (T : Sylow p (G ⧸ N))
    (hcard : Nat.card ↥(S : Subgroup G) = Nat.card ↥(T : Subgroup (G ⧸ N))) :
    ¬ p ∣ Nat.card ↥N := by
  classical
  have hG : Nat.card ↥(S : Subgroup G) * (S : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hQ : Nat.card ↥(T : Subgroup (G ⧸ N)) * (T : Subgroup (G ⧸ N)).index =
      Nat.card (G ⧸ N) := Subgroup.card_mul_index _
  have hlag : Nat.card ↥N * Nat.card (G ⧸ N) = Nat.card G := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.card_mul_index N
  have hpos : 0 < Nat.card ↥(S : Subgroup G) := Nat.card_pos
  -- `[G : S] = |N| * [G/N : T]`
  have hindex : (S : Subgroup G).index =
      Nat.card ↥N * (T : Subgroup (G ⧸ N)).index := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card ↥(S : Subgroup G) * (S : Subgroup G).index
        = Nat.card G := hG
      _ = Nat.card ↥N * Nat.card (G ⧸ N) := hlag.symm
      _ = Nat.card ↥N *
            (Nat.card ↥(T : Subgroup (G ⧸ N)) * (T : Subgroup (G ⧸ N)).index) := by
            rw [hQ]
      _ = Nat.card ↥(S : Subgroup G) *
            (Nat.card ↥N * (T : Subgroup (G ⧸ N)).index) := by
            rw [hcard]; ring
  intro hdvd
  exact S.not_dvd_index (hindex ▸ hdvd.mul_right _)

end Sylow
