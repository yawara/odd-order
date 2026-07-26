/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Subgroups of a finite cyclic group are determined by their order

In a finite cyclic group there is at most one subgroup of each order: a subgroup `B` is exactly
the `|B|`-torsion, because Lagrange puts `B` inside the torsion and `IsCyclic.card_pow_eq_one_le`
bounds the torsion by `|B|`.

Used by Peterfalvi (9.7)(a) (issue 0152): the block scalar characters `φ_i : Ū →* 𝔽_p^×` of the
`W₁`-conjugate blocks have images of equal order `a = |U : C_U(H₁)|`, and since `𝔽_p^×` is cyclic
that already forces the images to *coincide* -- which is what feeds the book's `|U| ∣ a^{q−1}`.
-/

namespace OddOrder.GroupTheory

open Finset

variable {A : Type*} [CommGroup A]

/-- Membership in the `n`-torsion subgroup, realised as the kernel of `x ↦ x ^ n`. -/
theorem mem_powMonoidHom_ker {n : ℕ} {x : A} :
    x ∈ (powMonoidHom n : A →* A).ker ↔ x ^ n = 1 := Iff.rfl

/-- A subgroup is contained in the torsion of its own order (Lagrange). -/
theorem le_powMonoidHom_ker_card (B : Subgroup A) :
    B ≤ (powMonoidHom (Nat.card B) : A →* A).ker := by
  intro x hx
  rw [mem_powMonoidHom_ker]
  have hord : orderOf (⟨x, hx⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
  have hx' : ((⟨x, hx⟩ : B) : A) ^ Nat.card B = 1 := by
    rw [← Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.mp hord, Subgroup.coe_one]
  simpa using hx'

/-- **In a finite cyclic group, a subgroup is its own torsion.**  Lagrange gives the inclusion, and
`IsCyclic.card_pow_eq_one_le` bounds the torsion by `|B|`, forcing equality. -/
theorem eq_powMonoidHom_ker_card [Finite A] [IsCyclic A] (B : Subgroup A) :
    B = (powMonoidHom (Nat.card B) : A →* A).ker := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hpos : 0 < Nat.card B := Nat.card_pos
  refine Subgroup.eq_of_le_of_card_ge (le_powMonoidHom_ker_card B) ?_
  have hle : #{a : A | a ^ Nat.card B = 1} ≤ Nat.card B :=
    IsCyclic.card_pow_eq_one_le hpos
  have hcard : Nat.card ((powMonoidHom (Nat.card B) : A →* A).ker) =
      #{a : A | a ^ Nat.card B = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    exact Finset.filter_congr fun x _ => by simp
  omega

/-- **Subgroups of a finite cyclic group are determined by their order.**  Two subgroups of the
same order coincide, since each is the torsion of that order. -/
theorem Subgroup.eq_of_card_eq_of_isCyclic [Finite A] [IsCyclic A] {B C : Subgroup A}
    (h : Nat.card B = Nat.card C) : B = C := by
  rw [eq_powMonoidHom_ker_card B, eq_powMonoidHom_ker_card C, h]

end OddOrder.GroupTheory
