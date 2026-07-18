/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Basic

/-!
# Peterfalvi Appendix III: central involutions

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Higman theorem (a), p. 141; Graham Higman,
*Suzuki 2-groups*, Illinois J. Math. 7 (1963), p. 79.

Higman's introductory observation is that the involutions of a Suzuki
`2`-group are central: a finite `2`-group has a central involution, the actor
preserves the characteristic center, and transitivity carries that one
involution to every other one.  Consequently the involutions together with
the identity form a central elementary-abelian subgroup.

This is only the easy inclusion in theorem (a).  The reverse assertion that
every nonidentity central element is an involution, hence that this subgroup
is the whole center, belongs to Higman's later structural argument and is not
claimed here.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory

variable {P : Type*} [Group P]

/-- **Peterfalvi Appendix III, Higman theorem (a), easy inclusion** (p. 141):
every involution of a finite Suzuki `2`-group lies in its center.

This is Higman's “evidently” observation on p. 79: start from one central
involution and use transitivity of the defining actor on all involutions. -/
theorem involutions_subset_center [Finite P] (hP : IsSuzuki2Group P) :
    involutions P ⊆ (Subgroup.center P : Set P) := by
  rcases hP with ⟨hP2, _, ⟨u, v, hu, hv, huv⟩, A, _, hreg⟩
  letI : Nontrivial P := ⟨⟨u, v, huv⟩⟩
  letI : Nontrivial ↥(Subgroup.center P) := hP2.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center P) :=
    hP2.to_subgroup (Subgroup.center P)
  have hZcard_ne : Nat.card ↥(Subgroup.center P) ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo_dvd : 2 ∣ Nat.card ↥(Subgroup.center P) :=
    hZ2.card_eq_or_dvd.resolve_left hZcard_ne
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center P)) 2 htwo_dvd
  have hz := orderOf_eq_prime_iff.mp hzorder
  have hzpow : ((z : P) ^ 2) = 1 := congrArg Subtype.val hz.1
  have hzne : (z : P) ≠ 1 := fun h => hz.2 (Subtype.ext h)
  have hzInv : (z : P) ∈ involutions P := ⟨hzpow, hzne⟩
  intro x hx
  obtain ⟨a, ha, _⟩ := hreg (z : P) hzInv x hx
  rw [← ha]
  exact MulEquivClass.apply_mem_center (a : MulAut P) z.2

/-- The central exponent-`2` subgroup: the identity together with all central
involutions. -/
def involutionSubgroup (P : Type*) [Group P] : Subgroup P :=
  omega1OfAbelian P (Subgroup.center P) 2 fun _ hx y _ =>
    (Subgroup.mem_center_iff.mp hx y).symm

/-- The identity together with the central involutions forms an elementary
abelian `2`-subgroup. -/
theorem involutionSubgroup_isElementaryAbelian :
    (involutionSubgroup P).IsElementaryAbelian 2 :=
  omega1OfAbelian_isElementaryAbelian

/-- In a finite Suzuki `2`-group, membership in `involutionSubgroup` is
equivalent to having square one.  The nonidentity case uses
`involutions_subset_center`. -/
theorem mem_involutionSubgroup_iff_sq_eq_one [Finite P]
    (hP : IsSuzuki2Group P) {x : P} :
    x ∈ involutionSubgroup P ↔ x ^ 2 = 1 := by
  rw [involutionSubgroup, mem_omega1OfAbelian]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact involutions_subset_center hP ⟨hx, hx1⟩

/-- For a finite Suzuki `2`-group, the nonidentity elements of
`involutionSubgroup` are exactly the involutions. -/
theorem involutions_eq_involutionSubgroup_diff_identity [Finite P]
    (hP : IsSuzuki2Group P) :
    involutions P = (involutionSubgroup P : Set P) \ {1} := by
  ext x
  simp [involutions, mem_involutionSubgroup_iff_sq_eq_one hP]

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
