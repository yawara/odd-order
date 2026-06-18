/-
Copyright (c) 2026 OddOrder contributors. All rights reserved.
-/
import OddOrder.BG.Ch1_Preliminary.S01_Solvable

/-!
# Invariant Schur–Zassenhaus (complement form)

A normal Hall subgroup `N` of a finite solvable group `G`, invariant under a coprime operator
action `φ : A →* MulAut G`, admits a `φ`-invariant complement.

This is the "invariant complement" half of Schur–Zassenhaus.  Mathlib supplies the plain version
(`Subgroup.exists_right_complement'_of_coprime`); the *invariant* refinement is exactly Peterfalvi's
"remark following Definition (8.4)" used in (13.1.b) to choose `U` so that `W₁` normalizes it.  We
obtain it for free from BG Proposition 1.5(b)
(`OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall`): the trivial subgroup is a
`φ`-invariant `π'`-subgroup (`π = π(|N|)`), hence is contained in a `φ`-invariant Hall
`π'`-subgroup `U`; coprimality of the `π`- and `π'`-parts makes `U` a complement of the Hall
`π`-subgroup `N`.
-/

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]

/-- **Invariant Schur–Zassenhaus, complement form.**  A `φ`-invariant normal Hall subgroup `N` of a
finite solvable group has a `φ`-invariant complement `U`, provided the action is coprime to `|G|`. -/
theorem exists_aInvariant_complement_of_normal_isHall [IsSolvable G] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    {N : Subgroup G} [N.Normal] (hN_inv : IsAInvariant φ N)
    (hN_hall : IsHallSubgroup (Nat.card ↥N).primeFactors N) :
    ∃ U : Subgroup G, Subgroup.IsComplement' N U ∧ IsAInvariant φ U := by
  classical
  set π : Set ℕ := ((Nat.card ↥N).primeFactors : Set ℕ) with hπ
  -- A `φ`-invariant Hall `π'`-subgroup `U`, from the trivial `π'`-subgroup `⊥ ≤ U`.
  obtain ⟨U, hU_hall, hU_inv, -⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall (π := {p | p ∉ π}) hCop
      (Subgroup.IsPiGroup.bot {p | p ∉ π}) (IsAInvariant.bot φ)
  refine ⟨U, ?_, hU_inv⟩
  -- `|N|` (a `π`-number) and `|U|` (a `π'`-number) are coprime.
  have hcop_NU : Nat.Coprime (Nat.card ↥N) (Nat.card ↥U) := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpU
    exact hU_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpU, Nat.card_pos.ne'⟩)
      (hN_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpN, Nat.card_pos.ne'⟩))
  -- `[G : N]` (a `π'`-number) and `[G : U]` (a `π`-number) are coprime.
  have hcop_idx : Nat.Coprime N.index U.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpU
    have hpπ' : p ∉ π :=
      hN_hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpN, Subgroup.index_ne_zero_of_finite⟩)
    have hpπ : p ∈ π := by
      by_contra hpπ
      exact hU_hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpU, Subgroup.index_ne_zero_of_finite⟩) hpπ
    exact hpπ' hpπ
  -- `|U| = [G : N]`: both equal the `π'`-part of `|G|`.
  have hU_eq_index : Nat.card ↥U = N.index := by
    refine Nat.dvd_antisymm ?_ ?_
    · -- `|U| ∣ |N|·[G:N] = |G|`, coprime to `|N|`, so `|U| ∣ [G:N]`.
      refine (Nat.Coprime.dvd_of_dvd_mul_left hcop_NU.symm ?_)
      rw [Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card U
    · -- `[G:N] ∣ |U|·[G:U] = |G|`, coprime to `[G:U]`, so `[G:N] ∣ |U|`.
      refine (Nat.Coprime.dvd_of_dvd_mul_right hcop_idx ?_)
      rw [Subgroup.card_mul_index]
      exact Subgroup.index_dvd_card N
  -- Hence `|N|·|U| = |G|`, and with coprimality `U` is a complement of `N`.
  refine Subgroup.isComplement'_of_coprime ?_ hcop_NU
  rw [hU_eq_index, Subgroup.card_mul_index]

end OddOrder.GroupTheory
