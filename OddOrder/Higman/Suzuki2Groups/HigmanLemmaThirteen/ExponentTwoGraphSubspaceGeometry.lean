/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Higman's Lemma 13: graph-subspace geometry

The graph of a nonzero coefficient pair across two disjoint linear axes is a
nonzero proper subspace of their sum.  It stays disjoint from every subspace
disjoint from that sum, and cannot generate the ambient space together with
such a subspace.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

universe uV

/-- A nontrivial diagonal across two disjoint field-coordinate axes is a
nonzero proper subspace of their sum.  Any subspace disjoint from the axis sum
is also disjoint from the diagonal and does not complement it to the top.
Thus the usual additional hypothesis that the axis sum and `W` generate the
top is not needed for these conclusions. -/
theorem graphSubspace_geometry
    {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module (ZMod 2) V]
    (iX iY : GaloisField 2 n →ₗ[ZMod 2] V)
    (hiX : Function.Injective iX)
    (hiY : Function.Injective iY)
    (hXY :
      LinearMap.range iX ⊓ LinearMap.range iY = ⊥)
    (a b : GaloisField 2 n)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (d : GaloisField 2 n →ₗ[ZMod 2] V)
    (hd : ∀ α, d α = iX (a * α) + iY (b * α))
    (W : Submodule (ZMod 2) V)
    (hXYW :
      (LinearMap.range iX ⊔ LinearMap.range iY) ⊓ W = ⊥) :
    Function.Injective d ∧
      LinearMap.range d ≠ ⊥ ∧
      LinearMap.range d <
        LinearMap.range iX ⊔ LinearMap.range iY ∧
      LinearMap.range d ⊓ W = ⊥ ∧
      LinearMap.range d ⊔ W ≠ ⊤ := by
  have hdInj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    rw [hd α] at hα
    have hXaMem :
        iX (a * α) ∈
          LinearMap.range iX ⊓ LinearMap.range iY := by
      constructor
      · exact ⟨a * α, rfl⟩
      · refine ⟨-(b * α), ?_⟩
        rw [map_neg]
        exact (eq_neg_of_add_eq_zero_left hα).symm
    have hXaZero : iX (a * α) = 0 := by
      rw [hXY] at hXaMem
      simpa only [Submodule.mem_bot] using hXaMem
    have hYbZero : iY (b * α) = 0 := by
      rw [hXaZero, zero_add] at hα
      exact hα
    have haα : a * α = 0 :=
      hiX (by simpa only [map_zero] using hXaZero)
    have hbα : b * α = 0 :=
      hiY (by simpa only [map_zero] using hYbZero)
    rcases hab with ha | hb
    · exact (mul_eq_zero.mp haα).resolve_left ha
    · exact (mul_eq_zero.mp hbα).resolve_left hb
  have hDneBot : LinearMap.range d ≠
      (⊥ : Submodule (ZMod 2) V) := by
    intro hD
    have hd0 : d = 0 := LinearMap.range_eq_bot.mp hD
    have hOneZero : (1 : GaloisField 2 n) = 0 := by
      apply hdInj
      rw [hd0]
      rfl
    exact one_ne_zero hOneZero
  have hDle :
      LinearMap.range d ≤
        LinearMap.range iX ⊔ LinearMap.range iY := by
    rintro _ ⟨α, rfl⟩
    rw [hd α]
    exact add_mem
      ((show LinearMap.range iX ≤
          LinearMap.range iX ⊔ LinearMap.range iY from le_sup_left)
        (show iX (a * α) ∈ LinearMap.range iX from ⟨a * α, rfl⟩))
      ((show LinearMap.range iY ≤
          LinearMap.range iX ⊔ LinearMap.range iY from le_sup_right)
        (show iY (b * α) ∈ LinearMap.range iY from ⟨b * α, rfl⟩))
  have hDne :
      LinearMap.range d ≠
        LinearMap.range iX ⊔ LinearMap.range iY := by
    intro hDeq
    by_cases ha : a = 0
    · have hDleY : LinearMap.range d ≤ LinearMap.range iY := by
        rintro _ ⟨α, rfl⟩
        refine ⟨b * α, ?_⟩
        rw [hd α, ha, zero_mul, map_zero, zero_add]
      have hBleY :
          LinearMap.range iX ⊔ LinearMap.range iY ≤
            LinearMap.range iY := by
        rw [← hDeq]
        exact hDleY
      have hiXOneMem :
          iX 1 ∈ LinearMap.range iX ⊓ LinearMap.range iY := by
        constructor
        · exact ⟨1, rfl⟩
        · exact hBleY
            ((show LinearMap.range iX ≤
                LinearMap.range iX ⊔ LinearMap.range iY from le_sup_left)
              (show iX 1 ∈ LinearMap.range iX from ⟨1, rfl⟩))
      have hiXOneZero : iX 1 = 0 := by
        rw [hXY] at hiXOneMem
        simpa only [Submodule.mem_bot] using hiXOneMem
      have hOneZero : (1 : GaloisField 2 n) = 0 :=
        hiX (by simpa only [map_zero] using hiXOneZero)
      exact one_ne_zero hOneZero
    · have hiYOneB :
          iY 1 ∈ LinearMap.range iX ⊔ LinearMap.range iY :=
        (show LinearMap.range iY ≤
            LinearMap.range iX ⊔ LinearMap.range iY from le_sup_right)
          (show iY 1 ∈ LinearMap.range iY from ⟨1, rfl⟩)
      have hiYOneD : iY 1 ∈ LinearMap.range d := by
        rw [hDeq]
        exact hiYOneB
      obtain ⟨α, hα⟩ := hiYOneD
      rw [hd α] at hα
      have hXaMem :
          iX (a * α) ∈
            LinearMap.range iX ⊓ LinearMap.range iY := by
        constructor
        · exact ⟨a * α, rfl⟩
        · refine ⟨1 - b * α, ?_⟩
          rw [map_sub]
          exact (eq_sub_of_add_eq hα).symm
      have hXaZero : iX (a * α) = 0 := by
        rw [hXY] at hXaMem
        simpa only [Submodule.mem_bot] using hXaMem
      have haα : a * α = 0 :=
        hiX (by simpa only [map_zero] using hXaZero)
      have hαZero : α = 0 :=
        (mul_eq_zero.mp haα).resolve_left ha
      subst α
      have hiYOneZero : iY 1 = 0 := by
        simpa only [mul_zero, map_zero, add_zero] using hα.symm
      have hOneZero : (1 : GaloisField 2 n) = 0 :=
        hiY (by simpa only [map_zero] using hiYOneZero)
      exact one_ne_zero hOneZero
  have hDlt :
      LinearMap.range d <
        LinearMap.range iX ⊔ LinearMap.range iY :=
    lt_of_le_of_ne hDle hDne
  have hDWbot : LinearMap.range d ⊓ W =
      (⊥ : Submodule (ZMod 2) V) := by
    apply le_bot_iff.mp
    exact (inf_le_inf_right W hDle).trans (le_of_eq hXYW)
  have hDWtop : LinearMap.range d ⊔ W ≠
      (⊤ : Submodule (ZMod 2) V) := by
    intro htop
    have hWDtop : W ⊔ LinearMap.range d =
        (⊤ : Submodule (ZMod 2) V) := by
      simpa [sup_comm] using htop
    have hBD :
        LinearMap.range iX ⊔ LinearMap.range iY =
          LinearMap.range d := by
      have hmod :
          (LinearMap.range iX ⊔ LinearMap.range iY) ⊓
              (W ⊔ LinearMap.range d) =
            LinearMap.range d := by
        rw [← inf_sup_assoc_of_le W hDle, hXYW, bot_sup_eq]
      rwa [hWDtop, inf_top_eq] at hmod
    exact hDne hBD.symm
  exact ⟨hdInj, hDneBot, hDlt, hDWbot, hDWtop⟩

end OddOrder.Higman.Suzuki2Groups
