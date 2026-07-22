/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSix

/-!
# Peterfalvi Part II, Ch. II, step (7): `N = P`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (7), p. 110.

`N` is the kernel of the action of `L = C_G(P)` on the fixed points `Ω_P`,
defined in step (2)(a).  Step (7) proves `N = P` (and `Σ ≅ C_W(P)`).

This leaf begins with the *decomposition* `N = (N ∩ W) × P`, phrased as
`N = (N ∩ W) ⊔ P`.  It is a clean consequence of step (1):

* `P ≤ N`: `P` fixes `Ω_P` pointwise, and `P` centralizes `C_Q(P) = Q_L`, so
  `P` lands in the kernel `N = C_{D_L}(Q_L)`
  (`normalCore_cH_eq_centralizer_cQ`);
* `N ≤ V`: `N ≤ C_D(P) = C_W(P) · P ≤ W · P = V` (step (1)); and
* every `n ∈ N ⊆ V` factors as `n = g·w` with `g ∈ P` and `w ∈ W`
  (`exists_decomp_of_mem_V`); since `g ∈ P ≤ N`, also `w = g⁻¹ n ∈ N`.

The reduction `N ∩ W = 1 ⟹ N = P` is then immediate.  The hard direction,
`N ∩ W = 1`, is the centralizer-trichotomy contradiction, handled separately.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- The kernel `N` of the action of `L = C_G(P)` on the fixed points `Ω_P`,
realized as a subgroup of `G` (the book's `N`, defined in step (2)(a)).  It is
`(H ∩ L).normalCore`, the kernel of `L → Sym(Ω_P)`, pushed forward along
`L ↪ G`. -/
noncomputable def kernelN : Subgroup G :=
  ((fc.toHypothesis.H.subgroupOf
      (Subgroup.centralizer (fc.P : Set G))).normalCore).map
    (Subgroup.centralizer (fc.P : Set G)).subtype

/-- `N ≤ C_G(P)`: the kernel consists of elements of `L = C_G(P)`. -/
theorem kernelN_le_centralizer :
    fc.kernelN ≤ Subgroup.centralizer (fc.P : Set G) := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- `N ≤ D`: the kernel lands in `D_L = C_D(P)`
(`normalCore_cH_eq_centralizer_cQ`). -/
theorem kernelN_le_D : fc.kernelN ≤ fc.toHypothesis.D := by
  rintro x ⟨y, hy, rfl⟩
  have hyD : y ∈ fc.toHypothesis.D.subgroupOf
      (Subgroup.centralizer (fc.P : Set G)) := by
    have hy' : y ∈ (fc.toHypothesis.D.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))) ⊓
        Subgroup.centralizer
          ((fc.toHypothesis.Q.subgroupOf
            (Subgroup.centralizer (fc.P : Set G))) :
            Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
      rw [← fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact hy
    exact hy'.1
  exact Subgroup.mem_subgroupOf.mp hyD

/-- `N` centralizes `C_Q(P) = Q_L`: the kernel is `C_{D_L}(Q_L)`. -/
theorem kernelN_le_centralizer_cQ :
    fc.kernelN ≤ Subgroup.centralizer
      ((fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G) : Subgroup G) :
        Set G) := by
  rintro x ⟨y, hy, rfl⟩
  have hyC : y ∈ Subgroup.centralizer
      ((fc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (fc.P : Set G))) :
        Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
    have hy' : y ∈ (fc.toHypothesis.D.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))) ⊓
        Subgroup.centralizer
          ((fc.toHypothesis.Q.subgroupOf
            (Subgroup.centralizer (fc.P : Set G))) :
            Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
      rw [← fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact hy
    exact hy'.2
  rw [Subgroup.mem_centralizer_iff]
  rintro z ⟨hzQ, hzC⟩
  -- `z ∈ C_G(P)`, so `z ∈ L`, and `z ∈ Q`; apply `hyC` to `z` viewed in `L`
  have hzL : z ∈ Subgroup.centralizer (fc.P : Set G) := hzC
  have hzQL : (⟨z, hzL⟩ : ↥(Subgroup.centralizer (fc.P : Set G))) ∈
      fc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (fc.P : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hzQ
  have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hzQL
  exact congrArg Subtype.val hcomm

/-- **Step (7): `P ≤ N`** (p. 110).  `P` centralizes itself, so `P ≤ L`; and
in `L`, `P` lands in `C_{D_L}(Q_L) = N`: `P ≤ D`, and every element of
`Q_L = C_Q(P)` centralizes `P`. -/
theorem P_le_kernelN : fc.P ≤ fc.kernelN := by
  have hPL : fc.P ≤ Subgroup.centralizer (fc.P : Set G) := fc.P_le_centralizer
  have hstep : fc.P.subgroupOf (Subgroup.centralizer (fc.P : Set G)) ≤
      (fc.toHypothesis.H.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))).normalCore := by
    rw [fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
    apply le_inf
    · exact Subgroup.comap_mono (fc.P_le_V.trans fc.toHypothesis.V_le_D)
    · intro p hp
      have hpP : (p : G) ∈ fc.P := Subgroup.mem_subgroupOf.mp hp
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hqL : (q : G) ∈ Subgroup.centralizer (fc.P : Set G) := q.2
      have hcomm := Subgroup.mem_centralizer_iff.mp hqL (p : G) hpP
      exact hcomm.symm
  calc fc.P = (fc.P.subgroupOf (Subgroup.centralizer (fc.P : Set G))).map
        (Subgroup.centralizer (fc.P : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPL).symm
    _ ≤ fc.kernelN := Subgroup.map_mono hstep

/-- **Step (7): `N ≤ V`** (p. 110).  `N ≤ C_D(P) = C_W(P) · P ≤ W · P = V`. -/
theorem kernelN_le_V : fc.kernelN ≤ fc.toHypothesis.V := by
  have h1 : fc.kernelN ≤
      fc.toHypothesis.D ⊓ Subgroup.centralizer (fc.P : Set G) :=
    le_inf fc.kernelN_le_D fc.kernelN_le_centralizer
  calc fc.kernelN
      ≤ fc.toHypothesis.D ⊓ Subgroup.centralizer (fc.P : Set G) := h1
    _ = (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P :=
        fc.D_inf_centralizer_eq_W_inf_centralizer_join_P
    _ ≤ fc.toHypothesis.V :=
        sup_le (le_trans inf_le_left fc.toHypothesis.W_le_V) fc.P_le_V

/-- **Peterfalvi Part II, Ch. II, step (7), the decomposition** (p. 110):
`N = (N ∩ W) × P`, stated as `N = (N ∩ W) ⊔ P`.

`N ≤ V` splits every `n ∈ N` as `n = g·w` with `g ∈ P` and `w ∈ W`; since
`g ∈ P ≤ N`, the factor `w = g⁻¹ n ∈ N ∩ W`. -/
theorem kernelN_eq_kernelInf_W_join_P :
    fc.kernelN = (fc.kernelN ⊓ fc.toHypothesis.W) ⊔ fc.P := by
  apply le_antisymm
  · intro n hn
    obtain ⟨g, hgP, hgw⟩ := fc.exists_decomp_of_mem_V (fc.kernelN_le_V hn)
    have hgN : g ∈ fc.kernelN := fc.P_le_kernelN hgP
    have hmem : g⁻¹ * n ∈ fc.kernelN ⊓ fc.toHypothesis.W :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hn, hgw⟩
    have hdecomp : n = g * (g⁻¹ * n) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgP)
      (Subgroup.mem_sup_left hmem)
  · exact sup_le inf_le_left fc.P_le_kernelN

/-- **Step (7), the reduction** (p. 110): `N ∩ W = 1 ⟹ N = P`.  Immediate from
the decomposition `N = (N ∩ W) × P`. -/
theorem kernelN_eq_P_of_kernelInf_W_eq_bot
    (h : fc.kernelN ⊓ fc.toHypothesis.W = ⊥) : fc.kernelN = fc.P := by
  have hd := fc.kernelN_eq_kernelInf_W_join_P
  rw [h, bot_sup_eq] at hd
  exact hd

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
