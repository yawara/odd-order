/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Nilpotent groups with cyclic abelianization are abelian

The standard fact `G` nilpotent and `G/G'` cyclic ⟹ `G` abelian, in the lower-central-series
form: `G' ≤ ⁅G', G⁆` (from the cyclic quotient via mathlib's
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` applied to
`G ⧸ ⁅G', ⊤⁆ →* G ⧸ G'`), so the lower central series stabilizes at `G'` and nilpotency
forces `G' = ⊥`.

Used by the Peterfalvi (13.2.a)-at-`T` caseB analysis (issue 2035): in the Singer/Galois
Clifford case the complement `V` is nilpotent with `V/V'` cyclic, hence abelian.
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {H : Type*} [Group H]

/-- **A nilpotent group with cyclic abelianization is abelian** (commutator form):
if `H` is nilpotent and `H/H'` is cyclic then `H' = ⊥`.

The quotient `H ⧸ ⁅H', ⊤⁆` has central kernel image `H'/⁅H', ⊤⁆` over the cyclic `H/H'`,
so it is abelian (`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`), giving
`H' ≤ ⁅H', ⊤⁆`; the lower central series then stabilizes at `H' = γ₁` and nilpotency
forces `H' = ⊥`. -/
theorem commutator_eq_bot_of_isCyclic_quotient [Group.IsNilpotent H]
    (hcyc : IsCyclic (H ⧸ commutator H)) : commutator H = ⊥ := by
  classical
  set N : Subgroup H := ⁅commutator H, (⊤ : Subgroup H)⁆ with hN
  haveI : N.Normal := Subgroup.commutator_normal _ _
  have hNle : N ≤ commutator H := by
    rw [hN]
    exact Subgroup.commutator_le_left _ _
  have hlift : ∀ x ∈ N, QuotientGroup.mk' (commutator H) x = 1 := fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr (hNle hx)
  set f : H ⧸ N →* H ⧸ commutator H :=
    QuotientGroup.lift N (QuotientGroup.mk' (commutator H)) hlift with hf
  -- the kernel of `f` is central in `H ⧸ N`: a kernel element is `mk x` with `x ∈ H'`, and
  -- `⁅x, y⁆ ∈ ⁅H', ⊤⁆ = N` for every `y`.
  have hker : f.ker ≤ Subgroup.center (H ⧸ N) := by
    intro a ha
    induction a using QuotientGroup.induction_on with
    | _ x =>
      rw [MonoidHom.mem_ker, hf, QuotientGroup.lift_mk'] at ha
      have hxG' : x ∈ commutator H := (QuotientGroup.eq_one_iff x).mp ha
      rw [Subgroup.mem_center_iff]
      intro b
      induction b using QuotientGroup.induction_on with
      | _ y =>
        have hcomm : ⁅x, y⁆ ∈ N :=
          hN ▸ Subgroup.commutator_mem_commutator hxG' (Subgroup.mem_top y)
        have h1 : (QuotientGroup.mk ⁅x, y⁆ : H ⧸ N) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hcomm
        rw [commutatorElement_def] at h1
        have h3 : ((QuotientGroup.mk x : H ⧸ N) * QuotientGroup.mk y *
            (QuotientGroup.mk x)⁻¹ * (QuotientGroup.mk y)⁻¹) = 1 := by
          simpa using h1
        calc (QuotientGroup.mk y : H ⧸ N) * QuotientGroup.mk x
            = ((QuotientGroup.mk x * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
                (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk y)) := by
              group
          _ = QuotientGroup.mk x * QuotientGroup.mk y := by rw [h3]; group
  -- `H ⧸ N` is abelian, so `H' ≤ N = ⁅H', ⊤⁆`.
  haveI : IsCyclic (H ⧸ commutator H) := hcyc
  have hcommQ : IsMulCommutative (H ⧸ N) :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hG'le : commutator H ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have h := hcommQ.is_comm.comm (QuotientGroup.mk g₁) (QuotientGroup.mk g₂)
    have h1 : (QuotientGroup.mk ⁅g₁, g₂⁆ : H ⧸ N) = 1 := by
      rw [commutatorElement_def]
      have h2 : (QuotientGroup.mk (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) : H ⧸ N)
          = QuotientGroup.mk g₁ * QuotientGroup.mk g₂ * (QuotientGroup.mk g₁)⁻¹ *
            (QuotientGroup.mk g₂)⁻¹ := by simp
      rw [h2, h]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  -- lower central series stabilization: `γ₁ = H'` and `γ₂ = ⁅H', ⊤⁆ = H'`, then nilpotency.
  have hstab : ∀ n : ℕ, 1 ≤ n →
      (⊤ : Subgroup H).lowerCentralSeries n = commutator H := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge m 1 with h1 | h1
      · have hm0 : m = 0 := by omega
        rw [hm0]
        exact Subgroup.top_lowerCentralSeries_one
      · rw [Subgroup.lowerCentralSeries_succ, ih h1, ← hN]
        exact le_antisymm hNle hG'le
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent H›
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `γ₀ = ⊤ = ⊥`: the group is trivial.
    rw [h0, Subgroup.lowerCentralSeries_zero] at hn
    rw [eq_bot_iff, ← hn]
    exact le_top
  · rw [← hstab n hpos]
    exact hn

/-- **A nilpotent group with cyclic abelianization is abelian** (`IsMulCommutative` form). -/
theorem isMulCommutative_of_isNilpotent_of_isCyclic_quotient [Group.IsNilpotent H]
    (hcyc : IsCyclic (H ⧸ commutator H)) : IsMulCommutative H := by
  have hbot := commutator_eq_bot_of_isCyclic_quotient hcyc
  refine ⟨⟨fun a b => ?_⟩⟩
  have hmem : ⁅a, b⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hmem]; group

end OddOrder.GroupTheory
