/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainHypothesis46
import OddOrder.Peterfalvi.S03b_Vanishing

/-!
# Peterfalvi (4.7), core support lemma: `H ⊄ Ker χ` characters live on `A ∪ {1}`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, pp. 21-24, statement (4.7).

This file records the heart of Theorem (4.7): under Hypothesis (4.6), an irreducible
character `χ` of `K` with `H ⊄ Ker χ` is supported on `A ∪ {1}`.  Concretely, every
nonidentity element `g ∈ K` with `χ(g) ≠ 0` maps into `A`.

## Proof (Peterfalvi (4.7), first sentence)

Apply (1.2) inside the group `K` to the normal subgroup `H ⊴ K` and `χ ∈ Irr(K)`.
Since `χ(g) ≠ 0`, the contrapositive of (1.2) gives `C_H(g) ≠ 1`, so `g` centralizes
some `h ∈ H^#`; equivalently `g ∈ C_K(h)^#`.  The covering condition (4.6.d)
`⋃_{h∈H^#} C_K(h)^# ⊆ A` then puts (the ambient image of) `g` in `A`.

The induced-character half (`Supp Ind_K^L χ ⊆ A ∪ {1}`) and the `χ_j` (`j ≥ 1`) half
of (4.7) build on this core statement and are developed separately.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi (4.7)**, core support statement.  Under Hypothesis (4.6), if
`χ ∈ Irr(K)` satisfies `H ⊄ Ker χ`, then every nonidentity `g ∈ K` with `χ(g) ≠ 0`
maps into `A` (i.e. `Supp χ ⊆ A ∪ {1}`).

The hypothesis `H ⊄ Ker χ` is phrased at the class-function level as
`¬ (H ⊆ characterKernel χ)`, matching Peterfalvi (1.2). -/
theorem mem_A_of_apply_ne_zero_of_not_subset_characterKernel
    (h : Hypothesis46 A L)
    (χ : IrreducibleCharacter ↥h.K)
    (hker : ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (χ : ClassFunction ↥h.K ℂ)))
    {g : ↥h.K}
    (hg1 : L.subtype (h.K.subtype g) ≠ 1)
    (hval : (χ : ClassFunction ↥h.K ℂ) g ≠ 0) :
    L.subtype (h.K.subtype g) ∈ A := by
  classical
  -- `H` is normal in `K` (a normal subgroup of `L` contained in `K`).
  haveI hHK_normal : (h.subH.subgroupOf h.K).Normal := h.subH_normal.subgroupOf h.K
  -- (1.2) contrapositive: `χ(g) ≠ 0 ⟹ C_H(g) ≠ 1`.
  have hCne : S03.centralizerInSubgroup (h.subH.subgroupOf h.K) g ≠ ⊥ := fun hbot =>
    hval (S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot χ hker hbot)
  -- extract a nontrivial `c ∈ H ∩ C_K(g)`.
  obtain ⟨c, hc_mem, hc_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
  rw [S03.mem_centralizerInSubgroup] at hc_mem
  obtain ⟨hc_H, hc_comm⟩ := hc_mem
  -- the images of `c` and `g` in `L`.
  set cL : ↥L := h.K.subtype c with hcL
  set gL : ↥L := h.K.subtype g with hgL
  have hcL_subH : cL ∈ h.subH := (Subgroup.mem_subgroupOf).mp hc_H
  have hcL_ne : cL ≠ 1 := fun he =>
    hc_ne (h.K.subtype_injective (he.trans (map_one h.K.subtype).symm))
  have hgL_K : gL ∈ h.K := g.2
  have hgL_ne : gL ≠ 1 := fun he => hg1 (by rw [he]; exact map_one L.subtype)
  -- `cL` and `gL` commute (image under the monoid hom `K.subtype` of `c * g = g * c`).
  have hcomm : cL * gL = gL * cL := by
    have := congrArg h.K.subtype hc_comm
    rwa [map_mul, map_mul] at this
  -- apply the covering condition (4.6.d).
  refine h.A_covers cL hcL_subH hcL_ne gL ?_ hgL_ne
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm, hgL_K⟩

/-- **Peterfalvi (4.7)**, support form (`Supp χ ⊆ A ∪ {1}`).  Under Hypothesis (4.6),
an irreducible character `χ` of `K` with `H ⊄ Ker χ` vanishes at every `g ∈ K` whose
ambient image lies outside `A ∪ {1}`.

This is the contrapositive of `mem_A_of_apply_ne_zero_of_not_subset_characterKernel`,
phrased for downstream consumers (the induced-support half of (4.7) and (4.8)). -/
theorem apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
    (h : Hypothesis46 A L)
    (χ : IrreducibleCharacter ↥h.K)
    (hker : ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (χ : ClassFunction ↥h.K ℂ)))
    {g : ↥h.K}
    (hgA : L.subtype (h.K.subtype g) ∉ A ∪ ({1} : Set G)) :
    (χ : ClassFunction ↥h.K ℂ) g = 0 := by
  by_contra hval
  rw [Set.mem_union, Set.mem_singleton_iff, not_or] at hgA
  exact hgA.1
    (mem_A_of_apply_ne_zero_of_not_subset_characterKernel h χ hker hgA.2 hval)

end OddOrder.Peterfalvi.S06
