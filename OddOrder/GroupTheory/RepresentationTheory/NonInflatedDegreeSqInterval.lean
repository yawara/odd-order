/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter

/-!
# The kernel-interval degree-square sum `∑_{N ≤ ker χ, K ⊄ ker χ} χ(1)² = |G/N| − |G/K|`

For a nested pair of normal subgroups `N ≤ K` of a finite group `G`, the squared degrees of the
irreducible characters of `G` whose kernel contains `N` but **not** `K` sum to `|G/N| − |G/K|`.

This is the two-condition refinement of `sumNonInflatedDegreeSq`
(`∑_{N ⊄ ker χ} χ(1)² = |G| − |G/N|`, the one-condition `N ⊄ ker` version): those characters with
`N ≤ ker` are the inflations of `Irr(G/N)` (`inflate`), and among them the `K ⊄ ker` condition
transfers to `K̄ = K/N ⊄ ker` in `G/N`, where `sumNonInflatedDegreeSq` applies and
`|(G/N)/K̄| = |G/K|` by the third isomorphism theorem.

Peterfalvi (9.11.3) consumes this for the quotient `HŪ/(H₀C)`: with `N = H₀C` and `K = H`, the sum
`∑_{χ ∈ 𝒳(H₀C)} χ(1)²` over the source family `𝒳(H₀C)` (characters with `H₀C ≤ ker`, `H ⊄ ker`)
equals `|HU/(H₀C)| − |HU/H| = p^q·u − u = u(p^q − 1)`, the character sum-of-squares of the (9.11.3)
class equation.
-/

namespace OddOrder.RepresentationTheory

open scoped Classical

variable {G : Type*} [Group G]

/-- **The `K`-kernel condition transfers through inflation.**  For a character `χbar` of `G ⧸ N` and
a subgroup `K` with `N ≤ K`, the kernel of `inflate N χbar` contains `K` iff the kernel
of `χbar` contains the image `K̄ = K.map (mk' N)`: `inflate N χbar = χbar ∘ mk' N`, so
`(inflate χbar)(k) = χbar(k̄)` and the kernel membership `k ∈ ker(inflate χbar)` reads off as
`k̄ ∈ ker χbar`. -/
theorem subset_characterKernel_inflate_iff (N : Subgroup G) [N.Normal]
    (K : Subgroup G) (χbar : IrreducibleCharacter (G ⧸ N)) :
    (K : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ)
      ↔ ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χbar : ClassFunction (G ⧸ N) ℂ) := by
  constructor
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkker := h hk
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, inflate_apply, inflate_apply_one] at hkker
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
    exact hkker
  · intro h k hk
    have hmem : (QuotientGroup.mk' N k) ∈ (K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :=
      Subgroup.mem_map_of_mem _ hk
    have hkker := h hmem
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hkker
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, inflate_apply, inflate_apply_one]
    exact hkker

variable [Finite G]

/-- **The kernel-interval degree-square sum** `∑_{N ≤ ker, K ⊄ ker} χ(1)² = |G/N| − |G/(K ⊔ N)|`.

For normal subgroups `N`, `K` of a finite group, the irreducibles of `G` with `N` in their kernel
but not `K`.  Via the inflation bijection `Irr(G/N) ≃ {χ ∈ Irr G | N ≤ ker χ}` (degree preserving),
the `K ⊄ ker` condition transfers to `K̄ = K.map(mk' N) ⊄ ker` in `G/N`, so the sum equals
`∑_{K̄ ⊄ ker χ̄} χ̄(1)² = |G/N| − |(G/N)/K̄| = |G/N| − |G/(K ⊔ N)|` (`sumNonInflatedDegreeSq` in
`G/N`, plus the third isomorphism theorem `(G/N)/((K ⊔ N)/N) ≅ G/(K ⊔ N)`, using
`K.map(mk' N) = (K ⊔ N).map(mk' N)` as `N` maps to `⊥`).  No `N ≤ K` hypothesis — when `N ≤ K` this
specializes to `|G/N| − |G/K|`; the `N ⊄ K` case (Peterfalvi (9.11.3): `N = H₀C`, `K = H`,
`K ⊔ N = HC`) gives `|G/N| − |G/HC|`. -/
theorem sumDegreeSq_kernelInterval (N K : Subgroup G) [N.Normal] [K.Normal] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) ∧
        ¬ (K : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) ^ 2
      = (Nat.card (G ⧸ N) : ℂ) - (Nat.card (G ⧸ (K ⊔ N)) : ℂ) := by
  classical
  set Kbar : Subgroup (G ⧸ N) := K.map (QuotientGroup.mk' N) with hKbar
  -- Transfer the sum to `G ⧸ N` via the inflation bijection, carrying the `K ⊄ ker` condition.
  have htransfer : ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) ∧
        ¬ (K : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) ^ 2
      = ∑ χbar ∈ Finset.univ.filter (fun χbar : IrreducibleCharacter (G ⧸ N) =>
          ¬ (Kbar : Set (G ⧸ N)) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (χbar : ClassFunction (G ⧸ N) ℂ)),
          ((χbar : ClassFunction (G ⧸ N) ℂ) 1) ^ 2 := by
    refine (Finset.sum_bij' (fun χbar _ => inflate N χbar)
      (fun χ hχ => (exists_inflate_eq_of_subset_characterKernel N χ
        ((Finset.mem_filter.mp hχ).2.1)).choose)
      ?_ ?_ ?_ ?_ ?_).symm
    · -- `inflate χbar` lands in the `G`-filter.
      intro χbar hχbar
      rw [Finset.mem_filter] at hχbar ⊢
      refine ⟨Finset.mem_univ _, subset_characterKernel_inflate N χbar, ?_⟩
      rw [subset_characterKernel_inflate_iff N K χbar, ← hKbar]
      exact hχbar.2
    · -- the chosen preimage lands in the `G ⧸ N`-filter.
      intro χ hχ
      rw [Finset.mem_filter] at hχ ⊢
      have hspec := (exists_inflate_eq_of_subset_characterKernel N χ hχ.2.1).choose_spec
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← subset_characterKernel_inflate_iff N K, hspec]
      exact hχ.2.2
    · -- left inverse
      intro χbar hχbar
      apply inflate_injective N
      exact (exists_inflate_eq_of_subset_characterKernel N (inflate N χbar)
        (subset_characterKernel_inflate N χbar)).choose_spec
    · -- right inverse
      intro χ hχ
      exact (exists_inflate_eq_of_subset_characterKernel N χ
        ((Finset.mem_filter.mp hχ).2.1)).choose_spec
    · -- degree agreement
      intro χbar _
      rw [inflate_apply_one]
  rw [htransfer]
  -- `sumNonInflatedDegreeSq` in `G ⧸ N` with `N := Kbar`.
  haveI : Kbar.Normal := hKbar ▸ Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  rw [sumNonInflatedDegreeSq (G := G ⧸ N) (N := Kbar)]
  -- `|(G ⧸ N) ⧸ Kbar| = |G ⧸ (K ⊔ N)|` by the third isomorphism theorem (`Kbar = (K ⊔ N).map`).
  congr 1
  have hKbar_eq : Kbar = (K ⊔ N).map (QuotientGroup.mk' N) := by
    rw [hKbar, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rw [hKbar_eq]
  exact_mod_cast Nat.card_congr
    (QuotientGroup.quotientQuotientEquivQuotient N (K ⊔ N) le_sup_right).toEquiv

end OddOrder.RepresentationTheory
