/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem
import OddOrder.Peterfalvi.Appendices.FeitSibleySsetCoherence
import OddOrder.Peterfalvi.Appendices.FeitSibleyInduction
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Peterfalvi Appendix IV: member images under the coherent extension

Peterfalvi Part II, Ch. III, Theorem C, step (9) (p. 116) reads:

> Let `𝒮 = {χ₁,…,χₙ}`, with `χᵢ(1) = aᵢ|D|` and `a₁ = 1`, and let
> `eᵢ ∈ ±Irr(G)` be such that `Ind_H^G(χᵢ − aᵢχ₁) = eᵢ − aᵢe₁` for `i ≥ 2`;
> the coherence of `𝒮` makes this possible.

This leaf provides the three ingredients in coherence-extension form
(`eᵢ := hcoh.extension χᵢ` for a coherence witness
`hcoh : IsCoherent hyp.tau hyp.Sset hyp.A` of the Feit–Sibley Theorem):

* `exists_anchor` — an anchor `χ₁ ∈ 𝒮` of degree exactly `d`, every `χ ∈ 𝒮`
  having degree `a·χ₁(1)` with `a ∈ ℕ`, `a ≥ 1` (the book's `χᵢ(1) = aᵢ|D|`,
  `a₁ = 1`);
* `extension_zsmul_irr` — `hcoh.extension χ ∈ ±Irr(G)` (the book's
  `eᵢ ∈ ±Irr(G)`): the extension is a norm-preserving map into `ℤ[Irr G]`;
* `induce_sub_nsmul_extension` — the displayed identity
  `Ind_H^G(χ − a·χ') = e_χ − a·e_{χ'}`: the difference is `A`-supported, where
  the extension agrees with `τ = Ind_H^G`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- **The anchor `χ₁` of Theorem C, step (9)** (p. 116, "`χᵢ(1) = aᵢ|D|` and
`a₁ = 1`"): a member `χ₁ ∈ 𝒮` of degree exactly `d`, such that every member's
degree is a positive natural multiple of `χ₁(1)`.

`𝒮(Q′) ≠ ∅` (`ssetOf_Qder_nonempty`, from `S·Q′ < Q`), its members have degree
exactly `d` (`apply_one_eq_d_of_mem_SsetOf_Qder`), and every member of `𝒮` has
degree `d·m` (`exists_apply_one_eq_d_mul`). -/
theorem exists_anchor [Finite G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.H : ℂ)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hnil : Group.IsNilpotent ↥hyp.Q1) :
    ∃ χ₁ ∈ hyp.Sset, χ₁ (1 : ↥hyp.H) = (hyp.d : ℂ) ∧
      ∀ χ ∈ hyp.Sset, ∃ a : ℕ, 0 < a ∧
        χ (1 : ↥hyp.H) = (a : ℂ) * χ₁ (1 : ↥hyp.H) := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.ssetOf_Qder_nonempty (hyp.sup_S_Qder_lt_Q hnil)
  have hd : χ₁ (1 : ↥hyp.H) = (hyp.d : ℂ) :=
    hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχ₁
  refine ⟨χ₁, hyp.SsetOf_subset hyp.Qder hχ₁, hd, fun χ hχ => ?_⟩
  obtain ⟨m, hm, hval⟩ := hyp.exists_apply_one_eq_d_mul hχ
  exact ⟨m, hm, by rw [hval, hd]; ring⟩

section CoherentImage

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
  [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]

/-- **`e_χ ∈ ±Irr(G)`** (Theorem C, step (9), p. 116: "let `eᵢ ∈ ±Irr(G)`"):
the coherent extension sends each member of `𝒮` to a signed irreducible
character of `G`.

The extension preserves inner products on `ℤ[𝒮]` and lands in `ℤ[Irr G]`, so
`‖e_χ‖² = ‖χ‖² = 1` and `e_χ = ε·ξ` with `ε = ±1`, `ξ ∈ Irr(G)`
(`exists_zsmul_irreducibleCharacter_of_inner_self_one`). -/
theorem extension_zsmul_irr
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
      hcoh.extension χ = ε • (ξ : ClassFunction G ℂ) := by
  have hmem : χ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset :=
    Submodule.subset_span hχ
  have hnorm : ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ) = 1 := by
    rw [hcoh.extension_inner_eq χ χ hmem hmem]
    exact hχ.1.inner_self_eq_one
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one
    (hcoh.extension_mem_ZIrr χ hmem) hnorm

/-- **The coherent extension is an isometry on members**: for `χ, χ' ∈ 𝒮`,
`⟨e_χ, e_{χ'}⟩ = ⟨χ, χ'⟩`. -/
theorem extension_inner_member
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ χ' : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset) :
    ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ')
      = ClassFunction.inner χ χ' :=
  hcoh.extension_inner_eq χ χ' (Submodule.subset_span hχ) (Submodule.subset_span hχ')

/-- **Theorem C, step (9), displayed identity** (p. 116):
`Ind_H^G(χ − a·χ') = e_χ − a·e_{χ'}` whenever `χ, χ' ∈ 𝒮` and
`χ(1) = a·χ'(1)`.

The degree-matched difference `χ − a·χ'` is supported on `A = Q^#`
(`scaled_diff_support_subset_A_of_mem_Sset`), where the coherent extension
agrees with `τ = Ind_H^G` (`extends_on_supported`); `ℤ`-linearity of the
extension splits the image. -/
theorem induce_sub_nsmul_extension [Finite G]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ χ' : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    {a : ℕ} (hdeg : χ (1 : ↥hyp.H) = (a : ℂ) * χ' (1 : ↥hyp.H)) :
    ClassFunction.induce hyp.H (χ - a • χ')
      = hcoh.extension χ - a • hcoh.extension χ' := by
  have hspan : χ - a • χ' ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset :=
    Submodule.sub_mem _ (Submodule.subset_span hχ)
      (nsmul_mem (Submodule.subset_span hχ') a)
  have hsupp : (χ - a • χ' : ClassFunction ↥hyp.H ℂ).support ⊆ hyp.A := by
    have h := hyp.scaled_diff_support_subset_A_of_mem_Sset hχ hχ' (n := 1) (m := a)
      (by rw [Nat.cast_one, one_mul]; exact hdeg)
    simpa using h
  have h1 : hcoh.extension (χ - a • χ') = hyp.tau (χ - a • χ') :=
    hcoh.extends_on_supported _ ⟨hspan, hsupp⟩
  have h2 : hcoh.extension (χ - a • χ')
      = hcoh.extension χ - a • hcoh.extension χ' := by
    rw [map_sub, map_nsmul]
  rw [← h2, h1, tau_apply]

end CoherentImage

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
