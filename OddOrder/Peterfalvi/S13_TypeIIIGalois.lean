/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_Orthogonality
import OddOrder.Peterfalvi.S12_Props109To1011
import OddOrder.GroupTheory.RepresentationTheory.GaloisInnerTransport

/-!
# Peterfalvi (11.9): the row-`0` projection — Galois constancy layer

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §11,
statement (11.9), pp. 66–67 (Coq `FTtype34_structure`, `PFsection11.v:1001`).

The Galois-transport layer of the (11.9.a) row-`0` projection analysis (issue 1024): the
`σ`-grid coefficients `a_{ij} = ⟨τ(μ₀ − ζ), ω_{ij}^σ⟩` of the Dade bridge are **constant along
the punctured row `0` and column `0`** (Peterfalvi's (3.9.b) step `a_{i0} = a_{10}`,
`a_{0j} = a_{01}`).  The engine is `ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add`
(the shared `a_aut`), fed by

* the Galois bridge `σ(τ(μ₀ − ζ)) = τ(μ₀ − ζ) + τ(ζ − σζ)` — the Dade map commutes with `σ`
  on `A₀`-supported arguments (`dadeIntegralCharacterMap_mapRingEquiv_comm`) and the column-`0`
  anchor `μ₀` is `σ`-fixed (`mapRingEquiv_muColumnZero_sum`);
* the correction orthogonality `τ(ζ − σζ) ⊥ (Irr W)^σ` — this file: the difference is a
  degree-`0` combination of the `S(HC)`-family (`ζ, σζ ∈ S(HC)` via
  `inducedFamily_closedUnderMapRingEquiv`), so the `S(HC)`-coherent `τ₁` computes it
  (`tau_zeta_sub_mapRingEquiv_eq_SHC_extension`) and lands `⊥`-grid by (5.3.b)
  (`SHC_extension_inner_alignedOmegaSigma_eq_zero`);
* the grid moves `σ(ω_{i0}^σ) = ω_{i'0}^σ` (`exists_mapRingEquiv_chiFam_left_move`/`right`).

The downstream (11.9.a) analysis (separability + Bessel + the integer case split) and the
(11.9.c) type-III determination consume this layer.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The Galois twist of `ζ` stays in the `S(HC)` stratum**: for `ζ ∈ S = inducedFamily M`
irreducible of degree `w₁` and a coefficient automorphism `u`, the twist `σζ` is again an
irreducible member of degree `w₁` (`inducedFamily_closedUnderMapRingEquiv`, `galoisMap`,
and `σ`-fixedness of the rational degree). -/
theorem Hypothesis.mapRingEquiv_mem_SHC_stratum [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.mapRingEquiv u ζ ∈ inducedFamily M ∧
      IsIrreducibleCharacter (ClassFunction.mapRingEquiv u ζ) ∧
      ClassFunction.mapRingEquiv u ζ 1 = (hyp.w1 : ℂ) := by
  refine ⟨inducedFamily_closedUnderMapRingEquiv M u hζS, ?_, ?_⟩
  · have h := (IrreducibleCharacter.galoisMap u ⟨ζ, hζirr⟩).isIrreducible
    rwa [IrreducibleCharacter.galoisMap_apply_coe] at h
  · rw [ClassFunction.mapRingEquiv_apply, hζ1, map_natCast]

open scoped FiniteInduce in
/-- **The `S(HC)`-coherent `τ₁` computes the Galois-twist difference** (the `σ`-generalization of
`tau_zeta_sub_conj_eq_SHC_extension`): `τ(ζ − σζ) = ζ^{τ₁} − (σζ)^{τ₁}`.  The difference is a
degree-`0` `ℤ`-combination of `S(HC)`-members, hence `A₀`-supported
(`SHC_zSpan_vanish_support`), where the coherent extension agrees with `τ`. -/
theorem Hypothesis.tau_zeta_sub_mapRingEquiv_eq_SHC_extension [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ)
      = coh.extension ζ - coh.extension (ClassFunction.mapRingEquiv u ζ) := by
  obtain ⟨hζuS, hζuirr, hζu1⟩ := hyp.mapRingEquiv_mem_SHC_stratum u hζS hζirr hζ1
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanζu : ClassFunction.mapRingEquiv u ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζuS, hζuirr, hζu1⟩
  have hsub1 : (ζ - ClassFunction.mapRingEquiv u ζ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hζ1, hζu1, sub_self]
  have hmem : (ζ - ClassFunction.mapRingEquiv u ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζu,
      hyp.SHC_zSpan_vanish_support hG (Submodule.sub_mem _ hspanζ hspanζu) hsub1⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

open scoped FiniteInduce in
/-- **The Galois-twist correction is orthogonal to the aligned `σ`-grid**:
`⟨τ(ζ − σζ), ω_{ij}^σ⟩ = 0`.  Both `τ₁`-images are `⊥`-grid by (5.3.b)
(`SHC_extension_inner_alignedOmegaSigma_eq_zero`, the non-reality inputs coming from the
odd order via `inducedFamily_hasNoRealCharacters`).  This is the `hcorrection` input of the
`a_aut` engine for the (11.9.a) row/column constancy. -/
theorem Hypothesis.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G)) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  haveI := hyp.finiteG
  obtain ⟨hζuS, hζuirr, hζu1⟩ := hyp.mapRingEquiv_mem_SHC_stratum u hζS hζirr hζ1
  have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hζne : ζ.conj ≠ ζ := fun h =>
    inducedFamily_hasNoRealCharacters hoddM hζS h
  have hζune : (ClassFunction.mapRingEquiv u ζ).conj ≠ ClassFunction.mapRingEquiv u ζ := fun h =>
    inducedFamily_hasNoRealCharacters hoddM hζuS h
  rw [hyp.tau_zeta_sub_mapRingEquiv_eq_SHC_extension hG coh u hζS hζirr hζ1,
    ClassFunction.inner_sub_left,
    hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne i j,
    hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζuS hζuirr hζu1 hζune i j,
    sub_zero]

end OddOrder.Peterfalvi.S12
