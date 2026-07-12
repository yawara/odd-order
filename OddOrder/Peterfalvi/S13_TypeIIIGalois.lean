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

/-- **`w₁` is prime for a type-III/IV maximal subgroup**: the `TypePNontrivialCore` of the
type-III/IV data carries `(|W₁'|).Prime` for *its* type-`P` structure, and `|W₁| = [M : M']`
is independent of the choice (`card_W1_eq_derived_index`), so `hyp.w1` inherits primality. -/
theorem Hypothesis.w1_prime_of_typeIIIorIV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    (hyp.w1).Prime := by
  have hbase : hyp.w1 = Nat.card ↥hyp.typeP.W1 := rfl
  rcases htype with h3 | h4
  · obtain ⟨data⟩ := h3
    refine (show Nat.card ↥data.typeP.W1 = hyp.w1 from ?_) ▸ data.common.2.1
    rw [data.typeP.card_W1_eq_derived_index, hbase, hyp.typeP.card_W1_eq_derived_index]
  · obtain ⟨data⟩ := h4
    refine (show Nat.card ↥data.typeP.W1 = hyp.w1 from ?_) ▸ data.common.2.1
    rw [data.typeP.card_W1_eq_derived_index, hbase, hyp.typeP.card_W1_eq_derived_index]

open scoped FiniteInduce in
/-- **The Galois bridge for the Dade image of `μ₀ − ζ`** (Coq `aut_phi`):
`σ(τ(μ₀ − ζ)) = τ(μ₀ − ζ) + τ(ζ − σζ)`.  The Dade map commutes with `σ` on the `A₀`-supported
`μ₀ − ζ` (`tau_mapRingEquiv_comm`), the anchor `μ₀` is `σ`-fixed
(`mapRingEquiv_muColumnZero_sum`), and `τ` is additive.  This is the `hφ` input of the `a_aut`
engine (`inner_eq_intCast_of_mapRingEquiv_eq_add`) for the (11.9.a) constancy. -/
theorem Hypothesis.mapRingEquiv_tau_muColumnZero_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.mapRingEquiv u
        (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ))
      = hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ)
        + hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ) := by
  haveI := hyp.finiteG
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  rw [← hyp.tau_mapRingEquiv_comm u hsupp, ← map_add]
  congr 1
  rw [ClassFunction.mapRingEquiv_sub, hyp.mapRingEquiv_muColumnZero_sum hG hodd u]
  abel

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.a), the column-`0` Galois constancy** (`a_{i'0} = a_{i0}` for
`i, i' ≠ 0`): the `σ`-grid coefficients of `ψ = τ(μ₀ − ζ)` along the punctured column `0` are
constant.  The `a_aut` engine (`inner_eq_intCast_of_mapRingEquiv_eq_add`) at the (3.9.b) grid
move `σ(ω_{i0}^σ) = ω_{i'0}^σ` (`exists_mapRingEquiv_chiFam_left_move`, `|W₁|` prime), with the
Galois bridge (`mapRingEquiv_tau_muColumnZero_sub_zeta`) and the correction orthogonality
(`tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero`). -/
theorem Hypothesis.inner_tau_muColumnZero_sub_zeta_columnZero_const [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {i i' : Fin hyp.w1} (hi : i ≠ 0) (hi' : i' ≠ 0) :
    ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
      = ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  have hchi := (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)
  -- the `(ρ 0, κ 0) = (1, 1)` anchor, from the trivial corner and orthonormality
  have h00 : (ρ 0, κ 0)
      = ((1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
        (1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)) := by
    by_contra hne
    have h0 := hchi.2.2.1 (ρ 0, κ 0) (1, 1)
    rw [if_neg hne, ← hprod 0 0, hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hchi.1] at h0
    have htmem : trivialClassFunction G ∈ irreducibleCharacters G :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner htmem htmem, if_pos rfl] at h0
    exact one_ne_zero h0
  have hρ0 : ρ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.1
  have hκ0 : κ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.2
  -- nontriviality of the moved indices
  have hpne : ρ i ≠ 1 := fun h => hi (hρinj (h.trans hρ0.symm))
  have hp'ne : ρ i' ≠ 1 := fun h => hi' (hρinj (h.trans hρ0.symm))
  -- `ψ` is a virtual character
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hμ0Z : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.muGrid_isIrreducible hG hodd r 0).mem_ZIrr)
  have hψZ : hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  -- the Galois move on the punctured column `0`
  have hprime : (Nat.card (typePData_toTICyclicHypothesis hyp.typeP hodd).W1).Prime :=
    hyp.w1_prime_of_typeIIIorIV htype
  obtain ⟨u, hmove⟩ :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).exists_mapRingEquiv_chiFam_left_move rfl
      (hyp.canonicalFullDadeApp hG hodd) hprime hpne hp'ne
  -- the integral coefficient at the source index
  have hηZ : (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
      (hyp.canonicalFullDadeApp hG hodd) (ρ i, 1) ∈ ZIrr G := hchi.2.1 _
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hψZ hηZ
  -- the correction orthogonality at the target index
  have hcorr : ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
        (hyp.canonicalFullDadeApp hG hodd) (ρ i', 1)) = 0 := by
    rw [← hκ0, ← hprod i' 0]
    exact hyp.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero hG coh hodd u
      hζS hζirr hζ1 i' 0
  -- the `a_aut` transport
  have htransport := ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add u m hψZ hηZ
    (hyp.mapRingEquiv_tau_muColumnZero_sub_zeta hG hodd u hζS hζ1) hmove.symm hm hcorr
  rw [hprod i' 0, hprod i 0, hκ0, htransport, hm]

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.a), the row-`0` Galois constancy** (`a_{0j'} = a_{0j}` for `j, j' ≠ 0`):
the `W₂`-side mirror of `inner_tau_muColumnZero_sub_zeta_columnZero_const`, via
`exists_mapRingEquiv_chiFam_right_move` and `|W₂|` prime (`w2_prime`). -/
theorem Hypothesis.inner_tau_muColumnZero_sub_zeta_rowZero_const [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {j j' : Fin hyp.w2} (hj : j ≠ 0) (hj' : j' ≠ 0) :
    ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd 0 j')
      = ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd 0 j) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  have hchi := (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)
  have h00 : (ρ 0, κ 0)
      = ((1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
        (1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)) := by
    by_contra hne
    have h0 := hchi.2.2.1 (ρ 0, κ 0) (1, 1)
    rw [if_neg hne, ← hprod 0 0, hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hchi.1] at h0
    have htmem : trivialClassFunction G ∈ irreducibleCharacters G :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner htmem htmem, if_pos rfl] at h0
    exact one_ne_zero h0
  have hρ0 : ρ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.1
  have hκ0 : κ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.2
  have hqne : κ j ≠ 1 := fun h => hj (hκinj (h.trans hκ0.symm))
  have hq'ne : κ j' ≠ 1 := fun h => hj' (hκinj (h.trans hκ0.symm))
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hμ0Z : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.muGrid_isIrreducible hG hodd r 0).mem_ZIrr)
  have hψZ : hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hsupp (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  have hprime : (Nat.card (typePData_toTICyclicHypothesis hyp.typeP hodd).W2).Prime :=
    hyp.w2_prime hG
  obtain ⟨u, hmove⟩ :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).exists_mapRingEquiv_chiFam_right_move rfl
      (hyp.canonicalFullDadeApp hG hodd) hprime hqne hq'ne
  have hηZ : (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
      (hyp.canonicalFullDadeApp hG hodd) (1, κ j) ∈ ZIrr G := hchi.2.1 _
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hψZ hηZ
  have hcorr : ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
        (hyp.canonicalFullDadeApp hG hodd) (1, κ j')) = 0 := by
    rw [← hρ0, ← hprod 0 j']
    exact hyp.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero hG coh hodd u
      hζS hζirr hζ1 0 j'
  have htransport := ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add u m hψZ hηZ
    (hyp.mapRingEquiv_tau_muColumnZero_sub_zeta hG hodd u hζS hζ1) hmove.symm hm hcorr
  rw [hprod 0 j', hprod 0 j, hρ0, htransport, hm]

end OddOrder.Peterfalvi.S12
