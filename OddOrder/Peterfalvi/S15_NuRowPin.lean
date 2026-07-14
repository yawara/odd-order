import OddOrder.Peterfalvi.S15_TSetMemberRFamily

/-!
# Peterfalvi (13.3.c)-`T` — the ν-row pin machinery (coherence-generic)

The `T`-side mirror of `S15_SAndT_Setup/MuColumnPin.lean` (issue 2035, #41 step 4): a
(9.11)-coherent extension of the honest `T`-instance §9 family `𝒯 = sSet(setupT)` on
`τ = Ind_T^G` sends the reducible prime-`TI` **row** sum `ν_i = ∑_j ν_{ij}` to a signed
`η`-**row** sum.  (The `S`/`T` transposition: `S` pins the `p−1` reducible μ-*columns*
`μ_j = ∑_i μ_{ij}` of the `q × p` grid; `T` pins the `q−1` reducible ν-*rows*
`ν_i = ∑_j ν_{ij}`, matching `sSet_reducible_eq_nuRowSum`.)

This file proves the coherence-generic machinery — every statement takes an arbitrary
`c : IsCoherent (Ind_T^G) 𝒯 A(T)`:

* `nuRow_apply_one` / `nuRow_inner` / `nuRow_not_irreducible` — the ν-row basics from the pure
  grid fields (`nu_apply_one_eq_v`, `nu_orthonormal`): degree `p·v`, self-norm `p`, hence
  reducible.
* `nuRow_diff_supported` — arbitrary-row differences are `A(T)`-supported (mirror of
  `muColumn_diff_supported`): both rows have degree `p·v`, so the difference vanishes at `1`,
  and `𝒯`-members are supported on `A(T) ∪ {1}` (`sSet_member_support_subset_T`).
* `coherentIndT_nuRow_diff` — the row-independence
  `c(ν_r) − c(ν_s) = ∑_j η_{rj} − ∑_j η_{sj}` (mirror of `coherentIndS_muColumn_diff`): `c`
  agrees with `Ind_T^G` on the `A(T)`-supported row difference (`extends_on_supported`), which
  is the honest `A₀(T)`-Dade image (`tInstance_dade0_eq_induce`), evaluated per-column by the
  prime-`TI` cross-relation `tauT_nu_cross`.
* `coherentIndT_image_inner_eta_eq_zero` — **Peterfalvi (5.3.b)-at-`T`** (mirror of
  `coherentIndS_image_inner_eta_eq_zero`, family-generic): coherent images of irreducible
  members are orthogonal to the shared `η`-grid.  The coherent conjugate difference is the
  `A₀(T)`-Dade image, vanishing on the saturated regular set `Ŵ^G`
  (`dadeT0_apply_eq_zero_of_regular`); the (3.7)–(3.8) norm-two engine
  `eta_orthogonal_of_norm_one_pair_vanish` finishes.

The pin dichotomy itself (`coherentIndT_nuRow_pin_of_irr`, mirror of
`coherentIndS_muColumn_pin_of_irr`) and its bundling into the (9.11)-`T` carrier
`sSet_coherent_indT_A` build on these; the γ-trick vanishing and the pin live downstream in
this file's continuation (issue 2035 #41 steps 4–5).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **ν-row degree** (Peterfalvi (13.3.a)-at-`T`, case-agnostic): `(∑_j ν_{ij})(1) = p·v` for
`i ≠ 0`.  Each per-entry `ν_{ij}(1) = v` (`nu_apply_one_eq_v`).  Mirror of
`muColumn_apply_one`. -/
theorem Hypothesis.nuRow_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    ((∑ j : Fin hyp.p, hyp.nu i j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
      = (hyp.p : ℂ) * (hyp.v : ℂ) := by
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun j _ => hyp.nu_apply_one_eq_v hG pins i j hi),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open scoped FiniteInduce in
/-- **ν-row self/cross inner product**: `⟨∑_j ν_{rj}, ∑_j ν_{sj}⟩ = p·[r = s]`, from the
full-grid orthonormality `nu_orthonormal`.  Mirror of `muColumn_inner`. -/
theorem Hypothesis.nuRow_inner [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (r s : Fin hyp.q) :
    ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu r j) (∑ j : Fin hyp.p, hyp.nu s j)
      = if r = s then (hyp.p : ℂ) else 0 := by
  haveI := hyp.finiteG
  by_cases hrs : r = s
  · subst hrs; rw [if_pos rfl, OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu r j) (∑ j' : Fin hyp.p, hyp.nu r j')
        = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right,
            Finset.sum_congr rfl (fun j' _ => pins.nu_orthonormal r r j j')]
          simp
      _ = (hyp.p : ℂ) := by simp
  · rw [if_neg hrs, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [pins.nu_orthonormal r s j j', if_neg (fun h => hrs h.1)]

open scoped FiniteInduce in
/-- **A ν-row sum is not irreducible**: `⟨ν_i, ν_i⟩ = p ≠ 1`, while irreducible characters have
norm `1`.  Mirror of `muColumn_not_irreducible`. -/
theorem Hypothesis.nuRow_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) :
    ¬ IsIrreducibleCharacter (∑ j : Fin hyp.p, hyp.nu i j) := by
  haveI := hyp.finiteG
  intro hirr
  have h1 := hirr.inner_self_eq_one
  rw [hyp.nuRow_inner pins i i, if_pos rfl] at h1
  have : hyp.p = 1 := by exact_mod_cast h1
  exact absurd (this ▸ hyp.p_prime) Nat.not_prime_one

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **ν-row differences are `A(T)`-supported** (case-agnostic, arbitrary rows; mirror of
`muColumn_diff_supported`).  Both rows have degree `p·v` (`nuRow_apply_one`), so `ν_r − ν_s`
vanishes at `1`; each row lies in `𝒯` (`nu_rowSum_mem_sOf_H0_T` + `sOf_subset_sSet`) whose
members are supported on `A(T) ∪ {1}` (`sSet_member_support_subset_T`), so the difference
avoids `{1}` and lands in `A(T)`. -/
theorem Hypothesis.nuRow_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r s : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T := by
  intro z hz
  have hz0 : ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)) z ≠ 0 := hz
  have hxmem : (∑ j : Fin hyp.p, hyp.nu r j) ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr)
  have hymem : (∑ j : Fin hyp.p, hyp.nu s j) ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs)
  have hdeg : ((∑ j : Fin hyp.p, hyp.nu r j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
      = ((∑ j : Fin hyp.p, hyp.nu s j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 := by
    rw [hyp.nuRow_apply_one hG pins r hr, hyp.nuRow_apply_one hG pins s hs]
  rcases ClassFunction.support_sub_subset _ _ hz with h | h
  · rcases hyp.sSet_member_support_subset_T hG hvd hxmem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset_T hG hvd hymem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁` row-difference identity, coherence-generic** (the (13.3.c)-at-`T` row-independence;
mirror of `coherentIndS_muColumn_diff`): *any* coherent extension `c` of `𝒯 = sSet(setupT)` on
`Ind_T^G` sends the reducible row difference to the aligned `η`-row difference,
`c(∑_j ν_{rj}) − c(∑_j ν_{sj}) = (∑_j η_{rj}) − (∑_j η_{sj})`, for distinct nonzero `r ≠ s`.
`c` agrees with `Ind_T^G` on the `A(T)`-supported row difference (`extends_on_supported`),
which is the honest `A₀(T)`-Dade image (`tInstance_dade0_eq_induce`), evaluated per-column by
the prime-`TI` cross-relation `tauT_nu_cross`. -/
theorem Hypothesis.coherentIndT_nuRow_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T))
    {r s : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩)
    (hrs : r ≠ s) :
    c.extension (∑ j : Fin hyp.p, hyp.nu r j) - c.extension (∑ j : Fin hyp.p, hyp.nu s j)
      = (∑ j : Fin hyp.p, hyp.eta r j) - (∑ j : Fin hyp.p, hyp.eta s j) := by
  classical
  haveI := hyp.finiteG
  have hAsupp := hyp.nuRow_diff_supported hG pins hvd chief hr hs
  have hmemSpan : ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T) :=
    ⟨Submodule.sub_mem _
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr)))
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs))),
      hAsupp⟩
  have hA0supp := hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
    (honestTypeP2ASet_subset_A0Set Tdata))
  rw [← map_sub, c.extends_on_supported _ hmemSpan, hyp.indT_apply,
    ← hyp.tInstance_dade0_eq_induce hG hnoV hT2 Tdata hA0supp,
    show ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j))
      = ∑ j : Fin hyp.p, (hyp.nu r j - hyp.nu s j) from by rw [Finset.sum_sub_distrib],
    map_sum, Finset.sum_congr rfl (fun j _ =>
      tauT_nu_cross hG hnoV hyp pins hT2 Tdata hU hW1 hW2 j hr hs hrs),
    Finset.sum_sub_distrib]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.3.b)-at-`T`, coherent images are orthogonal to the shared `η`-grid**
(mirror of `coherentIndS_image_inner_eta_eq_zero`, family-generic; issue 2035 #41 step 5's
`(5.3.b)-T` input).

For a conjugate-closed no-real family `𝒮` of characters of the type-`P₂` maximal `T` whose
conjugate differences are `A(T) = honestTypeP2ASet T`-supported, and a coherence
`coh : IsCoherent (Ind_T^G) 𝒮 A(T)` of the induction map `τ = Ind_T^G` (`hyp.indT`), every
coherent image `coh.extension ζ` (`ζ ∈ 𝒮` irreducible) is orthogonal to the entire `η`-grid.
The coherent conjugate difference agrees with the `A₀(T)`-Dade image
(`tInstance_dade0_eq_induce`), which vanishes on the saturated regular set `Ŵ^G`
(`dadeT0_apply_eq_zero_of_regular`); the (3.7)–(3.8) norm-two engine
`eta_orthogonal_of_norm_one_pair_vanish` finishes. -/
theorem coherentIndT_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {S : Set (ClassFunction ↥hyp.T ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T))
    {ζ : ClassFunction ↥hyp.T ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (coh.extension ζ) (hyp.eta i j) = 0 := by
  haveI := hyp.finiteG
  have hζc : ζ.conj ∈ S := hconj hζ
  -- `ζ − ζ̄` lies in the `A(T)`-supported span of `𝒮`.
  have hdiffSpan : ζ - ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) S :=
    Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hdiffSupp := hsupp ζ hζ
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T) :=
    ⟨hdiffSpan, hdiffSupp⟩
  -- `A(T) ⊆ A₀(T)`, so the difference is also `A₀(T)`-supported (the `dadeHypT0` support).
  have hA0Supp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T :=
    hdiffSupp.trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono (honestTypeP2ASet_subset_A0Set Tdata))
  -- `τ = Ind_T^G` equals the `A₀(T)`-Dade image on the `A₀(T)`-supported difference.
  have hmaps : hyp.indT (ζ - ζ.conj) =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
        ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData
          (hyp.dadeHypT0_hconj hG hT2 Tdata)) (ζ - ζ.conj) := by
    rw [hyp.indT_apply]
    exact (hyp.tInstance_dade0_eq_induce hG hnoV hT2 Tdata hA0Supp).symm
  -- the coherent conjugate difference agrees with that Dade image.
  have hextDiff : coh.extension ζ - coh.extension ζ.conj =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hT2 Tdata)
        ((hyp.dadeHypT0 hG hT2 Tdata).fullDadeIsometryData
          (hyp.dadeHypT0_hconj hG hT2 Tdata)) (ζ - ζ.conj) := by
    rw [← hmaps, ← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  -- the crux: the difference vanishes on the saturated regular set.
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (coh.extension ζ - coh.extension ζ.conj) x = 0 := by
    intro x hx
    rw [hextDiff]
    exact hyp.dadeT0_apply_eq_zero_of_regular hG hT2 Tdata hW1 hW2 hdiffSupp hx
  -- the straightforward `dirr`-input norms.
  have hpsiZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span hζ)
  have hconjZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζc)
  have hpsi1 : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
    rw [coh.extension_inner_eq ζ ζ (Submodule.subset_span hζ) (Submodule.subset_span hζ)]
    exact hζirr.inner_self_eq_one
  have hconj1 : ClassFunction.inner (coh.extension ζ.conj) (coh.extension ζ.conj) = 1 := by
    rw [coh.extension_inner_eq ζ.conj ζ.conj (Submodule.subset_span hζc)
      (Submodule.subset_span hζc)]
    exact hζirr.conj.inner_self_eq_one
  have hcross : ClassFunction.inner (coh.extension ζ) (coh.extension ζ.conj) = 0 := by
    rw [coh.extension_inner_eq ζ ζ.conj (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hnoReal hζ h.symm)]
  intro i j
  have h := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, star_eq_zero]
  exact h

end OddOrder.Peterfalvi.S15
