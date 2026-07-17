/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_HonestTypeP2A0
import OddOrder.Peterfalvi.S16_GridExpansion

/-!
# Peterfalvi (5.3.b) / (14.9), `S`-side coherent images are orthogonal to the shared `η`-grid

This is the `S`-side mirror of the proven T-side template
`OddOrder.Peterfalvi.S16.T_typeIII_coherent_image_inner_eta_eq_zero`
(`S16_NonExistenceG/TTypeIICoherence.lean`).

Let `𝒮` be a conjugate-closed, no-real family of irreducible characters of the type-`P₂`
maximal subgroup `S`, whose member differences `ζ − ζ̄` are supported on the honest type-`P₂`
Dade support `A(S) = honestTypeP2ASet S` (which lies inside `S' = derivedInG S`).  Given a
coherence `coh : IsCoherent (Ind_S^G) 𝒮 A(S)` of the induction map `τ = Ind_S^G` (Peterfalvi
(13.2.e), `hyp.indS`), every coherent image `τ₁ ζ = coh.extension ζ` is orthogonal to the whole
shared `η`-grid.

The proof mirrors the T-side line for line, with the `S`-side Dade pieces substituted:

* the difference `coh.extension ζ − coh.extension ζ̄` agrees with `τ = Ind_S^G` on the
  `A(S)`-supported span (`coh.extends_on_supported`), which is the `A₀(S)`-Dade image
  `dadeIntegralCharacterMap (dadeHypS0) (ζ − ζ̄)` by the honest `'A0`-Dade=Ind bridge
  `Hypothesis.sInstance_dade0_eq_induce` ((13.2.e) `τ_S = Ind_S^G` on `A₀(S)`-supported);
* for a regular element `w ∈ W ∖ (W₁ ∪ W₂)` (a `typePV`-point, hence in `A₀(S)` via the
  `V^S`-part `conjClassSetIn`), the Dade map reads the source difference at `w`, zero because the
  source is `A(S)`-supported and `A(S) ⊆ S' = derivedInG S`, while a regular `W`-element lies
  **outside** the derived subgroup (`typePData_typePV_not_mem_derived`);
* conjugacy invariance saturates the vanishing to `conjClassSet (W ∖ (W₁ ∪ W₂))`, and the
  (3.7)--(3.8) norm-two engine `S16.eta_orthogonal_of_norm_one_pair_vanish` gives the individual
  orthogonality.

Both `A(S)` (the coherence / difference support) and `A₀(S) = A(S) ∪ (V^S)` (the `dadeHypS0`
support) enter, exactly as `A₁(T) = sigmaSharp T` and `typePA0 T` do on the T-side.

The coherence `coh` is taken as a hypothesis (as on the T-side), with support the **honest
Dade support** `A(S) = honestTypeP2ASet S` (`⊆ S'`) — the analogue of the T-side
`A₁(T) = sigmaSharp T`.  This is **not** the support of the §9/§11 coherence
`Hypothesis.coherent_H0Cprime_S`: that carries the *kernel* support `(H₀C')^# = cprimeSharpS`,
which for the honest type-`P₂` `S` degenerates to `∅` (`cprimeSharpS_eq_empty`, since
`C' = [C_U(P), C_U(P)] = ⊥`), so its `extends_on_supported` fires only on `0`.  Instantiating this
engine therefore needs an `A(S)`-supported coherence of `Ind_S^G` — the (13.3)
`coherent_H0Cprime_S` **re-grounding** to the genuine Dade support `A(S)` (bridged by
`cprimeSharpS_subset_supportA : (C')^# ⊆ A(S)`), the remaining upstream step; this file supplies
the downstream orthogonality engine it feeds.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.3.b) / (14.9), `S`-side coherent images are orthogonal to the shared `η`-grid**
(the `S`-side mirror of `S16.T_typeIII_coherent_image_inner_eta_eq_zero`).

For a conjugate-closed no-real family `𝒮` of irreducible characters of the type-`P₂` maximal
`S` whose differences are `A(S) = honestTypeP2ASet S`-supported, and a coherence
`coh : IsCoherent (Ind_S^G) 𝒮 A(S)` of the (13.2.e) induction map `τ = Ind_S^G` (`hyp.indS`),
every coherent image `coh.extension ζ` (`ζ ∈ 𝒮` irreducible) is orthogonal to the entire
`η`-grid. -/
theorem coherentIndS_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)]
    {S : Set (ClassFunction ↥hyp.S ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S))
    {ζ : ClassFunction ↥hyp.S ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (coh.extension ζ) (hyp.eta i j) = 0 := by
  -- align the ambient `Fintype G`/`Invertible` with the canonical `FiniteInduce` instances that
  -- `hyp.eta` and the (3.8) engine `eta_orthogonal_of_norm_one_pair_vanish` are stated with.
  have hfintype : fintypeG = OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype :=
    Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG :=
    Subsingleton.elim _ _
  subst invertibleG
  classical
  have hζc : ζ.conj ∈ S := hconj hζ
  -- `ζ − ζ̄` lies in the `A(S)`-supported span of `𝒮`.
  have hdiffSpan : ζ - ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.S) S :=
    Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hdiffSupp := hsupp ζ hζ
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) :=
    ⟨hdiffSpan, hdiffSupp⟩
  -- `A(S) ⊆ A₀(S)`, so the difference is also `A₀(S)`-supported (the `dadeHypS0` support).
  have hA0Supp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
    hdiffSupp.trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono (honestTypeP2ASet_subset_A0Set hyp.Sdata))
  -- (13.2.e) `τ = Ind_S^G` equals the `A₀(S)`-Dade image on the `A₀(S)`-supported difference.
  have hmaps : hyp.indS (ζ - ζ.conj) =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (ζ - ζ.conj) := by
    rw [hyp.indS_apply]
    exact (hyp.sInstance_dade0_eq_induce hG hnoV hA0Supp).symm
  -- the coherent conjugate difference agrees with that Dade image.
  have hextDiff : coh.extension ζ - coh.extension ζ.conj =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (ζ - ζ.conj) := by
    rw [← hmaps, ← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  -- the crux: the difference vanishes on the saturated regular set.
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (coh.extension ζ - coh.extension ζ.conj) x = 0 := by
    intro x hx
    obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
    rw [hextDiff]
    rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (ζ - ζ.conj)).of_isConj
        (isConj_iff.mpr ⟨g, hg⟩)]
    -- `w` is a regular `W`-element, hence a `typePV`-point of the `S`-data.
    have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
      refine ⟨?_, ?_⟩
      · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
          rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
        rw [hWeq]; exact hw.1
      · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw.2
    have hwA0 : w ∈ honestTypeP2A0Set hyp.S hyp.Sdata :=
      Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) hA0Supp]
    let a : {a : G // a ∈ honestTypeP2A0Set hyp.S hyp.Sdata} := ⟨w, hwA0⟩
    have hwh : w ∈ (hyp.dadeHypS0 hG).hCoset a :=
      ⟨1, (hyp.dadeHypS0 hG).H a |>.one_mem, by simp [a]⟩
    rw [(hyp.dadeHypS0 hG).isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
    by_contra hne
    have hwSupp : (⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩ : ↥hyp.S) ∈ (ζ - ζ.conj).support :=
      ClassFunction.mem_support.mpr hne
    -- the source is `A(S)`-supported, so `w ∈ A(S) ⊆ S' = derivedInG S`.
    have hwA : w ∈ honestTypeP2ASet hyp.S := hdiffSupp hwSupp
    have hwDeriv : w ∈ derivedInG hyp.S := honestTypeP2ASet_subset_derived hwA
    -- but a regular `W`-element lies outside the derived subgroup.
    exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.Sdata hwV) hwDeriv
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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) uniform sub-family `S₁(d)`: coherent images are orthogonal to the shared `η`-grid**
(issue 1017, the (A)-engine instantiated on the honest uniform base coherence — *no coherence
hypothesis*).

The (A) engine `coherentIndS_image_inner_eta_eq_zero` takes an arbitrary `A(S)`-supported
coherence `coh : IsCoherent (Ind_S^G) S A(S)` of a conjugate-closed, no-real, difference-supported
family `S`.  Here we specialize it to the uniform-degree irreducible sub-family
`S = sSetIrrDeg hG d` (`S₁(d)`), discharging **all** of the engine's family/coherence inputs from
landed §9/§15 material:

* `hconj` = `sSetIrrDeg_closedUnderConjugate` (uses `hd : star d = d`);
* `hnoReal` = `sSetIrrDeg_hasNoRealCharacters` (via `oddCardS`);
* `hsupp` = `sSetIrrDeg_member_diff_supported` with `y = ζ̄` (the conjugate lands in `S₁(d)` by
  `sSetIrrDeg_closedUnderConjugate`);
* `coh` = `(sSetIrrDeg_coherent_indS hG d hd hd0 h2).some`, the honest (5.7)∘(5.3.a) uniform-degree
  base coherence of `Ind_S^G`.

The only remaining hypotheses are the degree reality/nonvanishing `hd`/`hd0` and the `≥ 2`
membership `h2` (the §9 (9.8.d) count, exposed as before) — there is **no** coherence hypothesis.
All finiteness instances are taken from the `FiniteInduce` scope (from `[Finite G]`), so the
`Ind_S^G` in the base coherence `sSetIrrDeg_coherent_indS` and in the engine's `coh` slot share the
same `Fintype ↥S`.  This is the downstream orthogonality the §13 char cascade consumes for the
uniform base; the full-`sSet` lift ((9.11.1)–(9.11.8) pair-adjoining induction) feeds the same
engine once the base is widened. -/
theorem sSetIrrDeg_coherentIndS_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard)
    {ζ : ClassFunction ↥hyp.S ℂ} (hζ : ζ ∈ hyp.sSetIrrDeg hG d)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner
        ((hyp.sSetIrrDeg_coherent_indS hG hnoV d hd hd0 h2).some.extension ζ)
        (hyp.eta i j) = 0 :=
  coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
    (hyp.sSetIrrDeg_closedUnderConjugate hG d hd)
    (hyp.sSetIrrDeg_hasNoRealCharacters hG d)
    (fun _ζ' hζ' => hyp.sSetIrrDeg_member_diff_supported hG d hζ'
      (hyp.sSetIrrDeg_closedUnderConjugate hG d hd hζ'))
    (hyp.sSetIrrDeg_coherent_indS hG hnoV d hd hd0 h2).some
    hζ hζirr

end OddOrder.Peterfalvi.S15
