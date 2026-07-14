import OddOrder.Peterfalvi.S15_CaseACoherence
import OddOrder.Peterfalvi.S15_SAndT_Setup.CountingLayer
import OddOrder.Peterfalvi.S15_SAndT_Setup.TSideDegrees

/-!
# Peterfalvi §13 (pp. 75–86) — (13.3)/(13.5) τ₁-field supplies on the irreducibly-induced family

Honest supplies for the `CharacterDegreeData` τ₁-fields (issue 2035/9094) that quantify over
**irreducibly**-induced members `Ind_{PC}^S θ ∈ Irr S`:

* `induce_H_mem_zSpan_sSet_irr` — the **irreducible branch of Coq's `S1cases`**
  (`PFsection13.v:401-428`): an *irreducible* `Ind_{PC}^S θ` (with `P ⊄ Ker θ`) lies in
  `ℤ[𝒮 ∩ Irr S]` (Coq's `'Z[calSirr]`).  The constituent expansion of
  `induce_H_mem_zSpan_S` is upgraded per-constituent: a reducible constituent-induction would
  be a `μ`-column (`sSet_reducible_eq_muColumnSum`), forcing `⟨Ind θ, μ_j⟩ ≠ 0` — but distinct
  `H`-inductions are orthogonal and `Ind θ = μ_j` is refuted by irreducibility
  (`mu_colSum_not_irreducible`).
* `tau1S_ofHonest_zSpanIrr_inner_eta` — `τ₁`-images of `ℤ[𝒮 ∩ Irr S]` are orthogonal to the
  `η`-grid (span induction over the (5.3.b) crux `coherentIndS_image_inner_eta_eq_zero`).
* `tau1S_ofHonest_induce_inner_eta` — the (13.3) field supply: for irreducible `Ind_{PC}^S θ`
  with `P ⊄ Ker θ`, `⟨η_{ij}, τ₁(Ind θ)⟩ = 0`.

The `P ⊄ Ker` guard is the honest scope (issue 2035 更新 #22): Peterfalvi's (13.5) converts
`τ₁ ↔ Ind_S^G` only on the `𝒮₁`-members (`P ⊄ Ker`), the `P`-kernel side staying as the
unknown `α` of (13.5.a).  This file is the landing pad for the (9094 ruling 案 A) conditional
producer and the λ-free core supplies.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
set_option maxHeartbeats 800000 in
/-- **The irreducible branch of Coq's `S1cases`** (`PFsection13.v:401-428`, issue 2035): an
*irreducible* induced character `Ind_{PC}^S θ` (`θ ∈ Irr H`, `P ⊄ Ker θ`) lies in
`ℤ[𝒮 ∩ Irr S]` — the integral span of the *irreducible* members of the honest §9 family
(Coq's `'Z[calSirr]`).

**Proof.**  As in `induce_H_mem_zSpan_S`, the two-stage expansion writes
`Ind_{PC}^S θ = ∑_s ⟨θ', Res s⟩ • Ind_{S'}^S s` over `S'`-constituents with `ℕ`-coefficients,
each nonzero-coefficient constituent having `P ⊄ Ker s` (hence `Ind_{S'}^S s ∈ 𝒮`).  The upgrade:
every such member is *irreducible*.  Otherwise it is a `μ`-column `μ_j = ∑_i μ_{ij}`
(`sSet_reducible_eq_muColumnSum`), and the expansion pairs to
`⟨Ind θ, μ_j⟩ = ∑_t k_t·⟨Ind_{S'} t, μ_j⟩`, a sum of non-negative integers with the offending
term `k_{s₀}·q > 0` (`𝒮`-members are pairwise orthogonal, `‖μ_j‖² = q`); but `⟨Ind θ, μ_j⟩ = 0`
since `μ_j = Ind_{PC}^S θ_j` ((13.3.a)) is a *distinct* `H`-induction (equality would make the
irreducible `Ind θ` equal the reducible `μ_j`), and distinct-source `H`-inductions are
orthogonal (`inner_induce_eq_zero_of_not_conj`). -/
theorem Hypothesis.induce_H_mem_zSpan_sSet_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
        ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
      Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
    have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
          (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
      ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      rfl
    rw [himg]; exact hθP
  -- Two-stage constituent expansion with `ℕ`-coefficients `k s`.
  have hzeta : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      = ∑ s : IrreducibleCharacter ↥HU,
          ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
            (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
              (s : ClassFunction ↥HU ℂ))
            • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
    rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ,
      OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
      ClassFunction.induce_sum]
    exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
  have hcoefNat : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
      ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
    intro s
    have hResChar : IsCharacter (ClassFunction.restrict
        ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
      OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
    obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
    exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
  choose k hk using hcoefNat
  -- Nonzero-coefficient constituents give family members (`P ⊄ Ker s`, membership by witness).
  have hmem : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
    intro s hks
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hk s]; exact_mod_cast hks
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs
  -- **The upgrade**: every nonzero-coefficient constituent induction is irreducible.
  have hirrall : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)) := by
    intro s₀ hk₀
    by_contra hred
    -- a reducible member is a nonzero `μ`-column ((13.3.a) reverse dichotomy)
    obtain ⟨j, hj, hμeq₀⟩ := hyp.sSet_reducible_eq_muColumnSum hG (hmem s₀ hk₀) hred
    obtain ⟨θj, hθjirr, -, hμeq⟩ := hyp.mu_j_isIndPC hG j hj
    -- `Ind θ ≠ μ_j` (irreducible vs. reducible), so the distinct `H`-inductions are orthogonal
    have hne' : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
        ≠ ClassFunction.induce (hyp.H.subgroupOf hyp.S) θj := by
      intro h
      exact hyp.mu_colSum_not_irreducible j (by rw [hμeq, ← h]; exact hind)
    haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
    have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
        (∑ i : Fin hyp.q, hyp.mu i j) = 0 := by
      rw [hμeq]
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj
        (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _)
        (⟨θj, hθjirr⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) ?_
      intro g hg
      apply hne'
      have h1 : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g
              (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) :
            OddOrder.RepresentationTheory.IrreducibleCharacter _) :
              ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
        exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
          (G := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) g _
      rw [← h1, hg]
    -- expand `⟨Ind θ, μ_j⟩` through the constituent sum: non-negative integer terms
    have hexp : ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
        (∑ i : Fin hyp.q, hyp.mu i j)
        = ∑ s : IrreducibleCharacter ↥HU, (k s : ℂ) *
            ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
              (∑ i : Fin hyp.q, hyp.mu i j) := by
      rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hk s, OddOrder.RepresentationTheory.ClassFunction.inner_smul_left]
    have hμmem : (∑ i : Fin hyp.q, hyp.mu i j) ∈ sSet data :=
      OddOrder.Peterfalvi.S11.sOf_subset_sSet data chief.H0
        (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
    have hterm : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
        (k s : ℂ) * ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
          (∑ i : Fin hyp.q, hyp.mu i j) = (n : ℂ) := by
      intro s
      rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
      · exact ⟨0, by rw [h0]; simp⟩
      · by_cases heq : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)
            = ∑ i : Fin hyp.q, hyp.mu i j
        · refine ⟨k s * hyp.q, ?_⟩
          rw [heq, hyp.muColumn_inner_self j]
          push_cast
          ring
        · refine ⟨0, ?_⟩
          rw [sSet_pairwiseOrthogonal data (hmem s hpos.ne') hμmem heq, mul_zero, Nat.cast_zero]
    choose n hn using hterm
    -- the total is `0`, so every `ℕ`-term vanishes — but the `s₀`-term is `k s₀ · q > 0`
    have hsumC : ∑ s : IrreducibleCharacter ↥HU, ((n s : ℕ) : ℂ) = 0 := by
      rw [Finset.sum_congr rfl fun s _ => (hn s).symm, ← hexp, hzmu]
    have hsumN : ∑ s : IrreducibleCharacter ↥HU, n s = 0 := by
      rw [← Nat.cast_sum] at hsumC
      exact_mod_cast hsumC
    have hn0 : n s₀ = 0 :=
      (Finset.sum_eq_zero_iff.mp hsumN) s₀ (Finset.mem_univ s₀)
    have hval : (k s₀ : ℂ) * ClassFunction.inner
        (ClassFunction.induce HU (s₀ : ClassFunction ↥HU ℂ))
        (∑ i : Fin hyp.q, hyp.mu i j) = (k s₀ : ℂ) * (hyp.q : ℂ) := by
      rw [hμeq₀, hyp.muColumn_inner_self j]
    have : ((n s₀ : ℕ) : ℂ) ≠ 0 := by
      rw [← hn s₀, hval]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hk₀)
        (Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne')
    exact this (by rw [hn0, Nat.cast_zero])
  -- assemble: the expansion lands in `ℤ[𝒮 ∩ Irr S]`
  rw [hzeta]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [hk s]
  rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
  · rw [h0]; simp
  · rw [Nat.cast_smul_eq_nsmul ℂ (k s)]
    have hmemIrr : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈
        {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet data ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} :=
      ⟨hmem s hpos.ne', hirrall s hpos.ne'⟩
    exact nsmul_mem (Submodule.subset_span hmemIrr) (k s)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of `ℤ[𝒮 ∩ Irr S]` are orthogonal to the `η`-grid** (Peterfalvi
(4.1)+(5.3.b), issue 2035): span induction over the (5.3.b) crux
`coherentIndS_image_inner_eta_eq_zero` — `τ₁` is `ℤ`-linear and the inner product is linear in
the first slot, so the member-level grid-orthogonality extends to the integral span of the
irreducible members. -/
theorem Hypothesis.tau1S_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ) (hyp.eta i j) = 0 := by
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
        (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
        (fun ζ' hζ' => by
          rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
              = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
            ClassFunction.support_neg]
          exact hyp.sSet_member_conjDiff_supported hG hζ')
        (hyp.coherent_H0Cprime_S hG hnoV chief) hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) honest supply for the `tau1S_induce_inner_eta` field** (issue 2035/9094): for
an irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) whose induction `Ind_{PC}^S θ` is irreducible,
the `τ₁`-image is orthogonal to the whole `η`-grid.  Composition of the `ℤ[𝒮 ∩ Irr S]`
membership (`induce_H_mem_zSpan_sSet_irr`, Coq `S1cases` irreducible branch) with the span-level
grid orthogonality (`tau1S_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpanIrr_inner_eta hG hnoV chief i j
      (hyp.induce_H_mem_zSpan_sSet_irr hG θ hθ hθP hind),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁`-images of the full lattice `ℤ[𝒮]` are orthogonal to the `η`-column `0`**
(Peterfalvi (4.1)+(5.3.b) + (13.3.c), issue 2035): span induction over the *mixed* family —
an irreducible member is grid-orthogonal by the (5.3.b) crux; a reducible member is a
`μ`-column (`sSet_reducible_eq_muColumnSum`) whose `τ₁`-image is a (signed) *nonzero*-column
`η`-sum (`tau1S_ofHonest_muColumn_formula`), orthogonal to column `0` by the grid
orthonormality. -/
theorem Hypothesis.tau1S_ofHonest_zSpan_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    {φ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))) :
    ClassFunction.inner (hyp.tau1S_ofHonest hG hnoV chief φ)
      (hyp.eta i ⟨0, hyp.p_prime.pos⟩) = 0 := by
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      by_cases hζirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter ζ
      · -- irreducible member: full grid orthogonality by the (5.3.b) crux
        exact coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
          (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
          (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
          (fun ζ' hζ' => by
            rw [show ζ' - (ζ' : ClassFunction ↥hyp.S ℂ).conj
                = -((ζ' : ClassFunction ↥hyp.S ℂ).conj - ζ') from (neg_sub _ _).symm,
              ClassFunction.support_neg]
            exact hyp.sSet_member_conjDiff_supported hG hζ')
          (hyp.coherent_H0Cprime_S hG hnoV chief) hζ hζirr i ⟨0, hyp.p_prime.pos⟩
      · -- reducible member: a nonzero `μ`-column, sent by (13.3.c) into a nonzero `η`-column
        obtain ⟨j, hj, rfl⟩ := hyp.sSet_reducible_eq_muColumnSum hG hζ hζirr
        rcases hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief with hclean | ⟨-, hflip⟩
        · rw [hclean j hj, OddOrder.RepresentationTheory.inner_sum_left]
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hyp.eta_orthonormal l i j ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj h.2)]
        · have h2lt : 2 < hyp.p := by have := hyp.three_le_p; omega
          set j1 : Fin hyp.p := ⟨1, hyp.p_prime.one_lt⟩ with hj1
          set j2 : Fin hyp.p := ⟨2, h2lt⟩ with hj2
          have hj10 : j1 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          have hj20 : j2 ≠ ⟨0, hyp.p_prime.pos⟩ := by
            intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          -- route through the other nonzero column `j' ≠ 0, j' ≠ j`
          obtain ⟨j', hj'0, hjj'⟩ : ∃ j' : Fin hyp.p,
              j' ≠ ⟨0, hyp.p_prime.pos⟩ ∧ j ≠ j' := by
            rcases eq_or_ne j j1 with rfl | hne1
            · exact ⟨j2, hj20, fun h => absurd (congrArg Fin.val h) (by norm_num)⟩
            · exact ⟨j1, hj10, hne1⟩
          rw [hflip j j' hj hj'0 hjj',
            OddOrder.RepresentationTheory.ClassFunction.inner_neg_left,
            OddOrder.RepresentationTheory.inner_sum_left]
          rw [Finset.sum_eq_zero fun l _ => by
            rw [hyp.eta_orthonormal l i j' ⟨0, hyp.p_prime.pos⟩, if_neg (fun h => hj'0 h.2)]]
          exact neg_zero
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open scoped FiniteInduce in
/-- **(4.1)+(5.3.b)+(13.3.c) honest supply for the `tau1S_induce_inner_eta_col_zero` field**
(issue 2035/9094): for *any* irreducible `θ ∈ Irr H` (`H = PC`, `P ⊄ Ker θ`) — the induction
`Ind_{PC}^S θ` may be irreducible or a `μ`-column — the `τ₁`-image is orthogonal to the
`η`-column `0`.  Composition of the `ℤ[𝒮]` membership (`induce_H_mem_zSpan_S`) with the
mixed-family column-`0` orthogonality (`tau1S_ofHonest_zSpan_inner_eta_col_zero`). -/
theorem Hypothesis.tau1S_ofHonest_induce_inner_eta_col_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (i : Fin hyp.q)
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
      (hyp.tau1S_ofHonest hG hnoV chief
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0 := by
  haveI := hyp.finiteG
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1S_ofHonest_zSpan_inner_eta_col_zero hG hnoV chief i
      (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a) with the `P`-witness** (issue 2035 更新 #22, the guard the (13.5)
consumers thread): the inducing linear character `θ` of the nonzero `μ`-column sum
`μ_j = Ind_{PC}^S θ` has `P ⊄ Ker θ` — i.e. `μ_j ∈ 𝒮₁` in the sense of (13.5).

**Proof.**  `mu_j_isIndPC` supplies `θ`; if `P ⊆ Ker θ` then `P ⊆ Ker μ_j` by the elementary
half of (1.6.a) (`subsetCharacterKernel_induce_of_subgroupOf`, `P ⊴ S`).  But `μ_j ∈ 𝒮(H₀)`
(`mu_colSum_mem_sOf_H0`) is induced from an `S'`-source `χ ∈ 𝒳` with `P ⊄ Ker χ`, and the
converse of (1.6.a) ([Is] 2.21, `mem_characterKernel_of_mem_characterKernel_induce`, `S' ⊴ S`)
pushes `P ⊆ Ker μ_j` down to `P ⊆ Ker χ` — contradiction. -/
theorem Hypothesis.mu_j_isIndPC_not_ker [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
        ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
            Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel θ) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨θ, hθirr, hθ1, hμeq⟩ := hyp.mu_j_isIndPC hG j hj
  refine ⟨θ, hθirr, hθ1, hμeq, fun hker => ?_⟩
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- the `S'`-level source: `μ_j = Ind_{HU}^S χ`, `χ ∈ 𝒳` (so `P ⊄ Ker χ`)
  obtain ⟨χ, hχ, hμeq'⟩ := OddOrder.Peterfalvi.S11.mem_sOf.mp
    (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hHUnorm : (OddOrder.Peterfalvi.S11.huSub data).Normal := by
    rw [OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data]
    infer_instance
  -- `P ⊴ S`, realised in `↥S`
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
    have hPle : hyp.P ≤ hyp.S := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
    Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
  -- (1.6.a) forward: `P ⊆ Ker θ` pushes up to `P ⊆ Ker μ_j`
  have hkerInd : OddOrder.Peterfalvi.S03.SubsetCharacterKernel
      ((hyp.P.subgroupOf hyp.S : Subgroup ↥hyp.S) : Set ↥hyp.S)
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) :=
    OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf hPH θ hker
  -- rewrite the induced character as the `S'`-stage induction
  have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
      = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
          (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) := by
    rw [← hμeq, hμeq']
    exact OddOrder.Peterfalvi.S11.induceHU_eq_induce data _
  -- contradict `χ ∈ 𝒳`: `P (in HU) ⊆ Ker χ`
  apply hχ.1
  intro x hx
  have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
    have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data) := hx
    have hPeq : data.H = hyp.P := by
      show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rw [hPeq] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub data)
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)) := by
    rw [← hInd_eq]
    exact hkerInd hxP
  have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
    χ.isIrreducible x.2 hxkerInd
  simpa using h

/-- **Peterfalvi (13.3.c), the `T`-side signs `δ'_i = 1`** — the δ'-half of the
`delta_eq_one` field.

**Assembled** (issue 2035, T-side reopening after the 9096 bundle split): the anchor row is
the (4.4)-at-`T` base sign (`NuGridSupplyData.deltaPrime_zero_eq_one`); off the anchor it is
`deltaPrime_eq_one_of_ne_zero_T` (`TSideDegrees.lean`) — the (4.3.d)-at-`T` congruence
`ν_{i0}(1) = δ'_i + p·a` against the **proven** Frobenius congruence `v ≡ 1 (mod p)`
(`v_modEq_one`) and the **proven** (13.3.a)-at-`T` per-entry degree `nu_apply_one_eq_v`
(via `card_Q_eq_qp`, the unconditional `|Q| = q^p`), exactly as `delta_eq_one_of_ne_zero`
runs the `S`-side.  The ν-grid facts enter through the sorried producer `nuGridSupply`
(a-owned canonical threading, issue 9096) — the assembly itself is sorry-free. -/
theorem Hypothesis.deltaPrime_eq_one_T [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) : hyp.deltaPrime i = 1 := by
  by_cases hi : i = ⟨0, hyp.q_prime.pos⟩
  · rw [hi]
    exact (hyp.nuGridSupply _hG).deltaPrime_zero_eq_one
  · exact hyp.deltaPrime_eq_one_of_ne_zero_T _hG (hyp.nuGridSupply _hG) i hi

open scoped FiniteInduce in
/-- **The λ-free core producer** (issue 9094 RULING 案 A): every field of
`CharacterDegreeCore` from the landed engines — `τ₁ = tau1S_ofHonest` with its five guarded
field supplies, the (13.3.a) `𝒮₁`-witnessed `μ`-facts (`mu_j_isIndPC_not_ker`,
`tau1S_ofHonest_mu_col_eta_col_one`), the (13.3.c) signs (`delta_eq_one_S` +
the ν-gated `deltaPrime_eq_one_T`), and the (13.3.c) column formula
(`tau1S_ofHonest_muColumn_formula`). -/
noncomputable def Hypothesis.characterDegreeCore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    CharacterDegreeCore hyp where
  tau1S := hyp.tau1S_ofHonest hG hnoV chief
  tau1T := hyp.indT
  tau1S_apply_induce_sub := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_apply_induce_sub hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_inner_induce := fun θ θ' hθ hθ' hθP hθ'P =>
    hyp.tau1S_ofHonest_inner_induce hG hnoV chief θ θ' hθ hθ' hθP hθ'P
  tau1S_induce_mem_ZIrr := fun θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_mem_ZIrr hG hnoV chief θ hθ hθP
  tau1S_induce_inner_eta := fun i j θ hθ hθP hind =>
    hyp.tau1S_ofHonest_induce_inner_eta hG hnoV chief i j θ hθ hθP hind
  tau1S_induce_inner_eta_col_zero := fun i θ hθ hθP =>
    hyp.tau1S_ofHonest_induce_inner_eta_col_zero hG hnoV chief i θ hθ hθP
  mu_col_tau1_eta_col_one := by
    obtain ⟨j, δ, θold, hj, hδ, -, -, -, hform⟩ :=
      hyp.tau1S_ofHonest_mu_col_eta_col_one hG hnoV chief
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨j, δ, θ, hj, hδ, hθirr, hθ1, hθP, hμeq, hform⟩
  mu_j_linear_induced := fun j hj => by
    obtain ⟨θ, hθirr, hθ1, hμeq, hθP⟩ := hyp.mu_j_isIndPC_not_ker hG j hj
    exact ⟨θ, hθirr, hθ1, hθP, hμeq⟩
  delta_eq_one :=
    ⟨fun j => hyp.delta_eq_one_S hG j, fun i => hyp.deltaPrime_eq_one_T hG i⟩
  mu_tau1_formula := hyp.tau1S_ofHonest_muColumn_formula hG hnoV chief

/-- **The λ-free core, unconditionally** (issue 9094 RULING 案 A): `CharacterDegreeCore` is
inhabited for every (13.1) hypothesis — the (12.x) no-type-V fact supplies `hnoV`, and a chief
factor datum always exists. -/
theorem Hypothesis.characterDegreeCore_nonempty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (CharacterDegreeCore hyp) := by
  haveI := hyp.finiteG
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupS hG)
  exact ⟨hyp.characterDegreeCore hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) chief⟩

open scoped FiniteInduce in
/-- **The conditional λ-cluster producer** (issue 9094 RULING 案 A, the (13.3.b) conditional
branch): a linear `θ ∈ Irr H` (`H = PC`) with `P ⊄ Ker θ` whose induction `Ind_{PC}^S θ` is
irreducible packages into `LambdaClusterData` — the degree is `[S:H]·1 = uq`
(`H_index_eq_uq`). -/
theorem Hypothesis.lambdaClusterData_of_irr_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ) (hθ1 : θ 1 = 1)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    Nonempty (LambdaClusterData hyp) := by
  haveI := hyp.finiteG
  refine ⟨⟨ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ, hind, ?_, θ, hθ, hθ1, rfl, ?_⟩⟩
  · rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one,
      hyp.H_index_eq_uq hG]
  · obtain ⟨x, hxP, hxker⟩ := Set.not_subset.mp hθP
    exact ⟨x, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxP), hxker⟩

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The (13.5)/(7.6) datum for `(S, H^#)` with a chosen `𝒮₁`-base** (issue 2035 更新
#22/#24): the `H_sharp_hypothesis76` mirror through `hypothesis76OfDadeBase`, pinning
`ζ₀ = Ind_{PC}^S φ₀` for a *given* `φ₀` — Peterfalvi's per-application base choice ((13.5)
takes `ζ₀ ∈ 𝒮₁`, i.e. `P ⊄ Ker φ₀`; the (13.5.a/b/c) coefficient computations then convert
`(ζ_i − ζ₀)^{τ₁} ↔ Ind_S^G` through the *guarded* `CharacterDegreeCore` fields, which the
trivial-base instance cannot). -/
noncomputable def H_sharp_hypothesis76_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase
    (H_sharp_hypothesis71 hG hyp) ?_ hyp.H ?_ ?_ rfl φ₀
  · exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).toDadeIsometryData.isDadeIsometry
  · have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  · intro l h hh
    by_cases h1 : h = 1
    · subst h1; simpa using hyp.H.one_mem
    · have hsh : h ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
        OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hh, h1⟩
      exact (OddOrder.Peterfalvi.S04.mem_sharp.mp (S_normalizes_H_sharp hG hyp l hsh)).1

open scoped FiniteInduce in
/-- **The chosen-base `(S, H^#)` family pins `ζ₀ = Ind_{PC}^S φ₀`.** -/
theorem H_sharp_hypothesis76_base_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S)) :
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) := by
  unfold H_sharp_hypothesis76_base
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase_zeta_zero _ _ _ _ _ _ _

open scoped Classical in
open scoped FiniteInduce in
set_option maxHeartbeats 800000 in
/-- **The (7.7.a) coefficients of `λ^{τ₁}` at the distinguished index, over a chosen
`𝒮₁`-base** (Peterfalvi (13.5)/(13.6), the guarded restatement of `lambda_tau1_cCoeff` —
issue 2035 更新 #22/#24, issue 9094 案 A): with the (7.6) family based at `ζ₀ = Ind φ₀`
(`φ₀ ∈ 𝒮₁`, i.e. `P ⊄ Ker φ₀`), `c_{i₁} = 1` at `λ`'s index and every other
**`P`-nonkernel** coefficient vanishes.  The `P`-kernel coefficients stay undetermined — they
are absorbed into the `α` of (13.5.a), exactly as in the book.

The τ₁-conversions run through the *guarded* `CharacterDegreeCore` fields
(`tau1S_apply_induce_sub` + `tau1S_inner_induce`), which is possible precisely because the
base and all indices considered are `P`-nonkernel. -/
theorem lambda_tau1_cCoeff_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda)
    (i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))
    (hi₁eq : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda) :
    (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i = 0) := by
  classical
  obtain ⟨θl, hθlirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ := lam.lambda_induced_from_PC_linear
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S
    with hKdef
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  -- λ's inducing character has `P ⊄ Ker` (the pointwise witness, set-negated)
  have hθlP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θl) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  -- `K ≅ H` abelian ⟹ all family degrees are `[S:K]` ⟹ `d ≡ 1`
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).d j = 1 := by
    intro j
    have h := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- distinct induced characters of `K` are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          ≠ ClassFunction.induce K (ψ : ClassFunction ↥K ℂ) →
      ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce K
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.S) (H := K) g _
    rw [← h1, heq]
  -- the guarded field bridges, in the `K`-spelling
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) →
      core.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ' hθP hθ'P
    have h := core.tau1S_apply_induce_sub _ _ θ.2 θ'.2 hθP hθ'P
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hfield2 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) →
      ClassFunction.inner (core.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)))
          (core.tau1S (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)))
        = ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ' hθP hθ'P
    have h := core.tau1S_inner_induce _ _ θ.2 θ'.2 hθP hθ'P
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  -- λ and the base φ₀, transported into the `K`-spelling
  have hθlK : ∃ θK : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      lam.lambda = ClassFunction.induce K (θK : ClassFunction ↥K ℂ) ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θK : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    exact ⟨⟨θl, hθlirr⟩, hlamEq, hθlP⟩
  obtain ⟨θlK, hlamK, hθlKP⟩ := hθlK
  have hφ₀K : ∃ φK : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
        = ClassFunction.induce K (φK : ClassFunction ↥K ℂ) ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (φK : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    exact ⟨φ₀, rfl, hφ₀P⟩
  obtain ⟨φK, hφ₀eq, hφKP⟩ := hφ₀K
  -- the base value: `ζ₀ = Ind φK`, orthogonal to `λ`
  have hζ0 : (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce K (φK : ClassFunction ↥K ℂ) := by
    rw [H_sharp_hypothesis76_base_zeta_zero hG hyp φ₀, ← hφ₀eq]
  have hz0lam : ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta 0)
      lam.lambda = 0 := by
    rw [hζ0, hlamK]
    exact hInd0 φK θlK (by rw [← hlamK, ← hφ₀eq]; exact hφ₀ne)
  -- the generic coefficient computation for a `P`-nonkernel family index
  have hcoeff : ∀ (j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))
      (θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j
          = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) j
        = ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta j) lam.lambda
          - ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta 0)
              lam.lambda := by
    intro j θ hζj hθP
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) j
        = ClassFunction.inner
            ((H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
              ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp j))
            (core.tau1S lam.lambda) from rfl]
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
        = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    have hψ : ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp j : ClassFunction ↥hyp.S ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (φK : ClassFunction ↥K ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 j, one_smul, hζj, hζ0]
    rw [hψ, ← hfield1 θ φK hθP hφKP, map_sub, ClassFunction.inner_sub_left, hlamK,
      hfield2 θ θlK hθP hθlKP, hfield2 φK θlK hφKP hθlKP, ← hlamK, ← hζj, ← hζ0]
  -- conjunct 1: `c_{i₁} = ⟨λ,λ⟩ − ⟨ζ₀,λ⟩ = 1 − 0`
  have hlamIrr : ClassFunction.inner lam.lambda lam.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨lam.lambda, lam.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨lam.lambda, lam.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [hcoeff i₁ θlK (by rw [hi₁eq, hlamK]) hθlKP, hi₁eq, hlamIrr, hz0lam, sub_zero]
  · intro i hine hiP
    obtain ⟨θi, hθi⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced i
    -- the S-level `P ⊄ Ker ζ_i` pushes down to the H-level source witness ((1.6.a) forward)
    have hθiP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θi : ClassFunction ↥K ℂ)) := by
      intro hker
      apply hiP
      haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
        have hPle' : hyp.P ≤ hyp.S := by
          rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle').mpr ?_
        rw [hyp.P_eq_SF]
        exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
      have hPle : hyp.P.subgroupOf hyp.S ≤ K := by
        rw [hKJ]
        exact Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
      have hfwd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (A := hyp.P.subgroupOf hyp.S) (H := K) hPle
        (θi : ClassFunction ↥K ℂ) hker
      rw [hθi]
      exact hfwd
    rw [hcoeff i θi hθi hθiP, hz0lam, sub_zero]
    have hne : ClassFunction.induce K (θi : ClassFunction ↥K ℂ)
        ≠ ClassFunction.induce K (θlK : ClassFunction ↥K ℂ) := by
      intro heq
      apply hine
      apply (H_sharp_hypothesis76_base hG hyp φ₀).zeta_injective
      rw [hθi, heq, hi₁eq, hlamK]
    rw [hθi, hlamK]
    exact hInd0 θi θlK hne

open scoped Classical in
open scoped FiniteInduce in
set_option maxHeartbeats 800000 in
/-- **The (7.7.a) coefficients of `η₁₀` vanish at `P`-nonkernel indices, over a chosen
`𝒮₁`-base** (Peterfalvi (13.7), the guarded restatement of `eta10_cCoeff_orthogonal` — issue
2035 更新 #22/#24, issue 9094 案 A): with the (7.6) family based at `ζ₀ = Ind φ₀` (`φ₀ ∈ 𝒮₁`),
every **`P`-nonkernel** `η₁₀`-coefficient vanishes — `τ₁`-images of `𝒮₁`-members are
orthogonal to the `η`-column `0` (`tau1S_induce_inner_eta_col_zero`, (4.1)+(5.3.b)+(13.3.c)).
The `P`-kernel coefficients are absorbed into the `α` of (13.5.a). -/
theorem eta10_cCoeff_base_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ))) :
    ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta10 i = 0 := by
  classical
  intro i hiP
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S
    with hKdef
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76_base hG hyp φ₀).d i = 1 := by
    have h := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- the guarded field bridges, in the `K`-spelling
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) →
      core.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ' hθP hθ'P
    have h := core.tau1S_apply_induce_sub _ _ θ.2 θ'.2 hθP hθ'P
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  -- the (4.1)/(5.3.b)+(13.3.c) column-`0` field, at the `η₁₀`-index
  have hfieldEta : ∀ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) →
      ClassFunction.inner hyp.eta10
        (core.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) = 0 := by
    rw [hKJ]
    intro θ hθP
    have h := core.tau1S_induce_inner_eta_col_zero ⟨1, hyp.q_prime.one_lt⟩ _ θ.2 hθP
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  -- the base `ζ₀ = Ind φK` in the `K`-spelling
  have hφ₀K : ∃ φK : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
        = ClassFunction.induce K (φK : ClassFunction ↥K ℂ) ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (φK : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    exact ⟨φ₀, rfl, hφ₀P⟩
  obtain ⟨φK, hφ₀eq, hφKP⟩ := hφ₀K
  have hζ0 : (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce K (φK : ClassFunction ↥K ℂ) := by
    rw [H_sharp_hypothesis76_base_zeta_zero hG hyp φ₀, ← hφ₀eq]
  -- the index source, with the H-level witness from the S-level guard ((1.6.a) forward)
  obtain ⟨θi, hθi⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced i
  have hθiP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf K : Set ↥K) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θi : ClassFunction ↥K ℂ)) := by
    intro hker
    apply hiP
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle' : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle').mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPle : hyp.P.subgroupOf hyp.S ≤ K := by
      rw [hKJ]
      exact Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hfwd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      (A := hyp.P.subgroupOf hyp.S) (H := K) hPle
      (θi : ClassFunction ↥K ℂ) hker
    rw [hθi]
    exact hfwd
  -- assemble: both τ₁-image terms are `η`-column-`0` orthogonal
  rw [show (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta10 i
      = ClassFunction.inner
          ((H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
            ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i))
          hyp.eta10 from rfl]
  rw [show (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
      = (H_sharp_hypothesis71 hG hyp).τ from rfl,
    H_sharp_tau_eq_induce hG hyp]
  have hψ : ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i : ClassFunction ↥hyp.S ℂ)
      = ClassFunction.induce K (θi : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (φK : ClassFunction ↥K ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul, hθi, hζ0]
  rw [hψ, ← hfield1 θi φK hθiP hφKP, map_sub, ClassFunction.inner_sub_left]
  have h1 : ClassFunction.inner
      (core.tau1S (ClassFunction.induce K (θi : ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta θi hθiP,
      star_zero]
  have h2 : ClassFunction.inner
      (core.tau1S (ClassFunction.induce K (φK : ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta φK hφKP,
      star_zero]
  rw [h1, h2, sub_zero]

open scoped FiniteInduce in
/-- **The `λ^{τ₁}`-value off the `H^#`-saturation is `±` an `η`-column sum** (Peterfalvi
(13.9.a) first step — the Core/λ-cluster restatement of
`lambda_tau1_apply_eq_of_not_mem_H_sat`, issue 9094 案 A): `(μ_j − λ)^{τ₁} = Ind_S^G(μ_j − λ)`
vanishes off `(H^#)^G` — both are induced from linear characters of `H = PC` with `P ⊄ Ker`
(the Core `mu_col` witness and the λ-cluster witness thread the *guarded*
`tau1S_apply_induce_sub`), so the difference is `H^#`-supported — whence
`λ^{τ₁}(x) = δ ∑_i η_{i1}(x)` there by the (13.3.c) column formula. -/
theorem lambda_tau1_apply_eq_of_not_mem_H_sat_core [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) {x : G}
    (hx : x ∉ OddOrder.GroupTheory.conjClassSet (sharpSubgroup hyp.H)) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      core.tau1S lam.lambda x
        = (δ : ℂ) * ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := by
  classical
  obtain ⟨j, δ, θμ, -, hδ, hθμirr, hθμ1, hθμP, hμInd, hμτ⟩ := core.mu_col_tau1_eta_col_one
  obtain ⟨θl, hθlirr, hθl1, hlamEq, x₀, hx₀P, hx₀ker⟩ := lam.lambda_induced_from_PC_linear
  have hθlP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θl) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hdiff : core.tau1S (∑ i : Fin hyp.q, hyp.mu i j) - core.tau1S lam.lambda
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) := by
    rw [← map_sub, hμInd, hlamEq]
    have h := core.tau1S_apply_induce_sub θμ θl hθμirr hθlirr hθμP hθlP
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hsupp : ∀ w : ↥hyp.S, (w : G) ∉ sharpSubgroup hyp.H →
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) w = 0 := by
    intro w hw
    rw [ClassFunction.sub_apply]
    by_cases hwH : (w : G) ∈ hyp.H
    · have hw1 : (w : G) = 1 := by
        by_contra hne
        exact hw ⟨hwH, fun h1 => hne (Set.mem_singleton_iff.mp h1)⟩
      have hw1' : w = 1 := Subtype.ext hw1
      subst hw1'
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθμ1, hθl1, sub_self]
    · rw [OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)),
        OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)), sub_self]
  have hvan : ClassFunction.induce hyp.S
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) x = 0 :=
    OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet _ hsupp hx
  refine ⟨δ, hδ, ?_⟩
  have hdv := congrArg (fun f : ClassFunction G ℂ => f x) hdiff
  simp only [ClassFunction.sub_apply] at hdv
  rw [hvan] at hdv
  have hμv := congrArg (fun f : ClassFunction G ℂ => f x) hμτ
  simp only [ClassFunction.smul_apply, smul_eq_mul,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] at hμv
  have hlamv : core.tau1S lam.lambda x = core.tau1S (∑ i : Fin hyp.q, hyp.mu i j) x :=
    (sub_eq_zero.mp hdv).symm
  exact hlamv.trans hμv

open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package, Core/λ-cluster form** ((13.4) character gate — the
core/lam restatement of `tSide_theta_package_of_not_caseB`, issue 9094 案 A).

**Residual (precisely named, mirrors the legacy sorried gate)**: the T-side (13.3.b)/(13.3.c)
package — `𝒯` contains an irreducible `θ` induced from a linear character of `K = QD`, the
`ν`-row τ₁-formula, and the pairwise orthogonality of `η`, `λ^{τ₁}`, `θ^{τ₁}`.  Gated on the
ν-side grid supply (`nuGridSupply`) and the `T`-side coherence — the swap-instance of the
S-side (13.3) engines (issue 9013 追記⁶). -/
theorem tSide_theta_package_of_not_caseB_core [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r r' : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (core.tau1S lam.lambda) θG = 0 := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.4), Core/λ-cluster form** (the core/lam restatement of
`lambda_forces_T_caseB`, issue 9094 案 A): if `𝒮` contains the λ-cluster (a degree-`uq`
character induced from a linear character of `PC`), then case (9.7.b) holds for `T`, with
`D = 1`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`.  The witnesses of the Core `mu_col` field and
the λ-cluster thread the guarded `tau1S_apply_induce_sub`/`tau1S_induce_inner_eta`. -/
theorem lambda_forces_T_caseB_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  haveI := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, r', δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB_core hG core lam hne
  -- S-side (13.3) data with the `𝒮₁`-witnesses.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hthetaLP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel thetaL) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  obtain ⟨j₀, δ, θlin, -, hδ, hθlinirr, hθlin1, hθlinP, hμeq, hμtau⟩ :=
    core.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hαsupp : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (lam.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = core.tau1S lam.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← core.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr hthetaLP hθlinP,
      map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (core.tau1S lam.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := core.tau1S_induce_inner_eta i j thetaL hthetaLirr hthetaLP
      (hlamEq ▸ lam.lambda_irreducible)
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (core.tau1S lam.lambda) θG r' ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0

open scoped FiniteInduce in
/-- **The `𝒮₁`-λ-witness predicate** (Pf (13.3.b)): `𝒮` contains a `uq`-degree `PC`-induced
irreducible — a linear `θ ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ` whose induction is
irreducible.  Its existence is the conditional branch of the (13.3.b) dichotomy
(`lambdaClusterData_of_irr_witness` packages it into `LambdaClusterData`); its failure is the
Galois/`C = ⊥` case. -/
def LambdaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)

open scoped FiniteInduce in
/-- **The no-λ (Galois) branch of the `T`-side (13.4) facts** (issue 9094 RULING §4, faithful
sorried bridging): if `𝒮` contains no `uq`-degree `PC`-induced irreducible (`¬ LambdaWitness`),
then by Pf (13.3.b) `M = S` is in case (9.7.b) with `C = ⊥`, `u = (p^q−1)/(p−1)` (Galois); the
`T`-mirror of (13.9)–(13.12) then forces `D = ⊥`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`.

Gated on the unbuilt `T`-mirror engine (RULING §4: `q < p` — Coq `PFsection14` `ltqp` — with
(13.13)-on-`T` and (13.12)-on-`T`).  This is the honest replacement, in the no-λ branch, of the
overstated unconditional λ-cluster of `character_degree_analysis`. -/
theorem T_caseB_facts_no_lambda [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (_hnolam : ¬ LambdaWitness hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)/(14.4), `T`-side case (9.7.b), unconditional via the (13.3.b) dichotomy**
(issue 9094 RULING 案 A + §4): `D = ⊥`, `v = (q^p−1)/(q−1)` and `|Q| = q^p`, obtained **without**
the overstated unconditional λ-cluster of the legacy `character_degree_analysis`.

Case-splits on `LambdaWitness hyp` (Pf (13.3.b) dichotomy): the λ-branch builds the honest
`LambdaClusterData` (`lambdaClusterData_of_irr_witness`) and runs `lambda_forces_T_caseB_core`
against the unconditional `CharacterDegreeCore`; the no-λ branch is the (Galois) T-mirror
`T_caseB_facts_no_lambda`.  This is the b-side export the (14.9) type-II endpoint
(`S16 … T_side_caseB_facts`) cites in place of the uninhabitable monolithic producer. -/
theorem T_caseB_facts_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨core⟩ := hyp.characterDegreeCore_nonempty hG
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    obtain ⟨lam⟩ := hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind
    exact lambda_forces_T_caseB_core hG core lam
  · exact T_caseB_facts_no_lambda hG hyp hlam

open OddOrder.Peterfalvi.S11 in
/-- **(9.8.c) with the regular seed exposed**: the degree-`qu` irreducible member of `𝒮(H₀C)` from
Peterfalvi (9.8.c) is `Ind_{HU}^M(Ind_{HC}(hcPsi θ))` for a *regular* seed `θ` (nontrivial on every
Clifford summand `caseA.Hpart i`, hence `θ ≠ 1`).  Identical parity argument to
`caseA_exists_irreducible_sOf_H0C` (`exists_regular_not_reducible_of_odd` on `Xθ \ Xmu`,
`|Xμ| = p-1`, `u·|Xθ| = (p-1)^q`, `u` odd, `p-1` even), but returns the *witnessing* `θ` (needed to
recover the `Ind_{HC}(linear)` shape and route it through `isIndHC_of_source_eq_induce_hcPsi` to a
`LambdaWitness`; the bare existence hides `θ`). -/
theorem caseA_exists_irreducible_witnessed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 ∧
      (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IsIrreducibleCharacter (induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ).toClassFunction)) := by
  classical
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H := ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  have hp1_even : Even (chief.p - 1) := by
    obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
    exact ⟨k, by omega⟩
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  have hcard : (↑Xmu : Set (ClassFunction ↥(huSub data) ℂ)).ncard = chief.p - 1 := by
    rw [Set.ncard_coe_finset]; exact caseA_Xmu_card_eq caseA hG
  have hcount : chars.u * (↑Xθ : Set (ClassFunction ↥(huSub data) ℂ)).ncard
      = (chief.p - 1) ^ data.q := by
    rw [Set.ncard_coe_finset]; exact oXtheta_count caseA
  obtain ⟨ζ, hζ, hζn⟩ := exists_regular_not_reducible_of_odd Xθ.finite_toSet
    (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hcard hcount
    (Nat.sub_pos_of_lt chief.p_prime.one_lt) hp1_even (u_odd hG chars) data.nontrivial.2.1.two_le
  rw [Finset.mem_coe, hXθ, Finset.mem_image] at hζ
  obtain ⟨θ, hθ, rfl⟩ := hζ
  have hreg := (Finset.mem_filter.mp hθ).2
  have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
  refine ⟨θ, hnt, hreg, ?_⟩
  by_contra h
  refine hζn ?_
  simp only [Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image]
  exact ⟨⟨θ, hθ, rfl⟩, h⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b) caseB forward — the Singer/Galois branch witness**: an irreducible member `χ` of
the `S`-instance family `𝒮(H₀ ⊔ C')` in Clifford case (b) is a `LambdaWitness` (a `uq`-degree
`PC`-linear induced irreducible).  Mirrors the caseA branch of `S_caseB_facts_no_lambda` (which
produces the witness unconditionally from the (9.8.c) regular seed); here the source is the given
`χ = Ind_{HU} ζ`, and the reverse (13.3.a)-for-irr characterization is the pair (`C'`-kernel)
`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`: `ζ ∈ 𝒳(H₀C')` irreducible equals
`Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character (`λ` trivial on `C'`).  Flattening
(`isIndHC_of_source_eq_induce_hcPsiPair`) and the `HC.map subtype = (PC).subgroupOf S` transport
(`hcRealized_map_subtype_eq`, `toTypesIIIIIIVSetupS_cSub_eq_C`) give the linear
`θ' ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ'` whose induction (`= χ`) is irreducible.

Stated with `chief`/`caseB`/`χ`-membership as explicit arguments (no `set` inside): the caseB
branch of `S_caseB_facts_no_lambda` is then a one-line call. -/
theorem lambdaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData (hyp.mkSection11CharacterDataS hG chief))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    LambdaWitness hyp := by
  classical
  haveI := hyp.finiteG
  -- Extract the source `ζ ∈ 𝒳(H₀C')` of the given irreducible `χ = Ind_{HU} ζ`.  Done *before*
  -- any `let`, and re-cast to `data`-form so every downstream term is uniform (a `set` here would
  -- revert/rename `ζ`; the extraction stays clean because `hχmem` names the explicit terms).
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupS hG
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  -- (1) the reverse (13.3.a)-for-irr characterization: `ζ = Ind_{HC}(hcPsiPair θ̄ λ)`, `θ̄ ≠ 1`.
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  -- (2) flatten `induceHU(Ind_{HC}(hcPsiPair)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
  -- (3) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)`, which (converse (1.6.a)) pushes to
    -- `P ⊆ Ker ζ`, contradicting `ζ ∈ 𝒳` (`P = H ⊄ Ker ζ`).  Mirrors `mu_j_isIndPC_not_ker`.
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
      Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hPH θ' hker
    have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b) caseA — the unconditional branch witness**: in Clifford case (a) a `LambdaWitness`
exists unconditionally (independent of the given `χ`).  The (9.8.c) degree-`qu` irreducible member
`Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` for a *regular* seed `θ̄` (`caseA_exists_irreducible_witnessed`) is
`Ind_{PC}^S(linear irr)`: flattening (`isIndHC_of_source_eq_induce_hcPsi`) and the
`HC.map subtype = (PC).subgroupOf S` transport give the linear `θ' ∈ Irr(H.subgroupOf S)` with
`P ⊄ Ker θ'` whose induction is irreducible.

Stated with `chief`/`caseA` explicit (no `set` inside), so the caseA branch of
`S_caseB_facts_no_lambda` is a one-line call and hbridge stays `set`-free (a `set` there would
split `chief` and desync the branch calls). -/
theorem lambdaWitness_of_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData (hyp.mkSection11CharacterDataS hG chief)) :
    LambdaWitness hyp := by
  classical
  haveI := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupS hG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  -- (1) the regular seed `θbar` with irreducible `induceHU(Ind_{HC}(hcPsi θbar))`.
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  -- (2) the `S'`-source `ζ' = Ind_{HC}(hcPsi θbar) ∈ 𝒳(H₀C)` (`P ⊄ Ker ζ'`).
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  -- (3) flatten `induceHU(Ind_{HC}(hcPsi)) = Ind_{HC.map subtype}(ψ)`, `ψ` linear irr.
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.S) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.S).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  -- (4) transport `HC.map subtype = (PC).subgroupOf S`.
  have hHeq : data.H = hyp.P := by show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.H.subgroupOf hyp.S := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `P ⊄ Ker θ'`: else `P ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ')` pushes to `P ⊆ Ker ζ'`,
    -- contradicting `ζ' ∈ 𝒳` (`P = H ⊄ Ker ζ'`).  Mirrors `mu_j_isIndPC_not_ker`.
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal := by
      have hPle : hyp.P ≤ hyp.S := by
        rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr ?_
      rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    have hPH : hyp.P.subgroupOf hyp.S ≤ hyp.H.subgroupOf hyp.S :=
      Subgroup.subgroupOf_mono hyp.S (show hyp.P ≤ hyp.H from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hPH θ' hker
    have hInd_eq : ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxP : (x : ↥hyp.S) ∈ hyp.P.subgroupOf hyp.S := by
      have hx' : x ∈ (data.H.subgroupOf hyp.S).subgroupOf (huSub data) := hx
      rw [hHeq] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.S) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.S).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxP
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-λ (Galois) branch of the `S`-side (13.3.b) facts** (issue 9094 RULING §2, faithful
sorried bridging): if `𝒮` contains no `uq`-degree `PC`-induced irreducible (`¬ LambdaWitness`),
then by Pf (13.3.b) `M = S` is in case (9.7.b) with `C = ⊥` and `u = (p^q−1)/(p−1)` — the Galois
case.

Assembled from the §9-generic `caseB_of_no_irreducible_sOf_H0Cprime` (sorry-free) through the
S15↔S11 `Section11CharacterData` SOf-identification: an irreducible member of the `S`-instance
family `𝒮(H₀ ⊔ C')` is (13.3.a-style) a `uq`-degree `PC`-linear induced irreducible, i.e. a
`LambdaWitness`, and the `chars.C`/`chars.u` conclusion transports to `hyp.C`/`hyp.u`
(`toTypesIIIIIIVSetupS_cSub_eq_C`).  That identification is the deep (13.3.b) forward bridge
(S15↔S11, multi-session); until it lands this is the honest, precisely-named gate. -/
theorem S_caseB_facts_no_lambda [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnolam : ¬ LambdaWitness hyp) :
    hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  haveI := hyp.finiteG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  -- **(13.3.b) forward, the one isolated genuine gate**: an irreducible member of the `S`-instance
  -- family `𝒮(H₀ ⊔ C')` is a `uq`-degree `PC`-linear induced irreducible — a `LambdaWitness`.
  -- (The reducible members are `Ind_{HC}` linear by `caseB_reducible_sOf_H0_isIndHC`; the
  -- irreducible ones — the `λ`-candidates — need the (13.3.a)-for-irr characterization, the
  -- multi-session S15↔S11 assembly.)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → LambdaWitness hyp := by
    intro χ _hχmem _hχirr
    -- `set`-free case split: a `set data`/`set chars` here would split the (externally obtained)
    -- `chief` into a folded copy plus a stray `chief✝`, desyncing `_hχmem` from `caseB`.  Both
    -- branches are `set`-free standalone witnesses (`lambdaWitness_of_caseA` / `_of_caseB_member`),
    -- each doing its own `let data` internally, so hbridge passes one pristine `chief`.
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · -- **caseA**: a `LambdaWitness` exists unconditionally (ignore `χ`) — the (9.8.c) degree-`qu`
      -- irreducible `Ind_{HU}^S(Ind_{HC}(hcPsi θ̄))` is `Ind_{PC}^S(linear irr)`.
      obtain ⟨caseA⟩ := hA
      exact lambdaWitness_of_caseA hG hyp chief caseA
    · -- **caseB** (Singer/Galois, `U` irreducible on `H̄`): the given irreducible `χ = Ind_{HU} ζ`
      -- (`ζ ∈ 𝒳(H₀C')`) is `Ind_{HC}(hcPsiPair θ̄ λ)` for a linear pair character
      -- (`caseB_xiOf_H0Cprime_eq_induce_hcPsiPair`); `lambdaWitness_of_caseB_member` flattens and
      -- transports it to the `Ind_{PC}(linear irr)` = `LambdaWitness` shape.
      obtain ⟨caseB⟩ := hB
      exact lambdaWitness_of_caseB_member hG hyp chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataS hG chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataS hG chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnolam (hbridge χ hmem hirr)
  obtain ⟨-, hCbot, hufull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataS hG chief) hno
  refine ⟨?_, ?_⟩
  · -- `chars.C = cSub = hyp.C` (`toTypesIIIIIIVSetupS_cSub_eq_C`)
    rw [← hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]
    exact hCbot
  · -- transport `chars.u = (chief.p^data.q − 1)/(chief.p − 1)` to `hyp.u = (p^q − 1)/(p − 1)`
    rw [← hyp.mkSection11CharacterDataS_u_eq hG chief, hufull, hyp.chiefFactorS_p_eq hG chief,
      hyp.toTypesIIIIIIVSetupS_q_eq hG]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.b) dichotomy, the `S`-side keystone producer** (issue 9094 RULING 案 A/§2):
either `𝒮` contains the honest λ-cluster (`Nonempty (LambdaClusterData hyp)`), or `M = S` is in
the Galois case (`C = ⊥`, `u = (p^q−1)/(p−1)`).  This is the producer every λ-independent
consumer of the legacy `character_degree_analysis` threads: the λ-branch supplies the
`LambdaClusterData` (against the unconditional `CharacterDegreeCore`), the no-λ branch supplies
the (13.10)-arithmetic inputs `C = ⊥ ∧ u = full`.

The case-split is `LambdaWitness hyp` (`Classical.em`): the λ-branch is
`lambdaClusterData_of_irr_witness`, the no-λ branch is `S_caseB_facts_no_lambda`. -/
theorem lambdaCluster_or_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LambdaClusterData hyp) ∨
      (hyp.C = ⊥ ∧ hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  by_cases hlam : LambdaWitness hyp
  · obtain ⟨θ, hθ, hθ1, hθP, hind⟩ := hlam
    exact Or.inl (hyp.lambdaClusterData_of_irr_witness hG θ hθ hθ1 hθP hind)
  · exact Or.inr (S_caseB_facts_no_lambda hG hyp hlam)

/-! ## The (13.3.b)-at-`T` θ-witness dichotomy

The `T`-side mirror of the `LambdaWitness` machinery (`S15_CharacterDegreeSupply`): a
`ThetaWitness` is a `vp`-degree `QD`-linear induced irreducible of `T` — Peterfalvi's
"`𝒯` contains an irreducible character of degree `vp` induced from a linear character of
`QD`" ((13.3.b)/(13.4)).  Its failure forces the Galois case `D = ⊥`,
`v = (q^p−1)/(q−1)` (`T_caseB_facts_no_theta`); contrapositively, `¬(13.4-caseB)` produces
the witness (`thetaWitness_of_not_caseB`) — the θ of the (13.4) proof. -/

open scoped FiniteInduce in
/-- **The `T`-side (13.3.b) witness shape**: a linear character of `K = QD` not containing
`Q` in its kernel whose induction to `T` is irreducible (a `vp`-degree `QD`-linear induced
irreducible).  Mirror of `LambdaWitness`. -/
def ThetaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseB forward — the Singer/Galois branch witness**: an irreducible
member `χ` of the `T`-instance family `𝒮_T(H₀ ⊔ C')` in Clifford case (b) is a
`ThetaWitness`.  Mirror of `lambdaWitness_of_caseB_member`. -/
theorem Hypothesis.thetaWitness_of_caseB_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {χ : ClassFunction ↥hyp.T ℂ}
    (hχmem : χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime))
    (_hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ThetaWitness hyp := by
  classical
  haveI := hyp.finiteG
  rw [Section11CharacterData.SOf_eq] at hχmem
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  have hχmem' : χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hχmem
  obtain ⟨ζ, hζxi, hχeq⟩ := mem_sOf.mp hχmem'
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  obtain ⟨θbar, lam, hnt, hlamC', hζeq⟩ :=
    caseB_xiOf_H0Cprime_eq_induce_hcPsiPair (data := data) (chief := chief) caseB hζxi
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsiPair (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar) (lam := lam) (ζ' := ζ) hζeq
  have hsupeq : (data.H : Subgroup G) ⊔ cSub data chief = hyp.K := by
    rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.K.subgroupOf hyp.T := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      = induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hψeq]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · -- `Q ⊄ Ker θ'`: else `Q ⊆ Ker(Ind θ') = Ker(Ind_{HU} ζ)` pushes to `Q ⊆ Ker ζ`,
    -- contradicting `ζ ∈ 𝒳` (`Q = H ⊄ Ker ζ`).
    intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal := by
      have hQle : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
    have hQK : hyp.Q.subgroupOf hyp.T ≤ hyp.K.subgroupOf hyp.T :=
      Subgroup.subgroupOf_mono hyp.T (show hyp.Q ≤ hyp.K from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hQK θ' hker
    have hInd_eq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
        = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζxi.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ζ.isIrreducible x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hχeq ▸ _hχirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.3.b)-at-`T` caseA — the unconditional branch witness**: in Clifford case (a) a
`ThetaWitness` exists unconditionally.  Mirror of `lambdaWitness_of_caseA`. -/
theorem Hypothesis.thetaWitness_of_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataT hG hvd chief)) :
    ThetaWitness hyp := by
  classical
  haveI := hyp.finiteG
  let data := hyp.toTypesIIIIIIVSetupT hG hvd
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal (data := data) chief
  obtain ⟨θbar, hnt, hreg, hirr⟩ :=
    caseA_exists_irreducible_witnessed (data := data) (chief := chief) caseA hG
  have hθ₀ := caseA_regular_inflation_inertia_eq (data := data) (chief := chief) caseA θbar hreg
  have hζ'mem := hcZeta_mem_xiOf (data := data) chief θbar hnt hθ₀
  obtain ⟨ψ, hψirr, hψ1, hψeq⟩ :=
    isIndHC_of_source_eq_induce_hcPsi (M := hyp.T) (data := data) (chief := chief)
      (θbar := θbar)
      (ζ' := ⟨ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)) (hcPsi chief θbar),
        hcZeta_irreducible (data := data) chief θbar hθ₀⟩) rfl
  have hwit : induceHU data (ClassFunction.induce (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
      (hcPsi chief θbar).toClassFunction)
      = ClassFunction.induce ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        hyp.T).subgroupOf (huSub data)).map (huSub data).subtype) ψ := hψeq
  have hsupeq : (data.H : Subgroup G) ⊔ cSub data chief = hyp.K := by
    rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf
      (huSub data)).map (huSub data).subtype = hyp.K.subgroupOf hyp.T := by
    rw [hcRealized_map_subtype_eq (data := data) chief, hsupeq]
  let θ' := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ
  have hθ'def : θ' = ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ := rfl
  have hindeq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      = induceHU data (ClassFunction.induce (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
        (hcPsi chief θbar).toClassFunction) := by
    rw [hθ'def, OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ, ← hwit]
  refine ⟨θ', ?_, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθ'def, ClassFunction.compHom_apply, map_one, hψ1]
  · intro hker
    haveI hHUnorm : (huSub data).Normal := by
      rw [huSub_eq_derivedInG_subgroupOf data]; infer_instance
    haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal := by
      have hQle : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
    have hQK : hyp.Q.subgroupOf hyp.T ≤ hyp.K.subgroupOf hyp.T :=
      Subgroup.subgroupOf_mono hyp.T (show hyp.Q ≤ hyp.K from le_sup_left)
    have hkerInd := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
      hQK θ' hker
    have hInd_eq : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
        = ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) := by
      rw [hindeq]; exact induceHU_eq_induce data _
    apply hζ'mem.1
    intro x hx
    have hxQ : (x : ↥hyp.T) ∈ hyp.Q.subgroupOf hyp.T := by
      have hx' : x ∈ (data.H.subgroupOf hyp.T).subgroupOf (huSub data) := hx
      rw [show (data.H : Subgroup G) = hyp.Q from hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxkerInd : (x : ↥hyp.T) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (huSub data) (ClassFunction.induce (hInHu data ⊔
          ((chief.H0 ⊔ cSub data chief).subgroupOf hyp.T).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction)) := by
      rw [← hInd_eq]; exact hkerInd hxQ
    have h := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (hcZeta_irreducible (data := data) chief θbar hθ₀) x.2 hxkerInd
    simpa using h
  · rw [hindeq]; exact hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The no-θ (Galois) branch of the `T`-side (13.3.b) facts**: if `𝒯` contains no
`vp`-degree `QD`-induced irreducible (`¬ ThetaWitness`), then `M = T` is in case (9.7.b)
with `D = ⊥` and `v = (q^p−1)/(q−1)`.  Mirror of `S_caseB_facts_no_lambda` (whose
`hbridge`/`hno` shape it reproduces verbatim on the `T`-instance). -/
theorem Hypothesis.T_caseB_facts_no_theta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hnotheta : ¬ ThetaWitness hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) := by
  haveI := hyp.finiteG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hbridge : ∀ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ → ThetaWitness hyp := by
    intro χ _hχmem _hχirr
    rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataT hG hvd chief) with hA | hB
    · obtain ⟨caseA⟩ := hA
      exact hyp.thetaWitness_of_caseA hG hvd chief caseA
    · obtain ⟨caseB⟩ := hB
      exact hyp.thetaWitness_of_caseB_member hG hvd chief caseB _hχmem _hχirr
  have hno : ¬ ∃ χ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    fun ⟨χ, hmem, hirr⟩ => hnotheta (hbridge χ hmem hirr)
  obtain ⟨-, hDbot, hvfull⟩ :=
    caseB_of_no_irreducible_sOf_H0Cprime hG
      (hyp.mkSection11CharacterDataT hG hvd chief) hno
  refine ⟨?_, ?_⟩
  · rw [← hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    exact hDbot
  · rw [← hyp.mkSection11CharacterDataT_v_eq hG hvd chief, hvfull,
      hyp.chiefFactorT_p_eq hG hvd chief, hyp.toTypesIIIIIIVSetupT_q_eq hG hvd]

/-- **The (13.4) θ-supply**: if `T` is *not* in the (9.7.b) Galois case (the `_hne` of
`tSide_theta_package_of_not_caseB_core`), then `𝒯` contains a `vp`-degree `QD`-linear
induced irreducible.  Contrapositive of `T_caseB_facts_no_theta` + the unconditional
`card_Q_eq_qp` (the third conjunct is always true, so `_hne` reduces to
`¬(D = ⊥ ∧ v = full)`). -/
theorem Hypothesis.thetaWitness_of_not_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) : ThetaWitness hyp := by
  by_contra hno
  obtain ⟨hD, hv⟩ := hyp.T_caseB_facts_no_theta hG hno
  exact hne ⟨hD, hv, hyp.card_Q_eq_qp hG⟩


end OddOrder.Peterfalvi.S15
