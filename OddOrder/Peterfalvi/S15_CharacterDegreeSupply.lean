import OddOrder.Peterfalvi.S15_CaseACoherence

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

end OddOrder.Peterfalvi.S15
