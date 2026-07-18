import OddOrder.Peterfalvi.S14_MaximalI.Hypothesis

/-!
# Peterfalvi (12.3)-(12.5) — orthogonality and rho-constancy

Split from the former monolithic `OddOrder.Peterfalvi.S14_MaximalI` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (12.3)--(12.5): orthogonality and rho-constancy -/

/-- **§8 thickening kernel containment.**  The subgroup `R(x) = supportKernel L M X x` of
Peterfalvi (8.14) is always contained in `L_F = maxNilpotentNormalHall L`: on the
escaping-centralizer set it is `L_F ⊓ C_G(x) ≤ L_F`, and elsewhere it is `⊥`. -/
theorem supportKernel_le_maxNilpotentNormalHall (L M : Subgroup G) (X : Set G) (x : G) :
    supportKernel L M X x ≤ maxNilpotentNormalHall L := by
  classical
  unfold supportKernel
  split
  · exact inf_le_left
  · exact bot_le

/-- **The type-I thickened cover lands in `L_F`-conjugates.**  If a support set `X` is contained in
`L_F = maxNilpotentNormalHall L`, then every element of the thickened support
`⋃_{z ∈ X} (z R(z))^G` (`thickenedSupport L M X`) is conjugate to an element of `L_F`: the coset
factor `z ∈ X ⊆ L_F` and the kernel factor `r ∈ R(z) ⊆ L_F`
(`supportKernel_le_maxNilpotentNormalHall`) multiply into `L_F`, which `𝒞_G` saturates.

This is the structural heart of the (12.17) type-I covering: the thickening `R(z)` never escapes
`L_F`, so the `A_1(L) = (L_F)#` cover by thickened sets is, up to conjugacy, a cover by `L_F`. -/
theorem thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall
    {L M : Subgroup G} {X : Set G} (hX : X ⊆ (maxNilpotentNormalHall L : Set G)) :
    thickenedSupport L M X ⊆ conjClassSet (maxNilpotentNormalHall L : Set G) := by
  rintro y ⟨z, hz, hyz⟩
  obtain ⟨w, hw, g, hgwy⟩ := hyz
  obtain ⟨r, hr, hzrw⟩ := hw
  have hzMF : z ∈ maxNilpotentNormalHall L := hX hz
  have hrMF : r ∈ maxNilpotentNormalHall L :=
    supportKernel_le_maxNilpotentNormalHall L M X z (SetLike.mem_coe.mp hr)
  have hwMF : w ∈ maxNilpotentNormalHall L := hzrw ▸ mul_mem hzMF hrMF
  exact ⟨w, SetLike.mem_coe.mpr hwMF, g, hgwy⟩

/- (Removed 2026-07-02, lane b: `dadeSupport_subset_conjClassSet_maxNilpotentNormalHall_of_frobenius`
claimed `Ã(L) ⊆ 𝒞_G(L_F)` for Frobenius `L`.  Under the faithful per-`x` signalizer of (8.14)
(`S10.ftSupportKernel`) this is **false** when `A(L)` has an escaping element `x`: the coset factor
`r ∈ R(x) = C_{(N[x])_F}(x)` is a nontrivial `σ(L)′`-element commuting with `x`, so `x·r` has order
divisible by a `σ(L)′`-prime and is not conjugate into `L_F`.  It was provable only against the
earlier self-based kernel pin `R(x) = C_{L_F}(x)` (issue 8021 unfaithfulness); no consumers. -/

/-- **`(L_F)^#`-conjugates of non-conjugate maximals are disjoint** — the clean M̃-geometry core.
`(L_F)^# = M_σ(L)^# = sigmaSharp L ⊆ M̃(L)` (`sigmaSharp_subset_Mtilde`), and the thickened
`M̃`-covers of non-conjugate maximals have disjoint conjugacy-saturations
(`conjClassSet_Mtilde_disjoint`, BG 14.5(b)).  `sorry`-free; no Frobenius needed (this is the
identity-free part, `sigmaSharp` excludes `1`). -/
theorem conjClassSet_sigmaSharp_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L1 L2 : Subgroup G}
    (hL1 : L1 ∈ maximalSubgroups G) (hL2 : L2 ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L1 L2) :
    Disjoint (conjClassSet (OddOrder.BG.Ch4.S14.sigmaSharp L1))
      (conjClassSet (OddOrder.BG.Ch4.S14.sigmaSharp L2)) :=
  Disjoint.mono
    (conjClassSet_mono (OddOrder.BG.Ch4.S14.sigmaSharp_subset_Mtilde hG _))
    (conjClassSet_mono (OddOrder.BG.Ch4.S14.sigmaSharp_subset_Mtilde hG _))
    (OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG
      (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hL1 hL2 hnc)

/-- The difference `φ − φ̄` of a constituent is supported in `A(L)` (each constituent is supported in
`A(L) ∪ {1}` by `data.supported`, and `(φ − φ̄)(1) = 0` by equal degree — `φ(1)` is real). -/
theorem constituentDiff_support_subset {L : Subgroup G} {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  haveI := hyp.finiteG
  have hsupp_eq : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj) x ≠ 0 := hx
  have hxsupp : x ∈ (φ : ClassFunction ↥L ℂ).support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases data.supported φ hφ hxsupp with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
    exact hx0 (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hd, star_natCast,
      sub_self])

/-- Evaluation of a finite sum of class functions at a point (the eval map is additive). -/
private theorem classFunction_sum_apply {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) (g : H) : (∑ i ∈ s, F i) g = ∑ i ∈ s, (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)/(12.5) input**: each member `χ = Ind_H^L θ` of `S` vanishes on `L − H`.
`H = L_F` is normal in `L` (`maxNilpotentNormalHall_subgroupOf_normal`, the Fitting subgroup `L_F`),
so the induced character is supported on `H` (`ClassFunction.induce_eq_zero_of_not_mem_normal`).
This
is the "the elements of `S` vanish on `L − H`" step of the constant-on-coset conclusions of
(12.4)/(12.5) (`ψ(xh) = β(xh) + γ(xh) = γ(x)`, the `β ∈ ℂ[S]` part vanishing off `H`). -/
theorem Sset_vanishes_off_H {L : Subgroup G} (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.Sset) {x : ↥L} (hxH : (x : G) ∉ hyp.H) : χ x = 0 := by
  haveI := hyp.finiteG
  obtain ⟨θ, _, hχ_eq⟩ := hχ
  haveI hnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  have hxmem : x ∉ (hyp.typeI.typeF.H).subgroupOf L :=
    fun hcon => hxH (Subgroup.mem_subgroupOf.mp hcon)
  rw [hχ_eq]
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hxmem

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The full-member difference is `A₁`-supported**: for `χ ∈ S` (`χ = Ind_H^L θ`, `H = L_F`),
`supp(χ − χ̄) ⊆ A₁(L) = (L_F)^#` — `χ` vanishes off the normal `H` (`Sset_vanishes_off_H`) and
`χ(1) = ∑_φ φ(1)` is real, so the difference also vanishes at `1`.  The `Ã₁`-side support input
of the mixed (8.18.c) application in (12.3). -/
theorem Sset_diff_support_subset_A1 {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    (chi - chi.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (A1 L PeterfalviType.I) L := by
  haveI := hyp.finiteG
  intro x hx
  rw [ClassFunction.mem_support] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hxA1
  apply hx
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply]
  by_cases hxH : (x : G) ∈ hyp.typeI.typeF.H
  · -- inside `H` but not in `A₁ = H^#`: forced `x = 1`, where the difference cancels.
    have hx1 : x = 1 := by
      by_contra hx1
      refine hxA1 ((Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr ?_, fun h => ?_⟩)
      · change (x : G) ∈ maxNilpotentNormalHall L
        rw [← hyp.typeI.typeF.H_eq]
        exact hxH
      · rw [Set.mem_singleton_iff] at h
        exact hx1 (Subtype.ext h)
    subst hx1
    have hreal : star (chi 1) = chi 1 := by
      rw [data.decomp, classFunction_sum_apply, star_sum]
      refine Finset.sum_congr rfl fun φ _ => ?_
      obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
      rw [hd, star_natCast]
    rw [hreal, sub_self]
  · rw [Sset_vanishes_off_H hyp data.chi_mem hxH, star_zero, sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `τ`-image of a full-member difference is `Ã₁`-supported** (the (2.11) restriction
computation): `supp((χ−χ̄)^τ) ⊆ Ã₁(L) = ftThickenedSupport L A₁`.  The difference is
`A₁`-supported (`Sset_diff_support_subset_A1`), so `τ` agrees with the `A₁`-restricted Dade map
(`Hypothesis.dadeMap_restrict_apply`), whose image vanishes off the restricted Dade support —
which is exactly the faithful thickened `A₁`-support (the per-point kernels agree,
`ftSupportKernel_restrict`). -/
theorem Sset_diff_tau_support_subset_ftThickenedA1 {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) :
    (hyp.tau (chi - chi.conj)).support ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (A1 L PeterfalviType.I) := by
  haveI := hyp.finiteG
  have hA₁A : A1 L PeterfalviType.I ⊆ typeIA L hyp.typeI :=
    OddOrder.Peterfalvi.S10.A1_subset_typeIA L hyp.typeI
  have hA₁norm : ∀ (l : ↥L) ⦃a : G⦄, a ∈ A1 L PeterfalviType.I →
      (l : G) * a * (l : G)⁻¹ ∈ A1 L PeterfalviType.I := fun l _ ha =>
    OddOrder.Peterfalvi.S10.A1_conj_mem L OddOrder.GroupTheory.PeterfalviType.I l.2 ha
  have hsuppA1 := Sset_diff_support_subset_A1 hyp data
  have hsuppA : (chi - chi.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := fun x hx => hA₁A (hsuppA1 hx)
  -- `τ(χ−χ̄)` is the (A₁-restricted) Dade map value on the A₁-supported difference
  have htau_eq : hyp.tau (chi - chi.conj)
      = (hyp.dadeData.dade.restrict hA₁A hA₁norm).dadeMap (k := ℂ)
          ⟨chi - chi.conj, (ClassFunction.mem_supportedSubmodule).mpr hsuppA1⟩ := by
    rw [OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_restrict_apply]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hsuppA
  -- the restricted Dade support is the faithful thickened `A₁`-support
  have hsub : (hyp.dadeData.dade.restrict hA₁A hA₁norm).dadeSupport ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (A1 L PeterfalviType.I) := by
    intro g hg
    obtain ⟨a, h, hh, hconj⟩ :=
      (hyp.dadeData.dade.restrict hA₁A hA₁norm).mem_dadeSupport_iff.mp hg
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨a.1, a.2, ?_⟩
    rw [OddOrder.GroupTheory.mem_conjClassSet]
    refine ⟨a.1 * h, ⟨h, ?_, rfl⟩, c, hc⟩
    rw [SetLike.mem_coe, OddOrder.Peterfalvi.S10.ftSupportKernel_restrict hA₁A a.2,
      ← hyp.dadeData.H_eq_ftSupportKernel ⟨a.1, hA₁A a.2⟩]
    exact hh
  intro g hg
  rw [ClassFunction.mem_support, htau_eq] at hg
  by_contra hgnot
  refine hg (OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_zero_of_not_mem_dadeSupport
    ((hyp.dadeData.dade.restrict hA₁A hA₁norm).isDadeMap_dadeMap) _ g
    (fun hmem => hgnot (hsub hmem)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `τ`-image of a constituent difference is `Ã`-supported**:
`supp((φ−φ̄)^τ) ⊆ Ã(L) = ftThickenedSupport L A(L)`.  The difference is `A`-supported
(`constituentDiff_support_subset`), `τ` is the Dade map there, and the (8.15) faithful Dade
support is `Ã(L)` (`dadeSupport_eq_ftThickenedSupport`). -/
theorem constituentDiff_tau_support_subset_ftThickenedA {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj)).support ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (typeIA L hyp.typeI) := by
  haveI := hyp.finiteG
  have hsupp := constituentDiff_support_subset data hφ
  have htau_eq : hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj)
      = hyp.dadeData.dade.dadeMap (k := ℂ)
          ⟨(φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj,
            (ClassFunction.mem_supportedSubmodule).mpr hsupp⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      hyp.dadeData.dade (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hsupp
  intro g hg
  rw [ClassFunction.mem_support, htau_eq] at hg
  by_contra hgnot
  refine hg (OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_zero_of_not_mem_dadeSupport
    hyp.dadeData.dade.isDadeMap_dadeMap _ g ?_)
  rw [hyp.dadeData.dadeSupport_eq_ftThickenedSupport]
  exact hgnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.18.c), the (12.3) instantiation**: for non-conjugate type-I maximals
`L₁, L₂`, either `Ã(L₁) ∩ Ã₁(L₂) = ∅` or `Ã(L₂) ∩ Ã₁(L₁) = ∅` — the mixed asymmetric
disjointness, from the S10 `ftThickenedSupport_mixed_disjoint_of_nonconjugate` (issue 0096). -/
theorem nonconjugate_thickened_mixed_disjoint_or_swap {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2) :
    Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
        (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)) ∨
      Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (typeIA L2 hyp2.typeI))
        (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (A1 L1 PeterfalviType.I)) := by
  haveI := hyp1.finiteG
  have hncTS : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L2 L1 := fun hc =>
    hnot_conj hc.symm
  rcases OddOrder.Peterfalvi.S10.ftThickenedSupport_mixed_disjoint_of_nonconjugate hG
    hyp2.maximal hyp1.maximal hyp2.typeI hyp1.typeI hncTS with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Mixed inner vanishing from the (8.18.c) disjointness**: when `Ã(L₁) ∩ Ã₁(L₂) = ∅`, every
`L₁`-constituent difference image is orthogonal to every `L₂`-full-member difference image.  The
two support computations + disjointly-supported orthogonality. -/
theorem constituent_fullDiff_inner_zero_of_disjoint {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
      (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)))
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau (chi2 - chi2.conj)) = 0 := by
  haveI := hyp1.finiteG
  exact ClassFunction.inner_eq_zero_of_disjoint_support
    (Disjoint.mono (constituentDiff_tau_support_subset_ftThickenedA hyp1 data1 hφ1)
      (Sset_diff_tau_support_subset_ftThickenedA1 hyp2 data2) hdisj)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Dade `τ` commutes with complex conjugation on `A(L)`-supported functions** — the
coefficientwise form of `S07.dadeIntegralCharacterMap_mapRingEquiv_comm` (the map's value at a
Dade-support point is an evaluation, and `0` elsewhere, so conjugating coefficients commutes).
The τ/conj commutation input of the (12.3) bar-trick ((5.9.b) via
`CharacterDifferenceImage.nu_eq_mu_conj`). -/
theorem tau_conj_of_supported {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {f : ClassFunction ↥L ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) :
    hyp.tau f.conj = (hyp.tau f).conj := by
  haveI := hyp.finiteG
  have h1 : f.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv f := by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  have h2 : (hyp.tau f).conj
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.tau f) := by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  rw [h1, h2]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    hyp.dadeData.dade _ _ hf

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(12.2.b) conjugate pairing of the difference-image block `R₁(φ)`**: `ν_φ = μ̄_φ`, so
`(φ − φ̄)^τ = ε·(μ_φ − μ̄_φ)`.  The (5.9.b) pairing `CharacterDifferenceImage.nu_eq_mu_conj`,
with the τ/conj commutation supplied by `tau_conj_of_supported` on the `A(L)`-supported
difference (`constituentDiff_support_subset`). -/
theorem R1cdi_nu_eq_mu_conj {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (R1cdi data hφ).nuClassFunction = (R1cdi data hφ).muClassFunction.conj := by
  haveI := hyp.finiteG
  exact OddOrder.Peterfalvi.S07.CharacterDifferenceImage.nu_eq_mu_conj _
    (tau_conj_of_supported hyp (constituentDiff_support_subset data hφ))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(12.2.b) cross-constituent image orthogonality**: for distinct constituents `φ ≠ φ'` of
one `χ ∈ S`, the images `(φ−φ̄)^τ` and `(φ'−φ̄')^τ` are orthogonal.  The Dade isometry
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) reduces to the `L`-side pairing
`⟨φ−φ̄, φ'−φ̄'⟩`, where the four irreducibles are pairwise distinct: `φ ≠ φ'` is given,
conjugation is injective, and `φ̄ ≠ φ'`, `φ ≠ φ̄'` are `data.conj_not_mem` — so all four
`Irr L` deltas vanish. -/
theorem constituentDiff_tau_inner_eq_zero_of_ne {L : Subgroup G} [Finite G]
    {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφ' : φ' ∈ data.constituents) (hne : φ ≠ φ') :
    ClassFunction.inner
        (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj))
        (hyp.tau ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)) = 0 := by
  haveI := hyp.finiteG
  classical
  -- The two differences form a supported generating family.
  have hSsupp : ∀ s ∈ ({((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj),
      ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)} :
        Set (ClassFunction ↥L ℂ)), s.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    rcases hs with rfl | hs
    · exact constituentDiff_support_subset data hφ
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact constituentDiff_support_subset data hφ'
  -- The Dade isometry transports the pairing to `L`.
  refine Eq.trans (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hSsupp
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))) ?_
  -- `L`-side: expand into four `Irr L` deltas, all off-diagonal.
  have hcross : ∀ a c : IrreducibleCharacter ↥L,
      ClassFunction.inner (a : ClassFunction ↥L ℂ) (c : ClassFunction ↥L ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have h2 : φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    exact data.conj_not_mem φ' hφ' φ hφ
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h).symm
  have h3 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ' := by
    intro h
    exact data.conj_not_mem φ hφ φ' hφ'
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h)
  have h4 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ
      ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    have hcf := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h
    simp only [OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter] at hcf
    exact hne (IrreducibleCharacter.ext
      (by rw [← ClassFunction.conj_conj (φ : ClassFunction ↥L ℂ), hcf,
        ClassFunction.conj_conj]))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ',
    hcross φ φ', hcross φ _, hcross _ φ', hcross _ _,
    if_neg hne, if_neg h2, if_neg h3, if_neg h4]
  norm_num

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Two-family variant of the constituent-difference block orthogonality.**  Same `L`, but the two
constituents may come from *different* members `χ₁, χ₂ ∈ S`: given `φ ∈ S(χ₁)`, `φ' ∈ S(χ₂)` with
the
distinctness conditions `φ ≠ φ'`, `φ ≠ φ̄'`, `φ̄ ≠ φ'` (a caller supplies these from
`χ₁ ∉ {χ₂, χ̄₂}`
+ disjoint constituents), the Dade images of the signed differences are orthogonal.

Generalizes `constituentDiff_tau_inner_eq_zero_of_ne` (same `χ`, where the conditions come from
`data.conj_not_mem`) — the cross-family input for the same-`L` `R(χ₁) ⊥ R(χ₂)` orthogonality.  The
proof is identical: the supports of both differences lie in `A(L)`
(`constituentDiff_support_subset`,
one per data), the Dade map is an isometry there, and the `L`-side pairing expands into four
off-diagonal `Irr L` deltas. -/
theorem constituentDiff_tau_inner_eq_zero_of_ne_across {L : Subgroup G} [Finite G]
    {hyp : Hypothesis L} {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data1.constituents)
    (hφ' : φ' ∈ data2.constituents) (hne : φ ≠ φ')
    (h2 : φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ')
    (h3 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ') :
    ClassFunction.inner
        (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj))
        (hyp.tau ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)) = 0 := by
  haveI := hyp.finiteG
  classical
  have hSsupp : ∀ s ∈ ({((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj),
      ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)} :
        Set (ClassFunction ↥L ℂ)), s.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    rcases hs with rfl | hs
    · exact constituentDiff_support_subset data1 hφ
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact constituentDiff_support_subset data2 hφ'
  refine Eq.trans (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hSsupp
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))) ?_
  have hcross : ∀ a c : IrreducibleCharacter ↥L,
      ClassFunction.inner (a : ClassFunction ↥L ℂ) (c : ClassFunction ↥L ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have h4 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ
      ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    have hcf := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h
    simp only [OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter] at hcf
    exact hne (IrreducibleCharacter.ext
      (by rw [← ClassFunction.conj_conj (φ : ClassFunction ↥L ℂ), hcf,
        ClassFunction.conj_conj]))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ',
    hcross φ φ', hcross φ _, hcross _ φ', hcross _ _,
    if_neg hne, if_neg h2, if_neg h3, if_neg h4]
  norm_num

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S07.CharacterDifferenceImage in
/-- **The (12.3) bar-trick descent, one-sided core.**  If `Ã(L₁) ∩ Ã₁(L₂) = ∅` ((8.18.c)),
each `L₁`-constituent image is orthogonal to each `L₂`-constituent image.

Peterfalvi's (12.3) argument: with `X = (χ₂−χ̄₂)^{τ₂}`, the support disjointness gives
`⟨(φ₁−φ̄₁)^{τ₁}, X⟩ = 0` (`constituent_fullDiff_inner_zero_of_disjoint`); writing
`(φ₁−φ̄₁)^{τ₁} = ε·(μ₁ − μ̄₁)` ((5.9.b), `R1cdi_nu_eq_mu_conj`) and using `X̄ = −X`
(`tau_conj_of_supported`) plus the integrality of the Fourier coefficients of `X ∈ ℤ[Irr G]`
(`mem_ZIrr_inner_int`) yields `⟨μ₁, X⟩ = ⟨μ̄₁, X⟩ = −conj ⟨μ₁, X⟩ = −⟨μ₁, X⟩`, so
`⟨μ₁, X⟩ = 0`.  Expanding `X = ∑_{φ∈S(χ₂)} (φ−φ̄)^{τ₂}`, the cross-`φ` block orthogonality
(`constituentDiff_tau_inner_eq_zero_of_ne` + the (4.1) member lemma) lets `μ₁` pair
nontrivially with at most one block, so every single summand `⟨μ₁, (φ₂−φ̄₂)^{τ₂}⟩` vanishes,
not just the sum — and likewise for `ν₁ = μ̄₁`. -/
theorem constituent_diffImage_inner_zero_of_disjoint {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
      (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)))
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  haveI := hyp1.finiteG
  classical
  set X : ClassFunction G ℂ := hyp2.tau (chi2 - chi2.conj) with hX
  -- (a) `χ₂ − χ̄₂ = ∑_{φ∈S(χ₂)} (φ − φ̄)`, hence `X = ∑ (φ−φ̄)^{τ₂}` and `X ∈ ℤ[Irr G]`.
  have hdiff_eq : chi2 - chi2.conj = ∑ φ ∈ data2.constituents,
      ((φ : ClassFunction ↥L2 ℂ) - (φ : ClassFunction ↥L2 ℂ).conj) := by
    have hconj : (∑ φ ∈ data2.constituents, (φ : ClassFunction ↥L2 ℂ)).conj
        = ∑ φ ∈ data2.constituents, (φ : ClassFunction ↥L2 ℂ).conj := by
      ext g
      rw [ClassFunction.conj_apply, classFunction_sum_apply, classFunction_sum_apply, star_sum]
      exact Finset.sum_congr rfl fun φ _ => by rw [ClassFunction.conj_apply]
    conv_lhs => rw [data2.decomp]
    rw [hconj, ← Finset.sum_sub_distrib]
  have hXsum : X = ∑ φ ∈ data2.constituents,
      hyp2.tau ((φ : ClassFunction ↥L2 ℂ) - (φ : ClassFunction ↥L2 ℂ).conj) := by
    rw [hX, hdiff_eq, map_sum]
  have hfsupp : (chi2 - chi2.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp2.ambientA L2 := by
    rw [hdiff_eq]
    intro x hx
    rw [ClassFunction.mem_support, classFunction_sum_apply] at hx
    obtain ⟨φ, hφm, hne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact constituentDiff_support_subset data2 hφm (ClassFunction.mem_support.mpr hne0)
  have hXZIrr : X ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [hX]
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp2.dadeData.dade hyp2.hconj hfsupp ?_
    rw [hdiff_eq]
    exact Submodule.sum_mem _ fun φ _ => Submodule.sub_mem _ φ.mem_ZIrr
      (OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L2) φ).mem_ZIrr
  -- (b) `⟨a, X⟩` is real for every irreducible `a` (integer Fourier coefficient).
  have hreal : ∀ a : IrreducibleCharacter G,
      star (ClassFunction.inner (a : ClassFunction G ℂ) X)
        = ClassFunction.inner (a : ClassFunction G ℂ) X := by
    intro a
    obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int a hXZIrr
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (a : ClassFunction G ℂ), hm,
      star_star, star_intCast]
  -- (c) `X̄ = −X` (τ₂ commutes with conjugation on the supported difference).
  have hXconj : X.conj = -X := by
    rw [hX, ← tau_conj_of_supported hyp2 hfsupp, ClassFunction.conj_sub,
      ClassFunction.conj_conj, ← neg_sub, map_neg]
  -- (d) the bar-trick: `⟨μ₁, X⟩ = ⟨ν₁, X⟩ = 0`.
  have hfull : ClassFunction.inner
      (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj)) X = 0 :=
    constituent_fullDiff_inner_zero_of_disjoint hyp1 hyp2 hdisj data1 hφ1 data2
  rw [(R1cdi data1 hφ1).image_eq_signedDifference] at hfull
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference] at hfull
  rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left,
    ClassFunction.inner_sub_left] at hfull
  have hs1 : (((R1cdi data1 hφ1).sign : ℤ) : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (R1cdi data1 hφ1).sign_ne_zero
  have heq : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X
      = ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfull).resolve_left hs1)
  have hnux : ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X
      = -star (ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X) := by
    rw [R1cdi_nu_eq_mu_conj data1 hφ1]
    conv_lhs => rw [← ClassFunction.conj_conj X]
    rw [OddOrder.RepresentationTheory.inner_conj_conj, hXconj,
      ClassFunction.inner_neg_right, star_neg]
  have hmux : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X = 0 := by
    have h1 : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X
        = -(ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X) := by
      conv_lhs => rw [heq, hnux, hreal (R1cdi data1 hφ1).mu]
    linear_combination h1 / 2
  have hnux0 : ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X = 0 :=
    heq.symm.trans hmux
  -- (e) descent: an irreducible orthogonal to `X` is orthogonal to the `φ₂`-summand.
  have hcrossG : ∀ a c : IrreducibleCharacter G,
      ClassFunction.inner (a : ClassFunction G ℂ) (c : ClassFunction G ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have hdescend : ∀ a : IrreducibleCharacter G,
      ClassFunction.inner (a : ClassFunction G ℂ) X = 0 →
      ClassFunction.inner (a : ClassFunction G ℂ)
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
    intro a haX
    by_contra ht2
    -- a nonzero pairing with the block of `φ'` puts `a` in its two-element image set.
    have hmem : ∀ φ' (hm : φ' ∈ data2.constituents),
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) ≠ 0 →
        (a : ClassFunction G ℂ) ∈ (R1cdi data2 hm).imageSet := by
      intro φ' hm hne0
      rw [(R1cdi data2 hm).image_eq_signedDifference] at hne0
      simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
        OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference] at hne0
      rw [← Int.cast_smul_eq_zsmul ℂ, OddOrder.RepresentationTheory.inner_smul_right,
        ClassFunction.inner_sub_right] at hne0
      have hsub : ClassFunction.inner (a : ClassFunction G ℂ)
            ((R1cdi data2 hm).muClassFunction)
          - ClassFunction.inner (a : ClassFunction G ℂ)
            ((R1cdi data2 hm).nuClassFunction) ≠ 0 :=
        fun h => hne0 (by rw [h, mul_zero])
      rw [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.mem_imageSet_iff]
      by_cases hc1 : a = (R1cdi data2 hm).mu
      · exact Or.inl (congrArg (fun c : IrreducibleCharacter G =>
          (c : ClassFunction G ℂ)) hc1)
      by_cases hc2 : a = (R1cdi data2 hm).nu
      · exact Or.inr (congrArg (fun c : IrreducibleCharacter G =>
          (c : ClassFunction G ℂ)) hc2)
      exfalso
      exact hsub (by rw [hcrossG a _, hcrossG a _, if_neg hc1, if_neg hc2, sub_zero])
    have hmem2 := hmem φ2 hφ2 ht2
    have hothers : ∀ φ' ∈ data2.constituents, φ' ≠ φ2 →
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) = 0 := by
      intro φ' hm' hne'
      by_contra htne'
      have hmem' := hmem φ' hm' htne'
      have hsd : ClassFunction.inner ((R1cdi data2 hm').signedDifference)
          ((R1cdi data2 hφ2).signedDifference) = 0 := by
        rw [← (R1cdi data2 hm').image_eq_signedDifference,
          ← (R1cdi data2 hφ2).image_eq_signedDifference]
        exact constituentDiff_tau_inner_eq_zero_of_ne data2 hm' hφ2 hne'
      have hcontra := inner_eq_zero_of_signedDifference_inner_zero_of_mem
        (R1cdi data2 hm') (R1cdi data2 hφ2) hsd hmem' hmem2
      rw [hcrossG a a, if_pos rfl] at hcontra
      exact one_ne_zero hcontra
    have hsum0 : ∑ φ' ∈ data2.constituents,
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) = 0 := by
      rw [← OddOrder.RepresentationTheory.inner_sum_right, ← hXsum]
      exact haX
    rw [Finset.sum_eq_single_of_mem φ2 hφ2 hothers] at hsum0
    exact ht2 hsum0
  -- (f) conclude: expand `(φ₁−φ̄₁)^{τ₁} = ε·(μ₁ − ν₁)` and apply the two descents.
  rw [(R1cdi data1 hφ1).image_eq_signedDifference]
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference]
  rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left,
    ClassFunction.inner_sub_left, hdescend (R1cdi data1 hφ1).mu hmux,
    hdescend (R1cdi data1 hφ1).nu hnux0, sub_zero, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.18.c) difference-image orthogonality** (the geometric obligation of (12.3)).
For non-conjugate type-I maximals `L1, L2` and constituents `φ_i`, the Dade difference images
`τ_i(φ_i − φ̄_i)` are orthogonal.

**Genuine proof** (2026-07-03, loop¹⁰⁰): the mixed asymmetric `Ã(L₁) ∩ Ã₁(L₂) = ∅ ∨ swap` is
`nonconjugate_thickened_mixed_disjoint_or_swap` (S10 (8.18.c), three §16 pins); on the
disjoint side the bar-trick descent `constituent_diffImage_inner_zero_of_disjoint` closes the
per-constituent orthogonality, and the swap side follows by conjugate symmetry of the inner
product.  Hub issue 9003 Cluster B. -/
theorem nonconjugate_diffImage_inner_zero {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  haveI := hyp1.finiteG
  rcases nonconjugate_thickened_mixed_disjoint_or_swap hG hyp1 hyp2 hnot_conj with h | h
  · exact constituent_diffImage_inner_zero_of_disjoint hyp1 hyp2 h data1 hφ1 data2 hφ2
  · have hswap := constituent_diffImage_inner_zero_of_disjoint hyp2 hyp1 h data2 hφ2 data1 hφ1
    rw [OddOrder.RepresentationTheory.inner_conj_symm
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj))
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj)),
      hswap, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups `L₁, L₂`, the families
`R(χ₁) = Rset data1` and `R(χ₂) = Rset data2` are mutually orthogonal.

Proof: a member `α ∈ R(χ₁)` lies in `R₁(φ₁) = (R1cdi data1 hφ₁).toOrthonormalImage` for some
constituent `φ₁`, and likewise `β ∈ R₁(φ₂)`.  The cross-`L` (4.1) orthogonality
`toOrthonormalImage_inner_eq_zero_across` reduces `⟨α, β⟩ = 0` to the orthogonality of the signed
differences `⟨(φ₁−φ̄₁)^{τ₁}, (φ₂−φ̄₂)^{τ₂}⟩ = 0` (`image_eq_signedDifference`), which is the
geometric
obligation `nonconjugate_diffImage_inner_zero` ((8.18.c): the supports lie in disjoint `Ã(L₁)`,
`Ã₁(L₂)`). -/
theorem nonconjugate_typeI_R_orthogonal {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ∀ α ∈ Rset data1, ∀ β ∈ Rset data2, ClassFunction.inner α β = 0 := by
  intro α hαm β hβm
  obtain ⟨φ1, hφ1, hα⟩ := hαm
  obtain ⟨φ2, hφ2, hβ⟩ := hβm
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ1) (R1cdi data2 hφ2) ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ1),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference (R1cdi data2 hφ2)]
  exact nonconjugate_diffImage_inner_zero hG hyp1 hyp2 hnot_conj data1 hφ1 data2 hφ2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Same-`L` cross-family orthogonality of the type-I `R`-families.**  For two members
`χ₁, χ₂ ∈ S` of *one* type-I maximal `L`, if the constituents are pairwise distinct across the two
families and their conjugates (`hcond`: `φ₁ ≠ φ₂`, `φ₁ ≠ φ̄₂`, `φ̄₁ ≠ φ₂` for all `φ₁ ∈ S(χ₁)`,
`φ₂ ∈ S(χ₂)` — which holds when `χ₁ ∉ {χ₂, χ̄₂}`), the families `R(χ₁) = Rset data1` and
`R(χ₂) = Rset data2` are mutually orthogonal.

The same-`L` companion of `nonconjugate_typeI_R_orthogonal`: the cross-`L` (4.1) reduction
`toOrthonormalImage_inner_eq_zero_across` sends `⟨α, β⟩ = 0` to the signed-difference orthogonality,
here `constituentDiff_tau_inner_eq_zero_of_ne_across` (the two-family block orthogonality) rather
than
the geometric `nonconjugate_diffImage_inner_zero`.  This is the `ζ ∈ ℤ[R(χ)] ⟹ ζ ⊥ R(χ')` input
(`χ' ≠ χ, χ̄`) behind the (12.14) coset-constancy of the coherent extension. -/
theorem samegroup_typeI_R_orthogonal {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    {chi1 chi2 : ClassFunction ↥L ℂ} (data1 : CharacterDecompositionData hyp chi1)
    (data2 : CharacterDecompositionData hyp chi2)
    (hcond : ∀ φ1 ∈ data1.constituents, ∀ φ2 ∈ data2.constituents,
      φ1 ≠ φ2 ∧ φ1 ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ2 ∧
        OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ1 ≠ φ2) :
    ∀ α ∈ Rset data1, ∀ β ∈ Rset data2, ClassFunction.inner α β = 0 := by
  intro α hαm β hβm
  obtain ⟨φ1, hφ1, hα⟩ := hαm
  obtain ⟨φ2, hφ2, hβ⟩ := hβm
  obtain ⟨hne, h2, h3⟩ := hcond φ1 hφ1 φ2 hφ2
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ1) (R1cdi data2 hφ2) ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ1),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference (R1cdi data2 hφ2)]
  exact constituentDiff_tau_inner_eq_zero_of_ne_across data1 data2 hφ1 hφ2 hne h2 h3

/-- **Difference-uniqueness for signed irreducible-character differences** (Peterfalvi §3, the
reconciliation core of (1.4)).  If two *signed* differences of distinct irreducible characters
coincide, `s • (a − b) = t • (c − d)` with `a ≠ b`, `c ≠ d` and a nonzero left scalar `s`, then the
unordered pairs agree, with the sign tracking the orientation: either `a = c, b = d, s = t`
(same orientation) or `a = d, b = c, s = −t` (reversed).

This is the lemma by which the per-constituent families `R₁(φ)` (built from `τ(φ̄ − φ)`) are
reconciled with the global signed family of (1.4) in pin (a) `constituent_diff_tau_mem_span`:
the two presentations of `τ(φ − φ̄)` as a signed difference must share their underlying irreducible
pair, so each `μ_φ` lands in `ℤ[R(χ)]`.

Proof: pairing the hypothesis on the *left* with the irreducible `a` (resp. `b`) and using
orthonormality `⟨χ, ψ⟩ = δ_{χ,ψ}` (`irreducibleCharacter_inner_eq_ite`; `ClassFunction.inner` is
ℂ-linear in the left slot) gives `s = t·([c=a] − [d=a])` and `−s = t·([c=b] − [d=b])`.  Since
`s ≠ 0`, exactly one of `c = a`, `d = a` holds (the two cases are the two orientations), and the
`b`-pairing pins the remaining equality. -/
theorem irreducibleCharacter_signed_difference_uniqueness [Finite G]
    {a b c d : IrreducibleCharacter G} (hab : a ≠ b) (hcd : c ≠ d)
    {s t : ℂ} (hs : s ≠ 0)
    (h : s • ((a : ClassFunction G ℂ) - (b : ClassFunction G ℂ))
        = t • ((c : ClassFunction G ℂ) - (d : ClassFunction G ℂ))) :
    (a = c ∧ b = d ∧ s = t) ∨ (a = d ∧ b = c ∧ s = -t) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hba : b ≠ a := fun he => hab he.symm
  -- Pair the equation on the left with an arbitrary irreducible `e`; orthonormality turns each
  -- coercion-inner into a Kronecker delta.
  have key : ∀ e : IrreducibleCharacter G,
      s * ((if a = e then (1 : ℂ) else 0) - (if b = e then 1 else 0))
        = t * ((if c = e then (1 : ℂ) else 0) - (if d = e then 1 else 0)) := by
    intro e
    have h2 := congrArg (fun f => ClassFunction.inner f (e : ClassFunction G ℂ)) h
    simpa only [ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
      irreducibleCharacter_inner_eq_ite] using h2
  -- Evaluate at `a`: `s = t·([c=a] − [d=a])`.
  have ka : s = t * ((if c = a then (1 : ℂ) else 0) - (if d = a then 1 else 0)) := by
    have hka := key a
    rwa [if_pos rfl, if_neg hba, sub_zero, mul_one] at hka
  -- Evaluate at `b`: `−s = t·([c=b] − [d=b])`.
  have kb : -s = t * ((if c = b then (1 : ℂ) else 0) - (if d = b then 1 else 0)) := by
    have hkb := key b
    rwa [if_neg hab, if_pos rfl, zero_sub, mul_neg_one] at hkb
  by_cases hca : c = a
  · -- Orientation A: `c = a`, hence `d ≠ a`, and `ka` collapses to `s = t`.
    have hda : d ≠ a := fun he => hcd (hca.trans he.symm)
    rw [if_pos hca, if_neg hda, sub_zero, mul_one] at ka
    have hcb : c ≠ b := fun he => hab (hca.symm.trans he)
    rw [if_neg hcb, zero_sub, mul_neg] at kb
    by_cases hdb : d = b
    · exact Or.inl ⟨hca.symm, hdb.symm, ka⟩
    · rw [if_neg hdb, mul_zero, neg_zero] at kb
      exact absurd (neg_eq_zero.mp kb) hs
  · by_cases hda : d = a
    · -- Orientation B: `c ≠ a`, `d = a`, and `ka` collapses to `s = −t`.
      rw [if_neg hca, if_pos hda, zero_sub, mul_neg_one] at ka
      have hdb : d ≠ b := fun he => hab (hda.symm.trans he)
      rw [if_neg hdb, sub_zero] at kb
      by_cases hcb : c = b
      · exact Or.inr ⟨hda.symm, hcb.symm, ka⟩
      · rw [if_neg hcb, mul_zero] at kb
        exact absurd (neg_eq_zero.mp kb) hs
    · -- Neither: `ka` forces `s = 0`, contradiction.
      rw [if_neg hca, if_neg hda, sub_zero, mul_zero] at ka
      exact absurd ka hs

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 3** (span membership): the two underlying irreducibles
`μ_φ, ν_φ` of the difference image `R1cdi data hφ` lie in `ℤ[R(χ)]`.  The orthonormal block
`R₁(φ).imageSet = {ε·μ_φ, −ε·ν_φ} ⊆ R(χ)` with `ε = ±1`, so `μ_φ = ε·(ε·μ_φ)` and
`ν_φ = (−ε)·(−ε·ν_φ)` are integer multiples of `R(χ)` members. -/
theorem R1cdi_muNu_mem_span_Rset {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (R1cdi data hφ).muClassFunction ∈ Submodule.span ℤ (Rset data) ∧
      (R1cdi data hφ).nuClassFunction ∈ Submodule.span ℤ (Rset data) := by
  haveI := hyp.finiteG
  classical
  have himg : (R1 data hφ).imageSet
      = ({(R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction,
          (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction} :
            Finset (ClassFunction G ℂ)) := rfl
  have hsq : (R1cdi data hφ).sign * (R1cdi data hφ).sign = 1 := (R1cdi data hφ).sign_mul_self
  have hμRset : (R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_self _ _⟩
  have hνRset : (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  refine ⟨?_, ?_⟩
  · have hμ : (R1cdi data hφ).muClassFunction
        = (R1cdi data hφ).sign • ((R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction) := by
      rw [smul_smul, hsq, one_smul]
    rw [hμ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hμRset)
  · have hν : (R1cdi data hφ).nuClassFunction
        = (-(R1cdi data hφ).sign) •
          ((-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction) := by
      rw [smul_smul, neg_mul_neg, hsq, one_smul]
    rw [hν]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hνRset)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 1** (global (1.4) coherence): the constituent set `S(χ)`
together with its complex conjugates forms a single coherent family under the Dade isometry `τ`.
There is a uniform sign `ε = ±1` and an injection `μ` of the conjugate-closed set
`T = S(χ) ∪ S(χ)‾` into `Irr G` with `τ(α − β) = ε·(μ α − μ β)` for all `α, β ∈ T`.

This is the §3 (1.4) keystone `isometry_difference_pair_structure` applied to the constant-degree
family `T` (every member supported in `A(L) ∪ {1}`, so member differences are `A(L)`-supported and
the three Dade-isometry hypotheses hold by `dadeIntegralCharacterMap_{mem_ZIrr_of_supported,
apply_one_eq_zero,inner_eq_on_supported_span}`). -/
theorem exists_uniform_image_of_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ∃ (ε : ℤ) (μ : IrreducibleCharacter ↥L → IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
      Set.InjOn μ ↑(data.constituents ∪
          data.constituents.image (IrreducibleCharacter.conjPerm ↥L)) ∧
      ∀ α ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
        ∀ β ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
          hyp.tau ((α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ))
            = ε • ((μ α : ClassFunction G ℂ) - (μ β : ClassFunction G ℂ)) := by
  haveI := hyp.finiteG
  classical
  set T := data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  obtain ⟨φref, hφref⟩ := data.constituents_nonempty
  -- (1) every member of `T` is supported in `A(L) ∪ {1}`.
  have hTsupp : ∀ x ∈ T, (x : ClassFunction ↥L ℂ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1} := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.supported x hx
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      have hconjsupp : (φ : ClassFunction ↥L ℂ).conj.support
          = (φ : ClassFunction ↥L ℂ).support := by
        ext y; simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
      rw [hconjsupp]; exact data.supported φ hφ
  -- (2) every member of `T` has the reference degree `φref(1)`.
  have hTdeg : ∀ x ∈ T, ((x : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((φref : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.equal_degree x hx φref hφref
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
      rw [ClassFunction.conj_apply, hd, star_natCast, ← hd]
      exact data.equal_degree φ hφ φref hφref
  -- (3) enumerate `T` as a `Fin n` family.
  set n := T.card with hndef
  have hφrefT : φref ∈ T := Finset.mem_union_left _ hφref
  have hconjrefT : IrreducibleCharacter.conjPerm ↥L φref ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφref)
  have hrefne : φref ≠ IrreducibleCharacter.conjPerm ↥L φref := fun hcon =>
    data.not_real φref hφref ((IrreducibleCharacter.conjPerm_eq_self_iff φref).mp hcon.symm)
  have hn2 : 2 ≤ n := Finset.one_lt_card.mpr ⟨φref, hφrefT, _, hconjrefT, hrefne⟩
  haveI : NeZero n := ⟨by omega⟩
  set fam : Fin n → IrreducibleCharacter ↥L :=
    fun i => (T.equivFin.symm i : IrreducibleCharacter ↥L)
    with hfamdef
  have hfam_mem : ∀ i, fam i ∈ T := fun i => (T.equivFin.symm i).2
  have hfam_inj : Function.Injective fam :=
    fun i j h => T.equivFin.symm.injective (Subtype.ext h)
  -- (4) each member difference `fam i − fam 0` is `A(L)`-supported.
  have hdiff_supp : ∀ i, (irreducibleCharacterDifference fam i).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro i y hy
    have hne1 : y ≠ 1 := by
      rintro rfl
      refine (ClassFunction.mem_support.mp hy) ?_
      change (fam i : ClassFunction ↥L ℂ) 1 - (fam 0 : ClassFunction ↥L ℂ) 1 = 0
      rw [hTdeg (fam i) (hfam_mem i), hTdeg (fam 0) (hfam_mem 0), sub_self]
    rcases ClassFunction.support_sub_subset _ _ hy with h | h
    · rcases hTsupp _ (hfam_mem i) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
    · rcases hTsupp _ (hfam_mem 0) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
  have hSsupp : ∀ s ∈ Set.range (irreducibleCharacterDifference fam),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    rintro s ⟨i, rfl⟩; exact hdiff_supp i
  -- (5) the three (1.4) hypotheses for the Dade isometry, via the supported-span lemmas.
  have hsame_deg : ∀ i, ((fam i : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((fam 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := fun i =>
    (hTdeg (fam i) (hfam_mem i)).trans (hTdeg (fam 0) (hfam_mem 0)).symm
  have hvirtual : IsometryDifferenceImagesAreVirtual hyp.tau fam := by
    intro i
    change hyp.tau (irreducibleCharacterDifference fam i) ∈ ZIrr G
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj (hdiff_supp i)
      (Submodule.sub_mem _ (fam i).mem_ZIrr (fam 0).mem_ZIrr)
  have hzero : IsometryDifferenceImagesVanishAtOne hyp.tau fam := by
    intro i
    change hyp.tau (irreducibleCharacterDifference fam i) (1 : G) = 0
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
      hyp.dadeData.dade hyp.hconj (hdiff_supp i)
  have hisom : ∀ i j, ClassFunction.inner (isometryDifferenceImage hyp.tau fam i)
      (isometryDifferenceImage hyp.tau fam j)
      = ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    change ClassFunction.inner (hyp.tau (irreducibleCharacterDifference fam i))
      (hyp.tau (irreducibleCharacterDifference fam j)) = _
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hyp.hconj hSsupp (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.subset_span ⟨j, rfl⟩)
  -- (6) apply the (1.4) keystone.
  obtain ⟨sdf, himage⟩ :=
    isometry_difference_pair_structure hn2 fam hfam_inj hsame_deg hyp.tau hvirtual hzero hisom
  -- (7) read off `ε` and `μ`.
  refine ⟨sdf.sign, fun x => if hx : x ∈ T then sdf.mu (T.equivFin ⟨x, hx⟩) else sdf.mu 0,
    sdf.sign_eq, ?_, ?_⟩
  · -- InjOn
    intro x hx y hy hxy
    have hxT : x ∈ T := Finset.mem_coe.mp hx
    have hyT : y ∈ T := Finset.mem_coe.mp hy
    simp only [dif_pos hxT, dif_pos hyT] at hxy
    exact Subtype.ext_iff.mp (T.equivFin.injective (sdf.injective hxy))
  · -- the pair relation
    intro α hα β hβ
    have hαT : α ∈ T := hα
    have hβT : β ∈ T := hβ
    -- key: for `x ∈ T`, `τ(x − fam 0) = ε·(μ x − μ₀)`.
    have key : ∀ x (hx : x ∈ T), hyp.tau ((x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
        = sdf.sign • ((sdf.mu (T.equivFin ⟨x, hx⟩) : ClassFunction G ℂ)
            - (sdf.mu 0 : ClassFunction G ℂ)) := by
      intro x hx
      have hfx : fam (T.equivFin ⟨x, hx⟩) = x := by
        simp only [hfamdef, Equiv.symm_apply_apply]
      have hLHS : (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = irreducibleCharacterDifference fam (T.equivFin ⟨x, hx⟩) := by
        change (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = (fam (T.equivFin ⟨x, hx⟩) : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
        rw [hfx]
      rw [hLHS]
      change isometryDifferenceImage hyp.tau fam (T.equivFin ⟨x, hx⟩) = _
      rw [himage (T.equivFin ⟨x, hx⟩),
        SignedIrreducibleDifferenceFamily.signedDifference_apply,
        SignedIrreducibleDifferenceFamily.difference_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply]
    have hsub : (α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ)
        = ((α : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
          - ((β : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)) := by abel
    rw [hsub, map_sub, key α hαT, key β hβT, ← smul_sub]
    congr 1
    simp only [dif_pos hαT, dif_pos hβT]
    abel

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (a)** (coherence): for constituents `φ₁, φ₂ ∈ S(χ)`, the Dade image
`(φ₁ − φ₂)^τ` lies in `ℤ[R(χ)]`.

Proof (the (1.4) coherence content, now genuine): the conjugate-closed constituent set `T` is a
single coherent family under `τ` (`exists_uniform_image_of_constituents`), giving a uniform sign
`ε` and injection `μ : T → Irr G` with `τ(φ₁ − φ₂) = ε·(μ φ₁ − μ φ₂)`.  For each constituent `φ`,
the two presentations of `τ(φ − φ̄)` — the global `ε·(μ φ − μ φ̄)` and the per-`φ` block
`R₁(φ)`'s `ε_φ·(μ_φ − ν_φ)` (`R1cdi.image_eq`) — must share their irreducible pair
(`irreducibleCharacter_signed_difference_uniqueness`), so `μ φ ∈ {μ_φ, ν_φ} ⊆ ℤ[R(χ)]`
(`R1cdi_muNu_mem_span_Rset`).  Hence `μ φ₁, μ φ₂ ∈ ℤ[R(χ)]` and `τ(φ₁ − φ₂) ∈ ℤ[R(χ)]`. -/
theorem constituent_diff_tau_mem_span {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) ∈
      Submodule.span ℤ (Rset dχ) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨ε, μ, hε, hμinj, hμrel⟩ := exists_uniform_image_of_constituents hyp dχ
  set T := dχ.constituents ∪ dχ.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  -- reconciliation: every `μ φ` (for a constituent `φ`) lies in `ℤ[R(χ)]`.
  have hmu_mem : ∀ φ ∈ dχ.constituents, (μ φ : ClassFunction G ℂ) ∈ Submodule.span ℤ (Rset dχ) := by
    intro φ hφ
    have hφT : φ ∈ T := Finset.mem_union_left _ hφ
    have hconjT : IrreducibleCharacter.conjPerm ↥L φ ∈ T :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφ)
    set cdi := R1cdi dχ hφ with hcdi
    -- global vs per-`φ` presentation of `τ(φ − φ̄)`.
    have hglob := hμrel φ hφT (IrreducibleCharacter.conjPerm ↥L φ) hconjT
    rw [IrreducibleCharacter.conjPerm_apply_coe] at hglob
    have hcomb : ε • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = cdi.sign • ((cdi.muClassFunction) - (cdi.nuClassFunction)) :=
      hglob.symm.trans cdi.image_eq
    have hcombℂ : (ε : ℂ) • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = (cdi.sign : ℂ) • (((cdi.mu : ClassFunction G ℂ)) - ((cdi.nu : ClassFunction G ℂ))) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hcomb
    -- the two distinct-pair hypotheses.
    have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
      dχ.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
    have hab : μ φ ≠ μ (IrreducibleCharacter.conjPerm ↥L φ) := fun h =>
      hφne (hμinj (Finset.mem_coe.mpr hφT) (Finset.mem_coe.mpr hconjT) h)
    have hs : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
    rcases irreducibleCharacter_signed_difference_uniqueness hab cdi.distinct hs hcombℂ with
      ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).1
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).2
  -- assemble.
  have hφ₁T : φ₁ ∈ T := Finset.mem_union_left _ h₁
  have hφ₂T : φ₂ ∈ T := Finset.mem_union_left _ h₂
  rw [hμrel φ₁ hφ₁T φ₂ hφ₂T]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmu_mem φ₁ h₁) (hmu_mem φ₂ h₂))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5)** (`χ^{τ₁} ∈ ℤ[R(χ)]` for a coherent extension).  For the coherent
extension `coh` of the type-I family `S` of a `Hypothesis L`, and a non-real member `χ ∈ S`
(as an `IrreducibleCharacter`) whose difference `χ − χ̄` is supported in the Dade domain `A(L)`
and which is orthogonal to its conjugate (`⟨χ, χ̄⟩ = 0`), the Dade character `ψ = χ^{τ₁} =
coh.extension χ` lies in the integral span of the orthonormal image family
`R(χ) = dadeOrthonormalCharacterImageFamilyOfDiff … χ`.

This is the `ψ = 0` case of the (5.4) decomposition `(χ − ψ)^{τ₁} = X − Y`.  Taking the coherent
extension as the auxiliary isometry `τ₁`, its `ZIrr`-codomain (`extension_mem_ZIrr`, the
virtual-character property the general **unsupported** `X`-family `Ind θ` lacks — `χ(1) ≠ 0`)
supplies the single number-theoretic input to `CharacterPsiDecomposition.ofProjection`; then
`eq_sum_of_psi_eq_zero` forces `Y = 0`, so `χ^{τ₁} = X = ∑_{α ∈ E ⊆ R(χ)} α ∈ ℤ[R(χ)]`.  This is
the L-side `ψ ∈ ℤ[R(χ_L)]` which, combined with the (12.3) cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)` (`nonconjugate_typeI_R_orthogonal`), yields `ψ ⊥ R(χ_M)` — the `horth` input of
the (12.14) coset-constancy `psi_constant_on_xK`. -/
theorem coherent_extension_mem_span_imageFamily {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (χ : IrreducibleCharacter ↥L)
    (hχmem : (χ : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    coh.extension (χ : ClassFunction ↥L ℂ) ∈
      Submodule.span ℤ
        ((OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.dadeData.dade hyp.hconj χ hχreal hdiffsupp).imageSet :
          Set (ClassFunction G ℂ)) := by
  classical
  set imF := OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
    hyp.dadeData.dade hyp.hconj χ hχreal hdiffsupp with himF
  -- membership of `χ`, `χ̄`, and `χ − χ̄` in the coherent lattice `ℤ[S]`.
  have hχ_zSpan : (χ : ClassFunction ↥L ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχmem
  have hχbar_mem : (χ : ClassFunction ↥L ℂ).conj ∈ hyp.Sset :=
    (Sset_closedUnderConjugate hyp).conj_mem hχmem
  have hχbar_zSpan : (χ : ClassFunction ↥L ℂ).conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχbar_mem
  have hdiff_zSpan : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.sub_mem _ hχ_zSpan hχbar_zSpan
  -- `χ − χ̄` is supported in `A(L)` (sign flip of the given `χ̄ − χ` support).
  have hdiffsupp' : ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj).support ⊆
      hyp.A := by
    have heq : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj
        = -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) := by abel
    rw [heq, ClassFunction.support_neg]
    exact hdiffsupp
  -- the sublattice `ℤ[χ − χ̄, χ − 0]` sits inside `ℤ[S]`.
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥L)
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - 0} ≤
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    change Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hχ_zSpan
  -- build the (5.4) decomposition with `ψ = 0` and `τ₁ = coh.extension`, forcing `Y = 0`.
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0) imF coh.extension
        (fun φ ζ hφ hζ => coh.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (coh.extends_on_supported
          ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
          ⟨hdiff_zSpan, hdiffsupp'⟩)
        (by rw [sub_zero]; exact coh.extension_mem_ZIrr _ hχ_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        hχχbar)
  -- `coh.extension χ = χ^{τ₁} = X = ∑_{α ∈ E} α ∈ ℤ[R(χ)]`.
  have hgoal : coh.extension (χ : ClassFunction ↥L ℂ) = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα => Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) → (12.2.b), constituent form**: the coherent Dade image `χ^{τ₁} =
coh.extension φ` of a constituent `φ ∈ S(χ)` (`data.constituents`) that is itself a member of the
family `S` lies in `ℤ[R(χ)] = Submodule.span ℤ (Rset data)`.

The (5.5) image family `dadeOrthonormalCharacterImageFamilyOfDiff … φ` is *definitionally* the block
`R₁(φ) = R1 data hφ` — both are the `toOrthonormalImage` of the same
`dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj φ (data.not_real φ hφ)
(R1_diffsupp data hφ)` — which is a subfamily of `R(χ) = Rset data`, so
`coherent_extension_mem_span_imageFamily` lands in `ℤ[R(χ)]` after `span_mono`.  The orthogonality
`⟨φ, φ̄⟩ = 0` comes for free from `data.not_real φ hφ` (a non-real irreducible is orthogonal to its
conjugate).  This is the L-side `ψ ∈ ℤ[R(χ_L)]` for the (12.16) witness: the distinguished
`χ_L = Ind θ` is irreducible (Frobenius), so its unique constituent is itself, in `S`. -/
theorem coherent_extension_constituent_mem_span_Rset {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφmem : (φ : ClassFunction ↥L ℂ) ∈ hyp.Sset) :
    coh.extension (φ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ (Rset data) := by
  classical
  -- a non-real irreducible is orthogonal to its complex conjugate.
  have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
    data.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
  have hχχbar :
      ClassFunction.inner (φ : ClassFunction ↥L ℂ) (φ : ClassFunction ↥L ℂ).conj = 0 := by
    have h0 := irreducibleCharacter_inner_eq_ite φ (IrreducibleCharacter.conjPerm ↥L φ)
    rw [if_neg hφne] at h0
    rwa [IrreducibleCharacter.conjPerm_apply_coe] at h0
  -- (5.5): `coh.extension φ ∈ ℤ[R₁(φ)]`; and `R₁(φ) ⊆ R(χ) = Rset data`.
  have h55 := coherent_extension_mem_span_imageFamily hyp coh φ hφmem
    (data.not_real φ hφ) (R1_diffsupp data hφ) hχχbar
  refine Submodule.span_mono ?_ h55
  intro α hα
  exact ⟨φ, hφ, Finset.mem_coe.mp hα⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) + (12.3): the L-side Dade character `ψ = χ_L^{τ₁}` is orthogonal to
`R(χ_M)`.**  For two non-conjugate type-I maximal subgroups `L`, `M` and a constituent
`φ_L ∈ S(χ_L)` of the L-side family that is itself a member of `S` (the Frobenius witness case,
where `χ_L = Ind θ` is irreducible), the coherent Dade image `ψ = coh_L.extension φ_L` is orthogonal
to every element of `R(χ_M) = Rset data_M`.

Two ingredients combine: (5.5) `coherent_extension_constituent_mem_span_Rset` puts
`ψ ∈ ℤ[R(χ_L)]`, and (12.3) `nonconjugate_typeI_R_orthogonal` gives the cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)`; since `⟨·,·⟩` is conjugate-symmetric and additive, orthogonality of `ψ` to all
of `R(χ_M)` follows from `inner_eq_zero_of_mem_zSpan`.  This is precisely the per-`χ_M` piece of the
`horth` hypothesis that the (12.4)/(12.14) coset-constancy chain (`Sset_coeff_equal`,
`psi_constant_on_xK`) consumes: `ψ` restricted to the `M`-structure has equal coefficients across
`S(χ_M)`, forcing `ψ` constant on the `M_F`-cosets. -/
theorem coherent_extension_constituent_orthogonal_Rset_of_nonconjugate {L M : Subgroup G}
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp_L : Hypothesis L)
    (coh_L : OddOrder.Peterfalvi.S07.IsCoherent hyp_L.tau hyp_L.Sset hyp_L.A)
    {chi_L : ClassFunction ↥L ℂ} (data_L : CharacterDecompositionData hyp_L chi_L)
    {φ_L : IrreducibleCharacter ↥L} (hφ_L : φ_L ∈ data_L.constituents)
    (hφ_L_mem : (φ_L : ClassFunction ↥L ℂ) ∈ hyp_L.Sset)
    (hyp_M : Hypothesis M) (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L = M)
    {chi_M : ClassFunction ↥M ℂ} (data_M : CharacterDecompositionData hyp_M chi_M) :
    ∀ α ∈ Rset data_M,
      ClassFunction.inner (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) α = 0 := by
  -- (5.5): `ψ = coh_L.extension φ_L ∈ ℤ[R(χ_L)]`.
  have h55 := coherent_extension_constituent_mem_span_Rset hyp_L coh_L data_L hφ_L hφ_L_mem
  -- (12.3): `R(χ_L) ⊥ R(χ_M)`.
  have horth := nonconjugate_typeI_R_orthogonal hG hyp_L hyp_M hnot_conj data_L data_M
  intro α hα
  -- `α ⊥ R(χ_L)` (conjugate-swap of (12.3)), hence `α ⊥ ℤ[R(χ_L)] ∋ ψ`; conjugate back.
  have hαperp : ∀ β ∈ Rset data_L, ClassFunction.inner α β = 0 := by
    intro β hβ
    rw [inner_conj_symm β α, horth β hβ α hα, star_zero]
  have h0 : ClassFunction.inner α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hαperp h55
  rw [inner_conj_symm α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)), h0, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), the `o_rpsi_S` orthogonality component**: a class function `ψ` orthogonal
to `R(χ) = Rset data` is orthogonal to the coherent Dade image `coh.extension φ` of every
constituent `φ ∈ S(χ)` that lies in `S`.  Immediate from (5.5)
`coherent_extension_constituent_mem_span_Rset` (`coh.extension φ ∈ ℤ[R(χ)]`) and
`inner_eq_zero_of_mem_zSpan`.

This is the same-`L` specialization of
`coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` with `ψ` an arbitrary
`R(χ)`-orthogonal function in place of a second coherent image, and is the `'[psi, tau2 xi] = 0`
step of the Coq (12.5) `o_rpsi_S` proof (`opsiR`). -/
theorem inner_psi_coherent_extension_eq_zero {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφmem : (φ : ClassFunction ↥L ℂ) ∈ hyp.Sset) {psi : ClassFunction G ℂ}
    (horth : ∀ α ∈ Rset data, ClassFunction.inner psi α = 0) :
    ClassFunction.inner psi (coh.extension (φ : ClassFunction ↥L ℂ)) = 0 :=
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan horth
    (coherent_extension_constituent_mem_span_Rset hyp coh data hφ hφmem)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5) support input** (the `A1xi12` step of the Coq `o_rpsi_S` proof): the
difference `χ₁ − χ₂` of two **equal-degree** members of `S` vanishes off `H^# = H ∖ {1}` — i.e. at
every `x` with `(x : G) ∉ H` (both `Ind_H^L`-characters vanish off the normal `H = L_F`,
`Sset_vanishes_off_H`) or `x = 1` (equal degree, so `(χ₁ − χ₂)(1) = 0`).  This is the
`xi1 − xi2 ∈ CF(L, H^#)` support hypothesis under which the type-I Dade isometry `τ` acts on the
difference (feeding `constituent_diff_tau_eq_induce` / the `chiRho_adjoint` reciprocity of the
(12.5) Fact-A rebuild). -/
theorem Sset_diff_vanishes_off_H_sharp {L : Subgroup G} (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L)) {x : ↥L}
    (hx : (x : G) ∉ hyp.H ∨ x = 1) : (χ₁ - χ₂) x = 0 := by
  rw [ClassFunction.sub_apply]
  rcases hx with hxH | hx1
  · rw [Sset_vanishes_off_H hyp hχ₁ hxH, Sset_vanishes_off_H hyp hχ₂ hxH, sub_zero]
  · subst hx1; rw [hdeg, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5) support, packaged for the Dade isometry** (the Frobenius witness case): the
difference `χ₁ − χ₂` of two equal-degree members of `S` is supported in `A(L) = ambientA` (as
`supportInSubgroup ambientA L`), so it is a `SupportedClassFunctions` to which the Dade isometry and
the `chiRho_adjoint` reciprocity apply.  From `Sset_diff_vanishes_off_H_sharp`
(`χ₁ − χ₂` vanishes off `H^# = H ∖ {1}`) and `hAH : A(L) = H^#`
(`mem_supportInSubgroup_sharp_subgroupOf_iff`).  Feeds the `A1xi12` step of the (12.5) `o_rpsi_S`
Fact-A. -/
theorem Sset_diff_support_subset_ambientA {L : Subgroup G} (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) :
    (χ₁ - χ₂).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hnot : ¬((x : G) ∉ hyp.H ∨ x = 1) := fun h =>
    hx (Sset_diff_vanishes_off_H_sharp hyp hχ₁ hχ₂ hdeg h)
  push Not at hnot
  exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
    hyp.typeI.typeF.H hAH x).mpr ⟨Subgroup.mem_subgroupOf.mpr hnot.1, hnot.2⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), the `o_rpsi_S` coefficient equality** (Frobenius witness case): the
`ρ`-image `χ^ρ = toHypothesis71.chiRhoCF ψ` has the *same* coefficient on two equal-degree members
`χ₁, χ₂ ∈ S`: `⟨χ₁, ρψ⟩ = ⟨χ₂, ρψ⟩`, provided the coherent Dade images `coh.extension χᵢ` are
orthogonal to `ψ`.

The Coq `o_rpsi_S` step, assembled from the now-complete bridge chain: the difference `χ₁ − χ₂` is
supported in `A(L)` (`Sset_diff_support_subset_ambientA`), so the Dade reciprocity `chiRho_adjoint`
gives `⟨χ₁ − χ₂, ρψ⟩ = ⟨H71.τ (χ₁−χ₂), ψ⟩`; the τ-bridging `toHypothesis71_tau_apply` and coherence
`extends_on_supported` rewrite `H71.τ (χ₁−χ₂) = hyp.tau (χ₁−χ₂) = coh.extension (χ₁−χ₂) =
coh.extension χ₁ − coh.extension χ₂`; the orthogonality hypotheses close it to `0`.  The
orthogonalities come from `inner_psi_coherent_extension_eq_zero` (`ψ ⊥ R(χ)`); combined with
Frobenius (`⟨Res_H ρψ, θ⟩ = ⟨ρψ, Ind_H^L θ⟩`) this is the degree-determined coefficient of the
(12.5) `DpsiH` decomposition. -/
theorem chiRhoCF_inner_eq_of_equal_degree {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) {ψ : ClassFunction G ℂ}
    (horth1 : ClassFunction.inner ψ (coh.extension χ₁) = 0)
    (horth2 : ClassFunction.inner ψ (coh.extension χ₂) = 0) :
    ClassFunction.inner χ₁ (hyp.toHypothesis71.chiRhoCF ψ)
      = ClassFunction.inner χ₂ (hyp.toHypothesis71.chiRhoCF ψ) := by
  haveI := hyp.finiteG
  have hsupp := Sset_diff_support_subset_ambientA hyp hχ₁ hχ₂ hdeg hAH
  set α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typeIA L hyp.typeI) L :=
    ⟨χ₁ - χ₂, (ClassFunction.mem_supportedSubmodule).mpr hsupp⟩ with hα
  have hmemspan : (χ₁ - χ₂) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A :=
    ⟨sub_mem (Submodule.subset_span hχ₁) (Submodule.subset_span hχ₂), hsupp⟩
  have hkey : ClassFunction.inner (χ₁ - χ₂) (hyp.toHypothesis71.chiRhoCF ψ) = 0 := by
    have hrec := hyp.toHypothesis71.chiRho_adjoint α ψ
    have hαcoe : (α : ClassFunction ↥L ℂ) = χ₁ - χ₂ := rfl
    rw [hαcoe] at hrec
    rw [← hrec, hyp.toHypothesis71_tau_apply α, hαcoe,
      ← coh.extends_on_supported (χ₁ - χ₂) hmemspan, map_sub, ClassFunction.inner_sub_left,
      inner_conj_symm ψ (coh.extension χ₁),
      inner_conj_symm ψ (coh.extension χ₂), horth1, horth2, star_zero, sub_zero]
  rw [ClassFunction.inner_sub_left] at hkey
  exact sub_eq_zero.mp hkey

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), the θ-level coefficient equality** (Frobenius form of `o_rpsi_S`).  For
`χᵢ = Ind_H^L θᵢ ∈ S` of equal degree, the `ρ`-image's `H`-restriction has equal coefficient on
`θ₁, θ₂`: `⟨θ₁, Res_H ρψ⟩ = ⟨θ₂, Res_H ρψ⟩`.  Frobenius reciprocity
(`inner_induce_eq_inner_restrict`, `⟨Ind_H^L θ, ρψ⟩ = ⟨θ, Res_H ρψ⟩`) applied to
`chiRhoCF_inner_eq_of_equal_degree`.  Input to the (12.5) `DpsiH` decomposition: grouped by the
induced-from-`H'` partition of `Irr H` (equal-degree blocks, general (1.7.b)), it forces
`Res_H ρψ = ∑_λ a_λ Ind_{H'}^H λ + a·1_H`. -/
theorem chiRhoCF_restrict_inner_eq_of_equal_degree {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) {ψ : ClassFunction G ℂ}
    (horth1 : ClassFunction.inner ψ (coh.extension χ₁) = 0)
    (horth2 : ClassFunction.inner ψ (coh.extension χ₂) = 0)
    {θ₁ θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ}
    (hθ₁ : χ₁ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ₁)
    (hθ₂ : χ₂ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ₂) :
    ClassFunction.inner θ₁ (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ))
      = ClassFunction.inner θ₂ (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ)) := by
  haveI := hyp.finiteG
  have hfact := chiRhoCF_inner_eq_of_equal_degree hyp coh hχ₁ hχ₂ hdeg hAH horth1 horth2
  rw [hθ₁, hθ₂, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict] at hfact
  exact hfact

open scoped Classical in
/-- **General TI-induction self-value** (Isaacs 7.x / Peterfalvi (3.2.c) value half), generalized
from `TICyclicHypothesis.induce_apply_eq_self_of_mem_V` to an arbitrary TI subset.  For a TI subset
`A` relative to `L` (`L ⊆ N_G(A)`, `A ⊆ L`, `IsTISubset A L`) and a class function `α` of `L`
supported in `A`, the induced class function `Ind_L^G α` agrees with `α` on `A`: only the `|L|`
conjugators `x ∈ L` contribute to the induction sum (the others land outside `A`, where `α`
vanishes,
by the TI property), each with value `α(a)`.  This is **pin (b), step 1** — the value-half of the
"Dade map = Ind on the trivial-`H` part" bridge. -/
theorem induce_apply_eq_self_of_mem_tiSubset {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hAL : A ⊆ (L : Set G))
    (hnorm : ∀ x ∈ L, ∀ a ∈ A, x⁻¹ * a * x ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (α : ClassFunction ↥L ℂ)
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {a : G} (ha : a ∈ A) :
    ClassFunction.induce L α a = α ⟨a, hAL ha⟩ := by
  classical
  haveI : Fintype ↥L := Fintype.ofFinite _
  have haL : a ∈ L := hAL ha
  have hterm : ∀ x : G, ClassFunction.induceTerm L α x a
      = if x ∈ L then α ⟨a, haL⟩ else 0 := by
    intro x
    by_cases hx : x ∈ L
    · rw [if_pos hx]
      have haxL : x⁻¹ * a * x ∈ L := hAL (hnorm x hx a ha)
      rw [ClassFunction.induceTerm_of_mem _ haxL]
      have harg : (⟨x⁻¹ * a * x, haxL⟩ : ↥L)
          = ⟨x⁻¹, L.inv_mem hx⟩ * ⟨a, haL⟩ * ⟨x⁻¹, L.inv_mem hx⟩⁻¹ := by
        apply Subtype.ext; simp [inv_inv]
      rw [harg]
      exact α.conj_eq ⟨a, haL⟩ ⟨x⁻¹, L.inv_mem hx⟩
    · rw [if_neg hx]
      by_cases hax : x⁻¹ * a * x ∈ L
      · rw [ClassFunction.induceTerm_of_mem _ hax]
        have hnotA : x⁻¹ * a * x ∉ A := fun hV =>
          hx (by simpa using L.inv_mem (hTI x⁻¹ ⟨a, ha, by simpa using hV⟩))
        by_contra hne
        exact hnotA ((OddOrder.Peterfalvi.S04.mem_supportInSubgroup).mp
          (hαsupp (ClassFunction.mem_support.mpr hne)))
      · rw [ClassFunction.induceTerm_of_not_mem _ hax]
  rw [ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.univ.filter (· ∈ L)).card = Nat.card ↥L := by
    rw [Nat.card_eq_fintype_card]; exact (Fintype.card_subtype _).symm
  rw [hcard, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

open scoped Classical in
/-- **Peterfalvi (12.4) pin (b), step 2**: for a Dade hypothesis with all trivial stabilizers
`∀ a, H(a) = ⊥`, induction `Ind_L^G` (restricted to `CF(L, A)`) **is** the Dade map.  Generalizes
`TICyclicHypothesis.isDadeMap_inducedDadeMap`: the value half is the step-1 self-value
`induce_apply_eq_self_of_mem_tiSubset` (the coset condition collapses to `IsConj a g` since
`h ∈ ⊥`),
the support half is `induce_eq_zero_of_not_conjugatesIntoSet` (induced functions vanish off the
`A`-conjugates, which are the Dade support when `H = ⊥`).  Via `IsDadeMap.unique` this pins the
abstract Dade map to `Ind_L^G` on `CF(L, A)`. -/
theorem isDadeMap_induce_of_forall_H_eq_bot {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hH : ∀ a, hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.IsDadeMap hyp
      (fun α => ClassFunction.induce L (α : ClassFunction ↥L ℂ)) where
  map_eq_of_isConj_hCoset := by
    intro α g a h hh hconj
    have hh1 : h = 1 := Subgroup.mem_bot.mp (by rw [← hH a]; exact hh)
    subst hh1
    have hga : IsConj a.1 g := by simpa using hconj
    change ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = _
    rw [← (ClassFunction.induce L (α : ClassFunction ↥L ℂ)).of_isConj hga]
    exact induce_apply_eq_self_of_mem_tiSubset hyp.subset_L
      (fun x hx a' ha' => by simpa using hyp.L_normalizes_A ⟨x⁻¹, L.inv_mem hx⟩ ha')
      (hyp.isTISubset_of_forall_H_eq_bot hH) _
      (ClassFunction.mem_supportedSubmodule.mp α.2) a.2
  map_eq_zero_of_not_mem_dadeSupport := by
    intro α g hg
    change ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = 0
    refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
      (ClassFunction.mem_supportedSubmodule.mp α.2) (fun hgin => hg ?_)
    rw [hyp.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot hH]
    obtain ⟨x, hx, hxV⟩ := hgin
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hxV
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨x⁻¹ * g * x, hxV, isConj_iff.mpr ⟨x, by group⟩⟩

/-- **Peterfalvi (12.4) pin (b), step 3** (restriction assembly): if a sub-support `A₁ ⊆ A` carries
only trivial Dade stabilizers (`(hyp.restrict …).H a = ⊥`), then on `A₁`-supported functions the
abstract Dade map of `hyp` **is** induction `Ind_L^G`.  The restricted hypothesis has `H = ⊥`, so
its
Dade map is `Ind_L^G` (step 2 + `IsDadeMap.unique`); `Hypothesis.dadeMap_restrict_apply` identifies
it with `hyp.dadeMap` of the included function. -/
theorem dadeMap_eq_induce_of_supported_on_trivial_H {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) {A₁ : Set G} (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.restrict hA₁A hA₁norm).H a = ⊥)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A₁ L) :
    hyp.dadeMap (OddOrder.Peterfalvi.S04.SupportedClassFunctions.inclusion
        (G := G) (k := ℂ) (L := L) hA₁A α)
      = ClassFunction.induce L (α : ClassFunction ↥L ℂ) := by
  have h1 := OddOrder.Peterfalvi.S04.IsDadeMap.unique
    ((hyp.restrict hA₁A hA₁norm).isDadeMap_dadeMap (k := ℂ))
    (isDadeMap_induce_of_forall_H_eq_bot (hyp.restrict hA₁A hA₁norm) hH₁)
  rw [← hyp.dadeMap_restrict_apply hA₁A hA₁norm α]
  exact congrFun h1 α

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (b), type-I bridge**: for a type-I maximal `L`, on a class function `f`
supported in a trivial-`H` sub-support `A₁ ⊆ A(L)` (an `L`-invariant subset on which the type-I Dade
stabilizers vanish), the Dade isometry `τ` acts as induction `Ind_L^G`.  This instantiates the
general step-3 bridge `dadeMap_eq_induce_of_supported_on_trivial_H` at the type-I Dade map `hyp.tau`
(via `dadeIntegralCharacterMap_apply_of_support`, and `inclusion` to widen the support from `A₁`). -/
theorem typeI_tau_eq_induce_of_supported_trivial_H {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {A₁ : Set G} (hA₁A : A₁ ⊆ hyp.ambientA)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥)
    {f : ClassFunction ↥L ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ L) :
    hyp.tau f = ClassFunction.induce L f := by
  haveI := hyp.finiteG
  have hfA : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  have h1 : hyp.tau f = hyp.dadeData.dade.dadeMap (k := ℂ)
      ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hfA⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hfA
  rw [h1]
  -- `⟨f, hfA⟩` is defeq to `inclusion hA₁A ⟨f, hf⟩` (same carrier `f`), so step 3 applies directly.
  exact dadeMap_eq_induce_of_supported_on_trivial_H hyp.dadeData.dade hA₁A hA₁norm hH₁
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- The escaping-centralizer set `{a ∈ X : ¬ C_G(a) ≤ M}` is `M`-conjugation invariant when `X` is
(`C_G(gag⁻¹) = g·C_G(a)·g⁻¹` and `g ∈ M` normalizes `M`).  The `L`-invariance of the trivial-`H`
sub-support `A(L) ∖ escaping` rests on this. -/
private theorem escaping_conj_mem_iff {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    g * x * g⁻¹ ∈ escapingCentralizerSet M X ↔ x ∈ escapingCentralizerSet M X := by
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg) :
      MulAut.conj g • M = M)]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  simp only [escapingCentralizerSet, Set.mem_setOf_eq, hmem, hcent]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Constituents of `χ = Ind_K^L θ` (`K = (L_F).subgroupOf L ⊴ L`) have equal restriction to `K`**
(the multiplicity-one case of Clifford's theorem [Is] 6.2, character level).  Two constituents
`φ₁, φ₂ ∈ S(χ)` both occur in `χ = Ind_K^L θ` with multiplicity one, so both lie over `θ`; by
Clifford single-orbit (`restrictionConstituentsSingleOrbit_of_isIrreducible`) the constituents of
`Res_K φᵢ` are exactly the `L`-orbit of `θ`, each with the common multiplicity one, whence
`Res_K φ₁ = Res_K φ₂`.  Computed at the inner-product level via Fourier: for every `ψ ∈ Irr K`,
`⟨Res_K φᵢ, ψ⟩ = ⟨φᵢ, Ind_K ψ⟩` (Frobenius) is `1` when `ψ` is `L`-conjugate to `θ`
(`Ind_K ψ = Ind_K θ = χ`, multiplicity one) and `0` otherwise (single-orbit), independently of `i`.
This is the [Is] 6.2 input Peterfalvi (12.4) cites for `Supp(φ₁ − φ₂) ⊆ A(L) − H^#`. -/
theorem restrict_eq_of_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ₂ : ClassFunction ↥L ℂ) := by
  haveI := hyp.finiteG
  classical
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := dχ.chi_mem
  -- Frobenius reciprocity: `⟨φ, Ind_K ψ⟩ = ⟨Res_K φ, ψ⟩`.
  have hfrob : ∀ (φ : IrreducibleCharacter ↥L) (ψ : IrreducibleCharacter ↥K),
      ClassFunction.inner (φ : ClassFunction ↥L ℂ) (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ))
        = ClassFunction.inner (ClassFunction.restrict K (φ : ClassFunction ↥L ℂ))
          (ψ : ClassFunction ↥K ℂ) := by
    intro φ ψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
  -- multiplicity-one: `⟨φ, χ⟩ = 1` for a constituent `φ`.
  have hmult : ∀ φ ∈ dχ.constituents, ClassFunction.inner (φ : ClassFunction ↥L ℂ) chi = 1 := by
    intro φ hφ
    rw [dχ.decomp, inner_sum_right,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg (Ne.symm hne)]),
      irreducibleCharacter_inner, if_pos rfl]
  -- per-`ψ` value of `⟨Res_K φ, ψ⟩`, independent of the constituent `φ`.
  have hval : ∀ φ ∈ dχ.constituents, ∀ ψ : IrreducibleCharacter ↥K,
      ClassFunction.inner (ClassFunction.restrict K (φ : ClassFunction ↥L ℂ))
          (ψ : ClassFunction ↥K ℂ)
        = if (∃ g : ↥L, IrreducibleCharacter.conjBy g θ = ψ) then (1 : ℂ) else 0 := by
    intro φ hφ ψ
    rw [← hfrob φ ψ]
    by_cases hc : ∃ g : ↥L, IrreducibleCharacter.conjBy g θ = ψ
    · rw [if_pos hc]
      obtain ⟨g, rfl⟩ := hc
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.induce_conjBy_eq, ← hchi_eq]
      exact hmult φ hφ
    · rw [if_neg hc]
      by_contra hne
      refine hc ?_
      have hoθ : IrreducibleCharacter.LiesOver K φ θ := by
        rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def,
          ← hfrob φ θ, ← hchi_eq, hmult φ hφ]
        exact one_ne_zero
      have hoψ : IrreducibleCharacter.LiesOver K φ ψ := by
        rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def, ← hfrob φ ψ]
        exact hne
      exact (restrictionConstituentsSingleOrbit_of_isIrreducible φ).exists_conj hoθ hoψ
  -- Fourier: equal inner products with every irreducible `ψ ∈ Irr K` force equality.
  rw [← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (φ₁ : ClassFunction ↥L ℂ)),
      ← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (φ₂ : ClassFunction ↥L ℂ))]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [hval φ₁ h₁ ψ, hval φ₂ h₂ ψ]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the §8 support obligation** ([Is] 6.2 + (8.12.a)): for constituents
`φ₁, φ₂ ∈ S(χ)`, the difference `φ₁ − φ₂` is supported on the **non-escaping** part of `A(L)`,
`A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (= `A(L) − H^#`, exactly where the type-I Dade stabilizers vanish).
By [Is] 6.2 `Res_H φ₁ = Res_H φ₂` (`restrict_eq_of_mem_constituents`, the multiplicity-one Clifford
restriction), so `φ₁ − φ₂` vanishes on `H`; each `φᵢ` is supported on `A(L) ∪ {1}` (carrier
`supported`) and the difference cancels the value at `1` (equal degree).  The escaping points of
`A(L)` lie in `A₁ = H^#` ((8.13.b) `escaping_typeIA_mem_A1`), so the difference vanishes there. -/
theorem constituent_diff_support_subset_nonescaping [Finite G] {L : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (hyp.ambientA \ escapingCentralizerSet L hyp.ambientA) L := by
  haveI := hyp.finiteG
  classical
  have hres := restrict_eq_of_mem_constituents hyp dχ h₁ h₂
  intro x hx
  rw [ClassFunction.mem_support] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, Set.mem_sdiff]
  -- `x` lies in the support of `φ₁` or `φ₂`, hence in `A(L) ∪ {1}`.
  have hxsupp : x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ ({1} : Set ↥L) := by
    rcases ne_or_eq ((φ₁ : ClassFunction ↥L ℂ) x) 0 with h | h
    · exact dχ.supported φ₁ h₁ (ClassFunction.mem_support.mpr h)
    · refine dχ.supported φ₂ h₂ (ClassFunction.mem_support.mpr ?_)
      intro h2
      exact hx (by rw [ClassFunction.sub_apply, h, h2, sub_zero])
  -- `x ≠ 1`: the difference vanishes at `1` by equal degree.
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx (by rw [ClassFunction.sub_apply, ← dχ.equal_degree φ₁ h₁ φ₂ h₂, sub_self])
  have hxAmem : (x : G) ∈ hyp.ambientA := by
    rcases hxsupp with h | h
    · exact OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h
    · exact absurd (Set.mem_singleton_iff.mp h) hx1
  refine ⟨hxAmem, fun hesc => ?_⟩
  -- an escaping point of `A(L)` lies in `A₁ = H^#`, so in `H`, where the two restrictions agree.
  have hxA1 : (x : G) ∈ A1 L PeterfalviType.I :=
    OddOrder.Peterfalvi.S10.escaping_typeIA_mem_A1 hG hyp.maximal hyp.typeI hesc
  have hxH : (x : G) ∈ hyp.typeI.typeF.H := by
    rw [hyp.typeI.typeF.H_eq]
    have hmem : (x : G) ∈ OddOrder.GroupTheory.sharpSubgroup (maxNilpotentNormalHall L) := hxA1
    exact ((Set.mem_sdiff _).mp hmem).1
  have hxK : x ∈ (hyp.typeI.typeF.H).subgroupOf L := Subgroup.mem_subgroupOf.mpr hxH
  refine hx ?_
  have hev : ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (φ₁ : ClassFunction ↥L ℂ) ⟨x, hxK⟩
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (φ₂ : ClassFunction ↥L ℂ) ⟨x, hxK⟩ := by rw [hres]
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply] at hev
  rw [ClassFunction.sub_apply, hev, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (b)** ([Is] 7.7 + (8.12.c) + [Is] 6.2): for constituents `φ₁, φ₂ ∈ S(χ)`,
the Dade isometry acts as induction on the difference, `(φ₁ − φ₂)^τ = Ind_L^G(φ₁ − φ₂)`.

Proof (now genuine, modulo the §8 support obligation): `φ₁ − φ₂` is supported on the non-escaping
part `A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (`constituent_diff_support_subset_nonescaping`), which is
`L`-invariant (`escaping_conj_mem_iff` + `A(L)` `L`-invariant) and carries only trivial Dade
stabilizers (`ftSupportKernel = ⊥` off the escaping set, via `H_eq_ftSupportKernel`).  On such a
trivial-`H` support the type-I Dade isometry coincides with `Ind_L^G`
(`typeI_tau_eq_induce_of_supported_trivial_H`, i.e. pin (b) steps 1–3 + the restriction assembly). -/
theorem constituent_diff_tau_eq_induce {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) =
      ClassFunction.induce L ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) := by
  have hmem : ∀ (l : L) (a : G), ((l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA ↔ a ∈ hyp.ambientA) := by
    intro l a
    refine ⟨fun h => ?_, fun h => hyp.dadeData.dade.L_normalizes_A l h⟩
    have h2 := hyp.dadeData.dade.L_normalizes_A l⁻¹ h
    have h3 : a ∈ typeIA L hyp.typeI := by simpa [Subgroup.coe_inv, mul_assoc] using h2
    exact h3
  have hA₁A : hyp.ambientA \ escapingCentralizerSet L hyp.ambientA ⊆ hyp.ambientA :=
    Set.sdiff_subset
  have hA₁norm : ∀ (l : L) ⦃a : G⦄,
      a ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA →
      (l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA := by
    intro l a ha
    exact ⟨hyp.dadeData.dade.L_normalizes_A l ha.1,
      fun hesc => ha.2 ((escaping_conj_mem_iff l.2 (hmem l a)).mp hesc)⟩
  have hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H, hyp.dadeData.H_eq_ftSupportKernel]
    exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping a.2.2
  exact typeI_tau_eq_induce_of_supported_trivial_H hyp hA₁A hA₁norm hH₁
    (constituent_diff_support_subset_nonescaping hG hyp dχ h₁ h₂)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), coherence → coefficient-equality bridge** (genuine).  If `ψ ⊥ R(χ)`, then
`Res_L ψ` has the *same* coefficient on every constituent of `χ`: `⟨Res_L ψ, φ₁⟩ = ⟨Res_L ψ, φ₂⟩`
for `φ₁, φ₂ ∈ S(χ)`.  Proof: `⟨Res_L ψ, φ₁ − φ₂⟩ = ⟨ψ, Ind_L^G(φ₁ − φ₂)⟩ = ⟨ψ, (φ₁ − φ₂)^τ⟩`
(Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry + pin (b)), and this is `0` because
`(φ₁ − φ₂)^τ ∈ ℤ[R(χ)]` (pin (a)) and `ψ ⊥ R(χ)` (`inner_eq_zero_of_mem_zSpan`).  This is the
genuine
content by which `ψ ⊥ R(χ)` forces the `∪S(χ)`-part of `Res_L ψ` to be `β = ∑_χ c_χ·χ ∈ ℂ[S]`. -/
theorem Sset_coeff_equal {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {psi : ClassFunction G ℂ} (horth : ∀ α ∈ Rset dχ, ClassFunction.inner psi α = 0)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.inner (ClassFunction.restrict L psi) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₂ : ClassFunction ↥L ℂ) := by
  haveI := hyp.finiteG
  set f : ClassFunction ↥L ℂ :=
    (φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ) with hf
  -- `⟨ψ, τ f⟩ = 0`: `τ f ∈ ℤ[R(χ)]` (pin a) and `ψ ⊥ R(χ)`.
  have hψτ : ClassFunction.inner psi (hyp.tau f) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan horth
      (constituent_diff_tau_mem_span hyp dχ h₁ h₂)
  -- `⟨f, Res_L ψ⟩ = ⟨Ind_L^G f, ψ⟩ = ⟨τ f, ψ⟩ = star⟨ψ, τ f⟩ = 0`.
  have hfres : ClassFunction.inner f (ClassFunction.restrict L psi) = 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict L f psi,
      ← constituent_diff_tau_eq_induce hG hyp dχ h₁ h₂,
      inner_conj_symm psi (hyp.tau f), hψτ, star_zero]
  -- `⟨Res_L ψ, f⟩ = star⟨f, Res_L ψ⟩ = 0`, then split the difference.
  have hresf : ClassFunction.inner (ClassFunction.restrict L psi) f = 0 := by
    rw [inner_conj_symm f (ClassFunction.restrict L psi), hfres, star_zero]
  rw [hf, ClassFunction.inner_sub_right] at hresf
  exact sub_eq_zero.mp hresf

/-- The "`H ⊆ ker φ`" predicate: the Fitting subgroup `H = L_F` lies in the character kernel of the
irreducible character `φ` of `L`.  The `γ`-components of `Res_L ψ` in (12.4) are exactly those `φ`
with `InHKernel`; they are constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`). -/
def InHKernel {L : Subgroup G} (hyp : Hypothesis L) (φ : IrreducibleCharacter ↥L) : Prop :=
  ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) ⊆
    OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the off-kernel direction** (genuine): every constituent `φ ∈ S(χ)` of a
member `χ = Ind_H^L θ ∈ S` (`θ ≠ 1_H`) is off-kernel, `H ⊄ ker φ`.  If `H ⊆ ker φ` then `Res_H φ` is
constant `= φ(1)` on `H` (`= φ(1)·1_H`), so by Frobenius
`⟨χ, φ⟩ = ⟨θ, Res_H φ⟩ = star(φ(1))·⟨θ, 1_H⟩
= 0` (`θ ≠ 1_H`); but `φ` a constituent of `χ` gives `⟨χ, φ⟩ = 1`.  This is the `⊇` inclusion
`S(χ) ⊆ {φ : H ⊄ ker φ}` of the partition `exists_offKernel_constituent_partition`. -/
theorem constituents_not_inHKernel {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hχ : chi ∈ hyp.Sset) (dχ : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ dχ.constituents) : ¬ InHKernel hyp φ := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := hχ
  intro hker
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  -- `Res_K φ = φ(1) · 1_K` (since `H ⊆ ker φ`, `φ` is constant `= φ(1)` on `K`).
  have hrestrict : ClassFunction.restrict K (φ : ClassFunction ↥L ℂ)
      = OddOrder.Peterfalvi.S03.characterDegree (φ : ClassFunction ↥L ℂ) •
        (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    ext k
    rw [ClassFunction.restrict_apply, ClassFunction.smul_apply]
    have hmem : (↑k : ↥L) ∈ OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ) :=
      hker k.2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
    simp only [hmem, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply, mul_one]
  -- `⟨χ, φ⟩ = ⟨θ, Res_K φ⟩ = star(φ(1)) · ⟨θ, 1_K⟩ = 0` (`θ ≠ 1_K`).
  have hzero : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 0 := by
    rw [hchi_eq, ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
      OddOrder.RepresentationTheory.inner_smul_right, irreducibleCharacter_inner, if_neg hθ_ne,
      mul_zero]
  -- `⟨χ, φ⟩ = 1` (multiplicity-one constituent), contradiction.
  have hone : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 1 := by
    rw [dχ.decomp, inner_sum_left,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg hne]),
      irreducibleCharacter_inner, if_pos rfl]
  rw [hone] at hzero
  exact one_ne_zero hzero

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the capturing direction** (genuine): every off-kernel irreducible `φ`
(`H ⊄ ker φ`) is a constituent of some `χ ∈ S`.  By `exists_constituent_not_subset_characterKernel`
([Is] 6.5 / constituent transitivity), `Res_H φ` has a constituent `θ ≠ 1_H`; then
`χ := Ind_H^L θ ∈ S`
and `⟨φ, χ⟩ = ⟨Res_H φ, θ⟩ ≠ 0` (Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry),
so
`φ ∈ S(χ)`.  This is the `⊆` inclusion `{φ : H ⊄ ker φ} ⊆ ⋃ S(χ)` of the partition
`exists_offKernel_constituent_partition`. -/
theorem not_inHKernel_imp_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} (hφ : ¬ InHKernel hyp φ) :
    ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hlo, hθker⟩ :=
    exists_constituent_not_subset_characterKernel
      (le_refl ((hyp.typeI.typeF.H).subgroupOf L)) φ hφ
  -- `θ ≠ 1`: else `K = K.subgroupOf K ⊆ ker θ = univ`, contradicting `hθker`.
  have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rintro rfl
    exact hθker (by
      simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction, Set.subset_univ])
  -- `θ` is a genuine constituent of `Res_K φ`.
  have hlo' : ClassFunction.inner
      (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ≠ 0 := by
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  -- `⟨φ, Ind_K θ⟩ = ⟨Res_K φ, θ⟩ ≠ 0` (Frobenius + conjugate symmetry).
  have hinner_ne : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    exact hlo'
  by_contra hnotin
  apply hinner_ne
  rw [(data _ ⟨θ, hθ_ne, rfl⟩).decomp, inner_sum_right]
  refine Finset.sum_eq_zero fun φ' hφ' => ?_
  have hne : φ ≠ φ' := by rintro rfl; exact hnotin hφ'
  rw [irreducibleCharacter_inner, if_neg hne]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Pin (c') partition characterization** (genuine, both directions): the off-kernel irreducibles
`{φ : H ⊄ ker φ}` are *exactly* the constituents of the `S`-members, `⋃_{χ ∈ S} S(χ)`.  `⊆` is the
capturing direction `not_inHKernel_imp_mem_constituents`; `⊇` is `constituents_not_inHKernel`.  This
is the set-equality underlying the `biUnion` of `exists_offKernel_constituent_partition`; the
residual
of that pin is now only the **disjointness** (φ in `S(χ) ∩ S(χ')` ⟹ χ = χ', via Clifford
single-orbit
`RestrictionConstituentsSingleOrbit.exists_conj` + `induce_conjBy_eq`) and the `parts`-`Finset`
construction. -/
theorem not_inHKernel_iff {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} :
    ¬ InHKernel hyp φ ↔
      ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents :=
  ⟨not_inHKernel_imp_mem_constituents hyp data,
    fun ⟨χ, hχ, hmem⟩ => constituents_not_inHKernel hyp hχ (data χ hχ) hmem⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), disjointness** (genuine, Clifford single-orbit): a `φ` that is a
constituent of both `χ, χ' ∈ S` forces `χ = χ'`.  Writing `χ = Ind_H^L θ`, `χ' = Ind_H^L θ'`, both
witnesses `θ, θ'` lie under `φ` (`⟨Res_H φ, θ⟩ = ⟨φ, χ⟩ ≠ 0`, Frobenius); by Clifford single-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible` + `.exists_conj`) they are `L`-conjugate,
`conjBy g θ = θ'`, so `Ind θ = Ind θ'` (`induce_conjBy_eq`, Peterfalvi (1.5.a)).  This is the
`PairwiseDisjoint` content of `exists_offKernel_constituent_partition`. -/
theorem constituents_eq_of_mem {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    (dχ : CharacterDecompositionData hyp χ) (dχ' : CharacterDecompositionData hyp χ')
    {φ : IrreducibleCharacter ↥L} (hmem : φ ∈ dχ.constituents) (hmem' : φ ∈ dχ'.constituents) :
    χ = χ' := by
  haveI := hyp.finiteG
  classical
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hχ'
  -- `θ`, `θ'` lie under `φ`: `⟨Res_K φ, η⟩ = ⟨φ, Ind_K η⟩ = 1 ≠ 0` for a constituent.
  have key : ∀ (η : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
      (dη : CharacterDecompositionData hyp
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)))
      (_ : φ ∈ dη.constituents),
      IrreducibleCharacter.LiesOver ((hyp.typeI.typeF.H).subgroupOf L) φ η := by
    intro η dη hη
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def]
    have hval : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)) = 1 := by
      rw [dη.decomp, inner_sum_right,
        Finset.sum_eq_single_of_mem φ hη (fun φ' _ hne => by
          rw [irreducibleCharacter_inner, if_neg (Ne.symm hne)]),
        irreducibleCharacter_inner, if_pos rfl]
    have hrel : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ))
        = ClassFunction.inner
          (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
          (η : ClassFunction _ ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        ClassFunction.inner_induce_eq_inner_restrict,
        OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    rw [← hrel, hval]; exact one_ne_zero
  obtain ⟨g, hg⟩ :=
    (restrictionConstituentsSingleOrbit_of_isIrreducible φ).exists_conj
      (key θ dχ hmem) (key θ' dχ' hmem')
  rw [← hg]
  exact (ClassFunction.induce_conjBy_eq (H := (hyp.typeI.typeF.H).subgroupOf L) g
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)).symm

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (c)** ([Is] 6.2 capturing + (1.5.a)/(1.2)): the off-kernel irreducible
characters `{φ : H ⊄ ker φ}` partition into the constituent-sets `S(χ)`, `χ ∈ S`.  By [Is] 6.2,
`H ⊄ ker φ ⟹ Res_H φ` has a non-trivial constituent `θ`, so `φ ∈ S(Ind_H^L θ)`; the orbit `θ`
determines `χ = Ind θ` uniquely ((1.5.a)/(1.2)), so the `S(χ)` are pairwise disjoint and cover the
off-kernel irreducibles.  This is the genuine cross-section content (the [Is] 6.2 partition); the
`β`-vanishing regroup `Sset_offKernel_vanishes_off_H` is proved from it. -/
theorem exists_offKernel_constituent_partition {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) :
    ∃ parts : Finset {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset},
      Finset.univ.filter (fun φ => ¬ InHKernel hyp φ) =
        parts.biUnion (fun χ => (data χ.1 χ.2).constituents) ∧
      (↑parts : Set {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset}).PairwiseDisjoint
        (fun χ => (data χ.1 χ.2).constituents) := by
  haveI := hyp.finiteG
  classical
  by_cases hne : (Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).Nonempty
  · -- The off-kernel filter is nonempty, so `S` is nonempty; build the capturing map.
    obtain ⟨φ0, hφ0⟩ := hne
    rw [Finset.mem_filter] at hφ0
    obtain ⟨χ0, hχ0, -⟩ := not_inHKernel_imp_mem_constituents hyp data hφ0.2
    haveI : Nonempty {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} := ⟨⟨χ0, hχ0⟩⟩
    let cap : IrreducibleCharacter ↥L → {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} :=
      fun φ => if h : ¬ InHKernel hyp φ then
        ⟨(not_inHKernel_imp_mem_constituents hyp data h).choose,
         (not_inHKernel_imp_mem_constituents hyp data h).choose_spec.choose⟩
      else Classical.arbitrary _
    refine ⟨(Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).image cap, ?_, ?_⟩
    · ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hφ
        refine ⟨cap φ, ⟨φ, hφ, rfl⟩, ?_⟩
        have hcapφ : cap φ = ⟨(not_inHKernel_imp_mem_constituents hyp data hφ).choose,
            (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose⟩ := dif_pos hφ
        rw [hcapφ]
        exact (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose_spec
      · rintro ⟨χs, ⟨φ', _, rfl⟩, hmem⟩
        exact constituents_not_inHKernel hyp (cap φ').2 (data (cap φ').1 (cap φ').2) hmem
    · intro χs _ χs' _ hne_s
      simp only [Function.onFun, Finset.disjoint_left]
      intro φ hmem hmem'
      exact hne_s (Subtype.ext (constituents_eq_of_mem hyp χs.2 χs'.2
        (data χs.1 χs.2) (data χs'.1 χs'.2) hmem hmem'))
  · -- The off-kernel filter is empty; the empty partition works.
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨∅, by rw [hne, Finset.biUnion_empty], by
      rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩


open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the off-kernel regroup** (genuine, from the [Is] 6.2 partition pin): the
off-kernel Fourier part `β = ∑_{φ : H ⊄ ker φ} ⟨Res_L ψ, φ⟩·φ` of `Res_L ψ` vanishes on `L − H`.
Regroup the off-kernel irreducibles by the partition into `S(χ)`
(`exists_offKernel_constituent_partition`); on each `S(χ)` the coefficient `⟨Res_L ψ, φ⟩` is
constant
(`Sset_coeff_equal`, from `ψ ⊥ R(χ)`), so the `S(χ)`-block is `c_χ·∑_{φ ∈ S(χ)} φ = c_χ·χ`
(`decomp`), which vanishes at `g ∈ L − H` (`Sset_vanishes_off_H`). -/
theorem Sset_offKernel_vanishes_off_H {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {g : ↥L} (hg : (g : G) ∉ hyp.H) :
    (∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
      ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g = 0 := by
  obtain ⟨parts, hpart, hdisj⟩ := exists_offKernel_constituent_partition hyp data
  rw [classFunction_sum_apply, hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun χ _ => ?_
  -- The `S(χ)`-block: `∑_{φ ∈ S(χ)} ⟨Res_L ψ, φ⟩ · φ(g) = c_χ · χ(g) = 0`.
  obtain ⟨φ₀, hφ₀⟩ := (data χ.1 χ.2).constituents_nonempty
  have hblock : ∑ φ ∈ (data χ.1 χ.2).constituents,
      (ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₀ : ClassFunction ↥L ℂ) *
        ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply,
      Sset_coeff_equal hG hyp (data χ.1 χ.2) (horth χ.1 χ.2) hφ hφ₀]
  have hdecomp : ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g = χ.1 g := by
    rw [← classFunction_sum_apply, ← (data χ.1 χ.2).decomp]
  rw [hblock, hdecomp, Sset_vanishes_off_H hyp χ.2 hg, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)**: a class function `ψ` orthogonal to every type-I family `R(χ)` (`χ ∈ S`) is
constant on each coset `xH` with `x ∈ L − H`.

Proof: write `Res_L ψ = γ + β` by the Fourier expansion (`sum_inner_irreducibleCharacter_smul`),
splitting `Irr L` into `{H ⊆ ker φ}` (= `γ`) and `{H ⊄ ker φ}` (= `β`).  The kernel part `γ` is
constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`, each `φ` with `H ⊆ ker φ`); the
off-kernel part `β` vanishes on `L − H` (`Sset_offKernel_vanishes_off_H`: by [Is] 6.2 + the
coefficient bridge `Sset_coeff_equal`, `β ∈ ℂ[S]` vanishes off `H`).  Hence
`ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`. -/
theorem orthogonal_character_constant_on_coset {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  haveI := hyp.finiteG
  classical
  intro h hh
  have hhL : h ∈ L := hyp.typeI.typeF.H_le hh
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  set hL : ↥L := ⟨h, hhL⟩ with hhLdef
  set gf : ClassFunction ↥L ℂ := ClassFunction.restrict L psi with hgf
  -- Fourier split of `Res_L ψ = γ + β`.
  set γ : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hγ
  set β : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hβ
  have hsplit : gf = γ + β := by
    rw [hγ, hβ, Finset.sum_filter_add_sum_filter_not]
    exact (sum_inner_irreducibleCharacter_smul gf).symm
  -- `hL` lies in `H` (as a subgroup of `L`).
  have hLmem : hL ∈ ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) :=
    Subgroup.mem_subgroupOf.mpr hh
  -- `γ` is constant on the `H`-coset `xL · hL`.
  have hγconst : γ (xL * hL) = γ xL := by
    rw [hγ, classFunction_sum_apply, classFunction_sum_apply]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply,
      apply_mul_eq_of_mem_characterKernel φ.isIrreducible
        ((Finset.mem_filter.mp hφ).2 hLmem) xL]
  -- `β` vanishes on `L − H` (off-kernel part is in `ℂ[S]`).
  have hxhH : x * h ∉ hyp.H := fun hcon => hxH (by
    have hmem : x * h * h⁻¹ ∈ hyp.H := mul_mem hcon (inv_mem hh)
    rwa [mul_inv_cancel_right] at hmem)
  have hβxh : β (xL * hL) = 0 := by
    rw [hβ]
    exact Sset_offKernel_vanishes_off_H hG hyp data horth (g := xL * hL)
      (by rw [Subgroup.coe_mul]; exact hxhH)
  have hβx : β xL = 0 := by
    rw [hβ]; exact Sset_offKernel_vanishes_off_H hG hyp data horth (g := xL) hxH
  -- Assemble: `ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`.
  have key : gf (xL * hL) = gf xL := by
    simp only [hsplit, ClassFunction.add_apply, hγconst, hβxh, hβx, add_zero]
  have hgxh : gf (xL * hL) = psi (x * h) := by
    rw [hgf, ClassFunction.restrict_apply, Subgroup.coe_mul]
  have hgx : gf xL = psi x := by rw [hgf, ClassFunction.restrict_apply]
  rw [← hgxh, ← hgx]; exact key

/-- **Commutator bridge for the (12.5) core.**  For `H ≤ L` (subgroups of `G`), an element `x` of
`↥(H.subgroupOf L)` lies in the derived subgroup `[G_core, G_core]` of `G_core := ↥(H.subgroupOf L)`
iff its underlying `G`-element lies in `derivedInG H = [H, H]`.  Via the `MulEquiv`
`subgroupOfEquivOfLe : ↥(H.subgroupOf L) ≃* ↥H` (which preserves the commutator subgroup) and
`(derivedInG H).subgroupOf H = commutator ↥H`.  Lets the generic `DpsiH` core (whose `H_core` is
`commutator G_core`) translate its `x ∉ H_core` conclusion back to `h ∉ Hprime`. -/
theorem mem_commutator_subgroupOf_iff {L H : Subgroup G} (hHL : H ≤ L)
    (x : ↥(H.subgroupOf L)) :
    x ∈ commutator ↥(H.subgroupOf L) ↔ ((x : ↥L) : G) ∈ derivedInG H := by
  have hcomm_H : (derivedInG H).subgroupOf H = commutator ↥H := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  set e := Subgroup.subgroupOfEquivOfLe hHL with he
  have hmap : commutator ↥H = (commutator ↥(H.subgroupOf L)).map e.toMonoidHom := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hcoe : ((e x : ↥H) : G) = ((x : ↥L) : G) := rfl
  have hstep1 : x ∈ commutator ↥(H.subgroupOf L) ↔ e x ∈ commutator ↥H := by
    rw [hmap]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hstep2 : e x ∈ commutator ↥H ↔ ((e x : ↥H) : G) ∈ derivedInG H := by
    rw [← hcomm_H, Subgroup.mem_subgroupOf]
  rw [hstep1, hstep2, hcoe]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5)**: for `ψ ∈ CF(G)` orthogonal to the coherent images of the family
(`⟨ψ, χ^ν⟩ = 0` for every `χ ∈ S`), the restriction of the `ρ`-image to `H` is **constant on
`H − H′`** (elements of `H` outside the derived subgroup).

Assembly of the proven pieces: the equal-degree coefficient equality
`chiRhoCF_restrict_inner_eq_of_equal_degree` (`⟨θ₁, Res ρψ⟩ = ⟨θ₂, Res ρψ⟩` for equal-degree
non-trivial `θᵢ`, star-flipped via `ClassFunction.inner_star_comm`), the Clifford (1.7.b) equal
degree of the constituents over a fixed `λ ∈ Irr H′`
(`commutator_induce_constituents_apply_one_eq`), the equal multiplicity
(`inner_induce_constituent_eq_of_apply_one_eq`), and the `DpsiH` span core
`constant_off_normal_of_inner_block_const` (`Res ρψ = Σ_λ a_λ Ind_{H′}^H λ + a·1_H`, each
`Ind_{H′}^H λ` vanishing off `H′`). -/
theorem chiRhoCF_restrict_constant_off_derived {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) {ψ : ClassFunction G ℂ}
    (horth : ∀ χ ∈ hyp.Sset, ClassFunction.inner ψ (coh.extension χ) = 0)
    {x y : ↥((hyp.typeI.typeF.H).subgroupOf L)}
    (hx : x ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
    (hy : y ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) :
    ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ) x
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ) y := by
  haveI := hyp.finiteG
  classical
  set Hc := ((hyp.typeI.typeF.H).subgroupOf L) with hHc
  set g : ClassFunction ↥Hc ℂ :=
    ClassFunction.restrict Hc (hyp.toHypothesis71.chiRhoCF ψ) with hg
  haveI : Fintype ↥(commutator ↥Hc) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(commutator ↥Hc) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥Hc) := Fintype.ofFinite _
  refine OddOrder.RepresentationTheory.constant_off_normal_of_inner_block_const g
    (fun θ₁ θ₂ ρ hθ₁t hθ₂t hlo₁ hlo₂ => ?_) (fun θ₁ θ₂ ρ hlo₁ hlo₂ => ?_) hx hy
  · -- Block-constant coefficients on the non-trivial constituents.
    have hdegθ : (θ₁ : ClassFunction ↥Hc ℂ) 1 = (θ₂ : ClassFunction ↥Hc ℂ) 1 :=
      OddOrder.RepresentationTheory.commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo₁ hlo₂
    have hχ₁ : ClassFunction.induce Hc (θ₁ : ClassFunction ↥Hc ℂ) ∈ hyp.Sset := ⟨θ₁, hθ₁t, rfl⟩
    have hχ₂ : ClassFunction.induce Hc (θ₂ : ClassFunction ↥Hc ℂ) ∈ hyp.Sset := ⟨θ₂, hθ₂t, rfl⟩
    have hdegχ : ClassFunction.induce Hc (θ₁ : ClassFunction ↥Hc ℂ) (1 : ↥L)
        = ClassFunction.induce Hc (θ₂ : ClassFunction ↥Hc ℂ) (1 : ↥L) := by
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one, hdegθ]
    have h := chiRhoCF_restrict_inner_eq_of_equal_degree hyp coh hχ₁ hχ₂ hdegχ hAH
      (horth _ hχ₁) (horth _ hχ₂) rfl rfl
    rw [ClassFunction.inner_star_comm g (θ₁ : ClassFunction ↥Hc ℂ),
      ClassFunction.inner_star_comm g (θ₂ : ClassFunction ↥Hc ℂ), h]
  · -- Block-constant multiplicities.
    have hdegθ : (θ₁ : ClassFunction ↥Hc ℂ) 1 = (θ₂ : ClassFunction ↥Hc ℂ) 1 :=
      OddOrder.RepresentationTheory.commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo₁ hlo₂
    exact OddOrder.RepresentationTheory.inner_induce_constituent_eq_of_apply_one_eq
      hlo₁ hlo₂ hdegθ

end OddOrder.Peterfalvi.S14

