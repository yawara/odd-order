import OddOrder.Peterfalvi.S11_MaximalII_III_IV.CaseBXi

/-!
# InnerCompHom

Prefix-split from `OddOrder.Peterfalvi.S11_MaximalII_III_IV.SummandComplementKernel` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S11
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}



set_option maxHeartbeats 1000000 in
/-- **Case-(b) exhaustion of `𝒳(H₀C)` by `hcPsi`-inductions** (Clifford correspondence, the
surjectivity half of the case-(b) `oXtheta`): every `χ ∈ 𝒳(H₀C)` equals
`Ind_{HC}^{HU}(hcPsi θbar)` for some nontrivial seed `θbar : H̄ →* ℂˣ`.

A constituent `ψ` of `Res_{HC} χ` kills `ker hcHom = H₀C` (kernel inheritance from
`H₀C ⊆ Ker χ`), so it factors through `hcHom : HC ↠ H̄` as `ψ = hcPsi θbar` (`H̄` abelian, the
factored character is linear).  If `θbar = 1` then `ψ` is the trivial (hence `HU`-invariant)
character and Clifford's invariant case (`restrict_eq_restrictionMultiplicity_smul_of_invariant`)
makes `Res_{HC} χ` constant, forcing `H ⊆ Ker χ` — contradicting `χ ∈ 𝒳`.  For `θbar ≠ 1` the
induction `Ind_{HC}(hcPsi θbar)` is irreducible (case-(b) inertia `inertia_eq_hcInHu`), so the
Clifford correspondence (`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`) gives
`χ = Ind_{HC}(hcPsi θbar)`. -/
theorem caseB_xiOf_H0C_eq_induce_hcPsi [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiOf data (chief.H0 ⊔ cSub data chief)) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ, θbar ≠ 1 ∧
      (χ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
  classical
  letI : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  obtain ⟨hχX, hχK⟩ := hχ
  obtain ⟨ψ, hψover⟩ := OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) χ
  haveI hN := realizedH0supCprime_normal_huSub chief
  haveI hNC := realizedH0supC_normal_huSub chief
  haveI hNsub : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hNC.subgroupOf _
  -- `ψ` kills `ker hcHom ⊆ H₀C ⊆ Ker χ`-inherited
  have hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    have hx1 : hcHom chief x = 1 := hx
    have hxH0C : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [hcHom, MonoidHom.comp_apply] at hx1
      have h2 : (QuotientGroup.mk' ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) x)
          = 1 := by
        apply (hcQuotientEquivHbar chief).injective
        rw [map_one]
        exact hx1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff x).mp h2
    exact liesOver_mem_characterKernel hψover (hχK (Subgroup.mem_subgroupOf.mp hxH0C))
  -- factor `ψ` through `hcHom` and make the factor linear
  obtain ⟨ψbar, hψbar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) ψ hker
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbar⟩ :=
    ψbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hψeq : (ψ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = (hcPsi chief θbar : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    rw [← hψbar, ← hθbar]
    ext x
    simp [hcPsi, linearIrreducibleCharacter_apply, ClassFunction.compHom_apply,
      MonoidHom.comp_apply]
  have hψeq' : ψ = hcPsi chief θbar := IrreducibleCharacter.ext hψeq
  rcases eq_or_ne θbar 1 with rfl | hθne
  · -- trivial seed: `ψ` invariant, Clifford forces `H ⊆ Ker χ`, contradiction with `χ ∈ 𝒳`
    exfalso
    have hψtriv : (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        = trivialClassFunction _ := by
      rw [hψeq]
      ext x
      simp [hcPsi, linearIrreducibleCharacter_apply, trivialClassFunction]
    have hinv : ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g ψ = ψ := by
      intro g
      apply IrreducibleCharacter.ext
      rw [IrreducibleCharacter.coe_conjBy, hψtriv]
      ext x
      simp [ClassFunction.conjBy_apply, trivialClassFunction]
    have hres := OddOrder.RepresentationTheory.restrict_eq_restrictionMultiplicity_smul_of_invariant
      (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      χ ψ hψover hinv
    apply hχX
    intro x hx
    rw [SetLike.mem_coe] at hx
    have hxHC : x ∈ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data) := Subgroup.mem_sup_left hx
    have h1 := congrArg (fun f : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ =>
      f (⟨x, hxHC⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))) hres
    have h2 := congrArg (fun f : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ =>
      f (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))) hres
    simp only [ClassFunction.restrict_apply, ClassFunction.smul_apply, hψtriv] at h1 h2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have htriv1 : (trivialClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        ClassFunction _ ℂ) (⟨x, hxHC⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
          M).subgroupOf (huSub data))) = 1 := rfl
    have htriv2 : (trivialClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        ClassFunction _ ℂ) (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
          M).subgroupOf (huSub data))) = 1 := rfl
    rw [htriv1] at h1
    rw [htriv2] at h2
    exact h1.trans h2.symm
  · -- nontrivial seed: Clifford correspondence
    have hθbarnt : (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        ≠ trivialClassFunction _ := by
      intro h0
      apply hθne
      rw [← linearIrreducibleCharacter_eq_trivial_iff]
      exact IrreducibleCharacter.ext
        (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
    have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
    refine ⟨θbar, hθne, ?_⟩
    exact OddOrder.RepresentationTheory.coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
      (G := ↥(huSub data)) χ (hcPsi chief θbar)
      (hcZeta_irreducible chief θbar hθ₀) (hψeq' ▸ hψover)

set_option maxHeartbeats 1600000 in
/-- **Case-(b) pair exhaustion of `𝒳(H₀C')`** (the `C'`-kernel analogue of
`caseB_xiOf_H0C_eq_induce_hcPsi`): every `ζ ∈ 𝒳(H₀C')` equals `Ind_{HC}^{HU}(hcPsiPair θ λ)` for a
nontrivial seed `θ : H̄ →* ℂˣ` and a linear `λ : C →* ℂˣ` trivial on `C'`.

Factors a constituent `ψ` of `Res_{HC} ζ` *not* killing `H`
(`exists_constituent_not_subset_characterKernel`, from `ζ ∈ 𝒳`).  `ψ` is linear
(`[HC,HC] ⊆ H₀C' ⊆ Ker ζ ⟹ Ker ψ`, `commutator_hcInHu_le_realized`); its `C`-restriction is `λ`
(trivial on `C'` since `C' ⊆ H₀C'`), and the correction `φ = ψ·(λ-lift)⁻¹` kills `H₀C`
(`realizedH0supC_eq_realizedH0_sup_cInHu`), so `φ = θ ∘ hcHom` factors through the chief factor
(`exists_compHom_eq_of_subset_characterKernel`), giving `ψ = hcPsiPair θ λ`.  `H ⊄ Ker ψ` forces
`θ ≠ 1`, so the case-(b) inertia `inertia(hcPsiPair θ λ) = HC` (`hcPsiPair_inertia_eq_hc` via
`inertia_eq_hcInHu`) makes `Ind_{HC}(hcPsiPair θ λ)` irreducible and the Clifford correspondence
(`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`) yields
`ζ = Ind_{HC}(hcPsiPair θ λ)`. -/
theorem caseB_xiOf_H0Cprime_eq_induce_hcPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {ζ : IrreducibleCharacter ↥(huSub data)}
    (hζ : ζ ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief)) :
    ∃ (θbar : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ), θbar ≠ 1 ∧
      (∀ c : ↥(cInHu data chief),
        (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
        lam c = 1) ∧
      (ζ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsiPair chief θbar lam).toClassFunction := by
  classical
  letI : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  haveI hNC := realizedH0supC_normal_huSub chief
  haveI : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hNC.subgroupOf _
  obtain ⟨hζX, hζK⟩ := hζ
  -- (1) A constituent `ψ` of `Res_{HC} ζ` not killing `H` (`ζ ∈ 𝒳`, so `H ⊄ Ker ζ`).
  obtain ⟨ψ, hψover, hψnt⟩ :=
    OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
      (A := hInHu data)
      (B := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      le_sup_left ζ hζX
  -- (2) `ψ` kills `H₀C'` (from `H₀C' ⊆ Ker ζ` and lies-over kernel inheritance).
  have hψkerC' : ∀ x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)),
      (x : ↥(huSub data)) ∈ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf
        (huSub data) →
      x ∈ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    exact liesOver_mem_characterKernel hψover (hζK hx)
  -- (3) `ψ` is linear: `[HC,HC] ⊆ H₀C' ⊆ Ker ζ ⊆ Ker ψ`.
  have hψ1 : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) 1 = 1 := by
    haveI : IsMulCommutative (↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ⧸ commutator ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data))) :=
      inferInstanceAs (IsMulCommutative (Abelianization _))
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data))) ψ ?_
    intro g hg
    apply hψkerC'
    have hcomm : ⁅hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data),
        hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)⁆
        ≤ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) := by
      rw [hInHu_sup_realizedH0supC chief]
      exact commutator_hcInHu_le_realized data chief
    apply hcomm
    rw [← derivedInG_eq_commutator]
    exact Subgroup.mem_map_of_mem _ hg
  -- (4) The underlying hom `ψhom` of the linear `ψ`, and `λ = ψhom|_C`.
  obtain ⟨ψhom, hψhom⟩ :=
    ψ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hψ1
  set lam : ↥(cInHu data chief) →* ℂˣ :=
    ψhom.comp (Subgroup.inclusion (cInHu_le_hcRealized chief)) with hlamdef
  -- `ψhom = 1` on any `x ∈ HC` in `Ker ψ`.
  have hψhom_one : ∀ x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)),
      x ∈ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) →
      ψhom x = 1 := by
    intro x hx
    have hval : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) x = 1 := by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hx
      rw [hx]; exact hψ1
    have h2 : (ψhom x : ℂ) = 1 := by rw [← linearIrreducibleCharacter_apply ψhom, hψhom]; exact hval
    exact Units.val_eq_one.mp h2
  -- (5) `λ` kills `C'` (`C' ⊆ H₀C' ⊆ Ker ψ`).
  have hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1 := by
    intro c hc
    rw [hlamdef, MonoidHom.comp_apply]
    refine hψhom_one _ (hψkerC' _ ?_)
    rw [Subgroup.coe_inclusion]
    exact (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_right)) hc
  -- (6) `φ = ψhom · (hcLambdaHom λ)⁻¹` factors through `hcHom` (`φ` kills `H₀C`).
  set φ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →* ℂˣ :=
    ψhom * (hcLambdaHom chief lam)⁻¹ with hφdef
  have hφkerH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤ φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxH : x ∈ (hInHu data).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)) hx
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.mul_apply, MonoidHom.inv_apply,
      hcLambdaHom_eq_one_of_mem_hInHu chief lam hxH, inv_one, mul_one]
    exact hψhom_one x (hψkerC' x
      ((Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_left)) hx))
  have hφkerC : (cInHu data chief).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤ φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxc : x = Subgroup.inclusion (cInHu_le_hcRealized chief)
        (⟨(x : ↥(huSub data)), hx⟩ : ↥(cInHu data chief)) :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    rw [MonoidHom.mem_ker, hxc, hφdef, MonoidHom.mul_apply, MonoidHom.inv_apply,
      hcLambdaHom_inclusion chief lam, hlamdef, MonoidHom.comp_apply, mul_inv_cancel]
  have hH0leHC : (chief.H0.subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    le_trans (Subgroup.subgroupOf_mono (huSub data)
      (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)) le_sup_left
  have hφkerH0C : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤ φ.ker :=
    calc (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        ≤ (((chief.H0.subgroupOf M).subgroupOf (huSub data)) ⊔ cInHu data chief).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
          Subgroup.subgroupOf_mono _ (realizedH0supC_eq_realizedH0_sup_cInHu chief).le
      _ = ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          ⊔ (cInHu data chief).subgroupOf
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
          Subgroup.subgroupOf_sup hH0leHC (cInHu_le_hcRealized chief)
      _ ≤ φ.ker := sup_le hφkerH0 hφkerC
  -- factor `φ = θ ∘ hcHom` at character level (through the chief factor `hcHom`).
  have hkerφ : ((hcHom chief).ker : Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (linearIrreducibleCharacter φ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    have hx1 : hcHom chief x = 1 := hx
    have hxH0C : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [hcHom, MonoidHom.comp_apply] at hx1
      have h2 : (QuotientGroup.mk' ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) x)
          = 1 := by
        apply (hcQuotientEquivHbar chief).injective
        rw [map_one]; exact hx1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff x).mp h2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply_one,
      MonoidHom.mem_ker.mp (hφkerH0C hxH0C), Units.val_one]
  obtain ⟨θbarChar, hθbarChar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) (linearIrreducibleCharacter φ) hkerφ
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbar⟩ :=
    θbarChar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  -- `θbar ∘ hcHom = φ`.
  have hφfac : θbar.comp (hcHom chief) = φ := by
    apply linearIrreducibleCharacter_injective
    apply IrreducibleCharacter.ext
    rw [← ClassFunction.compHom_linearIrreducibleCharacter, hθbar, hθbarChar]
  -- `ψhom = hcPairHom θbar λ`, hence `ψ = hcPsiPair θbar λ`.
  have hψhomeq : ψhom = hcPairHom chief θbar lam := by
    have hunfold : hcPairHom chief θbar lam
        = θbar.comp (hcHom chief) * hcLambdaHom chief lam := rfl
    rw [hunfold, hφfac, hφdef]
    exact (inv_mul_cancel_right ψhom (hcLambdaHom chief lam)).symm
  have hψeq' : ψ = hcPsiPair chief θbar lam := by
    apply IrreducibleCharacter.ext
    rw [← hψhom, hcPsiPair, hψhomeq]
  -- (7) `θbar ≠ 1` (else `ψ|_H = 1`, contradicting `H ⊄ Ker ψ`).
  have hθne : θbar ≠ 1 := by
    intro h1
    apply hψnt
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    have hxh : x = Subgroup.inclusion le_sup_left (⟨(x : ↥(huSub data)), hx⟩ : ↥(hInHu data)) :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hval : (ψ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ℂ) x = 1 := by
      rw [hxh, hψeq', hcPsiPair_apply_inclusion chief θbar lam, h1]
      simp [ClassFunction.compHom_apply]
    rw [hval, hψ1]
  -- (8) inertia `= HC`, `Ind` irreducible, Clifford correspondence.
  have hθbarnt : (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθne
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  refine ⟨θbar, lam, hθne, hlam, ?_⟩
  exact OddOrder.RepresentationTheory.coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
    (G := ↥(huSub data)) ζ (hcPsiPair chief θbar lam)
    (hcZetaPair_irreducible chief θbar lam hθ₀) (hψeq' ▸ hψover)

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Stages-flattening**: a `𝒮`-member whose (irreducible) source equals
`Ind_{HC}^{HU}(hcPsi θbar)` is induced from a linear character of the `M`-level `HC`
(`HC.map subtype`).  The case-split-free tail of the `isIndHC` lemmas: induction in stages
(`induce_induce_subgroupOf`) plus the `subgroupCongr` transport
(`induce_compHom_subgroupCongr`). -/
theorem isIndHC_of_source_eq_induce_hcPsi [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {ζ' : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hζ'eq : (ζ' : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsi chief θbar : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsi chief θbar).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsi, linearIrreducibleCharacter_apply_one]
  · have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsi chief θbar : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsi chief θbar : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr! <;> exact Subsingleton.elim _ _
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsi chief θbar : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Stages-flattening, pair version**: the `hcPsiPair` analogue of
`isIndHC_of_source_eq_induce_hcPsi`.  A `𝒮`-member whose (irreducible) source equals
`Ind_{HC}^{HU}(hcPsiPair θbar λ)` is induced from a linear character of the `M`-level `HC`
(`HC.map subtype`).  Identical case-split-free tail (`induce_induce_subgroupOf` +
`induce_compHom_subgroupCongr`); the seed is the linear pair character rather than `hcPsi`. -/
theorem isIndHC_of_source_eq_induce_hcPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {ζ' : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ} {lam : ↥(cInHu data chief) →* ℂˣ}
    (hζ'eq : (ζ' : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          (hcPsiPair chief θbar lam).toClassFunction) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsiPair chief θbar lam : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsiPair chief θbar lam).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsiPair, linearIrreducibleCharacter_apply_one]
  · have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsiPair chief θbar lam : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsiPair chief θbar lam : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsiPair chief θbar lam : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsiPair chief θbar lam : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsiPair chief θbar lam).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr! <;> exact Subsingleton.elim _ _
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsiPair chief θbar lam : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Peterfalvi (13.3.a) core (Coq `PFsection9.isIndHC`)**: in Clifford case (b), every
*reducible* member of `𝒮(H₀)` is induced from a linear character of `HC` at the `M`-level.
Chain: (9.9.b) membership (`reducible_mem_sOf_H0C`), the `hcPsi`-exhaustion of `𝒳(H₀C)`
(`caseB_xiOf_H0C_eq_induce_hcPsi`), and induction in stages
`Ind^M_{HU} ∘ Ind^{HU}_{HC} = Ind^M_{HC}` (`induce_induce_subgroupOf`, with the
`subgroupCongr`-transport `induce_compHom_subgroupCongr` bridging the two spellings of the
`M`-level `HC`).  In the §13 instantiation `HC = PC`, so this is exactly the (13.3.a)
"`μ_j` is induced from a linear character of `PC`" shape. -/
theorem caseB_reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    [Fintype ↥M]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data chief.H0) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      φ = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  letI : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  -- (9.9.b) membership + exhaustion
  have hφC := reducible_mem_sOf_H0C hG chars φ hφ hred
  obtain ⟨ζ', hζ'xi, rfl⟩ := mem_sOf.mp hφC
  obtain ⟨θbar, hθne, hζ'eq⟩ := caseB_xiOf_H0C_eq_induce_hcPsi caseB hζ'xi
  -- the `M`-level `HC` and the value-preserving iso back to the realized `HC`
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsi chief θbar : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsi chief θbar).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsi, linearIrreducibleCharacter_apply_one]
  · -- `Ind_{HU}^M (Ind_{HC}^{HU} ψ₀) = Ind_K^M (ψ₀ ∘ f)` by stages + `subgroupCongr` transport
    have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsi chief θbar : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    -- identify the inner induction with `Ind_{HC}^{HU}(hcPsi θbar)`
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsi chief θbar : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    show induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr! <;> exact Subsingleton.elim _ _
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsi chief θbar : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

/-- **`ζ(1) = u`**: the degree of `ζ = Ind_{HC}^{HU}(ψ)` is `u`.  `induce_apply_one` gives
`ζ(1) = [HU:HC]·ψ(1) = u·1` (`hc_index_eq_u`, and `ψ` linear so `ψ(1)=1`).  This is the degree-`u`
of the (9.8.c) irreducible; `induceHU ζ` then has degree `q·u = qu`. -/
theorem hcZeta_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (1 : ↥(huSub data))
      = (chars.u : ℂ) := by
  rw [ClassFunction.induce_apply_one, hc_index_eq_u chars,
    show (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        = 1 from by simp [hcPsi, linearIrreducibleCharacter_apply_one], mul_one]

/-- **`H₀C ⊆ Ker ψ`** (`HC`-level, pointwise): every `x` in the realized `H₀C` lies in the character
kernel of the `HC`-linear character `ψ`, since `ψ = θ ∘ hcHom` and `hcHom` kills `H₀C`
(`hcHom_eq_one_of_mem_realizedH0supC`).  Stated *without* the induce/Fintype/Invertible instances so
the giant `HC` term never enters a `whnf`-exploding unification; the induce-kernel step below cites it
pointwise. -/
theorem hcPsi_mem_characterKernel_of_mem_realizedH0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    x ∈ OddOrder.Peterfalvi.S03.characterKernel (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcPsi]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one, MonoidHom.comp_apply,
    hcHom_eq_one_of_mem_realizedH0supC chief hx, map_one, Units.val_one]

/-- **`H₀C ⊆ Ker ψ`** as a `Set` inclusion (`HC`-level), instance-free.  Packages the pointwise
`hcPsi_mem_characterKernel_of_mem_realizedH0supC` into the `hker` argument of
`subsetCharacterKernel_induce_of_subgroupOf`, kept *outside* the induce/Invertible instance scope so
the giant `HC` card never enters an `isDefEq`-exploding comparison. -/
theorem hcPsi_realizedH0supC_subgroupOf_subset_characterKernel [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcPsi chief θ) := by
  intro x hx
  exact hcPsi_mem_characterKernel_of_mem_realizedH0supC chief θ (SetLike.mem_coe.mp hx)

set_option maxHeartbeats 1000000 in
/-- **`H₀C ⊆ Ker ζ`**: the realized `H₀C` lies in the character kernel of `ζ = Ind_{HC}^{HU}(ψ)`.
Since `ψ` is `1` on `H₀C` (`hcPsi_mem_characterKernel_of_mem_realizedH0supC`) and `H₀C ◁ HC ≤ HU`,
the normal subgroup `H₀C` lies in `Ker(Ind ψ)` (`subsetCharacterKernel_induce_of_subgroupOf`).  This
is the `H₀C ⊆ Ker` half of `ζ ∈ 𝒳(H₀C)`.  The pointwise body is delegated to the instance-free
lemma above so the giant `HC`/`ψ` term never enters a `whnf`-exploding manipulation here. -/
theorem hcZeta_H0supC_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) : ℂ)] :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ)) := by
  haveI := realizedH0supC_normal_huSub chief
  exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    le_sup_right (hcPsi chief θ)
    (hcPsi_realizedH0supC_subgroupOf_subset_characterKernel chief θ)

set_option maxHeartbeats 1000000 in
/-- **`H ⊄ Ker ζ`** (`ζ ∈ 𝒳`): the irreducible `ζ = Ind_{HC}^{HU}(ψ)` is nontrivial on `H = hInHu`.
`ζ` lies over `ψ` (Frobenius: `⟨Ind ψ, ζ⟩ = ⟨ζ,ζ⟩ = 1`), so `H ⊆ Ker ζ` would descend
(`liesOver_mem_characterKernel`) to `H ⊆ Ker ψ` (`ψ|_H = 1`).  But `ψ|_H` is the inflation of `θ`
(`hcPsi_apply_inclusion`) and the descent hom `(mk' N) ∘ hInHuEquivH` is surjective, so `ψ|_H = 1`
forces `θ = 1`, contradicting `hθnt`.  The `xiSet` half of `ζ ∈ 𝒳(H₀C)`. -/
theorem hcZeta_mem_xiSet [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  classical
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ with hζdef
  -- `ζ` lies over `ψ`: Frobenius `⟨Ind ψ, ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0`.
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      ζ (hcPsi chief θ) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  -- Assume `H ⊆ Ker ζ` for contradiction; show `θ = 1`.
  rw [xiSet, Set.mem_setOf_eq]
  intro hsub
  apply hθnt
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun q => ?_
  obtain ⟨h, hhq⟩ := hfsurj q
  -- `(incl h : HU) ∈ H`, so it lies in `Ker ζ`, descending to `incl h ∈ Ker ψ`.
  have hgmem : ((Subgroup.inclusion
      (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) h : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (hcPsi chief θ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) 1 = 1 := by
    simp [hcPsi]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcPsi_apply_inclusion chief θ h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  -- `hψker : (θ ((mk' N) (hInHuEquivH h)) : ℂ) = 1`, and `(mk' N)(hInHuEquivH h) = q`.
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  show θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
/-- **`ζ ∈ 𝒳(H₀C)`**: combining the two halves `H ⊄ Ker ζ` (`hcZeta_mem_xiSet`) and `H₀C ⊆ Ker ζ`
(`hcZeta_H0supC_subset_ker`).  This is the source character of the (9.8.c) `𝒮(H₀C)`-member
`Ind_{HU}^M ζ` of degree `qu`. -/
theorem hcZeta_mem_xiOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ cSub data chief) := by
  rw [mem_xiOf]
  exact ⟨hcZeta_mem_xiSet chief θ hθnt hθ₀, hcZeta_H0supC_subset_ker chief θ⟩

/-- A nontrivial linear seed has a nontrivial character coercion (the seed form consumed by the
case-(b) inertia lift `inertia_eq_hcInHu`). -/
theorem linearIrreducibleCharacter_coe_ne_trivial_of_ne_one {K : Type*} [Group K] [Finite K]
    {θ : K →* ℂˣ} (hθ : θ ≠ 1) :
    (linearIrreducibleCharacter θ : ClassFunction K ℂ) ≠ trivialClassFunction K := by
  intro h0
  apply hθ
  rw [← linearIrreducibleCharacter_eq_trivial_iff]
  exact IrreducibleCharacter.ext
    (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)

/-- **A reducible `M`-induction has an `M`-invariant source** (inertia dichotomy at the prime
index `q = [M:HU]`): if `Ind_{HU}^M ζ` is *not* irreducible, then every `M`-conjugate of
`ζ ∈ Irr(HU)` equals `ζ`.  The inertia `I_M(ζ)` lies between `HU` and `M`
(`subgroup_le_inertia`); `[M:HU] = q` prime (`huSub_index_eq_q`) leaves `I = HU` or `I = M`
(`relIndex_mul_index`), and `I = HU` would make the induction irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`).  The injectivity input of the (9.9.c)
`|Xζ| = p−1` count. -/
theorem conjBy_eq_self_of_not_isIrreducibleCharacter_induceHU [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hred : ¬ IsIrreducibleCharacter (induceHU data (ζ : ClassFunction ↥(huSub data) ℂ)))
    (w : ↥M) : IrreducibleCharacter.conjBy w ζ = ζ := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hle : huSub data ≤ ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.subgroup_le_inertia _
  have hq : (data.q).Prime := data.nontrivial.2.1
  have hmul := Subgroup.relIndex_mul_index (H := huSub data)
    (K := ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)) hle
  rw [huSub_index_eq_q] at hmul
  have hdvd : (ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)).index ∣ data.q :=
    ⟨_, by rw [mul_comm]; exact hmul.symm⟩
  have htop : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤ := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h1 | hqq
    · exact Subgroup.index_eq_one.mp h1
    · -- `I.index = q` forces `relIndex = 1`, i.e. `I ≤ HU`, so `I = HU` — induction irreducible.
      exfalso
      rw [hqq] at hmul
      have hrel1 : (huSub data).relIndex
          (ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)) = 1 :=
        Nat.eq_of_mul_eq_mul_right hq.pos (hmul.trans (one_mul data.q).symm)
      have hIle : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) ≤ huSub data :=
        Subgroup.relIndex_eq_one.mp hrel1
      exact hred (OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq ζ
        (le_antisymm hIle hle))
  have hw : w ∈ ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) :=
    htop ▸ Subgroup.mem_top w
  rw [ClassFunction.mem_inertia] at hw
  exact IrreducibleCharacter.ext (by rw [IrreducibleCharacter.coe_conjBy]; exact hw)

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Peterfalvi (9.9.c), the `u`-formula half**: in Clifford case (b), if `𝒮(H₀C')` contains
no irreducible character then `u = (p^q−1)/(p−1)`.

With `C = ⊥` (`caseB_no_irreducible_forces_C_bot`) all the joins collapse to `H₀`, so every
member of `𝒮(H₀)` is reducible.  Count `𝒳(H₀)` two ways: the case-(b) `oXtheta`
(`caseB_oXtheta_count`) gives `u·|Xζ| = p^q−1` for the set `Xζ` of `hcPsi`-inductions, which
exhausts `𝒳(H₀)` (`caseB_xiOf_H0C_eq_induce_hcPsi`); and `Ind_{HU}^M` maps `Xζ` *bijectively*
onto the `p−1` reducible members of `𝒮(H₀)` (`reducible_count_sOf_H0`) — injectivity because a
reducible induction has an `M`-invariant source (`conjBy_eq_self_of_…`, prime-index inertia
dichotomy), so `Ind ζ₁ = Ind ζ₂ ⟹ ζ₂ = ζ₁^w = ζ₁`.  Hence `u·(p−1) = p^q−1`. -/
theorem caseB_no_irreducible_u_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) :
    chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  classical
  have hCbot : cSub data chief = ⊥ := caseB_no_irreducible_forces_C_bot hG chars caseB hno
  have hCpbot : cprimeSub data chief = ⊥ :=
    le_bot_iff.mp (hCbot ▸ cprimeSub_le_C data chief)
  have hcollapse : chief.H0 ⊔ cSub data chief = chief.H0 := by rw [hCbot, sup_bot_eq]
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  -- `hno` in `𝒮(H₀)`-form (`C' = ⊥` collapses the join)
  have hno' : ∀ φ ∈ sOf data chief.H0, ¬ IsIrreducibleCharacter φ := by
    intro φ hφ hirr
    apply hno
    refine ⟨φ, ?_, hirr⟩
    show φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief)
    rw [hCpbot, sup_bot_eq]
    exact hφ
  -- the case-(b) `oXtheta` count
  have hcount := caseB_oXtheta_count (chars := chars) caseB
  set NF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1 with hNF
  set Xz := NF.image fun θ =>
    ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) (hcPsi chief θ).toClassFunction with hXz
  -- every `Xζ`-member is (the coercion of) a `𝒳(H₀)`-irreducible
  have hXmem : ∀ φz ∈ Xz, ∃ ζ : IrreducibleCharacter ↥(huSub data),
      (ζ : ClassFunction ↥(huSub data) ℂ) = φz ∧ ζ ∈ xiOf data chief.H0 := by
    intro φz hφz
    obtain ⟨θ, hθNF, rfl⟩ := Finset.mem_image.mp hφz
    have hθne : θ ≠ 1 := (Finset.mem_filter.mp hθNF).2
    have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly
      (linearIrreducibleCharacter_coe_ne_trivial_of_ne_one hθne)
    refine ⟨⟨_, hcZeta_irreducible chief θ hθ₀⟩, rfl, ?_⟩
    have hxi := hcZeta_mem_xiOf chief θ hθne hθ₀
    exact (congrArg (xiOf data) hcollapse) ▸ hxi
  -- their `M`-inductions are reducible `𝒮(H₀)`-members
  have hXred : ∀ φz ∈ Xz, induceHU data φz ∈ sOf data chief.H0
      ∧ ¬ IsIrreducibleCharacter (induceHU data φz) := by
    intro φz hφz
    obtain ⟨ζ, hζcoe, hζxi⟩ := hXmem φz hφz
    have hmem : induceHU data φz ∈ sOf data chief.H0 := by
      rw [← hζcoe]
      exact mem_sOf.mpr ⟨ζ, hζxi, rfl⟩
    exact ⟨hmem, hno' _ hmem⟩
  -- `Ind_{HU}^M` is injective on `Xζ` (reducible inductions have `M`-invariant sources)
  have hinj : Set.InjOn (fun φz => induceHU data φz)
      (Xz : Set (ClassFunction ↥(huSub data) ℂ)) := by
    intro φz₁ h1 φz₂ h2 heq
    rw [Finset.mem_coe] at h1 h2
    obtain ⟨ζ₁, hζ₁coe, -⟩ := hXmem φz₁ h1
    obtain ⟨ζ₂, hζ₂coe, -⟩ := hXmem φz₂ h2
    have hred1 : ¬ IsIrreducibleCharacter (induceHU data (ζ₁ : ClassFunction _ ℂ)) := by
      rw [hζ₁coe]
      exact (hXred φz₁ h1).2
    have heq' : induceHU data (ζ₁ : ClassFunction _ ℂ)
        = induceHU data (ζ₂ : ClassFunction _ ℂ) := by
      rw [hζ₁coe, hζ₂coe]
      exact heq
    obtain ⟨w, hw⟩ := (OddOrder.RepresentationTheory.induce_eq_induce_iff_conj
      (G := ↥M) (H := huSub data) ζ₁ ζ₂).mp heq'
    have hfix := conjBy_eq_self_of_not_isIrreducibleCharacter_induceHU ζ₁ hred1 w
    rw [← hζ₁coe, ← hζ₂coe, ← hw, hfix]
  -- the image is exactly the reducible part of `𝒮(H₀)` (exhaustion for `⊇`)
  have himg : (fun φz => induceHU data φz) '' (Xz : Set (ClassFunction ↥(huSub data) ℂ))
      = {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ} := by
    ext φ
    constructor
    · rintro ⟨φz, hφz, rfl⟩
      rw [Finset.mem_coe] at hφz
      exact ⟨(hXred φz hφz).1, (hXred φz hφz).2⟩
    · rintro ⟨hφS, hφred⟩
      obtain ⟨ζ', hζ'xi, rfl⟩ := mem_sOf.mp hφS
      have hζ'xiC : ζ' ∈ xiOf data (chief.H0 ⊔ cSub data chief) :=
        (congrArg (xiOf data) hcollapse).symm ▸ hζ'xi
      obtain ⟨θbar, hθne, hζ'eq⟩ := caseB_xiOf_H0C_eq_induce_hcPsi caseB hζ'xiC
      refine ⟨(ζ' : ClassFunction ↥(huSub data) ℂ), ?_, rfl⟩
      rw [Finset.mem_coe, hζ'eq]
      exact Finset.mem_image.mpr ⟨θbar,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθne⟩, rfl⟩
  -- `|Xζ| = p − 1`
  have hXcard : Xz.card = chief.p - 1 :=
    calc Xz.card = (Xz : Set (ClassFunction ↥(huSub data) ℂ)).ncard :=
          (Set.ncard_coe_finset Xz).symm
      _ = ((fun φz => induceHU data φz) '' (Xz : Set (ClassFunction ↥(huSub data) ℂ))).ncard :=
          (Set.InjOn.ncard_image hinj).symm
      _ = chief.p - 1 := by rw [himg]; exact reducible_count_sOf_H0 hG chief
  -- assemble: `u·(p−1) = p^q − 1` (`set` already folded `NF`/`Xz` into `hcount`)
  rw [hXcard] at hcount
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  rw [← hcount]
  exact (Nat.mul_div_cancel _ hp1).symm


/-- **Degree of the (9.8.c) `𝒮`-member**: `(Ind_{HU}^M ζ)(1) = q·u = qu`.  Combines the `HU→M`
index `[M:HU] = q` (`induceHU_apply_one_eq_q_mul`) with `ζ(1) = u` (`hcZeta_apply_one`). -/
theorem hcZeta_induceHU_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ) (1 : ↥M)
      = ((data.q * chars.u : ℕ) : ℂ) := by
  rw [induceHU_apply_one_eq_q_mul, hcZeta_apply_one chars θ, Nat.cast_mul]

/-- **`Ind_{HU}^M ζ ∈ 𝒮(H₀C)`**: the (9.8.c) degree-`qu` character is a member of `𝒮(H₀C)`, witnessed
by its source `ζ ∈ 𝒳(H₀C)` (`hcZeta_mem_xiOf`). -/
theorem hcZeta_induceHU_mem_sOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ cSub data chief) := by
  rw [mem_sOf]
  exact ⟨⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩,
    hcZeta_mem_xiOf chief θ hθnt hθ₀, rfl⟩

/-- **`Ind_{HU}^M ζ` is irreducible** given `ζ` is not `W₁`-fixed (`I_M(ζ) ≠ M`).  Since `HU ◁ M`
with `[M : HU] = q` prime, `HU ≤ I_M(ζ) ≤ M` and `I_M(ζ) ≠ M` force `I_M(ζ) = HU`
(`eq_of_le_of_prime_index`), whence `Ind_{HU}^M ζ` is irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`).  The remaining input `hIM` (`ζ` not `W₁`-fixed) is
supplied by propagating `θ̄`'s free-`W₁`-orbit (`clifford_caseA_exists_char_inertia_hc_not_fixed`'s
`w₀` datum) through the construction. -/
theorem hcZeta_induceHU_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief)
    (hIM : ClassFunction.inertia (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ) ≠ ⊤) :
    IsIrreducibleCharacter (induceHU data (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ)) := by
  -- `letI` (not `haveI`) keeps the instances transparent so `induceHU = ClassFunction.induce`
  -- holds by `rfl` (matching `induceHU`'s own `letI`s); cf. the `hunfold` idiom at `reducible_count`.
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hIeq : ClassFunction.inertia (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ) = huSub data := by
    refine eq_of_le_of_prime_index (ClassFunction.subgroup_le_inertia _) ?_ hIM
    rw [huSub_index_eq_q]; exact data.nontrivial.2.1
  exact isIrreducibleCharacter_induce_of_inertia_eq
    (⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ : IrreducibleCharacter ↥(huSub data)) hIeq

/-- **Conjunct (c) of (9.8.c), `hIM`-gated assembly**: given the not-`W₁`-fixed datum (`hIM`), the
(9.8.c) construction `Ind_{HU}^M ζ` witnesses an irreducible `𝒮(H₀C)`-member of degree `qu`.  Bundles
the membership (`hcZeta_induceHU_mem_sOf`), irreducibility (`hcZeta_induceHU_irreducible`), and degree
(`hcZeta_induceHU_apply_one`).  Discharging `hIM` (the free-`W₁`-orbit propagation `θ̄^{w₀}≠θ̄ ⟹
ζ^{w₀}≠ζ`) closes conjunct (c) of `caseA_character_counts`. -/
theorem hcZeta_exists_irreducible_sOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief)
    (hIM : ClassFunction.inertia (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ) ≠ ⊤) :
    ∃ χ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      IsIrreducibleCharacter χ ∧ χ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) :=
  ⟨induceHU data (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ),
    hcZeta_induceHU_mem_sOf chars θ hθnt hθ₀,
    hcZeta_induceHU_irreducible chars θ hθ₀ hIM,
    hcZeta_induceHU_apply_one chars θ⟩

/-- **`H ◁ M`** realized: `(data.H.subgroupOf M).Normal`.  Extracted as in `hInHu_normal`. -/
theorem hSubgroupOfM_normal {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (data.H.subgroupOf M).Normal := by
  rw [show data.H = maxNilpotentNormalHall M from data.typeP.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M

/-- **The `m`-conjugation automorphism of `hInHu`** (`m ∈ M`).  Well-defined since `H ◁ M`
(`hSubgroupOfM_normal`), so `m` normalizes `hInHu`.  Realizing the `M`-conjugation of an
`hInHu`-character as `compHom` by this hom keeps the (9.8.c) free-`W₁`-orbit argument at the `hInHu`
level (no subgroup-realization transport). -/
noncomputable def hInHuConj {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M) :
    ↥(hInHu data) →* ↥(hInHu data) where
  toFun h := ⟨ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) m (h : ↥(huSub data)), by
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [ClassFunction.conjByMulEquiv_apply]
    exact (hSubgroupOfM_normal data).conj_mem _ (Subgroup.mem_subgroupOf.mp h.2) m⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    simp [map_mul]

@[simp] theorem hInHuConj_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M)
    (h : ↥(hInHu data)) :
    (((hInHuConj data m h : ↥(hInHu data)) : ↥(huSub data)) : ↥M)
      = m * ((h : ↥(huSub data)) : ↥M) * m⁻¹ :=
  rfl

/-- **Core identity for L1**: restricting the `M`-conjugate `conjBy m ζ` of an `HU`-character `ζ`
to `H = hInHu` equals `compHom`-by-`φ_m` of `Res ζ`.  Both evaluate at `h ∈ hInHu` to
`ζ(m·h·m⁻¹)`.  This converts the `M`-conjugation (needed for `I_M(ζ)`) into a `compHom`-by-aut
at the `hInHu` level, the hinge of the (9.8.c) free-`W₁`-orbit argument. -/
theorem hInHuConj_restrict_conjBy {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M)
    (ζ : ClassFunction ↥(huSub data) ℂ) :
    ClassFunction.restrict (hInHu data) (ClassFunction.conjBy m ζ)
      = ClassFunction.compHom (hInHuConj data m) (ClassFunction.restrict (hInHu data) ζ) := by
  ext h
  rfl

/-- **Inner sum is invariant under `compHom` by a bijective endomorphism** (reindexing the sum by
the induced permutation).  Mirrors `innerSum_conjBy_conjBy`. -/
theorem innerSum_compHom_of_bijective {H : Type*} [Group H] [Fintype H]
    (e : H →* H) (he : Function.Bijective e) (a b : ClassFunction H ℂ) :
    ClassFunction.innerSum (ClassFunction.compHom e a) (ClassFunction.compHom e b)
      = ClassFunction.innerSum a b := by
  simpa [ClassFunction.innerSum, ClassFunction.compHom_apply] using
    Fintype.sum_equiv (Equiv.ofBijective e he)
      (fun h => a (e h) * star (b (e h))) (fun h => a h * star (b h)) (fun _ => rfl)

/-- **Inner product is invariant under `compHom` by a bijective endomorphism.** -/
theorem inner_compHom_of_bijective {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (e : H →* H) (he : Function.Bijective e)
    (a b : ClassFunction H ℂ) :
    ClassFunction.inner (ClassFunction.compHom e a) (ClassFunction.compHom e b)
      = ClassFunction.inner a b := by
  simp [ClassFunction.inner, innerSum_compHom_of_bijective e he]

/-- **`φ_m` is bijective** (inverse `φ_{m⁻¹}`), so `compHom φ_m` preserves inner products and
irreducibility. -/
theorem hInHuConj_bijective {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M) :
    Function.Bijective (hInHuConj data m) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨hInHuConj data m⁻¹, ?_, ?_⟩ <;>
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    simp only [hInHuConj_coe]
    group

/-- **L2 result: `LiesOver`-equivariance under an `M`-fixing `m`.**  If `ζ` is fixed by `conjBy m`
and lies over `θ₀`, then `ζ` also lies over the `φ_m`-conjugate `φθ₀ = compHom φ_m θ₀`.  Proof: the
restriction multiplicity `⟨Res ζ, φθ₀⟩ = ⟨Res ζ, compHom φ_m θ₀⟩ = ⟨compHom φ_m (Res ζ), compHom φ_m
θ₀⟩` (by `Res ζ = compHom φ_m (Res ζ)`, from `conjBy m ζ = ζ` and the L1 identity) `= ⟨Res ζ, θ₀⟩ ≠ 0`
(`inner_compHom_of_bijective`). -/
theorem hcZeta_liesOver_compHom_of_fixed {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ φθ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ))
    (hφθ₀ : (φθ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ)) :
    OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ φθ₀ := by
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def, hφθ₀,
    show ClassFunction.restrict (hInHu data) (ζ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.compHom (hInHuConj data m)
            (ClassFunction.restrict (hInHu data) (ζ : ClassFunction ↥(huSub data) ℂ)) from by
        rw [← hInHuConj_restrict_conjBy, hfix],
    inner_compHom_of_bijective _ (hInHuConj_bijective data m)]
  have h := hlo
  rwa [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at h

/-- **L3: SingleOrbit reduction.**  If `ζ` is fixed by `conjBy m` and lies over `θ₀`, then `θ₀` and
its `φ_m`-conjugate are `HU`-conjugate: there is `g ∈ HU` with `conjBy g θ₀ = compHom φ_m θ₀`.  By
the L2 equivariance `ζ` lies over both `θ₀` and `φ_m·θ₀`, and Clifford's single-orbit theorem
(`restrictionConstituentsSingleOrbit_of_isIrreducible`) puts both constituents in one `HU`-orbit
(`exists_conj`).  The free-`W₁`-orbit hypothesis (L4) will deny exactly this. -/
theorem hcZeta_exists_conj_of_fixed {M : Subgroup G} {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ g : ↥(huSub data), ClassFunction.conjBy g (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ) := by
  have hirr : IsIrreducibleCharacter
      (ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ)) :=
    θ₀.isIrreducible.compHom_of_surjective (hInHuConj_bijective data m).surjective
  set φθ₀ : IrreducibleCharacter ↥(hInHu data) :=
    ⟨ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ), hirr⟩
    with hφdef
  have hη := hcZeta_liesOver_compHom_of_fixed m ζ θ₀ φθ₀ hlo hfix rfl
  obtain ⟨g, hg⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.RestrictionConstituentsSingleOrbit.exists_conj
      (OddOrder.RepresentationTheory.restrictionConstituentsSingleOrbit_of_isIrreducible ζ) hlo hη
  refine ⟨g, ?_⟩
  have hc := congrArg (fun x : IrreducibleCharacter ↥(hInHu data) =>
    (x : ClassFunction ↥(hInHu data) ℂ)) hg
  simpa [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy, hφdef] using hc

/-- **`I_M(ζ) ≠ M` from the free-`W₁`-orbit** (the reduction side of `hIM`, complete).  If there is
*no* `g ∈ HU` with `conjBy g θ₀ = compHom φ_m θ₀` (the free-orbit hypothesis L4), then `m ∉ I_M(ζ)`,
so `I_M(ζ) ≠ ⊤ = M`.  Indeed `m ∈ I_M(ζ)` would give `conjBy m ζ = ζ`, and L3
(`hcZeta_exists_conj_of_fixed`) would then produce exactly the forbidden `g`.  Combined with
`HU ≤ I_M(ζ) ≤ M` and `[M:HU]=q` prime, this is `hIM` for `hcZeta_induceHU_irreducible`. -/
theorem hcZeta_inertia_ne_top_of_free {M : Subgroup G} {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfree : ¬ ∃ g : ↥(huSub data), ClassFunction.conjBy g (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ)) :
    ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) ≠ ⊤ := by
  intro htop
  have hmem : m ∈ ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) :=
    htop ▸ Subgroup.mem_top m
  rw [ClassFunction.mem_inertia] at hmem
  exact hfree (hcZeta_exists_conj_of_fixed m ζ θ₀ hlo hmem)

/-- **`φ_m`-analog of the inflation-conjugation commute.**  For `m ∈ M` realized by `b ∈ U W₁`
(`↑m = ↑b`), `compHom φ_m` of an inflation equals the inflation of `typeP_conjAction b`.  Mirrors
`conjBy_compHom_hInHuEquivH` (both reduce to `m·h·m⁻¹ = b·h·b⁻¹` in `G`), turning the `M`-conjugation
`compHom φ_m θ₀` of the chief-factor `θ₀` into the abstract `b`-action on `H`. -/
theorem compHom_hInHuConj_hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (b : ↥(data.typeP.U ⊔ data.typeP.W1)) (m : ↥M) (hmb : ((m : G)) = (b : G))
    (θ : ClassFunction ↥data.H ℂ) :
    ClassFunction.compHom (hInHuConj data m)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom θ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (typeP_conjAction data.typeP b).toMonoidHom θ) := by
  ext h
  rw [ClassFunction.compHom_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.compHom_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [MulEquiv.coe_toMonoidHom, hInHuEquivH_coe, typeP_conjAction_apply, hInHuConj_coe,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hmb]

/-- **L4 connection core**: the free-orbit equality `conjBy g θ₀ = compHom φ_m θ₀` (for `θ₀` the
inflation of `θ̄`, `↑g = ↑a`, `↑m = ↑b`) is equivalent to the quotient-level equality
`quotientMulAutHom a θ̄ = quotientMulAutHom b θ̄`.  Chains the two inflation-conjugation commutes
(`conjBy_compHom_hInHuEquivH`, `compHom_hInHuConj_hInHuEquivH`), the descent
(`compHom_typeP_conjAction_inflation`, `rfl`), and double inflation injectivity
(`compHom_injective_of_surjective` for `hInHuEquivH` and `mk' N`).  This turns `hfree` into the pure
free-`W₁`-orbit statement `θ̄^{w₀} ∉ U-orbit`. -/
theorem conjBy_eq_compHom_iff_quotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (a b : ↥(data.typeP.U ⊔ data.typeP.W1))
    (g : ↥(huSub data)) (m : ↥M) (hag : ((g : ↥M) : G) = (a : G)) (hbm : ((m : G)) = (b : G))
    (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) :
    ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar))
      = ClassFunction.compHom (hInHuConj data m)
          (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar))
    ↔ ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant a).toMonoidHom θbar
      = ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant b).toMonoidHom θbar := by
  rw [conjBy_compHom_hInHuEquivH data a g hag, compHom_hInHuConj_hInHuEquivH data b m hbm,
    compHom_typeP_conjAction_inflation, compHom_typeP_conjAction_inflation]
  constructor
  · intro h
    exact ClassFunction.compHom_injective_of_surjective (QuotientGroup.mk'_surjective chief.N)
      (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective h)
  · intro h
    rw [h]

/-- **step 2 core: `M`-fixedness gives a `U`-conjugation** (Peterfalvi (9.8.c) surjectivity route).
If `χ` is fixed by `conjBy m` (`m ∈ M`) and lies over `θ₀`, then there is a `U`-part element
`u ∈ uInHu` with `conjBy u θ₀ = compHom φ_m θ₀`.  The single-orbit `g ∈ HU` of L3
(`hcZeta_exists_conj_of_fixed`) decomposes as `g = h·u` (`hInHu_sup_uInHu_eq_top`, `HU = H·U`); the
`H`-part `h` fixes `θ₀` (`h ∈ hInHu ≤ inertia θ₀`, `subgroup_le_inertia`), so
`conjBy g θ₀ = conjBy u (conjBy h θ₀) = conjBy u θ₀` (`conjBy_mul`).  Realizing the `M`-fixed
factor-permutation by a `U`-element (in `U ⊔ W₁`) is what lets `conjBy_eq_compHom_iff_quotient` turn
it into the `H̄`-level `q(u)θbar = q(w)θbar` (`θbar∘q(w)` in the `U`-orbit of `θbar`). -/
theorem exists_uInHu_conjBy_eq_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ u : ↥(huSub data), u ∈ uInHu data ∧
      ClassFunction.conjBy u (θ₀ : ClassFunction ↥(hInHu data) ℂ)
        = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ) := by
  haveI := hInHu_normal data
  obtain ⟨g, hg⟩ := hcZeta_exists_conj_of_fixed m ζ θ₀ hlo hfix
  -- `g = h · u` with `h ∈ hInHu`, `u ∈ uInHu` (`HU = H·U`, `hInHu ◁ HU`).
  have hgtop : g ∈ hInHu data ⊔ uInHu data :=
    hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgtop
  obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
  refine ⟨u, hu, ?_⟩
  -- `conjBy (h·u) θ₀ = conjBy u (conjBy h θ₀) = conjBy u θ₀` since `h` fixes `θ₀`.
  have hhfix : ClassFunction.conjBy (h : ↥(huSub data)) (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = (θ₀ : ClassFunction ↥(hInHu data) ℂ) :=
    ClassFunction.mem_inertia.mp
      (ClassFunction.subgroup_le_inertia (θ₀ : ClassFunction ↥(hInHu data) ℂ) hh)
  rw [ClassFunction.conjBy_mul, hhfix] at hg
  exact hg

/-- **step 2: `M`-fixedness gives an `H̄`-level orbit equality** (Peterfalvi (9.8.c) surjectivity).
If `χ` is fixed by `conjBy m` (`↑m = ↑b`, `b ∈ U ⊔ W₁`) and lies over the inflation `θ₀` of the seed
`θbar : H̄ →* ℂˣ`, then there is a `U`-element `a` with `θbar ∘ q(a) = θbar ∘ q(b)`
(`q = quotientMulAutHom`).  Chains the `U`-conjugation `exists_uInHu_conjBy_eq_of_fixed`, the L4
bridge `conjBy_eq_compHom_iff_quotient` (turning it into `q(a)θbar = q(b)θbar` at the `H̄`-level), and
`linearIrreducibleCharacter_injective` (stripping the linear wrapper).  Thus the `W₁`-twist
`θbar ∘ q(b)` lies in the `U`-orbit `{θbar ∘ q(a) : a ∈ U}` of `θbar` — the input to the
factor-permutation invariance of the nontrivial-`Hpart` set. -/
theorem exists_uPart_theta_comp_quotient_eq_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (m : ↥M) (b : ↥(data.typeP.U ⊔ data.typeP.W1)) (hbm : ((m : G)) = (b : G))
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ a : ↥(data.typeP.U ⊔ data.typeP.W1), ((a : G)) ∈ data.typeP.U ∧
      θbar.comp (quotientMulAutHom chief.N_aInvariant a).toMonoidHom
        = θbar.comp (quotientMulAutHom chief.N_aInvariant b).toMonoidHom := by
  obtain ⟨u, hu, hconj⟩ := exists_uInHu_conjBy_eq_of_fixed m ζ
    (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom))) hlo hfix
  have huU : ((u : ↥M) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hu)
  refine ⟨⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩, huU, ?_⟩
  -- form alignment: the step-1 `θ₀` equals the `conjBy_eq_compHom_iff_quotient` inflation form.
  have hinfl : (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) := by
    ext x
    simp only [ClassFunction.compHom_apply, linearIrreducibleCharacter_apply,
      MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply]
  -- L4 bridge with `θbar_CF = linearIrr θbar`.
  have hbridge := (conjBy_eq_compHom_iff_quotient
    (⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) b u m rfl hbm
    (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)).mp (by
      rw [← hinfl]; exact hconj)
  rw [ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter] at hbridge
  exact linearIrreducibleCharacter_injective (IrreducibleCharacter.ext hbridge)

/-- **step 2 D₁: `Ū` preserves per-`Hpart` nontriviality** (Peterfalvi (9.8.c) surjectivity).  For a
`U`-part element `a` (`a ∈ U ⊔ W₁` with `↑a ∈ U`), the twist `θbar ∘ q(a)` is trivial on the Clifford
summand `Hpart i` iff `θbar` is (`q = quotientMulAutHom`).  A form-alignment wrapper over
`caseA_uActionHom_comp_subtype_eq_one_iff`: `uActionHom data chief ⟨a, ·⟩ = quotientMulAutHom a`
(`uActionHom` is `quotientMulAutHom ∘ U.subgroupOf.subtype`), so the `Ū`-action on the factors matches
`q(a)`.  Combined with the orbit equality `θbar∘q(a) = θbar∘q(w)` (`exists_uPart_..._of_fixed`), this
makes the nontrivial-`Hpart` set invariant under the `W₁`-twist `q(w)`. -/
theorem caseA_theta_comp_quotient_uPart_comp_subtype_eq_one_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {a : ↥(data.typeP.U ⊔ data.typeP.W1)} (haU : ((a : G)) ∈ data.typeP.U)
    {i : Fin data.q} (θbar : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θbar.comp (quotientMulAutHom chief.N_aInvariant a).toMonoidHom).comp
        (caseA.Hpart i).subtype = 1
      ↔ θbar.comp (caseA.Hpart i).subtype = 1 :=
  caseA_uActionHom_comp_subtype_eq_one_iff caseA
    (⟨a, Subgroup.mem_subgroupOf.mpr haU⟩ :
      ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) θbar

/-- **`Ū`-invariance of nontriviality on a `U`-invariant `K`, `quotientMulAutHom` form**: for a
`U`-invariant `K` and a `U`-part element `a` (`↑a ∈ U`), `θ ∘ q(a)` is trivial on `K` iff `θ` is
(`q = quotientMulAutHom`).  The form-alignment (`uActionHom ⟨a,·⟩ = q(a)`) version of
`comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant` for the general-`K` uses in the (9.8.c)
surjectivity regularity argument (`K = q(w) • S₀` and `K = S₀`). -/
theorem comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {K : Subgroup (↥data.H ⧸ chief.N)} (hK : IsAInvariant (uActionHom data chief) K)
    {a : ↥(data.typeP.U ⊔ data.typeP.W1)} (haU : ((a : G)) ∈ data.typeP.U)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (quotientMulAutHom chief.N_aInvariant a).toMonoidHom).comp K.subtype = 1
      ↔ θ.comp K.subtype = 1 :=
  comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant hK
    (⟨a, Subgroup.mem_subgroupOf.mpr haU⟩ :
      ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) θ

/-- **step 2 D₂: precompose–pointwise-smul bridge**.  A character `θ` is trivial on the translate
`a • S` (`a : MulAut K`) iff its precomposition `θ ∘ a` is trivial on `S` (any element of `a • S` is
`a s` for `s ∈ S`).  Used with `a = q(v)` (`quotientMulAutHom`) and `S = S₀` to turn nontriviality on
the Clifford summand `Hpart i = q(orbitRep i) • S₀` into nontriviality of `θbar ∘ q(orbitRep i)` on
the generator `S₀`, the last bridge of the (9.8.c) surjectivity regularity argument. -/
theorem comp_subtype_pointwise_smul_eq_one_iff {K : Type*} [Group K] (a : MulAut K)
    (θ : K →* ℂˣ) (S : Subgroup K) :
    θ.comp (a • S).subtype = 1 ↔ (θ.comp a.toMonoidHom).comp S.subtype = 1 := by
  rw [MonoidHom.ext_iff, MonoidHom.ext_iff]
  refine ⟨fun h s => ?_, fun h y => ?_⟩
  · have hval := h ⟨a • (s : K), (Subgroup.smul_mem_pointwise_smul_iff).mpr s.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.smul_def] using hval
  · have hval := h ⟨a⁻¹ • (y : K), (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.smul_def, MulAut.apply_inv_self] at hval ⊢
    exact hval

/-- **step 2 E (W₁ case): `θbar ∘ q(w)` and `θbar` agree on `S₀` (triviality)** for `w` a
`W₁`-element, given `χ = ζ` is `M`-fixed.  From `M`-fixedness the orbit equality
`exists_uPart_theta_comp_quotient_eq_of_fixed` gives `a ∈ U` with `θbar ∘ q(a) = θbar ∘ q(w)`; then
`comp_quotient_uPart_..._of_aInvariant` (`S₀` is `U`-invariant, `S0_aInvariant`) collapses the
`U`-twist.  This is the `W₁`-half of the `U ⊔ W₁` orbit-invariance on `S₀`. -/
theorem caseA_theta_comp_quotient_W1_on_S0_eq_one_iff_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    {w : ↥(data.typeP.U ⊔ data.typeP.W1)} (hwW : ((w : G)) ∈ data.typeP.W1) :
    (θbar.comp (quotientMulAutHom chief.N_aInvariant w).toMonoidHom).comp caseA.S0.subtype = 1
      ↔ θbar.comp caseA.S0.subtype = 1 := by
  have hwM : ((w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ M := data.typeP.W1_le hwW
  have hfix : ClassFunction.conjBy (⟨(w : G), hwM⟩ : ↥M) (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.mem_inertia.mp (hMfix ▸ Subgroup.mem_top _)
  obtain ⟨a, haU, hEq⟩ :=
    exists_uPart_theta_comp_quotient_eq_of_fixed (⟨(w : G), hwM⟩ : ↥M) w rfl θbar ζ hlo hfix
  rw [← hEq]
  exact comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant caseA.S0_aInvariant haU θbar

/-- **step 2 E (`U ⊔ W₁` case): `θbar ∘ q(v)` and `θbar` agree on `S₀`** for any `v ∈ U ⊔ W₁`,
given `ζ` is `M`-fixed.  Frobenius-decompose `v = u·w` (`U ◁ U W₁`, `Subgroup.normal_mul`); then
`θbar∘q(u·w)` on `S₀` `= (θbar∘q(u))∘q(w)` on `S₀` `⟺ θbar∘q(u)` on `q(w)•S₀`
(`comp_subtype_pointwise_smul`) `⟺ θbar` on `q(w)•S₀` (`comp_quotient_uPart_..._of_aInvariant`,
`q(w)•S₀` `U`-invariant) `⟺ θbar∘q(w)` on `S₀` (`comp_subtype_pointwise_smul`) `⟺ θbar` on `S₀`
(the `W₁` case).  So `θbar`'s nontriviality on `S₀` is invariant under the whole `U ⊔ W₁`-action —
the key to reducing per-`Hpart` regularity to a single `S₀` condition. -/
theorem caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (v : ↥(data.typeP.U ⊔ data.typeP.W1)) :
    (θbar.comp (quotientMulAutHom chief.N_aInvariant v).toMonoidHom).comp caseA.S0.subtype = 1
      ↔ θbar.comp caseA.S0.subtype = 1 := by
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  have htop : data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hv : v ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := htop ▸ Subgroup.mem_top v
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := hv
  have huU : ((u : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp hu
  have hwW : ((w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
    Subgroup.mem_subgroupOf.mp hw
  have hsplit : (θbar.comp (quotientMulAutHom chief.N_aInvariant (u * w)).toMonoidHom).comp
        caseA.S0.subtype
      = ((θbar.comp (quotientMulAutHom chief.N_aInvariant u).toMonoidHom).comp
          (quotientMulAutHom chief.N_aInvariant w).toMonoidHom).comp caseA.S0.subtype := by
    rw [map_mul]; rfl
  rw [hsplit, ← comp_subtype_pointwise_smul_eq_one_iff,
    comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant
      (isAInvariant_comp_subtype_pointwise_smul hUnorm caseA.S0_aInvariant w) huU θbar,
    comp_subtype_pointwise_smul_eq_one_iff]
  exact caseA_theta_comp_quotient_W1_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix hwW

/-- **step 2 (regularity): a reducible constituent seed is regular** (Peterfalvi (9.8.c)
surjectivity).  If `ζ` is `M`-fixed (`I_M(ζ) = ⊤`, from reducibility of `Ind_M ζ`) and lies over the
inflation of a nonzero seed `θbar : H̄ →* ℂˣ`, then `θbar` is *regular*: nontrivial on every Clifford
summand `Hpart i`.  Two steps, both via the `S₀`-aggregation
`caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed` (`θbar ∘ q(v)` and `θbar` agree on `S₀`):
`θbar` is nontrivial on `S₀` (else it is trivial on every `Hpart i = q(orbitRep i) • S₀`, hence on
`⨆ Hpart = ⊤ = H̄`, forcing `θbar = 1`); and then each `Hpart i` inherits nontriviality from `S₀`.
This is the last input to `ζ = Ind_{HC}(hcPsi θbar) ∈ Xθ` (via `inertia_eq_hcInHu_caseA` and the
Clifford correspondence), closing the `Xmu`-surjectivity of the (9.8.c) parity dichotomy. -/
theorem caseA_reducible_theta_regular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1) :
    ∀ i, θbar.comp (caseA.Hpart i).subtype ≠ 1 := by
  -- `θbar` is nontrivial on `S₀`.
  have hS0 : θbar.comp caseA.S0.subtype ≠ 1 := by
    intro h0
    apply hnt
    -- Every `Hpart i` is in `ker θbar`, and they span `H̄`, so `θbar = 1`.
    have hker : ∀ i, caseA.Hpart i ≤ θbar.ker := by
      intro i x hx
      have htriv : θbar.comp (caseA.Hpart i).subtype = 1 := by
        rw [caseA.Hpart_orbit i, comp_subtype_pointwise_smul_eq_one_iff,
          caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix
            (caseA.orbitRep i)]
        exact h0
      have hval := DFunLike.congr_fun htriv ⟨x, hx⟩
      rw [MonoidHom.mem_ker]
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] using hval
    refine MonoidHom.ext fun x => ?_
    have hxker : x ∈ θbar.ker :=
      (caseA.Hpart_iSup ▸ iSup_le hker : (⊤ : Subgroup (↥data.H ⧸ chief.N)) ≤ θbar.ker)
        (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hxker
    rw [hxker, MonoidHom.one_apply]
  -- Each `Hpart i` inherits nontriviality from `S₀`.
  intro i
  rw [ne_eq, caseA.Hpart_orbit i, comp_subtype_pointwise_smul_eq_one_iff,
    caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix (caseA.orbitRep i)]
  exact hS0

/-- **step 5 foundation: a reducible constituent seed has inflation-inertia `HC`** (Peterfalvi
(9.8.c)).  Chains the regularity `caseA_reducible_theta_regular` (a reducible `M`-fixed `ζ`'s
constituent seed `θbar` is regular) into `inertia_eq_hcInHu_caseA` (a regular seed's inflation `θ₀`
has `HU`-inertia `HC`), converting the hom-form regularity to the `IrreducibleCharacter` pointwise
form via `comp_subtype_ne_one_iff_exists`.  This `I_{HU}(θ₀) = HC` is what makes `Ind_{HC}(hcPsi θbar)`
irreducible (`hcZeta_irreducible`) and drives the Clifford-correspondence identification
`ζ = Ind_{HC}(hcPsi θbar) ∈ Xθ` closing the `Xmu`-surjectivity. -/
theorem caseA_reducible_inflation_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1) :
    ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  refine inertia_eq_hcInHu_caseA data chief caseA (fun i => ?_)
  obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θbar i).mp
    (caseA_reducible_theta_regular caseA θbar ζ hlo hMfix hnt i)
  refine ⟨x, hx, ?_⟩
  rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one]
  simpa using hne

/-- **Restriction transitivity** (general): for `H ≤ K ≤ G`, restricting a class function to `K`
and then to `H` (realised in `K` as `H.subgroupOf K`) equals restricting directly to `H`, transported
along the iso `H.subgroupOf K ≃* H`.  Foundational for the lies-over transitivity in the (9.8.c)
Clifford-correspondence step 5 (`ξ` over `θ₀` at `H = hInHu ⊆ HC` factors through an `HC`-constituent).
Pointwise both sides are `φ` at the common `G`-image. -/
theorem restrict_restrict_subgroupOf {Γ k : Type*} [Group Γ] [CommRing k]
    {H K : Subgroup Γ} (hHK : H ≤ K) (φ : ClassFunction Γ k) :
    ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K φ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
          (ClassFunction.restrict H φ) := by
  ext x
  simp only [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  congr 1

/-- **`innerSum` is preserved under `compHom` by a group isomorphism** (reindex the sum by the iso).
Generalises `innerSum_compHom_of_bijective` (an endomorphism) to a `MulEquiv A ≃* B`. -/
theorem innerSum_compHom_mulEquiv {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (e : A ≃* B) (a b : ClassFunction B ℂ) :
    ClassFunction.innerSum (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.innerSum a b := by
  simpa only [ClassFunction.innerSum, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom] using
    Fintype.sum_equiv e.toEquiv
      (fun x => a (e x) * star (b (e x))) (fun y => a y * star (b y)) (fun _ => rfl)

end OddOrder.Peterfalvi.S11
