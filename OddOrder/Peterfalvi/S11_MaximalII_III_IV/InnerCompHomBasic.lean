import OddOrder.Peterfalvi.S11_MaximalII_III_IV.CaseBXi

/-!
# Peterfalvi §11 — the inner-complement homomorphism: opening layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
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
-- raised heartbeat budget for the heavy elaboration below
set_option backward.isDefEq.respectTransparency false in
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
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
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
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  obtain ⟨hχX, hχK⟩ := hχ
  obtain ⟨ψ, hψover⟩ := OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) χ
  have hN := realizedH0supCprime_normal_huSub chief
  have hNC := realizedH0supC_normal_huSub chief
  have hNsub : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
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
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbar⟩ :=
    ψbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hψeq : (ψ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = (hcPsi chief θbar : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    rw [← hψbar, ← hθbar]
    ext x
    simp [hcPsi, ClassFunction.compHom_apply,
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
      simp [hcPsi, trivialClassFunction]
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
-- raised heartbeat budget for the heavy elaboration below
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
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
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
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  have hNC := realizedH0supC_normal_huSub chief
  have : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
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
    have : IsMulCommutative (↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) ⧸ commutator ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data))) :=
      inferInstanceAs (IsMulCommutative (Abelianization _))
    refine apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
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
  set φ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →*
      ℂˣ :=
    ψhom * (hcLambdaHom chief lam)⁻¹ with hφdef
  have hφkerH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤
        φ.ker := by
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
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ≤
        φ.ker := by
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
          ↥(hInHu data ⊔
            ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
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
        rw [map_one]; exact hx1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff x).mp h2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply_one,
      MonoidHom.mem_ker.mp (hφkerH0C hxH0C), Units.val_one]
  obtain ⟨θbarChar, hθbarChar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) (linearIrreducibleCharacter φ) hkerφ
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
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
-- raised heartbeat budget for the heavy elaboration below
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
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
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
    simp [hcPsi]
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
          congr!
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
-- raised heartbeat budget for the heavy elaboration below
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
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
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
    simp [hcPsiPair]
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
          congr!
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
-- raised heartbeat budget for the heavy elaboration below
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
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
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
    simp [hcPsi]
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
    change induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr!
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsi chief θbar : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages



end OddOrder.Peterfalvi.S11
