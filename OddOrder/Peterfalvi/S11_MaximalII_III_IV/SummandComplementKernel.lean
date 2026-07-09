import OddOrder.Peterfalvi.S11_MaximalII_III_IV.Coherence911

/-!
# Peterfalvi (9.8.d) (γ) core — summand-complement kernel W ⊆ Ker ζ

Split from the former monolithic `OddOrder.Peterfalvi.S11_MaximalII_III_IV` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S11
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}


/-! ### Peterfalvi (9.8.d) (γ) core (1): the summand-complement kernel `W = H₂…H_q ⊆ Ker ζ`

The (9.8.d) `W₁`-injectivity (Coq `injXtheta`) needs, for each family member `ζ = Ind_{H·C_U(S₀)}^{HU}
ψ_{θ₁,λ}` (`θ₁ ∈ Irr(H̄/W)`, trivial on the summand-join complement `W = H₂…H_q`), that the *realized*
`W` lies in `Ker ζ`.  This is the direct mirror of `hcuZetaPair_H0supUprime_subset_ker`: `W`
realizes into `HU` as a normal subgroup on which `ψ_{θ₁,λ}` is trivial (the `θ`-factor is `θ|_W = 1`
via the seed, the `λ`-factor is trivial on `H ⊇ W`), so the induce-kernel step
(`subsetCharacterKernel_induce_of_subgroupOf`) puts it in `Ker ζ`. -/

/-- **Realized summand-complement `W` in `G`** (Peterfalvi (9.8.d)).  A subgroup `W ≤ H̄ = H/N`
(here the summand-join complement `H₂…H_q`) realizes as the preimage-in-`H`-viewed-in-`G`
`(W.comap (mk' N)).map H.subtype`.  It contains `H₀ = N.map H.subtype` (as `⊥ ≤ W` after `mk'`) and
lies in `H`; its `HU`-realization is the kernel carrier of the (9.8.d) `θ₁`-factor. -/
noncomputable def caseA_realizedComplement {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) : Subgroup G :=
  (W.comap (QuotientGroup.mk' chief.N)).map data.H.subtype

/-- The realized complement lies in `H`. -/
theorem caseA_realizedComplement_le_H {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    caseA_realizedComplement chief W ≤ data.H := by
  rintro _ ⟨x, _, rfl⟩; exact x.2

/-- `H₀ ≤ realized W` (`N ≤ preimage of W`, as `mk' N` kills `N`). -/
theorem H0_le_caseA_realizedComplement {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    chief.H0 ≤ caseA_realizedComplement chief W := by
  rw [chief.H0_eq, caseA_realizedComplement]
  refine Subgroup.map_mono (fun x hx => ?_)
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hx]
  exact W.one_mem

/-- The realized complement is `≤ M` (via `H ≤ M`). -/
theorem caseA_realizedComplement_le_M {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    caseA_realizedComplement chief W ≤ M :=
  (caseA_realizedComplement_le_H chief W).trans (H_le_M data)

/-- The `HU`-realized complement lies in `hInHu` (as `realized W ≤ H`). -/
theorem caseA_realizedComplement_subgroupOf_le_hInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (caseA_realizedComplement_le_H chief W))

/-- **The realization iso sends realized `W` (in `hInHu`) onto `W`** under `mk'(N) ∘ hInHuEquivH`.
Mirror of `realizedH0_subgroupOf_hInHu_eq_comap`: an element `x ∈ hInHu` lies in the realized `W`
iff `mk'(N)(hInHuEquivH x) ∈ W`. -/
theorem caseA_realizedComplement_subgroupOf_hInHu_eq_comap {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data)
      = W.comap ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    caseA_realizedComplement, Subgroup.mem_map, ← hInHuEquivH_coe]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    have hz_eq : z = hInHuEquivH data x := Subgroup.subtype_injective data.H hzeq
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hz
    rwa [hz_eq] at hz
  · intro h
    exact ⟨hInHuEquivH data x, by rwa [Subgroup.mem_comap, QuotientGroup.mk'_apply], rfl⟩

/-- **The seed hom `θ₀ = θ ∘ mk'(N) ∘ hInHuEquivH` kills the realized complement `W`** when `θ` is
trivial on `W ≤ H̄`.  For `h ∈ hInHu` in the realized `W`, `hInHuEquivH h` maps under `mk'(N)` into
`W`, on which `θ` is `1`.  Mirror of `hcuSeedHom_eq_one_of_mem_realizedH0` (which is the `W = ⊥`,
`θ`-agnostic case). -/
theorem hcuSeedHom_eq_one_of_mem_realizedComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1)
    {h : ↥(hInHu data)}
    (hh : h ∈ (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data)) :
    hcuSeedHom (chief := chief) θ h = 1 := by
  have hW : (QuotientGroup.mk' chief.N) (hInHuEquivH data h) ∈ W := by
    have := (caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief W) ▸ hh
    rwa [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [hcuSeedHom, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact hθW _ hW

/-- **`hcuPairHom` kills the realized complement `W`** (`HC`-level, pointwise), given `θ|_W = 1`.
Every `x` in the realized `W ⊆ H` has `θ`-part `hcuThetaHom x = hcuSeedHom θ x = 1`
(`hcuThetaHom_inclusion_hInHu`, `hcuSeedHom_eq_one_of_mem_realizedComplement`) and `λ`-part
`hcuLambdaHom x = 1` (`hcuLambdaHom_eq_one_of_mem_hInHu`, since `W ⊆ H`). -/
theorem hcuPairHom_eq_one_of_mem_realizedComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1)
    {x : ↥(hInHu data ⊔ cuInHu caseA)}
    (hx : x ∈ ((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf (hInHu data)).map
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA))) :
    hcuPairHom caseA θ hinv lam x = 1 := by
  haveI := hInHu_normal data
  obtain ⟨h, hhmem, hxeq⟩ := hx
  -- `x` is the inclusion of `h ∈ realized W ⊆ hInHu`.
  have hhH : (h : ↥(huSub data)) ∈ hInHu data := h.2
  have hxIncl : x = Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h :=
    hxeq.symm
  -- `θ`-part.
  have hθfac : hcuThetaHom caseA θ hinv x = 1 := by
    rw [hxIncl, hcuThetaHom_inclusion_hInHu caseA θ hinv h,
      hcuSeedHom_eq_one_of_mem_realizedComplement chief θ hθW hhmem]
  -- `λ`-part (`W ⊆ H`).
  have hlamfac : hcuLambdaHom caseA lam x = 1 := by
    apply hcuLambdaHom_eq_one_of_mem_hInHu caseA lam
    rw [hxIncl, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact h.2
  simp only [hcuPairHom, MonoidHom.mul_apply, hθfac, hlamfac, mul_one]

/-- **`W ⊆ Ker ψ_{θ₁,λ}` as a `Set` inclusion** (`HC`-level): the realized summand-complement `W` is
in the character kernel of the pair character, given `θ|_W = 1`.  Pointwise from
`hcuPairHom_eq_one_of_mem_realizedComplement`.  Mirror of
`hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel`. -/
theorem hcuPsiPair_realizedComplement_subset_characterKernel [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1) :
    (((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data)).map
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) :
        Set ↥(hInHu data ⊔ cuInHu caseA)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcuPsiPair caseA θ hinv lam) := by
  intro x hx
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcuPsiPair]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one,
    hcuPairHom_eq_one_of_mem_realizedComplement caseA θ hinv lam hθW (SetLike.mem_coe.mp hx),
    Units.val_one]

/-- **`HU` normalizes the realized summand-complement `W`** (Peterfalvi (9.8.d)).  For a
`U`-invariant `W ≤ H̄` (`IsAInvariant (uActionHom) W`), the realized `W`
(`caseA_realizedComplement`) is normalized by `H ⊔ U`: `H` normalizes it because `H̄ = H/N` is
abelian so `W ◁ H̄` and `N ≤ WH ≤ H` gives `WH ◁ H`; `U` normalizes it because `u·wh·u⁻¹` has
`H̄`-image `uActionHom(u) • (mk' wh) ∈ W` (U-invariance).  This supplies the `[A.Normal]` of the
induce-kernel step for `W ⊆ Ker ζ`. -/
theorem caseA_realizedComplement_uW_le_normalizer [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W) :
    data.H ⊔ data.U
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  -- `WH := W.comap (mk' N) ⊴ H` (preimage of a subgroup of the abelian `H̄`).
  set WH : Subgroup ↥data.H := W.comap (QuotientGroup.mk' chief.N) with hWH
  haveI hWHn : WH.Normal := by
    rw [hWH]; exact (Subgroup.normal_of_comm W).comap _
  -- `H` normalizes `caseA_realizedComplement = WH.map subtype`.
  have hH_norm : data.H
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := WH) data.H.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hWHn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  -- `U` normalizes it: conjugation by `u ∈ U` lands `WH` in `WH` (`U`-invariance of `W`).
  have hconj : ∀ (u : ↥data.U) {m : ↥data.H}, m ∈ WH →
      (u : G) * data.H.subtype m * (u : G)⁻¹ ∈ caseA_realizedComplement chief W := by
    intro u m hm
    have huU : (u : G) ∈ data.typeP.U := u.2
    have huUW1 : (u : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left huU
    -- `typeP_conjAction (u) m ∈ WH`, i.e. `mk'(u·m·u⁻¹) ∈ W`.
    have huinv : (uActionHom data chief
        ⟨⟨(u : G), huUW1⟩, Subgroup.mem_subgroupOf.mpr huU⟩)
          (QuotientGroup.mk' chief.N m) ∈ W :=
      hWinv.smul_mem
        (⟨⟨(u : G), huUW1⟩, Subgroup.mem_subgroupOf.mpr huU⟩ :
          ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
        (Subgroup.mem_comap.mp hm)
    rw [uActionHom, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'] at huinv
    refine ⟨typeP_conjAction data.typeP ⟨(u : G), huUW1⟩ m,
      Subgroup.mem_comap.mpr ?_, typeP_conjAction_apply data.typeP _ m⟩
    simpa only [Subgroup.subtype_apply, QuotientGroup.mk'_apply] using huinv
  have hU_norm : data.U
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun ⟨m, hm, hval⟩ => hval ▸ hconj ⟨g, hg⟩ hm, fun hh => ?_⟩
    obtain ⟨m, hm, hval⟩ := hh
    have key := hconj (⟨g, hg⟩ : ↥data.U)⁻¹ hm
    have hE : ((⟨g, hg⟩ : ↥data.U)⁻¹ : G) * data.H.subtype m
        * (((⟨g, hg⟩ : ↥data.U)⁻¹ : G))⁻¹ = h := by
      rw [hval]; show g⁻¹ * (g * h * g⁻¹) * (g⁻¹ : G)⁻¹ = h; group
    exact hE ▸ key
  exact sup_le hH_norm hU_norm

/-- **realized summand-complement `W ◁ M`** (Peterfalvi (9.8.d)): the realized `W` is normalized by
`M = H ⊔ (U ⊔ W₁)`; combined with `caseA_realizedComplement_le_M` this is `W ◁ M`, whose
`huSub`-restriction is the `[A.Normal]` input of the induce-kernel step.  (`W₁` need not normalize
`W`; but `H ⊔ U = HU` does, which is all the induce-kernel step over `HU` requires.) -/
theorem caseA_realizedComplement_subgroupOf_huSub_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W) :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.subgroupOf_mono M
      ((caseA_realizedComplement_le_H chief W).trans (le_sup_left : data.H ≤ data.H ⊔ data.U)) :
        ((caseA_realizedComplement chief W).subgroupOf M) ≤ huSub data)).mpr ?_
  -- `huSub = (H⊔U).comap subtype ≤ (normalizer WG).comap subtype ≤ normalizer(WG.subgroupOf M)`.
  have hle : huSub data ≤ (Subgroup.normalizer
      ((caseA_realizedComplement chief W : Subgroup G) : Set G)).comap M.subtype := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxs : (x : ↥M) ∈ (data.H ⊔ data.U).subgroupOf M := hx
    rw [Subgroup.mem_subgroupOf] at hxs
    exact caseA_realizedComplement_uW_le_normalizer hWinv hxs
  refine hle.trans ?_
  have := Subgroup.le_normalizer_comap (H := (caseA_realizedComplement chief W)) M.subtype
  rwa [show (caseA_realizedComplement chief W).comap M.subtype
    = (caseA_realizedComplement chief W).subgroupOf M from rfl] at this

/-- **Peterfalvi (9.7.a) realized orbit-move (`horbit`).**  For a nontrivial `w₁ ∈ W₁`, conjugation
by `w₁` inside `HU` moves the realized generator summand `S₀` into the realized summand-complement
`W = ⨆_{w∈W₁#} S₀^w` (`caseA_realizedComplement chief (caseA_wComplement caseA)`).

The `H̄`-descent of the concrete conjugation: for `s` in the realized `S₀`, take `x_s : ↥H` with
`mk'(N) x_s ∈ S₀` and `↑x_s = ↑s`; then `w₁·s·w₁⁻¹` realizes `x = (w₁·(·)·w₁⁻¹) x_s = typeP_conjAction
⟨w₁⟩ x_s`, whose `mk'(N)`-image is `φ(⟨w₁⟩)•(mk'(N) x_s) ∈ φ(⟨w₁⟩)•S₀ = S₀^{w₁}`
(`quotientMulAutHom_apply_mk'`).  Since `w₁ ≠ 1`, `S₀^{w₁} = caseA_wOrbit caseA ⟨w₁⟩ ≤ caseA_wComplement
caseA = W` (`caseA_wComplement` is the join over the nontrivial conjugates).  This is precisely the
`H₁^w ⊆ H₂…H_q` step (`w ∈ W₁#`) of the Coq `injXtheta` (`PFsection9.v` L1233-1253), discharging the
`horbit` hypothesis of `hcrit_of_summand_orbit`. -/
theorem caseA_wOrbit_horbit [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∀ w₁ : ↥M, ((w₁ : ↥M) : G) ∈ data.typeP.W1 → w₁ ≠ 1 →
      ∀ s ∈ ((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data),
        ClassFunction.conjByMulEquiv (H := huSub data) (w₁ : ↥M) s
          ∈ ((caseA_realizedComplement chief (caseA_wComplement caseA)).subgroupOf M).subgroupOf
            (huSub data) := by
  haveI : chief.N.Normal := chief.N_normal
  intro w₁ hw₁W1 hw₁ne s hs
  -- unpack `s ∈ realized S₀`: get `x_s : ↥H` with `mk'(N) x_s ∈ S₀`, `↑x_s = ↑↑s`.
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hs
  simp only [caseA_realizedComplement, Subgroup.mem_map] at hs
  obtain ⟨x_s, hx_sS0, hx_sval⟩ := hs
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hx_sS0
  -- `w₁` as an element of `U ⊔ W₁`.
  have hw₁UW1 : ((w₁ : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hw₁W1
  set a : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨((w₁ : ↥M) : G), hw₁UW1⟩ with ha
  -- the moved `H`-element.
  set x : ↥data.H := typeP_conjAction data.typeP a x_s with hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [caseA_realizedComplement, Subgroup.mem_map]
  refine ⟨x, ?_, ?_⟩
  · -- `mk'(N) x ∈ W`.
    rw [Subgroup.mem_comap]
    have hmkx : (QuotientGroup.mk' chief.N) x
        = (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s) := by
      rw [hx, OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
    rw [hmkx]
    -- `S₀^{w₁} = caseA_wOrbit caseA ⟨w₁⟩ ≤ caseA_wComplement caseA` (`w₁ ≠ 1`).
    have haW1sub : a ∈ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
      rw [Subgroup.mem_subgroupOf]; exact hw₁W1
    set awsub : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := ⟨a, haW1sub⟩
      with hawsub
    have hawne : awsub ≠ 1 := by
      intro h
      apply hw₁ne
      have ha1 : (awsub : ↥(data.typeP.U ⊔ data.typeP.W1)) = 1 := by rw [h]; rfl
      exact Subtype.ext (congrArg (fun z : ↥(data.typeP.U ⊔ data.typeP.W1) => (z : G)) ha1)
    have hmem_orbit : (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s)
        ∈ caseA_wOrbit caseA awsub := by
      rw [caseA_wOrbit]
      show (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s)
        ∈ quotientMulAutHom chief.N_aInvariant ↑awsub • caseA.S0
      rw [hawsub]
      exact Subgroup.smul_mem_pointwise_smul _ _ caseA.S0 hx_sS0
    exact (le_iSup₂ (f := fun w (_ : w ≠ 1) => caseA_wOrbit caseA w) awsub hawne) hmem_orbit
  · -- `↑x = ↑↑(conjByMulEquiv w₁ s)` in `G`.
    rw [Subgroup.coe_subtype, hx, typeP_conjAction_apply, ClassFunction.conjByMulEquiv_apply]
    show (a : G) * (x_s : G) * (a : G)⁻¹
      = ((w₁ : ↥M) : G) * ((s : ↥M) : G) * ((w₁ : ↥M) : G)⁻¹
    have hxs : (x_s : G) = ((s : ↥M) : G) := by rw [← hx_sval]; rfl
    rw [hxs]

/-- **`realized W ⊆ Ker ζ_{θ₁,λ}`** (Peterfalvi (9.8.d) (γ) core (1)): the realized summand-complement
`W = H₂…H_q` lies in the character kernel of `ζ_{θ₁,λ} = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})`, given
`θ|_W = 1` and `W` `U`-invariant.  Since the pair `ψ_{θ₁,λ}` is `1` on the realized `W`
(`hcuPsiPair_realizedComplement_subset_characterKernel`) and `W ◁ HU`
(`caseA_realizedComplement_subgroupOf_huSub_normal`), the normal subgroup lands in the induced
kernel (`subsetCharacterKernel_induce_of_subgroupOf`).  Direct mirror of
`hcuZetaPair_H0supUprime_subset_ker`.  This is the `H₂…H_q ⊆ Ker χ` of the (9.8.d) `injXtheta`
argument. -/
theorem hcuZetaPair_summandComplement_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hθW : ∀ w ∈ W, θ w = 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam)) := by
  haveI := caseA_realizedComplement_subgroupOf_huSub_normal hWinv
  refine OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ cuInHu caseA)
    (le_trans (caseA_realizedComplement_subgroupOf_le_hInHu chief W) le_sup_left)
    (hcuPsiPair caseA θ hinv lam) ?_
  -- Bridge: `A.subgroupOf (hInHu⊔cuInHu) = (A.subgroupOf hInHu).map (inclusion)`, then reuse vanishing.
  have hAle : ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data := caseA_realizedComplement_subgroupOf_le_hInHu chief W
  have hbridge : (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ cuInHu caseA)
      = ((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data)).map
          (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨⟨(y : ↥(huSub data)), hAle hy⟩, Subgroup.mem_subgroupOf.mpr hy,
        Subtype.ext (by rw [Subgroup.coe_inclusion])⟩
    · rintro ⟨z, hz, hzeq⟩
      rw [Subgroup.mem_subgroupOf] at hz
      have : ((y : ↥(hInHu data ⊔ cuInHu caseA)) : ↥(huSub data)) = (z : ↥(huSub data)) := by
        rw [← hzeq, Subgroup.coe_inclusion]
      rw [this]; exact hz
  rw [hbridge]
  exact hcuPsiPair_realizedComplement_subset_characterKernel caseA θ hinv lam hθW

/-- **`hInHu = realized S₀ ⊔ realized W`** when `S₀ ⊔ W = ⊤` in `H̄` (Peterfalvi (9.8.d) (γ) span).
The realizations `realized K = K.comap (mk'(N) ∘ hInHuEquivH)` (`≤ hInHu`) satisfy
`comap f (S₀ ⊔ W) = comap f S₀ ⊔ comap f W` (`comap_sup_eq`, `f` surjective), so `S₀ ⊔ W = ⊤`
gives `⊤ = realized S₀ ⊔ realized W` inside `hInHu`.  Equivalently `hInHu ≤ (realized S₀) ⊔
(realized W)` as subgroups of `huSub`.  This is what makes `H̄ ⊆ Ker ζ₁` follow from `realized S₀ ⊆
Ker ζ₁` (core (2)) plus `realized W ⊆ Ker ζ₁` (core (1)) in the `injXtheta` contradiction. -/
theorem caseA_hInHu_le_realizedS0_sup_realizedComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {S₀ W : Subgroup (↥data.H ⧸ chief.N)} (hsup : S₀ ⊔ W = ⊤) :
    (hInHu data : Subgroup ↥(huSub data)) ≤
      ((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data)
        ⊔ ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data) := by
  -- Work in `hInHu`: the two realizations `subgroupOf hInHu` are the comaps, joining to `⊤`.
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  have htop : (⊤ : Subgroup ↥(hInHu data))
      = (((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data)
        ⊔ (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data) := by
    rw [caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief S₀,
      caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief W,
      Subgroup.comap_sup_eq (f := (QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom)
        S₀ W hfsurj, hsup, Subgroup.comap_top]
  -- Transfer `⊤ = A' ⊔ B'` (in `hInHu`) to `hInHu ≤ A ⊔ B` (in `huSub`).
  -- the realized `S₀` in `hInHu` is normal (`S₀ ◁ H̄` abelian, comap of normal is normal).
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  haveI hS0n : ((((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf (hInHu data)).Normal := by
    rw [caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief S₀]
    exact (Subgroup.normal_of_comm S₀).comap _
  intro x hx
  have hxs : (⟨x, hx⟩ : ↥(hInHu data))
      ∈ (((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data)
        ⊔ (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data) := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hxs
  obtain ⟨a, ha, b, hb, hab⟩ := hxs
  have hxeq : x = (a : ↥(huSub data)) * (b : ↥(huSub data)) := by
    have hc := congrArg (Subtype.val : ↥(hInHu data) → ↥(huSub data)) hab
    rw [Subgroup.coe_mul] at hc
    exact hc.symm
  rw [hxeq]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)

set_option maxHeartbeats 1000000 in
/-- **`H ⊄ Ker ζ_{θ₁,λ}`** (`ζ_{θ₁,λ} ∈ 𝒳`): the irreducible `ζ_{θ₁,λ}` is nontrivial on
`H = hInHu`.  Single-factor mirror of `hcZetaPair_mem_xiSet` — the pair restricts on `hInHu` to the
inflation `θ₀` (`hcuPsiPair_apply_inclusion`), so `H ⊆ Ker` would force `θ = 1`. -/
theorem hcuZetaPair_mem_xiSet [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  classical
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ with hζdef
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ cuInHu caseA) ζ (hcuPsiPair caseA θ hinv lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  rw [xiSet, Set.mem_setOf_eq]
  intro hsub
  apply hθnt
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun q => ?_
  obtain ⟨h, hhq⟩ := hfsurj q
  have hgmem : ((Subgroup.inclusion
      (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h :
      ↥(hInHu data ⊔ cuInHu caseA)) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      1 = 1 := by
    simp [hcuPsiPair]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcuPsiPair_apply_inclusion caseA θ hinv lam h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  show θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
/-- **`ζ_{θ₁,λ} ∈ 𝒳(H₀U')`**: combining `H ⊄ Ker` (`hcuZetaPair_mem_xiSet`) and `H₀U' ⊆ Ker`
(`hcuZetaPair_H0supUprime_subset_ker`).  The source character of the (9.8.d) `𝒮(H₀U')`-member
`Ind_{HU}^M ζ_{θ₁,λ}`.  Single-factor mirror of `hcZetaPair_mem_xiOf`. -/
theorem hcuZetaPair_mem_xiOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ uprimeSub data) := by
  rw [mem_xiOf]
  exact ⟨hcuZetaPair_mem_xiSet caseA θ hθnt hinv lam hθ₀,
    hcuZetaPair_H0supUprime_subset_ker caseA θ hinv lam hlam⟩

/-- **`Ind_{HU}^M ζ_{θ₁,λ} ∈ 𝒮(H₀U')`** (Peterfalvi (9.8.d) membership (iii)): the `M`-induction of
the (9.8.d) source character lies in `𝒮(H₀U')`.  Direct from `hcuZetaPair_mem_xiOf` and the
definition of `sOf` (mirror of `hcZeta_induceHU_mem_sOf`). -/
theorem hcuZetaPair_induceHU_mem_sOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ uprimeSub data) := by
  rw [mem_sOf]
  exact ⟨⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩,
    hcuZetaPair_mem_xiOf caseA θ hθnt hinv lam hlam hθ₀, rfl⟩

/-- **`Ind_{HU}^M ζ_{θ₁,λ}` is irreducible** (Peterfalvi (9.8.d) (iv), `hIM`-gated).  Given the source
character `ζ_{θ₁,λ}` is not `W₁`-fixed (`hIM : I_{HU-ambient}(ζ) ≠ ⊤`, i.e. `I_M(ζ) ≠ M`), the
`M`-induction `Ind_{HU}^M ζ` is irreducible.  Since `HU ◁ M` with `[M:HU] = q` prime, `HU ≤ I_M(ζ) ≤ M`
and `I_M(ζ) ≠ M` force `I_M(ζ) = HU` (`eq_of_le_of_prime_index`), whence `Ind` is irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`).  Single-factor mirror of `hcZeta_induceHU_irreducible`;
its `hIM` is the genuinely-hard `W₁`-free-orbit datum for the `S₀`-supported `θ₁` (see the (9.8.d)
`Still open` note on `caseA_character_counts`), left as an explicit hypothesis. -/
theorem hcuZetaPair_induceHU_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA)
    (hIM : ClassFunction.inertia (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) ≠ ⊤) :
    IsIrreducibleCharacter (induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)) := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hIeq : ClassFunction.inertia (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) = huSub data := by
    refine eq_of_le_of_prime_index (ClassFunction.subgroup_le_inertia _) ?_ hIM
    rw [huSub_index_eq_q]; exact data.nontrivial.2.1
  exact isIrreducibleCharacter_induce_of_inertia_eq
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ : IrreducibleCharacter ↥(huSub data)) hIeq

/-- **A nontrivial linear character of the chief factor exists**: `H̄` is a nontrivial finite
abelian group, so `|Hom(H̄, ℂˣ)| = |H̄| > 1` (`card_monoidHom_of_hasEnoughRootsOfUnity`).
Supplies the `θ ≠ 1` seed of the (9.9.c) pair character in Clifford case (b) (where no regular
character is needed — `inertia_eq_hcInHu` takes any nontrivial `θ`). -/
theorem exists_chiefFactorHom_ne_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 := by
  haveI := chief.N_normal
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.1 }
  haveI : Nontrivial (↥data.H ⧸ chief.N) := by
    obtain ⟨x, hxH, hxnot⟩ := SetLike.exists_of_lt chief.H0_lt_H
    refine ⟨⟨QuotientGroup.mk ⟨x, hxH⟩, 1, ?_⟩⟩
    rw [ne_eq, QuotientGroup.eq_one_iff]
    intro hmem
    exact hxnot (chief.H0_eq ▸ Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)
  haveI : NeZero (Monoid.exponent (↥data.H ⧸ chief.N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((↥data.H ⧸ chief.N) →* ℂˣ) = Nat.card (↥data.H ⧸ chief.N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  haveI : Nontrivial ((↥data.H ⧸ chief.N) →* ℂˣ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr ‹_›
  obtain ⟨f, g, hfg⟩ := exists_pair_ne ((↥data.H ⧸ chief.N) →* ℂˣ)
  rcases eq_or_ne f 1 with rfl | hf
  · exact ⟨g, (Ne.symm hfg)⟩
  · exact ⟨f, hf⟩

/-- **The realization iso `cInHu ≃* C`** (`G`-value preserving): the doubly-realized
`C = C_U(H̄)` inside `HU` is isomorphic to the `G`-level `cSub`. -/
noncomputable def cInHuEquivC {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ↥(cInHu data chief) ≃* ↥(cSub data chief) :=
  (Subgroup.subgroupOfEquivOfLe (Subgroup.subgroupOf_mono M
      (le_trans (cSub_le_U data chief) le_sup_right))).trans
    (Subgroup.subgroupOfEquivOfLe ((cSub_le_U data chief).trans (U_le_M data)))

theorem cInHuEquivC_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) (c : ↥(cInHu data chief)) :
    ((cInHuEquivC data chief c : ↥(cSub data chief)) : G)
      = (((c : ↥(huSub data)) : ↥M) : G) := rfl

/-- **A `C'`-trivial nontrivial linear character of `C` exists** (`C ≠ 1`): `C` is a nontrivial
solvable group (subgroup of the solvable maximal `M`), so its abelianization is nontrivial
(`IsSolvable.commutator_lt_top_of_nontrivial`) and carries `|C/C'| > 1` linear characters; any
of them kills every element of the realized `C' = ⁅C,C⁆` (commutators die in an abelian
target).  Supplies the `λ` of the (9.9.c) pair character together with its `hlam` kernel
hypothesis. -/
theorem exists_cInHuHom_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hC : cSub data chief ≠ ⊥) :
    ∃ lam : ↥(cInHu data chief) →* ℂˣ, lam ≠ 1 ∧
      ∀ c : ↥(cInHu data chief),
        (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
        lam c = 1 := by
  classical
  -- `cInHu` is a nontrivial finite solvable group.
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups data.maximal
  haveI : IsSolvable ↥(cInHu data chief) :=
    solvable_of_solvable_injective (f := (huSub data).subtype.comp
      (cInHu data chief).subtype)
      ((huSub data).subtype_injective.comp (cInHu data chief).subtype_injective)
  haveI : Nontrivial ↥(cSub data chief) := (Subgroup.nontrivial_iff_ne_bot _).mpr hC
  haveI : Nontrivial ↥(cInHu data chief) := (cInHuEquivC data chief).toEquiv.nontrivial
  -- the abelianization is nontrivial, so it has more than one linear character.
  have hlt : commutator ↥(cInHu data chief) < ⊤ :=
    IsSolvable.commutator_lt_top_of_nontrivial ↥(cInHu data chief)
  haveI : Nontrivial (Abelianization ↥(cInHu data chief)) := by
    obtain ⟨x, -, hxnot⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨Abelianization.of x, 1, fun h => hxnot ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  haveI : NeZero (Monoid.exponent (Abelianization ↥(cInHu data chief))) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card (Abelianization ↥(cInHu data chief) →* ℂˣ)
      = Nat.card (Abelianization ↥(cInHu data chief)) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  haveI : Nontrivial (Abelianization ↥(cInHu data chief) →* ℂˣ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr ‹_›
  have hf : ∃ f : Abelianization ↥(cInHu data chief) →* ℂˣ, f ≠ 1 := by
    obtain ⟨f, g, hfg⟩ := exists_pair_ne (Abelianization ↥(cInHu data chief) →* ℂˣ)
    rcases eq_or_ne f 1 with rfl | hf
    · exact ⟨g, (Ne.symm hfg)⟩
    · exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hf
  refine ⟨f.comp Abelianization.of, ?_, ?_⟩
  · intro h1
    apply hf
    have hsurj : Function.Surjective ((Abelianization.of :
        ↥(cInHu data chief) →* Abelianization ↥(cInHu data chief))) := fun a =>
      QuotientGroup.mk_surjective a
    exact (MonoidHom.cancel_right hsurj).mp
      (h1.trans (MonoidHom.one_comp Abelianization.of).symm)
  · intro c hc
    -- `c` corresponds under the realization iso to an element of `commutator ↥C`.
    have hcG : (((c : ↥(huSub data)) : ↥M) : G) ∈ cprimeSub data chief :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hc)
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp (by
      rw [show cprimeSub data chief
          = (commutator ↥(cSub data chief)).map (cSub data chief).subtype from rfl] at hcG
      exact hcG)
    have hceq : cInHuEquivC data chief c = y :=
      Subtype.ext ((cInHuEquivC_coe data chief c).trans hyval.symm)
    have hcsymm : c = (cInHuEquivC data chief).symm y := by
      rw [← hceq, MulEquiv.symm_apply_apply]
    have hccomm : c ∈ commutator ↥(cInHu data chief) := by
      have hmapped : (commutator ↥(cSub data chief)).map
          (cInHuEquivC data chief).symm.toMonoidHom = commutator ↥(cInHu data chief) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (cInHuEquivC data chief).symm.surjective]
      rw [hcsymm, ← hmapped]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply,
      show (Abelianization.of c : Abelianization ↥(cInHu data chief))
        = QuotientGroup.mk c from rfl,
      (QuotientGroup.eq_one_iff c).mpr hccomm]
    exact map_one f

/-- **`ψ_{θ,λ}|_C = λ`** (pointwise): on the inclusion of `c ∈ cInHu` into `HC` the pair hom
returns `λ c` — the `θ`-factor dies on `C ≤ H₀C` (`hcHom_eq_one_of_mem_realizedH0supC`).
The (9.9.c) lever: `C ⊆ Ker ψ_{θ,λ}` forces `λ = 1`. -/
theorem hcPairHom_inclusion_cInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (c : ↥(cInHu data chief)) :
    hcPairHom chief θ lam (Subgroup.inclusion (cInHu_le_hcRealized chief) c) = lam c := by
  have hmemHC : Subgroup.inclusion (cInHu_le_hcRealized chief) c
      ∈ ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ le_sup_right) c.2
  have hθfac : θ.comp (hcHom chief) (Subgroup.inclusion (cInHu_le_hcRealized chief) c) = 1 := by
    rw [MonoidHom.comp_apply, hcHom_eq_one_of_mem_realizedH0supC chief hmemHC, map_one]
  simp only [hcPairHom, MonoidHom.mul_apply, hθfac, one_mul,
    hcLambdaHom_inclusion chief lam c]

set_option maxHeartbeats 1000000 in
/-- **`C ⊆ Ker ζ_{θ,λ}` forces `λ = 1`** (the (9.9.c) rigidity): if the realized `C` lies in
the kernel of `ζ_{θ,λ} = Ind_{HC}^{HU}(ψ_{θ,λ})`, then kernel descent
(`mem_characterKernel_of_mem_characterKernel_induce`, `HC ◁ HU`) puts `C` in the kernel of the
pair itself, whose `C`-restriction is `λ` (`hcPairHom_inclusion_cInHu`). -/
theorem lam_eq_one_of_cInHu_subset_ker_zetaPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    (hker : ∀ z : ↥(huSub data), z ∈ cInHu data chief →
      z ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ)))
    (c : ↥(cInHu data chief)) : lam c = 1 := by
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).Normal := hcInHu_realized_normal chief
  have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
    (L := ↥(huSub data))
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (hcPsiPair chief θ lam).isIrreducible
    (cInHu_le_hcRealized chief c.2) (hker (c : ↥(huSub data)) c.2)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def] at hdesc
  have hint : (⟨(c : ↥(huSub data)), cInHu_le_hcRealized chief c.2⟩ :
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      = Subgroup.inclusion (cInHu_le_hcRealized chief) c := rfl
  rw [hint] at hdesc
  have hpair1 : (hcPsiPair chief θ lam : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      1 = 1 := by simp [hcPsiPair]
  rw [hpair1] at hdesc
  refine Units.ext ?_
  rw [Units.val_one, ← hdesc]
  simp only [hcPsiPair, linearIrreducibleCharacter_apply, hcPairHom_inclusion_cInHu chief θ lam c]

set_option maxHeartbeats 1000000 in
/-- **Peterfalvi (9.9.c), the `C = 1` half**: in Clifford case (b), if `𝒮(H₀C')` contains no
irreducible character then `C = ⊥`.  Otherwise take `θ ≠ 1` on `H̄`
(`exists_chiefFactorHom_ne_one`) and `λ ≠ 1` on `C` trivial on `C'`
(`exists_cInHuHom_ne_one`): the pair induction `φ = Ind_{HU}^M ζ_{θ,λ}` lies in `𝒮(H₀C')`
(`hcZetaPair_mem_xiOf`), is reducible by the hypothesis, hence lies in `𝒮(H₀C)`
(`reducible_mem_sOf_H0C`, (9.9.b)); its source is then `M`-conjugate to a `𝒳(H₀C)`-member
(`induce_eq_induce_iff_conj`), so `C ⊆ H₀C ⊆ Ker ζ_{θ,λ}` (`H₀C ◁ M` transports the kernel
along the conjugation), forcing `λ = 1` (`lam_eq_one_of_cInHu_subset_ker_zetaPair`) —
contradiction. -/
theorem caseB_no_irreducible_forces_C_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) :
    chars.C = ⊥ := by
  classical
  by_contra hC
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  obtain ⟨θ, hθne⟩ := exists_chiefFactorHom_ne_one chief
  obtain ⟨lam, hlamne, hlam⟩ := exists_cInHuHom_ne_one hG chief hC
  have hθbarnt : (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθne
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  set ζp : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsiPair chief θ lam), hcZetaPair_irreducible chief θ lam hθ₀⟩ with hζpdef
  have hζpX : ζp ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief) :=
    hcZetaPair_mem_xiOf chief θ hθne lam hlam hθ₀
  have hφmem : induceHU data (ζp : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) :=
    mem_sOf.mpr ⟨ζp, hζpX, rfl⟩
  have hred : ¬ IsIrreducibleCharacter (induceHU data (ζp : ClassFunction ↥(huSub data) ℂ)) :=
    fun hirr => hno ⟨induceHU data (ζp : ClassFunction ↥(huSub data) ℂ), hφmem, hirr⟩
  have hφH0 : induceHU data (ζp : ClassFunction ↥(huSub data) ℂ) ∈ sOf data chief.H0 :=
    sOf_antitone data le_sup_left hφmem
  have hφH0C := reducible_mem_sOf_H0C hG chars _ hφH0 hred
  obtain ⟨ζ', hζ'X, hφeq⟩ := mem_sOf.mp hφH0C
  obtain ⟨w, hw⟩ := (OddOrder.RepresentationTheory.induce_eq_induce_iff_conj
    (G := ↥M) (H := huSub data) ζp ζ').mp hφeq
  haveI hH0Cnormal := chiefFactor_H0supC_subgroupOf_normal chief
  have hCker : ∀ z : ↥(huSub data), z ∈ cInHu data chief →
      z ∈ OddOrder.Peterfalvi.S03.characterKernel (ζp : ClassFunction ↥(huSub data) ℂ) := by
    intro z hz
    have hzH0C : (z : ↥M) ∈ (chief.H0 ⊔ cSub data chief).subgroupOf M :=
      Subgroup.subgroupOf_mono _ le_sup_right (Subgroup.mem_subgroupOf.mp hz)
    have hymem : w⁻¹ * (z : ↥M) * w ∈ huSub data := by
      simpa using (huSub_normal data).conj_mem _ z.2 w⁻¹
    have hyH0C : (⟨w⁻¹ * (z : ↥M) * w, hymem⟩ : ↥(huSub data))
        ∈ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa using hH0Cnormal.conj_mem _ hzH0C w⁻¹
    have hyker : (⟨w⁻¹ * (z : ↥M) * w, hymem⟩ : ↥(huSub data))
        ∈ OddOrder.Peterfalvi.S03.characterKernel
          (ζ' : ClassFunction ↥(huSub data) ℂ) := hζ'X.2 hyH0C
    have hval : (ζ' : ClassFunction ↥(huSub data) ℂ) ⟨w⁻¹ * (z : ↥M) * w, hymem⟩
        = (ζp : ClassFunction ↥(huSub data) ℂ) z := by
      rw [← hw, IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      exact congrArg _ (Subtype.ext
        (show w * (w⁻¹ * (z : ↥M) * w) * w⁻¹ = (z : ↥M) by group))
    have hone : (ζ' : ClassFunction ↥(huSub data) ℂ) 1
        = (ζp : ClassFunction ↥(huSub data) ℂ) 1 := by
      rw [← hw, IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      exact congrArg _ (Subtype.ext (by simp))
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hyker ⊢
    exact hval.symm.trans (hyker.trans hone)
  have hlam1 : ∀ c : ↥(cInHu data chief), lam c = 1 := by
    intro c
    exact lam_eq_one_of_cInHu_subset_ker_zetaPair chief θ lam (fun z hz => hCker z hz) c
  obtain ⟨c₀, hc₀⟩ := DFunLike.ne_iff.mp hlamne
  exact hc₀ (by rw [hlam1 c₀, MonoidHom.one_apply])

/-- **Inertia index of `hcPsi θ` is `u`** (regular `θ`): for a regular seed `θ` (nontrivial on each
Clifford factor `Hpart i`), the `HU`-inertia of `ζ_θ = hcPsi θ` is `HC` (`hcPsi_inertia_eq_hc` with the
`inertia_eq_hcInHu_caseA` seed), so `[HU : I_{HU}(hcPsi θ)] = [HU:HC] = u` (`hc_index_eq_u`).  This is
the uniform fibre size `[HU : I]` of the induction map `θ ↦ Ind_{HC}^{HU}(hcPsi θ)` in the `oXtheta`
`u`-to-1 count (each `HU`-conjugation orbit of a regular `hcPsi θ` has `u` elements). -/
theorem hcPsi_inertia_index_eq_u [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hreg : ∀ i, ∃ x ∈ caseA.Hpart i, θ x ≠ 1)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (IrreducibleCharacter.inertia (hcPsi chief θ)).index = chars.u := by
  have hreg' : ∀ i, ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro i
    obtain ⟨x, hx, hne⟩ := hreg i
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one]
    simpa using hne
  have hθ₀ := inertia_eq_hcInHu_caseA data chief caseA hreg'
  change (ClassFunction.inertia (hcPsi chief θ : ClassFunction
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)).index
      = chars.u
  rw [hcPsi_inertia_eq_hc chief θ hθ₀, hc_index_eq_u chars]

/-- **Descent of `HU`-conjugation to `H̄`.**  For `g ∈ HU`, conjugation by `g` on `HC` preserves
`ker hcHom = H₀C` (`H₀C ◁ HU`, `realizedH0supC_normal_huSub`), so it descends through `hcHom` to an
endomorphism `A_g` of `H̄`: `QuotientGroup.map` on `HC/H₀C` transported by the second iso
`hcQuotientEquivHbar`.  Satisfies `A_g ∘ hcHom = hcHom ∘ (conjBy g)` (`hcHom_hcConjDescend`), the
factoring behind the conjugation-commute `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`. -/
noncomputable def hcConjDescend [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (↥data.H ⧸ chief.N) →* (↥data.H ⧸ chief.N) :=
  letI hK : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  (hcQuotientEquivHbar chief).toMonoidHom.comp
    ((QuotientGroup.map
        ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (ClassFunction.conjByMulEquiv g).toMonoidHom
        (by
          intro x hx
          simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf,
            ClassFunction.conjByMulEquiv_apply] at hx ⊢
          exact (realizedH0supC_normal_huSub chief).conj_mem _ hx g)).comp
      (hcQuotientEquivHbar chief).symm.toMonoidHom)

/-- **Factoring `A_g ∘ hcHom = hcHom ∘ conjBy g`**: `A_g (hcHom x) = hcHom (g·x·g⁻¹)`.  Unwinding
`A_g = iso ∘ QuotientGroup.map ∘ iso⁻¹` and `hcHom = iso ∘ mk'`, the `iso⁻¹∘iso` cancels and
`QuotientGroup.map_mk'` turns `map (mk' x)` into `mk' (conjBy g x)`.  The pointwise identity behind
the conjugation-commute `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`. -/
theorem hcConjDescend_hcHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    hcConjDescend chief g (hcHom chief x) = hcHom chief (ClassFunction.conjByMulEquiv g x) := by
  letI hK : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  simp only [hcConjDescend, hcHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, QuotientGroup.map_mk']
  rw [QuotientGroup.mk'_apply]

/-- **Conjugation-commute for `hcPsi`**: `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)` for `g ∈ HU`, where
`A_g = hcConjDescend g`.  Pointwise: `(conjBy g (hcPsi θ)) y = (hcPsi θ)(g·y·g⁻¹) = θ(hcHom(g·y·g⁻¹))
= θ(A_g(hcHom y)) = (hcPsi (θ∘A_g)) y`, using the factoring `hcConjDescend_hcHom`.  This is the
`HU`-conjugation ↔ `Ū`-precomposition equivariance: the `HU`-orbit of `hcPsi θ` consists of the
`hcPsi (θ∘A_g)`, so the regular-inflated set is conjugation-closed (modulo the case-A regularity of
`θ∘A_g`) — the `T`-invariance input to the `oXtheta` `card_filter` count. -/
theorem hcPsi_conjBy_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ClassFunction.conjBy g (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = (hcPsi chief (θ.comp (hcConjDescend chief g)) : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  ext y
  have hval : ClassFunction.conjBy g (hcPsi chief θ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) y
      = (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (ClassFunction.conjByMulEquiv g y) := rfl
  rw [hval]
  simp only [hcPsi, linearIrreducibleCharacter_apply, MonoidHom.comp_apply, hcConjDescend_hcHom]

/-- **`A_g = hcConjDescend g` is bijective** (an automorphism of `H̄`), with inverse
`A_{g⁻¹}`: `A_g(A_{g⁻¹} z) = z` and `A_{g⁻¹}(A_g z) = z` by the factoring `hcConjDescend_hcHom`
(`hcHom` surjective) and `g·(g⁻¹·y·g)·g⁻¹ = y`.  Together with `A_g(Hpart i) ⊆ Hpart i` (case-A
`Hpart_aInvariant`, the `U`-action factor-preservation) this gives `A_g(Hpart i) = Hpart i`, hence
`θ ∘ A_g` regular ⟺ `θ` regular — the regularity half of the `oXtheta` `T`-invariance. -/
theorem hcConjDescend_bijective [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    Function.Bijective (hcConjDescend chief g) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨hcConjDescend chief g⁻¹, ?_, ?_⟩ <;>
  · intro z
    obtain ⟨x, rfl⟩ := hcHom_surjective chief z
    rw [hcConjDescend_hcHom, hcConjDescend_hcHom]
    congr 1
    apply Subtype.ext
    simp only [ClassFunction.conjByMulEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group

/-- **`A_g = id` for `g ∈ HC`**: conjugation by an `HC`-element descends to the identity on `H̄`,
because `H̄ = H/N` is abelian and `hcHom` is a homomorphism, so `hcHom(g·x·g⁻¹) = hcHom x`.  Since
`HC ⊇ hInHu` (the `H`-part of `HU`) and `HC ⊇ C`, the nontrivial part of `A_·` factors through
`HU/HC ≅ Ū`.  Reduces the case-A factor-preservation `A_g(Hpart i) ⊆ Hpart i` to the `U`-part
(realizable in `U ⊔ W₁`), where it is the `uActionHom` action (`Hpart_aInvariant`). -/
theorem hcConjDescend_eq_id_of_mem_hc [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) {g : ↥(huSub data)}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hg : g ∈ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
    hcConjDescend chief g = MonoidHom.id (↥data.H ⧸ chief.N) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, hx⟩ := hcHom_surjective chief z
  rw [← hx, hcConjDescend_hcHom, MonoidHom.id_apply]
  have hconj : ClassFunction.conjByMulEquiv g x
      = (⟨g, hg⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) * x * (⟨g, hg⟩)⁻¹ := by
    apply Subtype.ext
    simp [ClassFunction.conjByMulEquiv_apply]
  rw [hconj, map_mul, map_mul, map_inv,
    chief.quotient_elementaryAbelian.comm (hcHom chief ⟨g, hg⟩) (hcHom chief x),
    mul_assoc, mul_inv_cancel, mul_one]

/-- **`A_·` is multiplicative**: `A_{g₁·g₂} = A_{g₁} ∘ A_{g₂}` (conjugation is a homomorphism into
`End(H̄)`, preserved by the `QuotientGroup.map` transport).  With `hcConjDescend_eq_id_of_mem_hc`
(`A_h = id` for `h ∈ HC`) this reduces `A_g` for `g = h·u ∈ HU` (`h ∈ hInHu`, `u ∈ uInHu`) to the
`U`-part `A_u`, giving the case-A factor-preservation from `Hpart_aInvariant`. -/
theorem hcConjDescend_mul [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g₁ g₂ : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    hcConjDescend chief (g₁ * g₂)
      = (hcConjDescend chief g₁).comp (hcConjDescend chief g₂) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, hx⟩ := hcHom_surjective chief z
  rw [← hx, MonoidHom.comp_apply, hcConjDescend_hcHom, hcConjDescend_hcHom, hcConjDescend_hcHom]
  congr 1
  apply Subtype.ext
  simp only [ClassFunction.conjByMulEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- **`A_u = uActionHom(a)` for a `U`-part element `u ∈ uInHu`** (P3 of the case-A
factor-preservation).  For `u ∈ uInHu` (a realized `U`-element inside `HU`), the descended
conjugation `A_u = hcConjDescend u` agrees on `H̄ = H/N` with the abstract `U`-action
`uActionHom data chief a`, where `a` is the realization of `u` in `↥(U.subgroupOf (U ⊔ W₁))`.
Both descend the conjugation `x ↦ u·x·u⁻¹` to `H̄`, matched pointwise by the shared `G`-value
`u_G·h_G·u_G⁻¹`: on the left via `hcHom_inclusion` (`hcHom` on the `H`-part is `mk'_N ∘ hInHuEquivH`)
and the factoring `hcConjDescend_hcHom`, on the right via `quotientMulAutHom_apply_mk'` and
`typeP_conjAction_apply`.  Combined with `hcConjDescend_mul`/`hcConjDescend_eq_id_of_mem_hc` (the
`H`-part `A_h` is the identity), this reduces the case-A factor-preservation `A_g(Hpart i) ⊆ Hpart i`
to the `U`-invariance `Hpart_aInvariant`. -/
theorem hcConjDescend_eq_uActionHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) {u : ↥(huSub data)}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hu : u ∈ uInHu data) :
    ∃ a, ∀ z, hcConjDescend chief u z = uActionHom data chief a z := by
  have huU : ((u : ↥M) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hu)
  set x₀ : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩ with hx₀
  refine ⟨⟨x₀, Subgroup.mem_subgroupOf.mpr huU⟩, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective chief.N z
  obtain ⟨h, rfl⟩ := (hInHuEquivH data).surjective y
  -- right side: the abstract `U`-action descends `mk'_N` to `typeP_conjAction x₀`
  have hRHS : uActionHom data chief ⟨x₀, Subgroup.mem_subgroupOf.mpr huU⟩
        (QuotientGroup.mk' chief.N (hInHuEquivH data h))
      = QuotientGroup.mk' chief.N (typeP_conjAction data.typeP x₀ (hInHuEquivH data h)) := by
    show (quotientMulAutHom chief.N_aInvariant) x₀
        (QuotientGroup.mk' chief.N (hInHuEquivH data h)) = _
    rw [OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
  -- left side: `A_u ∘ hcHom` = `hcHom ∘ conjBy u`, and the conjugate lands in `hInHu`
  have hmem' : (u : ↥(huSub data)) * (h : ↥(huSub data)) * (u : ↥(huSub data))⁻¹ ∈ hInHu data :=
    (hInHu_normal data).conj_mem (h : ↥(huSub data)) h.2 (u : ↥(huSub data))
  have hincl : (ClassFunction.conjByMulEquiv u (Subgroup.inclusion le_sup_left h)
      : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      = Subgroup.inclusion le_sup_left ⟨_, hmem'⟩ := by
    apply Subtype.ext
    rw [ClassFunction.conjByMulEquiv_apply, Subgroup.coe_inclusion, Subgroup.coe_inclusion]
  rw [hRHS, ← hcHom_inclusion chief h, hcConjDescend_hcHom, hincl, hcHom_inclusion]
  -- both sides are `mk'_N` of the same `H`-element (equal `G`-value `u_G·h_G·u_G⁻¹`)
  refine congrArg (QuotientGroup.mk' chief.N) (Subtype.ext ?_)
  simp only [hInHuEquivH_coe, typeP_conjAction_apply, hx₀, Subgroup.coe_mul, Subgroup.coe_inv]

/-- **Case-A factor-preservation: `A_g` maps each Clifford summand `Hpart i` into itself.**  For any
`g ∈ HU`, the descended conjugation `A_g = hcConjDescend g` maps the order-`p` chief-factor summand
`caseA.Hpart i` into itself.  Decompose `g = h·u` (`h ∈ hInHu`, `u ∈ uInHu`, from
`hInHu_sup_uInHu_eq_top` + normality of `hInHu`); then `A_g = A_h ∘ A_u = A_u` (`hcConjDescend_mul`
and `hcConjDescend_eq_id_of_mem_hc`, since `h ∈ hInHu ⊆ HC`), and `A_u = uActionHom a`
(`hcConjDescend_eq_uActionHom`) preserves `Hpart i` by `Hpart_aInvariant`.  This is the geometric
core of the regularity half of the `oXtheta` `T`-invariance: `A_g` permutes the summands trivially
(each stays fixed setwise), so `θ ∘ A_g` is regular iff `θ` is. -/
theorem hcConjDescend_maps_Hpart [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data)) {i : Fin data.q} {z : ↥data.H ⧸ chief.N}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hz : z ∈ caseA.Hpart i) :
    hcConjDescend chief g z ∈ caseA.Hpart i := by
  -- decompose `g = h·u` with `h ∈ hInHu`, `u ∈ uInHu`
  have hgtop : g ∈ hInHu data ⊔ uInHu data := by rw [hInHu_sup_uInHu_eq_top]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgtop
  obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
  -- `A_{h·u} = A_h ∘ A_u`, and `A_h = id` (`h ∈ hInHu ⊆ HC`)
  rw [hcConjDescend_mul, MonoidHom.comp_apply,
    hcConjDescend_eq_id_of_mem_hc chief (Subgroup.mem_sup_left hh), MonoidHom.id_apply]
  -- `A_u = uActionHom a` preserves `Hpart i`
  obtain ⟨a, ha⟩ := hcConjDescend_eq_uActionHom chief hu
  rw [ha]
  exact (caseA.Hpart_aInvariant i).smul_mem a hz

/-- **`A_1 = id`**: `hcConjDescend 1` is the identity, since `1 ∈ HC`
(`hcConjDescend_eq_id_of_mem_hc`). -/
theorem hcConjDescend_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    hcConjDescend chief (1 : ↥(huSub data)) = MonoidHom.id (↥data.H ⧸ chief.N) :=
  hcConjDescend_eq_id_of_mem_hc chief (Subgroup.one_mem _)

/-- **`A_g ∘ A_{g⁻¹} = id`**: `A_g (A_{g⁻¹} z) = z`, from multiplicativity (`hcConjDescend_mul`)
and `A_1 = id` (`hcConjDescend_one`).  Together with `hcConjDescend_maps_Hpart` this makes `A_g`
restrict to a *bijection* of each Clifford summand `Hpart i`. -/
theorem hcConjDescend_apply_inv_apply [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (z : ↥data.H ⧸ chief.N) :
    hcConjDescend chief g (hcConjDescend chief g⁻¹ z) = z := by
  rw [← MonoidHom.comp_apply, ← hcConjDescend_mul, mul_inv_cancel, hcConjDescend_one,
    MonoidHom.id_apply]

/-- **Regularity preservation (per factor)**: for `g ∈ HU`, the precomposed character `θ ∘ A_g` is
trivial on the Clifford summand `Hpart i` iff `θ` is.  `A_g` restricts to a bijection of `Hpart i`
(`hcConjDescend_maps_Hpart` for both `g` and `g⁻¹`, inverted by `hcConjDescend_apply_inv_apply`),
so the value multisets `{θ(A_g x) | x ∈ Hpart i}` and `{θ(y) | y ∈ Hpart i}` coincide. -/
theorem hcConjDescend_comp_subtype_eq_one_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data)) {i : Fin data.q}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (hcConjDescend chief g)).comp (caseA.Hpart i).subtype = 1
      ↔ θ.comp (caseA.Hpart i).subtype = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun y => ?_
    have hval := DFunLike.congr_fun h ⟨_, hcConjDescend_maps_Hpart caseA g⁻¹ y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] at hval ⊢
    rwa [hcConjDescend_apply_inv_apply] at hval
  · intro h
    refine MonoidHom.ext fun x => ?_
    have hval := DFunLike.congr_fun h ⟨_, hcConjDescend_maps_Hpart caseA g x.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] using hval

/-- **Regularity preservation**: for `g ∈ HU`, `θ ∘ A_g` is regular (nontrivial on every Clifford
summand `Hpart i`) iff `θ` is.  Immediate from the per-factor
`hcConjDescend_comp_subtype_eq_one_iff`.  This is the regularity half of the `oXtheta`
`T`-invariance: combined with the conjugation-commute `hcPsi_conjBy_eq`
(`conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`), it shows the regular-inflated set `{hcPsi θ | θ regular}`
is closed under `HU`-conjugation — the input to the `card_filter` fibre count `u·|Xθ| = (p-1)^q`. -/
theorem hcConjDescend_comp_regular_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (∀ i, (θ.comp (hcConjDescend chief g)).comp (caseA.Hpart i).subtype ≠ 1)
      ↔ (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) :=
  forall_congr' fun _ => not_congr (hcConjDescend_comp_subtype_eq_one_iff caseA g θ)

/-- **Conjugation-commute at the `IrreducibleCharacter` level**: `(hcPsi θ)^g = hcPsi (θ ∘ A_g)`.
The `IrreducibleCharacter`-level form of `hcPsi_conjBy_eq` (`coe_conjBy` + `IrreducibleCharacter.ext`),
the shape consumed by the conjugation-closure hypothesis of `card_filter_induce_eq_index_inertia`. -/
theorem hcPsi_irreducibleConjBy_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    IrreducibleCharacter.conjBy g (hcPsi chief θ)
      = hcPsi chief (θ.comp (hcConjDescend chief g)) := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy, hcPsi_conjBy_eq]

/-- **The regular-inflated set is `HU`-conjugation-closed** (`oXtheta` `T`-invariance).  For a regular
seed `θ` (nontrivial on every Clifford factor `Hpart i`) and `g ∈ HU`, the conjugate `(hcPsi θ)^g`
equals `hcPsi θ'` for the regular seed `θ' = θ ∘ A_g`: the commute `hcPsi_irreducibleConjBy_eq` gives
the identity, and `hcConjDescend_comp_regular_iff` gives the regularity of `θ'`.  This is exactly the
conjugation-closure hypothesis `hT` of `card_filter_induce_eq_index_inertia` for the induction
`θ ↦ Ind_{HC}^{HU}(hcPsi θ)` over `T = {hcPsi θ | θ regular}`, whose fibres have size `u`
(`hcPsi_inertia_index_eq_u`), giving the `oXtheta` count `u·|Xθ| = (p-1)^q`
(`card_regular_chars_Hbar`). -/
theorem hcPsi_regular_conjBy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    (g : ↥(huSub data)) :
    ∃ θ', (∀ i, θ'.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IrreducibleCharacter.conjBy g (hcPsi chief θ) = hcPsi chief θ' :=
  ⟨θ.comp (hcConjDescend chief g), (hcConjDescend_comp_regular_iff caseA g θ).mpr hθ,
    hcPsi_irreducibleConjBy_eq chief g θ⟩

/-- **Regularity, hom-form ↔ pointwise-form.**  `θ` is nontrivial on the Clifford summand `Hpart i`
(as a hom, `θ ∘ (Hpart i).subtype ≠ 1`) iff it is nontrivial at some point of `Hpart i`
(`∃ x ∈ Hpart i, θ x ≠ 1`).  Bridges the hom-form regularity of `card_regular_chars_Hbar` to the
pointwise-form `hreg` consumed by `hcPsi_inertia_index_eq_u` in the `oXtheta` fibre count. -/
theorem comp_subtype_ne_one_iff_exists {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (i : Fin data.q) :
    θ.comp (caseA.Hpart i).subtype ≠ 1 ↔ ∃ x ∈ caseA.Hpart i, θ x ≠ 1 := by
  rw [Ne, MonoidHom.ext_iff, not_forall]
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply, Subtype.exists,
    exists_prop]

open scoped Classical in
/-- **The `oXtheta` count** (Peterfalvi (9.8) `oXtheta`): `u · |Xθ| = (p-1)^q`, where `Xθ` is the set
of distinct `HU`-induced characters `Ind_{HC}^{HU}(hcPsi θ)` over regular seeds `θ` (nontrivial on
every Clifford factor `Hpart i`).  The induction `θ ↦ Ind(hcPsi θ)` is `u`-to-1: its fibres are the
`HU`-conjugation orbits (`card_filter_induce_eq_index_inertia`, using the `T`-invariance
`hcPsi_regular_conjBy`), each of size `[HU:HC] = u` (`hcPsi_inertia_index_eq_u`); the domain of
regular seeds has size `(p-1)^q` (`card_regular_chars_Hbar`, `hcPsi_injective`).  This is the
numerator of the (9.8.c) parity dichotomy `exists_regular_not_reducible_of_odd`. -/
theorem oXtheta_count [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    [Fintype ↥(huSub data)] [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    chars.u * ((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
          ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).card
      = (chief.p - 1) ^ data.q := by
  classical
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set T := RegF.image (hcPsi chief) with hTdef
  -- `T = {hcPsi θ | θ regular}` is closed under `HU`-conjugation (T-invariance)
  have hTinv : ∀ χ ∈ T, ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g χ ∈ T := by
    intro χ hχ g
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨θ', hθ', heq⟩ := hcPsi_regular_conjBy caseA (Finset.mem_filter.mp hθ).2 g
    exact heq ▸ Finset.mem_image.mpr ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ'⟩, rfl⟩
  -- each induction fibre has size `u`
  have hfib : ∀ b ∈ T.image fun χ => ClassFunction.induce _ χ.toClassFunction,
      (T.filter fun χ => ClassFunction.induce _ χ.toClassFunction = b).card = chars.u := by
    intro b hb
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hb
    rw [card_filter_induce_eq_index_inertia (G := ↥(huSub data)) T hTinv χ₀ hχ₀]
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hχ₀
    exact hcPsi_inertia_index_eq_u caseA
      (fun i => (comp_subtype_ne_one_iff_exists caseA θ₀ i).mp ((Finset.mem_filter.mp hθ₀).2 i))
  -- fibrewise: `|T| = u · |Xθ|`
  have key : T.card
      = chars.u * (T.image fun χ => ClassFunction.induce _ χ.toClassFunction).card := by
    rw [Finset.card_eq_sum_card_fiberwise
        (fun χ hχ => Finset.mem_image_of_mem (fun χ => ClassFunction.induce _ χ.toClassFunction) hχ),
      Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- `|T| = |RegF| = (p-1)^q`
  have hTeq : T.card = (chief.p - 1) ^ data.q := by
    rw [hTdef, Finset.card_image_of_injective _ (hcPsi_injective chief), hRegF,
      ← card_regular_chars_Hbar chars caseA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- assemble: `u · |Xθ| = |T| = (p-1)^q`
  rw [key, hTdef, Finset.image_image] at hTeq
  exact hTeq

/-- **Nontriviality of a seed survives conjugation-descent**: for `θ ≠ 1` and `g ∈ HU`, the
conjugated seed `θ ∘ A_g` is again nontrivial (`A_g` bijective,
`hcConjDescend_bijective`), and `(hcPsi θ)^g = hcPsi (θ ∘ A_g)`.  The case-(b) `T`-invariance
(regularity of the case-(a) `oXtheta` replaced by mere nontriviality). -/
theorem hcPsi_ne_one_conjBy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : θ ≠ 1) (g : ↥(huSub data)) :
    ∃ θ' : (↥data.H ⧸ chief.N) →* ℂˣ, θ' ≠ 1 ∧
      IrreducibleCharacter.conjBy g (hcPsi chief θ) = hcPsi chief θ' := by
  refine ⟨θ.comp (hcConjDescend chief g), ?_, hcPsi_irreducibleConjBy_eq chief g θ⟩
  intro h1
  apply hθ
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (hcConjDescend_bijective chief g).surjective z
  simpa using DFunLike.congr_fun h1 x

/-- **Case-(b) inertia index of `hcPsi θ` is `u`** (any nontrivial `θ`): with the case-(b)
inertia lift `inertia_eq_hcInHu` (no regularity needed), `[HU : I(hcPsi θ)] = [HU:HC] = u`
(`hc_index_eq_u`).  The uniform fibre size of the case-(b) `oXtheta` count. -/
theorem hcPsi_inertia_index_eq_u_caseB [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : θ ≠ 1)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (IrreducibleCharacter.inertia (hcPsi chief θ)).index = chars.u := by
  have hθbarnt : (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθ
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  change (ClassFunction.inertia (hcPsi chief θ : ClassFunction
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)).index
      = chars.u
  rw [hcPsi_inertia_eq_hc chief θ hθ₀, hc_index_eq_u chars]

open scoped Classical in
/-- **The count of nontrivial chief-factor characters**: `|{θ : H̄ →* ℂˣ | θ ≠ 1}| = p^q − 1`.
Duality `|Hom(H̄, ℂˣ)| = |H̄| = p^q` (`card_monoidHom_of_hasEnoughRootsOfUnity`,
`chiefFactor_quotient_card`) minus the trivial character.  The domain count of the case-(b)
`oXtheta`. -/
theorem card_ne_one_chiefFactorHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)] :
    (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1).card
      = chief.p ^ data.q - 1 := by
  haveI := chief.N_normal
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.1 }
  haveI : NeZero (Monoid.exponent (↥data.H ⧸ chief.N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((↥data.H ⧸ chief.N) →* ℂˣ) = Nat.card (↥data.H ⧸ chief.N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcard, chiefFactor_quotient_card chief]

open scoped Classical in
/-- **The case-(b) `oXtheta` count**: `u · |Xζ| = p^q − 1`, where `Xζ` is the set of distinct
`HU`-induced characters `Ind_{HC}^{HU}(hcPsi θ)` over *all* nontrivial seeds `θ : H̄ →* ℂˣ`.
Mirror of the case-(a) `oXtheta_count` with regularity replaced by nontriviality: fibres of
`θ ↦ Ind(hcPsi θ)` are `HU`-conjugation orbits (`card_filter_induce_eq_index_inertia`,
`T`-invariance `hcPsi_ne_one_conjBy`) of size `u` (`hcPsi_inertia_index_eq_u_caseB`), and the
domain has size `p^q − 1` (`card_ne_one_chiefFactorHom`, `hcPsi_injective`).  With `C = ⊥`
(the (9.9.c) situation) `Xζ` exhausts `𝒳(H₀)`, giving `u·|𝒳(H₀)| = p^q − 1`. -/
theorem caseB_oXtheta_count [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    [Fintype ↥(huSub data)] [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    chars.u * ((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).card
      = chief.p ^ data.q - 1 := by
  classical
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  set NF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1 with hNF
  set T := NF.image (hcPsi chief) with hTdef
  have hTinv : ∀ χ ∈ T, ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g χ ∈ T := by
    intro χ hχ g
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨θ', hθ', heq⟩ := hcPsi_ne_one_conjBy chief (Finset.mem_filter.mp hθ).2 g
    exact heq ▸ Finset.mem_image.mpr ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ'⟩, rfl⟩
  have hfib : ∀ b ∈ T.image fun χ => ClassFunction.induce _ χ.toClassFunction,
      (T.filter fun χ => ClassFunction.induce _ χ.toClassFunction = b).card = chars.u := by
    intro b hb
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hb
    rw [card_filter_induce_eq_index_inertia (G := ↥(huSub data)) T hTinv χ₀ hχ₀]
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hχ₀
    exact hcPsi_inertia_index_eq_u_caseB caseB (Finset.mem_filter.mp hθ₀).2
  have key : T.card
      = chars.u * (T.image fun χ => ClassFunction.induce _ χ.toClassFunction).card := by
    rw [Finset.card_eq_sum_card_fiberwise
        (fun χ hχ => Finset.mem_image_of_mem (fun χ => ClassFunction.induce _ χ.toClassFunction) hχ),
      Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hTeq : T.card = chief.p ^ data.q - 1 := by
    rw [hTdef, Finset.card_image_of_injective _ (hcPsi_injective chief), hNF]
    exact card_ne_one_chiefFactorHom chief
  rw [key, hTdef, Finset.image_image] at hTeq
  exact hTeq

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

/-- **Inner product is preserved under `compHom` by a group isomorphism**.  Generalises
`inner_compHom_of_bijective` (an endomorphism) to a `MulEquiv A ≃* B`.  Used in the lies-over
transitivity of the (9.8.c) Clifford-correspondence step 5, where the intermediate subgroup
`H.subgroupOf K ≃* H` transports the restriction. -/
theorem inner_compHom_mulEquiv {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    [Invertible (Nat.card A : ℂ)] [Invertible (Nat.card B : ℂ)] (e : A ≃* B)
    (a b : ClassFunction B ℂ) :
    ClassFunction.inner (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.inner a b := by
  have hcard : (Nat.card A : ℂ) = Nat.card B := by rw [Nat.card_congr e.toEquiv]
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    innerSum_compHom_mulEquiv]
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcard]

/-- **Lies-over transitivity** (general Clifford): for `H ≤ K ≤ Γ`, if the irreducible `χ` of `Γ`
lies over `θ ∈ Irr H`, then there is an intermediate irreducible `ψ ∈ Irr K` such that `χ` lies over
`ψ` and `ψ` lies over `θ` (transported to `H.subgroupOf K` by `subgroupOfEquivOfLe`).  The
`Res_H χ = Res_{H.subgroupOf K}(Res_K χ)` transitivity (`restrict_restrict_subgroupOf`,
`inner_compHom_mulEquiv`) plus the `K`-irreducible decomposition `Res_K χ = Σ_ψ ⟨Res_K χ, ψ⟩ ψ`
(`sum_inner_irreducibleCharacter_smul`) split the nonzero multiplicity `⟨Res_H χ, θ⟩` as
`Σ_ψ ⟨Res_K χ, ψ⟩ · ⟨Res_{H.sK} ψ, θ'⟩`, so some `ψ` has both factors nonzero.  This is the (a) input
to the (9.8.c) Clifford-correspondence step 5 (a reducible `ξ` over `θ₀ ∈ Irr H` factors through an
`HC`-constituent). -/
theorem exists_liesOver_intermediate {Γ : Type*} [Group Γ] [Finite Γ]
    {H K : Subgroup Γ} (hHK : H ≤ K)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(H.subgroupOf K)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf K) : ℂ)]
    (χ : IrreducibleCharacter Γ) (θ : IrreducibleCharacter ↥H)
    (hover : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ) :
    ∃ ψ : IrreducibleCharacter ↥K,
      OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ ψ ∧
      OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (H.subgroupOf K) ψ
        ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
            (θ : ClassFunction ↥H ℂ),
          θ.isIrreducible.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHK).surjective⟩ := by
  classical
  haveI : Fintype (IrreducibleCharacter ↥K) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hHK with hedef
  set θ' : IrreducibleCharacter ↥(H.subgroupOf K) :=
    ⟨ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ),
      θ.isIrreducible.compHom_of_surjective e.surjective⟩ with hθ'def
  -- Transport `⟨Res_H χ, θ⟩` to `⟨Res_{H.sK}(Res_K χ), θ'⟩`.
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at hover
  have htrans : ClassFunction.inner
      (ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
      (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) ≠ 0 := by
    rw [restrict_restrict_subgroupOf hHK (χ : ClassFunction Γ ℂ),
      show (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ) from rfl,
      inner_compHom_mulEquiv e (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)]
    exact hover
  -- Decompose `Res_K χ = Σ_ψ ⟨Res_K χ, ψ⟩ ψ` and split the inner product.
  have hkey : ClassFunction.inner
      (ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
      (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
      = ∑ ψ : IrreducibleCharacter ↥K,
          ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
              (ψ : ClassFunction ↥K ℂ)
            * ClassFunction.inner
              (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
              (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
      (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))]
    have hrs : ClassFunction.restrict (H.subgroupOf K)
          (∑ ψ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ψ : ClassFunction ↥K ℂ) • (ψ : ClassFunction ↥K ℂ))
        = ∑ ψ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ψ : ClassFunction ↥K ℂ)
              • ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ) := by
      ext x
      simp only [ClassFunction.restrict_apply, ClassFunction.finset_sum_apply,
        ClassFunction.smul_apply]
    rw [hrs, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [ClassFunction.inner_smul_left]
  rw [hkey] at htrans
  obtain ⟨ψ, -, hψ⟩ := Finset.exists_ne_zero_of_sum_ne_zero htrans
  refine ⟨ψ, ?_, ?_⟩
  · rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
      ClassFunction.restrictionMultiplicity_def]
    exact fun h => hψ (by rw [h, zero_mul])
  · rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
      ClassFunction.restrictionMultiplicity_def]
    exact fun h => hψ (by rw [h, mul_zero])

open scoped ComplexOrder in
/-- **Lies-over transitivity, composing *down*** (general Clifford): for `H ≤ K ≤ Γ`, if the
irreducible `χ` lies over `ψ ∈ Irr K` and `ψ` lies over the (transported) `θ' ∈ Irr(H.subgroupOf
K)`,
then `χ` lies over `θ ∈ Irr H`.  The converse direction of `exists_liesOver_intermediate`: expand
`⟨Res_H χ, θ⟩ = ⟨Res_{H.sK}(Res_K χ), θ'⟩` (transitivity `restrict_restrict_subgroupOf` +
`inner_compHom_mulEquiv`) and decompose `Res_K χ = Σ_ρ ⟨Res_K χ,ρ⟩ ρ`, giving
`Σ_ρ ⟨Res_K χ,ρ⟩·⟨Res_{H.sK}ρ,θ'⟩`.  Every term is a product of non-negative restriction
multiplicities (`restrictionMultiplicity_nonneg`), and the `ρ = ψ` term is *strictly* positive (both
factors nonzero), so the whole sum is `> 0`, hence `⟨Res_H χ, θ⟩ ≠ 0`.  This is the tool that
pushes a
lies-over relation at an intermediate subgroup down to `H` — used to see the (9.8.d) `Ind_{HU}^M
ζ`'s
source `ζ` as lying over the chief-factor inflation `θ₀` at `hInHu`. -/
theorem liesOver_of_liesOver_liesOver_subgroupOf {Γ : Type*} [Group Γ] [Finite Γ]
    [Invertible (Nat.card Γ : ℂ)] {H K : Subgroup Γ} (hHK : H ≤ K)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(H.subgroupOf K)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf K) : ℂ)]
    (χ : IrreducibleCharacter Γ) (ψ : IrreducibleCharacter ↥K) (θ : IrreducibleCharacter ↥H)
    (hχψ : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ ψ)
    (hψθ : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (H.subgroupOf K) ψ
      ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
          (θ : ClassFunction ↥H ℂ),
        θ.isIrreducible.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHK).surjective⟩) :
    OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ := by
  classical
  haveI : Fintype (IrreducibleCharacter ↥K) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hHK with hedef
  set θ' : IrreducibleCharacter ↥(H.subgroupOf K) :=
    ⟨ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ),
      θ.isIrreducible.compHom_of_surjective e.surjective⟩ with hθ'def
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def]
  -- `⟨Res_H χ, θ⟩ = ⟨Res_{H.sK}(Res_K χ), θ'⟩`.
  rw [show ClassFunction.inner (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)
      = ClassFunction.inner (ClassFunction.restrict (H.subgroupOf K)
          (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) from ?_]
  · -- expand `Res_K χ = Σ_ρ ⟨Res_K χ, ρ⟩ ρ`.
    have hkey : ClassFunction.inner (ClassFunction.restrict (H.subgroupOf K)
          (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ∑ ρ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ρ : ClassFunction ↥K ℂ)
              * ClassFunction.inner
                (ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ))
                (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) := by
      conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))]
      have hrs : ClassFunction.restrict (H.subgroupOf K)
            (∑ ρ : IrreducibleCharacter ↥K,
              ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                  (ρ : ClassFunction ↥K ℂ) • (ρ : ClassFunction ↥K ℂ))
          = ∑ ρ : IrreducibleCharacter ↥K,
              ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                  (ρ : ClassFunction ↥K ℂ)
                • ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ) := by
        ext x
        simp only [ClassFunction.restrict_apply, ClassFunction.finset_sum_apply,
          ClassFunction.smul_apply]
      rw [hrs, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [ClassFunction.inner_smul_left]
    rw [hkey]
    -- every term `≥ 0`; the `ψ`-term is `> 0`, so the sum is `> 0`, hence `≠ 0`.
    refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun ρ : IrreducibleCharacter ↥K =>
      ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ρ : ClassFunction ↥K ℂ)
        * ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ))
      (fun ρ _ => ?_) (Finset.mem_univ ψ)))
    · -- `0 < ψ`-term.
      have h1 : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ψ : ClassFunction ↥K ℂ) :=
        ClassFunction.restrictionMultiplicity_nonneg K χ.isIrreducible ψ.isIrreducible
      have h1ne : ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ψ : ClassFunction ↥K ℂ) ≠ 0 := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
          ClassFunction.restrictionMultiplicity_def] at hχψ; exact hχψ
      have h2 : (0 : ℂ) ≤ ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) :=
        ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf K) ψ.isIrreducible
          θ'.isIrreducible
      have h2ne : ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) ≠ 0 := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
          ClassFunction.restrictionMultiplicity_def] at hψθ; exact hψθ
      exact mul_pos (lt_of_le_of_ne h1 (Ne.symm h1ne)) (lt_of_le_of_ne h2 (Ne.symm h2ne))
    · -- every term `≥ 0`.
      exact mul_nonneg
        (ClassFunction.restrictionMultiplicity_nonneg K χ.isIrreducible ρ.isIrreducible)
        (ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf K) ρ.isIrreducible
          θ'.isIrreducible)
  · rw [restrict_restrict_subgroupOf hHK (χ : ClassFunction Γ ℂ),
      show (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ) from rfl,
      inner_compHom_mulEquiv e (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)]

/-- **`ψ_{θ₁,λ}` restricts on `hInHu` to the seed inflation `θ₀`** (`subgroupOf` form, (9.8.d)).
Restricting the pair character `hcuPsiPair` to `hInHu.subgroupOf (H·C_U(S₀))` equals the inflation
`θ₀ = linearIrr(θ ∘ mk'_N ∘ hInHuEquivH)` transported along `subgroupOfEquivOfLe`.  Single-factor
mirror of `hcPsi_restrict_hInHu_subgroupOf`, from the pointwise `hcuPsiPair_apply_inclusion`.
Feeds the lies-over descent of `ζ_{θ₁,λ}` onto `θ₀` at `hInHu`. -/
theorem hcuPsiPair_restrict_hInHu_subgroupOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom
          (linearIrreducibleCharacter (θ.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
  ext x
  rw [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  set h := (Subgroup.subgroupOfEquivOfLe (le_sup_left :
    hInHu data ≤ hInHu data ⊔ cuInHu caseA)) x with hh
  have hxeq : (x : ↥(hInHu data ⊔ cuInHu caseA))
      = Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_inclusion, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [hxeq, hcuPsiPair_apply_inclusion caseA θ hinv lam h]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

open OddOrder.RepresentationTheory in
/-- **`ζ_{θ₁,λ}` lies over the chief-factor inflation `θ₀` at `hInHu`** (Peterfalvi (9.8.d)).  The
source `ζ = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})` lies over `ψ_{θ₁,λ}` at `H·C_U(S₀)` (Frobenius
reciprocity, `inner_induce_ne_zero_iff_liesOver`), and `ψ_{θ₁,λ}` restricts on `hInHu` to `θ₀`
(`hcuPsiPair_restrict_hInHu_subgroupOf`, a single irreducible), so `lies-over` descends
(`liesOver_of_liesOver_liesOver_subgroupOf`) to give `ζ` over the inflation `θ₀` at `hInHu`.  The
`hlo` input that lets `caseA_reducible_theta_regular` force the seed `θ` to be regular when `ζ` is
`W₁`-fixed — the crux of the `hIM` discharge. -/
theorem hcuZetaPair_liesOver_hInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Fintype ↥(hInHu data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IrreducibleCharacter.LiesOver (hInHu data)
      (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ : IrreducibleCharacter ↥(huSub data))
      (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)))) := by
  classical
  haveI : Fintype ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ with hζdef
  -- `ζ` lies over `ψ = hcuPsiPair` at `H·C_U(S₀)` (Frobenius reciprocity).
  have hlo0 : IrreducibleCharacter.LiesOver (hInHu data ⊔ cuInHu caseA) ζ
      (hcuPsiPair caseA θ hinv lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  -- `ψ` restricts on `hInHu` to the inflation `θ₀` (single irreducible), so `ψ` lies over `θ₀`.
  set θ'irr : IrreducibleCharacter ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom
        (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom))) : ClassFunction ↥(hInHu data) ℂ),
      (linearIrreducibleCharacter _).isIrreducible.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe _).surjective⟩ with hθ'irr
  have hψθ : IrreducibleCharacter.LiesOver
      ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
      (hcuPsiPair caseA θ hinv lam) θ'irr := by
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def]
    have hres : ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        = (θ'irr : ClassFunction ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) ℂ) :=
      hcuPsiPair_restrict_hInHu_subgroupOf caseA θ hinv lam
    rw [hres, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite θ'irr θ'irr,
      if_pos rfl]
    exact one_ne_zero
  exact liesOver_of_liesOver_liesOver_subgroupOf (le_sup_left :
    hInHu data ≤ hInHu data ⊔ cuInHu caseA) ζ (hcuPsiPair caseA θ hinv lam)
    (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom)))) hlo0 hψθ

/-- **`I_M(Ind_{HU}^M ζ_{θ₁,λ}) ≠ M`** (Peterfalvi (9.8.d), the `hIM` discharge).  For a
*non-regular*
seed `θ` (nontrivial on `S₀` but **trivial on a Clifford summand `Hpart j₁`**, `hnonreg`), the
(9.8.d) source `ζ = Ind_{HU} ψ_{θ₁,λ}` is **not** `W₁`-fixed: were `I_M(ζ) = ⊤`, then
`caseA_reducible_theta_regular` (via `ζ`'s lies-over `θ₀` at `hInHu`, `hcuZetaPair_liesOver_hInHu`)
would force `θ` to be *regular* — nontrivial on *every* summand, contradicting `hnonreg` at `j₁`. 
This is
the honest `W₁`-free-orbit content of (9.8.d): the single-summand `θ₁ ∈ Irr(H̄/(H₂…H_q))` cannot be
`W₁`-invariant because `W₁` transitively permutes the summands, so its support `S₀ = H₁` is moved
off
itself.  Supplies the `hIM` of `hcuZetaPair_induceHU_irreducible`, making the `M`-induction
unconditionally irreducible. -/
theorem hcuZetaPair_inertia_ne_top [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {j₁ : Fin data.q} (hnonreg : θ.comp (caseA.Hpart j₁).subtype = 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Fintype ↥(hInHu data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    ClassFunction.inertia (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) ≠ ⊤ := by
  intro hMfix
  -- `ζ` lies over the inflation `θ₀` at `hInHu`.
  have hlo := hcuZetaPair_liesOver_hInHu caseA θ hinv lam hθ₀
  -- If `I_M(ζ) = ⊤`, then `θ` is regular (`caseA_reducible_theta_regular`); contra `hnonreg` at
  -- `j₁`.
  have hreg := caseA_reducible_theta_regular caseA θ
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ : IrreducibleCharacter ↥(huSub data))
    hlo hMfix hθnt j₁
  exact hreg hnonreg

/-- **`Ind_{HU}^M ζ_{θ₁,λ}` is irreducible — unconditional** (Peterfalvi (9.8.d) (iv)).  Discharges
the
`hIM` hypothesis of `hcuZetaPair_induceHU_irreducible` using the non-regularity of the
single-summand
source `θ` (`hcuZetaPair_inertia_ne_top`): for a `θ` nontrivial on `S₀` and trivial on a Clifford
summand `Hpart j₁` (i.e. `θ ∈ Irr(H̄/(H₂…H_q))`), the `M`-induction of the degree-`a` source
`ζ_{θ₁,λ}` is irreducible with *no* extra hypothesis.  This removes the last `hIM` gate on the
(9.8.d)
degree-`qa` member. -/
theorem hcuZetaPair_induceHU_irreducible_of_nonRegular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {j₁ : Fin data.q} (hnonreg : θ.comp (caseA.Hpart j₁).subtype = 1)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Fintype ↥(hInHu data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IsIrreducibleCharacter (induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)) := by
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact hcuZetaPair_induceHU_irreducible caseA θ hinv lam hθ₀
    (hcuZetaPair_inertia_ne_top caseA θ hθnt hinv lam hnonreg hθ₀)

/-- **Peterfalvi (9.8.d): the degree-`qa` irreducible character of `HU` *whose `M`-induction is also
irreducible* (unconditional).**  Strengthens `caseA_exists_irreducible_source_degree_qa` by
additionally asserting that `Ind_{HU}^M ζ_{θ₁,λ}` is **irreducible** — no `hIM` hypothesis.  Built
from
the *non-regular* source hom (`exists_source_char_hom_caseA_nonRegular`, `θ ∈ Irr(H̄/(H₂…H_q))`
trivial on
a summand `Hpart j₁`): its inertia lift `inertia(θ₀) = H·C_U(S₀)` (`inertia_eq_hcuInHu`) gives the
degree-`a` irreducible source `ζ` (`hcuZetaPair_irreducible`) of degree `a` and `M`-induction degree
`qa` (`hcuZetaPair_induceHU_apply_one`), and its non-regularity discharges `hIM`
(`hcuZetaPair_induceHU_irreducible_of_nonRegular`).  This is the fully-assembled (9.8.d) (iv)
member:
an irreducible degree-`qa` character with irreducible `HU`-source — the input to the (9.8.d) count.
-/
theorem caseA_exists_irreducible_source_degree_qa_induceHU_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Fintype ↥(hInHu data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)] :
    ∃ ζ : ClassFunction ↥(huSub data) ℂ,
      IsIrreducibleCharacter ζ ∧ ζ (1 : ↥(huSub data)) = (caseA.a : ℂ) ∧
      IsIrreducibleCharacter (induceHU data ζ) ∧
      induceHU data ζ (1 : ↥M) = ((data.q * caseA.a : ℕ) : ℂ) := by
  haveI := hcuInHu_normal caseA
  obtain ⟨θ, W, hWinv, hsup, hreg, htriv, j₁, hnonreg⟩ :=
    exists_source_char_hom_caseA_nonRegular caseA
  -- the seed inertia `inertia(θ₀) = H·C_U(S₀)` from the full inertia lift.
  have hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
      (ClassFunction.compHom (QuotientGroup.mk' chief.N)
        (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA :=
    inertia_eq_hcuInHu caseA hWinv hsup hreg htriv
  have hinv := hcuSeedHom_invariance_of_cuInHu_le_inertia caseA θ
    (cuInHu_le_inertia_of_complement_triv caseA hWinv hsup htriv)
  -- `θ ≠ 1` (nontrivial on `S₀`).
  have hθnt : θ ≠ 1 := by
    obtain ⟨x, _, hxne⟩ := hreg
    intro h0
    apply hxne
    rw [h0]
    simp only [linearIrreducibleCharacter_apply, MonoidHom.one_apply, Units.val_one, map_one]
  refine ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
    hcuZetaPair_irreducible caseA θ hinv lam hθ₀,
    hcuZetaPair_apply_one caseA θ hinv lam, ?_,
    hcuZetaPair_induceHU_apply_one caseA θ hinv lam⟩
  exact hcuZetaPair_induceHU_irreducible_of_nonRegular caseA θ hθnt hinv lam hnonreg hθ₀

/-- **Conjugation-stable kernel-containment** (Peterfalvi (9.8.d) count substrate, intrinsic-family
`T`-invariance primitive).  For a class function `χ` on a normal subgroup `K ⊴ G` and a subset
`A ⊆ ↥K` that is *invariant* under conjugation-by-`g` (`conjByMulEquiv g` maps `A` into `A`), the
kernel-containment `A ⊆ Ker χ` transfers to the conjugate `χ^g`: `A ⊆ Ker (conjBy g χ)`.

Pointwise: `(conjBy g χ) y = χ (g·y·g⁻¹)` and `characterDegree (conjBy g χ) = characterDegree χ`
(conjugation fixes the value at `1`), so for `y ∈ A` the conjugate `g·y·g⁻¹ ∈ A ⊆ Ker χ` gives
`(conjBy g χ) y = χ (g·y·g⁻¹) = characterDegree χ = characterDegree (conjBy g χ)`, i.e.
`y ∈ Ker (conjBy g χ)`.

This is the linchpin of the *intrinsic* characterization of the (9.8.d) pair-family
`T = {ψ_{θ₁,λ}}` as `{χ ∈ Irr(H·C_U(S₀)) | linear ∧ H₀-realized ⊆ Ker χ ∧ W-lifted ⊆ Ker χ ∧
χ|_H ≠ 1 ∧ U'-realized ⊆ Ker χ}`: each realized kernel condition `N-realized ⊆ Ker χ` for an
`HU`-normal `N` (H₀-realized, W-lifted, U'-realized — all `◁ HU`) is `HU`-conjugation-stable, because
the ambient normality makes `N-realized ∩ (H·C_U(S₀))` a `conjByMulEquiv g`-invariant set for every
`g ∈ HU`.  Hence `T` is conjugation-closed, the input `hT` of `card_image_induce_eq_div` for the
`|image| = |T|/a` orbit step — without a `hcuPsiPair`-conjBy-descent lemma. -/
theorem subsetCharacterKernel_conjBy_of_invariant {K : Subgroup G} [K.Normal]
    (g : G) (χ : ClassFunction ↥K ℂ) (A : Set ↥K)
    (hAinv : ∀ a ∈ A, ClassFunction.conjByMulEquiv g a ∈ A)
    (hker : A ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) :
    A ⊆ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy g χ) := by
  intro y hy
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  have hy' : ClassFunction.conjByMulEquiv g y ∈ A := hAinv y hy
  have hdeg : OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy g χ)
      = OddOrder.Peterfalvi.S03.characterDegree χ := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, OddOrder.Peterfalvi.S03.characterDegree_def]
    show (ClassFunction.conjBy g χ) 1 = χ 1
    rw [ClassFunction.conjBy_apply]
    refine congrArg χ (Subtype.ext ?_)
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
  show (ClassFunction.conjBy g χ) y
    = OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy g χ)
  rw [ClassFunction.conjBy_apply, hdeg]
  have hmem := hker hy'
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
  rw [← hmem]
  congr 1

/-- **`conjByMulEquiv`-invariance of a realized normal subgroup** (Peterfalvi (9.8.d) count
substrate).  If `N ⊴ K` (`K ⊴ G`) then the underlying set of `N` — as a `Set ↥K` — is invariant
under `conjByMulEquiv g` for *every* `g : G` (not merely `g ∈ K`): `conjByMulEquiv g a = g·a·g⁻¹`
lands back in `N` by normality of `N` in the ambient (here `N` is a subgroup of `K` that is itself
`G`-conjugation-stable via the realization `N ⊴ G`).  Instantiated at the (9.8.d) `HU`-normal
realized subgroups (`H₀`-realized, `W`-lifted, `U'`-realized, all `◁ HU`, all `≤ H·C_U(S₀)`), this
supplies the `hAinv` hypothesis of `subsetCharacterKernel_conjBy_of_invariant`, making each kernel
condition `HU`-conjugation-stable. -/
theorem conjByMulEquiv_invariant_of_normal {K : Subgroup G} [K.Normal]
    {N : Subgroup ↥K} (hN : ∀ (g : G) (a : ↥K), a ∈ N →
      (⟨g * (a : G) * g⁻¹, ‹K.Normal›.conj_mem (a : G) a.2 g⟩ : ↥K) ∈ N)
    (g : G) :
    ∀ a ∈ (N : Set ↥K), ClassFunction.conjByMulEquiv g a ∈ (N : Set ↥K) := by
  intro a ha
  rw [SetLike.mem_coe] at ha ⊢
  have hval : ClassFunction.conjByMulEquiv g a
      = (⟨g * (a : G) * g⁻¹, ‹K.Normal›.conj_mem (a : G) a.2 g⟩ : ↥K) :=
    Subtype.ext (by rw [ClassFunction.conjByMulEquiv_apply])
  rw [hval]
  exact hN g a ha

/-- **Pointwise kernel transport under conjugation** (`cfker_conjg`, Peterfalvi (9.8.d) (γ)
substrate).  For a class function `χ` on a normal subgroup `K ⊴ G` and `w : G`, an element
`n ∈ ↥K` lies in the kernel of the conjugate `χ^w` iff its `w`-conjugate `w·n·w⁻¹` (as an element
of `↥K`, `conjByMulEquiv w n`) lies in the kernel of `χ`:

`n ∈ Ker (χ^w) ↔ conjByMulEquiv w n ∈ Ker χ`.

Elementary: `(χ^w) n = χ (w·n·w⁻¹)` (`conjBy_apply`) and `characterDegree (χ^w) = characterDegree χ`
(conjugation fixes the value at `1`).  This is the *non-invariant* counterpart of
`subsetCharacterKernel_conjBy_of_invariant` — instead of assuming a `conjByMulEquiv w`-invariant set,
it tracks exactly where conjugation moves the kernel.  It is the genuinely-absent `cfker_conjg`
brick underlying the (9.8.d) `W₁`-injectivity (Coq `injXtheta`, `cfker_conjg`): a `W₁`-conjugate of
a family member's kernel is the kernel of the conjugate, so a summand `S₀ = H₁` moved into
`W = H₂…H_q` by a nontrivial `w₁ ∈ W₁` lands in the kernel, forcing the family member trivial on
`H̄` — the contradiction that pins `w₁ = 1`. -/
theorem mem_characterKernel_conjBy {K : Subgroup G} [K.Normal]
    (w : G) (χ : ClassFunction ↥K ℂ) (n : ↥K) :
    n ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy w χ)
      ↔ ClassFunction.conjByMulEquiv w n
        ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.mem_characterKernel]
  have hdeg : OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy w χ)
      = OddOrder.Peterfalvi.S03.characterDegree χ := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, OddOrder.Peterfalvi.S03.characterDegree_def]
    show (ClassFunction.conjBy w χ) 1 = χ 1
    rw [ClassFunction.conjBy_apply]
    refine congrArg χ (Subtype.ext ?_)
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
  rw [hdeg, ClassFunction.conjBy_apply]
  constructor
  · intro h; rw [← h]; congr 1
  · intro h; rw [← h]; congr 1

/-- **Subgroup-level kernel transport under conjugation** (`cfker_conjg` subset form, Peterfalvi
(9.8.d) (γ) substrate).  A subgroup `N ≤ ↥K` (`K ⊴ G`) is contained in the kernel of the conjugate
`χ^w` iff every `w`-conjugate `conjByMulEquiv w n` (`n ∈ N`) lies in the kernel of `χ`.  Immediate
from the pointwise `mem_characterKernel_conjBy`.  The form consumed by the (9.8.d) injectivity: to
show `H₁ = S₀ ⊆ Ker (ζ₂^{w₁})` it suffices that `w₁·S₀·w₁⁻¹` — a Clifford `W₁`-conjugate of `S₀`,
contained in `W = H₂…H_q` for `w₁ ≠ 1` — is in `Ker ζ₂` (which it is, `W ⊆ Ker ζ₂`). -/
theorem subsetCharacterKernel_conjBy_iff {K : Subgroup G} [K.Normal]
    (w : G) (χ : ClassFunction ↥K ℂ) (N : Subgroup ↥K) :
    (N : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy w χ)
      ↔ ∀ n ∈ N, ClassFunction.conjByMulEquiv w n
        ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  constructor
  · intro h n hn; exact (mem_characterKernel_conjBy w χ n).mp (h hn)
  · intro h n hn; exact (mem_characterKernel_conjBy w χ n).mpr (h n hn)

/-- **`induceHU χ = Ind_{HU}^M χ`** (unfold the wrapper).  `induceHU` is definitionally
`ClassFunction.induce (huSub data)` with an internally-chosen `Invertible` instance; that instance is
propositional (`Subsingleton`), so the wrapper equals the raw induction for any ambient instance.
Lets the `induceHU`-injectivity frame reuse the `induce_eq_induce_iff_conj` orbit machinery. -/
theorem induceHU_eq_induce [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ = ClassFunction.induce (huSub data) χ := by
  unfold induceHU
  convert rfl using 2
  exact Subsingleton.elim (α := Invertible (Nat.card ↥(huSub data) : ℂ)) _ _

/-- **`induceHU`-equality gives an `M`-conjugation of the sources** (Peterfalvi (9.8.d) (γ) frame).
If two irreducible `HU`-characters `χ, ψ` have equal `M`-inductions `Ind_{HU}^M`, then some
`w ∈ M` conjugates `ψ` to `χ` (`induce_eq_induce_iff_conj` at the `induceHU` wrapper level).  The
raw first step of the (9.8.d) injectivity: distinct inductions ⟺ distinct `M`-conjugacy orbits. -/
theorem induceHU_eq_imp_exists_conj [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (h : induceHU data (χ : ClassFunction ↥(huSub data) ℂ)
      = induceHU data (ψ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ w : ↥M, IrreducibleCharacter.conjBy w ψ = χ := by
  haveI := huSub_normal data
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ),
    induceHU_eq_induce data (ψ : ClassFunction ↥(huSub data) ℂ)] at h
  obtain ⟨w, hw⟩ := (induce_eq_induce_iff_conj ψ χ).mp h.symm
  exact ⟨w, hw⟩

/-- **`induceHU` injective on irreducibles when the conjugator lies in `HU`** (Peterfalvi (9.8.d)
(γ) reduction — the honest frame isolating the `W₁`-content).  Given a criterion `hcrit` that *any*
`M`-conjugation carrying `ψ` to `χ` must be by an element of `HU` (`w ∈ huSub`), the `M`-induction
map `induceHU` is injective at `{χ, ψ}`: an `HU`-conjugation of an `HU`-character is inner
(`conjBy_eq_self_of_mem`), so `χ = conjBy w ψ = ψ`.

This reduces (9.8.d) (γ) — `Ind_{HU}^M` injective on the `ζ_{θ₁,λ}`-family up to `W₁` — to the pure
group/kernel statement `hcrit`: two family members are non-`W₁`-conjugate.  In the Coq proof
(`injXtheta`, `PFsection9.v` L1233-1253) `hcrit` is exactly the Frobenius `Ū ⋊ W₁` +
`cfker`-under-`W₁`-conjugation argument: decompose `w = y·w₁` (`M = HU ⋊ W₁`), `conjBy y` inner, so
`conjBy w₁ ψ = χ`; then `W = H₂…H_q ⊆ Ker ψ,Ker χ` (family members trivial on the summand complement)
while a nontrivial `w₁` moves `S₀ = H₁` into `W` (Clifford permutation `H̄ = ⊕ S₀^{w}`), forcing
`H̄ ⊆ Ker χ` (via `mem_characterKernel_conjBy`) — contradicting `H ⊄ Ker χ`; hence `w₁ = 1`, `w ∈ HU`.
The `cfker`-conjugation half (`mem_characterKernel_conjBy` / `subsetCharacterKernel_conjBy_iff`),
the `W = H₂…H_q ⊆ Ker` propagation (core (1), `hcuZetaPair_summandComplement_subset_ker`), and the
full `hcrit` reduction (`hcrit_of_summand_orbit`) are now all landed; the sole residual is the
(9.7.a) `W₁`-free-orbit datum `horbit` (`S₀^{w₁} ⊆ W`), absent from `CliffordCaseAData` (issue 1018). -/
theorem induceHU_inj_of_conj_mem_huSub [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (hcrit : ∀ w : ↥M, IrreducibleCharacter.conjBy w ψ = χ → (w : ↥M) ∈ huSub data)
    (h : induceHU data (χ : ClassFunction ↥(huSub data) ℂ)
      = induceHU data (ψ : ClassFunction ↥(huSub data) ℂ)) :
    χ = ψ := by
  haveI := huSub_normal data
  obtain ⟨w, hw⟩ := induceHU_eq_imp_exists_conj data h
  have hwHU : (w : ↥M) ∈ huSub data := hcrit w hw
  have hfix : IrreducibleCharacter.conjBy w ψ = ψ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    exact ClassFunction.conjBy_eq_self_of_mem hwHU (ψ : ClassFunction ↥(huSub data) ℂ)
  rw [← hw, hfix]

/-- **The `hcrit` of (9.8.d) (γ) from the Clifford data** (Peterfalvi (9.8.d), Coq `injXtheta`
`PFsection9.v` L1233-1253).  For two family members `ζ₁, ζ₂` with:
* `hS0notker`: `ζ₁`'s seed is nontrivial on the realized generator summand `S₀ = H₁`
  (`realized S₀ ⊄ Ker ζ₁` — true for a member, whose `θ₁ ≠ 1` on `S₀`);
* `hkerW₂`: `ζ₂` is trivial on the realized summand-complement `W = H₂…H_q` (core (1),
  `hcuZetaPair_summandComplement_subset_ker`);
* `horbit`: the (9.7.a) `W₁`-free-orbit datum — a nontrivial `w₁ ∈ W₁` moves `realized S₀` into
  `realized W`;

any `M`-conjugation `conjBy w ζ₂ = ζ₁` has `w ∈ HU`.  The honest reduction of `hcrit`:

* decompose `w = a·w₁` with `a ∈ HU`, `w₁ ∈ W₁` (`M = HU ⋊ W₁`, `data.typeP.M_complement`);
* `conjBy a` is inner (`a ∈ HU`, `conjBy_eq_self_of_mem`), so `conjBy w₁ ζ₂ = ζ₁`;
* if `w₁ ≠ 1`: for `s ∈ realized S₀`, `s ∈ Ker ζ₁ = Ker (conjBy w₁ ζ₂) ⟺ w₁·s·w₁⁻¹ ∈ Ker ζ₂`
  (`mem_characterKernel_conjBy`, `cfker_conjg`), and `w₁·s·w₁⁻¹ ∈ realized W` (`horbit`) `⊆ Ker ζ₂`
  (`hkerW₂`); so `realized S₀ ⊆ Ker ζ₁`, contradicting `hS0notker`;
* so `w₁ = 1`, `w = a ∈ HU`.

This is the exact `injXtheta` logic (`H₁ ⊆ Ker (χ^w)` for `w ∈ W₁#`, using `H₁^w ⊆ H₂…H_q ⊆ Ker`).
The `horbit` datum — a nontrivial `w₁ ∈ W₁` moving `S₀` into `W` — is the Peterfalvi (9.7.a)
free-`W₁`-orbit structure `H̄ = ⊕_{w ∈ W₁} S₀^w`; it is **reconstructed** from the stored `S₀`
(order `p`, `U`-invariant) and `chief.quotient_chiefFactor` (`U W₁`-irreducibility) by
`caseA_wOrbit_horbit` (with `W = caseA_wComplement caseA`), so the unconditional `hcrit`
(`horbit` discharged) is `caseA_hcrit_of_member`.  (`CliffordCaseAData` carries the summands only as
an *arbitrary* `U`-supindep family (`clifford_caseA_data`, `orbitRep : Fin q → U ⊔ W₁` from a choice
function), *not* the `W₁`-conjugate orbit; the orbit is re-derived rather than read off the carrier —
no structure enrichment is needed, see issue 1018.) -/
theorem hcrit_of_summand_orbit [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    {chief : ChiefFactorData data} [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {S₀ W : Subgroup (↥data.H ⧸ chief.N)}
    {ζ₁ ζ₂ : IrreducibleCharacter ↥(huSub data)}
    (hS0notker : ¬ (((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₁ : ClassFunction ↥(huSub data) ℂ))
    (hkerW₂ : (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₂ : ClassFunction ↥(huSub data) ℂ))
    (horbit : ∀ w₁ : ↥M, ((w₁ : ↥M) : G) ∈ data.typeP.W1 → w₁ ≠ 1 →
      ∀ s ∈ ((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data),
        ClassFunction.conjByMulEquiv (H := huSub data) (w₁ : ↥M) s
          ∈ ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)) :
    ∀ w : ↥M, IrreducibleCharacter.conjBy w ζ₂ = ζ₁ → (w : ↥M) ∈ huSub data := by
  haveI := huSub_normal data
  intro w hw
  -- decompose `w = a·w₁`, `a ∈ HU`, `w₁ ∈ W₁` (`M = HU ⋊ W₁`).
  have hcompl : Subgroup.IsComplement' (huSub data) (data.typeP.W1.subgroupOf M) := by
    rw [huSub_eq_derivedInG_subgroupOf]; exact data.typeP.M_complement
  obtain ⟨⟨a, w₁⟩, hprod⟩ := (hcompl.existsUnique w).exists
  simp only at hprod
  -- `conjBy w ζ₂ = conjBy w₁ ζ₂` (the `HU`-part `a` is inner).
  have hconjw₁ : IrreducibleCharacter.conjBy (w₁ : ↥M) ζ₂ = ζ₁ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    have hstep : ClassFunction.conjBy ((a : ↥M) * (w₁ : ↥M)) (ζ₂ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) := by
      rw [ClassFunction.conjBy_mul, ClassFunction.conjBy_eq_self_of_mem a.2]
    rw [← hstep, hprod, ← IrreducibleCharacter.coe_conjBy, hw]
  -- suffices `w₁ = 1`, since then `w = a·1 = a ∈ HU`.
  suffices hw₁ : (w₁ : ↥M) = 1 by
    have : w = (a : ↥M) := by rw [← hprod, hw₁, mul_one]
    rw [this]; exact a.2
  by_contra hw₁ne
  -- if `w₁ ≠ 1`: realized `S₀ ⊆ Ker ζ₁`, contradicting `hS0notker` (`θ₁ ≠ 1` on `S₀`).
  apply hS0notker
  intro s hs
  -- `ζ₁ = conjBy w₁ ζ₂`, so `s ∈ Ker ζ₁ ⟺ w₁·s·w₁⁻¹ ∈ Ker ζ₂` (`cfker_conjg`).
  have hζ₁coe : (ζ₁ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) := by
    rw [← IrreducibleCharacter.coe_conjBy, hconjw₁]
  rw [SetLike.mem_coe] at hs
  rw [hζ₁coe]
  refine (mem_characterKernel_conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) s).mpr ?_
  -- `w₁·s·w₁⁻¹ ∈ realized W` (core (2), `horbit`) `⊆ Ker ζ₂` (core (1), `hkerW₂`).
  exact hkerW₂ (horbit w₁ w₁.2 hw₁ne s hs)

/-- **(9.8.d) (γ) `hcrit`, `horbit` discharged** (Peterfalvi (9.8.d), Coq `injXtheta`).  The
unconditional form of `hcrit_of_summand_orbit` with the summand-complement fixed to the genuine
`(9.7.a)` free-`W₁`-orbit complement `W = caseA_wComplement caseA = ⨆_{w∈W₁#} S₀^w` and its `horbit`
datum supplied by the reconstructed `caseA_wOrbit_horbit` (a nontrivial `w₁ ∈ W₁` moves the realized
`S₀` into the realized `W`).  Thus the `hcrit` for the (γ) `W₁`-injectivity now needs only the two
character-kernel facts that hold for a family member `ζ₁, ζ₂` (`realized S₀ ⊄ Ker ζ₁`,
`realized W ⊆ Ker ζ₂`); the `(9.7.a)` prerequisite is fully discharged (no `horbit` hypothesis
remains).  Combined with `induceHU_inj_of_conj_mem_huSub` this closes (γ) of Peterfalvi (9.8.d) once
`hkerW₂` is instantiated at `W = caseA_wComplement caseA` (via `hcuZetaPair_summandComplement_subset_ker`
with `θ|_W = 1`, which holds since a member's seed `θ₁ ∈ Irr(H̄/W)`). -/
theorem caseA_hcrit_of_member [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {ζ₁ ζ₂ : IrreducibleCharacter ↥(huSub data)}
    (hS0notker : ¬ (((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₁ : ClassFunction ↥(huSub data) ℂ))
    (hkerW₂ : (((caseA_realizedComplement chief (caseA_wComplement caseA)).subgroupOf M).subgroupOf
          (huSub data) : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₂ : ClassFunction ↥(huSub data) ℂ)) :
    ∀ w : ↥M, IrreducibleCharacter.conjBy w ζ₂ = ζ₁ → (w : ↥M) ∈ huSub data :=
  hcrit_of_summand_orbit data hS0notker hkerW₂ (caseA_wOrbit_horbit caseA)

/-- **Homs trivial on `W` biject with homs of the quotient `H̄/W`** (Peterfalvi (9.8.d) (β) substrate).
A hom `θ : H̄ →* ℂˣ` with `W ≤ Ker θ` descends uniquely to `H̄/W →* ℂˣ` (`QuotientGroup.lift`,
inverse `comp (mk' W)`), giving `|{θ | W ≤ Ker θ}| = |H̄/W →* ℂˣ|`.  The counting bridge for the
`θ`-numerator of the (9.8.d) domain count. -/
theorem card_hom_triv_W_eq_card_quotient [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (W : Subgroup (↥data.H ⧸ chief.N)) [W.Normal] :
    Nat.card {θ : (↥data.H ⧸ chief.N) →* ℂˣ // W ≤ θ.ker}
      = Nat.card ((↥data.H ⧸ chief.N) ⧸ W →* ℂˣ) := by
  refine Nat.card_congr
    { toFun := fun θ => QuotientGroup.lift W θ.1
        (fun x hx => MonoidHom.mem_ker.mp (θ.2 hx))
      invFun := fun ρ => ⟨ρ.comp (QuotientGroup.mk' W), fun x hx => ?_⟩
      left_inv := fun θ => ?_
      right_inv := fun ρ => ?_ }
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  · apply Subtype.ext; apply MonoidHom.ext; intro x; dsimp only
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  · apply MonoidHom.ext; intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W x
    dsimp only
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply]

open scoped Classical in
/-- **θ-count** (Peterfalvi (9.8.d) (β) numerator): the number of homs `θ : H̄ →* ℂˣ` *trivial on the
summand complement* `W` and *nontrivial on `S₀`* equals `p − 1`.

Since `S₀ ⊔ W = ⊤`, `S₀ ⊓ W = ⊥` with `|S₀| = p`, the quotient `H̄/W ≅ S₀` (via the complement,
`IsComplement'.QuotientMulEquiv`) has order `p`.  Homs trivial on `W` are exactly homs of `H̄/W`
(`card_hom_triv_W_eq_card_quotient`), numbering `|H̄/W| = p` (Pontryagin,
`card_monoidHom_of_hasEnoughRootsOfUnity`); among them a hom is nontrivial on `S₀` iff it is nonzero
(a `W`-trivial, `S₀`-trivial hom is trivial on `S₀ ⊔ W = ⊤`, hence `= 1`), removing the single
trivial hom: `p − 1`.  This is the `(p-1)` factor of the (9.8.d) domain count `(p-1)·[C_U(S₀):U']`,
the `θ₁`-parameter count for the pair family `ψ_{θ₁,λ}` (`θ₁ ∈ Irr(H̄/W) \ {1}`). -/
theorem card_theta_triv_W_nontriv_S0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    {W : Subgroup (↥data.H ⧸ chief.N)} [W.Normal]
    (hinf : caseA.S0 ⊓ W = ⊥) (hsup : caseA.S0 ⊔ W = ⊤)
    (hS0card : Nat.card ↥caseA.S0 = chief.p) :
    (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
        W ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1).card = chief.p - 1 := by
  letI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  letI : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) :=
    { (inferInstance : Group ((↥data.H ⧸ chief.N) ⧸ W)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W b
        rw [← map_mul, ← map_mul, chief.quotient_elementaryAbelian.1 x y] }
  haveI : NeZero (Monoid.exponent ((↥data.H ⧸ chief.N) ⧸ W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  -- `#{θ | W ≤ ker θ} = |H̄/W →* ℂˣ| = |H̄/W| = p`.
  have hcardWhom : (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => W ≤ θ.ker).card
      = chief.p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      card_hom_triv_W_eq_card_quotient W,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((↥data.H ⧸ chief.N) ⧸ W) ℂ]
    letI : Fintype (↥data.H ⧸ chief.N) := Fintype.ofFinite _
    have hcompl : Subgroup.IsComplement' caseA.S0 W :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    rw [← hS0card]
    exact Nat.card_congr hcompl.QuotientMulEquiv.toEquiv
  -- The set is `{θ | W ≤ ker θ} \ {1}` (a `W`-trivial, `S₀`-trivial hom is trivial on `⊤`).
  have hkey : (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
        W ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1)
      = (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => W ≤ θ.ker).erase 1 := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hW, hS0⟩
      exact ⟨fun h1 => hS0 (by rw [h1]; ext x; simp), hW⟩
    · rintro ⟨hne, hW⟩
      refine ⟨hW, fun hS0 => hne ?_⟩
      have hkerS0 : caseA.S0 ≤ θ.ker := fun x hx => by
        rw [MonoidHom.mem_ker]; simpa using DFunLike.congr_fun hS0 ⟨x, hx⟩
      have hker_top : (⊤ : Subgroup (↥data.H ⧸ chief.N)) ≤ θ.ker := by
        rw [← hsup]; exact sup_le hkerS0 hW
      refine MonoidHom.ext (fun x => ?_)
      have hxk : x ∈ θ.ker := hker_top (Subgroup.mem_top x)
      rw [MonoidHom.mem_ker] at hxk
      rw [hxk, MonoidHom.one_apply]
  rw [hkey, Finset.card_erase_of_mem, hcardWhom]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [show ((1 : (↥data.H ⧸ chief.N) →* ℂˣ)).ker = ⊤ from MonoidHom.ker_one]
  exact le_top

/-- **step 5 (g): a `hcHom`-kernel-trivial `HC`-character is `hcPsi θbar`** (Peterfalvi (9.8.c)).
An irreducible `HC`-character `ψ` trivial on `Ker hcHom` (`= H₀C`) inflates from `H̄ = HC/H₀C`
(`exists_compHom_eq_of_subset_characterKernel`, `hcHom` surjective); since `H̄` is abelian the
inflation is *linear*, so `ψ = hcPsi θbar` for a hom-form seed `θbar : H̄ →* ℂˣ`.  This collapses the
step-5 (e)(linear)/(f)(trivial)/(g)(identification) chain: the reducible `ξ`'s `HC`-constituent `ψ'`,
being trivial on `H₀C` (from `ξ ∈ 𝒳(H₀C)`), is automatically linear and of `hcPsi` form. -/
theorem exists_hcPsi_eq_of_hcHom_ker_subset [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (ψ : IrreducibleCharacter
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
    (hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction _ ℂ)) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ,
      (ψ : ClassFunction _ ℂ) = (hcPsi chief θbar : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  obtain ⟨θbar_irr, heq⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) ψ hker
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbarval⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θbar_irr.isIrreducible
  refine ⟨θbar, ?_⟩
  have hθbar_eq : (θbar_irr : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
    ext g
    rw [linearIrreducibleCharacter_apply, hθbarval]
  rw [← heq, hθbar_eq, ClassFunction.compHom_linearIrreducibleCharacter]
  rfl

/-- **`hcPsi θ` restricts on `hInHu` to the seed inflation `θ₀`** (`subgroupOf` form).  Restricting
the `HC`-linear character `hcPsi θ` to `hInHu.subgroupOf HC` equals the inflation
`θ₀ = linearIrr(θ ∘ mk'_N ∘ hInHuEquivH)` transported along `subgroupOfEquivOfLe`.  This is the
`subgroupOf`-form of `hcPsi_apply_inclusion`, matching the intermediate-character shape produced by
`exists_liesOver_intermediate` in the (9.8.c) Clifford-correspondence step 5.  Feeds the seed
identification `θbar'' = θbar` (`Res ψ' = θ₀'` at the intermediate constituent). -/
theorem hcPsi_restrict_hInHu_subgroupOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ClassFunction.restrict ((hInHu data).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (hcPsi chief θ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data))).toMonoidHom
          (linearIrreducibleCharacter (θ.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
  ext x
  rw [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  set h := (Subgroup.subgroupOfEquivOfLe (le_sup_left :
    hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data))) x with hh
  have hxeq : (x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))
      = Subgroup.inclusion (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_inclusion, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [hxeq, hcPsi_apply_inclusion chief θ h]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

/-- **A lies-over character whose restriction is irreducible identifies the constituent** (general
Clifford orthonormality): if the irreducible `χ` of `Γ` lies over `θ ∈ Irr K` and `Res_K χ` equals a
*single* irreducible character `η ∈ Irr K`, then `η = θ`.  `⟨Res_K χ, θ⟩ ≠ 0` becomes `⟨η, θ⟩ ≠ 0`,
which forces `η = θ` (distinct irreducibles orthogonal, `irreducibleCharacter_inner_eq_ite`).  Used to
identify the intermediate constituent's seed in the (9.8.c) step-5 assembly (a linear `ψ'` restricts
to a single character, pinning its inflation seed). -/
theorem eq_of_liesOver_of_restrict_eq_irr {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {K : Subgroup Γ} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    {χ : IrreducibleCharacter Γ} {θ η : IrreducibleCharacter ↥K}
    (hover : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ θ)
    (hres : ClassFunction.restrict K (χ : ClassFunction Γ ℂ) = (η : ClassFunction ↥K ℂ)) :
    η = θ := by
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def, hres] at hover
  by_contra h
  exact hover (by rw [OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite η θ, if_neg h])

/-- **The seed is determined by the `hInHu`-restriction of `hcPsi`**: if `hcPsi θ₁` restricted to
`hInHu.subgroupOf HC` equals the transported inflation of `θ₂`, then `θ₁ = θ₂`.  By
`hcPsi_restrict_hInHu_subgroupOf` the left side is the transported inflation of `θ₁`, so the two
inflations agree; the descent hom `mk'_N ∘ hInHuEquivH ∘ subgroupOfEquivOfLe` is surjective, so
`θ₁ = θ₂` pointwise.  This is the (g′) identification of the (9.8.c) step-5 assembly: the intermediate
constituent `ψ' = hcPsi θbar''` lying over `θ₀ = infl θbar` forces `θbar'' = θbar`. -/
theorem hcPsi_seed_eq_of_restrict_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ₁ θ₂ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (h : ClassFunction.restrict ((hInHu data).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (hcPsi chief θ₁ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data))).toMonoidHom
          (linearIrreducibleCharacter (θ₂.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) :
    θ₁ = θ₂ := by
  have key := (hcPsi_restrict_hInHu_subgroupOf chief θ₁).symm.trans h
  have hsurj : Function.Surjective (fun z => (QuotientGroup.mk' chief.N)
      ((hInHuEquivH data) ((Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) z))) :=
    (QuotientGroup.mk'_surjective chief.N).comp
      ((hInHuEquivH data).surjective.comp (Subgroup.subgroupOfEquivOfLe _).surjective)
  refine MonoidHom.ext fun w => ?_
  obtain ⟨y, hy⟩ := hsurj w
  have hval : (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data))).toMonoidHom
        (linearIrreducibleCharacter (θ₁.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) y
      = (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data))).toMonoidHom
        (linearIrreducibleCharacter (θ₂.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) y := by rw [key]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply] at hval
  simp only [] at hy
  rw [hy] at hval
  exact Units.val_injective hval

set_option maxHeartbeats 1000000 in
/-- **step 5 (assembly): the reducible `M`-fixed `ζ` is `Ind_{HC}^{HU}(hcPsi θbar)`** (Peterfalvi
(9.8.c), `Xmu` surjectivity).  A reducible (`M`-fixed) `ζ ∈ 𝒳(H₀C)` lying over the seed inflation
`θ₀` (`hlo`; the seed `θbar` is regular by `caseA_reducible_theta_regular`, `≠ 1` by `hnt`) equals the
(9.8.c) construction `Ind_{HC}^{HU}(hcPsi θbar)`.

Chain: lies-over transitivity (`exists_liesOver_intermediate`) yields an `HC`-constituent `ψ'` with
`ζ` over `ψ'` and `ψ'` over `θ₀'`; `ζ ∈ 𝒳(H₀C)` (`hH0C`, trivial on `H₀C = Ker hcHom`) descends
(`liesOver_mem_characterKernel`) to `Ker hcHom ⊆ Ker ψ'`, so `ψ' = hcPsi θbar''`
(`exists_hcPsi_eq_of_hcHom_ker_subset`; `H̄` abelian ⟹ automatically linear).  Its restriction to
`hInHu` is `θ₀''` (`hcPsi_restrict_hInHu_subgroupOf`), a single irreducible (linear), so `ψ'` over
`θ₀'` forces `θ₀'' = θ₀'` (`eq_of_liesOver_of_restrict_eq_irr`), i.e. `θbar'' = θbar`
(`hcPsi_seed_eq_of_restrict_eq`).  Then `ζ` over `hcPsi θbar` and `Ind_{HC}(hcPsi θbar)` irreducible
(`hcZeta_irreducible`, foundation `caseA_reducible_inflation_inertia_eq`) give
`ζ = Ind_{HC}(hcPsi θbar)` (`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`).  This is the
surjectivity input to `|Xmu| = p-1`. -/
theorem caseA_reducible_eq_hcZeta [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1)
    (hH0C : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ : ClassFunction ↥(huSub data) ℂ)) :
    (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θbar) := by
  classical
  haveI : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  letI : Fintype ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- foundation `I_{HU}(θ₀) = HC`, hence `Ind_{HC}(hcPsi θbar)` irreducible.
  have hθ₀ := caseA_reducible_inflation_inertia_eq caseA θbar ζ hlo hMfix hnt
  have hind := hcZeta_irreducible chief θbar hθ₀
  -- intermediate `HC`-constituent `ψ'`.
  obtain ⟨ψ', hζψ', hψ'θ₀⟩ := exists_liesOver_intermediate
    (le_sup_left : hInHu data ≤ hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ζ
    (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom))) hlo
  -- (f) `Ker hcHom ⊆ Ker ψ'` from `ζ` trivial on `H₀C`.
  have hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ' : ClassFunction _ ℂ) := by
    intro g hg
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg
    refine liesOver_mem_characterKernel hζψ' (hH0C ?_)
    rw [SetLike.mem_coe, ← Subgroup.mem_subgroupOf]
    simp only [hcHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hg
    rwa [map_eq_one_iff _ (hcQuotientEquivHbar chief).injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
  -- (g) `ψ' = hcPsi θbar''`.
  obtain ⟨θbar'', hψ'eq⟩ := exists_hcPsi_eq_of_hcHom_ker_subset chief ψ' hker
  -- (g′) `θbar'' = θbar` via the restriction identity + orthonormality.
  set η : IrreducibleCharacter ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))).toMonoidHom
      (linearIrreducibleCharacter (θbar''.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ),
      (linearIrreducibleCharacter (θbar''.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom))).isIrreducible.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe _).surjective⟩ with hηdef
  have hres_eq : ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (ψ' : ClassFunction _ ℂ) = (η : ClassFunction _ ℂ) := by
    rw [hψ'eq, hcPsi_restrict_hInHu_subgroupOf chief θbar'']
  have hη := eq_of_liesOver_of_restrict_eq_irr hψ'θ₀ hres_eq
  have hθbar : θbar'' = θbar := by
    refine hcPsi_seed_eq_of_restrict_eq chief θbar'' θbar ?_
    rw [hcPsi_restrict_hInHu_subgroupOf chief θbar'']
    exact congrArg IrreducibleCharacter.toClassFunction hη
  -- conclude `ζ = Ind_{HC}(hcPsi θbar)`.
  refine coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce ζ (hcPsi chief θbar) hind ?_
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def]
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at hζψ'
  rwa [hψ'eq, hθbar] at hζψ'

set_option maxHeartbeats 1000000 in
/-- **step 5 consequence (caseA): a reducible `𝒮(H₀)`-member is `Ind_{HU}^M(Ind_{HC}(hcPsi θbar))` for
a regular seed `θbar`.**  A reducible `φ = Ind_{HU}^M χ ∈ 𝒮(H₀)` has `M`-fixed source `χ`
(`inertia_eq_top_of_induceHU_not_irreducible`); the case-agnostic cardinality argument
`reducible_mem_sOf_H0C` places `φ ∈ 𝒮(H₀C)`, and `Ind`-injectivity on reducibles
(`caseA_induceHU_inj_of_reducible`) upgrades `χ`'s kernel to `H₀C ⊆ Ker χ` (`χ ∈ 𝒳(H₀C)`).  The seed
`θbar` (`exists_hom_constituent_of_mem_xiSet_H0`, nontrivial) is regular by the `M`-fixedness
(`caseA_reducible_theta_regular`), so `caseA_reducible_eq_hcZeta` identifies
`χ = Ind_{HC}(hcPsi θbar)`.  The shared extraction behind the (9.8.b) degree
(`caseA_reducible_induceHU_apply_one_eq_qu`) and the (9.8.c) `Xmu`-surjectivity. -/
theorem caseA_reducible_source_eq_hcZeta [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ, (∀ i, θbar.comp (caseA.Hpart i).subtype ≠ 1) ∧
      φ = induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θbar)) := by
  classical
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    hcInHu_realized_normal chief
  obtain ⟨χ, hχ, rfl⟩ := hφ
  have hind_red : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)) := hred
  have hMfix := inertia_eq_top_of_induceHU_not_irreducible data χ hind_red
  obtain ⟨θbar, hnt, hlo⟩ := exists_hom_constituent_of_mem_xiSet_H0 hχ.1 hχ.2
  -- C-kernel: `χ ∈ 𝒳(H₀C)` via cardinality membership + `Ind`-injectivity.
  obtain ⟨χ', hχ'C, hχ'eq⟩ := reducible_mem_sOf_H0C hG chars
    (induceHU data (χ : ClassFunction ↥(huSub data) ℂ)) ⟨χ, hχ, rfl⟩ hred
  have hχ'χ : χ' = χ := caseA_induceHU_inj_of_reducible data hind_red hχ'eq
  have hH0C := (hχ'χ ▸ hχ'C : χ ∈ xiOf data (chief.H0 ⊔ chars.C)).2
  refine ⟨θbar, caseA_reducible_theta_regular caseA θbar χ hlo hMfix hnt, ?_⟩
  exact congrArg (induceHU data) (caseA_reducible_eq_hcZeta caseA θbar χ hlo hMfix hnt hH0C)

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Peterfalvi (13.3.a) core, case (a)** (the (9.8.b)-side `isIndHC`): in Clifford case (a),
every *reducible* member of `𝒮(H₀)` is induced from a linear character of `HC` at the
`M`-level.  `caseA_reducible_source_eq_hcZeta` identifies the source as
`Ind_{HC}(hcPsi θbar)` (regular seed), and the stages-flattening
(`isIndHC_of_source_eq_induce_hcPsi`) concludes. -/
theorem caseA_reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
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
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  obtain ⟨θbar, hreg, hφeq⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφ hred
  have hreg' : ∀ i, ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro i
    obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θbar i).mp (hreg i)
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    simpa using hne
  have hθ₀ := inertia_eq_hcInHu_caseA data chief caseA hreg'
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ := isIndHC_of_source_eq_induce_hcPsi
    (ζ' := ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θbar), hcZeta_irreducible chief θbar hθ₀⟩) (θbar := θbar) rfl
  exact ⟨ψ, hψirr, hψone, hφeq.trans hψeq⟩

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **Peterfalvi (13.3.a) core, case-agnostic (Coq `isIndHC`)**: every *reducible* member of
`𝒮(H₀)` is induced from a linear character of `HC` at the `M`-level — in either Clifford case
(`clifford_dichotomy`; case (a) = `caseA_reducible_sOf_H0_isIndHC` via (9.8.b), case (b) =
`caseB_reducible_sOf_H0_isIndHC` via (9.9.b)).  In the §13 `S`-instantiation `HC = PC`, so
this is exactly (13.3.a)'s "`μ_j` is induced from a linear character of `PC`". -/
theorem reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
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
  rcases clifford_dichotomy hG chars with hA | hB
  · obtain ⟨caseA⟩ := hA
    exact caseA_reducible_sOf_H0_isIndHC hG caseA hφ hred
  · obtain ⟨caseB⟩ := hB
    exact caseB_reducible_sOf_H0_isIndHC hG chars caseB hφ hred

/-- **step 5 consequence (9.8.b degree, caseA): a reducible `𝒮(H₀)`-member has degree `qu`.**  By
`caseA_reducible_source_eq_hcZeta` the reducible `φ = Ind_{HU}^M(Ind_{HC}(hcPsi θbar))`, whose degree
is `q·u` (`hcZeta_induceHU_apply_one`).  The degree half of `caseA_character_counts` conjunct (b). -/
theorem caseA_reducible_induceHU_apply_one_eq_qu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    φ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨θbar, _, rfl⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφ hred
  exact hcZeta_induceHU_apply_one chars θbar

/-- **A regular seed's inflation `θ₀` has `HU`-inertia `HC`** (caseA).  Converts the hom-form
regularity (`θ` nontrivial on each Clifford summand `Hpart i`) to `inertia_eq_hcInHu_caseA`'s
pointwise form via `comp_subtype_ne_one_iff_exists`.  The direct-seed analogue of
`caseA_reducible_inflation_inertia_eq` (which routes through `caseA_reducible_theta_regular`);
supplies the `hθ₀` of `hcZeta_irreducible` / `hcZeta_induceHU_mem_sOf` for `Xθ`-members. -/
theorem caseA_regular_inflation_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hreg : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)] :
    ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_caseA data chief caseA (fun i => by
    obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θ i).mp (hreg i)
    exact ⟨x, hx, by
      rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one]
      simpa using hne⟩)

/-- **A regular seed's `Ind_{HC}(hcPsi θ)` is irreducible** (caseA `Xθ`-member irreducibility).  The
inflation `θ₀` has `HU`-inertia `HC` (`caseA_regular_inflation_inertia_eq`), so
`Ind_{HC}^{HU}(hcPsi θ)` is irreducible (`hcZeta_irreducible`).  Bundles every `Xθ`-member as an
`IrreducibleCharacter`, the input to the (9.8.c) `|Xmu| = p-1` bijection. -/
theorem caseA_hcZeta_irreducible_of_regular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hreg : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    IsIrreducibleCharacter (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ)) :=
  hcZeta_irreducible chief θ (caseA_regular_inflation_inertia_eq caseA θ hreg)

set_option linter.style.openClassical false in
open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **|Xmu| = p-1** (Peterfalvi (9.8.c), the reducible-inducing regular seeds).  `Xmu` = the
`Xθ`-members `ζ = Ind_{HC}(hcPsi θ)` (regular `θ`) whose `M`-induction `Ind_{HU}^M ζ` is *reducible*.
The map `ζ ↦ Ind_{HU}^M ζ` is a bijection `Xmu ≃ {reducible 𝒮(H₀)-members}`: injective on reducibles
(`caseA_induceHU_inj_of_reducible`) and surjective (every reducible `𝒮(H₀)`-member is
`Ind_{HU}^M(Ind_{HC}(hcPsi θbar))` for a regular seed, `caseA_reducible_source_eq_hcZeta`), so
`|Xmu| = |{reducibles}| = p-1` (`reducible_count_sOf_H0`).  The `|Xmu|` half of the (9.8.c) parity
dichotomy `exists_regular_not_reducible_of_odd`. -/
theorem caseA_Xmu_card_eq [Finite G] {M : Subgroup G}
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
    (((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
          ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).filter fun ζ =>
        ¬ IsIrreducibleCharacter (induceHU data ζ)).card
      = chief.p - 1 := by
  classical
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  -- `Ind_{HU}^M` is injective on `Xmu` (its members induce reducibly).
  have hinj : Set.InjOn (induceHU data) ↑Xmu := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    rw [Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image] at hζ₁ hζ₂
    obtain ⟨⟨θ₁, hθ₁, rfl⟩, hred₁⟩ := hζ₁
    obtain ⟨⟨θ₂, hθ₂, rfl⟩, _⟩ := hζ₂
    have hirr₁ := caseA_hcZeta_irreducible_of_regular caseA θ₁ (Finset.mem_filter.mp hθ₁).2
    have hirr₂ := caseA_hcZeta_irreducible_of_regular caseA θ₂ (Finset.mem_filter.mp hθ₂).2
    have hχ := caseA_induceHU_inj_of_reducible data (χ := ⟨_, hirr₁⟩) (ψ := ⟨_, hirr₂⟩) hred₁ heq
    exact congrArg IrreducibleCharacter.toClassFunction hχ.symm
  -- `Ind_{HU}^M '' Xmu = {reducible 𝒮(H₀)-members}`.
  have himg : induceHU data '' ↑Xmu = {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ} := by
    ext φ
    simp only [Set.mem_image, Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨⟨θ, hθ, rfl⟩, hζred⟩, rfl⟩
      have hreg := (Finset.mem_filter.mp hθ).2
      have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
      exact ⟨sOf_antitone data le_sup_left
        (hcZeta_induceHU_mem_sOf chars θ hnt (caseA_regular_inflation_inertia_eq caseA θ hreg)),
        hζred⟩
    · rintro ⟨hφS, hφred⟩
      obtain ⟨θbar, hreg, rfl⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφS hφred
      exact ⟨_, ⟨⟨θbar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreg⟩, rfl⟩, hφred⟩, rfl⟩
  rw [← Set.ncard_coe_finset Xmu, ← Set.ncard_image_of_injOn hinj, himg,
    reducible_count_sOf_H0 hG chief]

set_option linter.style.openClassical false in
open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **Peterfalvi (9.8.c): `𝒮(H₀C)` contains an irreducible character of degree `qu`.**  The parity
dichotomy `exists_regular_not_reducible_of_odd` applied to `X = Xθ` (`u·|Xθ| = (p-1)^q` by
`oXtheta_count`, `p-1` even as `p ∤ |G|` is odd, `u` odd by `u_odd`) and its `p-1`-element subfamily
`Xmu` (`caseA_Xmu_card_eq`) yields a regular seed's `ζ = Ind_{HC}(hcPsi θ)` outside `Xmu`, i.e. with
`Ind_{HU}^M ζ` *irreducible*.  That `Ind_{HU}^M ζ` is the required member: in `𝒮(H₀C)`
(`hcZeta_induceHU_mem_sOf`), irreducible, of degree `q·u` (`hcZeta_induceHU_apply_one`). -/
theorem caseA_exists_irreducible_sOf_H0C [Finite G] {M : Subgroup G}
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
    ∃ χ ∈ sOf data (chief.H0 ⊔ chars.C), IsIrreducibleCharacter χ ∧
      χ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  -- `p ∣ |G|` (odd), so `p` is odd and `p-1` even.
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
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  -- a regular seed inducing irreducibly (`ζ ∈ Xθ \ Xmu`).
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
  have hirr : IsIrreducibleCharacter (induceHU data (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ).toClassFunction)) := by
    by_contra h
    refine hζn ?_
    simp only [Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image]
    exact ⟨⟨θ, hθ, rfl⟩, h⟩
  exact ⟨_, hcZeta_induceHU_mem_sOf chars θ hnt (caseA_regular_inflation_inertia_eq caseA θ hreg),
    hirr, hcZeta_induceHU_apply_one chars θ⟩

end OddOrder.Peterfalvi.S11
