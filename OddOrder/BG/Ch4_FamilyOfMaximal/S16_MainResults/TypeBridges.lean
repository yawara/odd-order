import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TheoremsAE

/-!
# BG Proposition 16.1 forward bridges — shared type data の構成

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S16
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## Proposition 16.1 forward bridges: constructing the shared type data -/

/-- The pointwise `MulAut`-action distributes over `sSup` of subgroups (it is `Subgroup.map`, a
left adjoint, so it preserves arbitrary joins). -/
private theorem mulAut_smul_sSup (a : MulAut G) (T : Set (Subgroup G)) :
    a • sSup T = ⨆ S ∈ T, a • S := by
  rw [Subgroup.pointwise_smul_def]
  exact (Subgroup.gc_map_comap _).l_sSup

/-- Conjugation by `u` carries `C_G(x)` to `C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizer_singleton (u x : G) :
    MulAut.conj u • Subgroup.centralizer ({x} : Set G)
      = Subgroup.centralizer ({u * x * u⁻¹} : Set G) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hsmul : ((MulAut.conj u)⁻¹ • g : G) = u⁻¹ * g * u := by
    rw [← map_inv]; simp [MulAut.smul_def, MulAut.conj_apply]
  rw [hsmul]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h2 := congrArg (fun t => u * t * u⁻¹) h
    calc u * x * u⁻¹ * g = u * (x * (u⁻¹ * g * u)) * u⁻¹ := by group
      _ = u * (u⁻¹ * g * u * x) * u⁻¹ := h2
      _ = g * (u * x * u⁻¹) := by group
  · intro h
    have h2 := congrArg (fun t => u⁻¹ * t * u) h
    calc x * (u⁻¹ * g * u) = u⁻¹ * (u * x * u⁻¹ * g) * u := by group
      _ = u⁻¹ * (g * (u * x * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * g * u * x := by group

/-- The generating family `{U ⊓ C_G(x) : x ∈ M_σ#}` of `centralizerGeneratedBySigma M U`. -/
private abbrev sigCentFam (M U : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ x ∈ S14.sigmaSharp M, C = U ⊓ Subgroup.centralizer ({x} : Set G)}

/-- `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩`: for `u ∈ U ≤ M` it permutes the generating set
`{U ⊓ C_G(x) : x ∈ M_σ#}`, since `M_σ ◁ M` makes `x ↦ u x u⁻¹` a bijection of `M_σ#` and
`u (U ⊓ C_G(x)) u⁻¹ = U ⊓ C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizerGeneratedBySigma {M U : Subgroup G} {u : G}
    (huM : u ∈ M) (huU : u ∈ U) :
    MulAut.conj u • S15.centralizerGeneratedBySigma M U
      = S15.centralizerGeneratedBySigma M U := by
  -- conjugation by an element of `M` preserves `M_σ#` (as `M_σ ◁ M`).
  have hsig : ∀ v : G, v ∈ M → ∀ x : G, x ∈ S14.sigmaSharp M → v * x * v⁻¹ ∈ S14.sigmaSharp M := by
    intro v hv x hx
    rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxMσ, hx1⟩ := hx
    refine ⟨?_, fun h => hx1 (mul_left_cancel ((mul_inv_eq_one.mp h).trans (mul_one v).symm))⟩
    have hvN : v ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hv
    exact (Subgroup.mem_normalizer_iff.mp hvN x).mp hxMσ
  -- conjugation by `v ∈ M ∩ U` maps each generator to a generator.
  have hgen : ∀ v : G, v ∈ M → v ∈ U →
      ∀ C ∈ sigCentFam M U, MulAut.conj v • C ∈ sigCentFam M U := by
    rintro v hvM hvU C ⟨x, hx, rfl⟩
    exact ⟨v * x * v⁻¹, hsig v hvM x hx, by
      rw [Subgroup.smul_inf, Subgroup.conj_smul_eq_self_of_mem hvU,
        conj_smul_centralizer_singleton]⟩
  rw [show S15.centralizerGeneratedBySigma M U = sSup (sigCentFam M U) from rfl, mulAut_smul_sSup]
  refine le_antisymm (iSup_le fun C => iSup_le fun hC => le_sSup (hgen u huM huU C hC)) ?_
  refine sSup_le fun C hC => ?_
  have hC' : (MulAut.conj u)⁻¹ • C ∈ sigCentFam M U := by
    rw [← map_inv MulAut.conj]
    exact hgen u⁻¹ (inv_mem huM) (inv_mem huU) C hC
  calc C = MulAut.conj u • ((MulAut.conj u)⁻¹ • C) := (smul_inv_smul _ _).symm
    _ ≤ ⨆ C' ∈ sigCentFam M U, MulAut.conj u • C' :=
      le_iSup₂ (f := fun C' (_ : C' ∈ sigCentFam M U) => MulAut.conj u • C')
        ((MulAut.conj u)⁻¹ • C) hC'

/-- **General helper (§14-independent, reusable).**  A nontrivial `M`-normal subgroup `H ⊴ M` of a
maximal subgroup `M` of a minimal simple group is self-normalizing in `G`: `N_G(H) = M`.  `H ⊴ M`
gives `M ≤ N_G(H)`; if the inclusion were proper, maximality forces `N_G(H) = G`, so `H ⊴ G`, and
simplicity gives `H ∈ {⊥, ⊤}` — both excluded (`H ≠ ⊥` by hypothesis, `H ≤ M ⊊ G` rules out `⊤`).
Generalizes `normalizer_Msigma_eq_self` (the `H = M_σ` instance) to any nontrivial `M`-normal `H`. -/
theorem normalizer_eq_self_of_subgroupOf_normal_of_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hHle : H ≤ M)
    (hHnorm : (H.subgroupOf M).Normal) (hHne : H ≠ ⊥) :
    Subgroup.normalizer (H : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mp hHnorm
  refine le_antisymm ?_ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : H.Normal :=
      Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
    · exact absurd hbot hHne
    · exact absurd (top_le_iff.mp (htop ▸ hHle)) (mem_maximalSubgroups.mp hM).1

/-- **The Fitting subgroup of a maximal subgroup is self-normalizing**: `N_G(F(M)) = M` for a
maximal `M` of a minimal simple group of odd order.  `F(M)` is normal in `M`
(`fittingInG_subgroupOf_normal`) and nontrivial (`fitting_ne_bot_of_solvable_nontrivial`, as `M` is
a nontrivial — `M_σ ≠ ⊥` — solvable proper subgroup); apply the self-normalizing helper. -/
theorem normalizer_fittingInAmbient_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have hFne : S15.fittingInAmbient M ≠ ⊥ := by
    intro hbot
    refine OddOrder.Isaacs.Ch01.fitting_ne_bot_of_solvable_nontrivial ↥M ?_
    have hmap : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype
        = (⊥ : Subgroup ↥M).map M.subtype := by
      rw [Subgroup.map_bot]; exact hbot
    exact Subgroup.map_injective M.subtype_injective hmap
  exact normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG hM
    (OddOrder.BG.Ch2.S08.fittingInG_le M) (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M) hFne

/-- **Prop 16.1(a) `alternative` disjunct (i), TI case** (Peterfalvi (8.3)(a)): if the Fitting
subgroup `F(M)` of a maximal `M` is `TI` (`FittingIsTI M`), then its nilpotent normal Hall core
`M_F#` is a `TI`-subset with normalizer `N_G(M_F)`.  Since `M_F ≤ F(M)`, an overlap `a, gag⁻¹ ∈ M_F#`
is an overlap in `F(M)#`, so `FittingIsTI` forces `g ∈ N_G(F(M)) = M` (`normalizer_fittingInAmbient_eq_self`);
and `M_F ⊴ M` gives `M ≤ N_G(M_F)`, whence `g ∈ N_G(M_F)`.  This supplies the first disjunct of the
`TypeIData.alternative` field in the `F(M)`-TI case of the `hFI` bridge of `proposition_type_classification`
(the non-TI case is the deeper BG Theorem 15.7(e) trichotomy, `fitting_not_ti_cases`). -/
theorem maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTI : S15.FittingIsTI M) :
    IsTISubset (sharpSubgroup (maxNilpotentNormalHall M))
      (Subgroup.normalizer (maxNilpotentNormalHall M : Set G)) := by
  -- `M_F ≤ F(M)`.
  have hMFleF : maxNilpotentNormalHall M ≤ S15.fittingInAmbient M :=
    S15.maxNilpotentNormalHall_le_fittingInG M
  -- `M ≤ N_G(M_F)` from `M_F ⊴ M`.
  have hMnorm : M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  -- `N_G(F(M)) = M`.
  have hNF : Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M :=
    normalizer_fittingInAmbient_eq_self hG hM
  intro g hg
  obtain ⟨a, haMem, hgaMem⟩ := hg
  rw [sharpSubgroup, Set.mem_sdiff] at haMem hgaMem
  -- Lift the overlap from `M_F#` to `F(M)#`.
  have ha' : a ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_sdiff]; exact ⟨hMFleF haMem.1, haMem.2⟩
  have hga' : g * a * g⁻¹ ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_sdiff]; exact ⟨hMFleF hgaMem.1, hgaMem.2⟩
  -- `FittingIsTI` ⟹ `g ∈ N_G(F(M)) = M ≤ N_G(M_F)`.
  exact hMnorm (hNF ▸ hTI g ⟨a, ha', hga'⟩)

/-- **Theorem A(8) `U = ⊥` core, from type `P₁`** (mmd L4274): for a type-`P₁` maximal subgroup,
the Hall `(κ(M) ∪ σ(M))ᶜ`-complement `U` is trivial.  Type `P₁` means `κ(M) = π(M) ∖ σ(M)`
(`IsTypeP1.2`), so `π(M) ⊆ κ(M) ∪ σ(M)` and the prime set `(κ(M) ∪ σ(M))ᶜ` meets `π(M)` only in
`∅`; a Hall `(κ ∪ σ)ᶜ`-subgroup of `M` therefore has order coprime to `|M|`, i.e. trivial.

This is the `U = ⊥` conjunct of Theorem A(8) (`theoremA_maximal_structure`), now **derivable from
`Thm 15.2 (mf_ne_msigma_typeP1_structure)`** via `isTypeP1_of_mf_ne_msigma`: `M_F ≠ M_σ ⟹ IsTypeP1 ⟹
U = ⊥`.  Together with `|K| = p` (also a Thm 15.2 output) this leaves only `FittingIsTI M` for the
full A(8).  Stated for the relative `U.subgroupOf M` (which is what the Hall hypothesis constrains);
when `U ≤ M` it gives `U = ⊥`. -/
theorem isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot [Finite G] {M U : Subgroup G}
    (hP1 : S14.IsTypeP1 M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    U.subgroupOf M = ⊥ := by
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  -- `p ∈ (κ ∪ σ)ᶜ` (Hall) and `p ∈ π(M)` (`|U.subgroupOf M| ∣ |M|`).
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩)
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans (Subgroup.card_subgroup_dvd_card (U.subgroupOf M)), Nat.card_pos.ne'⟩
  -- but `π(M) ⊆ κ(M) ∪ σ(M)` for type `P₁`.
  refine hpcompl ?_
  by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
  · exact Set.mem_union_right _ hpσ
  · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hpM, hpσ⟩)

/-- **For a type-`P₁` maximal subgroup, `M' = M_σ`** (Coq `BGsection16` `typePfacts`: for
`M ∈ ℳ_𝓟₁`, `Ms = M^(1)`; BG Theorem C(3) collapse with the trivial `(κ ∪ σ)'`-complement).
Since `κ(M) = π(M) ∖ σ(M)` for type `P₁`, the Hall `(κ ∪ σ)'`-subgroup `U` of `M` is trivial
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), so Lemma 15.1(b)'s decomposition `M' = U M_σ`
(`typeP_auxiliary_structure` conjunct 5) collapses to `M' = M_σ`.

This is the structural fact underlying the type-`P₁` half of Proposition 16.1's forward bridges: the
`TypePData` complement `U` (`M' = M_F ⊔ U`) lives inside `M_σ = M'`, and (Coq `typePfacts`)
`U = ⊥ ⟺ M_F = M_σ` distinguishes type V (`U = ⊥`) from types III/IV (`U ≠ ⊥`). -/
theorem isTypeP1_derivedInG_eq_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` and a Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ≠ ⊥` (type `P` has nonempty `κ`).
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `U = ⊥` (type `P₁`): the `(κ ∪ σ)'`-Hall is trivial.
  have hUbot : U = ⊥ := by
    have h0 : U.subgroupOf M = ⊥ := isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot hP1 hU
    rw [← Subgroup.card_eq_one] at h0 ⊢
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h0
  -- Lemma 15.1(b): `M' = U ⊔ M_σ = ⊥ ⊔ M_σ = M_σ`.
  have haux := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  rw [(haux.2.2.2.2.1 hKne).1, hUbot, bot_sup_eq]

/-- **Type-`P₁` `M_F`-internal complement** (the `M' = M_F ⋊ U` factorisation of Peterfalvi (8.4.b)
/ Coq `of_typeP`): for a type-`P₁` maximal subgroup `M` with Hall `κ(M)`-subgroup `K`, the Fitting
kernel `M_F` has a `K`-invariant complement `U` inside `M' = M_σ` (`M_F ⊔ U = M'`, `K ≤ N_G(U)`,
`M_F ⊓ U = ⊥`).

Construction: `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`) is solvable, `M_F ◁ M` is a Hall subgroup
of `M'` (`maxNilpotentNormalHall_isHall`, transferred from `M` via index-divisibility), and `K` (a
`σ'`-group, `κ ⊆ σᶜ`) acts coprimely on the `σ`-group `M'`; the `K`-invariant Schur–Zassenhaus
complement (`exists_aInvariant_complement_within_normal`) supplies `U`.  This discharges the
`hUle`/`hKnorm`/`hDcompl`/`U ≠ ⊥` `TypePData` fields of the FT-critical `hP1neIIIIV` bridge; the
remaining `TypePData` fields (`U` nilpotent `= M'/M_F` nilpotent, the `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`
decomposition) and `N_G(U) ⊆ M` are the deeper Coq `Fcore_structure` content. -/
theorem exists_typeP1_mf_complement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) :
    ∃ U : Subgroup G, U ≤ derivedInG M ∧
      maxNilpotentNormalHall M ⊔ U = derivedInG M ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧
      maxNilpotentNormalHall M ⊓ U = ⊥ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hM'_le_M : M' ≤ M := Subgroup.map_subtype_le _
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  haveI : IsSolvable ↥M' :=
    solvable_of_solvable_injective (f := (Subgroup.inclusion hM'_le_M))
      (Subgroup.inclusion_injective hM'_le_M)
  -- `N = M_F ≤ M' = M_σ`.
  have hN_le : N ≤ M' := by rw [hM'σ]; exact maxNilpotentNormalHall_le_Msigma hG hM
  -- Normalizer facts (`M_F ◁ M`, `M' ◁ M`, `K ≤ M`).
  have hM'_norm_N : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'_le_M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hK_norm_M' : K ≤ Subgroup.normalizer (M' : Set G) :=
    hKM.trans (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M)
  have hK_norm_N : K ≤ Subgroup.normalizer (N : Set G) :=
    hKM.trans (maxNilpotentNormalHall_le_normalizer M)
  -- `M_F` is a Hall subgroup of `M'` (transfer from `M`, since `[M':M_F] ∣ [M:M_F]`).
  have hN_hall : Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M') := by
    obtain ⟨h1, h2⟩ := maxNilpotentNormalHall_isHall M
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv] at hp
    · apply h2 p
      have hmul := Subgroup.relIndex_mul_relIndex N M' M hN_le hM'_le_M
      have hdvd : (N.subgroupOf M').index ∣ (N.subgroupOf M).index :=
        ⟨M'.relIndex M, hmul.symm⟩
      exact Nat.primeFactors_mono hdvd Subgroup.index_ne_zero_of_finite hp
  -- `K` (a `σ'`-group) acts coprimely on `M' = M_σ` (a `σ`-group).
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥M') := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => ?_) (fun p hp => ?_)
    · -- `p ∈ π(K) ⊆ κ ⊆ σᶜ`.
      have hpκ : p ∈ S14.kappa M := by
        apply hK.1
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact S14.kappa_subset_sigmaCompl hpκ
    · -- `p ∈ π(M') = π(M_σ) ⊆ σ`, so `p ∉ σᶜ`.
      simp only [Set.mem_compl_iff, not_not]
      have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv,
          ← hM'σ]
        exact hp
      exact (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).1 p hpMσ
  exact OddOrder.GroupTheory.exists_aInvariant_complement_within_normal
    hN_le hM'_norm_N hK_norm_M' hK_norm_N hN_hall hCop

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-complement is nilpotent** (`M'/M_F` nilpotent, the deferred half
of Corollary 15.5(c)): any complement `U` of `M_F` in `M' = M_σ` is nilpotent.

Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) supplies `Q ⋊ D = M_σ` with `Q ≤ M_F` and `D`
nilpotent; hence `M_σ = M_F · D`, so `M_σ/M_F` is the image of the nilpotent `D` under the
quotient map (`Group.nilpotent_of_surjective`), hence nilpotent.  The complement `U` (`U ⊓ M_F = ⊥`,
`U ⊔ M_F = M_σ`) is isomorphic to `M_σ/M_F` (the restricted quotient map is bijective), so `U` is
nilpotent.  Discharges the `hUnilp` field of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge. -/
theorem isNilpotent_complement_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Group.IsNilpotent ↥U := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hM'σ : derivedInG M = Mσ := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  rw [hM'σ] at hsup
  have hMFMσ : maxNilpotentNormalHall M ≤ Mσ := S15.maxNilpotentNormalHall_le_Msigma hG hM
  have hUMσ : U ≤ Mσ := hsup ▸ le_sup_right
  -- `M̄F = M_F.subgroupOf Mσ` is normal in `↥Mσ`.
  have hMFnormMσ : Mσ ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (OddOrder.BG.Ch3.S10.Msigma_le M).trans (S15.maxNilpotentNormalHall_le_normalizer M)
  haveI hMFbarNorm : ((maxNilpotentNormalHall M).subgroupOf Mσ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFMσ).mpr hMFnormMσ
  -- Theorem 15.2: `Q ⋊ D = M_σ`, `Q ≤ M_F`, `D` nilpotent.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨_, Q, _, D, _, _, _, _, _, _, _, _, _, hQMF, _, hQDcompl, hDnil, _⟩ :=
    S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK rfl
  -- `M̄F ⊔ D̄ = ⊤` in `↥Mσ` (`Q̄ ⊔ D̄ = ⊤`, `Q̄ ≤ M̄F`).
  have hMFDbarTop : (maxNilpotentNormalHall M).subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ :=
    top_le_iff.mp (hQDcompl.sup_eq_top ▸ sup_le_sup_right (Subgroup.subgroupOf_mono Mσ hQMF) _)
  -- `D̄ = D.subgroupOf Mσ` is nilpotent (`≅ D ⊓ Mσ ≤ D`).
  haveI hDnilI : Group.IsNilpotent ↥D := hDnil
  haveI hDbarNil : Group.IsNilpotent ↥(D.subgroupOf Mσ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Group.nilpotent_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ Mσ ≤ D)).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ Mσ ≤ Mσ)).symm)
  -- `M_σ/M_F` is nilpotent: the quotient map restricts to a surjection `D̄ ↠ M_σ/M_F`.
  haveI hquotNil : Group.IsNilpotent (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) := by
    have hsurj : Function.Surjective
        (((QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp
          (D.subgroupOf Mσ).subtype)) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨m, hm, d, hd, hmd⟩ :=
        Subgroup.mem_sup_of_normal_left.mp (hMFDbarTop ▸ Subgroup.mem_top g)
      refine ⟨⟨d, hd⟩, ?_⟩
      change QuotientGroup.mk (d : ↥Mσ) = QuotientGroup.mk g
      rw [← hmd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, one_mul]
    exact Group.nilpotent_of_surjective _ hsurj
  -- `U ≅ M_σ/M_F`: the restricted quotient map `Ū → M_σ/M_F` is bijective.
  have hŪsup : U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUMσ hMFMσ, sup_comm, hsup, Subgroup.subgroupOf_self]
  set g : ↥(U.subgroupOf Mσ) →* (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) :=
    (QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp (U.subgroupOf Mσ).subtype
    with hgdef
  have hUbarInf : U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ maxNilpotentNormalHall M ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.2, Subgroup.mem_subgroupOf.mp ha.1⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]
    exact Subtype.ext hval
  have hginj : Function.Injective g := by
    intro x y hxy
    have hdiv : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      (QuotientGroup.eq.mp hxy)
    have hxinv : (x : ↥Mσ)⁻¹ ∈ U.subgroupOf Mσ := inv_mem x.2
    have hUmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ U.subgroupOf Mσ := mul_mem hxinv y.2
    have hmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈
        U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      ⟨hUmem, hdiv⟩
    rw [hUbarInf, Subgroup.mem_bot, mul_eq_one_iff_inv_eq, inv_inv] at hmem
    exact Subtype.ext hmem
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ := by
      rw [hŪsup]; exact Subgroup.mem_top z
    obtain ⟨u, hu, m, hm, hum⟩ := Subgroup.mem_sup_of_normal_right.mp hz
    refine ⟨⟨u, hu⟩, ?_⟩
    change QuotientGroup.mk (u : ↥Mσ) = QuotientGroup.mk z
    rw [← hum, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, mul_one]
  haveI : Group.IsNilpotent ↥(U.subgroupOf Mσ) :=
    Group.nilpotent_of_mulEquiv (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩).symm
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUMσ)

/-- **Type-`P₁` `M_F`-complement is a genuine complement in `M'`** (the `hDcompl` `TypePData` field):
any `U` with `M_F ⊔ U = M'` and `M_F ⊓ U = ⊥` gives
`IsComplement' (M_F.subgroupOf M') (U.subgroupOf M')`.

`M_F ◁ M ⊇ M'`, so `M_F.subgroupOf M'` is normal in `↥M'`; with `M_F ⊓ U = ⊥` (disjoint) and
`M_F ⊔ U = M'` (codisjoint, i.e. `⊤` in `↥M'`) the internal product is the whole of `↥M'`.  Card
route: `[M':M_F] = M_F.relIndex M' = M_F.relIndex U = |U|` (second isomorphism theorem
`relIndex_sup_right`, then `M_F ⊓ U = ⊥`), so `|M_F.subgroupOf M'|·|U.subgroupOf M'| = |M'|`, and
`isComplement'_of_card_mul_and_disjoint` concludes.  Purely from `hsup`/`hinf` (no type-`P₁`
hypothesis); discharges the deepest *non*-Fitting `U`-field gated by `exists_typeP1_mf_complement`. -/
theorem isComplement'_mf_complement_of_sup_inf [Finite G] {M U : Subgroup G}
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      (U.subgroupOf (derivedInG M)) := by
  classical
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hNle : N ≤ M' := hsup ▸ le_sup_left
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `N.subgroupOf M'` is normal in `↥M'` (`M' ≤ M ≤ N_G(N)`).
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  haveI hN'norm : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNnormM'
  -- Disjointness and codisjointness in `↥M'`.
  have hdisj : Disjoint (N.subgroupOf M') (U.subgroupOf M') := by
    rw [disjoint_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ N ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]; exact Subtype.ext hval
  have hsup' : N.subgroupOf M' ⊔ U.subgroupOf M' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNle hUle, hsup, Subgroup.subgroupOf_self]
  -- `[M':M_F] = |U.subgroupOf M'|` (second iso theorem, then disjointness).
  have hidx : (N.subgroupOf M').index = Nat.card ↥(U.subgroupOf M') := by
    have key : (N.subgroupOf M').relIndex (U.subgroupOf M') = Nat.card ↥(U.subgroupOf M') := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot]
    rw [← key, ← Subgroup.relIndex_sup_right, sup_comm, hsup', Subgroup.relIndex_top_right]
  have hcard : Nat.card ↥(N.subgroupOf M') * Nat.card ↥(U.subgroupOf M') = Nat.card ↥M' := by
    rw [← hidx, Subgroup.card_mul_index]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

/-- **Coprime inner-induced conjugation is trivial**: if `x` normalizes `N`, `orderOf x` is coprime
to `|N|`, and conjugation by `x` agrees on `N` with conjugation by some `n ∈ N` (so `x` induces an
*inner* automorphism of `N`), then `x` centralizes `N`.

The induced automorphism `φ(x) ∈ Aut(N)` (via `normalizerMonoidHom`) equals `φ(n)`, an inner
automorphism by `n ∈ N`, so `orderOf (φ x)` divides both `orderOf x` and `|N|` (as
`orderOf (φ n) ∣ orderOf n ∣ |N|`); coprimality forces `orderOf (φ x) = 1`, i.e. `φ x = 1`, i.e.
`x ∈ ker (normalizerMonoidHom N) = C_G(N)`.  This is the coprime-action core of the type-`P₁`
`M_F`-internal Fitting decomposition (`F(M) ⊓ U ⊆ C(M_F)`). -/
theorem mem_centralizer_of_inner_conj_of_coprime [Finite G] {N : Subgroup G} {x n : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N)
    (hcop : Nat.Coprime (orderOf x) (Nat.card ↥N))
    (hconj : ∀ y ∈ N, x * y * x⁻¹ = n * y * n⁻¹) :
    x ∈ Subgroup.centralizer (N : Set G) := by
  classical
  have hnN : n ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hn
  set φ := N.normalizerMonoidHom with hφ
  -- `φ ⟨x⟩ = φ ⟨n⟩`: conjugation by `x` and by `n` agree on `N`.
  have hφeq : φ ⟨x, hxN⟩ = φ ⟨n, hnN⟩ := by
    ext y
    exact hconj (y : G) y.2
  -- `orderOf (φ ⟨x⟩) ∣ orderOf x`.
  have hdvd_x : orderOf (φ ⟨x, hxN⟩) ∣ orderOf x := by
    have h1 := orderOf_map_dvd φ ⟨x, hxN⟩
    rwa [Subgroup.orderOf_mk] at h1
  -- `orderOf (φ ⟨x⟩) = orderOf (φ ⟨n⟩) ∣ orderOf n ∣ |N|`.
  have hdvd_N : orderOf (φ ⟨x, hxN⟩) ∣ Nat.card ↥N := by
    rw [hφeq]
    refine (orderOf_map_dvd φ ⟨n, hnN⟩).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard N hn
  -- Coprimality forces the induced automorphism to be trivial.
  have h1 : orderOf (φ ⟨x, hxN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd_x hdvd_N
  have hker : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (N : Set G))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]; exact h1
  rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-internal Fitting decomposition** (BG Corollary 15.5, the
`M' = M_σ` form): for a type-`P₁` maximal `M` with `M_F`-complement `U` in `M' = M_σ`
(`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), the Fitting subgroup is `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.

`F(M)` is nilpotent with `M_F` a normal Hall subgroup (Hall in `M`, hence in `F(M)`) and
`F(M) ≤ M'` (`M` is not type `F`).  By the modular law `F(M) = M_F ⊔ (U ⊓ F(M))` (`M_F ≤ F(M)`,
`F(M) ≤ M' = M_F ⊔ U`).  The crux `U ⊓ F(M) ⊆ C(M_F)`: each `x ∈ U ⊓ F(M)` decomposes (Corollary
15.5, `F(M) = C_M(M_F) · M_F`) as `x = a · b` with `a ∈ C(M_F)`, `b ∈ M_F`, so conjugation by `x`
agrees on `M_F` with conjugation by `b` (inner); as `|U|` is coprime to `|M_F|` (`M_F` Hall),
`mem_centralizer_of_inner_conj_of_coprime` forces `x ∈ C(M_F)`.  Discharges the `hFiteq` (and hence
`hSDfit`, via `M'' ≤ F(M)`) residual of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge. -/
theorem fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set N := maxNilpotentNormalHall M with hNdef
  set M' := derivedInG M with hM'def
  set F := S15.fittingInAmbient M with hFdef
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_Y, -, -, -, _hM''F, hFcent, -, -, -, _hNM', hFle, -⟩ := S15.fitting_decomposition hG hM
  have hFleM' : F ≤ M' := hFle hnotF
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hFM : F ≤ M := hFleM'.trans hM'M
  have hNF : N ≤ F := S15.maxNilpotentNormalHall_le_fittingInG M
  have hNM : N ≤ M := maxNilpotentNormalHall_le M
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `coprime |U| |N|`: `|U| ∣ [M:N]` (complement card), `N` Hall in `M`.
  have hcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hcard0 := (Subgroup.isComplement'_iff_card_mul_and_disjoint.mp hcompl).1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ M' from hNF.trans hFleM')).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv] at hcard0
  -- `hcard0 : |N| * |U| = |M'|`.
  have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥N) := by
    have hHall := maxNilpotentNormalHall_isHall M
    have hci := hHall.coprime_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at hci
    -- `hci : coprime |N| (N.subgroupOf M).index`.
    have hMeq : Nat.card ↥N * (N.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
      exact Subgroup.card_mul_index (N.subgroupOf M)
    have hM'dvdM : Nat.card ↥M' ∣ Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (M'.subgroupOf M)
    have hUdvd : Nat.card ↥U ∣ (N.subgroupOf M).index := by
      have hdvd : Nat.card ↥N * Nat.card ↥U ∣ Nat.card ↥N * (N.subgroupOf M).index := by
        rw [hcard0, hMeq]; exact hM'dvdM
      exact (mul_dvd_mul_iff_left (Nat.card_pos (α := ↥N)).ne').mp hdvd
    exact (hci.coprime_dvd_right hUdvd).symm
  -- `F = N ⊔ (U ⊓ F)` (Dedekind modular law, via `M' = N ⋊ U` and `N ≤ F ≤ M'`).
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  haveI hNnorm' : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNF.trans hFleM')).mpr hNnormM'
  have hmod : F = N ⊔ (U ⊓ F) := by
    apply le_antisymm
    · intro f hf
      have hfM' : f ∈ M' := hFleM' hf
      have hmemsup : (⟨f, hfM'⟩ : ↥M') ∈ N.subgroupOf M' ⊔ U.subgroupOf M' := by
        rw [← Subgroup.subgroupOf_sup (hNF.trans hFleM') hUle, hsup, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, u, hu, hnu⟩ := Subgroup.mem_sup_of_normal_left.mp hmemsup
      have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
      have hfnu : f = (n : G) * (u : G) := by
        have h := congrArg Subtype.val hnu; simpa using h.symm
      have huF : (u : G) ∈ F := by
        rw [show (u : G) = (n : G)⁻¹ * f by rw [hfnu]; group]
        exact F.mul_mem (F.inv_mem (hNF hnN)) hf
      rw [hfnu]
      exact Subgroup.mul_mem_sup hnN (Subgroup.mem_inf.mpr ⟨huU, huF⟩)
    · exact sup_le hNF inf_le_right
  -- Crux: `U ⊓ F ≤ C(N)`.
  have hFUcent : U ⊓ F ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxF⟩ := hx
    have hxM : x ∈ M := hFM hxF
    haveI hNnorm : (N.subgroupOf M).Normal := maxNilpotentNormalHall_subgroupOf_normal M
    have hxFM : (⟨x, hxM⟩ : ↥M) ∈
        (Subgroup.centralizer (N : Set G) ⊓ M).subgroupOf M ⊔ N.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup inf_le_right hNM, Subgroup.mem_subgroupOf]
      show x ∈ Subgroup.centralizer (N : Set G) ⊓ M ⊔ N
      rw [← hFcent]; exact hxF
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hxFM
    have haC : (a : G) ∈ Subgroup.centralizer (N : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
    have hbN : (b : G) ∈ N := Subgroup.mem_subgroupOf.mp hb
    have hxab : x = (a : G) * (b : G) := by
      have h := congrArg (Subtype.val) hab
      simpa using h.symm
    have hxnorm : x ∈ Subgroup.normalizer (N : Set G) := maxNilpotentNormalHall_le_normalizer M hxM
    have hcopx : Nat.Coprime (orderOf x) (Nat.card ↥N) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard U hxU) hcop
    refine mem_centralizer_of_inner_conj_of_coprime hxnorm hbN hcopx ?_
    intro y hy
    have hbyb : (b : G) * y * (b : G)⁻¹ ∈ N := N.mul_mem (N.mul_mem hbN hy) (N.inv_mem hbN)
    have hcomm := (Subgroup.mem_centralizer_iff.mp haC) _ hbyb
    rw [hxab]
    calc (a : G) * (b : G) * y * ((a : G) * (b : G))⁻¹
        = (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (b : G) * y * (b : G)⁻¹ * (a : G) * (a : G)⁻¹ := by rw [← hcomm]
      _ = (b : G) * y * (b : G)⁻¹ := by group
  -- Assemble `F = N ⊔ (U ⊓ C(N))`.
  show F = N ⊔ (U ⊓ Subgroup.centralizer (N : Set G))
  apply le_antisymm
  · rw [hmod]
    exact sup_le_sup_left (le_inf inf_le_left hFUcent) N
  · refine sup_le hNF ?_
    have hle : U ⊓ Subgroup.centralizer (N : Set G) ≤ Subgroup.centralizer (N : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans (hUle.trans hM'M))
    exact hle.trans (le_sup_left.trans_eq hFcent.symm)

/-- **Prop 16.1(a) forward bridge, core** (mmd L4480): a type-`F` maximal `M` (`κ(M) = ∅`, so the
Hall `κ`-subgroup `K = ⊥`) carries the shared Peterfalvi type-`F` structure `TypeFData M`.

This is the `M ∈ ℳ_𝓕 ⟹ Type F` core feeding `proposition_type_classification`'s `hFI` (clause (a),
`mpr`).  The deep fields are read off existing §15 results: `U1_commutative` and `frobenius_HU0`
from `typeP_auxiliary_structure` (mmd 15.1(d)(e)); `H = M_F = M_σ` from Theorem A(8) (`U ≠ ⊥` rules
out the `M_F ≠ M_σ` branch); `M = U M_σ` from Theorem A(3) with `K = ⊥`; `centralizer_le_U1` is
`le_sSup` over `M_F# ⊆ M_σ#`; and `U1_normal` (`⟨C_U(x) | x ∈ M_σ#⟩ ◁ U`) is `U`-conjugation
invariance of the generating set `{U ⊓ C_G(x) : x ∈ M_σ#}` (`conj_smul_centralizerGeneratedBySigma`,
as `M_σ ◁ M`).  **Axiom-clean**: A(3) is `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` and the A(8)
`U = ⊥` exclusion routes through `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (Thm 15.2), not
the `sorry` standalone `theoremA_maximal_structure`; `typeP_auxiliary_structure` is itself clean. -/
theorem typeFData_of_kappa_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  -- Theorem A(3) decomposition `M = K U M_σ` (axiom-clean, via `hKM`/`hUM`; avoids the `sorry`
  -- standalone `theoremA_maximal_structure`).
  have hA3 : M = K ⊔ U ⊔ Mσ := typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU
  -- `M_F = M_σ`: `U ≠ ⊥` excludes the type-`P₁` `U = ⊥` (Theorem A(8), via Thm 15.2).
  have hMFMσ : S15.MF M = Mσ := by
    by_contra hne
    have hUsub : U.subgroupOf M = ⊥ :=
      isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot (isTypeP1_of_mf_ne_msigma hG hM hne) hU
    have h := Subgroup.map_subgroupOf_eq_of_le hUM
    rw [hUsub, Subgroup.map_bot] at h
    exact hUne h.symm
  -- `M = U M_σ` (A3 with `K = ⊥`).
  have hMU : M = U ⊔ Mσ := by rw [hA3, hKbot, bot_sup_eq]
  -- `typeP_auxiliary_structure`: `U1` abelian (15.1(d)) + the Frobenius `U₀ M_σ` (15.1(e)).
  obtain ⟨_, _, _, _, _, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := S15.MF M
    U := U
    U1 := S15.centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := rfl
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := S15.maxNilpotentNormalHall_le M
    U_le := hUM
    U1_le := by
      apply sSup_le
      rintro C ⟨x, _, rfl⟩
      exact inf_le_left
    U0_le := hU0U
    complement := ?_
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff]
      exact ⟨S15.maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := ?_ }⟩
  · -- `complement`: `M_F = M_σ` complements `U` in `M`.  `M_σ ◁ M`, `M_σ ⊓ U = ⊥` and `M_σ ⊔ U = M`
    -- come from the `K = ⊥` `SubgroupESetup` (`subgroupESetup_of_isHall_kappa_eq_bot`).
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    rw [hMFMσ]
    haveI hMσnorm : ((Mσ).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr
        (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxMσ hxU
      rw [Subgroup.mem_subgroupOf] at hxMσ hxU
      have hx : (x : G) ∈ Mσ ⊓ U := ⟨hxMσ, hxU⟩
      rw [hsetup.E_compl_inf, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hUM,
        hsetup.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]
  · -- `U1_normal`: `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩` (it permutes the generators).
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]
  · -- `frobenius_HU0`: rewrite `M_F = M_σ`, `M_F ⊔ U₀ = U₀ ⊔ M_σ` into the Frobenius datum.
    rw [hMFMσ, sup_comm]
    exact hfrob

/-- **Prop 16.1(a) `TypeFData` construction wrapper**: a BG-local type-`F` maximal `M`
(`S14.IsTypeF M`, i.e. `κ(M) = ∅`) carries the shared Peterfalvi type-`F` structure
`GroupTheory.IsTypeF M`.  Specializes `typeFData_of_kappa_eq_bot` with `K = ⊥` (a `κ`-Hall since
`κ(M) = ∅`) and a `(κ ∪ σ)'`-Hall `U` from Hall's theorem; `U ≠ ⊥` because the `σ`-complement of a
maximal subgroup is nontrivial (`SubgroupESetup.E_ne_bot`: `E = U = ⊥` would force `M = M_σ ≤ M'`,
contradicting `M' ⊊ M`).  This is the type-`F`-structure half of the `hFI` bridge of
`proposition_type_classification`; the `alternative` trichotomy is added in `isTypeI_of_isTypeF`. -/
theorem isTypeF_groupTheory_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hκ : S14.kappa M = ∅ := hF
  -- `K = ⊥` is a `κ(M)`-Hall subgroup (`κ(M) = ∅`).
  have hKhall : Ch03.IsHallSubgroup (S14.kappa M) ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
    intro p _; rw [hκ]; exact Set.notMem_empty p
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `U ≠ ⊥`: the `σ`-complement (`= U`, as `K = ⊥`) of the maximal subgroup is nontrivial.
  obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
    subgroupESetup_of_isHall_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU
  have hUne : U ≠ ⊥ := hsetup.E_ne_bot hG
  exact typeFData_of_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU hUne

/-- **BG Theorem 15.7(e), conjunct A divisibility per prime** (Coq `regZq_dv_q1`): for a type-`F`
datum `td` and a `td.U0`-invariant order-`q` subgroup `Z` of the Frobenius kernel `td.H = M_F`, the
exponent of the complement `U` divides `q - 1`.

`td.U0` acts on `Z` by conjugation (`Subgroup.normalizerMonoidHom`, valid since `td.U0 ≤ N_G(Z)`);
the action is fixed-point-free because `td.H ⋊ td.U0` is a Frobenius group with kernel `td.H ⊇ Z`
(`td.frobenius_HU0.conj_frobenius`).  Hence `IsFrobeniusAction td.U0 Z`, giving
`|U0| ∣ |Z| - 1 = q - 1` (`card_dvd_sub_one_of_isFrobeniusAction`), and
`exp U = exp U0 ∣ |U0| ∣ q - 1` (`td.exponent_eq`, `Group.exponent_dvd_nat_card`).  This is the
divisibility engine of the exponent conjunct (c) of `isTypeI_of_isTypeF`; the per-prime witness `Z`
(order-`q` characteristic subgroup of `M_F`) is supplied separately. -/
theorem typeF_exponent_dvd_sub_one_of_invariant_card [Finite G] {M : Subgroup G}
    (td : OddOrder.GroupTheory.TypeFData M) {Z : Subgroup G} {q : ℕ}
    (hZH : Z ≤ td.H) (hZcard : Nat.card ↥Z = q)
    (hU0NZ : td.U0 ≤ Subgroup.normalizer (Z : Set G)) :
    Monoid.exponent ↥td.U ∣ q - 1 := by
  classical
  -- `G`-level fixed-point-freeness of the conjugation action of `U0` on the kernel `td.H`.
  have hfpf : ∀ u ∈ td.U0, u ≠ 1 → ∀ z ∈ td.H, z ≠ 1 → u * z * u⁻¹ ≠ z := by
    intro u hu hu1 z hz hz1 hconj
    have huK : u ∈ td.H ⊔ td.U0 := (le_sup_right : td.U0 ≤ td.H ⊔ td.U0) hu
    have hzK : z ∈ td.H ⊔ td.U0 := (le_sup_left : td.H ≤ td.H ⊔ td.U0) hz
    refine td.frobenius_HU0.conj_frobenius ⟨u, huK⟩ ((Subgroup.mem_subgroupOf).mpr hu)
      (fun h => hu1 (by simpa using Subtype.ext_iff.mp h)) ⟨z, hzK⟩
      ((Subgroup.mem_subgroupOf).mpr hz)
      (fun h => hz1 (by simpa using Subtype.ext_iff.mp h)) ?_
    exact Subtype.ext (by simpa using hconj)
  -- Conjugation action of `U0` on `Z` (`U0 ≤ N_G(Z)`).
  letI : MulDistribMulAction ↥td.U0 ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hU0NZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥td.U0 ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    refine hfpf (u : G) u.2 (fun h => hu (Subtype.ext h)) (z : G) (hZH z.2)
      (fun h => hz (Subtype.ext h)) ?_
    rw [← h1]; exact congrArg Subtype.val hfix
  have hdvd : Nat.card ↥td.U0 ∣ q - 1 :=
    hZcard ▸ OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rw [← td.exponent_eq]
  exact Group.exponent_dvd_nat_card.trans hdvd

/-- **Prop 16.1(a) forward bridge `hFI`** (Peterfalvi (8.3) / BG Theorem 15.7): a type-`F` maximal
`M` is of type I.  The shared type-`F` structure `TypeFData M` is `isTypeF_groupTheory_of_isTypeF`;
the `TypeIData.alternative` trichotomy splits on whether `F(M)` is `TI`:

* `FittingIsTI M`: disjunct (a), `M_F#` is a `TI`-subset
  (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).
* `¬FittingIsTI M`: disjuncts (b)/(c) (`M_F` abelian of rank 2, or the exponent–cyclic case) come
  from the BG Theorem 15.7(e) trichotomy (`nonTI_Fitting_structure`, Coq `BGsection15`).  This is
  the genuinely deep residual: the `(e)` clause of the landed `fitting_not_ti_cases` is currently
  weakened to the tautology `abelian M_F ∨ ¬abelian M_F`, so the structured rank-2 / exponent
  alternatives are not yet available and the non-TI case must await formalizing 15.7(e). -/
theorem isTypeI_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeI M := by
  obtain ⟨td⟩ := isTypeF_groupTheory_of_isTypeF hG hM hF
  refine ⟨{ typeF := td, alternative := ?_ }⟩
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset.
    refine Or.inl ?_
    rw [td.H_eq]
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI
  · -- `F(M)` not TI ⟹ BG Theorem 15.7(e) trichotomy.  For type `F` the type-`P₁` case (e3) is
    -- excluded, leaving disjunct (b) (`M_F` abelian of rank 2) or (c) (exponent / cyclic-`O_{p'}`).
    rw [td.H_eq]
    -- The non-TI witness: `g ∉ M`, prime `p ∈ σ(M)`, order-`p` `X₁ ≤ M_σ ⊓ M_σ^g`, `rank (M_F ⊓ C_G(X₁)) < 3`.
    obtain ⟨g, p, X₁, hgM, hp, _hpσ, hX₁card, hX₁Mσ, hX₁cMσ, _hCGnotM, hrank3⟩ :=
      exists_inf_conj_fitting_orderP_witness hG hM hTI
    haveI : Fact p.Prime := ⟨hp⟩
    have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hTI
    -- `X₁ ≤ M_F` and `X₁ ≤ M_F^g` (using `M_F = M_σ`).
    have hX₁MF : X₁ ≤ MF M := le_trans hX₁Mσ (le_of_eq hMFeq.symm)
    have hX₁cMF : X₁ ≤ MulAut.conj g • MF M := by rw [hMFeq]; exact hX₁cMσ
    -- `p` is odd (`p ∣ |X₁| ∣ |G|`, `|G|` odd).
    have hpdvdG : p ∣ Nat.card G := hX₁card ▸ Subgroup.card_subgroup_dvd_card X₁
    have hpOdd : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | h
      · exact absurd (even_iff_two_dvd.mpr hpdvdG) (Nat.not_even_iff_odd.mpr hG.odd)
      · exact h
    by_cases habel : IsMulCommutative ↥(MF M)
    · -- abelian `M_F` ⟹ disjunct (b): `rank M_F = 2`.
      refine Or.inr (Or.inl ⟨habel, ?_⟩)
      show rank ↥(MF M) = 2
      have hcommMF : ∀ a b : ↥(MF M), a * b = b * a := isMulCommutative_iff.mp habel
      -- ≤ 2: `M_F` abelian ⟹ `M_F ≤ C_G(X₁)`, so `M_F ⊓ C_G(X₁) = M_F` and `rank M_F < 3`.
      have hMFcentr : MF M ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simpa using congrArg Subtype.val (hcommMF ⟨y, hX₁MF hy⟩ ⟨a, ha⟩)
      have hle3 : rank ↥(MF M) < 3 := (inf_eq_left.mpr hMFcentr) ▸ hrank3
      -- ≥ 2: `O_p(M_F)` is abelian (`≤ M_F`) and noncyclic, so `2 ≤ pRank ≤ rank`.
      have hOpMF : opiCoreInG ({p} : Set ℕ) (MF M) ≤ MF M := opiCoreInG_le {p} (MF M)
      have hcommOp : ∀ x y : ↥(opiCoreInG ({p} : Set ℕ) (MF M)), x * y = y * x := fun x y =>
        Subtype.ext (by simpa using congrArg Subtype.val (hcommMF ⟨(x : G), hOpMF x.2⟩ ⟨(y : G), hOpMF y.2⟩))
      have hOpnc : ¬ IsCyclic ↥(opiCoreInG ({p} : Set ℕ) (MF M)) :=
        not_isCyclic_opiCore_mf_of_orderP_le_conj hG hM hp hgM hX₁card hX₁MF hX₁cMF
      have h2pRank : 2 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (MF M)) p :=
        two_le_pRank_of_comm_isPGroup_not_isCyclic hpOdd hcommOp
          (isPGroup_opiCoreInG_singleton (MF M)) hOpnc
      have hge2 : 2 ≤ rank ↥(MF M) :=
        le_trans (le_trans h2pRank (pRank_le_rank p))
          (rank_le_of_injective (Subgroup.inclusion_injective hOpMF))
      omega
    · -- non-abelian `M_F` ⟹ disjunct (c): the exponent condition (conjunct A, via the Frobenius
      -- divisibility engine + per-prime order-`q` witnesses) and cyclic `O_{p'}(M_F)` (conjunct B).
      refine Or.inr (Or.inr ⟨fun q _hq hqπ => ?_, ?_⟩)
      · -- conjunct A: `exp U ∣ q - 1` for each `q ∈ π(M_F)`.
        obtain ⟨Z, hZMF, hZcard, hMNZ, -, -⟩ :=
          exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF _hCGnotM
            hrank3 habel _hq hqπ
        exact typeF_exponent_dvd_sub_one_of_invariant_card td (by rw [td.H_eq]; exact hZMF)
          hZcard ((td.U0_le.trans td.U_le).trans hMNZ)
      · -- conjunct B: `∃ p ∈ π(M_F), IsCyclic O_{p'}(M_F)`.
        exact ⟨p, hp,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).1,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).2⟩

/-- **Type-`P` `V`-normalizer characterization** (the `normalizer_V` field of `TypePData`,
Peterfalvi (8.4); BG records it as the self-normalizing exceptional set `M = N_G(V)`): if
`W = W₁ ⊔ W₂` is cyclic and the exceptional set `V = W ∖ (W₁ ∪ W₂)` is a `TI`-subset relative to
`W`, then every nonempty `X ⊆ V` has normalizer exactly `W`.

This is the genuine reduction underlying the deep-looking `normalizer_V` field: `N_G(X) ≤ W` is the
`TI` property (a conjugate of an element of `X ⊆ V` lands back in `V`, forcing the conjugator into
`W`); `W ≤ N_G(X)` is abelianness of the cyclic `W` (every `w ∈ W` centralizes `X ⊆ W`, so fixes it
setwise).  Both inputs (`W = K ⊔ K*` cyclic and the `zTilde K K*` `TI` property) are supplied by
Theorem 14.7 (`typeP_duality`), so this lemma discharges `normalizer_V` once §14 lands. -/
theorem normalizer_eq_sup_of_isTISubset_of_isCyclic {W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2))
    {X : Set G} (hXne : X.Nonempty)
    (hXV : X ⊆ (↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) :
    Subgroup.normalizer X = W1 ⊔ W2 := by
  classical
  haveI : IsCyclic ↥(W1 ⊔ W2) := hWcyc
  letI : CommGroup ↥(W1 ⊔ W2) := IsCyclic.commGroup
  -- elements of the cyclic `W = W₁ ⊔ W₂` commute in `G`.
  have hcomm : ∀ a b : G, a ∈ W1 ⊔ W2 → b ∈ W1 ⊔ W2 → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(W1 ⊔ W2)) ⟨b, hb⟩)
  apply le_antisymm
  · -- `N_G(X) ≤ W`: a conjugate of `a ∈ X ⊆ V` lands in `V`, so the `TI` property forces `g ∈ W`.
    intro g hg
    obtain ⟨a, haX⟩ := hXne
    have h1 : g⁻¹ * a * g ∈ X := (Subgroup.mem_set_normalizer_iff''.mp hg a).mp haX
    refine hTI g ⟨g⁻¹ * a * g, hXV h1, ?_⟩
    have he : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [he]; exact hXV haX
  · -- `W ≤ N_G(X)`: `w ∈ W` centralizes `X ⊆ W` (abelian), so it fixes `X` setwise.
    intro w hw
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hhX
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw (hXV hhX).1]; group
      rw [hfix]; exact hhX
    · intro hconj
      have hhW : h ∈ W1 ⊔ W2 := by
        have hrw : h = w⁻¹ * (w * h * w⁻¹) * w := by group
        rw [hrw]
        exact mul_mem (mul_mem (inv_mem hw) (hXV hconj).1) hw
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw hhW]; group
      rwa [hfix] at hconj

/-- **Prop 16.1(b)--(d) forward bridge, shared core**: assemble the Peterfalvi type-`P` datum
`TypePData M` (mmd L4116/L4190, Peterfalvi (8.4)) from the BG-local structural facts.  This is the
single construction feeding *all three* of the `hP2II`/`hP1neIIIIV`/`hP1eqV` forward bridges of
`proposition_type_classification` (types II, III, IV, V all bundle a `TypePData`).

Following the gated-endpoint skeleton pattern (cf. `typeP_kstar_in_mf_of_inputs`), the deep
structural fields are taken as named hypotheses; their BG sources are:

* the derived-series complement `M = M' W₁`, `W = W₁ ⊔ W₂` cyclic, and the `zTilde` `TI` property
  (`hMcompl`/`hWcyc`/`hTI`) come from Theorem 14.7 (`typeP_duality`) with `W₁ = K`, `W₂ = K*`,
  `W = K ⊔ K*`;
* the **real Fitting** decomposition `F(M) = H ⊔ (U ⊓ C_M(H))` (Peterfalvi (8.5.a), issue 7008 — the
  LHS is `F(M)`, not `M_F`) and `M'' ≤ F(M)`, with `M_F` noncyclic (`hFiteq`/`hSDfit`/`hHncyc`) come
  from Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) and Corollary 15.6;
* the `M'`-internal complement `M' = H U` with `U` nilpotent and **normalized by `W₁`** (Peterfalvi
  (8.4.b); `U ⊴ M'` would force `U = 1`, issue 7008) — `hDcompl`/`hUnilp`/`hW1norm` — comes from
  Lemma 15.1 / Theorem A.

The genuinely *derived* (not renamed) fields are `W_eq` (definitional), `W1_cyclic`/`W2_cyclic`
(subgroups of the cyclic `W`), and `normalizer_V` (the `TI` + cyclic reduction
`normalizer_eq_sup_of_isTISubset_of_isCyclic`).  Sorry-free in its own body. -/
def typePData_of_inputs {M H U W1 W2 : Subgroup G}
    (hHeq : H = maxNilpotentNormalHall M)
    (hHle : H ≤ derivedInG M)
    (hUle : U ≤ derivedInG M)
    (hW1le : W1 ≤ M)
    (hW2le : W2 ≤ H ⊓ secondDerivedInAmbient M)
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hW1ne : W1 ≠ ⊥) (hW2ne : W2 ≠ ⊥)
    (hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W1.subgroupOf M))
    (hW1norm : W1 ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl :
      Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hHncyc : ¬ IsCyclic ↥H)
    (hSDfit : secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hCentW1 : ∀ x ∈ W1, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = W2)
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2)) :
    TypePData M := by
  haveI := hWcyc
  exact
    { H := H
      U := U
      W1 := W1
      W2 := W2
      W := W1 ⊔ W2
      H_eq := hHeq
      H_le := hHle
      U_le := hUle
      W1_le := hW1le
      W2_le := hW2le
      W_eq := rfl
      W_cyclic := hWcyc
      W1_nontrivial := hW1ne
      W2_nontrivial := hW2ne
      W1_cyclic := Subgroup.isCyclic_of_le (le_sup_left : W1 ≤ W1 ⊔ W2)
      W2_cyclic := Subgroup.isCyclic_of_le (le_sup_right : W2 ≤ W1 ⊔ W2)
      M_complement := hMcompl
      W1_normalizes_U := hW1norm
      U_nilpotent := hUnilp
      derived_complement := hDcompl
      H_noncyclic := hHncyc
      secondDerived_le_fitting := hSDfit
      fitting_eq := hFiteq
      centralizer_W1 := hCentW1
      normalizer_V := fun X hXne hXV =>
        normalizer_eq_sup_of_isTISubset_of_isCyclic hWcyc hTI hXne hXV }

/-- **The `W₂ = C_{M'}(W₁#)` centralizer law** (BG Theorem C / Peterfalvi (8.4), the `TypePData`
`centralizer_W1` field): for a type-`P` maximal subgroup with cyclic `κ`-Hall `K`, the `M'`-centralizer
of every `k ∈ K#` is exactly `K* = C_{M_σ}(K)`.  Sharpens Theorem A(5) (`C_M(k) = K ⊔ K*`,
`typeP_centralizer_kappaElement_eq`) by intersecting with `M'`: since `K* ≤ M'` and `K ⊓ M' = ⊥`
(the `M = M' ⋊ K` complement has coprime orders, Theorem 14.7(h)), the modular law gives
`M' ⊓ (K ⊔ K*) = K*`.  Discharges the `hCentW1` residual of `typePData_of_isTypeP_of_inputs`. -/
theorem typeP_derivedInG_inf_centralizer_kappaElement_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ K, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = Kstar := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- Theorem 14.7(h): `M = M' ⋊ K` complement (coprime orders), `K ⊔ K*` cyclic ⟹ `K` cyclic.
  obtain ⟨_hMcompl, hcop, _, ⟨_, _, _, _, hWcyc, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
  haveI : IsCyclic ↥(K ⊔ Kstar) := hWcyc
  haveI : IsCyclic ↥K := Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` (for the Theorem A(5) citation).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ⊓ M' = ⊥` (coprime `|K|`, `|M'|`).
  have hcop' : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
    rw [e1, e2] at hcop; exact hcop.symm
  have hKinfM' : K ⊓ derivedInG M = ⊥ :=
    Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop'
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- `K* ≤ M_σ ≤ M'`.
  have hKstarM' : Kstar ≤ derivedInG M := by
    rw [hKstar]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `K ≤ N(K*)`: `K* ≤ C(K)` (from `K* = M_σ ⊓ C(K)`), so `K ≤ C(K*) ≤ N(K*)`.
  have hKsubCK : Kstar ≤ Subgroup.centralizer (K : Set G) := by rw [hKstar]; exact inf_le_right
  have hKN : K ≤ Subgroup.normalizer (Kstar : Set G) := by
    refine le_trans (fun k hk => ?_) (Subgroup.centralizer_le_normalizer (Kstar : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsCK := hKsubCK hs
    rw [Subgroup.mem_centralizer_iff] at hsCK
    exact (hsCK k hk).symm
  -- `M' ⊓ C(x) = M' ⊓ (M ⊓ C(x)) = M' ⊓ (K ⊔ K*)`, then Dedekind ⟹ `= K*`.
  intro x hx hx1
  have hA5 := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU x hx hx1
  have hredux : derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = derivedInG M ⊓ (K ⊔ Kstar) := by
    rw [← hA5, ← inf_assoc, inf_eq_left.mpr hM'M]
  rw [hredux]
  -- Dedekind (`eq_sup_inf_of_le_normalizer`): `H = K* ⊔ (H ⊓ K)`, with `H ⊓ K ≤ M' ⊓ K = ⊥`.
  have hKstarH : Kstar ≤ derivedInG M ⊓ (K ⊔ Kstar) := le_inf hKstarM' le_sup_right
  have hHle : derivedInG M ⊓ (K ⊔ Kstar) ≤ Kstar ⊔ K := by rw [sup_comm]; exact inf_le_right
  have hHinfK : (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    calc (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K ≤ derivedInG M ⊓ K := inf_le_inf_right K inf_le_left
      _ = ⊥ := by rw [inf_comm]; exact hKinfM'
  rw [eq_sup_inf_of_le_normalizer hKN hKstarH hHle, hHinfK, sup_bot_eq]

/-- **Prop 16.1(b)--(d) forward bridge — `TypePData M` from BG-local `IsTypeP M`** (gated-endpoint).
Constructs the shared Peterfalvi type-`P` datum (`TypePData M`) for a type-`P` maximal subgroup with
a nontrivial `κ(M)`-Hall `K`, discharging *twelve* of the eighteen `typePData_of_inputs` fields from
the proven §14/§15 structure and gating only on the genuinely-deep **`M_F`-internal Fitting core**
(BG Corollary 15.5 / Lemma 15.1):

* discharged (`typeP_duality` = Theorem 14.7: `hMcompl`/`hWcyc`/`hTI`; `typeP_kstar_in_mf` = Corollary
  15.6: `hW2ne`/`hW2le`/`hHncyc`; the `W₂ = C_{M'}(W₁#)` centralizer law `hCentW1`
  (`typeP_derivedInG_inf_centralizer_kappaElement_eq` = Theorem A(5) + Dedekind); plus
  `hHeq`/`hHle`/`hW1le`/`hW1ne`), with `W₁ = K`, `W₂ = K*`, `W = K ⊔ K*`, `H = M_F`;
* gated (named residuals): the `M_F`-internal complement `U` (`M' = M_F ⊔ U`, `U` nilpotent and
  normalized by `W₁` — `hUle`/`hKnorm`/`hUnilp`/`hDcompl`; issue 7008: `U ⊴ M'` is unfaithful) and the
  real Fitting decomposition `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hSDfit`/`hFiteq`).

This single construction feeds all three of `hP2II`/`hP1neIIIIV`/`hP1eqV` (types II/III/IV/V bundle a
`TypePData`); the gated residuals are exactly the `M_F`-internal structure not present in
`typeP_auxiliary_structure`'s `M' = U M_σ` decomposition. -/
noncomputable def typePData_of_isTypeP_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hUle : U ≤ derivedInG M)
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G))) :
    TypePData M := by
  classical
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstar
  -- Theorem 14.7 (`typeP_duality`): the `M'`-complement (`.1`), `K ⊔ K*` cyclic and `zTilde` TI
  -- (extracted in `Prop`-valued `have` blocks — the `∃!` witness cannot be eliminated into the
  -- `def`'s `Type`).
  have hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    (typeP_duality hG hM hP hKM hK hKstar).1
  have hWcyc : IsCyclic ↥(K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, h, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  have hTI : IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, _, h, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  -- Corollary 15.6 (`typeP_kstar_in_mf`): `K* ≠ ⊥`, `K* ≤ M_F`, `K* ≤ M''`, `M_F` noncyclic.
  have hk := typeP_kstar_in_mf hG hM hP hKM hK hKstar
  exact typePData_of_inputs (H := maxNilpotentNormalHall M) (U := U) (W1 := K) (W2 := Kstar)
    rfl (maxNilpotentNormalHall_le_derived hG hM) hUle hKM (le_inf hk.2.2.1 hk.2.2.2.1)
    hWcyc hKne hk.1 hMcompl hKnorm hUnilp hDcompl hk.2.2.2.2 hSDfit hFiteq
    (typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar) hTI

open scoped IsMulCommutative in
/-- **`TypePData M` for a type-`P₂` maximal subgroup** — the carrier-constructibility milestone for
Proposition 16.1's forward bridges: *every* type-`P₂` maximal subgroup carries a Peterfalvi
type-`P` datum, `sorry`-free.

Assembled from the matched `κ`-Hall / `(κ ∪ σ)'`-Hall pair
(`typeP2_exists_matched_kappa_hall_pair`, supplying an abelian `U` with `K ≤ N_G(U)`) and the
`M_F`-internal Fitting decomposition (`typeP2_mf_internal_fitting_decomposition`, supplying the
three deep `M'`-complement/Fitting fields `hDcompl`/`hSDfit`/`hFiteq`), fed to the gated-endpoint
constructor `typePData_of_isTypeP_of_inputs`.  This closes the deep `M_F`-internal residuals that
were the linchpin of all three (`hP2II`/`hP1neIIIIV`/`hP1eqV`) forward bridges; the type-`P₂` bridge
`hP2II` now reduces to the type-`II` last mile (`isTypeII_of_typePData`: `N_G(U) ⊄ M` via
Corollary 14.12, and the type-`F` structure of `M'`). -/
noncomputable def typePData_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    TypePData M := by
  classical
  -- Extract the matched pair via `Exists.choose` (the goal `TypePData M` is `Type`-valued, so
  -- `obtain`/`rcases` on the `Prop`-existential cannot eliminate into it).
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hUcomm : IsMulCommutative ↥U := hspec.2.2.2.2.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hspec.2.2.2.2.2.2
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hM'eq := (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  haveI := hUcomm
  have hUnilp : Group.IsNilpotent ↥U := inferInstance
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  exact typePData_of_isTypeP_of_inputs hG hM hP hKM hKne hK hUle hKnorm hUnilp
    hdec.1 hdec.2.1 hdec.2.2

/-- **For a type-`P₁` maximal subgroup with `M_F = M_σ`, `F(M) = M_F`** (the type-V Fitting
collapse, Coq `BGsection16` `typePfacts` `U = 1` branch).  Corollary 15.5(d)
(`fitting_decomposition`) gives `F(M) ≤ M'` since `M` is type `P` (not type `F`); `M' = M_σ`
(`isTypeP1_derivedInG_eq_Msigma`) `= M_F` (hypothesis), and `M_F ≤ F(M)` always
(`maxNilpotentNormalHall_le_fittingInG`), so `F(M) = M_F`.  This discharges the deepest field
(`fitting_eq`) of the type-V `TypePData`, where `U = ⊥` makes `F(M) = M_F ⊔ (⊥ ⊓ C_M(M_F)) = M_F`. -/
theorem fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    S15.fittingInAmbient M = S15.MF M := by
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFle, _⟩ := S15.fitting_decomposition hG hM
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  refine le_antisymm ?_ (S15.maxNilpotentNormalHall_le_fittingInG M)
  exact (hFle hnotF).trans_eq (hM'σ.trans hmf.symm)

open scoped IsMulCommutative in
/-- **`TypePData M` for a type-`P₁` maximal subgroup with `M_F = M_σ`** — the type-V
carrier-constructibility milestone: such a maximal subgroup carries a Peterfalvi type-`P` datum with
*trivial* complement `U = ⊥`, `sorry`-free.

For type `P₁`, `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`); with `M_F = M_σ` this gives
`M' = M_F`, so the `M_F`-internal complement collapses to `U = ⊥` (Coq `typePfacts`:
`M_F = M_σ ⟺ U = 1`).  Every `U`-field of `typePData_of_isTypeP_of_inputs` then trivializes:
`U ⊴ M'` and `K ≤ N_G(U)` are vacuous (`U = ⊥` normal), `hDcompl` is `IsComplement' ⊤ ⊥`
(`M_F.subgroupOf M' = ⊤` since `M' = M_F`), `hSDfit` is `M'' ≤ M' = M_F`, and `hFiteq` is the
type-V Fitting collapse `F(M) = M_F`
(`fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma`).  Feeds the `hP1eqV` bridge:
`isTypeV_of_typePData` reduces type V to the genuinely-deep Peterfalvi (8.8) `alternative`
trichotomy on `M_F`. -/
noncomputable def typePData_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    TypePData M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` (the cyclic `W₁ = K`).  The goal `TypePData M` is `Type`-valued,
  -- so we extract via `Exists.choose` (not `obtain`, which cannot eliminate a `Prop` into `Type`).
  have hKex := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := hKex.choose.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le hKex.choose
  have hKeq : K.subgroupOf M = hKex.choose :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective hKex.choose
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
    rw [hKeq]; exact hKex.choose_spec
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `M' = M_σ = M_F`, `F(M) = M_F`.
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hM'MF : derivedInG M = maxNilpotentNormalHall M := hM'σ.trans hmf.symm
  -- Build with `U = ⊥`; every `U`-field trivializes.
  refine typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK (U := ⊥) bot_le ?_ ?_ ?_ ?_ ?_
  · -- `hKnorm`: `K ≤ N_G(⊥) = ⊤`.
    exact le_top.trans_eq (Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))).symm
  · -- `hUnilp`: `⊥` is nilpotent.
    infer_instance
  · -- `hDcompl`: `IsComplement' ⊤ ⊥` (`M_F.subgroupOf M' = ⊤` since `M' = M_F`).
    rw [Subgroup.bot_subgroupOf,
      Subgroup.subgroupOf_eq_top.mpr (le_of_eq hM'MF)]
    exact Subgroup.isComplement'_top_left.mpr rfl
  · -- `hSDfit`: `M'' ≤ M_F` (`M'' ≤ M' = M_F`).
    rw [bot_inf_eq, sup_bot_eq]
    exact (Subgroup.map_subtype_le _ : secondDerivedInAmbient M ≤ derivedInG M).trans_eq hM'MF
  · -- `hFiteq`: `F(M) = M_F` (type-V Fitting collapse).
    rw [bot_inf_eq, sup_bot_eq]
    exact fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf

/-- **`TypePData M` for a type-`P₁` maximal subgroup with `M_F ≠ M_σ`** — the type III/IV
carrier-constructibility milestone: every such maximal subgroup carries a Peterfalvi type-`P` datum,
`sorry`-free.

The `M_F`-internal complement `U` (`M' = M_σ = M_F ⊔ U`, `M_F ⊓ U = ⊥`, `K ≤ N_G(U)`) is supplied by
`exists_typeP1_mf_complement` (`K`-invariant Schur–Zassenhaus); the four deep `U`/Fitting fields are
the new BG Corollary 15.5 lemmas: `U` is nilpotent (`isNilpotent_complement_of_isTypeP1_mf_ne_msigma`,
`U ≅ M_σ/M_F`), `U` is a genuine `M'`-complement (`isComplement'_mf_complement_of_sup_inf`), and the
Fitting decomposition `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`fittingInAmbient_eq_mf_sup_inf_of_…`, whence
`M'' ≤ F(M)` gives `hSDfit`).  Fed to the gated-endpoint `typePData_of_isTypeP_of_inputs`.  Mirrors
`typePData_of_isTypeP2`; together they construct the type-`P` datum for every non-type-V type-`P`
maximal, leaving the `hP1neIIIIV` bridge gated only on the type III/IV last mile `N_G(U) ⊆ M`. -/
noncomputable def typePData_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    TypePData M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` (`Type`-valued goal: extract via `Exists.choose`).
  have hKex := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := hKex.choose.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le hKex.choose
  have hKeq : K.subgroupOf M = hKex.choose :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective hKex.choose
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hKex.choose_spec
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- The `K`-invariant `M_F`-complement `U` in `M' = M_σ` (`Type`-valued goal: `Exists.choose`).
  have hUex := exists_typeP1_mf_complement hG hM hP1 hKM hK
  set U := hUex.choose with hUdef
  have hUspec := hUex.choose_spec
  have hUle : U ≤ derivedInG M := hUspec.1
  have hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M := hUspec.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hUspec.2.2.1
  have hinf : maxNilpotentNormalHall M ⊓ U = ⊥ := hUspec.2.2.2
  -- The four deep `U`/Fitting fields (BG Corollary 15.5).
  have hUnilp : Group.IsNilpotent ↥U :=
    isNilpotent_complement_of_isTypeP1_mf_ne_msigma hG hM hP1 hne hsup hinf
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hFiteq := fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma hG hM hP1 hsup hinf
  have hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    obtain ⟨_, -, -, -, hM''F, -, -, -, -, -, -, -⟩ := S15.fitting_decomposition hG hM
    rw [← hFiteq]; exact hM''F
  exact typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK hUle hKnorm hUnilp hDcompl hSDfit hFiteq

/-- **Prop 16.1 forward bridge, type III/IV last mile** (Peterfalvi (8.7)): a type-`P` datum whose
`U`-factor has its normalizer inside `M` is of type III or IV, according as `U` is abelian or not.
This is the clean part of the `hP1neIIIIV` bridge — no deep `alternative`/`derived_typeF` content,
only the decidable `IsMulCommutative ↥U` split distinguishing III (`U` abelian) from IV. -/
theorem isTypeIII_or_IV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hnorm : Subgroup.normalizer (data.U : Set G) ≤ M) :
    IsTypeIII M ∨ IsTypeIV M := by
  classical
  by_cases hU : IsMulCommutative ↥data.U
  · exact Or.inl ⟨{ typeP := data, common := hcommon, U_commutative := hU, normalizer_le := hnorm }⟩
  · exact Or.inr
      ⟨{ typeP := data, common := hcommon, U_not_commutative := hU, normalizer_le := hnorm }⟩

/-- **Prop 16.1 forward bridge, type II last mile** (Peterfalvi (8.6)): a type-`P` datum with `U`
abelian, `N_G(U) ⊄ M`, and the derived subgroup `M'` of type `F` (with `F(M') = H`) is of type II.
The `derived_typeF` field is the genuinely deep named residual (the type-`F` structure of `M'`). -/
theorem isTypeII_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hUcomm : IsMulCommutative ↥data.U)
    (hnorm : ¬ Subgroup.normalizer (data.U : Set G) ≤ M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = data.H) :
    IsTypeII M :=
  ⟨{ typeP := data, common := hcommon, U_commutative := hUcomm,
     normalizer_not_le := hnorm, derived_typeF := hderF, derived_fitting_eq := hderfit }⟩

open scoped IsMulCommutative in
/-- **Prop 16.1 forward bridge `hP2II`, reduced to the `M'`-type-`F` residual** — a type-`P₂`
maximal subgroup whose derived subgroup `M'` is of type `F` (with `F(M') = M_F`) is of type II.

This discharges *every* `isTypeII_of_typePData` input that is BG-local for the type-`P₂` case,
leaving exactly the genuinely-deep `M'`-type-`F` structure (`hderF`/`hderfit`, Peterfalvi (8.6)) as
hypotheses.  Notably **the whole `TypePNontrivialCore` (`hcommon`) is lane-local, not lane-b**:
`U ≠ ⊥` from the matched pair, `|W₁| = |K|` prime *and* the `M_σ`-`TI` condition both from
Proposition 14.2(g) (`typeP_structure`, proved) — `M_F = M_σ` for type `P₂`, so its `sharp`-`TI`
*is* the `σ#`-`TI`.  (Correcting the stale belief that `|W₁|` prime needs the lane-b (10.11)
`theorem88_caseB_prime_orders`; that is the *partner* primality, not the type-`P₂` `κ`-Hall's.)
`N_G(U) ⊄ M` is Corollary 14.12 (`typeP2_neighbor_is_typeF`) applied to a Sylow `r`-subgroup of the
matched `U`; the `TypePData` itself is `typePData_of_isTypeP2`.  The single remaining gate for the
`hP2II` bridge of `proposition_type_classification` is thus the type-`F` structure of `M'`. -/
theorem isTypeII_of_isTypeP2_of_derived_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hUcomm : IsMulCommutative ↥U := hspec.2.2.2.2.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hspec.2.2.2.2.2.2
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hM'eq := (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  haveI := hUcomm
  have hUnilp : Group.IsNilpotent ↥U := inferInstance
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  -- Proposition 14.2(g): `|K| = q` prime and `M_σ#` is `TI` (the `M_F#`-`TI` since `M_F = M_σ`).
  obtain ⟨_, q, hqp, hKq, hMσTI⟩ := (S14.typeP_structure hG hM hP hKM hK rfl hU).2.2.2.2.1 hP2
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥U) (⟨b, hb⟩ : ↥U))
  -- `N_G(U) ⊄ M`: Corollary 14.12 applied to a Sylow `r`-subgroup `R ≤ U` (`r ∈ π(U)`, `U ≠ ⊥`).
  have hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M := by
    obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd
      (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
    have hrπU : r ∈ S14.piSet U := Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩
    obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U) ({r} : Set ℕ)
    intro hNU
    obtain ⟨H, _, _, _, _, hHnorm⟩ := S14.typeP2_neighbor_is_typeF hG hM hP2 hKM hUM hK hU hUab
      hrπU (Subgroup.map_subtype_le R')
      (by rw [show (R'.map U.subtype).subgroupOf U = R' from
        Subgroup.comap_map_eq_self_of_injective U.subtype_injective R']; exact hR') hKnorm
    exact hHnorm (le_trans inf_le_right hNU)
  refine isTypeII_of_typePData
    (typePData_of_isTypeP_of_inputs hG hM hP hKM hKne hK hUle hKnorm hUnilp hdec.1 hdec.2.1 hdec.2.2)
    ⟨?_, ?_, ?_⟩ ?_ ?_ hderF ?_
  · show U ≠ ⊥; exact hUne
  · show (Nat.card ↥K).Prime; rw [hKq]; exact hqp
  · rw [hMFMσ]; exact hMσTI
  · show IsMulCommutative ↥U; exact hUcomm
  · show ¬ Subgroup.normalizer (U : Set G) ≤ M; exact hnorm
  · show maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M; exact hderfit

/-- **Prop 16.1 / Peterfalvi (8.6.b II), the `M'`-type-`F` residual (`hderF`), unconditional** — the
derived subgroup `M' = M^{(1)}` of a type-`P₂` maximal `M` is itself of type `F`.

Structurally `M' = M_σ ⋊ U` is the type-`F`-shaped `M_σ ⋊ (complement)` inside `M` — exactly as the
type-`F` *maximal* of `typeFData_of_kappa_eq_bot` is `M = M_σ ⋊ U` — so the *same* data assemble: the
`M_σ ⋊ U` complement (`typeP2_mf_internal_fitting_decomposition`), the abelian inertia `U₁` and the
Frobenius factor `M_σ ⋊ U₀` (Lemma 15.1(d)(e), `typeP_auxiliary_structure`), and the crucial `F`-core
identity `(M')_F = M_σ = M_F` (`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`).  This last
identity is the Coq `defM'F` step (`Fcore_max` + Hall transitivity): it needs **no** `τ₂(M) = ∅`
hypothesis (which is in fact false for some type-`P₂` `M`, cf. Corollary 15.9). -/
theorem isTypeF_derivedInG_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K]
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF (derivedInG M) := by
  classical
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hMFM' : maxNilpotentNormalHall M = maxNilpotentNormalHall (derivedInG M) :=
    hMFMσ.trans (maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK).symm
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  obtain ⟨_, _, _, _, hconj5, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := maxNilpotentNormalHall M
    U := U
    U1 := centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := hMFM'
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := maxNilpotentNormalHall_le_derived hG hM
    U_le := hUle
    U1_le := by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left
    U0_le := hU0U
    complement := hdec.1
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
      exact ⟨maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := by rw [hMFMσ, sup_comm]; exact hfrob }⟩
  · -- `U1_normal`: `U`-conjugation permutes the generators `C_U(x)` of `centralizerGeneratedBySigma`.
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]

/-- **BG Proposition 16.1(b) forward bridge `hP2II`, complete and unconditional** — *every*
type-`P₂` maximal subgroup is of type II.  The two residuals of
`isTypeII_of_isTypeP2_of_derived_typeF` are discharged: `hderF` by `isTypeF_derivedInG_of_isTypeP2`,
and `hderfit` (`(M')_F = M_F`, both `= M_σ`) by
`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`.  No `τ₂(M) = ∅` gate (the earlier
reduction to BG Theorem 15.8 was unnecessary — and `τ₂(M) = ∅` is false for some type-`P₂` `M`,
cf. Corollary 15.9). -/
theorem isTypeII_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  -- `K` cyclic (Theorem A(2) / Lemma 15.1(b), `typeP_auxiliary_structure` conjunct 2).
  obtain ⟨_, hKcyc, _⟩ := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  haveI := hKcyc
  -- `hderfit`: `(M')_F = M_F` (both `= M_σ`).
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M := by
    rw [maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK, hMFMσ]
  -- `hderF`: `M'` is of type `F`.
  have hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M) :=
    isTypeF_derivedInG_of_isTypeP2 hG hM hP2 hKM hUM hKne hK hU hUne
  exact isTypeII_of_isTypeP2_of_derived_typeF hG hM hP2 hderF hderfit

/-- **Existence of the signalizer maximal with Peterfalvi type `I`/`II`** (existence half of
Peterfalvi (8.13)): for an escaping `σ`-sharp element `x` (`x ∈ M_σ^#` with more than one
`σ`-maximal), the proven signalizer structure `signalizer_structure_of_mem_sigmaSharp` supplies a
maximal subgroup `N` over `C_G(x)` whose BG type-`F`/`P₂` dichotomy converts
(`isTypeI_of_isTypeF`/`isTypeII_of_isTypeP2`) to the Peterfalvi type `I`/`II`.  This is the existence
half of (8.13)'s `∃! L, C_G(x) ≤ L ∧ (IsTypeI ∨ IsTypeII)` conclusion; the uniqueness half is the
containing-maximal uniqueness `ℳ(C_G(x)) = {N[x]}` (Theorem D). -/
theorem exists_maximal_centralizer_le_typeI_or_typeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  obtain ⟨N, ⟨hNmax, hCN, _, _, _, hFP2, _⟩, _⟩ :=
    signalizer_structure_of_mem_sigmaSharp hG hM hxM hgt
  refine ⟨N, hNmax, hCN, ?_⟩
  rcases hFP2 with hF | hP2
  · exact Or.inl (isTypeI_of_isTypeF hG hNmax hF)
  · exact Or.inr (isTypeII_of_isTypeP2 hG hNmax hP2)

/-- **Prop 16.1 forward bridge, type V last mile** (Peterfalvi (8.8)): a type-`P` datum with
`U = ⊥` and the Peterfalvi (8.8) trichotomy on `H = M_F` is of type V.  The `alternative`
disjunction is the deep named residual (BG §15.7(c) / Peterfalvi (8.8)). -/
theorem isTypeV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hUbot : data.U = ⊥)
    (halt :
      IsTISubset (sharpSubgroup data.H) (Subgroup.normalizer (data.H : Set G)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥data.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ data.H)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥(opiCoreInG {p} data.H) = p ^ 3 ∧ Nat.card ↥data.W1 ∣ p + 1 ∧
        IsCyclic ↥(opiCoreInG {p}ᶜ data.H))) :
    IsTypeV M :=
  ⟨{ typeP := data, U_eq_bot := hUbot, alternative := halt }⟩

/-- **`M_σ`-centralizer of a `κ`-element is `K*`** (the prime-action constancy of fixed points): for
a type-`P` maximal `M` with Hall `κ`-subgroup `K` and `K* = M_σ ⊓ C(K)`, every `k ∈ K#` has
`C_{M_σ}(k) = K*`.  `K` acts *primely* on `M_σ` (Proposition 14.2, `typeP_structure` conjunct 1,
`ActsPrimeOn (M_σ) K`), so the fixed subgroup `C_{M_σ}(k) = fixedByElement (M_σ) k` equals
`fixedBy (M_σ) K = M_σ ⊓ C(K) = K*` for every nonidentity `k ∈ K`. -/
theorem centralizer_msigma_kappaElement_eq_kstar [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] {k : G} (hk : k ∈ K) (hk1 : k ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({k} : Set G) = Kstar := by
  have hprime : OddOrder.BG.Ch3.S13.ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K :=
    (S14.typeP_structure hG hM hP hKM hK hKstar hU).1
  -- `fixedByElement (M_σ) k = fixedBy (M_σ) K`, both defeq to the centralizer forms.
  have heq := hprime k hk hk1
  rw [hKstar]
  exact heq

/-- **`|K| ∣ p - 1` from `K` acting Frobenius on an `M`-normal order-`p` subgroup** (the
divisibility engine for type-V disjunct (e2), Coq `regZq_dv_q1`): if the Hall `κ`-subgroup `K`
normalizes an order-`p` subgroup `Z ≤ M_σ` with `Z ⊓ K* = ⊥`, then `K` acts on `Z` as a Frobenius
group — every `k ∈ K#` centralizes only `1` in `Z`, since `C_{M_σ}(k) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`) and `Z ⊓ K* = ⊥` — so `card_dvd_sub_one_of_isFrobeniusAction`
gives `|K| ∣ |Z| - 1 = p - 1`. -/
theorem kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Z : Subgroup G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    (hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M) (hZcard : Nat.card ↥Z = p)
    (hKNZ : K ≤ Subgroup.normalizer (Z : Set G)) (hZK : Z ⊓ Kstar = ⊥) :
    Nat.card ↥K ∣ p - 1 := by
  classical
  letI : MulDistribMulAction ↥K ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hKNZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥K ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    have hconj : (u : G) * (z : G) * (u : G)⁻¹ = (z : G) := by
      rw [← h1]; exact congrArg Subtype.val hfix
    have hcomm : (u : G) * (z : G) = (z : G) * (u : G) := mul_inv_eq_iff_eq_mul.mp hconj
    have huK1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hzKstar : (z : G) ∈ Kstar := by
      rw [← centralizer_msigma_kappaElement_eq_kstar hG hM hP hKM hK hKstar hU u.2 huK1]
      exact Subgroup.mem_inf.mpr ⟨hZMσ z.2,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx; exact hcomm)⟩
    have hz1 : (z : G) = 1 := by
      have hmem : (z : G) ∈ Z ⊓ Kstar := Subgroup.mem_inf.mpr ⟨z.2, hzKstar⟩
      rw [hZK, Subgroup.mem_bot] at hmem; exact hmem
    exact hz (Subtype.ext hz1)
  have hdvd := OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rwa [hZcard] at hdvd

/-- **`K` acts faithfully on `P = O_p(M_F)` in the type-V Singer case** (Coq `defKs`/`defZP`:
`K* = Z` forces `C_K(P) = 1`).  For a type-`P₁` maximal `M` with Hall `κ`-subgroup `K`,
`K* = M_σ ⊓ C(K)`, and an order-`p` subgroup `Z ≤ K*` with `X₁ ⊄ Z` (the non-TI witness `X₁` of order
`p`, `X₁ ≤ M_F`), the centralizer of `P` in `K` is trivial.

A nonidentity `x ∈ K ⊓ C_G(P)` centralizes `P ⊇ X₁`, so `X₁ ≤ M_σ ⊓ C_G(x) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`).  But `K* = Z`: `|K*|` is prime
(`kstar_card_prime_of_inputs`), `Z ≤ K*`, and `|Z| = p`, so `|K*| = p` and `Z = K*`.  Hence
`X₁ ≤ Z`, contradicting `X₁ ⊄ Z`.  This is the faithfulness input `K ⊓ C_G(P) = ⊥` to
`pRank_opiCore_le_two_of_kappaHall` (`rPle2`) for the type-V disjunct-3 (Singer/`SL₂(p)`) case. -/
theorem kappaHall_inf_centralizer_opiCore_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    {p : ℕ} {X₁ Z : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hZKstar : Z ≤ Kstar) (hZcard : Nat.card ↥Z = p) (hX₁notZ : ¬ X₁ ≤ Z) :
    K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  -- `K* = Z`: `|K*|` prime, `Z ≤ K*`, `|Z| = p`.
  have hKstarPrime : (Nat.card ↥Kstar).Prime :=
    S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have hKstarEqZ : Kstar = Z := by
    have hdvd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
    have hcard : Nat.card ↥Kstar = p := ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hdvd).symm
    exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hcard.trans hZcard.symm))).symm
  -- `X₁ ≤ P` (`p`-subgroup of the nilpotent `M_F`).
  haveI hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- A nonidentity `x ∈ K ⊓ C_G(P)` forces `X₁ ≤ K* = Z`, contradicting `X₁ ⊄ Z`.
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxK, hxCP⟩ := Subgroup.mem_inf.mp hx
  refine hX₁notZ ?_
  rw [← hKstarEqZ,
    ← centralizer_msigma_kappaElement_eq_kstar hG hM hP1.1 hKM hK hKstar hU hxK hx1]
  refine le_inf (hX₁MF.trans (S15.maxNilpotentNormalHall_le_Msigma hG hM)) (fun g hg => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Subgroup.mem_centralizer_iff.mp hxCP g (hX₁P hg)).symm

/-- **`M_F` is non-abelian for a type-V maximal** (the abelian-`H` exclusion of Coq
`nonTI_Fitting_structure`, the `P1maxM` branch): a type-`P₁` maximal subgroup `M` with `M_F = M_σ`
has non-abelian `M_F`.  The type-`P` datum's `W₂ = C_{M'}(W₁#)` is nontrivial (`W2_nontrivial`) and
lies in `M''` (`W2_le`); but `M' = M_σ = M_F` here, so `M'' = (M_F)'`, whence `(M_F)' ⊇ W₂ ≠ ⊥`,
i.e. `M_F` is non-abelian.  (Equivalently: were `M_F` abelian, `M'' = ⊥` would force `W₂ = ⊥`.) -/
theorem not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    ¬ IsMulCommutative ↥(S15.MF M) := by
  intro hab
  haveI := hab
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  -- `M' = M_σ = M_F`, so `M'' = (M_F)' = ⊥` (were `M_F` abelian).
  have hM'MF : derivedInG M = S15.MF M :=
    (isTypeP1_derivedInG_eq_Msigma hG hM hP1).trans hmf.symm
  have hM''bot : secondDerivedInAmbient M = ⊥ := by
    rw [secondDerivedInAmbient, hM'MF,
      show derivedInG (S15.MF M) = (commutator ↥(S15.MF M)).map (S15.MF M).subtype from rfl,
      commutator_eq_bot, Subgroup.map_bot]
  exact data.W2_nontrivial (le_bot_iff.mp ((data.W2_le.trans inf_le_right).trans hM''bot.le))

/-- **Common part of the Peterfalvi (8.8) trichotomy for type V** (Coq `cycHp'` + non-TI witness):
a type-`P₁` maximal `M` with `M_F = M_σ` and `¬FittingIsTI M` has a prime `p ∈ π(M_F)` with cyclic
`p'`-core `O_{p'}(M_F)` — the shared conclusion of disjuncts `(e2)`/`(e3)` of BG Theorem 15.7(e).
`M_F` is non-abelian (`not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma`); the non-TI witness
`X₁ ≤ M_σ = M_F` with `C_G(X₁) ⊄ M` (`exists_inf_conj_fitting_orderP_witness`) then feeds the
`cycHp'` building block `typeF_nonabelian_cyclic_opiCore_compl`.  The remaining `|W₁| ∣ p ∓ 1`
divisibility (which distinguishes disjunct 2 from disjunct 3) is the genuinely-deep `W₁`-action
residual. -/
theorem exists_prime_cyclic_opiCore_compl_of_isTypeV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    (hnotTI : ¬ S15.FittingIsTI M) :
    ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥(S15.MF M)).primeFactors ∧
      IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (S15.MF M)) := by
  have hnab := not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf
  obtain ⟨g, p, X₁, -, hp, -, hX₁card, hX₁Mσ, -, hCGnotM, -⟩ :=
    S15.exists_inf_conj_fitting_orderP_witness hG hM hnotTI
  -- `X₁ ≤ M_σ = M_F` (`mf_eq_msigma_of_not_fittingIsTI`).
  have hX₁MF : X₁ ≤ S15.MF M := by
    rw [S15.mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI]; exact hX₁Mσ
  obtain ⟨hpπ, hcyc⟩ :=
    S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab
  exact ⟨p, hp, hpπ, hcyc⟩

/-- **`O_p(M_F)` is narrow once its `p`-rank reaches 3** (BG Theorem 15.7(e), the narrow input for
the `r(P) ≤ 2` step of the type-V Singer case).  For `P = O_p(M_F)` with `pRank P ≥ 3`, the order-`p`
non-TI witness `X₁ ≤ M_F` whose `M_F`-centralizer has rank `< 3` (the `E1X_facts` rank bound from
`exists_inf_conj_fitting_orderP_witness`) realizes the narrow characterization
`narrow_iff_exists_card_prime_centralizer_pRank_le_two`: `X₁ ≤ P`
(`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`) and `C_P(X₁) = (C_G(X₁)).subgroupOf P` has
`pRank ≤ rank(M_F ⊓ C_G(X₁)) < 3` (it embeds into `M_F ⊓ C_G(X₁)` as `P ≤ M_F`).  No Sylow/`β`
plumbing is needed: the `pRank ≥ 3` hypothesis is exactly the contradiction branch of `r(P) ≤ 2`. -/
theorem isNarrow_opiCore_of_three_le_pRank [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (h3 : 3 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p) :
    OddOrder.GroupTheory.IsNarrow p ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPMF : P ≤ S15.MF M := opiCoreInG_le _ _
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  haveI hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  rw [OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two hpodd hPpg h3]
  refine ⟨X₁.subgroupOf P,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁P).toEquiv).trans hX₁card, ?_⟩
  -- `C_{↥P}(X₁.subgroupOf P) = (C_G(X₁)).subgroupOf P`.
  have himg_set : (P.subtype : ↥P → G) '' (↑(X₁.subgroupOf P) : Set ↥P) = (X₁ : Set G) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hX₁P]
  have hcent : Subgroup.centralizer (↑(X₁.subgroupOf P) : Set ↥P)
      = (Subgroup.centralizer (X₁ : Set G)).subgroupOf P := by
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, himg_set]
  rw [hcent]
  -- `↥((C_G(X₁)).subgroupOf P)` embeds into `M_F ⊓ C_G(X₁)` (image is `P ⊓ C_G(X₁) ≤ M_F ⊓ C_G(X₁)`).
  have hsub : ((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype
      ≤ S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G) := by
    simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact le_inf (inf_le_left.trans hPMF) inf_le_right
  calc pRank ↥((Subgroup.centralizer (X₁ : Set G)).subgroupOf P) p
      ≤ pRank ↥(((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).injective
    _ ≤ pRank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) p :=
        pRank_le_of_injective (Subgroup.inclusion_injective hsub)
    _ ≤ rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := pRank_le_rank p
    _ ≤ 2 := by omega

/-- **`r(O_p(M_F)) ≤ 2` for the type-V Singer case** (BG Theorem 15.7(e), Coq `rPle2`).  A
`κ`-Hall `K` (cyclic, `p'`, normalizing `P = O_p(M_F)`) that acts *faithfully* on `P`
(`K ⊓ C_G(P) = ⊥`) with `|K| ∤ p − 1` forces `pRank P ≤ 2`: were `pRank P ≥ 3`, `P` would be narrow
(`isNarrow_opiCore_of_three_le_pRank`), and BG Theorem 5.5(b) (`solvableAut_of_narrow`, applied to
the faithful `φ : K → MulAut P`) would give that every `p'`-element of `K` has order dividing
`p − 1`; the cyclic generator of `K` then yields `|K| ∣ p − 1`, contradicting `|K| ∤ p − 1`.

The faithfulness `K ⊓ C_G(P) = ⊥` is the `defZP`/`Kstar = Z(P)` content of the Singer case
(supplied separately). -/
theorem pRank_opiCore_le_two_of_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ K : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    [IsCyclic ↥K] (hKp' : ¬ p ∣ Nat.card ↥K)
    (hKnormP : K ≤ Subgroup.normalizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G))
    (hKfaithful : K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥)
    (hKp1 : ¬ Nat.card ↥K ∣ p - 1) :
    pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  haveI : IsSolvable ↥K := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
    refine isSolvable_of_comm fun a b => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm]
  by_contra hcon
  rw [not_le] at hcon
  have h3 : 3 ≤ pRank ↥P p := hcon
  have hPnarrow : OddOrder.GroupTheory.IsNarrow p ↥P :=
    isNarrow_opiCore_of_three_le_pRank hG hM hp hpodd hX₁card hX₁MF hrank3 h3
  -- The faithful conjugation action `φ : ↥K → MulAut ↥P`.
  set φ : ↥K →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKnormP) with hφdef
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hφdef, MonoidHom.comp_apply] at hk
    have hkmem : (Subgroup.inclusion hKnormP k) ∈ (Subgroup.normalizerMonoidHom P).ker :=
      MonoidHom.mem_ker.mpr hk
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hkmem
    have hmem : (k : G) ∈ K ⊓ Subgroup.centralizer (↑P : Set G) :=
      Subgroup.mem_inf.mpr ⟨k.2, hkmem⟩
    rw [hKfaithful, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  haveI hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  obtain ⟨-, -, hb, -⟩ :=
    OddOrder.BG.Ch1.S05.solvableAut_of_narrow hpodd hPpg hPnarrow φ hφinj hKodd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
  have hKcard : Nat.card ↥K = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hgcop : Nat.Coprime (orderOf g) p := hKcard ▸ (hp.coprime_iff_not_dvd.mpr hKp').symm
  have hgdvd : orderOf g ∣ p - 1 := hb h3 g hgcop
  rw [← hKcard] at hgdvd
  exact hKp1 hgdvd

/-- **`|Z(O_p(M_F))| = p` in the type-V Singer case** (BG Theorem 15.7(e), Coq `defZP`/`oZ0`): the
centre of `P = O_p(M_F)` has order `p`.  The cyclic `κ`-Hall `K` (a `p′`-group acting on `P`)
centralizes `Ω₁(Z(P))` — it equals `K* = M_σ ⊓ C(K)` and `Ω₁(Z(P)) ≤ K*` (the `(e3)` Singer
hypothesis) — so by **BG Theorem 1.11** (`actsTrivially_on_of_fixes_omega1`, the coprime `Ω₁`-rigidity)
`K` centralizes all of `Z(P)`.  Hence `Z(P) ≤ M_σ ⊓ C(K) = K* = Ω₁(Z(P)) ≤ Z(P)`, i.e.
`Z(P) = Ω₁(Z(P))`, whose order is `p`.  This is the `|Z(P)| = p` input to the central-product
collapse `mFT_rank2_Sylow_cprod` (`card_opiCore_eq_prime_cube_singer`).

The hypotheses `hZKstar`/`hZcard` are about the explicit `Ω₁(Z(P)) = omega1CenterInG P p`; in the
type-V branch they come from the witness `Z` (which equals `Ω₁(Z(P))`, exposed by
`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`) together with `Z ≤ K*`. -/
theorem card_center_opiCore_eq_prime_of_omega1Center_le_kstar [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hKp' : ¬ p ∣ Nat.card ↥K)
    (hKnormP : K ≤ Subgroup.normalizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G))
    (hZKstar : OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ Kstar)
    (hZcard : Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
      (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p) = p) :
    Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  set Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG P p with hZdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (S15.MF M)
  -- `K* = Z` (= `Ω₁(Z(P))`): `|K*|` prime, `Z ≤ K*`, `|Z| = p`.
  have hKstarEqZ : Kstar = Z := by
    have hKstarPrime : (Nat.card ↥Kstar).Prime :=
      S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
    have hdvd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
    have hc : Nat.card ↥Kstar = p := ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hdvd).symm
    exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hc.trans hZcard.symm))).symm
  -- Conjugation action `φ : ↥K →* MulAut ↥P`.
  set φ : ↥K →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKnormP) with hφdef
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hpodd
  -- `K` fixes `Z(P)` pointwise (Theorem 1.11): it fixes `Ω₁(Z(P)) = Z ≤ K* ≤ C(K)`.
  have htriv : ∀ a : ↥K, ∀ g ∈ Subgroup.center ↥P, φ a g = g := by
    refine OddOrder.BG.Ch1.S01.actsTrivially_on_of_fixes_omega1 hp2 hPpg hKp' φ
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ) ?_
    intro a g hg hgp
    have hgZ : (g : G) ∈ Z := by
      rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map]
      exact ⟨g, mem_omega1OfAbelian.mpr ⟨hg, hgp⟩, rfl⟩
    have hgC : (g : G) ∈ Subgroup.centralizer (K : Set G) := by
      have hgKstar : (g : G) ∈ Kstar := by rw [hKstarEqZ]; exact hgZ
      rw [hKstar] at hgKstar; exact (Subgroup.mem_inf.mp hgKstar).2
    apply Subtype.ext
    show (a : G) * (g : G) * (a : G)⁻¹ = (g : G)
    have hcomm : (a : G) * (g : G) = (g : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hgC (a : G) a.2
    rw [hcomm, mul_inv_cancel_right]
  -- `Z(P) ≤ K* = Z`: `Z(P) ≤ M_σ` and `K` centralizes `Z(P)`.
  have hcent_le : (Subgroup.center ↥P).map P.subtype ≤ Z := by
    rw [← hKstarEqZ, hKstar]
    refine le_inf ((Subgroup.map_subtype_le _).trans
      ((opiCoreInG_le _ _).trans (hmf ▸ S15.maxNilpotentNormalHall_le_Msigma hG hM))) ?_
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 : k * (g : G) * k⁻¹ = (g : G) := congrArg (fun z : ↥P => (z : G)) (htriv ⟨k, hk⟩ g hg)
    exact mul_inv_eq_iff_eq_mul.mp h2
  -- `Z = Ω₁(Z(P)) ≤ Z(P)`.
  have hZ_le_cent : Z ≤ (Subgroup.center ↥P).map P.subtype := by
    rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG]
    exact Subgroup.map_mono omega1OfAbelian_le
  have hcent_eq : (Subgroup.center ↥P).map P.subtype = Z := le_antisymm hcent_le hZ_le_cent
  have hmapcard : Nat.card ↥((Subgroup.center ↥P).map P.subtype) = Nat.card ↥(Subgroup.center ↥P) :=
    Subgroup.card_map_of_injective P.subtype_injective
  rw [hcent_eq] at hmapcard
  rw [← hmapcard, hZcard]

/-- **`O_p(M_F)` is a Sylow `p`-subgroup of `G`** (Coq `sylP_G`): for a maximal `M` with
`M_F = M_σ` and `p ∈ σ(M)`, the `p`-core `P = O_p(M_F)` is a Sylow `p`-subgroup of `G`.

`P` is a `{p}`-Hall (hence Sylow) subgroup of the nilpotent `M_F = M_σ`
(`oPiCore_isHall_of_isNilpotent`: `p ∤ [M_F : P]`), so `|P| = p^{v_p(|M_F|)}` is the full `p`-part of
`|M_σ|`; and since `M_σ` is the `σ`-Hall of `G` with `p ∈ σ` (`Msigma_isHall`: `p ∤ [G : M_σ]`), that
`p`-part equals `v_p(|G|)`.  Thus `|P| = p^{v_p(|G|)}`, so `Sylow.ofCard` exhibits `P` as a Sylow
`p`-subgroup of `G`.  This is the `mFT_rank2_Sylow_cprod` Sylow input for the type-V Singer case
(`card_opiCore_eq_prime_cube_singer`). -/
theorem exists_sylow_eq_opiCore_of_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) :
    ∃ S : Sylow p G, (S : Subgroup G) = opiCoreInG ({p} : Set ℕ) (S15.MF M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  -- `P` is a `p`-group: `|P| = p^a`.
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (S15.MF M)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPpg
  suffices hcard : Nat.card ↥P = p ^ (Nat.card G).factorization p by
    exact ⟨Sylow.ofCard P hcard, Sylow.coe_ofCard P hcard⟩
  -- `v_p(|M_F|) = a`: `P = O_p(M_F)` is a `{p}`-Hall of `M_F` (`p ∤ [M_F : P]`).
  have hP'hall : Ch03.IsHallSubgroup ({p} : Set ℕ) (Ch03.oPiCore ({p} : Set ℕ) ↥(S15.MF M)) :=
    OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
  have hPcard : Nat.card ↥P = Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) ↥(S15.MF M)) :=
    Subgroup.card_map_of_injective (S15.MF M).subtype_injective
  have hpidxP : ¬ p ∣ (Ch03.oPiCore ({p} : Set ℕ) ↥(S15.MF M)).index := fun h =>
    hP'hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩)
      (Set.mem_singleton_iff.mpr rfl)
  have hMFfact : (Nat.card ↥(S15.MF M)).factorization p = a := by
    rw [← Subgroup.card_mul_index (Ch03.oPiCore ({p} : Set ℕ) ↥(S15.MF M)),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxP, add_zero, ← hPcard, ha,
      Nat.factorization_pow_self hp]
  -- `v_p(|G|) = v_p(|M_σ|)`: `M_σ` is the `σ`-Hall of `G`, `p ∈ σ`, so `p ∤ [G : M_σ]`.
  have hσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  have hpidxσ : ¬ p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := fun h =>
    hσHall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hGa : (Nat.card G).factorization p = a := by
    rw [← Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma M),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxσ, add_zero, ← hmf, hMFfact]
  rw [ha, hGa]

/-- **`|O_p(M_F)| = p³` in the type-V Singer case** (BG Theorem 15.7(e), Coq `dimP`/`oP`): the order
of `P = O_p(M_F)` is `p³`.  The inputs `r(P) ≤ 2` (`hrPle2`, the `rPle2` step, discharged via the
faithfulness brick `kappaHall_inf_centralizer_opiCore_eq_bot` + `pRank_opiCore_le_two_of_kappaHall`)
and `P` non-abelian (`hPnab`) are in hand.

All four inputs are now discharged: `r(P) ≤ 2` (`hrPle2`), `P` non-abelian (`hPnab`), `P` Sylow of
`G` (`exists_sylow_eq_opiCore_of_mf_eq_msigma`, Coq `sylP_G`), and `|Z(P)| = p` (`hZPcard`,
`card_center_opiCore_eq_prime_of_omega1Center_le_kstar`, Coq `defZP` via BG Theorem 1.11).  The sole
remaining content is the **Blackburn rank-2 Sylow central-product structure** (`mFT_rank2_Sylow_cprod`,
Coq §10.7b; Lean `S10.sylow_structure_b`, currently `private`): a Sylow `P` with `r(P) ≤ 2` and `P`
non-abelian is a central product `S ∘ C` of a nonabelian `p³` `S = Ω₁` with cyclic `C`; with
`|Z(P)| = p` the cyclic factor `C = Z(P)` collapses into `Z(S)`, leaving `|P| = |S| = p³`.  To finish:
de-privatize/expose `sylow_structure_b`, build the `p′`-Hall complement `V` of `P` in `N_G(P)`
(Schur–Zassenhaus), convert `pRank ≤ 2` to `rank ≤ 2` (`rank_le_pRank_of_isPGroup`), and collapse the
central product using `hZPcard`. -/
theorem card_opiCore_eq_prime_cube_singer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    {p : ℕ} (hp : p.Prime) (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hpπ : p ∈ (Nat.card ↥(S15.MF M)).primeFactors)
    (hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2)
    (hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)))
    (hZPcard : Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p) :
    Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P = O_p(M_F)` is a Sylow `p`-subgroup of `G` (`sylP_G`).
  obtain ⟨S, hS⟩ := exists_sylow_eq_opiCore_of_mf_eq_msigma hG hM hmf hp hpσ
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (S15.MF M)
  -- `rank P ≤ 2` from `pRank P p ≤ 2` (a `p`-group has `rank = pRank` at `p`).
  have hrankP : rank ↥P ≤ 2 := by
    by_contra hc
    exact absurd (OddOrder.BG.Ch2.S09.three_le_pRank_of_isPGroup_of_three_le_rank hPpg
      (by omega)) (by omega)
  -- **Blackburn rank-2 Sylow central-product dichotomy** (Cor 10.7(b), `sylow_structure`): `P` is
  -- abelian (excluded by `hPnab`) or a central product `P₁ ∘ P₂` with `P₁` exponent-`p`
  -- extraspecial of order `p³` and `P₂` cyclic with `Ω₁(P₂) = Z(P₁)`.
  have hrankS : rank ↥(S : Subgroup G) ≤ 2 := by rw [hS]; exact hrankP
  have hdich := (OddOrder.BG.Ch3.S10.sylow_structure hG S).2.1 hrankS
  rw [hS] at hdich
  rcases hdich with hab | ⟨P₁, P₂, hP₁P, hP₂P, hP₁es, hP₁card, hP₂cyc, hΩeq, hcp⟩
  · exact absurd hab hPnab
  · -- **Collapse** (Coq `dimP`): `P₂` is central in `P` (it centralizes `P₁` and is abelian), so
    -- `P₂ ≤ Z(P)` and `|P₂| ≤ |Z(P)| = p`; conversely `Ω₁(P₂) = Z(P₁)` has order `p` (`P₁`
    -- extraspecial), so `|P₂| ≥ p`.  Hence `|P₂| = p`, `P₂ = Ω₁(P₂) = Z(P₁) ≤ P₁`, and
    -- `P = P₁ ⊔ P₂ = P₁`, giving `|P| = |P₁| = p³`.
    haveI : IsCyclic ↥P₂ := hP₂cyc
    -- `|Z(P₁)| = p` (`P₁` extraspecial), and `|Ω₁(P₂).map| = |Z(P₁).map| = p` (`hΩeq`).
    have hΩcard : Nat.card ↥((Omega ↥P₂ p 1).map P₂.subtype) = p := by
      rw [hΩeq, Subgroup.card_map_of_injective P₁.subtype_injective,
        hP₁es.isExtraspecial.center_card]
    -- `P₂ ≤ C_G(P)`: `P₂` centralizes `P₁` (central product) and itself (cyclic ⟹ abelian).
    have hP₂cP : P₂ ≤ Subgroup.centralizer (P : Set G) := by
      rw [hcp.sup_eq]
      exact Subgroup.le_centralizer_iff.mpr (sup_le hcp.le_centralizer_right
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance))
    -- `P₂ ≤ Z(P)` (as a `G`-subgroup): `P₂ ≤ P` and `P₂ ≤ C_G(P)`.
    have hP₂_center : P₂ ≤ (Subgroup.center ↥P).map P.subtype := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hP₂P hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      exact fun z => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hP₂cP hx) (z : G) z.2)
    -- `|P₂| = p`: `≤ |Z(P)| = p` (above) and `≥ |Ω₁(P₂).map| = p`.
    have hP₂card : Nat.card ↥P₂ = p := by
      refine le_antisymm ?_ ?_
      · calc Nat.card ↥P₂ ≤ Nat.card ↥((Subgroup.center ↥P).map P.subtype) :=
              Subgroup.card_le_of_le hP₂_center
          _ = Nat.card ↥(Subgroup.center ↥P) := Subgroup.card_map_of_injective P.subtype_injective
          _ = p := hZPcard
      · calc p = Nat.card ↥((Omega ↥P₂ p 1).map P₂.subtype) := hΩcard.symm
          _ ≤ Nat.card ↥P₂ := Subgroup.card_le_of_le (Subgroup.map_subtype_le _)
    -- `Ω₁(P₂) = ⊤` (every element of the order-`p` `P₂` satisfies `g^p = 1`), so
    -- `P₂ = Ω₁(P₂).map = Z(P₁).map ≤ P₁`.
    have hΩtop : Omega ↥P₂ p 1 = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact fun g => Omega.mem_of_pow_eq_one
        (by rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mp (hP₂card ▸ orderOf_dvd_natCard g))
    have hP₂P₁ : P₂ ≤ P₁ := by
      have h := hΩeq
      rw [hΩtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      rw [h]; exact Subgroup.map_subtype_le _
    -- `P = P₁ ⊔ P₂ = P₁`, so `|P| = |P₁| = p³`.
    rw [hcp.sup_eq, sup_eq_left.mpr hP₂P₁, hP₁card]

/-- **`|K| ∣ n` from a Singer embedding into a cyclic group all of whose `K`-images are `n`-th roots
of unity** (the final arithmetic step of the type-V Singer divisibility, route B step L5).  If a
finite group `K` embeds (`hμ`) into a finite cyclic group `C` and every image `μ k` is killed by `n`,
then `K` is cyclic and `|K| ∣ n`.

In the type-V disjunct-3 application `C = 𝔽_{p²}ˣ` (Singer field units of `V = P/Z(P)`), `μ` is the
Singer realization `K ↪ 𝔽_{p²}ˣ`, and `μ k ^ (p+1) = 1` is the determinant-one / symplectic condition
`det(k) = N(μ k) = μ(k)^{p+1} = 1` (`algebraMap_norm_eq_pow`): `K` preserves the alternating
commutator form on `V`, so `K ⊆ Sp(V) = SL₂` and `det = 1`.  Then `|K| ∣ p+1`. -/
theorem card_dvd_of_injective_to_cyclic_forall_pow {K C : Type*} [Group K] [Finite K]
    [Group C] [Finite C] [IsCyclic C] (μ : K →* C) (hμ : Function.Injective μ)
    {n : ℕ} (h : ∀ k : K, μ k ^ n = 1) : Nat.card K ∣ n := by
  -- `μ` injective ⟹ `∀ k, k ^ n = 1`.
  have hKn : ∀ k : K, k ^ n = 1 := fun k => hμ (by rw [map_pow, h k, map_one])
  -- `K ≃* μ.range ≤ C` is cyclic.
  haveI : IsCyclic ↥μ.range := inferInstance
  haveI : IsCyclic K := isCyclic_of_surjective (MonoidHom.ofInjective hμ).symm.toMonoidHom
    (MonoidHom.ofInjective hμ).symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  rw [(orderOf_eq_card_of_forall_mem_zpowers hg).symm]
  exact orderOf_dvd_of_pow_eq_one (hKn g)

/-- **Prop 16.1 forward bridge `hP1eqV`, reduced to the Peterfalvi (8.8) trichotomy residual** — a
type-`P₁` maximal subgroup with `M_F = M_σ` is of type V.

The type-`P` datum is the fully-constructed `typePData_of_isTypeP1_mf_eq_msigma` (`U = ⊥`,
`sorry`-free — the type-V carrier-constructibility milestone); `isTypeV_of_typePData` then reduces to
the `alternative` disjunction on `H = M_F`.  As for the type-`F` bridge `isTypeI_of_isTypeF`, the
`FittingIsTI M` case is discharged directly (disjunct (a): `M_F#` is a `TI`-subset, via
`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).

The sole remaining residual is thus the genuinely-deep **`¬FittingIsTI` case of Peterfalvi (8.8) /
BG Theorem 15.7(d)(e)** (Coq `BGsection15` `nonTI_Fitting_structure`): either `M_F` abelian of rank 2
with `|W₁| ∣ p - 1`, or `O_p(M_F)` of order `p³` with `|W₁| ∣ p + 1` (the Suzuki/`SL₂`-type
structures).  Unlike the type-`F` trichotomy (`isTypeI_of_isTypeF`, whose non-TI cases are `rank = 2`
/ `exp U ∣ p - 1`), the type-V alternatives carry the `W₁`-Frobenius divisibilities `|W₁| ∣ p ∓ 1`,
which need the `W₁`-action analysis of (8.8) not yet formalized.

(`hP1neIIIIV`, the sibling `M_F ≠ M_σ ⟹ III/IV` bridge, needs no trichotomy but instead the full
nilpotent `M_F`-complement `U ≠ ⊥`, gated on `M'/M_F` nilpotent.) -/
theorem isTypeV_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeV M := by
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  refine isTypeV_of_typePData data rfl ?_
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset (same as the type-`F` bridge).
    exact Or.inl (maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI)
  · -- `¬FittingIsTI` ⟹ disjuncts (e2)/(e3).  The non-TI witness `X₁` (order `p`, `C_G(X₁) ⊄ M`),
    -- the cyclic `O_{p'}(M_F)` (Coq `cycHp'`), and the `M`-normal order-`p` `Z = Ω₁(Z(O_p(M_F)))`
    -- (Coq `oZ`, `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`).
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    have hnab := not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf
    obtain ⟨g, p, X₁, -, hp, hpσ, hX₁card, hX₁Mσ, -, hCGnotM, hrank3⟩ :=
      S15.exists_inf_conj_fitting_orderP_witness hG hM hTI
    haveI : Fact p.Prime := ⟨hp⟩
    have hX₁MF : X₁ ≤ S15.MF M := by
      rw [S15.mf_eq_msigma_of_not_fittingIsTI hG hM hTI]; exact hX₁Mσ
    obtain ⟨hpπ, hcyc⟩ :=
      S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab
    have hHMF : data.H = S15.MF M := data.H_eq
    -- Reconstruct a Hall `κ`-subgroup `K` (cyclic), the trivial `(κ ∪ σ)'`-Hall `U = ⊥`, and `K*`.
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro q hq
      simp only [Set.mem_compl_iff, not_not]
      by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hqσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hq, hqσ⟩)
    haveI hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    -- `|W₁| = [M:M'] = |K|`.
    have hW1K : Nat.card ↥data.W1 = Nat.card ↥K :=
      (data.card_W1_eq_derived_index).trans
        (card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK).symm
    -- The `M`-normal order-`p` `Z ≤ M_F = M_σ` normalized by `K`.
    obtain ⟨Z, hZMF, hZcard, hZnorm, hX₁notZ, hZeq⟩ :=
      S15.exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF hCGnotM
        hrank3 hnab (q := p) hp hpπ
    -- `Z = Ω₁(Z(O_p(M_F)))` (Coq `Z0`), exposed for the type-V Singer `|Z(P)| = p` argument.
    have hZomega : Z = OddOrder.BG.Ch3.S10.omega1CenterInG
        (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p := hZeq rfl
    have hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M := hmf ▸ hZMF
    have hKNZ : K ≤ Subgroup.normalizer (Z : Set G) := hKM.trans hZnorm
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- (e2) vs (e3) dichotomy on the Frobenius divisibility `|W₁| ∣ p − 1` (matching Coq's
    -- `Ks = Z₀ → |K| ∣ p-1` split): if it holds, disjunct (e2) directly; otherwise the genuine
    -- Singer/`SL₂(p)` case (e3), where the `K`-action on `Z` is *not* Frobenius so `Z ⊓ K* ≠ ⊥`,
    -- i.e. `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`).
    by_cases hdvd : Nat.card ↥data.W1 ∣ p - 1
    · -- (e2): `|W₁| ∣ p − 1` directly (the cyclic `O_{p'}(M_F)` is `hcyc`).
      exact Or.inr (Or.inl ⟨p, hp, hHMF ▸ hpπ, hdvd, hHMF ▸ hcyc⟩)
    · -- (e3): `¬(|W₁| ∣ p − 1)`, the genuine Singer case.  Then `Z ⊓ K* ≠ ⊥` (else the Frobenius
      -- engine `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot` would give `|K| = |W₁| ∣ p − 1`),
      -- hence `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`/`defZP`/`rPle2`/`oZ0`, the genuinely-deep residual).
      have hZK : Z ⊓ Kstar ≠ ⊥ := fun h => hdvd
        (hW1K ▸ kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot hG hM hP1.1 hKM hK hKstardef hU
          hZMσ hZcard hKNZ h)
      -- `r(O_p(M_F)) ≤ 2` (Coq `rPle2`): faithfulness `K ⊓ C_G(P) = ⊥`
      -- (`kappaHall_inf_centralizer_opiCore_eq_bot`, brick 4) + `pRank_opiCore_le_two_of_kappaHall`.
      have hpodd : Odd p :=
        hG.odd.of_dvd_nat ((Nat.dvd_of_mem_primeFactors hpπ).trans
          (Subgroup.card_subgroup_dvd_card _))
      have hKp' : ¬ p ∣ Nat.card ↥K := by
        intro hdvdK
        have hpfK : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
          exact Nat.mem_primeFactors.mpr ⟨hp, hdvdK, Nat.card_pos.ne'⟩
        exact (S14.kappa_subset_sigmaCompl (hK.primeFactors_card_subset p hpfK)) hpσ
      have hKnormP : K ≤ Subgroup.normalizer
          (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) :=
        hKM.trans (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)
          (S15.maxNilpotentNormalHall_le_normalizer M))
      have hZKstar : Z ≤ Kstar := by
        have hd : Nat.card ↥(Z ⊓ Kstar) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime hp).mp hd with h1 | hpp
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZK
        · exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
            (le_of_eq (hZcard.trans hpp.symm)))
      have hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 :=
        pRank_opiCore_le_two_of_kappaHall hG hM hp hpodd hX₁card hX₁MF hrank3 hKp' hKnormP
          (kappaHall_inf_centralizer_opiCore_eq_bot hG hM hP1 hKM hK hKstardef hU hp hX₁card hX₁MF
            hZKstar hZcard hX₁notZ)
          (hW1K ▸ hdvd)
      -- `O_p(M_F)` is non-abelian (`opiCore_singleton_not_isMulCommutative_of_witness`).
      have hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) :=
        S15.opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
      -- `|Z(P)| = p` (Coq `defZP`, via BG Theorem 1.11): the witness `Z = Ω₁(Z(P))` (`hZomega`)
      -- lies in `K*` (`hZKstar`), so `K` centralizes `Z(P)`, forcing `Z(P) = Ω₁(Z(P))`.
      have hZPcard : Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p :=
        card_center_opiCore_eq_prime_of_omega1Center_le_kstar hG hM hP1 hmf hKM hK hKstardef
          hp hpodd hKp' hKnormP (hZomega ▸ hZKstar) (hZomega ▸ hZcard)
      refine Or.inr (Or.inr ⟨p, hp, hHMF ▸ hpπ, ?_, ?_, hHMF ▸ hcyc⟩)
      · -- (sorry 1) `|O_p(M_F)| = p³`.  All four inputs (`r(P) ≤ 2`, `P` non-abelian, `P` Sylow of
        -- `G`, `|Z(P)| = p`) are discharged; the residual is the `mFT_rank2_Sylow_cprod`
        -- central-product structure (Coq §10.7b, Lean `sylow_structure_b`), isolated in
        -- `card_opiCore_eq_prime_cube_singer`.
        exact card_opiCore_eq_prime_cube_singer hG hM hP1 hmf hp hpσ hpπ hrPle2 hPnab hZPcard
      · -- (sorry 2) `|W₁| ∣ p + 1` via route B (Singer/`SL₂(p)` symplectic divisibility).
        haveI : Fact p.Prime := ⟨hp⟩
        have hPcard3 : Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 :=
          card_opiCore_eq_prime_cube_singer hG hM hP1 hmf hp hpσ hpπ hrPle2 hPnab hZPcard
        set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
        have hPextra : OddOrder.GroupTheory.IsExtraspecial p ↥P :=
          OddOrder.GroupTheory.IsExtraspecial.of_card_eq_prime_cube hPcard3 (fun h => hPnab ⟨⟨h⟩⟩)
        have hPMσ : P ≤ OddOrder.BG.Ch3.S10.Msigma M :=
          (opiCoreInG_le _ _).trans (S15.maxNilpotentNormalHall_le_Msigma hG hM)
        -- conjugation action `φ : K → Aut P`.
        let φ : ↥K →* MulAut ↥P :=
          (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKnormP)
        have hφ : ∀ (k : ↥K) (x : ↥P), ((φ k x : ↥P) : G) = (k : G) * (x : G) * (k : G)⁻¹ :=
          fun _ _ => rfl
        -- `K* = Z`.
        have hKstarEqZ : Kstar = Z := by
          have hKstarPrime : (Nat.card ↥Kstar).Prime :=
            S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstardef
          have hd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
          have hc : Nat.card ↥Kstar = p :=
            ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hd).symm
          exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hc.trans hZcard.symm))).symm
        -- `Z = Ω₁(Z(P))` as a subgroup of `↥P`-center mapped to `G`.
        have hZmem : ∀ {g : G}, g ∈ Z → ∃ z : ↥P, z ∈ Subgroup.center ↥P ∧ (z : G) = g := by
          intro g hg
          rw [hZomega] at hg
          simp only [OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map,
            Subgroup.coe_subtype] at hg
          obtain ⟨z, hzΩ, hzg⟩ := hg
          exact ⟨z, OddOrder.GroupTheory.omega1OfAbelian_le hzΩ, hzg⟩
        -- `hfpf`: `φ k x = x ⟹ x ∈ commutator P` (`x` centralizes `k`, so lands in `K* = Z`).
        have hfpf : ∀ k : ↥K, k ≠ 1 → ∀ x : ↥P, (φ k) x = x → x ∈ commutator ↥P := by
          intro k hk1 x hfix
          have hkne : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
          have hcm : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
            have h := congrArg Subtype.val hfix; rwa [hφ k x] at h
          have hcomm : (k : G) * (x : G) = (x : G) * (k : G) := mul_inv_eq_iff_eq_mul.mp hcm
          have hxKstar : (x : G) ∈ Kstar := by
            rw [← centralizer_msigma_kappaElement_eq_kstar hG hM hP1.1 hKM hK hKstardef hU k.2 hkne]
            refine Subgroup.mem_inf.mpr ⟨hPMσ x.2, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            rintro g rfl
            exact hcomm
          obtain ⟨z, hzc, hzx⟩ := hZmem (hKstarEqZ ▸ hxKstar)
          have hzx' : z = x := Subtype.ext hzx
          rw [hPextra.commutator_eq_center, ← hzx']; exact hzc
        -- `hcentZ`: `K` centralizes `Z(P) = commutator P`.
        have hcentZ : ∀ k : ↥K, ∀ z : ↥P, z ∈ commutator ↥P → (φ k) z = z := by
          intro k z hz
          rw [hPextra.commutator_eq_center] at hz
          have hzZ : (z : G) ∈ Z := by
            rw [hZomega]
            simp only [OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map, Subgroup.coe_subtype]
            refine ⟨z, (OddOrder.GroupTheory.mem_omega1OfAbelian).mpr ⟨hz, ?_⟩, rfl⟩
            have hdz : orderOf z ∣ p := by
              have h1 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥P)) ∣
                  Nat.card ↥(Subgroup.center ↥P) := orderOf_dvd_natCard _
              rw [hZPcard] at h1
              rwa [← orderOf_injective (Subgroup.center ↥P).subtype
                Subtype.coe_injective ⟨z, hz⟩] at h1
            exact orderOf_dvd_iff_pow_eq_one.mp hdz
          have hzcK : (z : G) ∈ Subgroup.centralizer (K : Set G) :=
            (hZKstar.trans (hKstardef ▸ inf_le_right)) hzZ
          have hcomm : (k : G) * (z : G) = (z : G) * (k : G) :=
            Subgroup.mem_centralizer_iff.mp hzcK (k : G) k.2
          apply Subtype.ext
          rw [hφ k z, hcomm, mul_inv_cancel_right]
        exact hW1K ▸ OddOrder.GroupTheory.card_dvd_succ_of_primeAction_extraspecial hpodd
          hPextra hPcard3 φ hfpf hcentZ hKcyc hKp' (hW1K ▸ hdvd)

/-- **Prop 16.1(d)/(f) reverse, `M_F = M_σ` from `U = ⊥`** (the `M_F = M_σ` conjunct of `hVP1`,
mmd L4478): a type-`P` datum with trivial complement `U = ⊥` has `M_F = M_σ`.  Sandwiching:
`M' = M_F ⊔ U = M_F` (`TypePData.derivedInG_eq_fitting_sup_U` with `U = ⊥`), while always
`M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`); so `M_F = M_σ = M'`.
Axiom-clean (does *not* cite Theorem A(8), unlike the `M_F = M_σ` step of `typeFData_of_kappa_eq_bot`).
This is the structural half of clause (d): the `IsTypeP1` half is the (deeper) `κ` refinement. -/
theorem mf_eq_msigma_of_typePData_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M) (hU : data.U = ⊥) :
    S15.MF M = OddOrder.BG.Ch3.S10.Msigma M := by
  -- `M' = M_F` since `M' = M_F ⊔ U` and `U = ⊥`.
  have hderiv : derivedInG M = S15.MF M := by
    rw [data.derivedInG_eq_fitting_sup_U, hU, sup_bot_eq]
  -- `M_F ≤ M_σ` always; `M_σ ≤ M' = M_F`; hence equal.
  refine le_antisymm (S15.maxNilpotentNormalHall_le_Msigma hG hM) ?_
  exact hderiv ▸ OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM

/-- **Type V vs a nontrivial complement** (general `U = ⊥` exclusivity core): a maximal subgroup
cannot be both type `V` (a `TypeVData`, so `U = ⊥` and `M' = M_F`) and carry a `TypePData` with
`U ≠ ⊥`.  Both data fix the *same* `H = maxNilpotentNormalHall M` and present `U` as a complement of
`H` in `M' = M_F ⊔ U`; the type-V witness forces `M' = M_F`, so the other `U ≤ H`, hence
(disjointness of the complement) `U = ⊥`.  Generalises the `not_isTypeII_of_isTypeV` argument and is
the common core of the `III/IV ≠ V` exclusivity used in the reverse bridges. -/
theorem not_isTypeV_of_typePData_U_ne_bot {M : Subgroup G}
    (hV : OddOrder.GroupTheory.IsTypeV M) (data : TypePData M) (hU : data.U ≠ ⊥) : False := by
  obtain ⟨dV⟩ := hV
  have hMV : derivedInG M = maxNilpotentNormalHall M := by
    rw [dV.typeP.derivedInG_eq_fitting_sup_U, dV.U_eq_bot, sup_bot_eq]
  have hUH : data.U ≤ data.H := by
    rw [data.H_eq]
    have hsup : maxNilpotentNormalHall M ⊔ data.U = maxNilpotentNormalHall M := by
      rw [← data.derivedInG_eq_fitting_sup_U, hMV]
    exact le_sup_right.trans (le_of_eq hsup)
  have hdisj : Disjoint (data.H.subgroupOf (derivedInG M))
      (data.U.subgroupOf (derivedInG M)) := data.derived_complement.disjoint
  have hUsub : data.U.subgroupOf (derivedInG M) = ⊥ := by
    rw [← inf_of_le_left (Subgroup.subgroupOf_mono (derivedInG M) hUH), inf_comm,
      disjoint_iff.mp hdisj]
  have hUbot : data.U = ⊥ :=
    (inf_of_le_left data.U_le).symm.trans
      (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hUsub))
  exact hU hUbot

/-- **Type V and Type II are mutually exclusive** (the `U = ⊥` vs `U ≠ ⊥` dichotomy): a type-II
maximal has a nontrivial complement `U ≠ ⊥` (`TypePNontrivialCore`), ruled out against a type-V
witness by `not_isTypeV_of_typePData_U_ne_bot`.  Supplies the `¬ M_P2` half of `hVP1`. -/
theorem not_isTypeII_of_isTypeV {M : Subgroup G} :
    OddOrder.GroupTheory.IsTypeV M → ¬ OddOrder.GroupTheory.IsTypeII M :=
  fun hV ⟨dII⟩ => not_isTypeV_of_typePData_U_ne_bot hV dII.typeP dII.common.1

/-- **Type III/IV and Type V are mutually exclusive** (the `U ≠ ⊥` vs `U = ⊥` dichotomy): types III
and IV carry a `TypePData` with nontrivial complement `U ≠ ⊥` (`TypePNontrivialCore`), ruled out
against a type-V witness by `not_isTypeV_of_typePData_U_ne_bot`.  Used in the `hIIIIVP1` reverse
bridge to force `M_F ≠ M_σ` (else the type would be V). -/
theorem not_isTypeV_of_isTypeIII_or_IV {M : Subgroup G}
    (h : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    ¬ OddOrder.GroupTheory.IsTypeV M := by
  intro hV
  rcases h with hd | hd
  · exact not_isTypeV_of_typePData_U_ne_bot hV hd.some.typeP hd.some.common.1
  · exact not_isTypeV_of_typePData_U_ne_bot hV hd.some.typeP hd.some.common.1

/-- **Type-`P` complements are `M`-conjugate** (Schur–Zassenhaus): for any two `TypePData` on a
maximal subgroup `M`, the complements `U` are conjugate by an element of `M`.  Both `U_i` complement
the nilpotent normal Hall subgroup `H = M_F` in `M' = [M,M]` (the `derived_complement` field, with
`H` witness-independent via `H_eq`).  `H` is a Hall subgroup of `M`
(`maxNilpotentNormalHall_isHall`), hence Hall in `M'` (its `M'`-index divides its `M`-index), so
`|H|` and `[M' : H] = |U|` are coprime; Schur–Zassenhaus conjugacy of complements of a normal Hall
subgroup (`IsComplement'.exists_conj_of_coprime`, applied inside `↥M'`) gives `n ∈ H ≤ M` with
`n · U_1 · n⁻¹ = U_2`.  This is the engine behind the `II ≠ III/IV` exclusivity
(`not_isTypeII_of_isTypeIII_or_IV`): it transfers the normalizer condition `N_G(U) ≤ M` between
witnesses. -/
theorem typePData_exists_conj_U [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (d1 d2 : TypePData M) :
    ∃ n : G, n ∈ M ∧ MulAut.conj n • d1.U = d2.U := by
  have hH_le : maxNilpotentNormalHall M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  have hH_le_M : maxNilpotentNormalHall M ≤ M := maxNilpotentNormalHall_le M
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hU1_le : d1.U ≤ derivedInG M := d1.U_le
  have hU2_le : d2.U ≤ derivedInG M := d2.U_le
  -- Solvability of `↥M'` (transport along the inclusion `↥M' ↪ ↥M`).
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hM'solv : IsSolvable ↥(derivedInG M) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hM'_le_M)
  -- `H ◁ M'` (set-form normalizer, `M' ≤ M ≤ N_G(H)`).
  have hM'_le_NH : derivedInG M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hM'_le_M.trans (maxNilpotentNormalHall_le_normalizer M)
  haveI hHn_normal : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH_le).mpr hM'_le_NH
  -- Both `U_i` complement `H` in `M'` (`derived_complement`, rewritten via `H = M_F`).
  have hK1 : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).IsComplement'
      (d1.U.subgroupOf (derivedInG M)) := by rw [← d1.H_eq]; exact d1.derived_complement
  have hK2 : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).IsComplement'
      (d2.U.subgroupOf (derivedInG M)) := by rw [← d2.H_eq]; exact d2.derived_complement
  -- Coprimality `|H|` vs `[M' : H]`: `[M' : H] ∣ [M : H]` and `H` is Hall in `M`.
  have hdvd' : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).index ∣
      ((maxNilpotentNormalHall M).subgroupOf M).index := by
    have hmul := Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall M) (derivedInG M) M
      hH_le hM'_le_M
    exact ⟨(derivedInG M).relIndex M, hmul.symm⟩
  have hcardEq : Nat.card ↥((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      = Nat.card ↥((maxNilpotentNormalHall M).subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le_M).toEquiv]
  have hcop : Nat.Coprime
      (Nat.card ↥((maxNilpotentNormalHall M).subgroupOf (derivedInG M)))
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).index := by
    rw [hcardEq]
    exact ((maxNilpotentNormalHall_isHall M).coprime_index).coprime_dvd_right hdvd'
  -- Schur–Zassenhaus inside `↥M'`: `n ∈ H` with `(U_1)ᶜᵒⁿʲ = U_2`.
  obtain ⟨n, hnH, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hK1 hK2
  -- Translate the conjugacy back to `G` (intertwine `M'.subtype` with `conj`).
  have hintertwine : (derivedInG M).subtype.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp (derivedInG M).subtype := by
    ext ⟨y, hy⟩; rfl
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (n : G) • K = K.map (MulAut.conj (n : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hLHS : ((d1.U.subgroupOf (derivedInG M)).map (MulAut.conj n).toMonoidHom).map
      (derivedInG M).subtype = MulAut.conj (n : G) • d1.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU1_le, hsmul_map]
  have hRHS : (d2.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype = d2.U :=
    Subgroup.map_subgroupOf_eq_of_le hU2_le
  refine ⟨(n : G), hM'_le_M n.2, ?_⟩
  calc MulAut.conj (n : G) • d1.U
      = ((d1.U.subgroupOf (derivedInG M)).map (MulAut.conj n).toMonoidHom).map
          (derivedInG M).subtype := hLHS.symm
    _ = (d2.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype := by rw [hnconj]
    _ = d2.U := hRHS

/-- **Normalizer condition transfers between type-`P` complements** (mmd L4478 reverse): for two
`TypePData` on a maximal `M`, `N_G(U_1) ≤ M ⟺ N_G(U_2) ≤ M`.  The complements are `M`-conjugate
(`typePData_exists_conj_U`), and conjugation by `n ∈ M` fixes `M`
(`conj_smul_eq_self_of_mem_normalizer`) and intertwines normalizers (`normalizer_conj_smul`).  This
is the bridge that makes the type-II condition `¬ N_G(U) ≤ M` and the type-III/IV condition
`N_G(U) ≤ M` contradictory on the same `M`. -/
theorem typePData_normalizer_U_le_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (d1 d2 : TypePData M) :
    Subgroup.normalizer (d1.U : Set G) ≤ M ↔ Subgroup.normalizer (d2.U : Set G) ≤ M := by
  obtain ⟨n, hnM, hconj⟩ := typePData_exists_conj_U hG hM d1 d2
  have hnorm : Subgroup.normalizer (d2.U : Set G)
      = MulAut.conj n • Subgroup.normalizer (d1.U : Set G) := by
    rw [← hconj]; exact (normalizer_conj_smul n d1.U).symm
  have hMfix : MulAut.conj n • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hnM)
  rw [hnorm]
  constructor
  · intro h1
    calc MulAut.conj n • Subgroup.normalizer (d1.U : Set G)
        ≤ MulAut.conj n • M := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h1
      _ = M := hMfix
  · intro h2
    have h3 : MulAut.conj n • Subgroup.normalizer (d1.U : Set G) ≤ MulAut.conj n • M := by
      rw [hMfix]; exact h2
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h3

/-- **Type II and Type III/IV are mutually exclusive** (mmd L4478 reverse): the type-II condition
`¬ N_G(U) ≤ M` (`TypeIIData.normalizer_not_le`) and the type-III/IV condition `N_G(U) ≤ M`
(`TypeIIIData.normalizer_le`/`TypeIVData.normalizer_le`) cannot both hold on a maximal `M`, since the
complements `U` are `M`-conjugate (`typePData_normalizer_U_le_iff`).  This is the exclusivity that
refines `IsTypeP` (`= IsTypeP1 ∨ IsTypeP2`) into the precise type for the reverse bridges
`hIIP2`/`hIIIIVP1`. -/
theorem not_isTypeII_of_isTypeIII_or_IV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (h : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    ¬ OddOrder.GroupTheory.IsTypeII M := by
  rintro ⟨dII⟩
  rcases h with hd | hd
  · exact dII.normalizer_not_le
      ((typePData_normalizer_U_le_iff hG hM dII.typeP hd.some.typeP).mpr hd.some.normalizer_le)
  · exact dII.normalizer_not_le
      ((typePData_normalizer_U_le_iff hG hM dII.typeP hd.some.typeP).mpr hd.some.normalizer_le)

/-- **Prop 16.1 reverse, centralizer half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `1 ⊂ C_H(W₁) ⊆
C_{M_σ}(W₁)`): for a type-`P` datum and a nonidentity `x ∈ W₁`, the `M_σ`-centralizer of `x` is
nontrivial.  Witness: `W₂ = M' ⊓ C(x)` (`centralizer_W1`) lies in both `M_σ` (`W₂ ≤ H = M_F ≤ M_σ`)
and `C(x)`, and `W₂ ≠ ⊥` (`W2_nontrivial`); so `W₂ ≤ M_σ ⊓ C(x)` is a nontrivial subgroup.

This is the `κ(M)`-membership ingredient that is **derivable from the bare `TypePData`** (it needs
no `W₁ = κ`-Hall identification).  The remaining `κ`-membership ingredients — `p ∉ σ(M)` and the
rank-one condition `r_p(M) = 1` putting `p ∈ τ₁(M) ∪ τ₃(M)` — are the carrier-gated half (the latter
genuinely needs `W₁` to be the Hall `κ(M)`-subgroup; cf. issue 8015 and
`typep-w1-kappa-carrier-not-derivable`). -/
theorem typePData_msigma_inf_centralizer_W1_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {x : G} (hx : x ∈ data.W1) (hxne : x ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  -- `W₂ ≤ M_σ ⊓ C(x)`.
  have hW2le : data.W2 ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf ?_ ?_
    · -- `W₂ ≤ H = M_F ≤ M_σ`.
      calc data.W2 ≤ data.H := data.W2_le.trans inf_le_left
        _ = maxNilpotentNormalHall M := data.H_eq
        _ ≤ _ := S15.maxNilpotentNormalHall_le_Msigma hG hM
    · -- `W₂ = M' ⊓ C(x) ≤ C(x)`.
      rw [← data.centralizer_W1 x hx hxne]; exact inf_le_right
  -- A subgroup containing the nontrivial `W₂` is nontrivial.
  exact fun hbot => data.W2_nontrivial (le_bot_iff.mp (hW2le.trans hbot.le))

/-- **Prop 16.1 reverse, `σ`-complement half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `W₁ ∩ M_σ = 1`): for a
type-`P` datum, every prime dividing `|W₁|` lies outside `σ(M)`.  If `p ∈ σ(M)`, an order-`p`
subgroup `L ≤ W₁` is a `σ(M)`-group, so it lands in the `σ`-Hall subgroup `M_σ`
(`sigma_subgroup_le_Msigma_of_isHall`, `Msigma_isHall`); but `W₁ ∩ M_σ ≤ W₁ ∩ M' = 1`
(`M_complement`), forcing `L = ⊥` and `|L| = p = 1`, a contradiction.

This is the second `κ`-membership ingredient **derivable from the bare `TypePData`** (with
`typePData_msigma_inf_centralizer_W1_ne_bot`).  Together they give `p ∉ σ(M)` and `M_σ ⊓ C(P) ≠ ⊥`;
the only carrier-gated ingredient left for `π(W₁) ⊆ κ(M)` is the rank-one condition `r_p(M) = 1`. -/
theorem typePData_W1_prime_not_mem_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {p : ℕ} (hp : p ∈ (Nat.card ↥data.W1).primeFactors) :
    p ∉ OddOrder.BG.Ch3.S10.sigma M := by
  intro hpσ
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- An order-`p` element `g ∈ W₁` and the cyclic subgroup `L = ⟨g⟩` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p (Nat.dvd_of_mem_primeFactors hp)
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  set L : Subgroup G := Subgroup.zpowers (g : G) with hLdef
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, hgord]
  have hLW1 : L ≤ data.W1 := Subgroup.zpowers_le.mpr g.2
  have hLM : L ≤ M := hLW1.trans data.W1_le
  -- `L` is a `σ(M)`-group (its only prime divisor is `p ∈ σ(M)`).
  have hLpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) L := by
    intro q hq
    rw [hLcard, (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpσ
  -- So `L ≤ M_σ ≤ M'`, while `L ≤ W₁` and `W₁ ∩ M' = ⊥` (complement); hence `L = ⊥`.
  have hLMσ : L ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hLM hLpi
  have hLsub_bot : L.subgroupOf M = ⊥ := by
    rw [eq_bot_iff, ← disjoint_iff.mp data.M_complement.disjoint]
    exact le_inf
      (Subgroup.comap_mono (hLMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)))
      (Subgroup.comap_mono hLW1)
  have hLbot : L = ⊥ :=
    (inf_eq_left.mpr hLM).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hLsub_bot))
  rw [hLbot, Subgroup.card_bot] at hLcard
  exact (Fact.out : p.Prime).ne_one hLcard.symm

/-- **Prop 16.1 reverse, `M_P` from `TypePData` modulo the rank-one input** (mmd L4478,
`π(W₁) ⊆ κ(M) ⟹ κ(M) ≠ ∅`): a type-`P` datum whose `W₁`-primes all have `M`-rank one has
`κ(M) ≠ ∅`, hence `M` is `S14.IsTypeP`.  This is the gated-endpoint assembly of the three `κ`-bridge
ingredients for a prime `p ∣ |W₁|`: `p ∉ σ(M)` (`typePData_W1_prime_not_mem_sigma`) and `r_p(M) = 1`
(the hypothesis `hrank`) put `p ∈ τ₁(M) ∪ τ₃(M)`, while `⟨g⟩` (`g ∈ W₁` of order `p`) is a rank-one
elementary abelian subgroup with `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`
(`typePData_msigma_inf_centralizer_W1_ne_bot`).  So `p ∈ κ(M)`.

The only residual hypothesis `hrank` is the carrier-gated half (the `W₁ = κ`-Hall fact forces
`r_p(M) = 1`; cf. issue 8015).  Supplies the `→ M_P` direction of the reverse classifications
`hIIP2`/`hIIIIVP1`/`hVP1` of `proposition_type_classification_of_inputs`. -/
theorem typePData_kappa_nonempty_of_rank1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M)
    (hrank : ∀ p ∈ (Nat.card ↥data.W1).primeFactors, pRank ↥M p = 1) :
    (S14.kappa M).Nonempty := by
  classical
  -- A prime `p ∣ |W₁|` (`W₁ ≠ ⊥`).
  have hW1card : Nat.card ↥data.W1 ≠ 1 := fun h => data.W1_nontrivial (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hW1card
  have hp : p ∈ (Nat.card ↥data.W1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  -- An order-`p` element `g ∈ W₁` and the rank-one subgroup `P = ⟨g⟩`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p hpdvd
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := fun hc => by
    rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers, hgord]
  refine ⟨p, hpp, ?_, Subgroup.zpowers (g : G),
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩,
    (Subgroup.zpowers_le.mpr g.2).trans data.W1_le, ?_⟩
  · -- `p ∈ τ₁(M) ∪ τ₃(M)` from `p ∉ σ(M)` and `r_p(M) = 1`.
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := typePData_W1_prime_not_mem_sigma hG hM data hp
    have hr : pRank ↥M p = 1 := hrank p hp
    by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
    · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr⟩)
    · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr⟩)
  · -- `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`.
    have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ :=
      typePData_msigma_inf_centralizer_W1_ne_bot hG hM data g.2 hgne
    have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
        Subgroup.centralizer ((Subgroup.zpowers (g : G) : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
    exact fun hbot => hCne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))

/-- **Prop 16.1 reverse, cyclicity ingredient for `r_q(M) = 1`** (mmd L4478): for a type-`P`
datum and a prime `q ∤ |M'|`, every elementary abelian `q`-subgroup `A` of `↥M` is cyclic.

The abelianization `↥M ⧸ M'` is cyclic — the `M_complement` field makes the cyclic factor `W₁`
(`W1_cyclic`) a complement of `M' = [M,M]` in `M`, so `↥M ⧸ M' ≃* ↥W₁`
(`IsComplement'.QuotientMulEquiv`).  Since `q ∤ |M'|` and `A` is a `q`-group, `A ⊓ M' = ⊥`
(coprime orders), so the quotient map embeds `A` into the cyclic `↥M ⧸ M'`, forcing `A` cyclic.
This is the `q`-rank-one half of `π(W₁) ⊆ κ(M)` once `q ∤ |M'|` is in hand (Hall for type V, the
`centralizer_W1` fixed-point argument for types II–IV). -/
theorem typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M))
    {A : Subgroup ↥M} (hA : A.IsElementaryAbelian q) : IsCyclic ↥A := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclic ↥data.W1 := data.W1_cyclic
  set N : Subgroup ↥M := (derivedInG M).subgroupOf M with hNdef
  -- `N = commutator ↥M`, hence normal.
  have hN_eq : N = commutator ↥M := by
    rw [hNdef, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hNnorm : N.Normal := by rw [hN_eq]; infer_instance
  -- `↥M ⧸ N ≃* ↥(W₁.subgroupOf M)` is cyclic.
  haveI : IsCyclic ↥(data.W1.subgroupOf M) := by
    have e : ↥(data.W1.subgroupOf M) ≃* ↥data.W1 := Subgroup.subgroupOfEquivOfLe data.W1_le
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have ecyc : (↥M ⧸ N) ≃* ↥(data.W1.subgroupOf M) := (data.M_complement.symm).QuotientMulEquiv
  haveI : IsCyclic (↥M ⧸ N) := isCyclic_of_surjective ecyc.symm ecyc.symm.surjective
  -- `A ⊓ N = ⊥`: `|A|` is a `q`-power and `q ∤ |N| = |M'|`.
  have hNcard : Nat.card ↥N = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA.isPGroup
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N) := by
    rw [hk, hNcard]
    exact Nat.Coprime.pow_left k ((hq.coprime_iff_not_dvd).mpr hndvd)
  have hAN : A ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  -- `A` injects into the cyclic `↥M ⧸ N`.
  set φ : ↥A →* (↥M ⧸ N) := (QuotientGroup.mk' N).comp A.subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hmem : (a : ↥M) ∈ A ⊓ N := ⟨a.2, ha⟩
    rw [hAN, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  haveI : IsCyclic ↥φ.range := inferInstance
  exact isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm
    (MonoidHom.ofInjective hφinj).symm.surjective

/-- **Prop 16.1 reverse, `r_q(M) = 1` from `q ∤ |M'|`** (mmd L4478): for a type-`P` datum and a
prime `q ∣ |W₁|` with `q ∤ |M'|`, the `q`-rank of `M` is one.  Upper bound: every elementary
abelian `q`-subgroup is cyclic (`typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived`),
so `pRank ↥M q ≤ 1`.  Lower bound: `q ∣ |W₁| ∣ |M|` gives an order-`q` element, an elementary
abelian `q`-subgroup of order `q`, so `1 ≤ pRank ↥M q`.  This is the rank-one input that
`typePData_kappa_nonempty_of_rank1` needs to place the `W₁`-primes in `κ(M)`. -/
theorem typePData_pRank_eq_one_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hqW1 : q ∣ Nat.card ↥data.W1)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M)) :
    pRank ↥M q = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ ?_
  · exact pRank_le_one_of_forall_isElementaryAbelian_isCyclic (fun A hA =>
      typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived data hq hndvd hA)
  · have hqM : q ∣ Nat.card ↥M := hqW1.trans (Subgroup.card_dvd_of_le data.W1_le)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) q hqM
    have hcard : Nat.card ↥(Subgroup.zpowers g) = q := by rw [Nat.card_zpowers, hg]
    exact pow_le_card_of_le_pRank (Subgroup.zpowers g)
      (Subgroup.IsElementaryAbelian.of_card_prime hcard) (by rw [hcard, pow_one])

/-- **Prop 16.1 reverse, type V ⟹ type `P`** (mmd L4478, clause (d) `.mp`): a structurally
type-`V` maximal subgroup is type `P` (`κ(M) ≠ ∅`).  Type `V` has `U = ⊥`, so `M' = M_F` is the
nilpotent normal Hall subgroup `maxNilpotentNormalHall M`; Hall coprimality gives `q ∤ |M'|` for
every `q ∣ |W₁| = [M : M']`, whence `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`).  Feeding this rank-one fact to
`typePData_kappa_nonempty_of_rank1` places `π(W₁) ⊆ κ(M)`, so `κ(M) ≠ ∅`.  This is the type-V
branch of the `hVP1` reverse bridge (the `IsTypeP` half) of Proposition 16.1. -/
theorem isTypeP_of_isTypeV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hV : OddOrder.GroupTheory.IsTypeV M) : S14.IsTypeP M := by
  obtain ⟨v⟩ := hV
  -- `M' = M_F` (`U = ⊥`).
  have hM'eq : derivedInG M = maxNilpotentNormalHall M := by
    rw [v.typeP.derivedInG_eq_fitting_sup_U, v.U_eq_bot, sup_bot_eq]
  have hHall := maxNilpotentNormalHall_isHall M
  refine typePData_kappa_nonempty_of_rank1 hG hM v.typeP (fun q hq => ?_)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqW1 : q ∣ Nat.card ↥v.typeP.W1 := Nat.dvd_of_mem_primeFactors hq
  have hndvd : ¬ q ∣ Nat.card ↥(derivedInG M) := by
    rw [hM'eq]
    intro hdvd
    have hqMF : q ∈ (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
    have hidx : ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card ↥v.typeP.W1 := by
      rw [← hM'eq]; exact (v.typeP.card_W1_eq_derived_index).symm
    have hqIdx : q ∈ ((maxNilpotentNormalHall M).subgroupOf M).index.primeFactors := by
      rw [hidx]; exact Nat.mem_primeFactors.mpr ⟨hqp, hqW1, Nat.card_pos.ne'⟩
    exact (hHall.2 q hqIdx) hqMF
  exact typePData_pRank_eq_one_of_not_dvd_card_derived v.typeP hqp hqW1 hndvd

/-- Conjugation action of the cyclic group `⟨x⟩` on a subgroup `N` it normalizes. -/
def conjActionOfMemNormalizer {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    ↥(Subgroup.zpowers x) →* MulAut ↥N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hx))

theorem conjActionOfMemNormalizer_apply {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (a : ↥(Subgroup.zpowers x)) (n : ↥N) :
    ((conjActionOfMemNormalizer hx a) n : G) = (a : G) * (n : G) * (a : G)⁻¹ := rfl

/-- Fixed points of the cyclic conjugation action on `N` are the elements of `N` centralizing `x`. -/
theorem fixedPoints_conjActionOfMemNormalizer_eq {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    Subgroup.fixedPointsOfMulAut (conjActionOfMemNormalizer hx) =
      (N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf N := by
  ext n
  constructor
  · intro hn
    rw [Subgroup.mem_subgroupOf]
    refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    have hfixG := congrArg Subtype.val
      (Subgroup.mem_fixedPointsOfMulAut.mp hn ⟨y, Subgroup.mem_zpowers y⟩)
    rw [conjActionOfMemNormalizer_apply] at hfixG
    calc y * (n : G) = (y * (n : G) * y⁻¹) * y := by group
      _ = (n : G) * y := by rw [hfixG]
  · intro hn
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    apply Subtype.ext
    rw [conjActionOfMemNormalizer_apply]
    have hncent : (n : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hn).2
    have hcomm : Commute (x : G) (n : G) :=
      Subgroup.mem_centralizer_iff.mp hncent x (Set.mem_singleton x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hacomm : (a : G) * (n : G) = (n : G) * (a : G) := by
      rw [← hk]; exact (hcomm.zpow_left k)
    calc (a : G) * (n : G) * (a : G)⁻¹ = (n : G) * (a : G) * (a : G)⁻¹ := by rw [hacomm]
      _ = (n : G) := by group

/-- **`p`-element fixed-point count** (`[Finite G]`): if a `q`-element `x` normalizes `N` and
`q ∣ |N|`, then `q ∣ |C_N(x)|`.  The `q`-group `⟨x⟩` acts on `N` by conjugation, so
`|N| ≡ |C_N(x)| (mod q)` (`IsPGroup.card_modEq_card_fixedPoints`, the fixed points being
`N ⊓ C(x)`); since `q ∣ |N|`, also `q ∣ |C_N(x)|`.  Used to show `q ∤ |M'|` for the type-II–IV
reverse bridges: `C_{M'}(x) = W₂` has order coprime to `q = |W₁|`. -/
theorem prime_dvd_card_inf_centralizer_of_mem_normalizer [Finite G]
    {N : Subgroup G} {x : G} {q : ℕ} [Fact q.Prime]
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hxq : IsPGroup q ↥(Subgroup.zpowers x))
    (hdvd : q ∣ Nat.card ↥N) :
    q ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  letI : MulAction ↥(Subgroup.zpowers x) ↥N :=
    MulAction.compHom ↥N (conjActionOfMemNormalizer hx)
  have hmod := hxq.card_modEq_card_fixedPoints (α := ↥N)
  -- The fixed points of the conjugation action are `N ⊓ C(x)`.
  have hcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥N)
      = Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr (Equiv.trans (Equiv.subtypeEquivRight (fun n => ?_))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        N ⊓ Subgroup.centralizer ({x} : Set G) ≤ N)).toEquiv)
    rw [← fixedPoints_conjActionOfMemNormalizer_eq hx, Subgroup.mem_fixedPointsOfMulAut]
    exact Iff.rfl
  rw [hcard] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- **`q ∤ |W₂|` for prime `|W₁| = q`** (type II–IV): `W₁` and `W₂` are subgroups of the cyclic
`W = W₁W₂` with `W₁ ⊓ W₂ = ⊥` (`W₂ ≤ M_F ≤ M'` and `W₁ ⊓ M' = ⊥` by `M_complement`).  If `q ∣ |W₂|`,
order-`q` elements `x ∈ W₁`, `y ∈ W₂` generate the *same* order-`q` subgroup of the cyclic `W`
(`cyclic_subgroup_eq_of_card_eq`), so `x ∈ ⟨y⟩ ≤ W₂`, forcing `x ∈ W₁ ⊓ W₂ = ⊥`, contra. -/
theorem typePData_not_dvd_card_W2_of_card_W1_prime [Finite G] {M : Subgroup G}
    (data : TypePData M) (hq : (Nat.card ↥data.W1).Prime) :
    ¬ (Nat.card ↥data.W1) ∣ Nat.card ↥data.W2 := by
  intro hdvd
  haveI : Fact (Nat.card ↥data.W1).Prime := ⟨hq⟩
  haveI : IsCyclic ↥data.W := data.W_cyclic
  have hW2leM' : data.W2 ≤ derivedInG M := le_trans data.W2_le (le_trans inf_le_left data.H_le)
  have hW1W2 : data.W1 ⊓ data.W2 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, data.W1_le (Subgroup.mem_inf.mp hg).1⟩ : ↥M) ∈
        ((derivedInG M).subgroupOf M) ⊓ (data.W1.subgroupOf M) :=
      ⟨Subgroup.mem_subgroupOf.mpr (hW2leM' (Subgroup.mem_inf.mp hg).2),
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hg).1⟩
    rw [disjoint_iff.mp data.M_complement.disjoint, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W2) (Nat.card ↥data.W1) hdvd
  have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
  have hyord : orderOf ((y : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W2.subtype data.W2.subtype_injective y).trans hy
  have hxne : (x : G) ≠ 1 := fun hc => hq.ne_one (by rw [← hxord, hc, orderOf_one])
  have hW1leW : data.W1 ≤ data.W := le_sup_left.trans data.W_eq.ge
  have hW2leW : data.W2 ≤ data.W := le_sup_right.trans data.W_eq.ge
  have hxW : (x : G) ∈ data.W := hW1leW x.2
  have hyW : (y : G) ∈ data.W := hW2leW y.2
  have h1 : (Subgroup.zpowers (x : G)).subgroupOf data.W
      = (Subgroup.zpowers (y : G)).subgroupOf data.W := by
    refine OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxW)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyW)).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
  have hxin : (x : G) ∈ Subgroup.zpowers (y : G) := by
    have hm : (⟨(x : G), hxW⟩ : ↥data.W) ∈ (Subgroup.zpowers (x : G)).subgroupOf data.W :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers (x : G))
    rw [h1] at hm
    exact Subgroup.mem_subgroupOf.mp hm
  have hmem : (x : G) ∈ data.W1 ⊓ data.W2 := ⟨x.2, (Subgroup.zpowers_le.mpr y.2) hxin⟩
  rw [hW1W2, Subgroup.mem_bot] at hmem
  exact hxne hmem

/-- **Prop 16.1 reverse, type II–IV ⟹ type `P`** (mmd L4478): a type-`P` datum whose cyclic
factor `W₁` has *prime* order `q = |W₁|` (the `TypePNontrivialCore` of types II/III/IV) is BG type
`P`.  `q ∤ |M'|`: else the `q`-element `x ∈ W₁#` normalizing `M'` would give `q ∣ |C_{M'}(x)| = |W₂|`
(`prime_dvd_card_inf_centralizer_of_mem_normalizer`, `centralizer_W1`), contradicting `q ∤ |W₂|`
(`typePData_not_dvd_card_W2_of_card_W1_prime`).  Then `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`) and `κ(M) ≠ ∅`
(`typePData_kappa_nonempty_of_rank1`). -/
theorem isTypeP_of_typePData_of_card_W1_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hqprime : (Nat.card ↥data.W1).Prime) : S14.IsTypeP M := by
  haveI : Fact (Nat.card ↥data.W1).Prime := ⟨hqprime⟩
  refine typePData_kappa_nonempty_of_rank1 hG hM data (fun p hp => ?_)
  have hpq : p = Nat.card ↥data.W1 := by
    rcases hqprime.eq_one_or_self_of_dvd p (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact absurd h (Nat.prime_of_mem_primeFactors hp).ne_one
    · exact h
  subst hpq
  have hndvd : ¬ Nat.card ↥data.W1 ∣ Nat.card ↥(derivedInG M) := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
    have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
      (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
    have hxne : (x : G) ≠ 1 := fun hc => hqprime.ne_one (by rw [← hxord, hc, orderOf_one])
    have hsubeq : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    haveI hnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hsubeq]; infer_instance
    have hxnorm : (x : G) ∈ Subgroup.normalizer (derivedInG M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm (data.W1_le x.2)
    have hxpg : IsPGroup (Nat.card ↥data.W1) ↥(Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
    have hdvdW2 : Nat.card ↥data.W1 ∣ Nat.card ↥data.W2 := by
      have hd := prime_dvd_card_inf_centralizer_of_mem_normalizer hxnorm hxpg hdvd
      rwa [data.centralizer_W1 (x : G) x.2 hxne] at hd
    exact typePData_not_dvd_card_W2_of_card_W1_prime data hqprime hdvdW2
  exact typePData_pRank_eq_one_of_not_dvd_card_derived data hqprime dvd_rfl hndvd

/-- **Prop 16.1 reverse, type II ⟹ type `P`** (clause (b) `.mp`, `IsTypeP` half): immediate from
`isTypeP_of_typePData_of_card_W1_prime` and the `TypePNontrivialCore` primality of `|W₁|`. -/
theorem isTypeP_of_isTypeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hII : OddOrder.GroupTheory.IsTypeII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type III ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIII : OddOrder.GroupTheory.IsTypeIII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type IV ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIV : OddOrder.GroupTheory.IsTypeIV M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIV
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, every non-type-I maximal subgroup is type `P`** (mmd L4478): the common
`IsTypeP` half of clauses (b)–(d) `.mp`.  Types II/III/IV reduce to the prime-`|W₁|` argument
(`isTypeP_of_typePData_of_card_W1_prime`); type V to the Hall argument (`isTypeP_of_isTypeV`).
This is exactly what `not_isTypeI_of_isTypeNonI` consumes (it discards the `P₁`/`P₂` refinement),
so it closes the FT-critical content of the reverse type bridges modulo `hIF` (type I ⟹ type F). -/
theorem isTypeP_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : OddOrder.GroupTheory.IsTypeNonI M) : S14.IsTypeP M := by
  rcases h with hII | hIII | hIV | hV
  · exact isTypeP_of_isTypeII hG hM hII
  · exact isTypeP_of_isTypeIII hG hM hIII
  · exact isTypeP_of_isTypeIV hG hM hIV
  · exact isTypeP_of_isTypeV hG hM hV

/-- **Theorem A(8), the `FittingIsTI`-free part** (mmd L4274): for `M_F ≠ M_σ`, the Hall
`(κ ∪ σ)ᶜ`-complement `U` is trivial and `|K| = p` is prime.  Both follow from
`mf_ne_msigma_typeP1_structure` (Theorem 15.2): `M_F ≠ M_σ ⟹ IsTypeP1 M`
(`isTypeP1_of_mf_ne_msigma`), whence `U.subgroupOf M = ⊥`
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), while `|K| = p` prime is read off Theorem
15.2's structure conjunction directly.

This discharges two of the three conjuncts of Theorem A(8) in `theoremA_maximal_structure`; the
remaining `FittingIsTI M` (`F(M)` a TI-subgroup of `G`) is the genuinely deep §15 content (Theorem A
proper, via the §9–§10 uniqueness/fusion machinery) and is *not* supplied here. -/
theorem theoremA8_complement_eq_bot_and_kappa_prime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  refine ⟨isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot
    (isTypeP1_of_mf_ne_msigma hG hM hne) hU, ?_⟩
  obtain ⟨_, _, _, p, _, hpp, _, hKp, -⟩ :=
    (mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar).2
  exact ⟨p, hpp, hKp⟩

/-- **BG Theorem A(8), in full** (mmd L4274): for `M_F ≠ M_σ`, the Hall `(κ ∪ σ)ᶜ`-complement `U`
is trivial, `F(M)` is a TI-subgroup of `G`, and `|K| = p` is prime.  Combines the
`FittingIsTI`-free part (`theoremA8_complement_eq_bot_and_kappa_prime`, via Theorem 15.2) with the
`FittingIsTI` clause (`S15.fitting_isTI_of_mf_ne_msigma`, the contrapositive of the `M_F = M_σ`
conclusion of Theorem 15.7(a)).  This is the full conjunction `theoremA_maximal_structure` carries
for the `M_F ≠ M_σ` case; it is `sorry`-free modulo the single deep §15 rank-theoretic residual
`S15.piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` (Theorem 15.7(a) core). -/
theorem theoremA8_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  obtain ⟨hUbot, hKp⟩ :=
    theoremA8_complement_eq_bot_and_kappa_prime hG hM hKM hK hKstar hU hne
  exact ⟨hUbot, S15.fitting_isTI_of_mf_ne_msigma hG hM hne, hKp⟩

/-- **Type-`P₁` (`M_F ≠ M_σ`) `TypePNontrivialCore`** (the common type II--IV hypotheses of Peterfalvi
(8.6), for the type III/IV case): a `TypePData` of a type-`P₁` maximal subgroup with `M_F ≠ M_σ` and
nontrivial complement `U` satisfies `U ≠ ⊥`, `|W₁|` prime, and `M_F#` is a `TI`-subset.

The `|W₁|` primality is Theorem A(8) (`theoremA8_structure`: `M_F ≠ M_σ ⟹ |K| = p` prime, with
`|W₁| = |K| = [M:M']`); the `M_F#`-`TI` is the `FittingIsTI M` clause of A(8)
(`fitting_isTI_of_mf_ne_msigma`) read through `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`.
Discharges the `hcommon` input of the type III/IV last mile `isTypeIII_or_IV_of_typePData`, so once
the type-`P₁` `TypePData` is constructed (`exists_typeP1_mf_complement` plus the deep
nilpotency/Fitting fields) and `N_G(U) ⊆ M` is supplied, the `hP1neIIIIV` bridge closes. -/
theorem typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (data : TypePData M) (hUne : data.U ≠ ⊥) :
    TypePNontrivialCore M data := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  refine ⟨hUne, ?_, ?_⟩
  · -- `|W₁| = [M:M'] = |K| = p` prime (Theorem A(8)).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    -- The trivial `(κ ∪ σ)'`-Hall `U = ⊥` (type `P₁`: `π(M) ⊆ κ ∪ σ`).
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro p hp
      simp only [Set.mem_compl_iff, not_not]
      by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hpσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hp, hpσ⟩)
    haveI : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    obtain ⟨_, _, p, hp, hKp⟩ := theoremA8_structure hG hM hKM hK rfl hU hne
    rw [data.card_W1_eq_derived_index, ← card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK, hKp]
    exact hp
  · -- `M_F#` is `TI` (`FittingIsTI M` from `M_F ≠ M_σ`).
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM
      (S15.fitting_isTI_of_mf_ne_msigma hG hM hne)

/-- **Normalizer of a finite nilpotent subgroup is contained in the normalizer of each of its Sylow
subgroups** (the `char_norms (pcore_char p U)` step of Coq `BGsection16` `typePfacts`): for a finite
nilpotent `U ≤ G` and a Sylow `p`-subgroup `P` of `↥U`, the `G`-normalizer of `U` lies in the
`G`-normalizer of `P̄ = P.map U.subtype`.  Since `U` is nilpotent, `P` is normal — hence the *unique*
Sylow `p`-subgroup of `↥U` (`Sylow.unique_of_normal`) — so conjugation by any `g ∈ N_G(U)` (which
permutes `U`'s Sylow `p`-subgroups) fixes `P̄`.  Reusable. -/
theorem normalizer_le_normalizer_map_sylow_of_isNilpotent [Finite G] {U : Subgroup G}
    (hUnil : Group.IsNilpotent ↥U) {p : ℕ} [Fact p.Prime] (P : Sylow p ↥U) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (((P : Subgroup ↥U).map U.subtype : Subgroup G) : Set G) := by
  classical
  haveI := hUnil
  haveI hPnormal : (P : Subgroup ↥U).Normal := Ch01.Sylow.normal_of_isNilpotent P
  letI : Unique (Sylow p ↥U) := P.unique_of_normal hPnormal
  set Pbar : Subgroup G := (P : Subgroup ↥U).map U.subtype with hPbardef
  have hPbar_le_U : Pbar ≤ U := Subgroup.map_subtype_le _
  -- `|P̄|` is the full `p`-part of `|U|`.
  have hcardPbar : Nat.card ↥Pbar = p ^ (Nat.card ↥U).factorization p := by
    rw [hPbardef, Subgroup.card_map_of_injective U.subtype_injective]
    exact P.card_eq_multiplicity
  intro g hg
  have hgU : MulAut.conj g • U = U := conj_smul_eq_self_of_mem_normalizer hg
  -- `conj g • P̄ ≤ U` (since `g` normalizes `U`).
  have hconj_le_U : MulAut.conj g • Pbar ≤ U := by
    rw [pointwise_mulAut_smul_eq_map]
    calc (Pbar.map (MulAut.conj g : G →* G))
        ≤ U.map (MulAut.conj g : G →* G) := Subgroup.map_mono hPbar_le_U
      _ = MulAut.conj g • U := (pointwise_mulAut_smul_eq_map _ _).symm
      _ = U := hgU
  -- `(conj g • P̄).subgroupOf U` is a Sylow `p` of `↥U`, hence `= P` by uniqueness.
  have hcardConj : Nat.card ↥((MulAut.conj g • Pbar).subgroupOf U)
      = p ^ (Nat.card ↥U).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj_le_U).toEquiv,
      pointwise_mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcardPbar]
  set Q : Sylow p ↥U := Sylow.ofCard ((MulAut.conj g • Pbar).subgroupOf U) hcardConj with hQdef
  have hQP : (Q : Subgroup ↥U) = (P : Subgroup ↥U) := by rw [Subsingleton.elim Q P]
  have h2 : (Q : Subgroup ↥U) = (MulAut.conj g • Pbar).subgroupOf U := Sylow.coe_ofCard _ _
  -- Transport back to `G`: `conj g • P̄ = P̄`, so `g ∈ N_G(P̄)`.
  have hfix : MulAut.conj g • Pbar = Pbar := by
    have h1 : ((MulAut.conj g • Pbar).subgroupOf U).map U.subtype = MulAut.conj g • Pbar :=
      Subgroup.map_subgroupOf_eq_of_le hconj_le_U
    rw [← h1, ← h2, hQP]
  exact mem_normalizer_of_conj_smul_eq_self hfix

/-- **A prime dividing the type-`P₁` `M_F`-complement is a `σ`-prime that `U` carries fully**
(the `sMp`/`sylP` steps of Coq `BGsection16` `typePfacts`): for a type-`P₁` maximal `M` and an
`M_F`-complement `U` in `M' = M_σ` (`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), every prime `p ∣ |U|` lies in
`σ(M)` and the `p`-part of `|U|` equals the `p`-part of `|M|`.

`p ∈ σ(M)`: `p ∣ |U| ∣ |M_σ|` and `M_σ` is the `σ`-Hall (`Msigma_subgroupOf_isHall`).
`p`-parts agree: `|M| = |U| · [M:U]` and `p ∤ [M:U] = [M':U]·[M:M']`.  Here `[M':U] = |M_F|`
(`IsComplement'.index_eq_card`) and `p ∤ |M_F|` because `M_F` is a Hall subgroup of `M`
(`maxNilpotentNormalHall_isHall`) with `|U| ∣ [M:M_F]`, while `[M:M'] = [M:M_σ]` is a `σ'`-number
(`p ∈ σ`).  Hence a Sylow `p`-subgroup of `U` is a Sylow `p`-subgroup of `M`. -/
theorem typeP1_complement_mem_sigma_and_factorization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) :
    p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
      (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpU : p ∣ Nat.card ↥U := Nat.dvd_of_mem_primeFactors hp
  set M' := derivedInG M with hM'def
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hUle' : U ≤ M' := hsup ▸ le_sup_right
  have hMFle' : maxNilpotentNormalHall M ≤ M' := hsup ▸ le_sup_left
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hUM : U ≤ M := hUle'.trans hM'M
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  -- (1) `p ∈ σ(M)`: `p ∣ |U| ∣ |M'| = |M_σ|`, and `π(M_σ) ⊆ σ`.
  have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
    exact Nat.mem_primeFactors.mpr
      ⟨hpp, hpU.trans (hM'σ ▸ Subgroup.card_dvd_of_le hUle'), Nat.card_pos.ne'⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).1 p hpMσ
  refine ⟨hpσ, ?_⟩
  -- (2) `p`-parts agree.  `[M:U] = [M':U]·[M:M']`.
  have hidx_split : (U.subgroupOf M').index * (M'.subgroupOf M).index = (U.subgroupOf M).index :=
    Subgroup.relIndex_mul_relIndex U M' M hUle' hM'M
  -- `p ∤ [M':U] = |M_F|`.
  have hp_not_UM' : ¬ p ∣ (U.subgroupOf M').index := by
    rw [hDcompl.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMFle').toEquiv]
    intro hdvd
    -- `|U| ∣ [M:M_F]` (since `[M':M_F] = |U|` and `[M:M_F] = [M':M_F]·[M:M']`).
    have hMF'idx : ((maxNilpotentNormalHall M).subgroupOf M').index = Nat.card ↥U := by
      rw [hDcompl.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle').toEquiv]
    have hsplit2 : ((maxNilpotentNormalHall M).subgroupOf M').index * (M'.subgroupOf M).index
        = ((maxNilpotentNormalHall M).subgroupOf M).index :=
      Subgroup.relIndex_mul_relIndex _ M' M hMFle' hM'M
    have hUdvd : Nat.card ↥U ∣ ((maxNilpotentNormalHall M).subgroupOf M).index :=
      ⟨(M'.subgroupOf M).index, by rw [← hsplit2, hMF'idx]⟩
    have hp_idxMF : p ∈ (((maxNilpotentNormalHall M).subgroupOf M).index).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpU.trans hUdvd, Subgroup.index_ne_zero_of_finite⟩
    exact (maxNilpotentNormalHall_isHall M).2 p hp_idxMF
      (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩)
  -- `p ∤ [M:M'] = [M:M_σ]` (`σ`-Hall, `p ∈ σ`).
  have hp_not_M'M : ¬ p ∣ (M'.subgroupOf M).index := by
    intro hdvd
    refine (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).2 p ?_ hpσ
    rw [hM'σ] at hdvd
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩
  -- `p ∤ [M:U]`.
  have hp_not_UM : ¬ p ∣ (U.subgroupOf M).index := by
    rw [← hidx_split]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h1 | h2
    · exact hp_not_UM' h1
    · exact hp_not_M'M h2
  -- conclude.  `|M| = |U| · [M:U]`, `factorization p [M:U] = 0`.
  have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
    have h := Subgroup.card_mul_index (U.subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h
  rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hp_not_UM, add_zero]

/-- **Prop 16.1 forward bridge `hP1neIIIIV`, reduced to the Peterfalvi (8.7) normalizer residual** —
a type-`P₁` maximal subgroup with `M_F ≠ M_σ` is of type III or IV.

The type-`P` datum is now fully constructed (`typePData_of_isTypeP1_mf_ne_msigma`, the type III/IV
carrier-constructibility milestone, BG Corollary 15.5): the nilpotent `M_F`-complement `U ≠ ⊥` with
`F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.  The complement is built transparently here (rather than via the
opaque constructor) so that `U ≠ ⊥` (`hcommon`) and the normalizer condition are statable for the
*specific* `U`.  `isTypeIII_or_IV_of_typePData` then splits on `IsMulCommutative ↥U` (III vs IV).

The sole remaining residual is the genuinely-deep **type III/IV last mile `N_G(U) ⊆ M`** (Peterfalvi
(8.7) / Coq `BGsection15` `Fcore_structure`): this self-normalizing property of the `M_F`-complement
is exactly what distinguishes type III/IV (`normalizer_le`) from type II (`normalizer_not_le`), and
needs the BG uniqueness analysis of the complement not yet formalized. -/
theorem isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨U, hUle, hsup, hKnorm, hinf⟩ := exists_typeP1_mf_complement hG hM hP1 hKM hK
  have hUnilp : Group.IsNilpotent ↥U :=
    isNilpotent_complement_of_isTypeP1_mf_ne_msigma hG hM hP1 hne hsup hinf
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hFiteq := fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma hG hM hP1 hsup hinf
  have hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    obtain ⟨_, -, -, -, hM''F, -, -, -, -, -, -, -⟩ := S15.fitting_decomposition hG hM
    rw [← hFiteq]; exact hM''F
  -- `U ≠ ⊥`: else `M_F = M' = M_σ`, contradicting `hne`.
  have hUne : U ≠ ⊥ := by
    rintro rfl
    refine hne ?_
    have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
      isTypeP1_derivedInG_eq_Msigma hG hM hP1
    have hMF' : maxNilpotentNormalHall M = derivedInG M := by rw [← hsup, sup_bot_eq]
    rw [hM'σ] at hMF'; exact hMF'
  set data : TypePData M :=
    typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK hUle hKnorm hUnilp hDcompl hSDfit hFiteq
    with hdata
  have hdataU : data.U = U := rfl
  have hcommon : TypePNontrivialCore M data :=
    typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma hG hM hP1 hne data (hdataU ▸ hUne)
  refine isTypeIII_or_IV_of_typePData data hcommon ?_
  rw [hdataU]
  -- `N_G(U) ⊆ M` (Peterfalvi (8.7), Coq `typePfacts`): pick a prime `p ∣ |U|` and `P = Sylow_p(U)`.
  -- `N_G(U) ≤ N_G(P̄)` (`P̄` unique in the nilpotent `U`) and `P̄` is a `σ`-Sylow of `M`, so
  -- `N_G(P̄) ≤ M` (`normalizer_sylow_map_le_of_mem_sigma`).
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
  have hpπU : p ∈ (Nat.card ↥U).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hpσ, hfact⟩ :=
    typeP1_complement_mem_sigma_and_factorization hG hM hP1 hsup hinf hpπU
  have hUM : U ≤ M := hUle.trans (Subgroup.map_subtype_le _)
  have P : Sylow p ↥U := default
  have hPbarM : ((P : Subgroup ↥U).map U.subtype) ≤ M :=
    (Subgroup.map_subtype_le _).trans hUM
  have hcardPbar : Nat.card ↥(((P : Subgroup ↥U).map U.subtype).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPbarM).toEquiv,
      Subgroup.card_map_of_injective U.subtype_injective, P.card_eq_multiplicity, hfact]
  set Q : Sylow p ↥M := Sylow.ofCard (((P : Subgroup ↥U).map U.subtype).subgroupOf M) hcardPbar
    with hQdef
  refine le_trans (normalizer_le_normalizer_map_sylow_of_isNilpotent hUnilp P) ?_
  have hQmap : (Q : Subgroup ↥M).map M.subtype = (P : Subgroup ↥U).map U.subtype := by
    rw [hQdef, Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPbarM]
  have hnorm := OddOrder.BG.Ch3.S10.normalizer_sylow_map_le_of_mem_sigma hpσ Q
  rwa [hQmap] at hnorm

/-- **BG Theorem A(7), first clause — `M'' ⊆ F(M)`** (mmd L4354), as a standalone `sorry`-free
lemma for *any* maximal `M`.  No longer `M_F ≠ M_σ`-gated: Theorem 15.2's closing (issue 8012)
supplies the type-`P₁` half, so a case split on `M_F = M_σ` discharges both branches.

* `M_F = M_σ` (`M_σ` nilpotent, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`): then
  `M'' ≤ M_σ` (`derivedDerived_le_Msigma`, always true via §12 `E'` abelian) and
  `M_σ ≤ M_F ≤ F(M)` (`Msigma_le_maxNilpotentNormalHall_of_nilpotent`,
  `maxNilpotentNormalHall_le_fittingInG`);
* `M_F ≠ M_σ` (type `P₁`): the `M'' ⊆ F(M)` conjunct of Theorem 15.2
  (`mf_ne_msigma_typeP1_structure`), where `F(M) = Q C_M(Q) ⊊ M_σ` and the containment is the
  genuinely-harder chief-factor analysis (not reducible to `M'' ≤ M_σ`, since `M_σ ⊄ F(M)` here).

The second clause of A(7) (`F(M) = C_M(M_F) M_F`, and `K ≠ 1 → F(M) ⊆ M'`) is left to the gated
`fittingInAmbient_eq_*`/`theoremC_paired_structure`; only `M'' ⊆ F(M)` enters the faithful monolith
`theoremA_maximal_structure_faithful`. -/
theorem derivedDerived_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    derivedInG (derivedInG M) ≤ S15.fittingInAmbient M := by
  by_cases hne : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
  · -- `M_σ` nilpotent: `M'' ≤ M_σ ≤ M_F ≤ F(M)`.
    have hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hne
    calc derivedInG (derivedInG M)
        ≤ OddOrder.BG.Ch3.S10.Msigma M := S15.derivedDerived_le_Msigma hG hM
      _ ≤ maxNilpotentNormalHall M :=
          S15.Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil
      _ ≤ S15.fittingInAmbient M := S15.maxNilpotentNormalHall_le_fittingInG M
  · -- type `P₁`: cite the `M'' ⊆ F(M)` conjunct (16th) of Theorem 15.2.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA7, _, _, _⟩ :=
      S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar
    exact hA7

/-- **BG Theorem A — the faithful monolith** (mmd L4346-4355), all 11 conjuncts `sorry`-free.

This is the faithfulness-corrected counterpart of `theoremA_maximal_structure`: it adds the explicit
`hKM : K ≤ M` and `hUM : U ≤ M` that the BG setup `M = K U M_σ` carries but the bare Hall
conditions on `K.subgroupOf M` / `U.subgroupOf M` do not force, so conjuncts A(3) (`M = K U M_σ`),
A(4) (`C_U(k) = 1`), and A(8) (`U = 1`) become provable.  Every conjunct is discharged by a
standalone lemma — none gated:

* A(1) `M_σ` is `σ(M)`-Hall, A(2) `K` cyclic, A(3)-normal `M ≤ N(U M_σ)`, A(4) `C_U(k) = 1`,
  A(5) `K* ≠ 1` and `C_M(k) = K K*`, A(6) `M_F ≤ M_σ ≤ M'` — all from `theoremA_ungated_conjuncts`;
* A(3)-decomposition `M = K U M_σ` — `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`;
* A(7) `M'' ⊆ F(M)` — `derivedDerived_le_fittingInAmbient` (now ungated, issue 8012);
* A(8) `M_F ≠ M_σ ⟹ U = 1 ∧ F(M)` TI `∧ |K|` prime — `theoremA8_structure` (`U.subgroupOf M = ⊥`
  upgraded to `U = ⊥` via `hUM`).

The `sorry` `theoremA_maximal_structure` is kept as-is for its existing (cross-lane) callers; new
consumers wanting a proved Theorem A cite this faithful form. -/
theorem theoremA_maximal_structure_faithful [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ S15.fittingInAmbient M ∧
      (S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
        U = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p) := by
  obtain ⟨hA1, hA2, hA3n, hA4, hA5a, hA5b, hA6a, hA6b⟩ :=
    theoremA_ungated_conjuncts hG hM hKM hUM hK hKstar hU
  refine ⟨hA1, hA2, typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU,
    hA3n, hA4, hA5a, hA5b, hA6a, hA6b,
    derivedDerived_le_fittingInAmbient hG hM hKM hK hKstar, ?_⟩
  -- A(8): `theoremA8_structure` gives `U.subgroupOf M = ⊥`; lift to `U = ⊥` via `hUM`.
  intro hne
  obtain ⟨hUsub, hTI, hp⟩ := theoremA8_structure hG hM hKM hK hKstar hU hne
  refine ⟨?_, hTI, hp⟩
  have h := Subgroup.map_subgroupOf_eq_of_le hUM
  rw [hUsub, Subgroup.map_bot] at h
  exact h.symm

end OddOrder.BG.Ch4.S16
