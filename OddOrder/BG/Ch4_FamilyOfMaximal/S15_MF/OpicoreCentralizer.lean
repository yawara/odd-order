import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.PisetBetaDisjoint

/-!
# OpicoreCentralizer

Prefix-split from `OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.TIFailure` (2000-line limit, issue 0103 第
2 パス).
-/
namespace OddOrder.BG.Ch4.S15
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise
open scoped IsMulCommutative
open scoped commutatorElement

variable {G : Type*} [Group G]



/-- **BG Theorem 15.7(a), rank-theoretic core** (mmd L4192-4198): if `F(M)` is not a TI-subgroup
of `G`, then no prime divides `M_F` and lies in `β(M)`.

The `≥ 3` side is fully proved (`three_le_pRank_mf_of_mem_beta`: any `r ∈ π(M_F) ∩ β(M)` has
`r_r(M_F) ≥ 3`); the proof below reduces the goal to the complementary `< 3` bound
`pRank (M_F) r < 3`, the genuinely deep §15 content isolated as the single remaining `sorry`.

**Proved building blocks (this file):** the setup
`exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` (step 1: `g ∉ M`,
`X = F(M) ⊓ F(M)^g ≠ ⊥`)
and `rank_lt_three_of_le_two_maximals` (step 7 core: a subgroup in two distinct maximals has rank
`< 3`).  The remaining assembly, with the located upstream lemmas:

* **(step 3, `p ∈ σ(M)`)** pick `p ∈ π(X)`, `X₁ ≤ X` of order `p`
  (`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`: `X₁ ≤ O_p(F(M))`).  If `p ∉ σ(M)` then
  `O_p(F(M)) ≤ O_{σ'}(F(M))` is cyclic (`fitting_decomposition`), so `X₁` is the unique order-`p`
  subgroup, hence characteristic and normal in both `M` and `M^g`;
  `normalizer_eq_of_normal_of_mem_maximal`
  (S08, currently `private`) forces `M^g = M`, contradicting `g ∉ M`. ⟹ `p ∈ σ(M)`. *(fiddly
  sub-step:
  cyclic group ⟹ unique/characteristic order-`p` subgroup.)*
* **(step 5, `p ∉ β(M)`)** `X₁ ≤ O_p(M) ≤ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`) and
  `X₁ ≤ F(M)^g ≤ M^g`, so `X₁ ≤ M_σ ⊓ M^g`; Lemma 12.17 (`Msigma_inf_conj_isBetaCompl`) ⟹
  `p ∉ β(M)`,
  hence `r ≠ p` for the `β`-prime `r` (so the `r = p` case is vacuous).
* **(step 6, `C_G(X₁) ⊄ M`)** `fusion_control_of_mem_sigma` part (e) with `p ∈ σ(M)`, `X₁ ≤ M`,
  `conj g⁻¹ • X₁ ≤ M`.
* **(step 7, `rank C_{M_F}(X₁) < 3`)** `C_G(X₁) < ⊤` (else `X₁ ≤ Z(G) = ⊥`, simple), so a coatom
  `N ⊇ C_G(X₁)` exists with `N ≠ M`; `C_{M_F}(X₁) ≤ M ⊓ N` ⟹ `rank_lt_three_of_le_two_maximals`.
* **(step 8, bridge)** `O_r(M_F) ≤ C_{M_F}(X₁)` (`commute_of_coprime_orderOf_of_isNilpotent`, `r ≠ p`,
  both in nilpotent `F(M)`), so `r_r(M_F) = r_r(O_r(M_F)) ≤ rank C_{M_F}(X₁) < 3`.

Combined with `mf_eq_msigma_of_piSet_inf_beta_disjoint` this yields the `M_F = M_σ` conclusion of
Theorem 15.7(a), i.e. the `FittingIsTI` clause of Theorem A(8). -/
theorem piSet_mf_inf_beta_disjoint_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) :
    ∀ q : ℕ, q ∈ S14.piSet (MF M) → q ∉ OddOrder.BG.Ch3.S10.beta M := by
  intro r hrπ hrβ
  -- The `≥ 3` side (proved): `r ∈ π(M_F) ∩ β(M) ⟹ r_r(M_F) ≥ 3`.
  have h3 : 3 ≤ pRank ↥(MF M) r := three_le_pRank_mf_of_mem_beta hG hM hrπ hrβ
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrπ
  haveI : Fact r.Prime := ⟨hrp⟩
  refine absurd h3 (not_le.mpr ?_)
  -- Setup: `g ∉ M`, `X = F(M) ⊓ F(M)^g ≠ ⊥`.
  obtain ⟨g, hgM, hXne⟩ := exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI hnotTI
  -- A prime `p ∈ π(X)`, and `p ∈ σ(M)` (step 3).
  have hXcard : Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M) ≠ 1 :=
    fun h => hXne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hXcard
  haveI : Fact p.Prime := ⟨hp⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    mem_sigma_of_prime_dvd_card_inf_conj_fitting hG hM hgM hp hpdvd
  -- An order-`p` subgroup `X₁ ≤ X`.
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M)) p hpdvd
  set X₁ : Subgroup G :=
    (Subgroup.zpowers x).map (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype
    with hX₁def
  have hX₁leX : X₁ ≤ fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M :=
    hX₁def ▸ Subgroup.map_subtype_le _
  have hX₁card : Nat.card ↥X₁ = p := by
    rw [hX₁def, Subgroup.card_map_of_injective
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype_injective,
      Nat.card_zpowers, hxord]
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁F : X₁ ≤ fittingInAmbient M := hX₁leX.trans inf_le_left
  have hX₁cF : X₁ ≤ MulAut.conj g • fittingInAmbient M := hX₁leX.trans inf_le_right
  have hX₁M : X₁ ≤ M := hX₁F.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  -- Step 5: `p ∉ β(M)` (via `X₁ ≤ M_σ ⊓ M^g` and Lemma 12.17), hence `r ≠ p`.
  have hpσ_sub : ({p} : Set ℕ) ⊆ OddOrder.BG.Ch3.S10.sigma M := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  have hX₁Mσ : X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have h1 : X₁ ≤ opiCoreInG ({p} : Set ℕ) (fittingInAmbient M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hX₁F hX₁pg
    have h2 : opiCoreInG ({p} : Set ℕ) (fittingInAmbient M)
        ≤ opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσ_sub _)
    have h3' : opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M)
        = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
      opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
    exact (h1.trans h2).trans (h3' ▸ OddOrder.BG.Ch2.S08.fittingInG_le _)
  have hX₁cM : X₁ ≤ MulAut.conj g • M :=
    hX₁cF.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
      (OddOrder.BG.Ch2.S08.fittingInG_le M))
  have hpβ : p ∉ OddOrder.BG.Ch3.S10.beta M :=
    OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl hG hM hgM p
      (Nat.mem_primeFactors.mpr ⟨hp,
        hX₁card ▸ Subgroup.card_dvd_of_le (le_inf hX₁Mσ hX₁cM),
        Nat.card_pos.ne'⟩)
  have hrnep : r ≠ p := fun h => hpβ (h ▸ hrβ)
  -- Step 6: `C_G(X₁) ⊄ M` (Theorem 10.1(e)).
  have hconj_g_inv : MulAut.conj g⁻¹ • X₁ ≤ M := by
    have hle : MulAut.conj g⁻¹ • X₁ ≤ MulAut.conj g⁻¹ • (MulAut.conj g • fittingInAmbient M) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
    exact hle.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hCG
    have he := (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hpσ hX₁ne hX₁pg).2.2.2.2
    exact hgM (by simpa using inv_mem (he hX₁M hCG g⁻¹ hconj_g_inv))
  -- Step 7: `rank (C_{M_F}(X₁)) < 3` (`C_{M_F}(X₁)` lies in `M` and in a coatom `N ≠ M`).
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  have hCGlt : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
    lt_of_le_of_lt
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x₀.2))
      (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG
        (fun h => hx₀ne (Subtype.ext h)))
  obtain ⟨N, hNco, hCGN⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer (X₁ : Set G))).resolve_left hCGlt.ne
  have hNmax : N ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hNco
  have hNneM : M ≠ N := fun h => hCGnotM (h ▸ hCGN)
  have hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 :=
    rank_lt_three_of_le_two_maximals hG hM hNmax hNneM
      (inf_le_left.trans (maxNilpotentNormalHall_le M)) (inf_le_right.trans hCGN)
  -- Step 8: `r`-elements of `M_F` centralize `X₁` (coprime, `F(M)` nilpotent), so the `r`-Sylow of
  -- `M_F` lies in `C_{M_F}(X₁)`; hence `r ∤ [M_F : C_{M_F}(X₁)]` and
  -- `r_r(M_F) = r_r(C_{M_F}(X₁)) < 3`.
  haveI : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  have hcentr : ∀ A : Subgroup G, A ≤ MF M → IsPGroup r ↥A →
      A ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro A hAMF hAr a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have haF : a ∈ fittingInAmbient M := (hAMF.trans (maxNilpotentNormalHall_le_fittingInG M)) ha
    have hyF : y ∈ fittingInAmbient M := hX₁F hy
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hAr) ⟨a, ha⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hX₁pg) ⟨y, hy⟩
    have e1 : orderOf (⟨a, haF⟩ : ↥(fittingInAmbient M)) = r ^ i :=
      (orderOf_injective (fittingInAmbient M).subtype
        (fittingInAmbient M).subtype_injective ⟨a, haF⟩).symm.trans
        ((orderOf_injective A.subtype A.subtype_injective ⟨a, ha⟩).trans hi)
    have e2 : orderOf (⟨y, hyF⟩ : ↥(fittingInAmbient M)) = p ^ j :=
      (orderOf_injective (fittingInAmbient M).subtype
        (fittingInAmbient M).subtype_injective ⟨y, hyF⟩).symm.trans
        ((orderOf_injective X₁.subtype X₁.subtype_injective ⟨y, hy⟩).trans hj)
    have hcop : Nat.Coprime (orderOf (⟨a, haF⟩ : ↥(fittingInAmbient M)))
        (orderOf (⟨y, hyF⟩ : ↥(fittingInAmbient M))) := by
      rw [e1, e2]; exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hrp hp).mpr hrnep)
    have hcomm := OddOrder.BG.Ch3.S10.commute_of_coprime_orderOf_of_isNilpotent
      (x := (⟨a, haF⟩ : ↥(fittingInAmbient M))) (y := ⟨y, hyF⟩) hcop
    have := congrArg (Subtype.val) hcomm.eq
    simpa using this.symm
  -- The `r`-Sylow `P'` of `M_F` lies in `C_{M_F}(X₁) = M_F ⊓ C_G(X₁)`.
  obtain ⟨P⟩ : Nonempty (Sylow r ↥(MF M)) := inferInstance
  set P' : Subgroup G := (P : Subgroup ↥(MF M)).map (MF M).subtype with hP'def
  have hP'MF : P' ≤ MF M := hP'def ▸ Subgroup.map_subtype_le _
  have hP'r : IsPGroup r ↥P' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.2
    exact IsPGroup.of_card (by
      rw [hP'def, Subgroup.card_map_of_injective (MF M).subtype_injective, hn])
  have hP'C : P' ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) :=
    le_inf hP'MF (hcentr P' hP'MF hP'r)
  have hidx : ¬ r ∣ ((MF M ⊓ Subgroup.centralizer (X₁ : Set G)).subgroupOf (MF M)).index := by
    intro hdvd
    have hP'sub : P'.subgroupOf (MF M) ≤ (MF M ⊓ Subgroup.centralizer (X₁ : Set G)).subgroupOf (MF M) :=
      Subgroup.subgroupOf_mono (MF M) hP'C
    have hdvd2 : r ∣ (P'.subgroupOf (MF M)).index :=
      hdvd.trans (Subgroup.index_dvd_of_le hP'sub)
    have hPeq : P'.subgroupOf (MF M) = (P : Subgroup ↥(MF M)) :=
      hP'def ▸ Subgroup.comap_map_eq_self_of_injective (MF M).subtype_injective _
    rw [hPeq] at hdvd2
    exact P.not_dvd_index hdvd2
  calc pRank ↥(MF M) r
      = pRank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) r :=
        (OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index inf_le_left hidx).symm
    _ ≤ rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := pRank_le_rank r
    _ < 3 := hrank3

/-- **`M_F = M_σ` from `¬FittingIsTI`** (the `M_F = M_σ` conclusion of BG Theorem 15.7(a)):
combine the rank-theoretic core `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` with the
Theorem 15.2(b) endgame `mf_eq_msigma_of_piSet_inf_beta_disjoint`. -/
theorem mf_eq_msigma_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) : MF M = OddOrder.BG.Ch3.S10.Msigma M :=
  mf_eq_msigma_of_piSet_inf_beta_disjoint hG hM
    (piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI)

/-- **BG Theorem 15.7(c), `M' ≤ F(M)` for `¬FittingIsTI M`** (Coq `nonTI_Fitting_structure` `sM'F`):
the derived subgroup of a maximal subgroup whose Fitting subgroup is *not* `TI` is nilpotent, hence
`≤ F(M)`.

`M_F = M_σ` (`mf_eq_msigma_of_not_fittingIsTI`), and `M_β ≤ M_σ = M_F` is a `β(M)`-group
(`Mbeta_isPiGroup`; `β ⊆ α ⊆ σ` via `alpha_subset_sigma`), so `π(M_β) ⊆ π(M_F) ∩ β(M) = ∅`
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`), forcing `M_β = 1`. Then `M'/M_β ≅ M'` is
nilpotent
(`derivedQuotientMbeta_isNilpotent`), and the nilpotent normal `M'` lies in the Fitting subgroup
(`le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent`).  Sole upstream gate of the `E₃ = 1`
chain feeding Corollary 15.9's cyclic Frobenius complement (with
`tau3_eq_empty_of_derivedInG_le_fittingInAmbient` + `E3_eq_bot_of_tau3_eq_empty`). -/
theorem derivedInG_le_fittingInAmbient_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) : derivedInG M ≤ fittingInAmbient M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMFMσ : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  -- `M_β ≤ M_σ`: `M_β` is a normal `σ(M)`-subgroup (`β ⊆ α ⊆ σ`).
  have hMβσ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      (OddOrder.BG.Ch3.S10.Mbeta M) := fun p hp =>
    OddOrder.BG.Ch3.S10.alpha_subset_sigma hG hM (OddOrder.BG.Ch3.S10.Mbeta_isPiGroup M p hp).1
  have hMβnorm : ((OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Mbeta, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]; infer_instance
  have hMβMσ : OddOrder.BG.Ch3.S10.Mbeta M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    le_opiCoreInG_of_normal_of_isPiSubgroup (OddOrder.BG.Ch3.S10.Mbeta_le M) hMβnorm hMβσ
  -- `M_β = ⊥`: `π(M_β) ⊆ π(M_F) ∩ β(M) = ∅`.
  have hMβbot : OddOrder.BG.Ch3.S10.Mbeta M = ⊥ := by
    rw [← Subgroup.card_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpMβ : p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Mbeta M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpβ : p ∈ OddOrder.BG.Ch3.S10.beta M := OddOrder.BG.Ch3.S10.Mbeta_isPiGroup M p hpMβ
    have hpMF : p ∈ S14.piSet (MF M) := by
      change p ∈ (Nat.card ↥(MF M)).primeFactors
      rw [hMFMσ]
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le hMβMσ) Nat.card_pos.ne' hpMβ
    exact piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI p hpMF hpβ
  -- `M'` nilpotent: `M'/M_β ≅ M'` (`M_β = ⊥`), and `M'/M_β` is nilpotent (Corollary 10.7).
  have heq : (OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf (derivedInG M) = ⊥ := by
    rw [hMβbot, Subgroup.bot_subgroupOf]
  haveI hnorm2 : ((OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf (derivedInG M)).Normal := by
    rw [heq]; infer_instance
  haveI := OddOrder.BG.Ch3.S10.derivedQuotientMbeta_isNilpotent hG hM
  haveI hM'nil : Group.IsNilpotent ↥(derivedInG M) :=
    Group.nilpotent_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq heq).trans QuotientGroup.quotientBot)
  -- `M'` normal in `M` + nilpotent ⟹ `M' ≤ F(M)`.
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  haveI hM'norm : ((derivedInG M).subgroupOf M).Normal := by rw [hid]; infer_instance
  exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent (Subgroup.map_subtype_le _) hM'norm

/-- **BG Theorem 15.7(d), `E₃ = 1`** (Coq `nonTI_Fitting_structure` `E3_1`): the `τ₃(M)`-Hall factor of
any `σ(M)'`-complement `E`-setup is trivial when `F(M)` is not `TI`.  Composes the three parts:
`M' ≤ F(M)` (`derivedInG_le_fittingInAmbient_of_not_fittingIsTI`, part (c)) → `τ₃(M) = ∅`
(`tau3_eq_empty_of_derivedInG_le_fittingInAmbient`) → `E₃ = ⊥` (`E3_eq_bot_of_tau3_eq_empty`).  With
`τ₂(M) = ∅` (Theorem 15.8) forcing `E₂ = 1` too, `E = E₁` is cyclic (`E1_isCyclic`) — the cyclic
Frobenius complement of Corollary 15.9. -/
theorem E3_eq_bot_of_not_fittingIsTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnotTI : ¬ FittingIsTI M)
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃) : E₃ = ⊥ :=
  E3_eq_bot_of_tau3_eq_empty hsetup
    (tau3_eq_empty_of_derivedInG_le_fittingInAmbient hG hM
      (derivedInG_le_fittingInAmbient_of_not_fittingIsTI hG hM hnotTI))

/-- **BG Theorem A(8), the `FittingIsTI` clause** (mmd L4274, schematic proof: Theorem 15.7(a)(b)):
if `M_F ≠ M_σ`, then `F(M)` is a TI-subgroup of `G`.  This is the contrapositive of the
`M_F = M_σ` conclusion of Theorem 15.7(a) (`mf_eq_msigma_of_not_fittingIsTI`): if `F(M)` failed to
be TI, then `M_F` would equal `M_σ`.  Discharges the last (and deepest) conjunct of Theorem A(8),
modulo the single rank-theoretic residual `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`. -/
theorem fitting_isTI_of_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) : FittingIsTI M := by
  by_contra h
  exact hne (mf_eq_msigma_of_not_fittingIsTI hG hM h)

/-- **`IsTypeP2 M → FittingIsTI M`** — the type-classification conjunct (a) of BG Theorem 15.7
(mmd L4244): a type-`P₂` maximal subgroup has a TI Fitting subgroup.  Equivalently, every maximal
`M` with `¬FittingIsTI M` lies in `M_F ∪ M_{P₁}` (is type `F` or `P₁`, never `P₂`) — conjunct (a)
of `fitting_not_ti_cases`, separated out here because it is all that BG's §16 (Theorem C(10) /
Proposition 16.1) needs, and it is provable from the landed §15 pieces alone.

Proof (BG L4244): suppose `¬FittingIsTI M`.  Then `M_F = M_σ`
(`mf_eq_msigma_of_not_fittingIsTI`) and `π(M_F) ∩ β(M) = ∅`
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`).  But a type-`P₂` maximal subgroup has
`σ(M) = β(M)` (Proposition 14.2(g) = the type-`P₂` clause of `typeP_structure`), and `M_σ ≠ 1`
provides a prime `q ∈ π(M_σ) = π(M_F)` with `q ∈ σ(M) = β(M)`, contradicting the disjointness. -/
theorem fittingIsTI_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    FittingIsTI M := by
  classical
  by_contra hnotTI
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- Hall `κ(M)`- and `(κ ∪ σ)ᶜ`-subgroups `K`, `U` of `M`, as Proposition 14.2 needs.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- Proposition 14.2(g): a type-`P₂` maximal subgroup has `σ(M) = β(M)`.
  have hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M :=
    ((S14.typeP_structure hG hM hP2.1 hKM hK rfl hU).2.2.2.2.1 hP2).1
  -- `¬FittingIsTI`: `M_F = M_σ` and `π(M_F) ∩ β(M) = ∅`.
  have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  have hdisj := piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI
  -- `M_σ ≠ 1` gives a prime `q ∈ π(M_σ) = π(M_F)`, in `σ(M) = β(M)`: the contradiction.
  have hMσne1 : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := by
    rw [ne_eq, Subgroup.card_eq_one]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hMσne1
  have hqπMσ : q ∈ S14.piSet (OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, Nat.card_pos.ne'⟩
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM).1 q hqπMσ
  have hqMF : q ∈ S14.piSet (MF M) := by rw [hMFeq]; exact hqπMσ
  exact hdisj q hqMF (hσβ ▸ hqσ)

/-- **BG Theorem 15.7** (mmd L4180): if `F(M)` is not TI in `G`, then `M` is in
`M_F ∪ M_P1`, the relevant intersection is cyclic inside `M_F = M_sigma`, and
one of the three local cases of the theorem holds.

**Proof state (2026-06-21):** conjunct (a) `M ∈ M_F ∪ M_{P₁}` is discharged from
`fittingIsTI_of_isTypeP2` (the type-`P₂` exclusion) plus the F/P₁/P₂ trichotomy; conjunct (b)
`M_F = M_σ` from `mf_eq_msigma_of_not_fittingIsTI`.  In the `∃ X` clause, `X` is only required to
be *some* cyclic nontrivial subgroup of `M_F` (the Lean surface does not pin `X = F(M) ∩ F(M)ᵍ` as
BG does — a scaffold weakening), so it is supplied by an order-`q` element of `M_σ ≠ 1`; the prime
`p ∈ σ(M) ∖ β(M)` comes from that same `q` via the rank-core disjointness
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`), and the final disjunct follows from (a).

**Faithfulness fix (2026-06-22): conjunct (c) is `M' ≤ F(M)`, not the printed `M' = F(M)`.**  BG's
printed Theorem 15.7(c) asserts the *equality* `M' = F(M) = M_σ × O_{σ'}(F(M))`, but the equality is
an **overstatement** for the type-`F` case.  Verified two ways: (1) a ChatGPT (GPT-5 Pro) consult
plus an independent reduction shows `M' = F(M) ⟺ C_Y(E₁) = 1` (E₁ acts fixed-point-freely on the
τ₂-Fitting factor `Y = O_{σ'}(F(M))`), and `C_Y(E₁) = 1` is **not** derivable from the cited results
(Cor 12.6(d) is vacuous once `E₃ = 1`; the rest control the action on `M_σ`, not on `Y`); (2) the
authoritative MathComp odd-order formalization (`theories/BGsection15.v`, `nonTI_Fitting_structure`)
states conjunct (c) as `M^'(1) ⊆ 'F(M)` (inclusion) `∧ M_σ × O_σ('F(M)) = 'F(M)`, **not** equality —
its source comment explicitly records the change: *"We had to change the statement … the first
equality of part (c) does not appear to be valid: if M is of type F … E2 might have a Sylow subgroup
that meets F(M) but is also centralised by E1 and hence intersects M' trivially; … only the
inclusion
M' ⊆ F(M) seems to be needed in the sequel."*  (independently curl-verified, not via the consult).
Only `M' ≤ F(M)` is BG-faithful and provable; the equality holds iff `C_Y(E₁) = 1`, a non-derivable
condition (BG only gets `M` Frobenius later, in Corollary 15.9, after `τ₂(M) = ∅`, i.e. `E₂ = 1`).
See `notes/bg/s15_7_typeF_chatgpt_prompt.md`.

`M' ≤ F(M)` is proved here for the **type-`P₁`** case (`U = ⊥` ⟹ `M' = M_σ` by Lemma 15.1(b);
`M_σ = M_F` nilpotent ⟹ `M' = M_σ ≤ F(M)`).  The remaining residual is the **type-`F`** case of
`M' ≤ F(M)` — now **ungated** (the `= F(M)` gate `C_Y(E₁) = 1` is gone): `M' = M_σ × E'` with `E'`
centralizing `M_σ` (Lemma 12.19, as `π(M_σ) ∩ β = ∅`) is nilpotent normal, so `M' ≤ F(M)`; the
remaining work is the `E`-setup + nilpotent-direct-product packaging. -/
theorem fitting_not_ti_cases [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnotTI : ¬ FittingIsTI M) :
    (S14.IsTypeF M ∨ S14.IsTypeP1 M) ∧ MF M = OddOrder.BG.Ch3.S10.Msigma M ∧
      ∃ X : Subgroup G,
        X ≤ MF M ∧ X ≠ ⊥ ∧ IsCyclic ↥X ∧
        -- ⚠ conjunct (c) is `≤`, NOT `=`.  The BG book (Theorem 15.7(c)) prints the *equality*
        -- `M' = F(M)`, but that equality is an **overstatement** in the type-`F` case (it is
        -- equivalent to the non-derivable condition `C_Y(E₁) = 1`).  We therefore weakened it to the
        -- faithful inclusion `M' ⊆ F(M)`, matching the authoritative MathComp formalization
        -- (`nonTI_Fitting_structure`, which uses `M^'(1) ⊆ 'F(M)` and whose source comment states
        -- the
        -- printed equality "does not appear to be valid"). Full justification in the docstring
        -- above.
        derivedInG M ≤ fittingInAmbient M ∧
        (∃ p : ℕ, p.Prime ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
          p ∉ OddOrder.BG.Ch3.S10.beta M ∧
          (IsMulCommutative ↥(MF M) ∨
            ¬ IsMulCommutative ↥(MF M) ∧
              (S14.IsTypeF M ∨ S14.IsTypeP1 M))) := by
  -- (a) `M ∈ M_F ∪ M_{P₁}`: `¬FittingIsTI` excludes type `P₂` (`fittingIsTI_of_isTypeP2`),
  -- and every maximal subgroup is type `F`, `P₁`, or `P₂`.
  have ha : S14.IsTypeF M ∨ S14.IsTypeP1 M := by
    have hnP2 : ¬ S14.IsTypeP2 M := fun hP2 => hnotTI (fittingIsTI_of_isTypeP2 hG hM hP2)
    by_cases hP : S14.IsTypeP M
    · exact Or.inr ((S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP).resolve_right hnP2)
    · exact Or.inl (S14.isTypeF_iff_not_isTypeP.mpr hP)
  refine ⟨ha, mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI, ?_⟩
  -- The Lean `∃X` clause asks only for *some* cyclic nontrivial `X ≤ M_F` (not specifically
  -- `F(M) ∩ F(M)ᵍ`), with `M' = F(M)` and a prime `p ∈ σ ∖ β` as *independent* conjuncts, and the
  -- final disjunct follows from (a).  So the whole clause reduces to the single deep structural
  -- identity `M' = F(M)` (BG (c), via Corollary 15.5 + Lemma 12.1).
  have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  have hMσne1 : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := by
    rw [ne_eq, Subgroup.card_eq_one]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hMσne1
  haveI : Fact q.Prime := ⟨hqp⟩
  -- a prime `q ∈ π(M_σ) = π(M_F) ⊆ σ(M)`, with `q ∉ β(M)` by the rank-core disjointness.
  have hqπMσ : q ∈ S14.piSet (OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, Nat.card_pos.ne'⟩
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM).1 q hqπMσ
  have hqπMF : q ∈ S14.piSet (MF M) := by rw [hMFeq]; exact hqπMσ
  have hqβ : q ∉ OddOrder.BG.Ch3.S10.beta M :=
    piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI q hqπMF
  -- an order-`q` element `x ∈ M_σ = M_F` generates a cyclic nontrivial `X = ⟨x⟩ ≤ M_F`.
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have hwMF : (w : G) ∈ MF M := by rw [hMFeq]; exact w.2
  have hwne : (w : G) ≠ 1 := by
    have hw1 : w ≠ 1 := by
      intro hc; rw [hc, orderOf_one] at hw; exact hqp.ne_one hw.symm
    simpa using hw1
  refine ⟨Subgroup.zpowers (w : G), Subgroup.zpowers_le.mpr hwMF, ?_, ?_, ?_, q, hqp, hqσ, hqβ, ?_⟩
  · -- `X ≠ ⊥`
    exact fun h => hwne (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (w : G)))
  · -- `IsCyclic X`
    infer_instance
  · -- **`M' ≤ F(M)`** (BG conjunct (c), faithful form — see docstring: the printed `M' = F(M)` is an
    -- overstatement, MathComp `BGsection15` uses `M^'(1) ⊆ 'F(M)`). The argument is
    -- *type-independent*
    -- (covers both type `F` and type `P₁`): take a §12 `E`-setup `M = M_σ ⋊ E`, so
    -- `M' = M_σ ⊔ E'` (`derivedInG_eq_Msigma_sup_derivedInG_complement`). Lemma 12.19 supplies a
    -- Hall
    -- `β(M)'`-subgroup `W ≤ M_σ` of `M_σ` that `E'` centralizes; since `π(M_σ) = π(M_F)` is
    -- disjoint
    -- from `β(M)` (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`, as `M_F = M_σ`), `M_σ` is
    -- itself a
    -- `β'`-group, so `W = M_σ` and `E' ≤ C_G(M_σ)`. Then `M_σ ≤ F(M)` (`M_F = M_σ` nilpotent
    -- normal)
    -- and `E' ≤ C_G(M_σ) ⊓ M ≤ F(M)` (`fitting_decomposition`: `F(M) = (C_M(M_F) ⊓ M) ⊔ M_F`),
    -- whence
    -- `M' = M_σ ⊔ E' ≤ F(M)`.
    haveI : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    -- `M' = M_σ ⊔ E'`.
    rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG hsetup]
    -- Lemma 12.19: a Hall `β(M)'`-subgroup `W ≤ M_σ` of `M_σ` centralized by `E'`.
    obtain ⟨W, hWle, hWHall, hWcent⟩ := derivedE_centralizes_betaComplement hG hsetup
    -- `W = M_σ`: every prime of the index `[M_σ : W]` divides `|M_σ| = |M_F|`, hence lies in
    -- `π(M_F)`,
    -- which is disjoint from `β(M)`; but the Hall condition makes that index a `β`-number, so it is
    -- `1`.
    have hWeq : W = OddOrder.BG.Ch3.S10.Msigma M := by
      have hidx : (W.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index = 1 := by
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpβ : p ∈ OddOrder.BG.Ch3.S10.beta M := by
          by_contra hpc
          exact hWHall.2 p
            (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Subgroup.index_ne_zero_of_finite⟩) hpc
        have hpπ : p ∈ S14.piSet (MF M) := by
          rw [hMFeq]
          exact Nat.mem_primeFactors.mpr ⟨hpp,
            hpdvd.trans (W.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index_dvd_card,
            Nat.card_pos.ne'⟩
        exact piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI p hpπ hpβ
      exact le_antisymm hWle (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx))
    -- `M_σ ≤ F(M)` (`M_σ = M_F`, nilpotent normal).
    have hMσF : OddOrder.BG.Ch3.S10.Msigma M ≤ fittingInAmbient M :=
      hMFeq ▸ le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent
        (maxNilpotentNormalHall_le M) (maxNilpotentNormalHall_subgroupOf_normal M)
    -- `E' ≤ C_G(M_σ) ⊓ M ≤ F(M)`.
    have hE'F : derivedInG E ≤ fittingInAmbient M := by
      have hE'cent : derivedInG E ≤ Subgroup.centralizer (MF M : Set G) := by
        rw [hMFeq, ← hWeq]; exact hWcent
      have hE'M : derivedInG E ≤ M := (Subgroup.map_subtype_le _).trans hsetup.E_le
      obtain ⟨Y, -, -, -, -, hFdecomp, -, -, -, -, -, -⟩ := fitting_decomposition hG hM
      rw [hFdecomp]
      exact le_sup_of_le_left (le_inf hE'cent hE'M)
    exact sup_le hMσF hE'F
  · -- final disjunct: from (a).
    by_cases h : IsMulCommutative ↥(MF M)
    · exact Or.inl h
    · exact Or.inr ⟨h, ha⟩

/-- **BG Corollary 15.5(b) consequence** (mmd L4219-4226): for a type-`P₂` maximal subgroup `M`
with `τ₂(M) = ∅`, the Fitting subgroup is exactly `M_σ`.

From `fitting_decomposition`'s `F(M) = F(M_σ) ⊔ Y`, where `Y = O_{σ(M)'}(F(M))` is a cyclic
`τ₂(M)`-group (Corollary 15.5(a)): `Y.primeFactors ⊆ τ₂(M) = ∅` forces `Y = ⊥`, and `F(M_σ) = M_σ`
since `M_σ` is nilpotent for type `P₂`.  This is the `Y = ⊥` content behind Peterfalvi (8.6.b II)'s
`(M')_F = H = M_σ`; the single residual gate is `τ₂(M) = ∅` (BG Theorem 15.8,
`tau2_transfer_constraint`). -/
theorem fittingInAmbient_eq_Msigma_of_isTypeP2_of_tau2_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : S14.IsTypeP2 M) (htau2 : tau2 M = ∅) :
    fittingInAmbient M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  obtain ⟨Y, -, hYpf, -, -, -, h6, -, -, -, -, -⟩ := fitting_decomposition hG hM
  haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    msigma_isNilpotent_of_isTypeP2 hG hM hP2
  -- `Y = ⊥`: its order has no prime factors, since they would lie in `τ₂(M) = ∅`.
  have hYbot : Y = ⊥ := by
    have hpf : (Nat.card ↥Y).primeFactors = ∅ := by
      rw [← Finset.coe_eq_empty, ← Set.subset_empty_iff]
      rw [htau2] at hYpf
      exact hYpf
    rcases Nat.primeFactors_eq_empty.mp hpf with h0 | h1
    · exact absurd h0 Nat.card_pos.ne'
    · exact Subgroup.card_eq_one.mp h1
  rw [h6, hYbot, sup_bot_eq, fittingInAmbient_eq_self_of_isNilpotent]

/-- **`maxNilpotentNormalHall N` is `M`-normal when `N ◁ M`** (`N ≤ M`).  `maxNilpotentNormalHall N`
is a priori only normal in `N`; this upgrades it to normality in the larger `M`: each `g ∈ M`
conjugates `N` to itself (`N ◁ M`), and `maxNilpotentNormalHall_pointwise_smul` transports this to
`maxNilpotentNormalHall N`, so `M ≤ N_G(maxNilpotentNormalHall N)`. -/
theorem maxNilpotentNormalHall_subgroupOf_normal_of_le_of_normal [Finite G] {N M : Subgroup G}
    (hNM : N ≤ M) (hnorm : (N.subgroupOf M).Normal) :
    ((maxNilpotentNormalHall N).subgroupOf M).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((maxNilpotentNormalHall_le N).trans hNM)]
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hnorm hg
  have hNfix : N.map (MulAut.conj g).toMonoidHom = N :=
    OddOrder.BG.Ch1.S03f.map_conj_eq_self_of_mem_normalizer hgN
  have hNsmul : (MulAut.conj g) • N = N := by
    rw [pointwise_mulAut_smul_eq_map]; exact hNfix
  have key := maxNilpotentNormalHall_pointwise_smul (MulAut.conj g) N
  rw [hNsmul, pointwise_mulAut_smul_eq_map] at key
  exact OddOrder.BG.Ch1.S03f.mem_normalizer_of_map_conj_eq key

/-- **Peterfalvi (8.6.b II) `(M')_F = H = M_σ`, reduced to `τ₂(M) = ∅`** (the deep gate = BG
Theorem 15.8).  For a type-`P₂` maximal `M` with `τ₂(M) = ∅`, the Fitting core of the derived
subgroup `M'` is `M_σ`:

* `⊆`: `maxNilpotentNormalHall M'` is `M`-normal (`M' ◁ M` + the equivariance helper) and nilpotent,
  hence `≤ F(M) = M_σ` (`fittingInAmbient_eq_Msigma_of_isTypeP2_of_tau2_empty`).
* `⊇`: `M_σ` is a nilpotent normal Hall subgroup of `M'` (`M_σ ≤ M'` is Lemma 15.1(a); Hall because
  `[M' : M_σ] ∣ [M : M_σ]` and `M_σ` is `σ`-Hall in `M`).

This discharges the `hderfit` input of `isTypeII_of_isTypeP2_of_derived_typeF`; the single residual
gate is `τ₂(M) = ∅` (BG Theorem 15.8, `tau2_transfer_constraint`). -/
theorem maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2_of_tau2_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : S14.IsTypeP2 M) (htau2 : tau2 M = ∅) :
    maxNilpotentNormalHall (derivedInG M) = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  haveI hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    msigma_isNilpotent_of_isTypeP2 hG hM hP2
  have hFMσ : fittingInAmbient M = OddOrder.BG.Ch3.S10.Msigma M :=
    fittingInAmbient_eq_Msigma_of_isTypeP2_of_tau2_empty hG hM hP2 htau2
  have hMσnormM : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hM'normM : ((derivedInG M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM'M]
    exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  refine le_antisymm ?_ ?_
  · -- `⊆`
    haveI : Group.IsNilpotent ↥(maxNilpotentNormalHall (derivedInG M)) :=
      maxNilpotentNormalHall_isNilpotent (derivedInG M)
    have hnorm : ((maxNilpotentNormalHall (derivedInG M)).subgroupOf M).Normal :=
      maxNilpotentNormalHall_subgroupOf_normal_of_le_of_normal hM'M hM'normM
    have hle := le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent
      ((maxNilpotentNormalHall_le (derivedInG M)).trans hM'M) hnorm
    rwa [hFMσ] at hle
  · -- `⊇` : `M_σ` is a nilpotent normal Hall subgroup of `M'`.
    refine le_maxNilpotentNormalHall hMσM' ?_ ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMσM']
      exact hM'M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMσM).mp hMσnormM)
    · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσM').symm
    · -- `M_σ` Hall in `M'`.
      have hHallM : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
        OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
      have hcard' : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM').toEquiv
      have hcardM : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
      -- `[M' : M_σ] ∣ [M : M_σ]` via `card M_σ · [M':M_σ] = card M' ∣ card M = card M_σ · [M:M_σ]`.
      have hidxdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
        have e1 := Subgroup.card_mul_index
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M))
        have e2 := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        rw [hcard'] at e1; rw [hcardM] at e2
        have hM'dvdM : Nat.card ↥(derivedInG M) ∣ Nat.card ↥M := by
          have h := Subgroup.card_subgroup_dvd_card ((derivedInG M).subgroupOf M)
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv] at h
        have hmul : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
            Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
          rw [e1, e2]; exact hM'dvdM
        exact (mul_dvd_mul_iff_left (Nat.card_pos
          (α := ↥(OddOrder.BG.Ch3.S10.Msigma M))).ne').mp hmul
      refine ⟨fun p hp => by rwa [hcard'] at hp, fun p hp hpπ => ?_⟩
      have hpidxM : p ∈ (((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index).primeFactors := by
        obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hidxdvd, Subgroup.index_ne_zero_of_finite⟩
      have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := hHallM.1 p (by rw [hcardM]; exact hpπ)
      exact hHallM.2 p hpidxM hpσ

/-- **Coprime order/index ⟹ self-`primeFactors`-Hall**: if `H ≤ V` and `|H|` is coprime to the
relative index `[V : H]`, then `H` is a `π(H)`-Hall subgroup of `V` (the `π = π(H)` instance of
`IsHallSubgroup`).  This is the BG-side mirror of the Peterfalvi helper
`isHall_subgroupOf_primeFactors_of_coprime_index`. -/
theorem isHallSubgroup_primeFactors_of_coprime_index [Finite G] {V H : Subgroup G}
    (hHV : H ≤ V) (hcop : Nat.Coprime (Nat.card ↥H) ((H.subgroupOf V).index)) :
    Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors (H.subgroupOf V) := by
  have hcard : Nat.card ↥(H.subgroupOf V) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  refine ⟨fun p hp => by rw [hcard] at hp; exact hp, fun p hp hpπ => ?_⟩
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hpπ).2.1
    (Nat.mem_primeFactors.mp hp).2.1
  exact absurd (Nat.dvd_one.mp hp1) (Nat.mem_primeFactors.mp hp).1.ne_one

/-- **Hall transitivity (coprime form)**: for `L ≤ Mid ≤ M`, if `|L|` is coprime to `[Mid : L]`
and `|Mid|` is coprime to `[M : Mid]`, then `|L|` is coprime to `[M : L]`.  The relative index is
multiplicative (`relIndex_mul_relIndex`), `|L| ∣ |Mid|`, and `|Mid|` coprime `[M:Mid]` transfers
to `|L|`. -/
theorem coprime_card_index_subgroupOf_trans [Finite G] {L Mid M : Subgroup G}
    (hLMid : L ≤ Mid) (hMidM : Mid ≤ M)
    (hL : Nat.Coprime (Nat.card ↥L) ((L.subgroupOf Mid).index))
    (hMid : Nat.Coprime (Nat.card ↥Mid) ((Mid.subgroupOf M).index)) :
    Nat.Coprime (Nat.card ↥L) ((L.subgroupOf M).index) := by
  have hmul : (L.subgroupOf Mid).index * (Mid.subgroupOf M).index = (L.subgroupOf M).index := by
    have h := Subgroup.relIndex_mul_relIndex L Mid M hLMid hMidM
    simpa only [Subgroup.relIndex] using h
  rw [← hmul]
  exact Nat.Coprime.mul_right hL (hMid.coprime_dvd_left (Subgroup.card_dvd_of_le hLMid))

/-- **`(M')_F = M_σ` for type-`P₂`, unconditional** (Coq `defM'F`, BGsection16.v l.1135; the
`M'`_\F = H` conjunct of `of_typeII`).  For a type-`P₂` maximal `M` with cyclic `κ`-Hall `K`, the
`F`-core of the derived subgroup `M' = M^{(1)}` is exactly `M_σ` — with **no** `τ₂(M) = ∅`
hypothesis.

The argument is elementary (and *avoids* the `τ₂(M) = ∅` route, which is moreover false for some
type-`P₂` `M`, cf. Corollary 15.9's `N ∈ ℳ_𝓟₂` with `r ∈ τ₂(N)`):

* `⊆`: `M' = M^{(1)}` complements the cyclic `κ`-Hall `K` in `M`
  (`typeP_derivedInG_isComplement_kappaHall`), so `M'` is a `κ(M)'`-Hall subgroup of `M`.  Hence
  `maxNilpotentNormalHall M'`, Hall in `M'` by `maxNilpotentNormalHall_isHall`, is — by Hall
  transitivity — a nilpotent normal Hall subgroup of `M`, so `≤ M_F = M_σ`
  (`le_maxNilpotentNormalHall`, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`).
* `⊇`: `M_σ` is a nilpotent normal Hall subgroup of `M'` (`[M':M_σ] ∣ [M:M_σ]`).

This discharges both the `hderfit` (`maxNilpotentNormalHall M' = maxNilpotentNormalHall M`) and the
`TypeFData.H_eq` inputs of the type-`P₂ ⟹ II` bridge. -/
theorem maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    maxNilpotentNormalHall (derivedInG M) = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  haveI hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    msigma_isNilpotent_of_isTypeP2 hG hM hP2
  have hMσnormM : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hM'normM : ((derivedInG M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM'M]
    exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  -- `M_F = M_σ` for type-`P₂` (`M_σ` nilpotent).
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hMσnil
  -- `M' = M^{(1)}` complements the `κ`-Hall `K`, hence is `κ'`-Hall in `M`.
  have hcompl := typeP_derivedInG_isComplement_kappaHall hG hM (isTypeP_of_isTypeP2 hP2) hKM hK
  have hM'cop : Nat.Coprime (Nat.card ↥(derivedInG M)) (((derivedInG M).subgroupOf M).index) := by
    have hcop_BA : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
        (Nat.card ↥((derivedInG M).subgroupOf M)) := by
      have h := hK.coprime_index
      rwa [hcompl.index_eq_card] at h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv, hcompl.symm.index_eq_card]
    exact hcop_BA.symm
  refine le_antisymm ?_ ?_
  · -- `⊆`: `maxNilpotentNormalHall M'` is nilpotent normal Hall in `M`, hence `≤ M_F = M_σ`.
    have hLM' : maxNilpotentNormalHall (derivedInG M) ≤ derivedInG M :=
      maxNilpotentNormalHall_le (derivedInG M)
    have hLM : maxNilpotentNormalHall (derivedInG M) ≤ M := hLM'.trans hM'M
    haveI : Group.IsNilpotent ↥(maxNilpotentNormalHall (derivedInG M)) :=
      maxNilpotentNormalHall_isNilpotent (derivedInG M)
    -- `maxNilpotentNormalHall M'` is coprime to `[M':·]` (Hall in `M'`).
    have hLcopMid : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (derivedInG M)))
        (((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).index) := by
      have h := (maxNilpotentNormalHall_isHall (derivedInG M)).coprime_index
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM').toEquiv] at h
    -- transitivity ⟹ coprime to `[M:·]`.
    have hLcopM : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (derivedInG M)))
        (((maxNilpotentNormalHall (derivedInG M)).subgroupOf M).index) :=
      coprime_card_index_subgroupOf_trans hLM' hM'M hLcopMid hM'cop
    have hLnorm : ((maxNilpotentNormalHall (derivedInG M)).subgroupOf M).Normal :=
      maxNilpotentNormalHall_subgroupOf_normal_of_le_of_normal hM'M hM'normM
    have hLnil : Group.IsNilpotent ↥((maxNilpotentNormalHall (derivedInG M)).subgroupOf M) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLM).symm
    have hLhall := isHallSubgroup_primeFactors_of_coprime_index hLM hLcopM
    calc maxNilpotentNormalHall (derivedInG M)
        ≤ maxNilpotentNormalHall M := le_maxNilpotentNormalHall hLM hLnorm hLnil hLhall
      _ = OddOrder.BG.Ch3.S10.Msigma M := hMFMσ
  · -- `⊇` : `M_σ` is a nilpotent normal Hall subgroup of `M'`.
    refine le_maxNilpotentNormalHall hMσM' ?_ ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMσM']
      exact hM'M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMσM).mp hMσnormM)
    · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσM').symm
    · -- `M_σ` Hall in `M'`.
      have hHallM : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
        OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
      have hcard' : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM').toEquiv
      have hcardM : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
      have hidxdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
        have e1 := Subgroup.card_mul_index
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M))
        have e2 := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        rw [hcard'] at e1; rw [hcardM] at e2
        have hM'dvdM : Nat.card ↥(derivedInG M) ∣ Nat.card ↥M := by
          have h := Subgroup.card_subgroup_dvd_card ((derivedInG M).subgroupOf M)
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv] at h
        have hmul : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
            Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
          rw [e1, e2]; exact hM'dvdM
        exact (mul_dvd_mul_iff_left (Nat.card_pos
          (α := ↥(OddOrder.BG.Ch3.S10.Msigma M))).ne').mp hmul
      refine ⟨fun p hp => by rwa [hcard'] at hp, fun p hp hpπ => ?_⟩
      have hpidxM : p ∈ (((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index).primeFactors := by
        obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hidxdvd, Subgroup.index_ne_zero_of_finite⟩
      have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := hHallM.1 p (by rw [hcardM]; exact hpπ)
      exact hHallM.2 p hpidxM hpσ

/-- **BG Theorem 14.7(f) / Proposition 14.2(g), type-`P₂` case** (mmd L4264, the first sentence of
Theorem 15.8's proof: *"By Theorem 14.7(f), `|K| = q`"*): for a type-`P₂` maximal subgroup `M` and a
Hall `κ(M)`-subgroup `K ≤ M`, the order `|K|` is prime.

This is the `∃ q, q.Prime ∧ |K| = q` half of the Proposition 14.2(g) clause packaged inside
`typeP_structure`, specialised to the *given* `K` (rather than the partner's `Kstar`, as in
`kstar_card_prime_of_inputs`).  Proof: build the required Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of the
solvable `M` by Hall's theorem (`Ch03.hall_E_exists`) and set `Kstar = C_{M_σ}(K)`; then the
`IsTypeP2 M →` conjunct of `typeP_structure` delivers `∃ q, q.Prime ∧ Nat.card ↥K = q`. -/
theorem card_kappaHall_prime_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) :
    ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of the solvable `M` (Hall's theorem), lifted to an
  -- ambient `U' ≤ M` with `(U'.map).subgroupOf M` Hall (as in `exists_typeP_data`).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `typeP_structure` on `M` with the *given* `K`; its `IsTypeP2 M →` conjunct is
  -- `σ(M) = β(M) ∧ ∃ q, q.Prime ∧ Nat.card ↥K = q ∧ IsTISubset …`.
  obtain ⟨_hσβ, q, hq, hKq, _hTI⟩ :=
    (S14.typeP_structure hG hM hP2.1 hKM hK rfl hU).2.2.2.2.1 hP2
  exact ⟨q, hq, hKq⟩

/-- **Phase B foundation of BG Theorem 15.8** (Coq `Ptype_embedding` step): the type-`P₂`
maximal `M`'s partner `M*` — realized as any maximal `Mstar ∈ 𝓜(C(K))` — is type-`P`, has
`κ(Mstar)`-Hall `Ks := M_σ ⊓ C(K)`, and satisfies `K = Mstar_σ ⊓ C(Ks)`.

Proof: `typeP_duality` supplies the unique nonconjugate type-`P` partner `Mst` with exactly this
structure; `typeP_structure` (conjunct 6, with `K ∈ ℰ_q¹`) gives `𝓜(C(K)) = {Mst}`, so the
given `Mstar ∈ 𝓜(C(K))` equals `Mst`. -/
theorem typeP2_partner_structure_of_mem [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G))) :
    S14.IsTypeP Mstar ∧
      Ch03.IsHallSubgroup (S14.kappa Mstar)
        ((OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Mstar) ∧
      K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer
        ((OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) :
          Subgroup G) : Set G) ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤ Mstar := by
  classical
  have hP : S14.IsTypeP M := hP2.1
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨q, hqprime, hKcard⟩ := card_kappaHall_prime_of_isTypeP2 hG hM hP2 hKM hK
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  -- The unique nonconjugate type-`P` partner `Mst` (Theorem 14.7 / `typeP_duality`).
  obtain ⟨Mst, hMstprop, _hMstuniq⟩ := (S14.typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, _hMnc, hMstpair, _hZcyc, _hZti, _hP2or, _hcover⟩ := hMstprop
  -- `𝓜(C(K)) = {Mst}` (`typeP_structure` conjunct 6 for `Mst`, rank-one `K ∈ ℰ_q¹`).
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    haveI hMstsol : IsSolvable ↥Mst := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((S14.kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (S14.kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (S14.typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  -- `Mstar = Mst`, so it inherits `Mst`'s partner structure.
  have hMstarEq : Mstar = Mst := by
    have hmem : Mstar ∈ ({Mst} : Set (Subgroup G)) := huniqMst ▸ hMstar
    exact Set.eq_of_mem_singleton hmem
  subst hMstarEq
  exact ⟨hMstP, hMstpair.2.1, hMstpair.2.2, hMstpair.1⟩

/-- **Phase A of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, up to `cKA`): from the
σ(H)′-Hall `E`-setup of a maximal `H` (the Corollary 14.12 signalizer neighbour supplied by
`typeP2_neighbor_is_typeF_of_mem`), a `κ`-Hall `K ⊆ F(E)`, and a prime `q₁ ∈ τ₂(H)`,
there is a rank-2 elementary abelian `A ≤ E` for `q₁` that centralizes `K`.

Proof (Coq `cKA`): extract `A ∈ ℰ²_{q₁}(E)` (`exists_elemAb_rank_two_le_E_of_tau2`); then
`A ⊴ E` (`elemAb_normal_in_E_of_tau2`) and `A` is a `q₁`-group, so `A ⊆ F(E)`
(`le_fittingInG_of_normal_isPiSubgroup_singleton`).  `F(E)` is a nilpotent σ(H)′-subgroup of `H`,
hence abelian (`nilpotent_sigmaComplement_abelian`, BG Cor 12.10).  As `A, K ⊆ F(E)` abelian,
`A ⊆ C(K)`. -/
theorem exists_rank2_elemAb_le_centralizer_kappa_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H K E E₁ E₂ E₃ : Subgroup G}
    (hEsetup : SubgroupESetup H E E₁ E₂ E₃)
    (hKFE : K ≤ OddOrder.BG.Ch2.S08.fittingInG E)
    {q1 : ℕ} (hq1prime : q1.Prime) (hq1 : q1 ∈ tau2 H) :
    ∃ A : Subgroup G, A ∈ elemAbelianOfRank G q1 2 ∧ A ≤ E ∧
      A ≤ Subgroup.centralizer (K : Set G) := by
  classical
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  obtain ⟨A, hA_elem, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hEsetup hq1
  refine ⟨A, hA_elem, hAE, ?_⟩
  -- `A ⊴ E` (Coq `nsAD`).
  have hEnA : E ≤ Subgroup.normalizer (A : Set G) :=
    ((elemAb_normal_in_E_of_tau2 hG hEsetup hq1 hA_elem hAE).1).1
  have hAnormE : (A.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mpr hEnA
  -- `A` is a `q₁`-group, so `A ⊆ F(E)`.
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA_elem
  have hApi : Subgroup.IsPiSubgroup ({q1} : Set ℕ) A :=
    isPiSubgroup_singleton_of_isPGroup hAea.isPGroup
  have hAFE : A ≤ OddOrder.BG.Ch2.S08.fittingInG E :=
    OddOrder.BG.Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hAE hAnormE hApi
  -- `F(E)` is a nilpotent σ(H)′-subgroup of `H`, hence abelian (Coq `sigma'_nil_abelian`).
  have hFEnil : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E
  have hFEleH : OddOrder.BG.Ch2.S08.fittingInG E ≤ H :=
    (OddOrder.BG.Ch2.S08.fittingInG_le E).trans hEsetup.E_le
  have hFEpi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma H)ᶜ)
      (OddOrder.BG.Ch2.S08.fittingInG E) := fun p hp =>
    hEsetup.isPiGroup_sigma_compl hG p
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (OddOrder.BG.Ch2.S08.fittingInG_le E))
        Nat.card_pos.ne' hp)
  have hFEab : IsMulCommutative ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
    (nilpotent_sigmaComplement_abelian hG hEsetup).1 _ hFEleH hFEpi hFEnil
  -- `A, K ⊆ F(E)` abelian ⟹ `A ⊆ C(K)`.
  exact le_centralizer_of_le_of_le hFEab hAFE hKFE

/-- **Phase D core of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, the `apply/pgroupP` step,
BGsection15.v:1383--1392): for a maximal `M` with an abelian Hall `(κ(M)∪σ(M))'`-subgroup `U ≤ M`
(Proposition 14.2(a); `κ`-Hall `K` normalizing `U`), *every* prime `r ∈ τ₂(M)` that divides `|U|`
has `C_G(U) ≤ M`.

This is the reusable per-prime heart of the final `τ₂(M) = ∅` argument: given the escape witness
`¬(C_G(U) ≤ M)`, it forces `τ₂(M)` to contain no such prime.

Proof (Coq): `r ∈ τ₂(M) ⊆ σ(M)'` and `r ∉ κ(M)` (κ-primes have `pRank ≤ 1`, `r` has `pRank 2`),
so `r ∈ (κ(M)∪σ(M))'`, the prime class of `U`.  Take a §12 `E`-setup with `M_σ`-complement `E ⊇ U`
(`exists_subgroupESetup_with_le`, `U` a `σ(M)'`-subgroup), and a rank-2 `B ∈ ℰ²_r(E)`
(`exists_elemAb_rank_two_le_E_of_tau2`).  Then `B ⊴ E` (`elemAb_normal_in_E_of_tau2`) and
`C_G(B) ≤ E ≤ M` (`centralizer_le_E_of_tau2`, = Corollary 12.6(b)).  Inside `↥E`, `B.subgroupOf E`
is a *normal* `(κ∪σ)'`-subgroup and `U.subgroupOf E` is a `(κ∪σ)'`-Hall (transferred from
`hU`), so `B ⊆ U` (`Subgroup.IsPiGroup.normal_le_hall`, Coq `normal_sub_max_pgroup`).  Hence
`C_G(U) ≤ C_G(B) ≤ M`. -/
theorem centralizer_kappaCompl_le_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M U K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (_hKM : K ≤ M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (_hKNU : K ≤ Subgroup.normalizer (U : Set G))
    {r : ℕ} (hrprime : r.Prime) (hr : r ∈ tau2 M) (_hrU : r ∈ piSet U) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  classical
  haveI : Fact r.Prime := ⟨hrprime⟩
  -- `r ∉ κ(M)`: κ-primes lie in `τ₁ ∪ τ₃` (`pRank ≤ 1`), but `r ∈ τ₂` has `pRank = 2`.
  have hrκ : r ∉ kappa M := by
    intro hrk
    rcases kappa_subset_tau1_union_tau3 hrk with h1 | h3
    · have := tau1_pRank_eq_one h1; have := tau2_pRank_eq_two hr; omega
    · have := tau3_pRank_eq_one h3; have := tau2_pRank_eq_two hr; omega
  have hrσ : r ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hr
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := fun h => h.elim hrκ hrσ
  -- `U` is a `σ(M)'`-subgroup (its prime class `(κ∪σ)'` is contained in `σ'`).
  have hU_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) U := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
    exact fun hpσ => hU.1 p hp (Or.inr hpσ)
  -- A §12 `E`-setup with `M_σ`-complement `E ⊇ U`.
  obtain ⟨E, E₁, E₂, E₃, hEsetup, hUE, _hEpi⟩ :=
    exists_subgroupESetup_with_le hG hM hUM hU_pi
  -- A rank-2 elementary abelian `B ∈ ℰ²_r(E)`.
  obtain ⟨B, hB_elem, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hEsetup hr
  -- `C_G(B) ≤ E ≤ M` (Cor 12.6(b)).
  have hCBE : Subgroup.centralizer (B : Set G) ≤ E :=
    (centralizer_le_E_of_tau2 hG hEsetup hr hB_elem hBE).1
  have hCBM : Subgroup.centralizer (B : Set G) ≤ M := hCBE.trans hEsetup.E_le
  -- `B ⊴ E` (Coq `nsBUK`).
  have hEnB : E ≤ Subgroup.normalizer (B : Set G) :=
    ((elemAb_normal_in_E_of_tau2 hG hEsetup hr hB_elem hBE).1).1
  have hBnormE : (B.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mpr hEnB
  -- `B ⊆ U`: `B.subgroupOf E` is a normal `(κ∪σ)'`-subgroup of `↥E`, and `U.subgroupOf E` is a
  -- `(κ∪σ)'`-Hall of `↥E`, so the normal π-subgroup lands inside the Hall.
  have hBU : B ≤ U := by
    -- `B` is a `{r}`-group with `r ∈ (κ∪σ)'`, hence a `(κ∪σ)'`-group.
    have hB_pi : Ch03.Subgroup.IsPiGroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) B := by
      intro p hp
      obtain ⟨hae, hcard⟩ := mem_elemAbelianOfRank.mp hB_elem
      have hpr : p = r := by
        have hpd : p ∈ (r ^ 2).primeFactors := hcard ▸ hp
        rw [Nat.primeFactors_prime_pow (by norm_num) hrprime, Finset.mem_singleton] at hpd
        exact hpd
      exact hpr ▸ hrκσ
    have hB_piE : Ch03.Subgroup.IsPiGroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        (B.subgroupOf E) := Ch03.Subgroup.IsPiGroup.subgroupOf hBE hB_pi
    -- `U.subgroupOf E` is a `(κ∪σ)'`-Hall of `↥E`: prime factors of `|U|` stay in the class, and
    -- `[E : U] ∣ [M : U]` has no primes in the class.
    have hUhallE : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        (U.subgroupOf E) := by
      refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUE).toEquiv] at hp
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
        exact hU.1 p hp
      · have hdvd : (U.subgroupOf E).index ∣ (U.subgroupOf M).index := by
          have hmul : U.relIndex E * E.relIndex M = U.relIndex M :=
            Subgroup.relIndex_mul_relIndex U E M hUE hEsetup.E_le
          exact ⟨E.relIndex M, hmul.symm⟩
        refine hU.2 p ?_ hpπ
        rw [Nat.mem_primeFactors] at hp ⊢
        exact ⟨hp.1, hp.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩
    have := (hB_piE.normal_le_hall hUhallE)
    intro x hx
    have hxE : x ∈ E := hBE hx
    have : (⟨x, hxE⟩ : ↥E) ∈ U.subgroupOf E := this (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp this
  -- `C_G(U) ≤ C_G(B) ≤ M`.
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBU)).trans hCBM

/-- **BG Theorem 15.8, final `τ₂(M) = ∅` step for primes** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1383, the `pgroupP` conclusion): under the signalizer escape witness
`¬(C_G(U) ≤ M)`, no *prime* lies in `τ₂(M)`.

Proof: for a prime `r ∈ τ₂(M)`, `r ∣ |M|` (positive `pRank`) and `r ∈ (κ(M)∪σ(M))'`, so `r ∣ |U|`
(`U` is the `(κ∪σ)'`-Hall of `M`, whose order carries the full `r`-part of `|M|`); then
`centralizer_kappaCompl_le_of_mem_tau2` gives `C_G(U) ≤ M`, contradicting the escape witness.

(Stated in prime form `∀ r, r.Prime → r ∉ τ₂(M)`, matching how the repo threads `τ₂` primality
throughout §12; the literal set-equality `τ₂(M) = ∅` additionally rules out composite labels via
the `pRank`-of-non-prime degeneracy, handled where the full theorem is assembled.) -/
theorem not_prime_mem_tau2_of_centralizer_kappaCompl_not_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M U K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hesc : ¬ (Subgroup.centralizer (U : Set G) ≤ M)) :
    ∀ r : ℕ, r.Prime → r ∉ tau2 M := by
  intro r hrprime hr
  haveI : Fact r.Prime := ⟨hrprime⟩
  -- `r ∈ (κ(M)∪σ(M))'` (as in `centralizer_kappaCompl_le_of_mem_tau2`).
  have hrκ : r ∉ kappa M := by
    intro hrk
    rcases kappa_subset_tau1_union_tau3 hrk with h1 | h3
    · have := tau1_pRank_eq_one h1; have := tau2_pRank_eq_two hr; omega
    · have := tau3_pRank_eq_one h3; have := tau2_pRank_eq_two hr; omega
  have hrσ : r ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hr
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := fun h => h.elim hrκ hrσ
  -- `r ∣ |M|` (positive `pRank`), and `r ∤ [M : U]` (Hall), so `r ∣ |U| = |U.subgroupOf M|`.
  have hrM : r ∈ (Nat.card ↥M).primeFactors :=
    OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank
      (by rw [tau2_pRank_eq_two hr]; norm_num)
  have hrUsub : r ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
    have hlag : Nat.card ↥(U.subgroupOf M) * (U.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (U.subgroupOf M).index := fun hd =>
      hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) hrκσ
    have hrdvdM : r ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors hrM
    have hrU : r ∣ Nat.card ↥(U.subgroupOf M) :=
      ((Nat.Prime.dvd_mul hrprime).mp (by rw [hlag]; exact hrdvdM)).resolve_right hridx
    exact Nat.mem_primeFactors.mpr ⟨hrprime, hrU, Nat.card_pos.ne'⟩
  have hrU : r ∈ piSet U := by
    rwa [piSet, Set.mem_setOf_eq, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  exact hesc (centralizer_kappaCompl_le_of_mem_tau2 hG hM hKM hUM hU hKNU hrprime hr hrU)

/-- **Phase B/C step 1 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1300--1307,
the `sKLs`/`sLq` block): from the partner structure of the type-`P₂` maximal `M` (via
`typeP2_partner_structure_of_mem`), the `κ`-Hall `K` embeds into `M*_σ`, and `q := |K|` (prime)
lies in `σ(M*)`.

Proof (Coq `sKLs`, `sLq`): the partner structure gives `K = M*_σ ⊓ C(Ks)` (with
`Ks = M_σ ⊓ C(K)`), so `K ≤ M*_σ` (`inf_le_left`).  As `|K| = q` is prime and `q ∣ |M*_σ|`
(`K ≤ M*_σ`), and `M*_σ` is a `σ(M*)`-group (`Msigma_isPiGroup`), we get `q ∈ σ(M*)`. -/
theorem partner_kappaHall_le_Msigma_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G))) :
    K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar ∧
      ∀ q : ℕ, q.Prime → Nat.card ↥K = q → q ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
  obtain ⟨_hMstP, _hKsHall, hKeq, _⟩ :=
    typeP2_partner_structure_of_mem hG hM hP2 hKM hK hMstar
  -- `K = M*_σ ⊓ C(Ks) ≤ M*_σ`.
  have hKMσstar : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by rw [hKeq]; exact inf_le_left
  refine ⟨hKMσstar, fun q hqprime hKcard => ?_⟩
  -- `q ∣ |M*_σ|`, and `M*_σ` is a `σ(M*)`-group.
  have hqdvd : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    rw [← hKcard]; exact Subgroup.card_dvd_of_le hKMσstar
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q
    (Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd, Nat.card_pos.ne'⟩)

/-- **Phase B/C step 3 (nilpotent case) of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1317--1324, the `defLF` branch): for a maximal `M` with `q ∈ σ(M)` and `M_σ`
**nilpotent** (`M_F = M_σ`), the `q`-core `Q = O_q(M)` is a Sylow `q`-subgroup of `M` — there is
a `Sylow q ↥M` whose ambient image is `Q`.

Proof (Coq `Fcore_pcore_Sylow`): `Q ≤ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`), and
`Q = O_q(M_σ)` (`opiCoreInG_eq_of_normal_le`); in the nilpotent `M_σ`, `O_q(M_σ)` is a Hall
`{q}`-subgroup (`oPiCore_isHall_of_isNilpotent`), so `q ∤ [M_σ : Q]`.  Also `q ∤ [M : M_σ]` since
`M_σ` is a `σ(M)`-Hall (`Msigma_subgroupOf_isHall`) and `q ∈ σ(M)`.  The index tower
`[M : Q] = [M_σ : Q]·[M : M_σ]` then has no factor of `q`, and `exists_sylow_eq_opiCore` produces
the Sylow witness. -/
theorem exists_sylow_eq_opiCore_of_mem_sigma_of_msigma_nilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    ∃ P : Sylow q ↥M, opiCoreInG ({q} : Set ℕ) M = (P : Subgroup ↥M).map M.subtype := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) M with hQdef
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQMσ : Q ≤ Mσ := by
    rw [hQdef, hMσ]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton M
  -- `Q = O_q(M_σ)`, and in the nilpotent `M_σ` this is a Hall `{q}`-subgroup.
  have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) Mσ := by
    rw [hQdef, hMσ]
    exact opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hMσ ▸ hQMσ)
  have hQsub_eq : Q.subgroupOf Mσ = Ch03.oPiCore ({q} : Set ℕ) ↥Mσ := by
    rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
  haveI : Group.IsNilpotent ↥Mσ := hMσ ▸ hnil
  have hQMσHall : Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mσ) := by
    rw [hQsub_eq]
    exact OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent ({q} : Set ℕ)
  -- `q ∤ [M_σ : Q]` (Hall) and `q ∤ [M : M_σ]` (`σ`-Hall, `q ∈ σ`); combine via the index tower.
  have hqidxMσ : ¬ q ∣ (Q.subgroupOf Mσ).index := fun hd =>
    hQMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)
      (Set.mem_singleton q)
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) := by
    rw [hMσ]; exact OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  have hqidxMσM : ¬ q ∣ (Mσ.subgroupOf M).index := fun hd =>
    hMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  have hidx : ¬ q ∣ (Q.subgroupOf M).index := by
    -- `(Q.subgroupOf M).index = Q.relIndex M = (Q.relIndex Mσ) * (Mσ.relIndex M)`.
    have htower : Q.relIndex Mσ * Mσ.relIndex M = Q.relIndex M :=
      Subgroup.relIndex_mul_relIndex Q Mσ M hQMσ hMσM
    intro hd
    have hd' : q ∣ Q.relIndex Mσ * Mσ.relIndex M := htower ▸ hd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hd' with h1 | h2
    · exact hqidxMσ h1
    · exact hqidxMσM h2
  simpa only [hQdef] using
    exists_sylow_eq_opiCore (hQ := hQdef) hQM hMnormQ hQpg hidx

/-- **`sigma'2Elem_tau2`** (BG §12, Coq BGsection12.v:209; converse to
`exists_elemAb_rank_two_le_E_of_tau2`): a rank-2 elementary abelian `p`-subgroup `A ≤ E` inside a
`σ(M)'`-Hall `E`-setup forces `p ∈ τ₂(M)` (for `p` prime).

Proof (Coq): `A ≤ E` is a nontrivial `p`-group, so `p ∈ π(E)`; then `p ∈ τ₁(M) ∪ τ₂(M) ∪ τ₃(M)`
(`SubgroupESetup.mem_tau_union_of_mem_primeFactors`).  Since `A ∈ ℰ²_p(E)` and `A ≤ E ≤ M`,
`pRank ↥M p ≥ 2` (`le_pRank`), but `τ₁`/`τ₃` primes have `pRank = 1`; so `p ∈ τ₂(M)`.

This is the missing converse used in the `sLq1` step of `tau2_P2type_signalizer` (proving
`q₁ ∈ σ(M*)` by contradiction: were `q₁ ∉ σ(M*)`, `A` would be a `τ₂(M*)` witness). -/
theorem mem_tau2_of_elemAb_rank_two_le_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (hEsetup : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} (hpprime : p.Prime)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    p ∈ tau2 M := by
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  -- `p ∈ π(E)`: `p ∣ |A| = p² ∣ |E|`.
  have hpE : p ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hpprime, ?_, Nat.card_pos.ne'⟩
    refine (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans ?_
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hAE
  -- `p ∈ τ₁ ∪ τ₂ ∪ τ₃`; rule out `τ₁`/`τ₃` by `pRank ↥M p ≥ 2`.
  have hpτ : p ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
    hEsetup.mem_tau_union_of_mem_primeFactors hG hpE
  have hAM : A ≤ M := hAE.trans hEsetup.E_le
  have hpRank2 : 2 ≤ pRank ↥M p := by
    have hAsubEA : (A.subgroupOf M).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM).symm hAea
    have hle := le_pRank (A.subgroupOf M) hAsubEA
    have hcard : Nat.card ↥(A.subgroupOf M) = p ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hAcard
    rw [hcard, Nat.log_pow hpprime.one_lt] at hle
    exact hle
  rcases hpτ with (h1 | h2) | h3
  · exact absurd (tau1_pRank_eq_one h1) (by omega)
  · exact h2
  · exact absurd (tau3_pRank_eq_one h3) (by omega)

/-- **Phase B/C step 2 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1307--1316,
the `sLq1`/`sALs` block): with the partner `M*` type-`P`, `K ≤ M*_σ`, `q := |K| ∈ σ(M*)`, and a
rank-2 elementary abelian `A ∈ ℰ²_{q₁}(G)` (`q₁` prime) with `A ≤ C(K)` and `A ≤ M*`, one has
`q₁ ∈ σ(M*)` and `A ≤ M*_σ`.

Proof (Coq `sLq1`): by contradiction — if `q₁ ∉ σ(M*)`, then `A` is a `σ(M*)'`-group, so it lies in
a `σ(M*)'`-Hall `E`-setup (`exists_subgroupESetup_with_le`).  Then `q₁ ∈ τ₂(M*)`
(`mem_tau2_of_elemAb_rank_two_le_E`), so `C_G(A) ≤ E` (Cor 12.6(b), `centralizer_le_E_of_tau2`).
But `K ≤ C_G(A)` (`A ≤ C(K)` symmetrised), so `K ≤ E`, a `σ(M*)'`-group; yet `q = |K| ∈ σ(M*)`
divides `|K|` — contradiction.  Then `A ⊆ M*_σ` (`sALs`): `A` is a `σ(M*)`-group (`q₁ ∈ σ(M*)`) in
`M*`, absorbed by the normal `σ(M*)`-Hall `M*_σ` (`isPiGroup_le_of_normal_isHallSubgroup`). -/
theorem mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Mstar K A : Subgroup G} {q q1 : ℕ}
    (hMstar : Mstar ∈ maximalSubgroups G) (hqprime : q.Prime) (hKcard : Nat.card ↥K = q)
    (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar)
    (hq1prime : q1.Prime) (hA : A ∈ elemAbelianOfRank G q1 2)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) (hAMstar : A ≤ Mstar) :
    q1 ∈ OddOrder.BG.Ch3.S10.sigma Mstar ∧ A ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
  classical
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  -- `K ≤ C_G(A)` (symmetrise `A ≤ C_G(K)`).
  have hKCA : K ≤ Subgroup.centralizer (A : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hACK ha) k hk).symm
  -- `q₁ ∈ σ(M*)`, by contradiction.
  have hq1σ : q1 ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
    by_contra hq1nσ
    -- `A` is a `σ(M*)'`-subgroup (a `q₁`-group with `q₁ ∉ σ(M*)`).
    have hApi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ) A := by
      intro p hp
      have hpq1 : p = q1 := by
        have hpd : p ∈ (q1 ^ 2).primeFactors := hAcard ▸ hp
        rw [Nat.primeFactors_prime_pow (by norm_num) hq1prime, Finset.mem_singleton] at hpd
        exact hpd
      exact hpq1 ▸ hq1nσ
    -- a `σ(M*)'`-Hall `E`-setup with `A ≤ E`.
    obtain ⟨E, E₁, E₂, E₃, hEsetup, hAE, _hEpi⟩ :=
      exists_subgroupESetup_with_le hG hMstar hAMstar hApi
    -- `q₁ ∈ τ₂(M*)`, so `C_G(A) ≤ E`.
    have hq1τ2 : q1 ∈ tau2 Mstar := mem_tau2_of_elemAb_rank_two_le_E hG hEsetup hq1prime hA hAE
    have hCAE : Subgroup.centralizer (A : Set G) ≤ E :=
      (centralizer_le_E_of_tau2 hG hEsetup hq1τ2 hA hAE).1
    -- `K ≤ C_G(A) ≤ E`, so `q ∣ |K|` lies in `π(E) ⊆ σ(M*)'` — contradicting `q ∈ σ(M*)`.
    have hKE : K ≤ E := hKCA.trans hCAE
    have hqπE : q ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, (hKcard ▸ Subgroup.card_dvd_of_le hKE), Nat.card_pos.ne'⟩
    exact hEsetup.not_mem_sigma_of_mem_primeFactors hG hqπE hqσ
  refine ⟨hq1σ, ?_⟩
  -- `A ⊆ M*_σ`: `A` a `σ(M*)`-group in `M*`, absorbed by the normal `σ(M*)`-Hall `M*_σ`.
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)
      ((OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hMstar
  have hApiσ : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma Mstar) (A.subgroupOf Mstar) := by
    intro p hp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMstar).toEquiv, hAcard,
      Nat.primeFactors_prime_pow (by norm_num) hq1prime, Finset.mem_singleton] at hp
    exact hp ▸ hq1σ
  haveI : ((OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hAsubMσ : A.subgroupOf Mstar ≤ (OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hMσHall hApiσ
  have hmap := Subgroup.map_mono (f := Mstar.subtype) hAsubMσ
  rwa [Subgroup.map_subgroupOf_eq_of_le hAMstar,
    Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le Mstar)] at hmap

/-- **Phase B/C step 4 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1358--1367,
the `not_cQQ` block): with the partner `L` type-`P₁` (so `L_σ` nilpotent, `L' = L_σ`), `q ∈ σ(L)`,
the `q`-core `Q = O_q(L)` a Sylow `q`-subgroup of `L` (Step 3), and the `κ`-Hall `K` with `|K| = q`
prime, `K ≤ Q` and `K ≤ (L_σ)'`, the Sylow `Q` is **nonabelian**.

Proof (Coq `not_cQQ`, working inside `↥(L_σ)`): the nilpotent `L_σ` factors as
`L_σ = O_{q'}(L_σ)·Q` (`oPiCore_sup_compl_eq_top`, since `Q.subgroupOf L_σ = O_q(↥L_σ)`).  BG Lemma
6.5(a) (`inf_commutator_eq_of_coprime`) with the normal `q'`-part `O_{q'}(↥L_σ)`, `U = Q`, `H = K`
gives `K ⊓ (L_σ)' = K ⊓ ⁅Q, Q⁆`.  If `Q` were abelian, `⁅Q, Q⁆ = ⊥`, so `K ⊓ (L_σ)' = ⊥`; but
`K ≤ (L_σ)'` gives `K ⊓ (L_σ)' = K`, forcing `K = ⊥`, contradicting `|K| = q > 1`. -/
theorem partner_opiCore_nonabelian [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (_hL : L ∈ maximalSubgroups G) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L))
    (hKcard : Nat.card ↥K = q)
    (hKQ : K ≤ opiCoreInG ({q} : Set ℕ) L)
    (hKderiv : K ≤ derivedInG (OddOrder.BG.Ch3.S10.Msigma L)) :
    ¬ IsMulCommutative ↥(opiCoreInG ({q} : Set ℕ) L) := by
  classical
  intro hQab
  set Ls : Subgroup G := OddOrder.BG.Ch3.S10.Msigma L with hLsdef
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσM : Ls ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hMnormMσ : L ≤ Subgroup.normalizer (Ls : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  -- `Q ≤ L_σ` and `Q = O_q(L_σ)`.
  have hQMσ : Q ≤ Ls := by
    rw [hQdef, hLsdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) Ls := by
    rw [hQdef, hLsdef]
    exact opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hLsdef ▸ hQMσ)
  haveI : Group.IsNilpotent ↥Ls := hLsdef ▸ hnil
  -- Inside `↥(L_σ)`: `Q̄ = O_q(↥L_σ)`, `Ō = O_{q'}(↥L_σ)`, with `Ō ⊔ Q̄ = ⊤`.
  have hQsub_eq : Q.subgroupOf Ls = Ch03.oPiCore ({q} : Set ℕ) ↥Ls := by
    rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
  have hKMσ : K ≤ Ls := hKQ.trans hQMσ
  set Qbar : Subgroup ↥Ls := Q.subgroupOf Ls with hQbardef
  set Obar : Subgroup ↥Ls := Ch03.oPiCore ({q}ᶜ : Set ℕ) ↥Ls with hObardef
  set Kbar : Subgroup ↥Ls := K.subgroupOf Ls with hKbardef
  haveI hObarN : Obar.Normal := hObardef ▸ Ch03.oPiCore.normal _ _
  have hsup : Obar ⊔ Qbar = ⊤ := by
    have h := oPiCore_sup_compl_eq_top (K := ↥Ls) ({q}ᶜ : Set ℕ)
    rw [compl_compl] at h
    rw [hObardef, hQsub_eq]; exact h
  -- `K̄ = K.subgroupOf L_σ ≤ Q̄`; coprime `(|K̄|, |Ō|)` (`q`-group vs `q'`-group).
  have hKbarQ : Kbar ≤ Qbar := Subgroup.subgroupOf_mono Ls hKQ
  have hKbarcard : Nat.card ↥Kbar = q := by
    rw [hKbardef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKMσ).toEquiv]; exact hKcard
  have hObarpi : Ch03.Subgroup.IsPiGroup ({q}ᶜ : Set ℕ) Obar :=
    hObardef ▸ Ch03.oPiCore.isPiGroup ({q}ᶜ : Set ℕ)
  have hcop : Nat.Coprime (Nat.card ↥Kbar) (Nat.card ↥Obar) := by
    refine coprime_of_forall_prime_not_dvd (fun r hr hrK hrO => ?_)
    have hrq : r = q := by
      have hmem : r ∈ (q : ℕ).primeFactors := by
        rw [hKbarcard] at hrK
        exact Nat.mem_primeFactors.mpr ⟨hr, hrK, (Fact.out : q.Prime).ne_zero⟩
      rw [(Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hmem; exact hmem
    have hrOmem : r ∈ ({q}ᶜ : Set ℕ) :=
      hObarpi r (Nat.mem_primeFactors.mpr ⟨hr, hrO, Nat.card_pos.ne'⟩)
    exact hrOmem (by rw [hrq]; rfl)
  -- BG Lemma 6.5(a): `K̄ ⊓ commutator ↥L_σ = K̄ ⊓ ⁅Q̄, Q̄⁆`.
  have hfocal := OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime (K := Obar) (U := Qbar)
    (H := Kbar) hsup hKbarQ hcop
  -- `Q` abelian ⟹ `Q̄` abelian ⟹ `⁅Q̄, Q̄⁆ = ⊥`, so RHS `= ⊥`.
  have hQbarab : IsMulCommutative ↥Qbar :=
    OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hQMσ).symm hQab
  have hQQbot : ⁅Qbar, Qbar⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx; rw [Subgroup.mem_centralizer_iff]; intro y hy
    exact congrArg Subtype.val (hQbarab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  -- `K̄ ≤ commutator ↥L_σ` (from `K ≤ (L_σ)'`).
  have hKbarComm : Kbar ≤ commutator ↥Ls := by
    have hid : (derivedInG Ls).subgroupOf Ls = commutator ↥Ls :=
      Subgroup.comap_map_eq_self_of_injective Ls.subtype_injective (commutator ↥Ls)
    rw [hKbardef, ← hid]
    exact Subgroup.subgroupOf_mono Ls (hLsdef ▸ hKderiv)
  -- `K̄ = K̄ ⊓ commutator = K̄ ⊓ ⁅Q̄,Q̄⁆ = K̄ ⊓ ⊥ = ⊥`, contradicting `|K̄| = q > 1`.
  have hKbot : Kbar = ⊥ := by
    have h1 : Kbar ⊓ commutator ↥Ls = Kbar := inf_eq_left.mpr hKbarComm
    rw [hfocal, hQQbot, inf_bot_eq] at h1
    exact h1.symm
  rw [hKbot, Subgroup.card_bot] at hKbarcard
  exact (Fact.out : q.Prime).one_lt.ne' hKbarcard.symm

end OddOrder.BG.Ch4.S15
