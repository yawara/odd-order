import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.Corollary155

/-!
# BG Theorems 15.7-15.9 — TI failure and final local constraints

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF` (directory split, issue 0103).
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


/-! ## Theorems 15.7--15.9: TI failure and final local constraints -/

/-- **BG Theorem 15.2(b), contrapositive form** (mmd L4185): if no prime divides `M_F` and lies
in `β(M)`, then `M_F = M_σ`.  Theorem 15.2 shows that whenever `M_F ≠ M_σ`, the prime `q = |K*|`
satisfies `q ∈ π(M_F) ∩ β(M)`; the contrapositive gives the claim.  A Hall `κ(M)`-subgroup `K`
needed to invoke 15.2 exists by solvability of `M` (Hall's theorem).

This is the `M_F = M_σ` endgame of Theorem 15.7(a): once the rank-theoretic core
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` establishes `π(M_F) ∩ β(M) = ∅`, this lemma
delivers `M_F = M_σ` (equivalently, `M_σ` nilpotent). -/
theorem mf_eq_msigma_of_piSet_inf_beta_disjoint [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hdisj : ∀ q : ℕ, q ∈ S14.piSet (MF M) → q ∉ OddOrder.BG.Ch3.S10.beta M) :
    MF M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  by_contra hne
  -- A Hall `κ(M)`-subgroup `K` of `M` exists by Hall's theorem in the solvable group `↥M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  -- Theorem 15.2(b): for `M_F ≠ M_σ`, the prime `q = |K*|` lies in `π(M_F) ∩ β(M)`.
  obtain ⟨_, _, _, _, _, _, _, _, _, hqπ, hqβ, _⟩ :=
    (mf_ne_msigma_typeP1_structure hG hM hne hKM hK rfl).2
  exact hdisj _ hqπ hqβ

/-- **BG Corollary 15.5(a)**: `O_{σ(M)'}(F(M))` is cyclic.  Extracted from `fitting_decomposition`,
whose cyclic witness `Y` (a `τ₂(M) ⊆ σ(M)ᶜ`-group, normal in the nilpotent `F(M)` and complementing
`O_{σ(M)}(F(M)) = F(M_σ)`) equals `O_{σ(M)'}(F(M))` by modularity. -/
theorem opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    IsCyclic ↥(opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)ᶜ (fittingInAmbient M)) := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set F := fittingInAmbient M with hFdef
  obtain ⟨Y, hYcyc, hYtau2, hYleF, _, _, hF_eq, _hFmσ_Y_bot, hcomm, _, _, _⟩ :=
    fitting_decomposition hG hM
  -- `O_σ(F) = F(M_σ)`, so `F = O_σ(F) ⊔ Y`.
  have hOσ : opiCoreInG σ F = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  have hF_eq2 : F = opiCoreInG σ F ⊔ Y := by rw [hOσ]; exact hF_eq
  -- `Y ⊴ F`: normalized by `Y` and by `F(M_σ)` (which centralizes it), and `F = F(M_σ) ⊔ Y`.
  have hYnorm : (Y.subgroupOf F).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hYleF).mpr ?_
    rw [hF_eq]
    refine sup_le ?_ Subgroup.le_normalizer
    have h1 : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  -- `Y` is a `σᶜ`-group (`π(Y) ⊆ τ₂(M) ⊆ σᶜ`).
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := fun r hr => tau2_subset_sigma_compl M (hYtau2 hr)
  have hYle : Y ≤ opiCoreInG σᶜ F := le_opiCoreInG_of_normal_of_isPiSubgroup hYleF hYnorm hYpi
  have hinf : opiCoreInG σ F ⊓ opiCoreInG σᶜ F = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  -- `O_σ(F) = F(M_σ)` centralizes `Y`, so it normalizes `Y`.
  have hEnorm : opiCoreInG σ F ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hOσ]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `O_{σᶜ}(F) = Y` by the normality-aware Dedekind law, hence cyclic.
  have hDF : opiCoreInG σᶜ F ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  have hDY : opiCoreInG σᶜ F = Y := by
    have hkey := Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
      (W := Y) (A := opiCoreInG σ F) (L := opiCoreInG σᶜ F) hYle hinf hEnorm
    rw [← hkey, sup_comm, ← hF_eq2, inf_eq_right.mpr hDF]
  rw [hDY]; exact hYcyc

/-- **BG Corollary 15.5(a), `τ₂`-membership form**: the `σ'`-part `O_{σ(M)'}(F(M))` of the Fitting
subgroup is a `τ₂(M)`-group.  Companion to `opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic`,
extracted from `fitting_decomposition`'s cyclic witness `Y` (which equals `O_{σ'}(F(M))` by the
modular argument). -/
theorem opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ↑(Nat.card ↥(opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)ᶜ (fittingInAmbient M))).primeFactors ⊆
      tau2 M := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set F := fittingInAmbient M with hFdef
  obtain ⟨Y, _hYcyc, hYtau2, hYleF, _, _, hF_eq, _, hcomm, _, _, _⟩ := fitting_decomposition hG hM
  have hOσ : opiCoreInG σ F = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  have hF_eq2 : F = opiCoreInG σ F ⊔ Y := by rw [hOσ]; exact hF_eq
  have hYnorm : (Y.subgroupOf F).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hYleF).mpr ?_
    rw [hF_eq]
    refine sup_le ?_ Subgroup.le_normalizer
    have h1 : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := fun r hr => tau2_subset_sigma_compl M (hYtau2 hr)
  have hYle : Y ≤ opiCoreInG σᶜ F := le_opiCoreInG_of_normal_of_isPiSubgroup hYleF hYnorm hYpi
  have hinf : opiCoreInG σ F ⊓ opiCoreInG σᶜ F = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  have hEnorm : opiCoreInG σ F ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hOσ]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDF : opiCoreInG σᶜ F ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  have hDY : opiCoreInG σᶜ F = Y := by
    have hkey := Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
      (W := Y) (A := opiCoreInG σ F) (L := opiCoreInG σᶜ F) hYle hinf hEnorm
    rw [← hkey, sup_comm, ← hF_eq2, inf_eq_right.mpr hDF]
  rw [hDY]; exact hYtau2

/-- **BG Theorem 15.7(d), the `τ₃(M) = ∅` prime-set core**: if `M' ≤ F(M)` then `τ₃(M) = ∅`.

`F(M) = F(M_σ) × O_{σ'}(F(M))` (`fitting_decomposition`, an internal direct product) with `F(M_σ)`
a `σ(M)`-group (`= O_σ(F(M))`) and `O_{σ'}(F(M))` a `τ₂(M)`-group, so every prime of `M' ≤ F(M)` is
in `σ(M) ∪ τ₂(M)`.  A `τ₃(M)`-prime is `∉ σ(M)` (hence `∈ τ₂(M)`, `r_p = 2`) yet lies in `π(M')`
with `r_p = 1` — contradiction.

This is the `defE`/`E3_1` prime-set half of Corollary 15.9's cyclic Frobenius complement (Coq
`nonTI_Fitting_structure` part (d)): once `τ₃(M) = ∅` the `τ₃`-Hall `E₃` of any `σ(M)'`-complement is
trivial (`E3_eq_bot_of_tau3_eq_empty`), so `E = E₁E₂` and — with `τ₂(M) = ∅` (Theorem 15.8) — `E = E₁`
is cyclic.  The remaining upstream gate is the `¬FittingIsTI`-specific `M' ≤ F(M)` (`M'` nilpotency;
issue 2037). -/
theorem tau3_eq_empty_of_derivedInG_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hM'F : derivedInG M ≤ fittingInAmbient M) : tau3 M = ∅ := by
  classical
  obtain ⟨Y, -, hYtau2, -, -, -, hF6, hF7, hF8, -, -, -⟩ := fitting_decomposition hG hM
  set Fσ : Subgroup G := fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) with hFσdef
  -- `F(M) = F(M_σ) × Y` ⟹ `|F(M)| = |F(M_σ)| · |Y|`.
  have hFσnormY : Fσ ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF8).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ↥(fittingInAmbient M) = Nat.card ↥Fσ * Nat.card ↥Y := by
    rw [hF6]; exact card_sup_eq_mul_of_le_normalizer_of_disjoint hFσnormY hF7
  -- `π(F(M_σ)) ⊆ σ(M)` (`F(M_σ) = O_σ(F(M))`, a `σ`-core).
  have hFσσ : ∀ p ∈ (Nat.card ↥Fσ).primeFactors, p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    rw [hFσdef, ← opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma] at hp
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)
      (fittingInAmbient M) p hp
  -- No `τ₃`-prime survives.
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_tau3_iff]
  rintro ⟨hpσ, hpM', hp1⟩
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpM'
  have hpF : p ∈ (Nat.card ↥(fittingInAmbient M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime,
      (Nat.dvd_of_mem_primeFactors hpM').trans (Subgroup.card_dvd_of_le hM'F), Nat.card_pos.ne'⟩
  rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne', Finset.mem_union] at hpF
  rcases hpF with h | h
  · exact hpσ (hFσσ p h)
  · have hp2 : pRank ↥M p = 2 := ((mem_tau2_iff M p).mp (hYtau2 (Finset.mem_coe.mpr h))).2
    omega

/-- **`E₃ = ⊥` from `τ₃(M) = ∅`**: the `τ₃(M)`-Hall factor `E₃` of any `σ(M)'`-complement `E`-setup
is trivial when `M` has no `τ₃`-primes.  A `{τ₃}`-Hall subgroup of the empty prime set has order
coprime to every prime, hence order `1`.  Companion to
`tau3_eq_empty_of_derivedInG_le_fittingInAmbient` (BG Theorem 15.7(d), `E3_1`). -/
theorem E3_eq_bot_of_tau3_eq_empty [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃) (htau3 : tau3 M = ∅) :
    E₃ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpsub : p ∈ (Nat.card ↥(E₃.subgroupOf E)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₃_le).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
  have hmem : p ∈ tau3 M := hsetup.E₃_hall.1 p hpsub
  rw [htau3] at hmem
  exact hmem

/-- **`E₂ = ⊥` from `τ₂(M) = ∅`**: the `τ₂(M)`-Hall factor `E₂` of any `σ(M)'`-complement `E`-setup is
trivial when `M` has no `τ₂`-*primes* (Theorem 15.8's `τ₂(M) = ∅` for the Corollary 15.9 escape, in
the `∀ p, p.Prime → p ∉ τ₂(M)` form output by `tau2_transfer_constraint`).  `τ₂`-analogue of
`E3_eq_bot_of_tau3_eq_empty`. -/
theorem E2_eq_bot_of_tau2_eq_empty [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (htau2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M) :
    E₂ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpsub : p ∈ (Nat.card ↥(E₂.subgroupOf E)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₂_le).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
  exact htau2 p hp (hsetup.E₂_hall.1 p hpsub)

/-- **Type-`P₂` `M_F`-internal Fitting decomposition** (BG Corollary 15.5; the `M' = M_F × U`
form feeding Proposition 16.1's forward bridges).  For a type-`P₂` maximal subgroup `M` with
`κ`-Hall `K` and `(κ ∪ σ)'`-Hall `U`, the derived subgroup `M'` is the internal direct product of
the Fitting kernel `M_F` and `U` (the complement `hDcompl`), the Fitting subgroup is
`F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hFiteq`), and `M'' ≤ F(M)` (`hSDfit`).

This discharges the three genuinely-deep `M_F`-internal residuals (`hDcompl`/`hSDfit`/`hFiteq`)
of `typePData_of_isTypeP_of_inputs`, the shared linchpin of the `hP2II`/`hP1neIIIIV`/`hP1eqV`
forward bridges of `proposition_type_classification`.

Proof: `M_F = M_σ` (`M_σ` nilpotent for type `P₂`) and `M' = U ⊔ M_σ` with `U ⊓ M_σ = ⊥`
(Lemma 15.1(b)) give the complement.  The Fitting identity routes through `Y := O_{σ'}(F(M))`,
the `τ₂`-part of `F(M)` (Corollary 15.5(a)): `Y` is a `(κ ∪ σ)'`-group normal in `M`
(`π(Y) ⊆ τ₂`, and `τ₂ ∩ κ = ∅` by rank), hence `Y ≤ U`, and `Y` centralizes `M_σ = M_F`, so
`F(M) = M_F ⊔ Y ≤ M_F ⊔ (U ⊓ C_M(M_F)) ≤ F(M)`. -/
theorem typeP2_mf_internal_fitting_decomposition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
        (U.subgroupOf (derivedInG M)) ∧
      secondDerivedInAmbient M ≤ maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) ∧
      (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype = maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  set F := fittingInAmbient M with hFdef
  haveI hFnil : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  -- `M_F = M_σ`: `M_σ` is nilpotent for type `P₂`.
  haveI hMσnil : Group.IsNilpotent ↥Mσ := S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2
  have hMFMσ : maxNilpotentNormalHall M = Mσ :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hMσnil
  -- Lemma 15.1(b): `M' = U ⊔ M_σ`.
  obtain ⟨hM'eq, _hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU
  have hMσ_le_M' : Mσ ≤ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hMσ_le_M : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hU_le_M' : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  -- `U ⊓ M_σ = ⊥` (coprime Hall orders).
  have hUMσ_bot : U ⊓ Mσ = ⊥ := by
    have hMσHall : Ch03.IsHallSubgroup σ (Mσ.subgroupOf M) :=
      OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
    have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
        (π := (S14.kappa M ∪ σ)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
      · intro p hp
        exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      · intro p hp hpcompl
        have hpMσ : p ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσ_le_M).toEquiv]
        exact hpcompl (Or.inr (hMσHall.1 p hpMσ))
    exact Subgroup.inf_eq_bot_of_coprime hcop
  -- `Y := O_{σ'}(F(M))`, the `τ₂`-part of `F(M)`.
  set Y := opiCoreInG σᶜ F with hYdef
  have hY_le_M : Y ≤ M :=
    (OddOrder.GroupTheory.opiCoreInG_le σᶜ F).trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hOσMσ : opiCoreInG σ F = Mσ := by
    rw [opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma, ← hMσdef,
      fittingInAmbient_eq_self_of_isNilpotent]
  -- `Y` centralizes `M_σ`.
  have hY_le_cent : Y ≤ Subgroup.centralizer (Mσ : Set G) := by
    have hcomm : ⁅opiCoreInG σ F, Y⁆ = ⊥ := by
      rw [hYdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot σ F
    rw [hOσMσ, Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  -- `Y ≤ U`: `Y` is a `(κ∪σ)'`-group normal in `M`, and `U` is the `(κ∪σ)'`-Hall.
  have hY_le_U : Y ≤ U := by
    have hY_pi : Ch03.Subgroup.IsPiGroup ((S14.kappa M ∪ σ)ᶜ) (Y.subgroupOf M) := by
      intro p hp
      have hpY : p ∈ (Nat.card ↥Y).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_le_M).toEquiv] at hp
      have hpσ : p ∈ σᶜ := OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F p hpY
      have hpτ2 : p ∈ tau2 M :=
        opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2 hG hM hpY
      rw [Set.mem_compl_iff, Set.mem_union]
      rintro (hpκ | hpσ')
      · have hr1 : pRank ↥M p = 1 := by
          rcases S14.kappa_subset_tau1_union_tau3 hpκ with h | h
          · exact ((mem_tau1_iff M p).mp h).2.2
          · exact ((mem_tau3_iff M p).mp h).2.2
        have hr2 : pRank ↥M p = 2 := ((mem_tau2_iff M p).mp hpτ2).2
        rw [hr1] at hr2; exact absurd hr2 (by norm_num)
      · exact hpσ hpσ'
    haveI hYnorm_M : (Y.subgroupOf M).Normal := by
      rw [hYdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M
    have hsub_le : Y.subgroupOf M ≤ U.subgroupOf M :=
      Ch03.Subgroup.IsPiGroup.normal_le_hall hY_pi hU
    have hmap := Subgroup.map_mono (f := M.subtype) hsub_le
    rwa [Subgroup.map_subgroupOf_eq_of_le hY_le_M, Subgroup.map_subgroupOf_eq_of_le hUM] at hmap
  -- `F(M) = M_F ⊔ Y`.
  have hF_split : F = maxNilpotentNormalHall M ⊔ Y := by
    have hsplit : opiCoreInG σ F ⊔ Y = F := by
      rw [hYdef]; exact opiCoreInG_sup_compl_eq_of_isNilpotent σ
    rw [← hsplit, hOσMσ, hMFMσ]
  -- `M_F ≤ F(M)`.
  have hMF_le_F : maxNilpotentNormalHall M ≤ F := by
    haveI : Group.IsNilpotent ↥(maxNilpotentNormalHall M) := maxNilpotentNormalHall_isNilpotent M
    exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent
      (maxNilpotentNormalHall_le M) (maxNilpotentNormalHall_subgroupOf_normal M)
  -- `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.
  have hFiteq : F = maxNilpotentNormalHall M ⊔
      (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    apply le_antisymm
    · rw [hF_split]
      refine sup_le_sup_left (le_inf hY_le_U ?_) _
      rw [hMFMσ]; exact hY_le_cent
    · refine sup_le hMF_le_F ?_
      have hFcent : F = (Subgroup.centralizer (maxNilpotentNormalHall M : Set G) ⊓ M) ⊔
          maxNilpotentNormalHall M := by
        obtain ⟨-, -, -, -, -, h, -, -, -, -, -, -⟩ := fitting_decomposition hG hM
        exact h
      rw [hFcent]
      exact (le_inf inf_le_right (inf_le_left.trans hUM)).trans le_sup_left
  refine ⟨?_, ?_, hFiteq⟩
  · -- `hDcompl`: `M_F = M_σ` complements `U` in `M'`.
    rw [hMFMσ]
    haveI hMσnorm' : ((Mσ).subgroupOf (derivedInG M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMσ_le_M').mpr
        (hM'_le_M.trans (OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M))
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxMσ hxU
      rw [Subgroup.mem_subgroupOf] at hxMσ hxU
      have hx : (x : G) ∈ U ⊓ Mσ := ⟨hxU, hxMσ⟩
      rw [hUMσ_bot, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσ_le_M' hU_le_M',
        sup_comm, ← hM'eq, Subgroup.subgroupOf_self, Subgroup.coe_top]
  · -- `hSDfit`: `M'' ≤ F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.
    have hM''F : secondDerivedInAmbient M ≤ F := by
      obtain ⟨-, -, -, -, h, -, -, -, -, -, -, -⟩ := fitting_decomposition hG hM
      exact h
    exact hM''F.trans (le_of_eq hFiteq)

/-- In a finite cyclic group, a subgroup is determined by its cardinality (every subgroup is the
kernel of `x ↦ x ^ |A|`, which depends only on `|A|`). -/
theorem eq_of_card_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H K : Subgroup C} (h : Nat.card ↥H = Nat.card ↥K) : H = K := by
  letI : CommGroup C := IsCyclic.commGroup
  have key : ∀ A : Subgroup C, A = (powMonoidHom (Nat.card ↥A) : C →* C).ker := by
    intro A
    have hcard : Nat.card ↥((powMonoidHom (Nat.card ↥A) : C →* C).ker) = Nat.card ↥A := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card A)]
    refine Subgroup.eq_of_le_of_card_ge (fun a ha => ?_) (le_of_eq hcard)
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have h1 : (⟨a, ha⟩ : ↥A) ^ Nat.card ↥A = 1 := pow_card_eq_one'
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val h1
  rw [key H, key K, h]

/-- Two subgroups of `G` of equal finite order, both contained in a cyclic subgroup `C`, are
equal. -/
theorem eq_of_le_isCyclic_of_card_eq [Finite G] {C H K : Subgroup G} [IsCyclic ↥C]
    (hHC : H ≤ C) (hKC : K ≤ C) (h : Nat.card ↥H = Nat.card ↥K) : H = K := by
  have hcardH : Nat.card ↥(H.subgroupOf C) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
  have hcardK : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  have hsub : H.subgroupOf C = K.subgroupOf C :=
    eq_of_card_eq_of_isCyclic (by rw [hcardH, hcardK, h])
  rw [← Subgroup.map_subgroupOf_eq_of_le hHC, ← Subgroup.map_subgroupOf_eq_of_le hKC, hsub]

/-- If `K` normalizes a cyclic subgroup `C` and `X ≤ C` is finite, then `K` normalizes `X`:
subgroups of a cyclic group are determined by their order, so the order-preserving `C`-conjugation
by elements of `K` fixes `X`. -/
theorem le_normalizer_of_le_isCyclic_normalized [Finite G] {C X K : Subgroup G} [IsCyclic ↥C]
    (hXC : X ≤ C) (hKC : K ≤ Subgroup.normalizer (C : Set G)) :
    K ≤ Subgroup.normalizer (X : Set G) := by
  intro m hm
  -- `m` conjugates `C` to itself.
  have hmC : MulAut.conj m • C = C := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show ((MulAut.conj m)⁻¹ • x : G) = m⁻¹ * x * m by
        simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    exact ((Subgroup.mem_normalizer_iff''.mp (hKC hm)) x).symm
  -- `conj m • X ≤ C` and has the same order, so equals `X`.
  have hconjle : MulAut.conj m • X ≤ C :=
    hmC ▸ (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXC)
  have hcard : Nat.card ↥(MulAut.conj m • X) = Nat.card ↥X :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj m) X).toEquiv).symm
  have hXeq : MulAut.conj m • X = X := eq_of_le_isCyclic_of_card_eq hconjle hXC hcard
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  have hiff : h ∈ MulAut.conj m • X ↔ m⁻¹ * h * m ∈ X := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show ((MulAut.conj m)⁻¹ • h : G) = m⁻¹ * h * m by
        simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
  rwa [hXeq] at hiff

/-- **Setup for BG Theorem 15.7(a)**: `¬FittingIsTI M` produces an element `g ∉ M` and a nontrivial
intersection `F(M) ⊓ F(M)^g`.  Unfolding `¬IsTISubset (F(M)^#) (N_G(F(M)))`: there is `g ∉ N_G(F(M))`
and `a ∈ F(M)^#` with `gag⁻¹ ∈ F(M)^#`; then `gag⁻¹ ∈ F(M) ⊓ (conj g • F(M))` is nontrivial, and
`g ∉ M` because `F(M) ⊴ M` forces `M ≤ N_G(F(M))`. -/
theorem exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI {M : Subgroup G}
    (hnotTI : ¬ FittingIsTI M) :
    ∃ g : G, g ∉ M ∧
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) ≠ ⊥ := by
  rw [FittingIsTI] at hnotTI
  simp only [OddOrder.GroupTheory.IsTISubset] at hnotTI
  push Not at hnotTI
  obtain ⟨g, ⟨a, haA, hgaA⟩, hgN⟩ := hnotTI
  simp only [fittingSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at haA hgaA
  obtain ⟨haF, _ha1⟩ := haA
  obtain ⟨hgaF, hga1⟩ := hgaA
  -- `g ∉ M`: `F(M) ⊴ M` ⟹ `M ≤ N_G(F(M))`, but `g ∉ N_G(F(M))`.
  have hMN : M ≤ Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
      (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)
  refine ⟨g, fun h => hgN (hMN h), ?_⟩
  -- `gag⁻¹` is a nontrivial element of `F(M) ⊓ conj g • F(M)`.
  intro hbot
  have hmem : g * a * g⁻¹ ∈
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) := by
    refine Subgroup.mem_inf.mpr ⟨hgaF, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using haF
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hga1 hmem

/-- **Step 3 of BG Theorem 15.7(a)**: a prime `p` dividing the TI-failure intersection
`F(M) ⊓ F(M)^g` (with `g ∉ M`) lies in `σ(M)`.

If not, `O_{σ(M)'}(F(M))` is cyclic (`opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic`), so any
order-`p` subgroup `X₁ ≤ F(M) ⊓ F(M)^g` (it is a `p`-subgroup of `F(M)`, hence
`≤ O_p(F(M)) ≤ O_{σ'}(F(M))`) is the unique one, hence normalized by both `M` and `M^g` (each
normalizes the relevant cyclic `O_{σ'}` and `X₁ = (X₁)` is order-preserved).  Then
`normalizer_eq_of_normal_of_mem_maximal` gives `N_G(X₁) = M`, but also `M = N_G(g⁻¹·X₁·g) = g⁻¹·M·g`,
forcing `g ∈ M` — contradiction. -/
theorem mem_sigma_of_prime_dvd_card_inf_conj_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {g : G} (hgM : g ∉ M) {p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M)) :
    p ∈ OddOrder.BG.Ch3.S10.sigma M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hpσ
  set F := fittingInAmbient M with hFdef
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  have hFleM : F ≤ M := OddOrder.BG.Ch2.S08.fittingInG_le M
  -- `O_{σᶜ}(F)` is cyclic and normalized by `M`.
  haveI hcyc : IsCyclic ↥(opiCoreInG σᶜ F) := opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic hG hM
  have hMNOσc : M ≤ Subgroup.normalizer ((opiCoreInG σᶜ F : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((OddOrder.GroupTheory.opiCoreInG_le σᶜ F).trans hFleM)).mp
      (OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M)
  have hpσc : ({p} : Set ℕ) ⊆ σᶜ := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  -- Generic helper: a `p`-subgroup of `F` is normalized by `M` (via `X₁ ≤ O_{σᶜ}(F)` cyclic).
  have hpnorm : ∀ Z : Subgroup G, Z ≤ F → IsPGroup p ↥Z →
      M ≤ Subgroup.normalizer (Z : Set G) := by
    intro Z hZF hZp
    have hZOp : Z ≤ opiCoreInG ({p} : Set ℕ) F :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hZF hZp
    have hZOσc : Z ≤ opiCoreInG σᶜ F :=
      hZOp.trans (Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσc _))
    exact le_normalizer_of_le_isCyclic_normalized hZOσc hMNOσc
  -- An order-`p` subgroup `X₁` of `X = F ⊓ F^g`.
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(F ⊓ MulAut.conj g • F)) p hpdvd
  set X₁ : Subgroup G := (Subgroup.zpowers x).map (F ⊓ MulAut.conj g • F).subtype with hX₁def
  have hX₁leX : X₁ ≤ F ⊓ MulAut.conj g • F := hX₁def ▸ Subgroup.map_subtype_le _
  have hX₁card : Nat.card ↥X₁ = p := by
    rw [hX₁def, Subgroup.card_map_of_injective (F ⊓ MulAut.conj g • F).subtype_injective,
      Nat.card_zpowers, hxord]
  have hX₁ne : X₁ ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hX₁card; exact hp.one_lt.ne' hX₁card.symm
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁F : X₁ ≤ F := hX₁leX.trans inf_le_left
  have hX₁cF : X₁ ≤ MulAut.conj g • F := hX₁leX.trans inf_le_right
  -- `X₁ ⊴ M`, so `N_G(X₁) = M`.
  have hMNX₁ : M ≤ Subgroup.normalizer (X₁ : Set G) := hpnorm X₁ hX₁F hX₁pg
  have hNX₁ : Subgroup.normalizer (X₁ : Set G) = M :=
    OddOrder.BG.Ch2.S08.normalizer_eq_of_normal_of_mem_maximal hG hM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hX₁F.trans hFleM)).mpr hMNX₁)
      hX₁ne (hX₁F.trans hFleM)
  -- `g⁻¹·X₁·g ≤ F` is also a `p`-group, so `M ≤ N(g⁻¹·X₁·g) = g⁻¹·N(X₁)·g = g⁻¹·M·g`.
  set X₁' : Subgroup G := MulAut.conj g⁻¹ • X₁ with hX₁'def
  have hX₁'card : Nat.card ↥X₁' = p := by
    rw [hX₁'def, ← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
  have hX₁'F : X₁' ≤ F := by
    have hle : X₁' ≤ MulAut.conj g⁻¹ • (MulAut.conj g • F) :=
      hX₁'def ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hX₁'pg : IsPGroup p ↥X₁' := IsPGroup.of_card (n := 1) (by rw [hX₁'card, pow_one])
  have hMNX₁' : M ≤ Subgroup.normalizer (X₁' : Set G) := hpnorm X₁' hX₁'F hX₁'pg
  -- `N(X₁') = g⁻¹ • N(X₁) = g⁻¹ • M`.
  have hNX₁'eq : Subgroup.normalizer (X₁' : Set G) = MulAut.conj g⁻¹ • M := by
    rw [hX₁'def, ← hNX₁]
    exact (Subgroup.map_normalizer_eq_of_bijective X₁ (MulAut.conj g⁻¹).bijective).symm
  -- So `M ≤ g⁻¹ • M`, equal cards ⟹ `M = g⁻¹ • M`, i.e. `g ∈ N(M) = M`.
  rw [hNX₁'eq] at hMNX₁'
  have hcardM : Nat.card ↥(MulAut.conj g⁻¹ • M) = Nat.card ↥M :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) M).toEquiv).symm
  have hMeq : MulAut.conj g⁻¹ • M = M :=
    (Subgroup.eq_of_le_of_card_ge hMNX₁' (le_of_eq hcardM)).symm
  -- `g⁻¹·M·g = M ⟹ g⁻¹ ∈ N_G(M) ≤ M ⟹ g ∈ M`, contradicting `g ∉ M`.
  have hg_inv_N : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have hiff : h ∈ MulAut.conj g⁻¹ • M ↔ g * h * g⁻¹ ∈ M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        show ((MulAut.conj g⁻¹)⁻¹ • h : G) = g * h * g⁻¹ by
          simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    rw [hMeq] at hiff
    rw [inv_inv]; exact hiff
  have hg_inv_M : g⁻¹ ∈ M :=
    OddOrder.BG.Ch3.S10.maximal_normalizer_le_self hG hM hg_inv_N
  exact hgM (by simpa using inv_mem hg_inv_M)

/-- **Rank-3 lower bound on `M_F` for `β`-primes** (the `≥ 3` side of BG Theorem 15.7(a)'s rank
dichotomy): if a prime `r` divides `M_F` and lies in `β(M)`, then `r_r(M_F) ≥ 3`.

`M_F` is a Hall subgroup of `M` (`maxNilpotentNormalHall_isHall`), so `r ∈ π(M_F)` gives
`r ∤ [M : M_F]` and hence `r_r(M_F) = r_r(M)` (`pRank_eq_of_le_of_not_dvd_index`); and
`r ∈ β(M) ⊆ α(M)` gives `r_r(M) ≥ 3` by the definition of `α(M)`.  Consumed by the rank core
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` as the contradiction target against the `< 3`
bound coming from `C_{M_F}(X₁)`. -/
theorem three_le_pRank_mf_of_mem_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {r : ℕ} (hrπ : r ∈ S14.piSet (MF M)) (hrβ : r ∈ OddOrder.BG.Ch3.S10.beta M) :
    3 ≤ pRank ↥(MF M) r := by
  have hrmem : r ∈ (Nat.card ↥(MF M)).primeFactors := hrπ
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  haveI : Fact r.Prime := ⟨hrp⟩
  -- `M_F` is `π(M_F)`-Hall in `M`; `r ∈ π(M_F)` ⟹ `r ∤ [M : M_F]`.
  have hHall := maxNilpotentNormalHall_isHall (G := G) M
  have hidx : ¬ r ∣ ((MF M).subgroupOf M).index := fun hdvd =>
    hHall.2 r (Nat.mem_primeFactors.mpr ⟨hrp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrmem
  -- `r_r(M_F) = r_r(M)`; and `r ∈ β(M) ⊆ α(M)` ⟹ `r_r(M) ≥ 3`.
  rw [OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index (maxNilpotentNormalHall_le M) hidx]
  exact (OddOrder.BG.Ch3.S10.beta_subset_alpha M hrβ).2

/-- A subgroup contained in two **distinct** maximal subgroups of a minimal simple odd group has
rank `< 3`.  Contrapositive of `isUniquelyMaximal_of_three_le_rank_of_lt_top`: rank `≥ 3` would
force unique maximality, contradicting membership in two distinct coatoms. -/
theorem rank_lt_three_of_le_two_maximals [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {C M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hMN : M ≠ N) (hCM : C ≤ M) (hCN : C ≤ N) : rank ↥C < 3 := by
  by_contra h
  have hCt : C < ⊤ := lt_of_le_of_lt hCM (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM).lt_top
  exact hMN ((OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hCt
    (not_lt.mp h)).eq_of_isCoatom_of_le (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM) hCM
    (OddOrder.GroupTheory.mem_maximalSubgroups.mp hN) hCN)

/-- **Order-`p` non-TI witness extraction** (shared infrastructure of BG Theorem 15.7(a)/(e)):
from `¬FittingIsTI M` produce an element `g ∉ M`, a prime `p ∈ σ(M)`, and an order-`p` subgroup `X₁`
of `M_σ` that is also contained in the conjugate `M_σ^g`, with `C_G(X₁) ⊄ M` and
`rank (M_F ⊓ C_G(X₁)) < 3`.  This bundles the common prefix (steps 1, 3, 5–7) of
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`, so that both the rank-core (`M_F = M_σ`,
Theorem 15.7(a)) and the type-`F` trichotomy (Theorem 15.7(e), `isTypeI_of_isTypeF`) can consume the
same witness `X₁`.  The two conjugate-membership facts `X₁ ≤ M_σ` and `X₁ ≤ M_σ^g` drive the
`O_p(M_σ)`-noncyclicity argument (Coq `not_cycMp`), and `rank (M_F ⊓ C_G(X₁)) < 3` is the
`E1X_facts` rank bound. -/
theorem exists_inf_conj_fitting_orderP_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) :
    ∃ (g : G) (p : ℕ) (X₁ : Subgroup G),
      g ∉ M ∧ p.Prime ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
        Nat.card ↥X₁ = p ∧
        X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        X₁ ≤ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ∧
        ¬ Subgroup.centralizer (X₁ : Set G) ≤ M ∧
        rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 := by
  classical
  -- Setup: `g ∉ M`, `X = F(M) ⊓ F(M)^g ≠ ⊥`.
  obtain ⟨g, hgM, hXne⟩ := exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI hnotTI
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
  have hpσ_sub : ({p} : Set ℕ) ⊆ OddOrder.BG.Ch3.S10.sigma M := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  -- Generic helper: a `p`-subgroup of `F(M)` lies in `M_σ` (`O_p(F(M)) ≤ O_σ(F(M)) = F(M_σ) ≤ M_σ`).
  have hMσ_of : ∀ Z : Subgroup G, Z ≤ fittingInAmbient M → IsPGroup p ↥Z →
      Z ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    intro Z hZF hZp
    have h1 : Z ≤ opiCoreInG ({p} : Set ℕ) (fittingInAmbient M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hZF hZp
    have h2 : opiCoreInG ({p} : Set ℕ) (fittingInAmbient M)
        ≤ opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσ_sub _)
    have h3' : opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M)
        = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
      opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
    exact (h1.trans h2).trans (h3' ▸ OddOrder.BG.Ch2.S08.fittingInG_le _)
  have hX₁Mσ : X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := hMσ_of X₁ hX₁F hX₁pg
  -- `X₁ ≤ M_σ^g`: pull `X₁` back by `g⁻¹` into `F(M)`, apply `hMσ_of`, push forward by `g`.
  have hY₁ : MulAut.conj g⁻¹ • X₁ ≤ fittingInAmbient M := by
    have hle : MulAut.conj g⁻¹ • X₁ ≤ MulAut.conj g⁻¹ • (MulAut.conj g • fittingInAmbient M) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hY₁pg : IsPGroup p ↥(MulAut.conj g⁻¹ • X₁) := by
    have hcard : Nat.card ↥(MulAut.conj g⁻¹ • X₁) = p := by
      rw [← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hX₁cMσ : X₁ ≤ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
    have hY₁Mσ : MulAut.conj g⁻¹ • X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := hMσ_of _ hY₁ hY₁pg
    have hpush := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hY₁Mσ
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at hpush
  -- Step 6: `C_G(X₁) ⊄ M` (Theorem 10.1(e)).
  have hconj_g_inv : MulAut.conj g⁻¹ • X₁ ≤ M := hY₁.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hCG
    have he := (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hpσ hX₁ne hX₁pg).2.2.2.2
    exact hgM (by simpa using inv_mem (he hX₁M hCG g⁻¹ hconj_g_inv))
  -- Step 7: `rank (M_F ⊓ C_G(X₁)) < 3` (`C_{M_F}(X₁)` lies in `M` and in a coatom `N ≠ M`).
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
  exact ⟨g, p, X₁, hgM, hp, hpσ, hX₁card, hX₁Mσ, hX₁cMσ, hCGnotM, hrank3⟩

/-- **`O_p(M_F)` is noncyclic at a non-TI witness prime** (Coq `nonTI_Fitting_structure`, `not_cycMp`):
if `M_F` contains an order-`p` subgroup `X₁` that is also contained in the conjugate `M_F^g` for some
`g ∉ M`, then `O_p(M_F)` is not cyclic.  Were it cyclic, `X₁` would be its unique order-`p` subgroup,
hence characteristic in `O_p(M_F) ⊴ M`, giving `N_G(X₁) = M`; applied to `g⁻¹·X₁·g ≤ O_p(M_F)` it gives
`N_G(g⁻¹·X₁·g) = g⁻¹·M·g`, so `M = g⁻¹·M·g`, forcing `g ∈ M` — contradiction.  Both `X₁` and its
`g⁻¹`-conjugate land in the *same* cyclic `O_p(M_F)`, so no cyclic-conjugate transfer is needed.

This supplies the rank `≥ 2` lower bound of the abelian branch of Theorem 15.7(e)
(`isTypeI_of_isTypeF`): an abelian noncyclic `p`-group has `p`-rank `≥ 2`. -/
theorem not_isCyclic_opiCore_mf_of_orderP_le_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {g : G} {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime) (hgM : g ∉ M)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hX₁cMF : X₁ ≤ MulAut.conj g • MF M) :
    ¬ IsCyclic ↥(opiCoreInG ({p} : Set ℕ) (MF M)) := by
  classical
  intro hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hCdef
  haveI : IsCyclic ↥C := hcyc
  -- `M ≤ N(C)` since `C = O_p(M_F)` is characteristic in `M_F ⊴ M`.
  have hMNC : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ (maxNilpotentNormalHall_le_normalizer M)
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have hX₁C : X₁ ≤ C :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hX₁M : X₁ ≤ M := hX₁MF.trans (maxNilpotentNormalHall_le M)
  -- `M ≤ N(X₁)`, hence `N(X₁) = M`.
  have hMNX₁ : M ≤ Subgroup.normalizer (X₁ : Set G) :=
    le_normalizer_of_le_isCyclic_normalized hX₁C hMNC
  have hNX₁ : Subgroup.normalizer (X₁ : Set G) = M :=
    OddOrder.BG.Ch2.S08.normalizer_eq_of_normal_of_mem_maximal hG hM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hX₁M).mpr hMNX₁) hX₁ne hX₁M
  -- `X₁' := g⁻¹·X₁·g ≤ O_p(M_F)` too (it lies in `M_F` and is a `p`-group), so `M ≤ N(X₁')`.
  set X₁' : Subgroup G := MulAut.conj g⁻¹ • X₁ with hX₁'def
  have hX₁'card : Nat.card ↥X₁' = p := by
    rw [hX₁'def, ← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
  have hX₁'pg : IsPGroup p ↥X₁' := IsPGroup.of_card (n := 1) (by rw [hX₁'card, pow_one])
  have hX₁'MF : X₁' ≤ MF M := by
    have hle : X₁' ≤ MulAut.conj g⁻¹ • (MulAut.conj g • MF M) :=
      hX₁'def ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cMF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hX₁'C : X₁' ≤ C :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁'MF hX₁'pg
  have hMNX₁' : M ≤ Subgroup.normalizer (X₁' : Set G) :=
    le_normalizer_of_le_isCyclic_normalized hX₁'C hMNC
  -- `N(X₁') = g⁻¹ • N(X₁) = g⁻¹ • M`.
  have hNX₁'eq : Subgroup.normalizer (X₁' : Set G) = MulAut.conj g⁻¹ • M := by
    rw [hX₁'def, ← hNX₁]
    exact (Subgroup.map_normalizer_eq_of_bijective X₁ (MulAut.conj g⁻¹).bijective).symm
  rw [hNX₁'eq] at hMNX₁'
  have hcardM : Nat.card ↥(MulAut.conj g⁻¹ • M) = Nat.card ↥M :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) M).toEquiv).symm
  have hMeq : MulAut.conj g⁻¹ • M = M :=
    (Subgroup.eq_of_le_of_card_ge hMNX₁' (le_of_eq hcardM)).symm
  -- `g⁻¹·M·g = M ⟹ g⁻¹ ∈ N_G(M) ≤ M ⟹ g ∈ M`, contradicting `g ∉ M`.
  have hg_inv_N : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have hiff : h ∈ MulAut.conj g⁻¹ • M ↔ g * h * g⁻¹ ∈ M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        show ((MulAut.conj g⁻¹)⁻¹ • h : G) = g * h * g⁻¹ by
          simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    rw [hMeq] at hiff
    rw [inv_inv]; exact hiff
  have hg_inv_M : g⁻¹ ∈ M :=
    OddOrder.BG.Ch3.S10.maximal_normalizer_le_self hG hM hg_inv_N
  exact hgM (by simpa using inv_mem hg_inv_M)

/-- **An abelian noncyclic `p`-group (`p` odd) has `p`-rank `≥ 2`** (additive analogue of mathcomp's
`abelian_rank1_cyclic`): a finite commutative `p`-group `R` with `p` odd that is not cyclic has
`2 ≤ pRank R p`.  Noncyclicity gives `p < |Ω₁(R)|` (contrapositive of
`isCyclic_of_card_omega1_le_prime`); `Ω₁(R)` is elementary abelian
(`isElementaryAbelian_omega_one_of_comm`) and a `p`-group, so `p² ≤ |Ω₁(R)|` and hence
`2 ≤ log_p|Ω₁(R)| ≤ pRank R p` (`le_pRank`).  Supplies the rank `≥ 2` lower bound of the abelian
branch of BG Theorem 15.7(e) (`isTypeI_of_isTypeF`). -/
theorem two_le_pRank_of_comm_isPGroup_not_isCyclic {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hcomm : ∀ x y : R, x * y = y * x)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) : 2 ≤ pRank R p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- `Ω₁(R)` is elementary abelian and a `p`-group.
  have hΩea : (Omega R p 1).IsElementaryAbelian p :=
    OddOrder.BG.Ch1_Preliminary.isElementaryAbelian_omega_one_of_comm hcomm
  have hΩpg : IsPGroup p ↥(Omega R p 1) := fun g =>
    (hR g.val).imp fun k hk =>
      Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hk)
  -- Noncyclicity ⟹ `p < |Ω₁(R)|`.
  have hlt : p < Nat.card ↥(Omega R p 1) := by
    by_contra hle
    exact hnc (OddOrder.BG.Ch1.S04.isCyclic_of_card_omega1_le_prime hR hp_odd (not_lt.mp hle))
  -- `|Ω₁(R)| = p^k` with `k ≥ 2`.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩpg
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    · simp only [pow_zero] at hk; rw [hk] at hlt; omega
    · simp only [pow_one] at hk; rw [hk] at hlt; omega
  have hcard : p ^ 2 ≤ Nat.card ↥(Omega R p 1) := by
    rw [hk]; exact Nat.pow_le_pow_right (le_of_lt hp1) hk2
  -- `2 ≤ log_p|Ω₁(R)| ≤ pRank R p`.
  exact le_trans (Nat.le_log_of_pow_le hp1 hcard) (le_pRank (Omega R p 1) hΩea)

/-- **`C_{M_F}(X₁)` is not uniquely maximal** (Coq `nonTI_Fitting_structure`, `E1X_facts` clause
`C1 ∉ 'U`): if the centralizer `C_G(X₁)` of a nontrivial subgroup `X₁` is not contained in `M`, then
`C_{M_F}(X₁) = M_F ⊓ C_G(X₁)` is not uniquely maximal.

Were it uniquely maximal, then since `C_{M_F}(X₁) ≤ C_G(X₁) < ⊤`, the overgroup `C_G(X₁)` would also
be uniquely maximal (`IsUniquelyMaximal.of_le_of_lt_top`); and the unique maximal subgroup over
`C_{M_F}(X₁)` is `M` (a coatom containing it), so `C_G(X₁) ≤ M`, contradicting the hypothesis.
This is the `E1X_facts` input feeding the non-abelian branch of Theorem 15.7(e)
(`abelian C_{M_F}(X₁)` and `cyclic O_{p'}(M_F)`). -/
theorem not_isUniquelyMaximal_mf_inf_centralizer_of_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X₁ : Subgroup G} (hX₁ne : X₁ ≠ ⊥)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M) :
    ¬ OddOrder.GroupTheory.IsUniquelyMaximal (MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := by
  intro huniq
  -- `C₁ ≤ M`, `C₁ ≤ C_G(X₁)`, and `C_G(X₁) < ⊤`.
  have hC1M : MF M ⊓ Subgroup.centralizer (X₁ : Set G) ≤ M :=
    inf_le_left.trans (maxNilpotentNormalHall_le M)
  have hC1C : MF M ⊓ Subgroup.centralizer (X₁ : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    inf_le_right
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  have hCGlt : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
    lt_of_le_of_lt (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x₀.2))
      (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG (fun h => hx₀ne (Subtype.ext h)))
  -- `C_G(X₁)` is uniquely maximal, with the same unique maximal subgroup `M` as `C₁`.
  have huniqC : OddOrder.GroupTheory.IsUniquelyMaximal (Subgroup.centralizer (X₁ : Set G)) :=
    huniq.of_le_of_lt_top hC1C hCGlt
  have hMco : IsCoatom M := OddOrder.GroupTheory.mem_maximalSubgroups.mp hM
  have heq : M = huniqC.uniqueMaximalSubgroup :=
    huniq.eq_of_isCoatom_of_le hMco hC1M huniqC.uniqueMaximalSubgroup_isCoatom
      (hC1C.trans huniqC.le_uniqueMaximalSubgroup)
  exact hCGnotM (heq ▸ huniqC.le_uniqueMaximalSubgroup)

/-- **A finite nilpotent group with all Sylow subgroups abelian is abelian.**  A finite nilpotent
group is the internal direct product of its (normal) Sylow subgroups
(`Sylow.directProductOfNormal`); if each factor is commutative the product is, and commutativity
transports back across the isomorphism.  Used to prove `abelian C_{M_F}(X₁)` in the `E1X_facts`
input to BG Theorem 15.7(e): each Sylow of the nilpotent `C_{M_F}(X₁)` is abelian (a non-abelian
one would be uniquely maximal by `nonabelian_pgroup_isUniquelyMaximal`, contradicting
`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`). -/
theorem isMulCommutative_of_isNilpotent_of_sylow_comm {N : Type*} [Group N] [Finite N]
    [Group.IsNilpotent N]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p N), IsMulCommutative ↥(P : Subgroup N)) :
    IsMulCommutative N := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  have hnorm : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), (↑P : Subgroup N).Normal :=
    fun P => OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  let e := Sylow.directProductOfNormal (G := N) hnorm
  -- The direct-product domain is commutative: each component `↥P` is.
  have hDcomm : ∀ a b : (∀ p : (Nat.card N).primeFactors, ∀ P : Sylow p N, ↥(P : Subgroup N)),
      a * b = b * a := by
    intro a b
    funext p P
    haveI : Fact (p : ℕ).Prime := Fact.mk (Nat.prime_of_mem_primeFactors p.2)
    exact (isMulCommutative_iff.mp (h p P)) (a p P) (b p P)
  -- Transport commutativity across `e : (Π Sylows) ≃* N`.
  refine isMulCommutative_iff.mpr fun x y => ?_
  have hxy := congrArg e (hDcomm (e.symm x) (e.symm y))
  rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at hxy

/-- **`C_{M_F}(X₁)` is abelian** (Coq `nonTI_Fitting_structure`, `E1X_facts` clause `abelian C1`):
if `C_G(X₁) ⊄ M` (with `X₁ ≠ 1`), the nilpotent subgroup `C_{M_F}(X₁) = M_F ⊓ C_G(X₁)` is abelian.

Every Sylow `P` of the nilpotent `C_{M_F}(X₁)` is abelian: a non-abelian one would be uniquely
maximal (`nonabelian_pgroup_isUniquelyMaximal`), and as `P ≤ C_{M_F}(X₁) < ⊤` this would force
`C_{M_F}(X₁)` itself to be uniquely maximal (`IsUniquelyMaximal.of_le_of_lt_top`), contradicting
`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`.  Then `isMulCommutative_of_isNilpotent_of_sylow_comm`
gives abelianness.  This is the second `E1X_facts` input (with noncyclicity) to the non-abelian
branch of BG Theorem 15.7(e). -/
theorem isMulCommutative_mf_inf_centralizer_of_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X₁ : Subgroup G} (hX₁ne : X₁ ≠ ⊥)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M) :
    IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := by
  classical
  set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
  have hC1MF : C1 ≤ MF M := inf_le_left
  -- `C1` is nilpotent (a subgroup of the nilpotent `M_F`).
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  haveI : Group.IsNilpotent ↥(C1.subgroupOf (MF M)) := Subgroup.isNilpotent (C1.subgroupOf (MF M))
  haveI hC1nil : Group.IsNilpotent ↥C1 :=
    Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hC1MF).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hC1MF).surjective
  -- `C1 < ⊤` and `C1` is not uniquely maximal.
  have hC1notU : ¬ OddOrder.GroupTheory.IsUniquelyMaximal C1 :=
    not_isUniquelyMaximal_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hC1lt : C1 < ⊤ := lt_of_le_of_lt (hC1MF.trans (maxNilpotentNormalHall_le M))
    (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM).lt_top
  -- Each Sylow of `C1` is abelian (else `C1` is uniquely maximal).
  apply isMulCommutative_of_isNilpotent_of_sylow_comm
  intro r _ P
  by_contra hnab
  set P' : Subgroup G := (P : Subgroup ↥C1).map C1.subtype with hP'def
  have hP'le : P' ≤ C1 := hP'def ▸ Subgroup.map_subtype_le _
  have hequiv : ↥(P : Subgroup ↥C1) ≃* ↥P' :=
    Subgroup.equivMapOfInjective _ C1.subtype C1.subtype_injective
  have hP'p : IsPGroup r ↥P' := P.isPGroup'.of_equiv hequiv
  have hP'nab : ¬ IsMulCommutative ↥P' := fun hcomm => hnab <|
    isMulCommutative_iff.mpr fun a b => hequiv.injective <| by
      rw [map_mul, map_mul]; exact (isMulCommutative_iff.mp hcomm) (hequiv a) (hequiv b)
  exact hC1notU ((nonabelian_pgroup_isUniquelyMaximal hG hP'p hP'nab).of_le_of_lt_top hP'le hC1lt)

/-- **Frobenius complement order divides `|kernel| - 1`** (mathcomp `regular_norm_dvd_pred`, in the
`IsFrobeniusAction` form): if a finite group `A` acts on a finite group `N` by automorphisms with no
nonidentity element of `A` fixing a nonidentity element of `N` (`IsFrobeniusAction A N`), then
`|A| ∣ |N| - 1`.  Immediate from `IsFrobeniusAction.card_modEq_one` (`|N| ≡ 1 [MOD |A|]`).

This is the divisibility crux of the exponent condition (conjunct A) of BG Theorem 15.7(e2):
applied to `N = Z_q = Ω₁(Z(O_q(M_σ)))` (order `q`) with `A = U₀` the Frobenius complement acting
fixed-point-freely on the kernel `M_σ`, it gives `|U₀| ∣ q - 1`, hence `exp(U) = exp(U₀) ∣ q - 1`. -/
theorem card_dvd_sub_one_of_isFrobeniusAction {A N : Type*} [Group A] [Finite A] [Group N]
    [Finite N] [MulDistribMulAction A N] (h : OddOrder.Isaacs.Ch06.IsFrobeniusAction A N) :
    Nat.card A ∣ Nat.card N - 1 := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype N := Fintype.ofFinite N
  have hmod : Nat.card N ≡ 1 [MOD Nat.card A] := by
    simpa only [Nat.card_eq_fintype_card] using h.card_modEq_one
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm

/-- **The join of two commuting commutative subgroups is commutative.**  Writing `A ⊔ B` as the
closure of `↑A ∪ ↑B`, generators commute: two from `A` (abelian), two from `B` (abelian), or one of
each (they centralize each other, `A ≤ C_G(B)`).  Used for `not_cPP` in BG Theorem 15.7(e): were
`O_p(M_F)` abelian, then `M_F = O_p(M_F) ⊔ O_{p'}(M_F)` would be abelian (the `p'`-core is abelian
and centralizes the `p`-core), contradicting non-abelianness of `M_F`. -/
theorem isMulCommutative_sup_of_le_centralizer {A B : Subgroup G}
    (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simpa using congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hx⟩ ⟨y, hy⟩)
  · exact (Subgroup.mem_centralizer_iff.mp (hAB hx) y hy).symm
  · exact Subgroup.mem_centralizer_iff.mp (hAB hy) x hx
  · simpa using congrArg Subtype.val (isMulCommutative_iff.mp hB ⟨x, hx⟩ ⟨y, hy⟩)

/-- **A finite commutative group of odd order and rank `≤ 1` is cyclic** (additive converse of
mathcomp's `abelian_rank1_cyclic`).  Each Sylow `q`-subgroup is an abelian `q`-group whose `pRank`
is at most `rank N ≤ 1`, hence cyclic (contrapositive of
`two_le_pRank_of_comm_isPGroup_not_isCyclic`, using that `q`, a divisor of the odd `|N|`, is odd);
so `N` is a `Z`-group, and a finite commutative (hence nilpotent) `Z`-group is cyclic
(`IsZGroup.exponent_eq_card` + `IsCyclic.of_exponent_eq_card`).  This is the rank-1 ⇒ cyclic step of
the `cyclic O_{p'}(M_F)` conjunct of BG Theorem 15.7(e). -/
theorem isCyclic_of_isMulCommutative_of_rank_le_one {N : Type*} [Group N] [Finite N]
    (hcomm : ∀ x y : N, x * y = y * x) (hodd : Odd (Nat.card N)) (hrank : rank N ≤ 1) :
    IsCyclic N := by
  classical
  haveI hmc : IsMulCommutative N := isMulCommutative_iff.mpr hcomm
  haveI hZ : _root_.IsZGroup N := by
    refine ⟨fun q hq P => ?_⟩
    haveI : Fact q.Prime := ⟨hq⟩
    by_contra hPnc
    rcases subsingleton_or_nontrivial ↥(P : Subgroup N) with _ | hnt
    · exact hPnc inferInstance
    · have hPcomm : ∀ x y : ↥(P : Subgroup N), x * y = y * x := fun x y =>
        Subtype.ext (hcomm (x : N) (y : N))
      have hqdvd : q ∣ Nat.card N := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
        have h1 : 1 < Nat.card ↥(P : Subgroup N) := Finite.one_lt_card_iff_nontrivial.mpr hnt
        have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; omega
        have hqP : q ∣ Nat.card ↥(P : Subgroup N) := by rw [hn]; exact dvd_pow_self q hn0
        exact hqP.trans (Subgroup.card_subgroup_dvd_card _)
      have hqodd : Odd q := by
        rcases hq.eq_two_or_odd' with rfl | h
        · exact absurd (even_iff_two_dvd.mpr hqdvd) (Nat.not_even_iff_odd.mpr hodd)
        · exact h
      have h2 : 2 ≤ pRank ↥(P : Subgroup N) q :=
        two_le_pRank_of_comm_isPGroup_not_isCyclic hqodd hPcomm P.isPGroup' hPnc
      have hle : pRank ↥(P : Subgroup N) q ≤ rank N :=
        le_trans (pRank_mono_of_le (P : Subgroup N)) (pRank_le_rank q)
      omega
  exact IsCyclic.of_exponent_eq_card (_root_.IsZGroup.exponent_eq_card N)

/-- **Shared "`O_p(M_F)` is non-abelian" step** for BG Theorem 15.7(e) (Coq `not_cPP`).  From the
non-TI witness data (`X₁ ≤ M_F` of order `p`, `C_G(X₁) ⊄ M`) with a non-abelian Fitting subgroup
`M_F`, the `p`-core `P = O_p(M_F)` is non-abelian: the `p'`-core `R = O_{p'}(M_F)` centralizes `P`
(cores of a nilpotent group commute) and lies in the abelian `C₁ = C_{M_F}(X₁)`, so `R` is abelian;
were `P` abelian too, `M_F = P ⊔ R` would be a join of two commuting commutative subgroups, hence
abelian.  Used by both conjunct B (`typeF_nonabelian_cyclic_opiCore_compl`) and the per-prime
witness `q = p` case. -/
theorem opiCore_singleton_not_isMulCommutative_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (MF M)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hX₁ne : X₁ ≠ ⊥ :=
    fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  set R : Subgroup G := opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) with hRdef
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hcomm : ⁅R, P⁆ = ⊥ := by
    rw [hRdef, hPdef, Subgroup.commutator_comm]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (MF M)
  have hRcP : R ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hRMF : R ≤ MF M := opiCoreInG_le _ _
  have hCPCX : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₁P)
  have hRC1 : R ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf hRMF (hRcP.trans hCPCX)
  have hC1ab : IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hRab : ∀ x y : ↥R, x * y = y * x := fun x y =>
    Subtype.ext (by
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(x : G), hRC1 x.2⟩ ⟨(y : G), hRC1 y.2⟩))
  have hPRsup : P ⊔ R = MF M := opiCoreInG_sup_compl_eq_of_isNilpotent ({p} : Set ℕ)
  intro hPab
  refine hnab (hPRsup ▸ isMulCommutative_sup_of_le_centralizer hPab ?_ ?_)
  · exact isMulCommutative_iff.mpr hRab
  · rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

/-- **BG Theorem 15.7(e), conjunct B — `cyclic O_{p'}(M_F)`** (Coq `nonTI_Fitting_structure`,
`cycHp'`): for the non-TI witness prime `p` (`X₁ ≤ M_F` of order `p`, `C_G(X₁) ⊄ M`) and a
non-abelian Fitting subgroup `M_F`, the `p'`-core `O_{p'}(M_F)` is cyclic.

`C₁ = C_{M_F}(X₁)` is abelian (`isMulCommutative_mf_inf_centralizer_of_not_le`) and not uniquely
maximal (`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`).  The `p'`-core `R = O_{p'}(M_F)`
centralizes the `p`-core `P = O_p(M_F) ⊇ X₁` (`opiCoreInG_commutator_compl_eq_bot`), so `R ≤ C₁`,
hence `R` is abelian.  `P` is non-abelian (else `M_F = P ⊔ R` would be abelian,
`isMulCommutative_sup_of_le_centralizer`), so `P ∈ 𝒰` (`nonabelian_pgroup_isUniquelyMaximal`).
Were `rank R ≥ 2`, then `D = M_F ⊓ C_G(P) ⊇ R` would have `rank ≥ 2` and lie in `C_G(P)`, so
`D ∈ 𝒰` (BG Corollary 9.2) and hence `C₁ ⊇ D` would be uniquely maximal — contradiction.  Thus
`rank R ≤ 1`, and the odd abelian `R` is cyclic (`isCyclic_of_isMulCommutative_of_rank_le_one`). -/
theorem typeF_nonabelian_cyclic_opiCore_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    p ∈ (Nat.card ↥(MF M)).primeFactors ∧
      IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  -- `p ∈ π(M_F)`: `p = |X₁| ∣ |M_F|`.
  have hpπ : p ∈ (Nat.card ↥(MF M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hX₁card ▸ Subgroup.card_dvd_of_le hX₁MF, Nat.card_pos.ne'⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  set R : Subgroup G := opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) with hRdef
  -- `X₁ ≤ P = O_p(M_F)`.
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- `R = O_{p'}(M_F) ≤ C_G(P)` (the `p`- and `p'`-cores of the nilpotent `M_F` commute).
  have hcomm : ⁅R, P⁆ = ⊥ := by
    rw [hRdef, hPdef, Subgroup.commutator_comm]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (MF M)
  have hRcP : R ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hRMF : R ≤ MF M := opiCoreInG_le _ _
  have hCPCX : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₁P)
  have hRC1 : R ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf hRMF (hRcP.trans hCPCX)
  -- `C₁` abelian ⟹ `R` abelian.
  have hC1ab : IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hRab : ∀ x y : ↥R, x * y = y * x := fun x y =>
    Subtype.ext (by
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(x : G), hRC1 x.2⟩ ⟨(y : G), hRC1 y.2⟩))
  -- `P` non-abelian (`not_cPP`): else `M_F = P ⊔ R` is abelian.
  have hPRsup : P ⊔ R = MF M := opiCoreInG_sup_compl_eq_of_isNilpotent ({p} : Set ℕ)
  have hPnab : ¬ IsMulCommutative ↥P := by
    intro hPab
    refine hnab (hPRsup ▸ isMulCommutative_sup_of_le_centralizer hPab ?_ ?_)
    · exact isMulCommutative_iff.mpr hRab
    · rw [Subgroup.commutator_comm] at hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  have hPU : OddOrder.GroupTheory.IsUniquelyMaximal P :=
    nonabelian_pgroup_isUniquelyMaximal hG hPpg hPnab
  -- `rank R ≤ 1`: else `C₁ ∈ 𝒰` via `D = M_F ⊓ C_G(P)`, contradicting `nonuniqC1`.
  have hC1notU : ¬ OddOrder.GroupTheory.IsUniquelyMaximal
      (MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    not_isUniquelyMaximal_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hrankR : rank ↥R ≤ 1 := by
    by_contra hr
    have h2R : 2 ≤ rank ↥R := by omega
    have hRD : R ≤ MF M ⊓ Subgroup.centralizer (P : Set G) := le_inf hRMF hRcP
    have h2D : 2 ≤ rank ↥(MF M ⊓ Subgroup.centralizer (P : Set G)) :=
      le_trans h2R (rank_le_of_injective (Subgroup.inclusion_injective hRD))
    have hDU : OddOrder.GroupTheory.IsUniquelyMaximal (MF M ⊓ Subgroup.centralizer (P : Set G)) :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hPU inf_le_right h2D
    have hDC1 : MF M ⊓ Subgroup.centralizer (P : Set G) ≤
        MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf inf_le_left (inf_le_right.trans hCPCX)
    have hC1lt : MF M ⊓ Subgroup.centralizer (X₁ : Set G) < ⊤ :=
      lt_of_le_of_lt (inf_le_left.trans (maxNilpotentNormalHall_le M))
        (mem_maximalSubgroups.mp hM).lt_top
    exact hC1notU (hDU.of_le_of_lt_top hDC1 hC1lt)
  -- `R` is odd, abelian, of rank `≤ 1`, hence cyclic.
  have hRodd : Odd (Nat.card ↥R) := by
    rcases Nat.even_or_odd (Nat.card ↥R) with he | ho
    · exact absurd
        (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans (Subgroup.card_subgroup_dvd_card R)))
        (Nat.not_even_iff_odd.mpr hG.odd)
    · exact ho
  exact ⟨hpπ, isCyclic_of_isMulCommutative_of_rank_le_one hRab hRodd hrankR⟩

/-- **BG Theorem 15.7(e), conjunct A per-prime witness** (Coq `oZ`: `|Ω₁(Z(O_q(H)))| = q`): for the
non-TI witness data and a non-abelian `M_F`, every prime `q ∈ π(M_F)` has an order-`q` subgroup `Z`
of `M_F` that is normal in `M` (hence `td.U0`-invariant), feeding
`typeF_exponent_dvd_sub_one_of_invariant_card`.

* `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic (`typeF_nonabelian_cyclic_opiCore_compl`), so its unique
  order-`q` subgroup `Ω₁(O_q(M_F))` is characteristic (`characteristic_of_subgroup_of_isCyclic`) in
  `O_q(M_F)`, characteristic in `M_F`, hence normal in `M`.
* `q = p`: `Z = Ω₁(Z(O_p(M_F)))`; `|Z| = p` because `B = X₁ ⊔ Z` is elementary abelian of `p`-rank
  `≤ rank (M_F ⊓ C_G(X₁)) < 3`, forcing `pRank Z ≤ 1`, and `Z ≠ ⊥` (`O_p(M_F)` is a nontrivial
  `p`-group); `X₁ ⊄ Z` because `O_p(M_F)` is non-abelian (else `M_F = O_p ⊔ O_{p'}` abelian).

The conclusion also records `¬ X₁ ≤ Z` (`X₁ ⊄ Z`): for `q = p` this is the structural fact above;
for `q ≠ p` it is immediate from `|X₁| = p`, `|Z| = q` coprime.  This feeds the type-V Singer-case
faithfulness `K ⊓ C_G(O_p(M_F)) = ⊥` (`kappaHall_inf_centralizer_opiCore_eq_bot`). -/
theorem exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M))
    {q : ℕ} (hq : q.Prime) (hqπ : q ∈ (Nat.card ↥(MF M)).primeFactors) :
    ∃ Z : Subgroup G, Z ≤ MF M ∧ Nat.card ↥Z = q ∧
      M ≤ Subgroup.normalizer (Z : Set G) ∧ ¬ X₁ ≤ Z ∧
      (q = p → Z = OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (MF M)) p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have hMNMF : M ≤ Subgroup.normalizer ((MF M : Subgroup G) : Set G) :=
    maxNilpotentNormalHall_le_normalizer M
  by_cases hqp : q = p
  · -- `q = p`: `Z = Ω₁(Z(O_p(M_F)))`, `|Z| = p` by the rank argument (Coq `oZ0`, L1085-1117).
    set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
    -- `X₁ ≤ P`, and `P` is a nontrivial `p`-group.
    have hX₁ne : X₁ ≠ ⊥ :=
      fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
    have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
    have hX₁P : X₁ ≤ P :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
    have hPne : P ≠ ⊥ := fun h => hX₁ne (le_bot_iff.mp (h ▸ hX₁P))
    haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
    have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
    -- `P` non-abelian; `C₁ = C_{M_F}(X₁)` abelian.
    have hPnab : ¬ IsMulCommutative ↥P :=
      opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
    set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
    have hC1ab : IsMulCommutative ↥C1 :=
      isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
    -- `Z := Ω₁(Z(P))`, elementary abelian, `≤ P ≤ M_F`.
    set Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG P p with hZdef
    have hZP : Z ≤ P := OddOrder.BG.Ch3.S10.omega1CenterInG_le P p
    have hZMF : Z ≤ MF M := hZP.trans (opiCoreInG_le _ _)
    have hWea : (omega1OfAbelian ↥P (Subgroup.center ↥P) p
        (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).IsElementaryAbelian p :=
      omega1OfAbelian_isElementaryAbelian
    have hZea : Z.IsElementaryAbelian p := by rw [hZdef]; exact hWea.map P.subtype_injective
    -- `X₁` centralizes `Z` (`Z ≤ Z(P)`, `X₁ ≤ P`).
    have hX₁CZ : X₁ ≤ Subgroup.centralizer (Z : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
      obtain ⟨z', hz', hz'eq⟩ := hz
      have hz'c : z' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hz').1
      rw [← hz'eq]
      simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨x, hX₁P hx⟩)).symm
    -- `X₁ ⊄ Z`: else `X₁ ≤ Z(P)` ⟹ `P ≤ C_G(X₁)` ⟹ `P ≤ C₁` abelian (vs `hPnab`).
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hsub
      refine hPnab ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have hPCX₁ : P ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxZ : x ∈ Z := hsub hx
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hxZ
        obtain ⟨x', hx', hx'eq⟩ := hxZ
        have hx'c : x' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hx').1
        rw [← hx'eq]
        simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx'c ⟨g, hg⟩)).symm
      have hPC1 : P ≤ C1 := le_inf (opiCoreInG_le _ _) hPCX₁
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(a : G), hPC1 a.2⟩ ⟨(b : G), hPC1 b.2⟩)
    -- `X₁ ⊓ Z = ⊥` (`X₁` prime order, `X₁ ⊄ Z`).
    have hX₁Zbot : X₁ ⊓ Z = ⊥ := by
      have hdvd : Nat.card ↥(X₁ ⊓ Z) ∣ p :=
        hX₁card ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd (inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hX₁card, hpp]))) hX₁notZ
    -- `B = X₁ ⊔ Z` elementary abelian, `≤ C₁`.
    have hX₁ea : X₁.IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_card_prime hX₁card
    have hBea : (X₁ ⊔ Z).IsElementaryAbelian p :=
      isElementaryAbelian_sup_of_le_centralizer hX₁ea hZea hX₁CZ
    have hX₁C1 : X₁ ≤ C1 :=
      le_inf hX₁MF (le_centralizer_self_of_isElementaryAbelian hX₁ea)
    have hZC1 : Z ≤ C1 := by
      refine le_inf hZMF (fun z hz => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hX₁CZ hx) z hz).symm
    have hBC1 : (X₁ ⊔ Z) ≤ C1 := sup_le hX₁C1 hZC1
    -- `|X₁ ⊔ Z| = p · |Z|`.
    have hX₁NZ : X₁ ≤ Subgroup.normalizer Z :=
      hX₁CZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hcoe : (↑X₁ * ↑Z : Set G) = ↑(X₁ ⊔ Z) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z hX₁NZ).symm
    have hcardform : Nat.card ↥(X₁ ⊔ Z) = p * Nat.card ↥Z := by
      have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X₁ Z
      rw [hcoe, hX₁Zbot, Subgroup.card_bot, mul_one, hX₁card] at h
      exact h
    -- `log_p |X₁ ⊔ Z| ≤ rank C₁ < 3`.
    have hBlog : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ 2 := by
      have hB'ea : ((X₁ ⊔ Z).subgroupOf C1).IsElementaryAbelian p :=
        OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hBC1).symm hBea
      have hB'card : Nat.card ↥((X₁ ⊔ Z).subgroupOf C1) = Nat.card ↥(X₁ ⊔ Z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC1).toEquiv
      have h1 : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ pRank ↥C1 p := by
        rw [← hB'card]; exact le_pRank _ hB'ea
      have h2 : pRank ↥C1 p ≤ rank ↥C1 := pRank_le_rank p
      have h3 : rank ↥C1 < 3 := hrank3
      omega
    -- `Z` is a nontrivial `p`-group, so `|Z| = p`.
    have hZpow : Nat.card ↥Z = p ^ (Nat.log p (Nat.card ↥Z)) := by
      rw [hZea.log_card_eq_finrank]; exact hZea.card_eq_pow_finrank
    have hZne : Z ≠ ⊥ := by
      haveI hcNt : Nontrivial ↥(Subgroup.center ↥P) := hPpg.center_nontrivial
      have hcdvd : Nat.card ↥(Subgroup.center ↥P) ∣ Nat.card ↥P :=
        Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPpg
      have hpdvd : p ∣ Nat.card ↥(Subgroup.center ↥P) := by
        have h1 : 1 < Nat.card ↥(Subgroup.center ↥P) :=
          Finite.one_lt_card_iff_nontrivial.mpr hcNt
        rw [hk] at hcdvd
        obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hcdvd
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · rw [pow_zero] at hjeq; omega
        · rw [hjeq]; exact dvd_pow_self p hjpos.ne'
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) p hpdvd
      have hwne : ((w : ↥P) : G) ≠ 1 := by
        intro hcoe1
        have : (w : ↥P) = 1 := by ext; simpa using hcoe1
        have hw1 : w = 1 := by ext; simpa using this
        rw [hw1, orderOf_one] at hw; exact hp.one_lt.ne' hw.symm
      refine fun hbot => hwne ?_
      have hmem : ((w : ↥P) : G) ∈ Z := by
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG]
        refine Subgroup.mem_map.mpr ⟨(w : ↥P), mem_omega1OfAbelian.mpr ⟨w.2, ?_⟩, rfl⟩
        have : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
        simpa using congrArg (Subtype.val (p := fun a => a ∈ Subgroup.center ↥P)) this
      rw [hbot] at hmem; simpa using hmem
    obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥Z = p ^ d := ⟨_, hZpow⟩
    have hsupeq : Nat.card ↥(X₁ ⊔ Z) = p ^ (d + 1) := by rw [hcardform, hd, pow_succ']
    rw [hsupeq, Nat.log_pow hp.one_lt] at hBlog
    have hd_ge : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero] at hd
      exact hZne (Subgroup.eq_bot_of_card_eq _ hd)
    have hZcard : Nat.card ↥Z = p := by
      rw [hd, show d = 1 from le_antisymm (by omega) hd_ge, pow_one]
    -- `M ≤ N(Z)`: `M ≤ N(P) ≤ N(Ω₁(Z(P))) = N(Z)`.
    have hMNP : M ≤ Subgroup.normalizer (P : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ) hMNMF
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [hZdef]
      exact hMNP.trans (OddOrder.BG.Ch3.S10.normalizer_le_normalizer_omega1CenterInG P p)
    exact ⟨Z, hZMF, hZcard.trans hqp.symm, hMNZ, hX₁notZ, fun _ => hZdef⟩
  · -- `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic; take its order-`q` subgroup.
    have hqdvd : q ∣ Nat.card ↥(MF M) := (Nat.mem_primeFactors.mp hqπ).2.1
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(MF M)) q hqdvd
    set Z : Subgroup G := (Subgroup.zpowers x).map (MF M).subtype with hZdef
    have hZcard : Nat.card ↥Z = q := by
      rw [hZdef, Subgroup.card_map_of_injective (MF M).subtype_injective, Nat.card_zpowers, hxord]
    have hZMF : Z ≤ MF M := hZdef ▸ Subgroup.map_subtype_le _
    have hZpg : IsPGroup q ↥Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
    -- `Z ≤ O_q(M_F)` (a `q`-group inside the nilpotent `M_F`).
    have hZOq : Z ≤ opiCoreInG ({q} : Set ℕ) (MF M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hZMF hZpg
    -- `O_q(M_F) ≤ O_{p'}(M_F)` (as `q ≠ p`), and `O_{p'}(M_F)` is cyclic, so `O_q(M_F)` is cyclic.
    have hcyc : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) :=
      (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab).2
    have hOqle : opiCoreInG ({q} : Set ℕ) (MF M) ≤ opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono
        (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hqp)) ↥(MF M))
    haveI : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := hcyc
    haveI hOqcyc : IsCyclic ↥(opiCoreInG ({q} : Set ℕ) (MF M)) := Subgroup.isCyclic_of_le hOqle
    -- `Z.subgroupOf O_q(M_F)` is characteristic (subgroup of a cyclic group).
    haveI hWchar : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).Characteristic :=
      OddOrder.Isaacs.Ch04.characteristic_of_subgroup_of_isCyclic _
    -- `M ≤ N(O_q(M_F)) ≤ N(Z)`.
    have hMNOq : M ≤ Subgroup.normalizer ((opiCoreInG ({q} : Set ℕ) (MF M) : Subgroup G) : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hMNMF
    have hZeq : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).map
        (opiCoreInG ({q} : Set ℕ) (MF M)).subtype = Z :=
      Subgroup.map_subgroupOf_eq_of_le hZOq
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← hZeq]
      exact hMNOq.trans (OddOrder.Isaacs.Ch07.normalizer_le_normalizer_map_of_characteristic)
    -- `¬ X₁ ≤ Z`: `|X₁| = p`, `|Z| = q`, `p ≠ q`, so `X₁ ≤ Z` would force `p ∣ q`.
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hle
      have hdvd : p ∣ q := by
        have h := Subgroup.card_dvd_of_le hle; rwa [hX₁card, hZcard] at h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm
    exact ⟨Z, hZMF, hZcard, hMNZ, hX₁notZ, fun h => absurd h hqp⟩

/-- **BG Theorem 15.7(a), rank-theoretic core** (mmd L4192-4198): if `F(M)` is not a TI-subgroup
of `G`, then no prime divides `M_F` and lies in `β(M)`.

The `≥ 3` side is fully proved (`three_le_pRank_mf_of_mem_beta`: any `r ∈ π(M_F) ∩ β(M)` has
`r_r(M_F) ≥ 3`); the proof below reduces the goal to the complementary `< 3` bound
`pRank (M_F) r < 3`, the genuinely deep §15 content isolated as the single remaining `sorry`.

**Proved building blocks (this file):** the setup
`exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` (step 1: `g ∉ M`, `X = F(M) ⊓ F(M)^g ≠ ⊥`)
and `rank_lt_three_of_le_two_maximals` (step 7 core: a subgroup in two distinct maximals has rank
`< 3`).  The remaining assembly, with the located upstream lemmas:

* **(step 3, `p ∈ σ(M)`)** pick `p ∈ π(X)`, `X₁ ≤ X` of order `p`
  (`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`: `X₁ ≤ O_p(F(M))`).  If `p ∉ σ(M)` then
  `O_p(F(M)) ≤ O_{σ'}(F(M))` is cyclic (`fitting_decomposition`), so `X₁` is the unique order-`p`
  subgroup, hence characteristic and normal in both `M` and `M^g`; `normalizer_eq_of_normal_of_mem_maximal`
  (S08, currently `private`) forces `M^g = M`, contradicting `g ∉ M`.  ⟹ `p ∈ σ(M)`.  *(fiddly sub-step:
  cyclic group ⟹ unique/characteristic order-`p` subgroup.)*
* **(step 5, `p ∉ β(M)`)** `X₁ ≤ O_p(M) ≤ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`) and
  `X₁ ≤ F(M)^g ≤ M^g`, so `X₁ ≤ M_σ ⊓ M^g`; Lemma 12.17 (`Msigma_inf_conj_isBetaCompl`) ⟹ `p ∉ β(M)`,
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
  -- `M_F` lies in `C_{M_F}(X₁)`; hence `r ∤ [M_F : C_{M_F}(X₁)]` and `r_r(M_F) = r_r(C_{M_F}(X₁)) < 3`.
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
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`), forcing `M_β = 1`.  Then `M'/M_β ≅ M'` is nilpotent
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
      show p ∈ (Nat.card ↥(MF M)).primeFactors
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
that meets F(M) but is also centralised by E1 and hence intersects M' trivially; … only the inclusion
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
        -- (`nonTI_Fitting_structure`, which uses `M^'(1) ⊆ 'F(M)` and whose source comment states the
        -- printed equality "does not appear to be valid").  Full justification in the docstring above.
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
    -- overstatement, MathComp `BGsection15` uses `M^'(1) ⊆ 'F(M)`).  The argument is *type-independent*
    -- (covers both type `F` and type `P₁`): take a §12 `E`-setup `M = M_σ ⋊ E`, so
    -- `M' = M_σ ⊔ E'` (`derivedInG_eq_Msigma_sup_derivedInG_complement`).  Lemma 12.19 supplies a Hall
    -- `β(M)'`-subgroup `W ≤ M_σ` of `M_σ` that `E'` centralizes; since `π(M_σ) = π(M_F)` is disjoint
    -- from `β(M)` (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`, as `M_F = M_σ`), `M_σ` is itself a
    -- `β'`-group, so `W = M_σ` and `E' ≤ C_G(M_σ)`.  Then `M_σ ≤ F(M)` (`M_F = M_σ` nilpotent normal)
    -- and `E' ≤ C_G(M_σ) ⊓ M ≤ F(M)` (`fitting_decomposition`: `F(M) = (C_M(M_F) ⊓ M) ⊔ M_F`), whence
    -- `M' = M_σ ⊔ E' ≤ F(M)`.
    haveI : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    -- `M' = M_σ ⊔ E'`.
    rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG hsetup]
    -- Lemma 12.19: a Hall `β(M)'`-subgroup `W ≤ M_σ` of `M_σ` centralized by `E'`.
    obtain ⟨W, hWle, hWHall, hWcent⟩ := derivedE_centralizes_betaComplement hG hsetup
    -- `W = M_σ`: every prime of the index `[M_σ : W]` divides `|M_σ| = |M_F|`, hence lies in `π(M_F)`,
    -- which is disjoint from `β(M)`; but the Hall condition makes that index a `β`-number, so it is `1`.
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
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    {r : ℕ} (hrprime : r.Prime) (hr : r ∈ tau2 M) (hrU : r ∈ piSet U) :
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
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
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

/-- **Phase B/C step 6 `def_q1` centralization of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1336--1338, the `sub_nilpotent_cent2` step): with the partner `L`'s `σ`-core `L_σ`
**nilpotent**, its `q`-core `Q = O_q(L) ≤ L_σ`, and a `q₁`-subgroup `A ≤ L_σ` with `q₁ ≠ q`
(`q₁` prime), one has `A ≤ C_G(Q)`.

Proof (Coq `sub_nilpotent_cent2 (Fitting_nil L)`): working inside the nilpotent `↥(L_σ)`,
`Q.subgroupOf L_σ = O_q(↥L_σ)` is a *normal* `q`-subgroup and `A.subgroupOf L_σ` is a `q₁`-group
with `q₁ ≠ q` (so `q ∤ |A|`); `commutator_eq_bot_of_isNilpotent_of_normal_isPGroup` gives
`⁅Q̄, Ā⁆ = ⊥`, i.e. `Ā ≤ C(Q̄)`, which pushes out to `A ≤ C_G(Q)`. -/
theorem le_centralizer_opiCore_of_msigma_nilpotent [Finite G]
    {L A : Subgroup G} {q q1 : ℕ} [Fact q.Prime]
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L))
    (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma L)
    (hq1prime : q1.Prime) (hq1ne : q1 ≠ q) (hApg : IsPGroup q1 ↥A) :
    A ≤ Subgroup.centralizer (opiCoreInG ({q} : Set ℕ) L : Set G) := by
  classical
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  set Ls : Subgroup G := OddOrder.BG.Ch3.S10.Msigma L with hLsdef
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσM : Ls ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hMnormMσ : L ≤ Subgroup.normalizer (Ls : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQMσ : Q ≤ Ls := by
    rw [hQdef, hLsdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) Ls := by
    rw [hQdef, hLsdef]
    exact opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hLsdef ▸ hQMσ)
  haveI : Group.IsNilpotent ↥Ls := hLsdef ▸ hnil
  -- `Q̄ = Q.subgroupOf L_σ = O_q(↥L_σ)`, a normal `q`-subgroup of `↥L_σ`.
  have hQsub_eq : Q.subgroupOf Ls = Ch03.oPiCore ({q} : Set ℕ) ↥Ls := by
    rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
  haveI hQbarN : (Q.subgroupOf Ls).Normal := by rw [hQsub_eq]; exact Ch03.oPiCore.normal _ _
  have hQbarpg : IsPGroup q ↥(Q.subgroupOf Ls) :=
    (isPGroup_opiCoreInG_singleton L (q := q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQMσ).symm
  -- `Ā = A.subgroupOf L_σ` is a `q₁`-group; `q ∉ π(|Ā|)` since `q ≠ q₁`.
  have hAbarpg : IsPGroup q1 ↥(A.subgroupOf Ls) :=
    hApg.of_equiv (Subgroup.subgroupOfEquivOfLe hAMσ).symm
  have hqnotA : q ∉ (Nat.card ↥(A.subgroupOf Ls)).primeFactors := by
    intro hq
    obtain ⟨n, hn⟩ := hAbarpg.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hq
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hq1prime).mp
      (hq.1.dvd_of_dvd_pow hq.2.1)
    exact hq1ne this.symm
  -- `⁅Q̄, Ā⁆ = ⊥` (nilpotent, normal `q`-part vs `q'`-part), so `Ā ≤ C(Q̄)`.
  have hcommbot : ⁅Q.subgroupOf Ls, A.subgroupOf Ls⁆ = ⊥ :=
    commutator_eq_bot_of_isNilpotent_of_normal_isPGroup hQbarpg hqnotA
  have hAbarC : A.subgroupOf Ls ≤ Subgroup.centralizer ((Q.subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcommbot)
  -- Push out to the ambient: `A ≤ C_G(Q)`.
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have haLs : a ∈ Ls := hAMσ ha
  have hgLs : g ∈ Ls := hQMσ hg
  have haA : (⟨a, haLs⟩ : ↥Ls) ∈ A.subgroupOf Ls := Subgroup.mem_subgroupOf.mpr ha
  have hgQ : (⟨g, hgLs⟩ : ↥Ls) ∈ Q.subgroupOf Ls := Subgroup.mem_subgroupOf.mpr hg
  have haC := hAbarC haA
  have hcomm := Subgroup.mem_centralizer_iff.mp haC (⟨g, hgLs⟩ : ↥Ls) hgQ
  exact congrArg Subtype.val hcomm

/-- **Phase B/C uniqueness core of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1329--1338, the `def_q1` argument): if a uniqueness subgroup `Q ∈ 𝒰`
(`IsUniquelyMaximal Q`) is centralized by a rank-2 elementary abelian `A ∈ ℰ²_{q₁}(G)`, and `A`
lies in two maximal subgroups `H` and `Mstar`, then `H = Mstar`.

This is the engine behind `def_q1`: in the theorem, `Q = O_q(M*)` is a uniqueness subgroup
(Thm 12.13), `A ⊆ C(Q)` (both in the nilpotent `F(M*)`, coprime when `q₁ ≠ q`), and `A ⊆ H`,
`A ⊆ M*`; the conclusion `H = M*` contradicts `H ≠ M*`, forcing `q₁ = q`.

Proof (Coq `cent_uniq_Uniqueness` + `eq_uniq_mmax`): `A` is a rank-2 (`≥ 2`) subgroup of `C_G(Q)`,
so `A ∈ 𝒰` by BG Corollary 9.2 (`isUniquelyMaximal_of_le_centralizer_of_two_le_rank`).  Then both
`H` and `Mstar`, being maximal subgroups over `A`, equal `A.uniqueMaximalSubgroup`, hence are
equal. -/
theorem eq_of_uniquelyMaximal_centralized_by_rank2_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Q A H Mstar : Subgroup G} {q1 : ℕ}
    (hq1prime : q1.Prime)
    (hQU : IsUniquelyMaximal Q) (hACQ : A ≤ Subgroup.centralizer (Q : Set G))
    (hA : A ∈ elemAbelianOfRank G q1 2) (hHmax : H ∈ maximalSubgroups G) (hAH : A ≤ H)
    (hMstarmax : Mstar ∈ maximalSubgroups G) (hAMstar : A ≤ Mstar) :
    H = Mstar := by
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  -- `A ∈ 𝒰` (BG Corollary 9.2: rank-2 subgroup of `C_G(Q)` with `Q ∈ 𝒰`).
  have hAU : IsUniquelyMaximal A :=
    OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hQU hACQ
      (two_le_rank_of_mem_elemAbelianOfRank_two hA)
  -- Both maximal subgroups over `A` are `A.uniqueMaximalSubgroup`, hence equal.
  have hH := hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hHmax) hAH
  have hMst :=
    hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hMstarmax) hAMstar
  rw [hH, hMst]

/-- **Phase B/C step 6 `def_q1` centralization, `F(L)`-nilpotent form**
(Coq `tau2_P2type_signalizer`, BGsection15.v:1337, the `sub_nilpotent_cent2 (Fitting_nil L)` step):
a `q₁`-subgroup `A ≤ F(L)` and the `q`-core `Q = O_q(L) ≤ F(L)` (`q₁ ≠ q`, `q₁` prime) satisfy
`A ≤ C_G(Q)`.

Unlike `le_centralizer_opiCore_of_msigma_nilpotent` (which needs the σ-core `L_σ` nilpotent — *not*
yet available at the `def_q1` point of Theorem 15.8), this uses **`F(L)` (`fittingInAmbient L`)
nilpotent**, which is *always* true (`fittingInG_isNilpotent`, Coq `Fitting_nil L`).  This is what
breaks the `def_q1`/`nilLs` circularity: `def_q1` is derived *before* `L_σ`-nilpotency.

Proof: working inside the nilpotent `↥(F(L))`, `Q.subgroupOf F(L)` is a *normal* `q`-subgroup
(`Q = O_q(L) ⊴ L ⊇ F(L)`, so normal in `F(L)`; a `q`-group by `isPGroup_opiCoreInG_singleton`) and
`A.subgroupOf F(L)` is a `q₁`-group with `q ∉ π(|A|)` (`q ≠ q₁`);
`commutator_eq_bot_of_isNilpotent_of_normal_isPGroup` gives `⁅Q̄, Ā⁆ = ⊥`, i.e. `Ā ≤ C(Q̄)`, which
pushes out to `A ≤ C_G(Q)`. -/
theorem le_centralizer_opiCore_of_fittingInAmbient_nilpotent [Finite G]
    {L A : Subgroup G} {q q1 : ℕ} [Fact q.Prime]
    (hMnormQ : L ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) L : Set G))
    (hQFL : opiCoreInG ({q} : Set ℕ) L ≤ fittingInAmbient L)
    (hAFL : A ≤ fittingInAmbient L)
    (hq1prime : q1.Prime) (hq1ne : q1 ≠ q) (hApg : IsPGroup q1 ↥A) :
    A ≤ Subgroup.centralizer (opiCoreInG ({q} : Set ℕ) L : Set G) := by
  classical
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  set F : Subgroup G := fittingInAmbient L with hFdef
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hFL : F ≤ L := OddOrder.BG.Ch2.S08.fittingInG_le L
  haveI : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent L
  -- `Q.subgroupOf F` is a normal `q`-subgroup of the nilpotent `↥F`.
  have hFnormQ : F ≤ Subgroup.normalizer (Q : Set G) := hFL.trans hMnormQ
  haveI hQbarN : (Q.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQFL).mpr hFnormQ
  have hQbarpg : IsPGroup q ↥(Q.subgroupOf F) :=
    (isPGroup_opiCoreInG_singleton L (q := q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQFL).symm
  -- `A.subgroupOf F` is a `q₁`-group; `q ∉ π(|Ā|)` since `q ≠ q₁`.
  have hAbarpg : IsPGroup q1 ↥(A.subgroupOf F) :=
    hApg.of_equiv (Subgroup.subgroupOfEquivOfLe hAFL).symm
  have hqnotA : q ∉ (Nat.card ↥(A.subgroupOf F)).primeFactors := by
    intro hq
    obtain ⟨n, hn⟩ := hAbarpg.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hq
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hq1prime).mp
      (hq.1.dvd_of_dvd_pow hq.2.1)
    exact hq1ne this.symm
  -- `⁅Q̄, Ā⁆ = ⊥` (nilpotent, normal `q`-part vs `q'`-part), so `Ā ≤ C(Q̄)`.
  have hcommbot : ⁅Q.subgroupOf F, A.subgroupOf F⁆ = ⊥ :=
    commutator_eq_bot_of_isNilpotent_of_normal_isPGroup hQbarpg hqnotA
  have hAbarC : A.subgroupOf F ≤
      Subgroup.centralizer ((Q.subgroupOf F : Subgroup ↥F) : Set ↥F) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcommbot)
  -- Push out to the ambient: `A ≤ C_G(Q)`.
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have haF : a ∈ F := hAFL ha
  have hgF : g ∈ F := hQFL hg
  have haA : (⟨a, haF⟩ : ↥F) ∈ A.subgroupOf F := Subgroup.mem_subgroupOf.mpr ha
  have hgQ : (⟨g, hgF⟩ : ↥F) ∈ Q.subgroupOf F := Subgroup.mem_subgroupOf.mpr hg
  have haC := hAbarC haA
  have hcomm := Subgroup.mem_centralizer_iff.mp haC (⟨g, hgF⟩ : ↥F) hgQ
  exact congrArg Subtype.val hcomm

/-- **BG Prop 14.2(e) uniqueness (`O_q(L) ∈ 𝒰`)** — the `uniqQ` clause the repo `typeP_structure`
omits, recovered from Lemma 13.6.  Coq `Ptype_structure` clause (e) `uniqQ` (BGsection14.v), used at
the `uniqQ` step of `tau2_P2type_signalizer` (BGsection15.v:1330).  For a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, `q ∈ π(K) ∩ σ(L)`, if `Q = O_q(L)` is a Sylow-`q` of `L`
(`q ∤ [L:Q]`) then `Q` is uniquely maximal.

Proof: `Q ≤ L_σ` is a Sylow-`q` of `L_σ` too (`q ∈ σ ⟹ q ∤ [L:L_σ]`, so `|Q| = q^{v_q|L_σ|}`,
giving the maximal-`q`-subgroup property `hSmax`); a rank-1 `q`-witness `X = ⟨w⟩ ≤ K ≤ L_σ ⊓ C(E₁)`
(as `E₁ ≤ Ks` and `K ≤ C(Ks)`) feeds Lemma 13.6 (`maximalContaining_eq_singleton_of_E1`,
`P = E₁ ≠ ⊥` from the type-`P` `E`-setup) giving `𝓜(Q) = {L}`; conclude via
`IsUniquelyMaximal.of_unique_maximal`.  Avoids the (circular) `nonabelian` route. -/
theorem opiCore_isUniquelyMaximal_of_isSylow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKsHall : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdef : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπK : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hQidx : ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index) :
    IsUniquelyMaximal (opiCoreInG ({q} : Set ℕ) L) := by
  classical
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQL : Q ≤ L := hQMσ.trans hMσL
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- `|Q| = q ^ v_q(|L|) = q ^ v_q(|L_σ|)` (Sylow of `L`; `q ∈ σ ⟹ q ∤ [L:L_σ]`).
  have hQsubL : IsPGroup q ↥(Q.subgroupOf L) := hQpg.comap_subtype
  have hcardL : Nat.card ↥Q = q ^ (Nat.card ↥L).factorization q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
    have hc := (hQsubL.toSylow hQidx).card_eq_multiplicity
    rwa [hQsubL.toSylow_coe hQidx] at hc
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma L)
      ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hL
  have hqidxMσ : ¬ q ∣ ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L).index := fun hd =>
    hMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)).factorization q := by
    rw [hcardL]
    congr 1
    have hcardmul := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv] at hcardmul
    rw [← hcardmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqidxMσ, add_zero]
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma L → IsPGroup q ↥T →
      Q ≤ T → Q = T :=
    fun T hT hTq hQT =>
      OddOrder.BG.Ch3.S13.eq_of_le_of_isPGroup_card_eq_factorization hQcard hT hTq hQT
  -- Type-`P` `E`-setup and a rank-1 `q`-witness `X = ⟨w⟩ ≤ K`.
  obtain ⟨E, E₁, E₂, E₃, hE, hE1Ks, hKsE, hE1ne⟩ :=
    S14.exists_typePESetup_kappaHall hG hL hP hKsL hKsHall
  have hqdvdK : q ∣ Nat.card ↥K := Nat.dvd_of_mem_primeFactors hqπK
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvdK
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = q := by
    rw [Nat.card_zpowers]; exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXC : Subgroup.zpowers (w : G) ≤
      OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (E₁ : Set G) := by
    refine hXK.trans (le_inf (hKdef ▸ inf_le_left) ?_)
    exact (show K ≤ Subgroup.centralizer (Ks : Set G) from hKdef ▸ inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE1Ks))
  have hMQ : maximalSubgroupsContaining Q = {L} :=
    (OddOrder.BG.Ch3.S13.maximalContaining_eq_singleton_of_E1 hG hE hqσ (le_refl E₁) hE1ne
      hXelem hXC hQMσ hQpg hSmax).2
  refine IsUniquelyMaximal.of_unique_maximal
    (lt_of_le_of_lt hQL (mem_maximalSubgroups.mp hL).lt_top) hL hQL (fun N hN hQN => ?_)
  have hNmem : N ∈ maximalSubgroupsContaining Q := ⟨mem_maximalSubgroups.mp hN, hQN⟩
  rw [hMQ, Set.mem_singleton_iff] at hNmem
  exact hNmem

/-- **`O_q(L)` is a Sylow-`q` of `L` (`q ∤ [L : O_q(L)]`)** for a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, `q ∈ π(K) ∩ σ(L)` (Coq `sylQ`, `tau2_P2type_signalizer`
BGsection15.v:1319).  Reduces to `q ∤ [L_σ : Q]` (index tower with `q ∤ [L:L_σ]`, `σ`-Hall); the
`q`-core `Q = O_q(L) = O_q(L_σ)` is a Sylow-`q` of `L_σ` in both cases: `L_σ` nilpotent ⟹ `Q` a
Hall `{q}`-subgroup (`oPiCore_isHall_of_isNilpotent`); `L_σ` non-nilpotent ⟹ `L` type-`P₁`
(Thm 15.2) with a `K`-invariant `q'`-complement `D` of `Q` in `L_σ`
(`exists_kInvariant_qComplement`), so `[L_σ:Q] = |D|` is a `q'`-number. -/
theorem opiCore_index_coprime_of_typeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdef : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπK : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L) :
    ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index := by
  classical
  haveI : IsSolvable ↥L := hG.solvable_of_mem_maximalSubgroups hL
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- `q ∤ [L_σ : Q]`.
  have hqidxMσ : ¬ q ∣ (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)).index := by
    by_cases hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L)
    · -- nilpotent: `Q = O_q(L_σ)` is a Hall `{q}`-subgroup of `L_σ`.
      have hMnormMσ : L ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma L : Subgroup G) : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMσL).mp
          (by rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance)
      have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) (OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [hQdef]; exact opiCoreInG_eq_of_normal_le hMσL hMnormMσ (hQdef ▸ hQMσ)
      have hQsub_eq : Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)
          = Ch03.oPiCore ({q} : Set ℕ) ↥(OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
      haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L) := hnil
      have hHall : Ch03.IsHallSubgroup ({q} : Set ℕ)
          (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)) := by
        rw [hQsub_eq]; exact OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent ({q} : Set ℕ)
      exact fun hd => hHall.2 q (Nat.mem_primeFactors.mpr
        ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) (Set.mem_singleton q)
    · -- non-nilpotent: type-`P₁`; `Q` has a `K`-invariant `q'`-complement `D` in `L_σ`.
      have hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L := fun heq =>
        hnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mp heq)
      have hP1 : S14.IsTypeP1 L := isTypeP1_of_mf_ne_msigma hG hL hne
      have hKprime : (Nat.card ↥K).Prime :=
        kstar_card_prime_of_inputs hG hL hP1 hKsL hKs hKdef
      have hKcard : Nat.card ↥K = q :=
        ((Nat.prime_dvd_prime_iff_eq Fact.out hKprime).mp (Nat.dvd_of_mem_primeFactors hqπK)).symm
      have hMσderived : OddOrder.BG.Ch3.S10.Msigma L = derivedInG L :=
        typeP1_msigma_eq_derivedInG hG hL hP1 hKsL hKs hKdef
      obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hL hP hKsL hKs hKdef
      have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
          (Ks.subgroupOf L) := by rw [hMσderived]; exact hcomplDer
      have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L))
          (Nat.card ↥(Ks.subgroupOf L)) := by
        have h := coprime_card_derived_kappaHall_of_isComplement' hKs hcomplDer
        rwa [← hMσderived] at h
      have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hL hP hKsL hKs hKdef
      have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L
          ⊓ Subgroup.centralizer (Ks : Set G))).Prime := by rw [← hKdef]; exact hKprime
      have hKstarQ : K ≤ Q := by
        have h := kstar_le_opiCore_of_inputs hG hL hKsL hcomplMσ hcop_sub.symm hcond2 hne hqG
        rw [← hKdef, hKcard, ← hQdef] at h; exact h
      have hcopKMσ : Nat.Coprime (Nat.card ↥Ks) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsL).toEquiv] at hcop_sub
        exact hcop_sub.symm
      have hKMσdisj : Disjoint Ks (OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [disjoint_iff]
        exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
          (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
      have hKsne : Ks ≠ ⊥ := by
        intro h0
        apply hnil
        have hKeqMσ : K = OddOrder.BG.Ch3.S10.Msigma L := by
          rw [hKdef, h0]
          have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
            rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
          rw [hc, inf_top_eq]
        exact (IsPGroup.of_card (show Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) = q ^ 1 by
          rw [pow_one, ← hKcard, hKeqMσ])).isNilpotent
      have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma L := fun hQeq =>
        hnil (hQeq ▸ hQpg.isNilpotent)
      obtain ⟨D, hDMσ, -, -, hcomplD, -, -, hDq'⟩ :=
        exists_kInvariant_qComplement hG hL hP hKsL hKs hKdef hQdef hQMσ hMnormQ hKstarQ hQneMσ
          hKsne hKMσdisj hcopKMσ
      rw [hcomplD.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDMσ).toEquiv]
      exact fun hd => hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)
  -- Tower `[L:Q] = [L_σ:Q]·[L:L_σ]` with `q ∤ [L:L_σ]` (`σ`-Hall).
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma L)
      ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hL
  have hqidxMσL : ¬ q ∣ ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L).index := fun hd =>
    hMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  intro hd
  have htower : Q.relIndex (OddOrder.BG.Ch3.S10.Msigma L)
      * (OddOrder.BG.Ch3.S10.Msigma L).relIndex L = Q.relIndex L :=
    Subgroup.relIndex_mul_relIndex Q (OddOrder.BG.Ch3.S10.Msigma L) L hQMσ hMσL
  have hd' : q ∣ Q.relIndex (OddOrder.BG.Ch3.S10.Msigma L)
      * (OddOrder.BG.Ch3.S10.Msigma L).relIndex L := htower ▸ hd
  rcases (Nat.Prime.dvd_mul Fact.out).mp hd' with h1 | h2
  · exact hqidxMσ h1
  · exact hqidxMσL h2

/-- **BG Theorem 15.2 `sAFL`, non-nilpotent case** (Coq `tau2_P2type_signalizer` sAFL step,
BGsection15.v:1322 via `Fcore_structure`): for a type-`P` maximal `L` with non-nilpotent `L_σ`
(`M_F ≠ M_σ`, so `L` is type-`P₁`), `κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, a rank-2 elementary
abelian `A ≤ L_σ` lies in `F(L)`.  `A` centralizes the chief factor `Q/Q₀` (`Q = O_q(L)`,
`Q₀ = C_Q(D)`, `D` the `q'`-complement), so `A ⊆ C_{L_σ}(Q/Q₀) = F(L)`
(`centralizer_msigma_quotient_le_fittingInAmbient`).

The hypothesis `A ≤ C(K)` (`K = C_{L_σ}(Ks)`) is Coq's `cKA` — **essential for soundness**: the
bare statement "every rank-2 `A ≤ L_σ` lies in `F(L)`" is *false* when `q1 ≠ q` (an `A ≤ D` in the
`q'`-complement acting non-innerly on `Q` escapes `F(L) = Q·C(Q)`); Coq's `A` centralizes `K`, which
via the chief-factor action forces `A ⊆ C_{L_σ}(Q/Q₀) = F(L)`.

✅ **Landed sorry-free** (2026-07-07, issue 9017 更新 #18; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`).  This was the third `sAFL` clause and the *last* gate of
`typeP_partner_sylow_uniquelyMaximal_bundle` (hence of `tau2_transfer_constraint` = BG Thm 15.8, now
also sorry-free); `sylQ` = `opiCore_index_coprime_of_typeP` and `uniqQ` =
`opiCore_isUniquelyMaximal_of_isSylow` were already proved.

**Proof** (Coq `Fcore_structure` eq3 `C_Ms(Ks/Q₀|'Q)=F(M)`, BGsection15.v:579-593): the repo has eq2
(`centralizer_msigma_quotient_le_fittingInAmbient`: `x∈M_σ` centralizing `Q̄=Q/Q₀` ⟹ `x∈F(L)`); eq3
is derived by the **minimality lifting** `C_{M_σ}(K̄|'Q) = C_{M_σ}(Q̄|'Q)`.  `W = {y∈Q : ∀x∈H, ⁅x,y⁆
∈Q₀}` for `H = C_{M_σ}(K̄) = {x∈M_σ : ∀k∈K, ⁅x,k⁆∈Q₀}` satisfies `K ≤ W`, `Q₀ < W ≤ Q`, and is
`L`-normal, so `hmin` (minimality of the chief factor `Q/Q₀`) forces `Q ≤ W`, i.e. every `x`
centralizing `K̄` centralizes `Q̄`.  The keystone `hWnorm` (`W` is `L`-normal) reduces to `H` being
`L`-normal via the conjugation identity `⁅x, g y g⁻¹⁆ = g ⁅g⁻¹ x g, y⁆ g⁻¹` (`L` normalizes `Q`,
`Q₀`).  `H ⊴ L` splits over `L = M_σ ⊔ Ks` (`hcomplMσ`): (1) `M_σ ≤ N(H)` since
`M_σ' = ⁅M_σ,M_σ⁆ ⊆ Q ⊔ ⁅D,D⁆ ⊆ H ⊆ M_σ` (`derivedInG_le_sup_of_normal`, `hDcomm`,
`commutator_le_iff_le_normalizer`); (2) `Ks ≤ N(H)` since `Ks` centralizes `K` (`K ⊆ C(Ks)`, so
`s⁻¹ k s = k`) and normalizes `M_σ`, `Q₀`.  Then `hACK : A⊆C(K)` ⟹ `Ā` centralizes `K̄` ⟹ (lifting)
`Ā` centralizes `Q̄` ⟹ (eq2) `A⊆F(L)`.  (issue 9017 update #12/#15/#16/#18.) -/
theorem A_le_fittingInAmbient_of_typeP1_nonnil [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L Ks K A : Subgroup G} {q1 : ℕ}
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L)
    (hA : A ∈ elemAbelianOfRank G q1 2) (hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma L)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) :
    A ≤ fittingInAmbient L := by
  classical
  haveI : IsSolvable ↥L := hG.solvable_of_mem_maximalSubgroups hL
  have hP1 : S14.IsTypeP1 L := isTypeP1_of_mf_ne_msigma hG hL hne
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mpr hnil)
  -- Chief-factor prime `q = |K|` and `Q = O_q(L)`.
  have hKprime : (Nat.card ↥K).Prime := kstar_card_prime_of_inputs hG hL hP1 hKsL hKs hKdefL
  set q : ℕ := Nat.card ↥K with hqcard
  haveI : Fact q.Prime := ⟨hKprime⟩
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hKMσ : K ≤ OddOrder.BG.Ch3.S10.Msigma L := by rw [hKdefL]; exact inf_le_left
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q (Nat.mem_primeFactors.mpr
      ⟨hKprime, Subgroup.card_dvd_of_le hKMσ, Nat.card_pos.ne'⟩)
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQL : Q ≤ L := hQMσ.trans hMσL
  have hMnormQ : L ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- Complement setup (as in `opiCore_index_coprime_of_typeP` non-nil branch).
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma L = derivedInG L :=
    typeP1_msigma_eq_derivedInG hG hL hP1 hKsL hKs hKdefL
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hL hP hKsL hKs hKdefL
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
      (Ks.subgroupOf L) := by rw [hMσderived]; exact hcomplDer
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L))
      (Nat.card ↥(Ks.subgroupOf L)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hKs hcomplDer
    rwa [← hMσderived] at h
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hL hP hKsL hKs hKdefL
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L
      ⊓ Subgroup.centralizer (Ks : Set G))).Prime := by rw [← hKdefL]; exact hKprime
  have hKstarQ : K ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hL hKsL hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKdefL, ← hqcard, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥Ks) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsL).toEquiv] at hcop_sub
    exact hcop_sub.symm
  have hKMσdisj : Disjoint Ks (OddOrder.BG.Ch3.S10.Msigma L) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKsne : Ks ≠ ⊥ := by
    intro h0; apply hMσnotnil
    have hKeqMσ : K = OddOrder.BG.Ch3.S10.Msigma L := by
      rw [hKdefL, h0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    exact (IsPGroup.of_card (show Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) = q ^ 1 by
      rw [pow_one, hqcard, hKeqMσ])).isNilpotent
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma L := fun hQeq =>
    hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  obtain ⟨D, hDMσ, hKnormD, hQDdisj, hcomplD, hDnil, hDne, hDq'⟩ :=
    exists_kInvariant_qComplement hG hL hP hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ hQneMσ
      hKsne hKMσdisj hcopKMσ
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hQ0Q : Q0 ≤ Q := by rw [hQ0def]; exact inf_le_left
  obtain ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, hmin⟩ :=
    chiefFactor_Q0_normal_minimal_of_inputs hG hL hP1 hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ
      hQneMσ hKsne hKMσdisj hcopKMσ hMσnotnil hDq' hDMσ hKnormD hQDdisj hcomplD hDnil hDne
  haveI hQ0nQ : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr (hQL.trans hMNQ0)
  obtain ⟨hEA, -⟩ :=
    isElementaryAbelian_chiefFactor_of_minimalNormal hQ0ltQ hQL hQpg hMnormQ hMNQ0 hmin
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := by
    intro x hxQ y hyQ
    have hcomm := hEA.comm (QuotientGroup.mk (⟨x, hxQ⟩ : ↥Q)) (QuotientGroup.mk (⟨y, hyQ⟩ : ↥Q))
    have h1 : QuotientGroup.mk (⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆) =
        (1 : ↥Q ⧸ Q0.subgroupOf Q) := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have h2 : ((⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆ : ↥Q) : G) = ⁅x, y⁆ := by
      push_cast [commutatorElement_def]; rfl
    rwa [h2] at h1
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using Nat.coprime_one_right _
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hd =>
        hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))).symm
  have hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma L, (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) →
      x ∈ fittingInAmbient L :=
    centralizer_msigma_quotient_le_fittingInAmbient hG hL hQMσ hDMσ hQ0def hQ0Q hcomplD hMnormQ
      hMNQ0 hQpg hDnil hcopDQ hQab
  -- **Minimality lifting** (Coq `Fcore_structure` eq3, BGsection15.v:579-593): `C_{L_σ}(K̄|'Q) =
  -- C_{L_σ}(Q̄|'Q)`.  `W = {y ∈ Q : ∀ x ∈ C_{L_σ}(K̄), ⁅x,y⁆ ∈ Q₀}` is `M`-normal, `⊇ K ⊋ Q₀`, so
  -- `Q ≤ W` (`hmin`), i.e. every `x` centralizing `K̄` centralizes `Q̄`.  (issue 9017 #16.)
  have hLift : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma L,
      (∀ k ∈ K, ⁅x, k⁆ ∈ Q0) → (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) := by
    have hMσnormQ0 : OddOrder.BG.Ch3.S10.Msigma L ≤ Subgroup.normalizer (Q0 : Set G) :=
      hMσL.trans hMNQ0
    have hQnormQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQMσ.trans hMσnormQ0
    -- `H = C_{M_σ}(K̄)`, the `M_σ`-elements centralizing `K` modulo `Q₀`.
    let H : Subgroup G :=
      { carrier := {x | x ∈ OddOrder.BG.Ch3.S10.Msigma L ∧ ∀ k ∈ K, ⁅x, k⁆ ∈ Q0}
        one_mem' := ⟨(OddOrder.BG.Ch3.S10.Msigma L).one_mem, fun k _ => by
          rw [commutatorElement_one_left]; exact Q0.one_mem⟩
        mul_mem' := fun {x x'} hx hx' => ⟨(OddOrder.BG.Ch3.S10.Msigma L).mul_mem hx.1 hx'.1,
          fun k hk => by
            have heq : ⁅x * x', k⁆ = (x * ⁅x', k⁆ * x⁻¹) * ⁅x, k⁆ := by
              rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
            rw [heq]
            have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
            exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 ⁅x', k⁆).mp (hx'.2 k hk))
              (hx.2 k hk)⟩
        inv_mem' := fun {x} hx => ⟨(OddOrder.BG.Ch3.S10.Msigma L).inv_mem hx.1, fun k hk => by
          have heq : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * (x⁻¹)⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
          exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN0)
            ⁅x, k⁆⁻¹).mp (Q0.inv_mem (hx.2 k hk))⟩ }
    have hHle : H ≤ OddOrder.BG.Ch3.S10.Msigma L := fun x hx => hx.1
    -- `W = {y ∈ Q : ∀ x ∈ H, ⁅x,y⁆ ∈ Q₀}`, the `Q̄`-elements fixed by `H`.
    let W : Subgroup G :=
      { carrier := {y | y ∈ Q ∧ ∀ x ∈ H, ⁅x, y⁆ ∈ Q0}
        one_mem' := ⟨Q.one_mem, fun x _ => by rw [commutatorElement_one_right]; exact Q0.one_mem⟩
        mul_mem' := fun {y y'} hy hy' => ⟨Q.mul_mem hy.1 hy'.1, fun x hx => by
          have heq : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hyN0 : y ∈ Subgroup.normalizer (Q0 : Set G) := hQnormQ0 hy.1
          exact Q0.mul_mem (hy.2 x hx)
            ((Subgroup.mem_normalizer_iff.mp hyN0 ⁅x, y'⁆).mp (hy'.2 x hx))⟩
        inv_mem' := fun {y} hy => ⟨Q.inv_mem hy.1, fun x hx => by
          have heq : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * (y⁻¹)⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hyN0 : y ∈ Subgroup.normalizer (Q0 : Set G) := hQnormQ0 hy.1
          exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hyN0)
            ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hy.2 x hx))⟩ }
    have hWle : W ≤ Q := fun y hy => hy.1
    have hKW : K ≤ W := fun k hk => ⟨hKstarQ hk, fun x hx => hx.2 k hk⟩
    have hQ0W : Q0 ≤ W := fun z hz => ⟨hQ0Q hz, fun x hx => by
      have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 (hHle hx)
      rw [commutatorElement_def]
      exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 z).mp hz) (Q0.inv_mem hz)⟩
    have hQ0ltW : Q0 < W := lt_of_le_of_ne hQ0W (fun heq => hKstarNotQ0 (le_of_le_of_eq hKW heq.symm))
    -- `W` is `M`-normal (from the `M`-invariance of `H`); the deep chief-factor step.
    have hWnorm : (W.subgroupOf L).Normal := by
      -- `L` normalizes `M_σ = O_{σ(L)}(L)`.
      have hLnormMσ : L ≤ Subgroup.normalizer
          ((OddOrder.BG.Ch3.S10.Msigma L : Subgroup G) : Set G) :=
        OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma L) L
      -- `hDcomm`: `⁅D, D⁆` centralizes the chief factor `Q̄` (chief-factor engine).
      obtain ⟨_, _, hDcomm, _⟩ :=
        chiefFactor_engine_of_inputs hG hL hP1 hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ hKsne
          hKMσdisj hcopKMσ hDq' hDMσ hKnormD hQDdisj hDne hQ0def hMNQ0 hKstarNotQ0 hQ0ltQ hmin
      -- **(1) `M_σ ≤ N(H)`.**  `M_σ' = ⁅M_σ, M_σ⁆ ⊆ Q ⊔ ⁅D, D⁆ ⊆ H ⊆ M_σ`, so `H ⊴ M_σ`
      -- (a subgroup between `M_σ'` and `M_σ` is `M_σ`-normal).  `Q`, `⁅D, D⁆` centralize `K̄ ⊆ Q̄`.
      have hQH : Q ≤ H := fun x hxQ => ⟨hQMσ hxQ, fun k hk => hQab x hxQ k (hKstarQ hk)⟩
      have hDDMσ : ⁅D, D⁆ ≤ OddOrder.BG.Ch3.S10.Msigma L := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hDMσ ha) (hDMσ hb)) (inv_mem (hDMσ ha))) (inv_mem (hDMσ hb))
      have hDDH : ⁅D, D⁆ ≤ H := fun g hg => ⟨hDDMσ hg, fun k hk => hDcomm g hg k (hKstarQ hk)⟩
      have hsup : Q ⊔ D = OddOrder.BG.Ch3.S10.Msigma L := by
        have h := congrArg (Subgroup.map (OddOrder.BG.Ch3.S10.Msigma L).subtype) hcomplD.sup_eq_top
        rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hQMσ, inf_eq_left.mpr hDMσ, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
      have hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσL.trans hMnormQ)
      have hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma L) ≤ Q ⊔ ⁅D, D⁆ := by
        have hle := OddOrder.BG.Ch3.S13.derivedInG_le_sup_of_normal hQMσ hDMσ hsup hQnMσ
        rwa [show derivedInG D = ⁅D, D⁆ from Subgroup.map_subtype_commutator D] at hle
      have hMσ'H : derivedInG (OddOrder.BG.Ch3.S10.Msigma L) ≤ H :=
        hsigmaprime.trans (sup_le hQH hDDH)
      have hHMσ' : ⁅H, OddOrder.BG.Ch3.S10.Msigma L⁆ ≤ H := by
        refine (Subgroup.commutator_mono hHle le_rfl).trans ?_
        rw [← show derivedInG (OddOrder.BG.Ch3.S10.Msigma L) =
          ⁅OddOrder.BG.Ch3.S10.Msigma L, OddOrder.BG.Ch3.S10.Msigma L⁆ from
          Subgroup.map_subtype_commutator _]
        exact hMσ'H
      have hMσN : OddOrder.BG.Ch3.S10.Msigma L ≤ Subgroup.normalizer (H : Set G) :=
        OddOrder.Isaacs.Ch04.commutator_le_iff_le_normalizer.mp hHMσ'
      -- **(2) `Ks ≤ N(H)`.**  `Ks` centralizes `K` (`K ⊆ C(Ks)`, so `s⁻¹ k s = k`), normalizes
      -- `M_σ` and `Q₀`; hence conjugation by `Ks` fixes the defining condition of `H`.
      have hKsCentK : ∀ s ∈ Ks, ∀ k ∈ K, s * k = k * s := fun s hs k hk =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKdefL ▸ hk)).2) s hs
      have hconjH_Ks : ∀ s ∈ Ks, ∀ x, x ∈ H → s * x * s⁻¹ ∈ H := by
        intro s hs x hx
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hLnormMσ (hKsL hs)) x).mp hx.1, fun k hk => ?_⟩
        have hskk : s⁻¹ * k * s = k := by rw [mul_assoc, ← hKsCentK s hs k hk]; group
        have hgen : ⁅s * x * s⁻¹, k⁆ = s * ⁅x, s⁻¹ * k * s⁆ * s⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [hgen, hskk]
        exact (Subgroup.mem_normalizer_iff.mp (hMNQ0 (hKsL hs)) ⁅x, k⁆).mp (hx.2 k hk)
      have hKsN : Ks ≤ Subgroup.normalizer (H : Set G) := by
        intro s hs
        rw [Subgroup.mem_normalizer_iff]
        refine fun x => ⟨fun hx => hconjH_Ks s hs x hx, fun hx => ?_⟩
        have hconj := hconjH_Ks s⁻¹ (Ks.inv_mem hs) (s * x * s⁻¹) hx
        have hsimp : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
        rwa [hsimp] at hconj
      -- `L = M_σ ⊔ Ks` (complement), so `L ≤ N(H)`.
      have hLsup : OddOrder.BG.Ch3.S10.Msigma L ⊔ Ks = L := by
        have h := congrArg (Subgroup.map L.subtype) hcomplMσ.sup_eq_top
        rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hMσL, inf_eq_left.mpr hKsL, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
      have hHnorm : L ≤ Subgroup.normalizer (H : Set G) := by
        rw [← hLsup]; exact sup_le hMσN hKsN
      -- **`W` is `L`-normal** from the `L`-invariance of `H`, `Q`, `Q₀`
      -- (conjugation identity `⁅x, g y g⁻¹⁆ = g ⁅g⁻¹ x g, y⁆ g⁻¹`).
      have hconjW : ∀ g ∈ L, ∀ y, y ∈ W → g * y * g⁻¹ ∈ W := by
        intro g hg y hy
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormQ hg) y).mp hy.1, fun x hxH => ?_⟩
        have hxconj : g⁻¹ * x * g ∈ H := by
          have h := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (H : Set G)).inv_mem (hHnorm hg)) x).mp hxH
          simpa only [inv_inv] using h
        have hgen : ⁅x, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, y⁆ * g⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [hgen]
        exact (Subgroup.mem_normalizer_iff.mp (hMNQ0 hg) ⁅g⁻¹ * x * g, y⁆).mp
          (hy.2 (g⁻¹ * x * g) hxconj)
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hWle.trans hQL)).mpr ?_
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      refine fun y => ⟨fun hy => hconjW g hg y hy, fun hy => ?_⟩
      have hconj := hconjW g⁻¹ (L.inv_mem hg) (g * y * g⁻¹) hy
      have hsimp : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rwa [hsimp] at hconj
    have hQW : Q ≤ W := hmin W hQ0ltW hWle hWnorm
    intro x hxMs hxK y hyQ
    exact (hQW hyQ).2 x ⟨hxMs, hxK⟩
  -- `A ⊆ F(L)`: each `a ∈ A` is in `M_σ`, centralizes `K̄` (trivially, `A ⊆ C(K)`), hence by the
  -- lifting centralizes `Q̄`, hence lies in `F(L)` (`hsecFit`).
  intro a ha
  have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma L := hAMσ ha
  refine hsecFit a haMσ (hLift a haMσ (fun k hk => ?_))
  have hcomm : a * k = k * a := ((Subgroup.mem_centralizer_iff.mp (hACK ha)) k hk).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
  exact Q0.one_mem

/-- **BG Theorem 12.15 / `Ptype_structure` + `Fcore_structure` `sylQ`/`sAFL`/`uniqQ` bundle**
(Coq `tau2_P2type_signalizer`, BGsection15.v:1315--1333): for a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)` (`|K| = q` prime, `q ∈ σ(L)`), and a rank-2 elementary abelian
`A ≤ L_σ` that is a `q₁`-group (`q₁` prime), one has: (a) `A ≤ F(L)` (Coq `sAFL`, line 1319);
(b) `Q = O_q(L)` is a Sylow-`q` of `L` (Coq `sylQ`, line 1319); (c) `Q ∈ 𝒰` (Coq `uniqQ`, line 1330).

⚠ **This is a genuinely unformalized §12/§15 keystone of BG Theorem 15.8** (`tau2_transfer_constraint`).
It bundles the three "pre-`def_q1`" facts Coq extracts from `Ptype_structure`/`Fcore_structure`
before proving `q₁ = q`:
* `sAFL`/`sylQ` (line 1319) — in the nilpotent `L_F = L_σ` case, `A ⊆ L_σ = L_F ⊆ F(L)` and
  `Q = O_q(L)` is a Sylow via `Fcore_pcore_Sylow`; in the non-nilpotent case, both flow through
  `Fcore_structure` (= Theorem 15.2), whose repo form (`mf_ne_msigma_typeP1_structure`) does not
  expose the Sylow witness / `A ⊆ F(L)`.
* `uniqQ` (line 1330) — the Sylow-uniqueness clause of Coq `Ptype_structure`
  (`[_ _ _ [_ uniqQ _] _]`), *not* among the six conjuncts of the repo `typeP_structure`.  The
  repo's only `IsUniquelyMaximal` route (`S12.nonabelian_pgroup_isUniquelyMaximal`) needs `Q`
  nonabelian, which itself depends on `def_q1` ⟹ this lemma: **circular**.

All three feed *only* `def_q1` (`A ≤ C(Q)` via `F(L)` nilpotent + `Q, A ⊆ F(L)` + coprimality), so
they are bundled here.  The statement is **sound and non-vacuous** — each conjunct is a genuine
consequence of Coq `Ptype_structure`/`Fcore_structure`. (issue 9017 update #12.) -/
theorem typeP_partner_sylow_uniquelyMaximal_bundle [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K A : Subgroup G} {q q1 : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπ : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hq1prime : q1.Prime) (hA : A ∈ elemAbelianOfRank G q1 2)
    (hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma L)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) :
    A ≤ fittingInAmbient L ∧
      (∃ P : Sylow q ↥L, opiCoreInG ({q} : Set ℕ) L = (P : Subgroup ↥L).map L.subtype) ∧
      IsUniquelyMaximal (opiCoreInG ({q} : Set ℕ) L) := by
  classical
  have hQidx : ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index :=
    opiCore_index_coprime_of_typeP hG hL hP hKsL hKs hKdefL hqπ hqσ
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQMσ : opiCoreInG ({q} : Set ℕ) L ≤ OddOrder.BG.Ch3.S10.Msigma L :=
    OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQL : opiCoreInG ({q} : Set ℕ) L ≤ L := hQMσ.trans hMσL
  have hMnormQ : L ≤ Subgroup.normalizer ((opiCoreInG ({q} : Set ℕ) L : Subgroup G) : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥(opiCoreInG ({q} : Set ℕ) L) := isPGroup_opiCoreInG_singleton L
  refine ⟨?_, exists_sylow_eq_opiCore rfl hQL hMnormQ hQpg hQidx,
    opiCore_isUniquelyMaximal_of_isSylow hG hL hP hKsL hKs hKdefL hqπ hqσ hQidx⟩
  -- `sAFL`: `A ⊆ F(L)`, by cases on nilpotency of `L_σ`.
  by_cases hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L)
  · -- nilpotent: `A ≤ L_σ ≤ M_F ≤ F(L)`.
    exact hAMσ.trans ((Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hL hnil).trans
      (maxNilpotentNormalHall_le_fittingInG L))
  · -- non-nilpotent: type-`P₁`; the isolated chief-factor lemma.
    have hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L := fun heq =>
      hnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mp heq)
    exact A_le_fittingInAmbient_of_typeP1_nonnil hG hL hP hKsL hKs hKdefL hne hA hAMσ hACK

/-- **BG `Ptype_structure` "not-`P₁` ⟹ `q ∈ β`" clause** (Coq `tau2_P2type_signalizer` `P1maxL`,
BGsection15.v:1342--1344): a type-`P` maximal `L` with `κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`
(`|K| = q` prime), and `q ∉ β(L)` is type-`P₁`.

⚠ **Second genuinely unformalized keystone of BG Theorem 15.8.**  Coq derives `L ∈ 𝓜_'P1` by
`contraR b'q => notP1maxL; Ptype_structure PmaxL hallKs [q ∈ β(L)]` — i.e. the *last* clause of
Coq `Ptype_structure` says a *not*-type-`P₁` type-`P` maximal has its `κ`-prime `q` ideal
(`q ∈ β`).  The repo `typeP_structure` (S14) does **not** expose this "not-`P₁` ⟹ `q ∈ β`"
implication, and it cannot be recovered from the six conjuncts it has.  Needed to obtain
`M*′ = M*_σ` (`typeP1_msigma_eq_derivedInG`, type-`P₁` only) for the `K ⊆ (M*_σ)′` input of
Step 4.  Sound: it is exactly the contrapositive of Coq `Ptype_structure`'s final component.
(issue 9017 update #12.) -/
theorem typeP_isTypeP1_of_not_mem_beta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hKcard : Nat.card ↥K = q)
    (hqβ : q ∉ OddOrder.BG.Ch3.S10.beta L) :
    S14.IsTypeP1 L := by
  classical
  haveI : IsSolvable ↥L := hG.solvable_of_mem_maximalSubgroups hL
  -- `q ∈ σ(L)`: `K = L_σ ⊓ C(Ks) ≤ L_σ`, `|K| = q` prime, and `L_σ` is a `σ(L)`-group.
  have hKMσ : K ≤ OddOrder.BG.Ch3.S10.Msigma L := by rw [hKdefL]; exact inf_le_left
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L := by
    have hqdvd : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) := by
      rw [← hKcard]; exact Subgroup.card_dvd_of_le hKMσ
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hqdvd, Nat.card_pos.ne'⟩)
  -- Type-`P` splits as `P₁ ∨ P₂`; rule out `P₂`, which (Coq `Ptype_structure` final clause,
  -- repo `typeP_structure` conjunct 5) forces `σ(L) = β(L)`, so `q ∈ σ(L) = β(L)` — contradiction.
  rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
  · exact hP1
  · exfalso
    -- a `(κ(L) ∪ σ(L))'`-Hall `U` of the solvable `L` (Hall's theorem), lifted to `U'.map ≤ L`.
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥L)
      ((S14.kappa L ∪ OddOrder.BG.Ch3.S10.sigma L)ᶜ)
    have hUeq : (U'.map L.subtype).subgroupOf L = U' :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((S14.kappa L ∪ OddOrder.BG.Ch3.S10.sigma L)ᶜ)
        ((U'.map L.subtype).subgroupOf L) := by rw [hUeq]; exact hU'
    obtain ⟨hσβ, _⟩ := (S14.typeP_structure hG hL hP hKsL hKs hKdefL hU).2.2.2.2.1 hP2
    exact hqβ (hσβ ▸ hqσ)

/-- **BG Theorem 15.8** (mmd L4264; Feit--Thompson 1991, `tau2_P2type_signalizer`,
BGsection15.v:1262): in the Corollary 14.12 signalizer setup — a type-`P₂` maximal `M` with
`κ`-complement `K` (a Hall `κ(M)`-subgroup), `U` the abelian Hall `(κ(M)∪σ(M))'`-factor
(Proposition 14.2(a)), `M* ∈ 𝓜(C_G(K))`, `R` a Sylow `r`-subgroup of `U`, and `H ∈ 𝓜(N_G(R))` the
signalizer neighbour — nonempty `τ₂(H)` forces `q := |K|` prime, `τ₂(H) = {q}`, and `τ₂(M) = ∅`.

**Signature correction (2026-07-06, Lane b, authorized).**  The previous scaffold hypothesized
only `(τ₂ H).Nonempty` with **no witness tying `H` to `M`**, under which the conclusion
`τ₂ H = {|K|}` is *not derivable* (an arbitrary maximal `H` with `τ₂(H) ≠ ∅` need not have
`|K| ∈ τ₂(H)`).  The hypotheses are now the genuine Coq `tau2_P2type_signalizer` ones:
`kappa_complement M U K` (unbundled as `hK`/`hU`/`hUM`/`hKM`/`hUab`/`hKNU`, matching
`typeP2_neighbor_is_typeF`), `M* ∈ 𝓜(C_G(K))` (`hMstar`), `r`-Sylow `R ≤ U` (`hr`/`hRU`/`hR`), and
crucially **`H ∈ 𝓜(N_G(R))`** (`hH`) — the missing link making `H` the Cor 14.12 signalizer
neighbour.  `tau2_transfer_constraint` has **zero code consumers** (only docstrings/AxiomsCheck
comments cite it), so the signature change breaks nothing downstream.

**Prime-restricted form (2026-07-06 #6, matching the `S12_Theorem127`/`127d` convention).**  The
repo's `tau2 M := {p | p ∉ σ M ∧ pRank ↥M p = 2}` is `ℕ`-valued, not prime-restricted: a
*composite* odd `p` (e.g. `p = 15`, `A = C₃²×C₅²`, `|A| = 15²`, `pRank = 2` since
`IsElementaryAbelian 15 A`) can lie in `tau2 M` abstractly.  So the literal `tau2 M = ∅` /
`tau2 H = {q}` over-state Coq (whose `\tau2` is implicitly a set of *primes*) and are unprovable by
the `ℰ²`-argument (which needs `Fact p.Prime`).  So the hypothesis and both `tau2` conclusions
are prime-restricted: `∃ p prime ∈ τ₂(H)`; `∀ p prime, p ∉ τ₂(M)`; and `q ∈ τ₂(H)` with every
prime of `τ₂(H)` equal to `q`.  These are faithful to Coq `~~ \tau2(H)^'.-group H` /
`\tau2(M)^'.-group M` / `\tau2(H) =i q`, and sufficient downstream
(`fittingInAmbient_eq_Msigma_of_..._tau2_empty` kills only `Y.primeFactors`, which are primes).
The `ℕ`-valued `tau2` def is a latent shared-infra issue flagged in issue 9017.

Proof spine (Coq `tau2_P2type_signalizer`): pick `q₁ ∈ τ₂(H)`; extract `A ∈ ℰ²_{q₁}(D)` for a
`σ(H)'`-Hall `D ∋ K` of `H` (Cor 14.12 `hallD`, Thm 12.7 `exists_elemAb_rank_two_le_E_of_tau2`);
`A ⊆ C(K)` (Cor 14.12 `sKFD`: `K ⊆ F(D)`, `A ⊴ D`, `F(D)` abelian), so `A ⊆ C(K) ⊆ M*` (Prop
14.2(d)); `q₁ ∉ β(G)` (Uniqueness / Lemma 12.1(g)); `M*` type-`P₁`, `M*_σ` nilpotent; `q₁ = q`;
`Q = O_q(M*)` nonabelian (Thm 12.13 `nonabelian_pgroup_isUniquelyMaximal`) ⟹ `X = C_A(H_σ)` has
`|X| = q` and `τ₂(H) = {q}` (Thm 12.7 `nonabelian_tau2` = `tau2_singleton_of_nonabelianSylow`);
finally `X ≠ K`, `C_G(U) ⊄ M`, and the `τ₂(M)`-Sylow argument give `τ₂(M) = ∅`.

⚠ **Proof status (2026-07-07, issue 9017 更新 #7):** the corrected statement is sound and matches
Coq exactly.  Landed sorry-free, in document order: Phase A (Coq `cKA`) =
`exists_rank2_elemAb_le_centralizer_kappa_of_tau2`; Phase B foundation =
`typeP2_partner_structure_of_mem`; Step 1 = `partner_kappaHall_le_Msigma_of_isTypeP2`; Step 2 =
`mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa`; Step 3 (nilpotent case) =
`exists_sylow_eq_opiCore_of_mem_sigma_of_msigma_nilpotent`; **Step 4** (Coq `not_cQQ`, `Q = O_q(M*)`
nonabelian) = `partner_opiCore_nonabelian` (focal Lemma 6.5(a) inside `↥M*_σ`); **Step 5** (`Q ∈ 𝒰`)
= `S12.nonabelian_pgroup_isUniquelyMaximal` (a nonabelian Sylow-`q` of `G` over `Q`); **Step 6**
`def_q1` centralization (Coq `sub_nilpotent_cent2`) = `le_centralizer_opiCore_of_msigma_nilpotent`
+ engine `eq_of_uniquelyMaximal_centralized_by_rank2_le`; the `τ₂(H) = {q}` singleton =
`S12.tau2_singleton_of_nonabelianSylow`; Phase D core = `centralizer_kappaCompl_le_of_mem_tau2` +
`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le` (given the escape witness `C_G(U) ⊄ M`).

⚠ **Assembly landed: `tau2_transfer_constraint` is sorry-free** (2026-07-07, issue 9017 更新 #12),
citing **three** precisely-isolated genuinely-gated keystones (the brief's premise that only `uniqQ`
gates was too optimistic; three clauses of Coq `Ptype_structure`/`Fcore_structure`/`P2type_signalizer`
are missing from the repo's §14 API).  The full Coq spine is built inline; dependency graph
(verified non-circular): **Keystone A** `typeP_partner_sylow_uniquelyMaximal_bundle`
(Coq `sAFL`+`sylQ`+`uniqQ`) → `def_q1` (`F(L)` nilpotent via
`le_centralizer_opiCore_of_fittingInAmbient_nilpotent` — *not* `L_σ`-nilpotent, so no circularity —
+ `eq_of_uniquelyMaximal_centralized_by_rank2_le`) → `b'q` (`q ∉ β(M*)`, from
`isMaximalElementaryAbelian_of_mem_tau2`'s `¬ idealPrime` + `mem_beta_iff`) → **Keystone B**
`typeP_isTypeP1_of_not_mem_beta` (Coq `P1maxL`) → `nilLs` (`M*_σ` nilpotent, via the *contrapositive*
of `mf_ne_msigma_typeP1_structure`'s `q ∈ β(M*)` conjunct) → `sKLs'` (`K ⊆ (M*_σ)′`,
`typeP1_msigma_eq_derivedInG` + `Msigma_inf_centralizer_le_derivedDerived`) → Step 4 `not_cQQ`
(`partner_opiCore_nonabelian`) → `oX`/singleton (`tau2_singleton_of_nonabelianSylow`) → escape
witness `C_G(U) ⊄ M` (**inline**, Coq `not_sXM`/`not_sCUM`: `X = A ⊓ C(H_σ)`, `|X| = q`, `X ≠ K`
via **Keystone C** `signalizer_msigma_sup_inf_partner_eq` = Coq's `H = H_σ ⋊ (H∩M*)`, `X ⊄ M` via
`κ`-Hall maximality `IsHallSubgroup.card_dvd_of_isPiGroup`, `X ⊆ C(U)` via `U ⊆ H_σ`) → Phase D
(`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`).

✅ **All three keystones A/B/C are now landed sorry-free** (Keystone C/B in earlier commits;
**Keystone A** `A_le_fittingInAmbient_of_typeP1_nonnil` (Coq `Fcore_structure` eq3 minimality
lifting) landed 2026-07-07, issue 9017 更新 #18).  Hence `tau2_transfer_constraint` is **fully
sorry-free**: `#print axioms tau2_transfer_constraint = [propext, Classical.choice, Quot.sound]`. -/
theorem tau2_transfer_constraint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M Mstar U K R H : Subgroup G} {r : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)))
    (hr : r ∈ S14.piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)))
    (hHtau : ∃ p : ℕ, p.Prime ∧ p ∈ tau2 H) :
    (∀ p : ℕ, p.Prime → p ∉ tau2 M) ∧
      ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧ q ∈ tau2 H ∧
        ∀ p : ℕ, p.Prime → p ∈ tau2 H → p = q := by
  classical
  -- **Setup.**  `L := Mstar` (Coq `L`).  `q := |K|` prime (Theorem 14.7(f)).
  have hMstarmax : Mstar ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMstar).1
  have hCKMstar : Subgroup.centralizer (K : Set G) ≤ Mstar :=
    (mem_maximalSubgroupsContaining.mp hMstar).2
  obtain ⟨q, hqprime, hKcard⟩ := card_kappaHall_prime_of_isTypeP2 hG hM hP2 hKM hK
  haveI : Fact q.Prime := ⟨hqprime⟩
  -- Corollary 14.12 signalizer neighbour: `H` type-`F`, `U ≤ H_σ`, and the `σ(H)'`-Hall
  -- `E`-setup (Coq `D`) with `K ≤ E`, `K ≤ F(E)`.
  obtain ⟨_hHF, hUHs, _hMHUK, _hHNU, E, E₁, E₂, E₃, hEsetup, _hKE, hKFE⟩ :=
    S14.typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  have hHmax : H ∈ maximalSubgroups G := hEsetup.mem_maximal
  -- Pick a prime `q₁ ∈ τ₂(H)` (Coq `q1`).
  obtain ⟨q1, hq1prime, hq1⟩ := hHtau
  haveI : Fact q1.Prime := ⟨hq1prime⟩
  -- **Phase A** (Coq `cKA`, `sAL`): a rank-2 `A ∈ ℰ²_{q₁}(E)` with `A ≤ C(K)`, hence `A ≤ M*`.
  obtain ⟨A, hA_elem, hAE, hACK⟩ :=
    exists_rank2_elemAb_le_centralizer_kappa_of_tau2 hG hEsetup hKFE hq1prime hq1
  have hAMstar : A ≤ Mstar := hACK.trans hCKMstar
  have hAH : A ≤ H := hAE.trans hEsetup.E_le
  -- **Phase B** partner structure (Coq `Ptype_embedding`): `M*` type-`P`, `κ(M*)`-Hall
  -- `Ks := M_σ ⊓ C(K)`, and `K = M*_σ ⊓ C(Ks)` (Coq `defK`).
  set Ks : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKsdef
  obtain ⟨hMstP, hKsHall, hKeq, hKsMstar⟩ :=
    typeP2_partner_structure_of_mem hG hM hP2 hKM hK hMstar
  -- Step 1 (Coq `sKLs`, `sLq`): `K ≤ M*_σ` and `q ∈ σ(M*)`.
  obtain ⟨hKMσstar, hqσfun⟩ := partner_kappaHall_le_Msigma_of_isTypeP2 hG hM hP2 hKM hK hMstar
  have hqσL : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar := hqσfun q hqprime hKcard
  -- Step 2 (Coq `sLq1`, `sALs`): `q₁ ∈ σ(M*)` and `A ≤ M*_σ`.
  obtain ⟨hq1σL, hAMσstar⟩ :=
    mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa hG hMstarmax hqprime hKcard hqσL
      hq1prime hA_elem hACK hAMstar
  -- `q ∈ π(K)` (`|K| = q` prime), used by both keystones.
  have hqπK : q ∈ S14.piSet K := by
    rw [S14.piSet, Set.mem_setOf_eq, hKcard]
    exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_refl q, hqprime.ne_zero⟩
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) Mstar with hQdef
  have hQMσstar : Q ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσL
  have hMnormQ : Mstar ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ Mstar
  -- **`sAFL` + `sylQ` + `uniqQ`** (Keystone A): `A ≤ F(M*)`, `Q = O_q(M*)` a Sylow of `M*`, `Q ∈ 𝒰`.
  obtain ⟨hAFL, ⟨P, hPQ⟩, hQU⟩ :=
    typeP_partner_sylow_uniquelyMaximal_bundle hG hMstarmax hMstP hKsMstar hKsHall hKeq hqπK hqσL
      hq1prime hA_elem hAMσstar hACK
  -- **`def_q1`** (Coq lines 1329--1338): `q₁ = q`.  If `q₁ ≠ q`, `A ⊆ C(Q)` (both in the nilpotent
  -- `F(M*)`, coprime) makes `H = M*` (uniqueness engine), contradicting `H ≠ M*`.
  have hneqHL : H ≠ Mstar := fun hHL => tau2_subset_sigma_compl Mstar (hHL ▸ hq1) hq1σL
  have hdef_q1 : q1 = q := by
    by_contra hq1ne
    -- `A ⊆ C(Q)` via `F(M*)` nilpotent (`Q, A ⊆ F(M*)`, coprime since `q₁ ≠ q`).
    have hQFL : Q ≤ fittingInAmbient Mstar := by
      rw [hQdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG Mstar
    have hApg : IsPGroup q1 ↥A := (mem_elemAbelianOfRank.mp hA_elem).1.isPGroup
    have hACQ : A ≤ Subgroup.centralizer (Q : Set G) :=
      le_centralizer_opiCore_of_fittingInAmbient_nilpotent
        (L := Mstar) (q := q) (q1 := q1) hMnormQ hQFL hAFL hq1prime hq1ne hApg
    exact hneqHL
      (eq_of_uniquelyMaximal_centralized_by_rank2_le hG hq1prime hQU hACQ hA_elem
        hHmax hAH hMstarmax hAMstar)
  -- Rewrite the `q₁`-facts to `q` (avoiding `subst`, which would eliminate the `set`-bound `q`).
  rw [hdef_q1] at hq1 hA_elem
  -- Now `A ∈ ℰ²_q`, `q ∈ τ₂(H)`.
  -- **`b'q`** (Coq line 1341): `q ∉ β(M*)`.  From `¬ idealPrime q G` (Lemma 12.1(g)) and
  -- `β(M*) ⊆ {ideal primes}`.
  have hqNotIdeal : ¬ OddOrder.BG.Ch3.S10.idealPrime q G :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG hHmax hqprime hq1 hAH hA_elem).2
  have hqNotBetaL : q ∉ OddOrder.BG.Ch3.S10.beta Mstar := fun hβ =>
    hqNotIdeal ((OddOrder.BG.Ch3.S10.mem_beta_iff Mstar q).mp hβ).2
  -- **`P1maxL`** (Keystone B): `M*` is type-`P₁`.
  have hP1L : S14.IsTypeP1 Mstar :=
    typeP_isTypeP1_of_not_mem_beta hG hMstarmax hMstP hKsMstar hKsHall hKeq hKcard hqNotBetaL
  -- **`nilLs`** (Coq line 1345): `M*_σ` nilpotent.  Contrapositive of Theorem 15.2's `q ∈ β(M*)`
  -- conjunct: `M_F ≠ M_σ ⟹ q ∈ β(M*)`, so `q ∉ β(M*) ⟹ M_F = M_σ ⟹ M_σ` nilpotent.
  have hnilLs : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    by_contra hnotnil
    have hne : MF Mstar ≠ OddOrder.BG.Ch3.S10.Msigma Mstar := fun heq =>
      hnotnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hMstarmax).mp heq)
    obtain ⟨-, _Q', _Q0', _D', _p', q', _, _hq'prime, _, hKcard', _, hq'β, _⟩ :=
      mf_ne_msigma_typeP1_structure hG hMstarmax hne hKsMstar hKsHall hKeq
    -- `q' = |Kstar_{M*}| = |K| = q` (`hKcard'` binds `Kstar := K`), so `q ∈ β(M*)` — contradiction.
    have hq'q : q' = q := by rw [← hKcard']; exact hKcard
    exact hqNotBetaL (hq'q ▸ hq'β)
  -- **`sKLs'`** (Coq line 1355): `K ≤ (M*_σ)′`.  Type-`P₁` gives `M*′ = M*_σ`, so `(M*_σ)′ = M*″`;
  -- and `K = M*_σ ⊓ C(Ks) ≤ M*″` (the `typeP_duality` complement +
  -- `Msigma_inf_..._derivedDerived`).
  have hMσderiv : OddOrder.BG.Ch3.S10.Msigma Mstar = derivedInG Mstar :=
    typeP1_msigma_eq_derivedInG hG hMstarmax hP1L hKsMstar hKsHall hKeq
  have hKderiv : K ≤ derivedInG (OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    obtain ⟨hcomplMst, hcopMst, _⟩ := typeP_duality hG hMstarmax hMstP hKsMstar hKsHall hKeq
    have hKdd : K ≤ derivedInG (derivedInG Mstar) := by
      rw [hKeq]
      exact Msigma_inf_centralizer_le_derivedDerived_of_isComplement' hG hMstarmax hcomplMst hcopMst
    rwa [hMσderiv]
  -- `K ≤ Q = O_q(M*)` (Coq `sKQ`): `K` a `q`-group in `M*`, absorbed by the normal Sylow `Q`.
  have hKMstar : K ≤ Mstar := hKMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)
  have hQsubOf : Q.subgroupOf Mstar = (P : Subgroup ↥Mstar) := by
    rw [hQdef, hPQ, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective _
  have hKQ : K ≤ Q := by
    -- `Q.subgroupOf M*` is a Hall `{q}`-subgroup (a Sylow-`q` `P` of `↥M*`), normal (Q ⊴ M*).
    haveI hQnorm : (Q.subgroupOf Mstar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (hQMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar))).mpr hMnormQ
    have hQHall : Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mstar) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := ↥(Q.subgroupOf Mstar))).mp
        (hQsubOf ▸ P.isPGroup')
      refine ⟨fun p' hp' => ?_, fun p' hp' => ?_⟩
      · -- prime factors of `|P| = q^n` are `⊆ {q}` (empty if `n = 0`).
        rw [hn] at hp'
        rw [Set.mem_singleton_iff]
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · rw [hn0, pow_zero, Nat.primeFactors_one] at hp'; exact absurd hp' (Finset.notMem_empty _)
        · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out, Finset.mem_singleton] at hp'; exact hp'
      · rw [hQsubOf] at hp'
        rw [Set.mem_singleton_iff]; rintro rfl
        exact P.not_dvd_index (Nat.mem_primeFactors.mp hp').2.1
    have hKpi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (K.subgroupOf Mstar) := fun p' hp' => by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKMstar).toEquiv, hKcard,
        (Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hp'
      exact hp' ▸ rfl
    have hsub := OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hQHall hKpi
    have hmap := Subgroup.map_mono (f := Mstar.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hKMstar,
      Subgroup.map_subgroupOf_eq_of_le (hQMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar))]
      at hmap
  -- **Step 4** (Coq `not_cQQ`): `Q` is nonabelian.
  have hnotcQQ : ¬ IsMulCommutative ↥Q :=
    partner_opiCore_nonabelian hG hMstarmax hqσL hnilLs hKcard hKQ hKderiv
  -- A nonabelian Sylow-`q` of `G`: extend `Q` (nonabelian) to a Sylow of `G`.
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton Mstar
  obtain ⟨SG, hSGle⟩ := IsPGroup.exists_le_sylow hQpg
  have hnonabG : ∃ S : Sylow q G, ¬ IsMulCommutative (S : Subgroup G) :=
    ⟨SG, fun hSGab => hnotcQQ (OddOrder.BG.Ch3.S12.isMulCommutative_of_le hSGab hSGle)⟩
  -- **`oX`** + **singleton** (Coq `nonabelian_tau2`): `X := A₀ = A ⊓ C(H_σ)`, `|X| = q`, and every
  -- prime of `τ₂(H)` equals `q` (goal conjunct 3).
  obtain ⟨hsingleton, X, hXeq, hXcard, _hXstruct, _hXesc, _hXcmpl⟩ :=
    OddOrder.BG.Ch3.S12.tau2_singleton_of_nonabelianSylow hG hEsetup hq1 hA_elem hAE hnonabG
  refine ⟨?_, q, hqprime, hKcard, hq1, hsingleton⟩
  -- **Escape witness `C_G(U) ⊄ M`** (Coq `not_sXM`/`not_sCUM`), then **Phase D**.
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hXA : X ≤ A := hXeq ▸ inf_le_left
  have hXcHs : X ≤ Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
    hXeq ▸ inf_le_right
  have hXCK : X ≤ Subgroup.centralizer (K : Set G) := hXA.trans hACK
  have hXM : X ≤ H := hXA.trans hAH
  -- `X ≠ K` (Coq `neqXK`): else `H = H_σ ⊔ (H ∩ M*) ⊆ C(K) ⊆ M*`, forcing `H = M*`.
  have hneqXK : X ≠ K := by
    intro hXK
    apply hneqHL
    -- `H_σ ⊆ C(X) = C(K)` (symmetrise `X ⊆ C(H_σ)`), so `H_σ ⊆ M*`.
    have hHsCK : OddOrder.BG.Ch3.S10.Msigma H ≤ Subgroup.centralizer (K : Set G) := by
      rw [← hXK]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hXcHs hz) y hy).symm
    -- `H = H_σ ⊔ (H ∩ M*)`, and both summands are `⊆ M*`.
    have hHsup : OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mstar) = H :=
      S14.signalizer_msigma_sup_inf_partner_eq hG hM hP2 hKM hUM hK hU hUab hMstar hr hRU hR hKNU hH
    have hHMstar : H ≤ Mstar := by
      rw [← hHsup]
      exact sup_le (hHsCK.trans hCKMstar) inf_le_right
    -- `H ≤ M*`, both coatoms ⟹ `H = M*` (else `H < M*` forces `M* = ⊤`).
    rcases eq_or_lt_of_le hHMstar with heq | hlt
    · exact heq
    · exact absurd ((mem_maximalSubgroups.mp hHmax).2 Mstar hlt)
        (mem_maximalSubgroups.mp hMstarmax).1
  -- `X ⊄ M` (Coq `not_sXM`): else `X ⊔ K` a `q`-group `⊆ M` with `K` the `κ`-Hall, so `X = K`.
  have hnotXM : ¬ (X ≤ M) := by
    intro hXMle
    apply hneqXK
    -- `X ⊔ K ⊆ M` is a `q`-group (commuting `q`-groups), and `K` is a `κ`-Hall of `M`; `q ∈ κ(M)`.
    have hqκ : q ∈ S14.kappa M :=
      hK.1 q (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
        exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_refl q, hqprime.ne_zero⟩)
    -- `K ≤ C(X)` (symmetrise `X ⊆ C(K)`); so `K ≤ N(X)`, hence `↑(X ⊔ K) = ↑X * ↑K`.
    have hKCX : K ≤ Subgroup.centralizer (X : Set G) := le_centralizer_swap hXCK
    have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
      hKCX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
    have hmulsup : (↑(X ⊔ K : Subgroup G) : Set G) = ↑X * ↑K :=
      Subgroup.coe_mul_of_right_le_normalizer_left X K hKNX
    have hXKM : (X ⊔ K : Subgroup G) ≤ M := sup_le hXMle hKM
    -- `(X ⊔ K).subgroupOf M` is a `κ(M)`-group: `|X ⊔ K| · |X ⊓ K| = |X| · |K| = q²`.
    have hXKpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) ((X ⊔ K).subgroupOf M) := by
      intro p' hp'
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXKM).toEquiv] at hp'
      have hcardprod : Nat.card ↥(X ⊔ K : Subgroup G) * Nat.card ↥(X ⊓ K : Subgroup G)
          = Nat.card ↥X * Nat.card ↥K := by
        have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X K
        rwa [← hmulsup] at h
      have hdvd : Nat.card ↥(X ⊔ K : Subgroup G) ∣ Nat.card ↥X * Nat.card ↥K :=
        ⟨_, hcardprod.symm⟩
      have hp'q : p' = q := by
        have hmem : p' ∈ (Nat.card ↥X * Nat.card ↥K).primeFactors :=
          Nat.primeFactors_mono hdvd (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') hp'
        rw [hXcard, hKcard, ← pow_two, Nat.primeFactors_prime_pow (by norm_num) hqprime,
          Finset.mem_singleton] at hmem
        exact hmem
      exact hp'q ▸ hqκ
    -- `K.subgroupOf M` is the `κ(M)`-Hall; `|X ⊔ K| ∣ |K|` and `K ≤ X ⊔ K` force `X ⊔ K = K`.
    have hcarddvd : Nat.card ↥((X ⊔ K).subgroupOf M) ∣ Nat.card ↥(K.subgroupOf M) :=
      hK.card_dvd_of_isPiGroup hXKpi
    have hcardKle : Nat.card ↥(K.subgroupOf M) ≤ Nat.card ↥((X ⊔ K).subgroupOf M) :=
      Nat.card_le_card_of_injective _
        (Subgroup.inclusion_injective (Subgroup.subgroupOf_mono M (le_sup_right)))
    have hcardeq : Nat.card ↥((X ⊔ K).subgroupOf M) = Nat.card ↥(K.subgroupOf M) :=
      Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos hcarddvd) hcardKle
    -- Transfer `hcardeq` to ambient cardinalities: `|X ⊔ K| = |K|`.
    have hcardeqamb : Nat.card ↥(X ⊔ K : Subgroup G) = Nat.card ↥K := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXKM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hcardeq
      exact hcardeq
    have hXKeqK : (X ⊔ K : Subgroup G) = K :=
      (Subgroup.eq_of_le_of_card_ge le_sup_right hcardeqamb.le).symm
    -- `X ≤ X ⊔ K = K`; equal cardinality (`|X| = q = |K|`) gives `X = K`.
    exact Subgroup.eq_of_le_of_card_ge (hXKeqK ▸ le_sup_left) (by rw [hXcard, hKcard])
  -- `C_G(U) ⊄ M` (Coq `not_sCUM`): `X ⊆ C(H_σ) ⊆ C(U)` since `U ⊆ H_σ`.
  have hesc : ¬ (Subgroup.centralizer (U : Set G) ≤ M) := by
    intro hCUM
    exact hnotXM ((hXcHs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUHs))).trans
      hCUM)
  exact not_prime_mem_tau2_of_centralizer_kappaCompl_not_le hG hM hKM hUM hU hKNU hesc

/-- **`N_G(F(M)) ≤ M` for a maximal `M`** (`F(M)` is "self-normalizing modulo `M`"): the ambient
Fitting subgroup of a maximal subgroup of a minimal simple group has normalizer contained in `M`.

Proof: `M ≤ N_G(F(M))` (any `m ∈ M` normalizes `F(M)`, `mem_normalizer_fittingInG_of_mem`).  If the
containment were strict, maximality (`IsCoatom M`) would force `N_G(F(M)) = ⊤`, i.e. `F(M) ⊴ G`; but
`F(M) ≠ ⊥` (the proper subgroup `M < ⊤` is solvable and nontrivial, so `F(M) = F(↥M).map ι ≠ ⊥` by
`fitting_ne_bot_of_solvable_nontrivial`), so a nontrivial normal `F(M) ⊴ G` in a simple `G` must be
`⊤`, whence `G ≅ ↥F(M)` is nilpotent — contradicting `¬ IsSolvable G`.  So `N_G(F(M)) = M`.

`F(M) ≠ ⊥` is proved unconditionally (no `M_σ`-nilpotency needed): `↥M` is solvable
(`solvable_of_mem_maximalSubgroups`) and nontrivial (`M ≠ ⊥`, else `M` a coatom equal to `⊥` makes
every nontrivial subgroup `⊤`, forcing `G` cyclic hence solvable), so `F(↥M) ≠ ⊥`, and the
injective `M.subtype`-image `fittingInG M` is `≠ ⊥`. -/
theorem normalizer_fittingInG_le_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) ≤ M := by
  have hco : IsCoatom M := mem_maximalSubgroups.mp hM
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `M ≠ ⊥` (a `⊥` coatom would make `G` cyclic, hence solvable).
  have hMne : M ≠ ⊥ := by
    intro hMbot
    have hco' : ∀ b : Subgroup G, ⊥ < b → b = ⊤ := by rw [← hMbot]; exact hco.2
    haveI : Nontrivial G := hG.simple.toNontrivial
    obtain ⟨g, hg1⟩ := exists_ne (1 : G)
    have hgtop : Subgroup.zpowers g = ⊤ :=
      hco' _ (bot_lt_iff_ne_bot.mpr (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h)))
    exact hG.notSolvable (isSolvable_of_comm fun a b => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top a)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top b)
      rw [← zpow_add, ← zpow_add, add_comm])
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  -- `M ≤ N_G(F(M))`.
  have hM_le_N : M ≤ Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) :=
    fun m hm => OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem hm
  rcases eq_or_lt_of_le hM_le_N with heq | hlt
  · exact heq.ge
  · exfalso
    -- Strict `⟹` `N_G(F(M)) = ⊤` (maximality), i.e. `F(M) ⊴ G`.
    have hFnorm : (fittingInAmbient M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (hco.2 _ hlt)
    -- `F(M) ≠ ⊥`: `↥M` solvable + nontrivial ⟹ `F(↥M) ≠ ⊥` ⟹ its injective image `≠ ⊥`.
    have hFne : fittingInAmbient M ≠ ⊥ := by
      have hFMne : OddOrder.Isaacs.Ch01.fitting ↥M ≠ ⊥ :=
        OddOrder.Isaacs.Ch01.fitting_ne_bot_of_solvable_nontrivial ↥M
      show OddOrder.BG.Ch2.S08.fittingInG M ≠ ⊥
      rw [OddOrder.BG.Ch2.S08.fittingInG]
      exact fun h => hFMne ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
    -- `F(M) ⊴ G`, `F(M) ≠ ⊥`, `G` simple ⟹ `F(M) = ⊤` ⟹ `G` nilpotent ⟹ solvable, contradiction.
    rcases hG.simple.eq_bot_or_eq_top_of_normal (fittingInAmbient M) hFnorm with hbot | htop
    · exact hFne hbot
    · -- `F(M) = ⊤`: `G ≃ ↥F(M)` is nilpotent, hence solvable.
      haveI : Group.IsNilpotent ↥(fittingInAmbient M) := by
        show Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG M)
        exact OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
      haveI : Group.IsNilpotent (↥(⊤ : Subgroup G)) := htop ▸ this
      haveI : Group.IsNilpotent G := Group.nilpotent_of_mulEquiv Subgroup.topEquiv
      exact hG.notSolvable IsNilpotent.to_isSolvable

/-- **`F(M)` fails to be TI once a centralizer of one of its nonidentity elements escapes `M`**
(BG Corollary 15.9, mmd L4320: *"`x ∈ M_σ ⊆ F(M)` and `C_G(x) ⊄ M`.  Hence `F(M)` is not a
`TI`-subgroup of `G`."*).  Stated in the BG-faithful generality on `x ∈ F(M)^#` (Corollary 15.9
supplies this from `x ∈ M_σ^#` once `M_σ ⊆ F(M)`, i.e. after `M ∈ 𝓜_𝓕` makes `M_σ` nilpotent).

Proof: pick `y ∈ C_G(x) ∖ M`.  As `y` centralizes `x`, `y·x·y⁻¹ = x`; so the *same* nonidentity
`x ∈ F(M)^#` witnesses an overlap `∃ a ∈ F(M)^#, y·a·y⁻¹ ∈ F(M)^#`.  Were `F(M)` a TI-subset with
normalizer-bound `N_G(F(M))`, this would force `y ∈ N_G(F(M)) ≤ M` (`normalizer_fittingInG_le_self`),
contradicting `y ∉ M`. -/
theorem not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxF : x ∈ fittingSharp M)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ¬ FittingIsTI M := by
  intro hTI
  -- `y ∈ C_G(x) ∖ M`.
  obtain ⟨y, hyC, hyM⟩ := Set.not_subset.mp hesc
  -- `y` centralizes `x`: `y·x·y⁻¹ = x` (from `x·y = y·x`).
  have hyx : y * x * y⁻¹ = x := by
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hyC) x (Set.mem_singleton x)
    rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  -- The overlap `∃ a ∈ F(M)^#, y·a·y⁻¹ ∈ F(M)^#` (both equal to `x`).
  have hoverlap : ∃ a ∈ fittingSharp M, y * a * y⁻¹ ∈ fittingSharp M :=
    ⟨x, hxF, by rw [hyx]; exact hxF⟩
  -- TI forces `y ∈ N_G(F(M)) ≤ M`, contradicting `y ∉ M`.
  exact hyM (normalizer_fittingInG_le_self hG hM (hTI y hoverlap))

/-- **The `hfratt` input of `mf_hall_centralizer_control_of_inputs`** (BG Corollary 15.3(b),
mmd L4213): when a nonidentity Hall subgroup `H ≤ M_σ` is **not** normal in `M`, the Frattini
factorization `M = N_M(H)·Q` holds for the normal `q`-subgroup `Q = O_q(M)`.

Proof (BG L4213).  `H ⋬ M` forces `M_σ` non-nilpotent (`hall_subgroupOf_normal_of_msigma_nilpotent`),
i.e. `M_F ≠ M_σ`, so `M` is type `P₁` (`isTypeP1_of_mf_ne_msigma`) and Theorem 15.2's machinery
supplies the normal `q`-subgroup `Q = O_q(M) ≤ M_σ` with `M_σ/Q` nilpotent
(`msigma_quotient_isNilpotent_of_inputs`).  Since `Q = O_q(M_σ)` (`opiCoreInG_eq_of_normal_le`),
`Q.subgroupOf M_σ = O_q(↥M_σ)` is characteristic; with `M_σ/Q` nilpotent and `H` a Hall subgroup,
`characteristic_sup_hall_of_quotient_nilpotent` makes `QH` characteristic in `M_σ`, hence (as
`M_σ ◁ M`) `QH ◁ M` (`normal_subgroupOf_of_characteristic_subgroupOf_le`).  Finally `q ∉ π(H)`
(else `Q = O_q(M_σ) ≤ H` by `normal_isPiGroup_le_isHall`, so `QH = H ◁ M`, contradiction), giving
`Q ∩ H = 1` and `gcd(|Q|, |H|) = 1`, so the Frattini argument (`frattini_factorization`) applies. -/
theorem hfratt_of_hall_not_normal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) (hHnotnorm : ¬ (H.subgroupOf M).Normal) :
    ∃ Q : Subgroup G, Q ≤ M ∧ (Q.subgroupOf M).Normal ∧ Disjoint Q H ∧
      ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hHM : H ≤ M := hHMσ.trans hMσM
  -- `M_σ` not nilpotent (else `H ⊴ M`); `M_F ≠ M_σ`.
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hHnotnorm (hall_subgroupOf_normal_of_msigma_nilpotent hHMσ hHhall hnil)
  have hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M := fun heq =>
    hMσnotnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp heq)
  -- **Setup** (= the Theorem 15.2 `Q = O_q(M)` construction, mmd L4188-4202).
  set q : ℕ := Nat.card ↥Kstar with hqdef
  have hP1 : S14.IsTypeP1 M := isTypeP1_of_mf_ne_msigma hG hM hne
  have hP : S14.IsTypeP M := hP1.1
  have hq_prime : q.Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M :=
    typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hM hP hKM hK hKstar
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M) := by rw [hMσderived]; exact hcomplDer
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [hqdef]; exact Subgroup.card_dvd_of_le hKstarMσ
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ, Nat.card_pos.ne'⟩)
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) M with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hK hcomplDer
    rwa [hMσderived]
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hM hP hKM hK hKstar
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
      ⊓ Subgroup.centralizer (K : Set G))).Prime := by rw [← hKstar]; exact hq_prime
  have hKstarQ : Kstar ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hM hKM hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKstar, ← hqdef, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    rw [e1, e2] at hcop_sub; exact hcop_sub.symm
  have hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKne : K ≠ ⊥ := by
    intro hK0
    apply hMσnotnil
    have hKstareq : Kstar = OddOrder.BG.Ch3.S10.Msigma M := by
      rw [hKstar, hK0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    have hcardMσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = q ^ 1 := by
      rw [pow_one, hqdef, hKstareq]
    exact (IsPGroup.of_card hcardMσ).isNilpotent
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton M
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M := by
    intro hQeq; exact hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  -- **`M_σ/Q` nilpotent** (Theorem 15.2 chief-factor engine).
  haveI hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  haveI hNilMσQ : Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  -- **`Q = O_q(M_σ)`**, so `Q.subgroupOf M_σ` is characteristic in `↥M_σ`.
  have hQeqMσ : opiCoreInG ({q} : Set ℕ) M = opiCoreInG ({q} : Set ℕ)
      (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hQMσ)
  haveI hQchar : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Characteristic := by
    rw [hQdef, hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
    exact Ch03.oPiCore.characteristic _ _
  -- **`QH ◁ M`**: `QH` characteristic in `M_σ`, lifted along `M_σ ◁ M`.
  have hQHchar : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)
      ⊔ H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Characteristic :=
    characteristic_sup_hall_of_quotient_nilpotent hNilMσQ hHhall
  have hQHnorm : ((Q ⊔ H).subgroupOf M).Normal := by
    refine normal_subgroupOf_of_characteristic_subgroupOf_le hMσM hMnormMσ
      (sup_le hQMσ hHMσ) ?_
    rw [Subgroup.subgroupOf_sup hQMσ hHMσ]; exact hQHchar
  -- **`q ∉ π(H)`** (else `Q ≤ H` and `QH = H ◁ M`).
  have hqnotπH : q ∉ S14.piSet H := by
    intro hqπ
    apply hHnotnorm
    have hQsub_pi : Ch03.Subgroup.IsPiGroup (S14.piSet H)
        (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv] at hr
      obtain ⟨n, hn⟩ := hQpg.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hr
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr.1 hq_prime).mp
        (hr.1.dvd_of_dvd_pow hr.2.1)
      rw [hrq]; exact hqπ
    have hQH_sub := normal_isPiGroup_le_isHall hQsub_pi hHhall
    have hQH : Q ≤ H := by
      have hmap := Subgroup.map_mono (f := (OddOrder.BG.Ch3.S10.Msigma M).subtype) hQH_sub
      rwa [Subgroup.map_subgroupOf_eq_of_le hQMσ, Subgroup.map_subgroupOf_eq_of_le hHMσ] at hmap
    exact (sup_eq_right.mpr hQH) ▸ hQHnorm
  -- **`Q ∩ H = 1`, coprime orders, Frattini.**
  have hqndvdH : ¬ q ∣ Nat.card ↥H := fun hdvd => hqnotπH (by
    rw [S14.piSet, Set.mem_setOf_eq]
    exact Nat.mem_primeFactors.mpr ⟨hq_prime, hdvd, Nat.card_pos.ne'⟩)
  have hcopQH : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥H) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]; exact ((Nat.Prime.coprime_iff_not_dvd hq_prime).mpr hqndvdH).pow_left n
  have hdisjQH : Disjoint Q H := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopQH
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hQnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  exact ⟨Q, hQM, hQnorm, hdisjQH,
    frattini_factorization hQM hHM hQnorm hQHnorm hdisjQH hcopQH ‹IsSolvable ↥M›⟩

/-- **BG Corollary 15.3** (mmd L4204): for a nonidentity Hall subgroup `H` of `M_σ`,
(a) `C_M(H) = C_{M_σ}(H)·X` with `X` a cyclic `τ₂(M)`-subgroup, and (b) any two elements of `H`
conjugate in `G` are already conjugate in `N_M(H)` (`N_M(H)`-fusion control).

*sorry-free.*  Discharges the three inputs of `mf_hall_centralizer_control_of_inputs`:
* `ha` ← `mf_centralizer_hall_decomp` (Proposition 14.2(b1)(e) + Lemma 15.1(c));
* `hconj` ← `mf_hall_conj_realized_in_M` (Theorem 14.4 + `N_G(M) = M`);
* `hfratt` ← `hfratt_of_hall_not_normal` (Theorem 15.2's normal `Q = O_q(M)` with `M_σ/Q`
  nilpotent, then the Frattini argument), with a `κ(M)`-Hall `K` produced from the trivial
  `κ`-witness `⊥` (`exists_isHallSubgroup_kappa_ge`).

The `H ≤ M_σ` hypothesis (BG: "`H` a Hall subgroup of `M_σ`") is what the inputs require;
consumers (Corollary 15.4 in `nilpotent_hall_embeds_in_msigma`, Theorem I in §16) supply it
after placing `H ≤ M_σ`. -/
theorem mf_hall_centralizer_control [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hH : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    (∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X) ∧
    (∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) →
      ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) := by
  refine mf_hall_centralizer_control_of_inputs (hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    (mf_centralizer_hall_decomp hG hM hHMσ hH hHne)
    (mf_hall_conj_realized_in_M hG (dummySigmaDecomposition G) hM hHMσ) ?_
  intro hHnotnorm
  obtain ⟨K, hKM, hK, -⟩ := exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by
    intro q hq; rw [Subgroup.card_bot] at hq; simp at hq)
  exact hfratt_of_hall_not_normal hG hM hKM hK rfl hHMσ hH hHne hHnotnorm

end OddOrder.BG.Ch4.S15

