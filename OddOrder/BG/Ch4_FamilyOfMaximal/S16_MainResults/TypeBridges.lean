import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeP1Criteria

/-!
# TAIL

Prefix-split from `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeBridges` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.BG.Ch4.S16
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]



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

This discharges two of the three conjuncts of Theorem A(8) in
`theoremA_maximal_structure_faithful`; the
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
conclusion of Theorem 15.7(a)).  This is the full conjunction
`theoremA_maximal_structure_faithful` carries
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

This is the canonical faithful form of BG Theorem A.  It includes the explicit `hKM : K ≤ M` and
`hUM : U ≤ M` that the BG setup `M = K U M_σ` carries but the bare Hall
conditions on `K.subgroupOf M` / `U.subgroupOf M` do not force, so conjuncts A(3) (`M = K U M_σ`),
A(4) (`C_U(k) = 1`), and A(8) (`U = 1`) become provable.  Every conjunct is discharged by a
standalone lemma — none gated:

* A(1) `M_σ` is `σ(M)`-Hall, A(2) `K` cyclic, A(3)-normal `M ≤ N(U M_σ)`, A(4) `C_U(k) = 1`,
  A(5) `K* ≠ 1` and `C_M(k) = K K*`, A(6) `M_F ≤ M_σ ≤ M'` — all from `theoremA_ungated_conjuncts`;
* A(3)-decomposition `M = K U M_σ` — `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`;
* A(7) `M'' ⊆ F(M)` — `derivedDerived_le_fittingInAmbient` (now ungated, issue 8012);
* A(8) `M_F ≠ M_σ ⟹ U = 1 ∧ F(M)` TI `∧ |K|` prime — `theoremA8_structure` (`U.subgroupOf M = ⊥`
  upgraded to `U = ⊥` via `hUM`).

The former bare overstatement omitted `hKM`/`hUM` and was retired after all consumers migrated;
this theorem is the sole monolithic Theorem A API. -/
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
