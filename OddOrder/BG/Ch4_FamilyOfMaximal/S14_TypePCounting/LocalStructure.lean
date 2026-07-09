import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting.Basics

/-!
# BG Lemma 14.1 / Proposition 14.2 — local structure of type-P members

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S14
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch3.S13
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## Lemma 14.1 and Proposition 14.2: local structure of type-P members -/

/-- **BG Lemma 14.1** (mmd L3811): suppose `M ∈ 𝓜` and `p ∈ π(M) - (σ(M) ∪ κ(M))`.
Let `A` be an elementary abelian `p`-subgroup of `M` of maximal rank `r_p(M)`
(realized by `A = Ω₁(S)` for `S ∈ Syl_p(M)`).  Then `|A| ≤ p²`, `C_{M_σ}(A) = 1`,
and `M_σ` is nilpotent.

BG's hypothesis `M ∉ 𝓜_{𝓟₁}` only guarantees that such a prime `p` exists; once
`p` is given (`hpπ`, `hpσ`, `hpκ`), it plays no role in the proof, so it is dropped
here.  The `A = Ω₁(S)` binding is encoded as `A ∈ ℰ_p^{r_p(M)}(M)` (the same
`Ω`-deferral used in Theorem 12.5), under which `|A| = p^{r_p(M)}`, so the
cardinality assertion `|A| ≤ p²` is the rank bound `r_p(M) ≤ 2`.

Proof: by the τ-classification `r_p(M) ∈ {1, 2}`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`
and all three assertions are Theorem 12.5(a)(d).  If `r_p(M) = 1` then
`p ∈ τ₁(M) ∪ τ₃(M)`; `C_{M_σ}(A) = 1` because `p ∉ κ(M)`, and since `A` has prime
order it then acts fixed-point-freely on `M_σ`, so `M_σ` is nilpotent by Theorem
3.7 (`isNilpotent_of_normalizing_primeOrder_fixedPointFree`). -/
theorem msigma_structure_of_notMem_sigma_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) :
    Nat.card ↥A ≤ p ^ 2 ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  have hp : p.Prime := Fact.out
  have hpM : p ∈ (Nat.card ↥M).primeFactors := hpπ
  -- Rank bounds `1 ≤ r_p(M) ≤ 2` via the §12 `E`-setup.
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hp hpM hpσ
  have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  have h2r : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
  have hcardA : Nat.card ↥A = p ^ pRank ↥M p := hA.2
  -- (1) `|A| ≤ p²` is the rank bound.
  have hbound : Nat.card ↥A ≤ p ^ 2 := by
    rw [hcardA]; exact Nat.pow_le_pow_right hp.one_le h2r
  refine ⟨hbound, ?_⟩
  have hrank12 : pRank ↥M p = 1 ∨ pRank ↥M p = 2 := by omega
  rcases hrank12 with hr1 | hr2
  · -- `r_p(M) = 1`: `p ∈ τ₁(M) ∪ τ₃(M)`, fixed-point-free action.
    have hAr1 : A ∈ elemAbelianOfRank G p 1 := by rw [← hr1]; exact hA
    have hcardp : Nat.card ↥A = p := by rw [hcardA, hr1, pow_one]
    have hpτ13 : p ∈ tau1 M ∪ tau3 M := by
      by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
      · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr1⟩)
      · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr1⟩)
    -- `C_{M_σ}(A) = 1` because `p ∉ κ(M)`.
    have hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
      by_contra hne
      exact hpκ ⟨hp, hpτ13, A, hAr1, hAM, hne⟩
    refine ⟨hC, ?_⟩
    -- `A` is commutative, hence `A ≤ C_G(A)`.
    have hAcent : A ≤ Subgroup.centralizer (A : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hA.1.comm (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A)
      exact congrArg (Subtype.val) this
    -- Hypotheses for Theorem 3.7 (`N = M_σ`, `R = A`).
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    haveI : IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ A) :=
      solvable_of_solvable_injective
        (Subgroup.inclusion_injective (sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) hAM))
    have hAnorm : A ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      hAM.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.Msigma M) A := by
      rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ A
            ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
              inf_le_inf_left _ hAcent
        _ = ⊥ := hC
    have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    have hAne : A ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hAr1
    -- `A` acts fixed-point-freely on `M_σ`: an element fixed by `r ∈ A#` would
    -- centralize `⟨r⟩ = A` and so lie in `C_{M_σ}(A) = 1`.
    have hgen : ∀ r ∈ A, r ≠ 1 → A = Subgroup.zpowers r := by
      intro r hr hr1'
      have hle : Subgroup.zpowers r ≤ A := Subgroup.zpowers_le.mpr hr
      have hcardzp : Nat.card ↥(Subgroup.zpowers r) = p := by
        have hdvd : orderOf r ∣ p := by
          rw [← hcardp, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
        rw [Nat.card_zpowers]
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
        · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
        · exact hpp
      exact (Subgroup.eq_of_le_of_card_ge hle (hcardp.trans hcardzp.symm).le).symm
    have hFPF : ∀ r ∈ A, r ≠ 1 → ∀ n ∈ OddOrder.BG.Ch3.S10.Msigma M, n ≠ 1 →
        r * n * r⁻¹ ≠ n := by
      intro r hr hr1' n hn hn1 heq
      have hcomm : Commute r n := mul_inv_eq_iff_eq_mul.mp heq
      have hAr : A = Subgroup.zpowers r := hgen r hr hr1'
      have hncent : n ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a haA
        rw [hAr, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at haA
        obtain ⟨k, rfl⟩ := haA
        exact hcomm.zpow_left k
      have hmem : n ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
        ⟨hn, hncent⟩
      rw [hC, Subgroup.mem_bot] at hmem
      exact hn1 hmem
    exact OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      hAnorm hdisj hMσne hAne ⟨p, hp, hcardp⟩ hFPF
  · -- `r_p(M) = 2`: `p ∈ τ₂(M)`; Theorem 12.5(a),(d).
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr2⟩
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by rw [← hr2]; exact hA
    have h125 := Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 hAM
    exact ⟨h125.2.2.2.1, h125.1⟩

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`: a maximal-rank elementary abelian
`p`-subgroup `A ≤ M` satisfying Lemma 14.1's hypotheses (`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`) gives
`C_{M_σ}(A) = 1` (Lemma 14.1); since `A ≤ U`, centralizer antitonicity lifts this to
`C_{M_σ}(U) ≤ C_{M_σ}(A) = 1`. -/
theorem msigma_centralizer_eq_bot_of_elemAb_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {U A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) (hAU : A ≤ U) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  obtain ⟨_, hCA, hnilp⟩ := msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA hAM
  refine ⟨?_, hnilp⟩
  rw [eq_bot_iff, ← hCA]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAU))

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`, case `E₃ = ⊥`: for `q ∈ τ₂(M)` and a
`q`-element `y' ∈ E₂#`, `Ω₁(E₂)` is a rank-two elementary abelian `q`-subgroup *of `E₂`* (not just
`E`) containing `y'`.  Same as `exists_elemAb_rank_two_le_E_mem_of_tau2` but exposes the stronger
containment `A ≤ E₂`, which the `U = E₂E₃ = E₂` reduction needs. -/
private theorem exists_elemAb_rank_two_le_E2_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E₂ ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE2, hy'A⟩

/-- **`C_{M_σ}(U) = 1`** for `U = E₂E₃` in case `τ₁` (BG Lemma 14.1 bridge).  `U` is a Hall
`(κ(M) ∪ σ(M))'`-subgroup; picking any prime `p ∈ π(U)` and a maximal-rank elementary abelian
`p`-subgroup `A ≤ U`, Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`,
and `C_{M_σ}(U) ≤ C_{M_σ}(A)`.  (In case `τ₁`, `κ(M) ∩ τ₃(M) = ∅` ensures `π(U) ∩ κ(M) = ∅`.)
This is the `C_{M_σ}(U) = 1` hypothesis Proposition 14.2(g) feeds to Theorem 3.10(a).

Proof: since `U = E₂E₃ ≠ 1`, either `E₃ ≠ 1` or `E₂ ≠ 1`.  If `E₃ ≠ 1`, a prime `p ∣ |E₃|`
lies in `τ₃(M)` (as `E₃` is Hall `τ₃(M)` of `E`) with `r_p(M) = 1`, and a cyclic `A = ⟨g⟩ ≤ E₃`
of order `p` is rank-one elementary abelian; `p ∉ κ(M)` because `κ(M) ∩ τ₃(M) = ∅`.  If `E₃ = 1`
then `U = E₂ ≠ 1`; a prime `q ∣ |E₂|` lies in `τ₂(M)` with `r_q(M) = 2`, and `A = Ω₁(E₂) ≤ E₂`
is rank-two elementary abelian; `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)` since `r_q(M) = 2 ≠ 1`.  Either way
Lemma 14.1 (via `msigma_centralizer_eq_bot_of_elemAb_le`) closes the goal. -/
theorem Msigma_centralizer_E23_eq_bot_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  by_cases hE3 : E₃ = ⊥
  · -- Case `E₃ = ⊥`: `U = E₂E₃ = E₂ ≠ ⊥`; pick `q ∈ τ₂(M)` and `A = Ω₁(E₂)` of rank two.
    have hE2 : E₂ ≠ ⊥ := by
      intro hb; exact hUne (by rw [hb, hE3, bot_sup_eq])
    have hcard2 : Nat.card ↥E₂ ≠ 1 := fun hc => hE2 (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard2
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₂) q hqdvd
    have hy'E2 : (y' : G) ∈ E₂ := y'.2
    have hy'ord : orderOf (y' : G) = q :=
      (orderOf_injective E₂.subtype E₂.subtype_injective y').trans hy'
    have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
    have hy'1 : (y' : G) ≠ 1 := by
      intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
    -- `q ∈ τ₂(M)`: `q ∣ |E₂|`, and `E₂` is Hall `τ₂(M)` of `E`.
    have hqE2 : q ∈ (Nat.card ↥E₂).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
    have hqτ2 : q ∈ tau2 M := by
      have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
      exact h.E₂_hall.1 q (hc2 ▸ hqE2)
    -- rank-two `A = Ω₁(E₂) ≤ E₂`.
    obtain ⟨A, hAmem, hAE2, _⟩ :=
      exists_elemAb_rank_two_le_E2_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
    have hAM : A ≤ M := hAE2.trans (h.E₂_le.trans h.E_le)
    have hArank : A ∈ elemAbelianOfRank G q (pRank ↥M q) := by
      rw [tau2_pRank_eq_two hqτ2]; exact hAmem
    have hpπ : q ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hq,
        hqdvd.trans (Subgroup.card_dvd_of_le (h.E₂_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hqτ2
    -- `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`: `r_q(M) = 2`, but `τ₁, τ₃` have `r = 1`.
    have hqκ : q ∉ kappa M := by
      intro hqκ
      have hr2 := tau2_pRank_eq_two hqτ2
      rcases kappa_subset_tau1_union_tau3 hqκ with hτ1 | hτ3'
      · have := tau1_pRank_eq_one hτ1; omega
      · have := tau3_pRank_eq_one hτ3'; omega
    have hAU : A ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE2.trans le_sup_left
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hqσ hqκ hArank hAM hAU
  · -- Case `E₃ ≠ ⊥`: pick `p ∈ τ₃(M)` and a cyclic rank-one `A = ⟨g⟩ ≤ E₃`.
    have hcard3 : Nat.card ↥E₃ ≠ 1 := fun hc => hE3 (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard3
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₃) p hpdvd
    have hgE3 : (g : G) ∈ E₃ := g.2
    have hgord : orderOf (g : G) = p :=
      (orderOf_injective E₃.subtype E₃.subtype_injective g).trans hg
    have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers]; exact hgord
    have hAE3 : Subgroup.zpowers (g : G) ≤ E₃ := Subgroup.zpowers_le.mpr hgE3
    have hAr1 : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
    -- `p ∈ τ₃(M)`: `p ∣ |E₃|`, and `E₃` is Hall `τ₃(M)` of `E`.
    have hpE3 : p ∈ (Nat.card ↥E₃).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpτ3 : p ∈ tau3 M := by
      have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
      exact h.E₃_hall.1 p (hc3 ▸ hpE3)
    have hAM : Subgroup.zpowers (g : G) ≤ M := hAE3.trans (h.E₃_le.trans h.E_le)
    have hArank : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [tau3_pRank_eq_one hpτ3]; exact hAr1
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le
        (h.E₃_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := tau3_subset_sigma_compl M hpτ3
    -- `p ∉ κ(M)`: `κ(M) ∩ τ₃(M) = ∅` and `p ∈ τ₃(M)`.
    have hpκ : p ∉ kappa M := fun hpκ => hτ3 ⟨p, hpκ, hpτ3⟩
    have hAU : Subgroup.zpowers (g : G) ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE3.trans le_sup_right
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hpσ hpκ hArank hAM hAU

/-- **BG Proposition 14.2(g), TI conjunct** (mmd L3850): if `σ(M) = β(M)` then `M_σ^#` is a
TI-subset of `G` with normalizer-bound `N_G(M_σ)`.  For `g` producing an overlap of `M_σ^#`
with its `g`-conjugate, either `g ∈ M ≤ N_G(M_σ)`, or `g ∉ M` and Lemma 12.17
(`Msigma_inf_conj_isBetaCompl`) makes `M_σ ∩ M_σ^g` a `β(M)′ = σ(M)′`-group; being also a
`σ(M)`-group (`≤ M_σ`) it is trivial, contradicting the nontrivial overlap.  This is the
TI clause Proposition 14.2(g) concludes from `β(M) = σ(M)`. -/
theorem isTISubset_sigmaSharp_of_sigma_eq_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M) :
    IsTISubset (sigmaSharp M)
      (Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)) := by
  intro g hov
  obtain ⟨a, haS, hgaS⟩ := hov
  simp only [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff,
    SetLike.mem_coe] at haS hgaS
  obtain ⟨haMσ, _ha1⟩ := haS
  obtain ⟨hgaMσ, hga1⟩ := hgaS
  by_cases hgM : g ∈ M
  · exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hgM
  · exfalso
    -- `g a g⁻¹ ∈ M_σ ∩ (conj g • M_σ)`, nontrivial.
    have hgaConj : g * a * g⁻¹ ∈ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using haMσ
    have hmemInf : g * a * g⁻¹ ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M :=
      Subgroup.mem_inf.mpr ⟨hgaMσ, hgaConj⟩
    have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓
        MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := fun h =>
      hga1 (Subgroup.mem_bot.mp ((Subgroup.card_eq_one.mp h) ▸ hmemInf))
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
    haveI : Fact p.Prime := ⟨hp⟩
    -- `p ∈ σ(M)` since the intersection is `≤ M_σ`.
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    -- `p ∉ β(M)` by Lemma 12.17, since the intersection is `≤ M_σ ⊓ M^g`.
    have hle : OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M :=
      inf_le_inf_left _ (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (OddOrder.BG.Ch3.S10.Msigma_le M))
    have hpβ := OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl hG hM hgM p
      (Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
    exact hpβ (hσβ ▸ hpσ)

/-- **BG Proposition 14.2(g), Frobenius core** (mmd L3850): in case `κ ⊆ τ₁` with `E₁ = K`
non-regular prime on `M_σ` and `U = E₂E₃ ≠ 1`, the type-`P₂` conclusions `σ(M) = β(M)` and
`|K|` prime hold.  `E = E₁ ⋉ U` is a Frobenius group (`isFrobeniusGroup_E_of_caseTau1`) with
`C_{M_σ}(U) = 1` and `M_σ` nilpotent (`Msigma_centralizer_E23_eq_bot_of_caseTau1`); since `E₁`
is prime on the nilpotent `M_σ`, Theorem 3.10(a) gives `|E₁|` prime.  Coprime fixed-point-free
action gives `U = [U, E₁] ≤ E'` (`le_commutator_of_coprime_inf_centralizer_eq_bot`), so `U`
is abelian (Corollary 12.10(b): `E'` abelian) and, by Lemma 12.19, `U` centralizes a Hall
`β(M)'`-subgroup `W` of `M_σ`; `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing
`σ(M) = β(M)`. -/
theorem sigma_eq_beta_and_prime_card_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
      ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q := by
  classical
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hUleE_sup : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  -- `E = E₁ ⋉ U` is Frobenius; `C_{M_σ}(U) = 1` and `M_σ` is nilpotent.
  have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h hE1ne hKstar hτ3 hUne
  obtain ⟨hCU, hMnilp⟩ := Msigma_centralizer_E23_eq_bot_of_caseTau1 hG h hτ3 hUne
  -- `M_σ ≠ ⊥`.
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := fun hb => hKstar (by rw [hb, bot_inf_eq])
  -- Coprime `|E₁|` and `|U|` (Frobenius kernel/complement).
  have hcopKU : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) := by
    have hc := (hfrob.coprime_card_kernel_complement).symm
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE_sup).toEquiv] at hc
  -- `C_U(E₁) = ⊥` (regular action of `E₁` on `U`).
  have hCUK : (E₂ ⊔ E₃ : Subgroup G) ⊓ Subgroup.centralizer (E₁ : Set G) = ⊥ := by
    obtain ⟨⟨g₀, hg₀E1⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1ne
    have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
    have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3 g₀ hg₀E1 hg₀1
    rw [fixedByElement_def] at hr
    rw [eq_bot_iff, ← hr]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀E1))
  -- **Task B**: `U = [U, E₁] ≤ E'`.
  haveI hE1solv : IsSolvable ↥E₁ :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (h.E₁_le.trans h.E_le))
  have hUleE' : (E₂ ⊔ E₃ : Subgroup G) ≤ derivedInG E := by
    have hUcomm : (E₂ ⊔ E₃ : Subgroup G) ≤ ⁅E₁, E₂ ⊔ E₃⁆ :=
      OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
        (h.E₁_le.trans (h.E23_normal hG)) hcopKU hCUK
    have hcomm_le : (⁅E₁, E₂ ⊔ E₃⁆ : Subgroup G) ≤ ⁅E, E⁆ :=
      Subgroup.commutator_mono h.E₁_le hUleE_sup
    exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator E).symm)
  -- `U` is abelian (`U ≤ E'` and `E'` is abelian by Corollary 12.10(b)).
  have hE'ab : IsMulCommutative ↥(derivedInG E) := (nilpotent_sigmaComplement_abelian hG h).2.1.2
  have hUab : ∀ a b : ↥(E₂ ⊔ E₃), (a : G) * (b : G) = (b : G) * (a : G) := fun a b =>
    congrArg Subtype.val (hE'ab.is_comm.comm ⟨a, hUleE' a.2⟩ ⟨b, hUleE' b.2⟩)
  -- `E₁` is prime on `M_σ` ⟹ the `hcond3` hypothesis of Theorem 3.10(a).
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  have hcond3 : ∀ x ∈ E₁, x ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
    intro x hx hx1
    have := hE1prime x hx hx1
    rwa [fixedByElement_def, fixedBy_def] at this
  -- `E ≤ N_G(M_σ)`, coprime `|E|` `|M_σ|`, and `M_σ ⊔ E` solvable.
  have hEMσ : E ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    h.E_le.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
  have hcopEMσ : Nat.Coprime (Nat.card ↥E) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have h1 := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rw [Nat.coprime_comm] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at h1
  haveI hsolvME : IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ E) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hMσM h.E_le))
  -- **Theorem 3.10(a)**: `|E₁|` has prime order.
  have hKprime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q :=
    OddOrder.BG.Ch1.S03.prime_card_complement_of_frobenius_conj hsolvME hUleE_sup h.E₁_le hfrob
      hUab hEMσ hMnilp hMσne hcopEMσ hCU hcond3
  -- **σ = β**: Lemma 12.19 gives `W` a Hall `β'`-subgroup of `M_σ` with `E' ≤ C_G(W)`; since
  -- `U ≤ E'` we get `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing `σ(M) = β(M)`.
  obtain ⟨W, hWMσ, hWHall, hE'centW⟩ :=
    OddOrder.BG.Ch3.S12.derivedE_centralizes_betaComplement hG h
  have hWcentU : W ≤ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (hE'centW (hUleE' hu))) w hw).symm
  have hWbot : W = ⊥ := by
    have hWle : W ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := le_inf hWMσ hWcentU
    rw [hCU] at hWle; exact le_bot_iff.mp hWle
  have hπMσβ : ∀ p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.beta M := by
    intro p hp
    have hidx : (W.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      rw [hWbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    have hmem := hWHall.2 p (hidx ▸ hp)
    simp only [Set.mem_compl_iff, not_not] at hmem
    exact hmem
  have hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M := by
    refine Set.eq_of_subset_of_subset (fun p hp => ?_) (fun p hp =>
      OddOrder.BG.Ch3.S10.alpha_subset_sigma hG h.mem_maximal
        (OddOrder.BG.Ch3.S10.beta_subset_alpha M hp))
    -- `σ ⊆ β`: `p ∈ σ ⟹ p ∣ |M_σ|` (Hall) `⟹ p ∈ β`.
    refine hπMσβ p ?_
    obtain ⟨hpπM, _⟩ := (OddOrder.BG.Ch3.S10.mem_sigma_iff M p).mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπM
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
    by_contra hndvd
    have hHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal
    have hcardM := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    have hcardeq : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    have hpM : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπM).2.1
    rw [← hcardM, hcardeq] at hpM
    have hpidx : p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
      (hpp.dvd_mul.mp hpM).resolve_left hndvd
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpidx, Subgroup.index_ne_zero_of_finite⟩) hp
  exact ⟨hσβ, hKprime⟩

/-- **BG Proposition 14.2(g), type-`P₂` ⟹ `U ≠ 1`** (mmd L3850, "`M ∈ 𝓜_{𝒫₂}`, i.e. `U ≠ 1`"):
in case `κ ⊆ τ₁` (so `κ(M) = τ₁(M)`), if `E₂E₃ = 1` then `E = E₁ = K`, hence `κ(M)` equals
`π(M) ∖ σ(M)` (every `σ(M)'`-prime of `M` divides `|E| = |E₁|` and lies in `κ` by the prime
action), so `M` is type `P₁`.  The contrapositive: `IsTypeP2 M ⟹ E₂E₃ ≠ 1`. -/
theorem E23_ne_bot_of_isTypeP2_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hP2 : IsTypeP2 M) :
    (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥ := by
  classical
  intro hUbot
  -- `E = E₁` since `E = E₁E₂E₃` and `E₂ = E₃ = ⊥`.
  have hE2bot : E₂ = ⊥ := le_bot_iff.mp (le_sup_left.trans hUbot.le)
  have hE3bot : E₃ = ⊥ := le_bot_iff.mp (le_sup_right.trans hUbot.le)
  have hEeq : E = E₁ := by
    rw [h.eq_sup hG, hE2bot, hE3bot, sup_bot_eq, sup_bot_eq]
  -- `κ(M) = π(M) ∖ σ(M)`, contradicting `IsTypeP2 M`.
  refine absurd ?_ hP2.2
  apply Set.eq_of_subset_of_subset
  · -- `κ(M) ⊆ π(M) ∖ σ(M)`.
    intro p hpκ
    obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      rcases hpτ with hp | hp
      · exact tau1_subset_sigma_compl M hp
      · exact tau3_subset_sigma_compl M hp
    exact ⟨Nat.mem_primeFactors.mpr
      ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
  · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E| = |E₁|` ⟹ `p ∈ κ`.
    intro p hp
    obtain ⟨hpπ, hpσ⟩ := hp
    obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
    have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
      rw [h.card_Msigma_mul_card_E]; exact hpdvdM
    have hpE1 : p ∈ (Nat.card ↥E₁).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpp, hEeq ▸ (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
    exact mem_kappa_of_mem_primeFactors_card_E1 hG h hE1prime hCE1 hpE1

/-- **BG Proposition 14.2(e), second clause `S ⊄ K*`** (mmd L3828, proof L3846).  In a type-`P`
`E`-setup whose `τ₁`-Hall `E₁` lies in the `κ(M)`-subgroup `K` (so `K` is a `τ₁∪τ₃`-group and
`K* = C_{M_σ}(K)`), no Sylow `q`-subgroup `S` of `M_σ` is contained in `K*`.

This is the linchpin of Corollary 15.3(a): with it one shows `C_M(H)` is a `κ(M)'`-group for every
nontrivial Hall subgroup `H` of `M_σ` (if `H ≤ K*`, a Sylow `S ≤ H ≤ K*` of `M_σ` violates this).
It strengthens — and now subsumes — `kstar_ne_msigma_aux` (`K* ≠ M_σ`).

Proof (BG L3846).  **Part A** (`ℳ(K*) ≠ {M}`): pick `p₀ ∈ π(K)` and `X ∈ ℰ_{p₀}¹(K)`; then
`C_{M_σ}(X) ⊇ K* ≠ 1`, so Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`), applied to a maximal
`Mi ⊇ N_G(X)`, gives `p₀ ∈ σ(Mi)`; as `p₀ ∈ τ₁∪τ₃ ⊆ σ(M)'` we get `Mi ≠ M`, and
`K* ≤ C_G(X) ≤ N_G(X) ≤ Mi`.  **Part B**: if `S ≤ K*`, take `X_S ∈ ℰ_q¹(S) ⊆ ℰ_q¹(K*)`; since
`E₁ ≤ K`, `X_S ≤ M_σ ⊓ C(E₁)`, so Lemma 13.6 (`maximalContaining_eq_singleton_of_E1`, `P = E₁`)
gives `ℳ(S) = {M}`; but `S ≤ K* ≤ Mi` forces `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, a contradiction. -/
theorem typeP_sylow_not_le_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  classical
  intro hSK
  -- ## Part A: `ℳ(K*) ≠ {M}` — some maximal `Mi ≠ M` contains `K*`.
  obtain ⟨p₀, hp₀, hp₀dvd⟩ :=
    (Nat.card ↥K).exists_prime_and_dvd (fun hc => hKne (Subgroup.card_eq_one.mp hc))
  haveI : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀ hp₀dvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p₀ := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p₀ 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXM : Subgroup.zpowers (w : G) ≤ M := (hXK.trans hKE).trans h.E_le
  have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M :=
    hKpi13 p₀ (Nat.mem_primeFactors.mpr ⟨hp₀, hp₀dvd, Nat.card_pos.ne'⟩)
  have hKstar_le_inf : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) := by
    rw [hKstar]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≠ ⊥ :=
    fun hbot => hKstar_ne (le_bot_iff.mp (hKstar_le_inf.trans hbot.le))
  have hNlt : Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hXM hXne
  obtain ⟨Mi, hMico, hNMi⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G))).resolve_left
      hNlt.ne
  have hMimem : Mi ∈ maximalSubgroupsContaining
      (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G)) := ⟨hMico, hNMi⟩
  have hp₀σMi : p₀ ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    mem_sigma_of_tau1_tau3_centralize hG h hp₀τ13 hXelem ((hXK.trans hKE)) hCX hMimem
  have hMineM : Mi ≠ M := by
    intro hMieq
    have hp₀σM : p₀ ∈ OddOrder.BG.Ch3.S10.sigma M := hMieq ▸ hp₀σMi
    have hp₀nσM : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M :=
      hp₀τ13.elim (fun hh => tau1_subset_sigma_compl M hh) (fun hh => tau3_subset_sigma_compl M hh)
    exact hp₀nσM hp₀σM
  have hKstar_le_Mi : Kstar ≤ Mi :=
    ((hKstar_le_inf.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)).trans hNMi
  -- ## Part B: `S ≤ K*` contradicts `ℳ(S) = {M}` (Lemma 13.6).
  -- `q ∣ |S|` (nontrivial `q`-group), so pick `X_S ∈ ℰ_q¹(S)`.
  have hqdvdS : q ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSq
    rw [hk]
    refine dvd_pow_self q ?_
    rintro rfl
    rw [pow_zero] at hk
    exact hSne (Subgroup.card_eq_one.mp hk)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' q hqdvdS
  have hXScard : Nat.card ↥(Subgroup.zpowers (v : G)) = q := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ S.subtype_injective v).trans hv
  have hXSelem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXScard, by rw [hXScard, pow_one]⟩
  have hXS_le_S : Subgroup.zpowers (v : G) ≤ S := Subgroup.zpowers_le.mpr v.2
  have hXS_le_Kstar : Subgroup.zpowers (v : G) ≤ Kstar := hXS_le_S.trans hSK
  -- `X_S ≤ M_σ ⊓ C(E₁)` (`X_S ≤ K* = M_σ ⊓ C(K) ≤ M_σ ⊓ C(E₁)`, since `E₁ ≤ K`).
  have hXC : Subgroup.zpowers (v : G) ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (E₁ : Set G) := by
    have h1 : Subgroup.zpowers (v : G) ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := hKstar ▸ hXS_le_Kstar
    exact le_inf (h1.trans inf_le_left)
      ((h1.trans inf_le_right).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE1K)))
  -- `q ∈ σ(M)` (`X_S ≤ M_σ`).
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hqdvdS.trans (Subgroup.card_dvd_of_le hSle), Nat.card_pos.ne'⟩)
  -- Lemma 13.6: `ℳ(S) = {M}`.
  have hMS : maximalSubgroupsContaining S = {M} :=
    (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hXSelem hXC hSle hSq hSmax).2
  -- `S ≤ K* ≤ Mi`, so `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, contradicting `Mi ≠ M`.
  have hMiS : Mi ∈ maximalSubgroupsContaining S := ⟨hMico, hSK.trans hKstar_le_Mi⟩
  rw [hMS, Set.mem_singleton_iff] at hMiS
  exact hMineM hMiS

/-- **BG Proposition 14.2(e), `K* ⊊ M_σ` form** (mmd L3846).  Immediate corollary of
`typeP_sylow_not_le_kstar`: a Sylow `S` of `M_σ` cannot lie in `K*`, so `K* ≠ M_σ` (else every
`S ≤ M_σ = K*`).  Retained as a named lemma for the `typeP_structure` `(e)` conjunct. -/
theorem kstar_ne_msigma_aux [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥) :
    Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  intro hKMσ
  -- Pick `p ∈ π(M_σ)` and a Sylow `S = Syl_p(M_σ)`; then `S ≤ M_σ = K*`, contradicting
  -- `typeP_sylow_not_le_kstar` (`S ⊄ K*`).
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ :=
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG h.mem_maximal
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).exists_prime_and_dvd
    (fun hc => hMσne (Subgroup.card_eq_one.mp hc))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h p
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup p ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hpdvdS : p ∣ Nat.card ↥S := by
      rw [hScard]
      exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hpdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hpdvdS
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvdS)
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSMσ hSq hSmax (by rw [hKMσ]; exact hSMσ)

/-- **BG Proposition 14.2** (mmd L3778): structure of a type-`P` maximal subgroup
("nearly everything proved in §13" about `M ∈ 𝓜_𝓟`).

`K` = Hall `κ(M)`-subgroup of `M`, `K* = C_{M_σ}(K)`, `U` = Hall `(κ(M) ∪ σ(M))'`-subgroup.
BG states seven parts (a)–(g); this Lean surface is a **faithful partial** capturing the
prime action `(a)`, `K* ≠ 1` `(c)`, the normalizer identity `N_M(X) = K × K*` `(b1)`, the
`(d)` disjointness `K* ∩ M^g = 1` for `g ∉ M`, and the type-`P₂` consequences `(g)`
(`σ = β`, `|K|` prime, `M_σ` a `TI`-subgroup). Deferred to proof time (gated on §13): the
`(a)` regular action on `U` / normal complement `U M_σ`, part `(b2)`, the second half of
`(c)`, the `(d)` clause `K ∩ K^g = 1`, parts `(e)`, `(f)`, and `M_σ` nilpotent in `(g)`.
See `notes/bg/s14_typeP_counting.md` for the full part-map.

**Faithfulness note (2026-06-14):** a spurious `M_σ ≤ N_G(K*)` conjunct was removed — it is
not one of BG's seven parts and is false in general (`K = C_q` acting on a Heisenberg
`M_σ = p^{1+2}` by `a ↦ aʳ, b ↦ b, c ↦ cʳ` gives `K* = ⟨b⟩`, which is **not** normal in
`M_σ` since `a b a⁻¹ = bc ∉ ⟨b⟩`). -/
theorem typeP_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K ∧
      Kstar ≠ ⊥ ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ K →
        Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar) ∧
      (∀ g : G, g ∉ M → Kstar ⊓ (MulAut.conj g • M) = ⊥) ∧
      (IsTypeP2 M → OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
        ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧
          IsTISubset (sigmaSharp M) (Subgroup.normalizer
            ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G))) ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ Kstar →
        maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
      Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  -- Choose a §12 `E`-setup whose `M_σ`-complement `E` contains `K` (BG: "take `E ⊇ K`").
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- BG splits on whether `κ(M) ∩ τ₃(M) = ∅` (i.e. `E₃ ≠ 1` and `E₃` non-regular vs `κ ⊆ τ₁`).
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `E₃` acts non-regularly on `M_σ` (the `κ`-witness conjugates
    -- into `E₃`), so Corollary 13.11 gives `E = E₁ ⊔ E₃`, `E` prime on `M_σ`, and every
    -- `X ∈ ℰ¹(E)` normal in `E`; then `K = E`, and the conjuncts follow.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    -- Extract an `E₃`-witness `x` with `C_{M_σ}(x) ≠ 1` from non-regularity.
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    -- `π(E) ⊆ κ(M)`, so `E` is a `κ(M)`-subgroup; the Hall `κ(M)`-subgroup `K ≤ E` forces `K = E`.
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (a) prime action: immediate from `K = E` and Corollary 13.11.
      rw [hKEeq]; exact hEprime
    · -- `K^* = C_{M_σ}(K) = C_{M_σ}(E) ≠ 1` (prime action + the non-regular witness).
      rw [hKstar, hKEeq]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
    · -- (b1) `N_M(X) = K ⊔ K^*` for rank-one `X ≤ K`.  `⊇`: `K = E ≤ N_G(X)` by Corollary 13.11
      -- (`hEnorm`), and `K^* = C_{M_σ}(K) ≤ C_G(X) ≤ N_G(X)`, `K^* ≤ M_σ ≤ M`.  `⊆` (BG "clear",
      -- needs the `M = M_σ ⋊ E` semidirect structure) is deferred.
      intro p hp X hXrank hXK
      haveI : Fact p.Prime := ⟨hp⟩
      refine le_antisymm ?_ ?_
      · -- ⊆: decompose `n = s·e` (`s ∈ M_σ`, `e ∈ E`) in `↥M`; for `g ∈ X#`, `s·(ege⁻¹)·s⁻¹ =
        -- ngn⁻¹ ∈ X ≤ E`, so `[s, ege⁻¹] ∈ M_σ ∩ E = 1`, i.e. `s` centralizes `ege⁻¹ ∈ E#`.
        -- Prime action then gives `s ∈ C_{M_σ}(E) = K*`, and `e ∈ E = K`.
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        haveI hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hsetup.E_le,
            hsetup.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
        have hse : (a : G) * (b : G) = n := by
          have h := congrArg (Subtype.val) hab; simpa using h
        -- A nonidentity `g ∈ X` and `y' = e g e⁻¹ ∈ E#`.
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
        have hgE : g ∈ E := (hXK.trans hKEeq.le) hgX
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ E := E.mul_mem (E.mul_mem he hgE) (E.inv_mem he)
        have hy'1 : (b : G) * g * (b : G)⁻¹ ≠ 1 := by
          rw [show (b : G) * g * (b : G)⁻¹ = MulAut.conj (b : G) g from (MulAut.conj_apply _ _).symm]
          exact fun hc => hg1' ((MulAut.conj (b : G)).map_eq_one_iff.mp hc)
        -- `s · y' · s⁻¹ = n g n⁻¹ ∈ X ≤ E`.
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        -- `[s, y'] ∈ M_σ ∩ E = 1`, so `s` centralizes `y'`.
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ E :=
          hsy' ▸ (hXK.trans hKEeq.le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (hsetup.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ E :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, E.mul_mem hsy'E (E.inv_mem hy'E)⟩
          rw [hsetup.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `s ∈ C_{M_σ}(y') = C_{M_σ}(E) = K*`, `e ∈ E = K`, so `n = s·e ∈ K ⊔ K*`.
        have hscent : (a : G) ∈ Subgroup.centralizer ({(b : G) * g * (b : G)⁻¹} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)).symm
        have hsKstar : (a : G) ∈ Kstar := by
          rw [hKstar, hKEeq, ← fixedBy_def, ← hEprime _ hy'E hy'1, fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs, hscent⟩
        rw [← hse]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hsKstar)
          (Subgroup.mem_sup_left (hKEeq ▸ he))
      · refine sup_le ?_ ?_
        · rw [hKEeq]
          exact le_inf (hEnorm p hp X hXrank (hXK.trans hKEeq.le)) (hKEeq ▸ hKM)
        · rw [hKstar]
          exact le_inf
            (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
              (Subgroup.centralizer_le_normalizer _)))
            (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K^* ∩ M^g = 1` for `g ∉ M`: a rank-one `X ≤ K^* ∩ M^g` has `C_G(X) ⊆ M` by (c),
      -- and `X ≤ M^g` with Theorem 10.1(e) forces `g ∈ M`.
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w).trans hw
      have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w.2
      have hKstarE : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) := by
        rw [hKstar, hKEeq]
      have hXK : Subgroup.zpowers (w : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) :=
        hKstarE ▸ (hXle.trans inf_le_left)
      -- (c): `C_G(X) ⊆ M`.
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem hXK
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      -- `X ≤ M_σ ≤ M`, `q ∈ σ(M)`, `X` a `q`-group.
      have hXMσ : Subgroup.zpowers (w : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
      have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
      -- `X ≤ M^g` gives `conj g⁻¹ • X ≤ M`; Theorem 10.1(e) yields `g⁻¹ ∈ M`.
      have hXgM : Subgroup.zpowers (w : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) In the `κ ∩ τ₃` case `K = E`, so `κ(M) = π(M) ∖ σ(M)`, i.e. `M` is type `P₁`;
      -- this contradicts `IsTypeP2 M` (whose defining clause is `κ(M) ≠ π(M) ∖ σ(M)`).
      intro hP2
      refine absurd ?_ hP2.2
      apply Set.eq_of_subset_of_subset
      · -- `κ(M) ⊆ π(M) ∖ σ(M)`: each `p ∈ κ` is a prime dividing `|M|` (witness `P ≤ M`) and `∉ σ`.
        intro p hpκ
        obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
        have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
          rcases hpτ with h | h
          · exact tau1_subset_sigma_compl M h
          · exact tau3_subset_sigma_compl M h
        exact ⟨Nat.mem_primeFactors.mpr
            ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
      · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E|` ⟹ `p ∈ κ` (by `mem_kappa…`).
        intro p hp
        obtain ⟨hpπ, hpσ⟩ := hp
        obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
        haveI : Fact p.Prime := ⟨hpp⟩
        have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
          hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
            (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
        have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
          rw [hsetup.card_Msigma_mul_card_E]; exact hpdvdM
        have hpE : p ∈ (Nat.card ↥E).primeFactors :=
          Nat.mem_primeFactors.mpr
            ⟨hpp, (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
        exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hpE
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E)` (`K = E`),
      -- so the `C(E)`-form Corollary 12.14 helper (`…_centralizer_E`) applies directly.
      intro p hp X hXelem hXKstar
      haveI : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem
        (hKEeq ▸ hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁ ≤ K = E`.
      have hE1K : E₁ ≤ K := by rw [hKEeq]; exact hsetup.E₁_le
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar, hKEeq]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
      refine kstar_ne_msigma_aux hG hsetup hE1K (le_of_eq hKEeq) hE1ne
        (fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))) (fun q hq => ?_) hKstar hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  · -- Case `κ(M) ⊆ τ₁(M)`: `κ = τ₁`, and `K` is `M`-conjugate to `E₁` (both Hall `κ(M)`).
    -- Conjugate the `E`-setup by `w` (`conj w • E₁ = K`) and read the conjuncts off the new setup
    -- via the `E₁`-lemmas (Theorem 13.5 etc.), exactly as in case `τ₃` with `E₁` in place of `E`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    -- `E₁ ≠ 1`, non-regular, prime on `M_σ`, `C_{M_σ}(E₁) ≠ 1`.
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    -- `E₁` is a Hall `κ(M)`-subgroup of `E` (π(E₁) ⊆ κ by coverage; index avoids `κ ⊆ τ₁`).
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    -- WLOG `conj w • E₁ = K`; conjugate the setup so its new `E₁` is `K`.
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    -- Read off `K = (h').E₁` facts.
    obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
    refine ⟨hKprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (K* ≠ 1) `= C_{M_σ}(K) ≠ 1`.
      rw [hKstar]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
    · -- (b1) `N_M(X) = K ⊔ K*` for rank-one `X ≤ K`.  Here `K = E₁' ⊊ E'`, so the case-`τ₃`
      -- argument is twisted: decompose `n = a·b` (`a ∈ M_σ`, `b ∈ E'`); `[a, bgb⁻¹] = 1` gives
      -- `ngn⁻¹ = bgb⁻¹`, so `s' := b⁻¹n` centralizes `g`, hence `s' ∈ C_{M_σ}(K) = K*` (prime
      -- action), `n = b·s'`, and `b = n·s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K` by the Frobenius normalizer lemma.
      intro p hp X hXrank hXK
      haveI : Fact p.Prime := ⟨hp⟩
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hKcentX : K ≤ Subgroup.centralizer (X : Set G) := by
        letI : CommGroup ↥K := (subgroupE_basic hG h').2.2.2.1.1.commGroup
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (mul_comm (⟨y, hXK hy⟩ : ↥K) (⟨k, hk⟩ : ↥K))
      refine le_antisymm ?_ ?_
      · -- ⊆
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        haveI hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔
            (MulAut.conj w • E).subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h'.E_le,
            h'.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ MulAut.conj w • E := Subgroup.mem_subgroupOf.mp hb
        have hbM : (b : G) ∈ M := h'.E_le he
        have hse : (a : G) * (b : G) = n := by have hh := congrArg Subtype.val hab; simpa using hh
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
        have hgK : g ∈ K := hXK hgX
        have hgE' : g ∈ MulAut.conj w • E := h'.E₁_le hgK
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ MulAut.conj w • E :=
          (MulAut.conj w • E).mul_mem ((MulAut.conj w • E).mul_mem he hgE')
            ((MulAut.conj w • E).inv_mem he)
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ MulAut.conj w • E :=
          hsy' ▸ (hXK.trans h'.E₁_le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (h'.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj w • E) :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, (MulAut.conj w • E).mul_mem hsy'E
              ((MulAut.conj w • E).inv_mem hy'E)⟩
          rw [h'.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `n g n⁻¹ = b g b⁻¹` (the `M_σ`-part `a` centralizes `b g b⁻¹`).
        have hngn_eq : n * g * n⁻¹ = (b : G) * g * (b : G)⁻¹ :=
          hsy'.symm.trans (mul_inv_eq_one.mp hcomm1)
        -- `s' := b⁻¹ · n ∈ M_σ` centralizes `g`, so `s' ∈ C_{M_σ}(K) = K*`.
        have hs'Mσ : (b : G)⁻¹ * n ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have hbinvN : (b : G)⁻¹ ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
            Subgroup.inv_mem _ (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hbM)
          have heq2 : (b : G)⁻¹ * n = (b : G)⁻¹ * (a : G) * ((b : G)⁻¹)⁻¹ := by rw [← hse]; group
          rw [heq2]
          exact (Subgroup.mem_normalizer_iff.mp hbinvN (a : G)).mp hs
        have hs'cent : (b : G)⁻¹ * n ∈ Subgroup.centralizer ({g} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz; rw [Set.mem_singleton_iff.mp hz]
          -- `g * (b⁻¹n) = (b⁻¹n) * g`, i.e. `b⁻¹ n centralizes g`, from `ngn⁻¹ = bgb⁻¹`.
          have hkey : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹ = g := by
            have hrw : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹
                = (b : G)⁻¹ * (n * g * n⁻¹) * (b : G) := by group
            rw [hrw, hngn_eq]; group
          exact (mul_inv_eq_iff_eq_mul.mp hkey).symm
        have hs'Kstar : (b : G)⁻¹ * n ∈ Kstar := by
          rw [hKstar, ← fixedBy_def, ← hKprime g hgK hg1', fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs'Mσ, hs'cent⟩
        -- `b = n · s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K`.
        have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := by
          have hs'N : ((b : G)⁻¹ * n)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
            (Subgroup.normalizer (X : Set G)).inv_mem
              ((hKstar ▸ inf_le_right.trans
                ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
                  (Subgroup.centralizer_le_normalizer _))) hs'Kstar)
          have hbeq : (b : G) = n * ((b : G)⁻¹ * n)⁻¹ := by group
          rw [hbeq]; exact (Subgroup.normalizer (X : Set G)).mul_mem hnX hs'N
        have hbK : (b : G) ∈ K :=
          normalizer_inf_E_le_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hXrank hXK
            (Subgroup.mem_inf.mpr ⟨hbN, he⟩)
        -- `n = b · s' ∈ K ⊔ K*`.
        have hnbs' : n = (b : G) * ((b : G)⁻¹ * n) := by group
        rw [hnbs']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbK) (Subgroup.mem_sup_right hs'Kstar)
      · refine sup_le (le_inf (hKcentX.trans (Subgroup.centralizer_le_normalizer _)) hKM) ?_
        rw [hKstar]
        exact le_inf
          (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
            (Subgroup.centralizer_le_normalizer _)))
          (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K* ∩ M^g = 1` for `g ∉ M` (mirror of case `τ₃`, using the new setup `h'` whose
      -- `E₁ = K` and the `C(E₁)`-form of (c)).
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w' : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w').trans hw'
      have hXelem : Subgroup.zpowers (w' : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w' : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w'.2
      have hXC : Subgroup.zpowers (w' : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) :=
        hKstar ▸ (hXle.trans inf_le_left)
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem hXC
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w' : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      have hXMσ : Subgroup.zpowers (w' : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
      have hXM : Subgroup.zpowers (w' : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w' : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w' : G)) := hXelem.1.isPGroup
      have hXgM : Subgroup.zpowers (w' : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) type-`P₂` ⟹ `σ = β`, `|K|` prime, `M_σ` nilpotent TI.  `IsTypeP2 M` forces
      -- `U = E₂E₃ ≠ 1` (`E23_ne_bot_of_isTypeP2_caseTau1`); the Frobenius core
      -- (`sigma_eq_beta_and_prime_card_E1_of_caseTau1`) gives `σ = β` and `|K|` prime via
      -- Theorem 3.10(a); the TI clause follows from `σ = β` (`isTISubset_sigmaSharp_of_sigma_eq_beta`).
      intro hP2
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hUne := E23_ne_bot_of_isTypeP2_caseTau1 hG h' hKprime hKstar_ne hτ3 hP2
      obtain ⟨hσβ, q, hq, hqcard⟩ :=
        sigma_eq_beta_and_prime_card_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hUne
      exact ⟨hσβ, q, hq, hqcard, isTISubset_sigmaSharp_of_sigma_eq_beta hG hM hσβ⟩
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E₁')` (`K = E₁'`),
      -- so the `C(E₁)`-form Corollary 12.14 helper (`…_centralizer_E1`) applies directly.
      intro p hp X hXelem hXKstar
      haveI : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem
        (hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁' = K`.
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      refine kstar_ne_msigma_aux hG h' (le_refl K) h'.E₁_le hKne hKne (fun q hq => ?_) hKstar hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))

/-- **BG Proposition 14.2(b2)** (mmd L3829): for a type-`P` `M`, a Hall `κ(M)`-subgroup `K`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every `M* ∈ ℳ(N_G(X))` satisfies `X ⊆ M*_σ`.

This is the clause of Prop 14.2(b) that `typeP_structure` omits — it carries only (b1)
(`N_M(X) = K × K*`).  The hypothesis `C_{M_σ}(X) ≠ 1` is automatic for `X ∈ ℰ¹(K)` (then
`C_{M_σ}(X) ⊇ C_{M_σ}(K) = K* ≠ 1`), so callers supply it from `typeP_structure`'s `K* ≠ 1`.
Theorem 14.7's neighbour analysis (`Z = K×K* ⊆ M_i`, `X_i ⊆ M_{iσ}`) needs this clause.

Proof (BG): `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`; Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`) gives
`p ∈ σ(M*)`; since `X ≤ N_G(X) ≤ M*` is a `σ(M*)`-subgroup, `X ⊆ M*_σ`. -/
theorem typeP_elemAbelian_le_neighbor_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
  classical
  -- `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  have hpτ13 : p ∈ tau1 M ∪ tau3 M := kappa_subset_tau1_union_tau3 hpκ
  -- `K` is a `σ(M)'`-subgroup; get an `E`-setup with `K ≤ E`, so `X ≤ E`.
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := fun q hq =>
    kappa_subset_sigmaCompl (hK.1 q (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- Lemma 13.13: `p ∈ σ(M*)`.
  have hpσMstar : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch3.S13.mem_sigma_of_tau1_tau3_centralize hG hsetup hpτ13 hX (hXK.trans hKE)
      hCX hMstar
  -- `X ≤ M*` is a `σ(M*)`-subgroup, hence `X ≤ M*_σ`.
  have hMstarMax : Mstar ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMstar).1
  have hXMstar : X ≤ Mstar :=
    Subgroup.le_normalizer.trans (mem_maximalSubgroupsContaining.mp hMstar).2
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarMax) hXMstar (fun q hq => ?_)
  rw [(mem_elemAbelianOfRank.mp hX).2, pow_one, Nat.Prime.primeFactors (Fact.out : p.Prime),
    Finset.mem_singleton] at hq
  rwa [hq]

/-- **Theorem 14.7 neighbour-embedding** (BG L3977-3982), step 1 of the §16-independent
pre-position: for a type-`P` `M` with Hall `κ(M)`-subgroup `K`, `K* = C_{M_σ}(K)`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every neighbour `M_i ∈ ℳ(N_G(X))` is **not conjugate to `M`**,
contains `Z = K ⊔ K*`, and has `X ⊆ M_{iσ}`.

Uses Prop 14.2(b1) [`N_M(X) = K×K*`, so `K ⊔ K* = N_G(X) ⊓ M ≤ N_G(X) ≤ M_i`], Prop 14.2(b2)
[`X ⊆ M_{iσ}`], and `σ`-conjugation-invariance: `p ∈ π(X) ⊆ κ(M) ⊆ σ(M)'`, but `X ⊆ M_{iσ}` gives
`p ∈ σ(M_i)`, so `M_i = M^g` would force `p ∈ σ(M^g) = σ(M)`, a contradiction. -/
theorem typeP_neighbor_embed [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ¬ IsConjugateSubgroup M Mi ∧ K ⊔ Kstar ≤ Mi ∧ X ≤ OddOrder.BG.Ch3.S10.Msigma Mi := by
  classical
  -- `p ∈ κ(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  -- `X ⊆ M_{iσ}` (Prop 14.2(b2)).
  have hXMiσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi :=
    typeP_elemAbelian_le_neighbor_Msigma hG hM hKM hK hX hXK hCX hMi
  -- `K ⊔ K* ≤ M_i` (Prop 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`, and `N_G(X) ≤ M_i`).
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hZMi : K ⊔ Kstar ≤ Mi := by
    rw [← hb1 p Fact.out X hX hXK]
    exact le_trans inf_le_left (mem_maximalSubgroupsContaining.mp hMi).2
  refine ⟨?_, hZMi, hXMiσ⟩
  -- `M_i` not conjugate to `M`: else `σ(M_i) = σ(M)`, but `p ∈ σ(M_i) ∩ κ(M) ⊆ σ(M) ∩ σ(M)'`.
  rintro ⟨g, hg⟩
  have hpσMi : p ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXMiσ), Nat.card_pos.ne'⟩)
  rw [← hg] at hpσMi
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hpσMi
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  exact kappa_subset_sigmaCompl hpκ hpσM

/-- **A `κ(M)`-subgroup of `M` lies in some Hall `κ(M)`-subgroup of `M`** (Hall D / Wielandt,
`Ch03.hall_D`, applied inside the solvable group `↥M`).  Used by Corollary 14.3 branch 1 to put
the `κ`-witness `X₀ ≤ ⟨x'⟩` into a Hall `κ`-subgroup `K`, so that Proposition 14.2(b1)/(c) apply. -/
theorem exists_isHallSubgroup_kappa_ge [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXκ : ∀ q ∈ (Nat.card ↥X).primeFactors, q ∈ kappa M) :
    ∃ K : Subgroup G, K ≤ M ∧ Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧ X ≤ K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXκ q hq
  obtain ⟨K', hK'hall, hK'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  have hKeq : (K'.map M.subtype).subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  refine ⟨K'.map M.subtype, Subgroup.map_subtype_le K', ?_, ?_⟩
  · rw [hKeq]; exact hK'hall
  · exact le_of_eq_of_le (Subgroup.map_subgroupOf_eq_of_le hXM).symm (Subgroup.map_mono hK'ge)

/-- **`C_M(M_σ)` is a `κ(M)'`-group** (BG Corollary 15.3 step, mmd L4209 "By Proposition
14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group", for `H = M_σ`).  No prime of `κ(M)` divides
`|C_M(M_σ)|`.

Proof.  If some `p ∈ κ(M)` divided `|C_M(M_σ)|`, take `x ∈ C_M(M_σ)` of order `p`; then
`X₀ = ⟨x⟩` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes
`M_σ`, `M_σ ≤ C_G(X₀) ≤ N_G(X₀)`, and Proposition 14.2(b1) (`typeP_structure` conjunct 3) gives
`N_G(X₀) ⊓ M = K ⊔ K*`.  By the Dedekind identity (`K* ≤ M_σ`, `M_σ ⊓ K = ⊥`, `K ≤ N(K*)`),
`M_σ ⊓ (K ⊔ K*) = K*`, whence `M_σ = K*`, contradicting `K* ≠ M_σ` (`typeP_structure`
conjunct 7, BG Prop 14.2(e), `kstar_ne_msigma_aux`). -/
theorem centralizer_msigma_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ
      (Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: an order-`p` element `x` of `C = C_M(M_σ)`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤
      Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  -- `X₀` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  -- A Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: (b1) and (e) `K* ≠ M_σ`, with `K* = M_σ ⊓ C(K)`.
  obtain ⟨_, _, hb1, _, _, _, hKstar_ne⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `M_σ ≤ N_G(X₀) ⊓ M = K ⊔ K*`  (`X₀ ≤ C(M_σ)` ⟹ `M_σ ≤ C(X₀) ≤ N_G(X₀)`).
  have hMσ_le : OddOrder.BG.Ch3.S10.Msigma M ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    refine le_inf ?_ (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hcent : OddOrder.BG.Ch3.S10.Msigma M ≤
        Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G) :=
      Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  -- `M_σ = K*` (since `M_σ ≤ K ⊔ K*`), contradicting `K* ≠ M_σ`.
  exact hKstar_ne (((inf_of_le_left hMσ_le).symm).trans hdedekind).symm

/-- **§12 `E`-setup adapted to a `κ(M)`-Hall subgroup `K`** (the preamble of BG Prop 14.2's proof,
mmd L3832-3840).  For a type-`P` `M` and a Hall `κ(M)`-subgroup `K`, there is an `E`-setup whose
`τ₁`-Hall `E₁` lies in `K ≤ E` with `E₁ ≠ 1`.  In the `κ ∩ τ₃ ≠ ∅` case `K = E ⊇ E₁`; in the
`κ ⊆ τ₁` case the setup is conjugated so its `E₁` becomes `K`.  Packages exactly the hypotheses
that `typeP_sylow_not_le_kstar` (Prop 14.2(e)) consumes. -/
theorem exists_typePESetup_kappaHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    ∃ E E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ ∧ E₁ ≤ K ∧ K ≤ E ∧ E₁ ≠ ⊥ := by
  classical
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ ∩ τ₃ ≠ ∅`: `E = E₁ E₃` is `κ`-pure, so `K = E`; then `E₁ ≤ E = K`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, _, hEprime, _⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    exact ⟨E, E₁, E₂, E₃, hsetup, hsetup.E₁_le.trans hKEeq.ge, hKEeq.le, hE1ne⟩
  · -- Case `κ ⊆ τ₁`: `K` is `M`-conjugate to `E₁`; conjugate the setup so its new `E₁ = K`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    obtain ⟨hKne, _⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    exact ⟨MulAut.conj w • E, K, MulAut.conj w • E₂, MulAut.conj w • E₃, h', le_refl K,
      h'.E₁_le, hKne⟩

/-- **BG Proposition 14.2(e), packaged for `typeP_structure` inputs** (mmd L3828).  The `S ⊄ K*`
clause of Prop 14.2(e) stated with the natural type-`P` hypotheses (`M` maximal type-`P`, `K` a
Hall `κ(M)`-subgroup) instead of a raw `E`-setup: it builds the setup via
`exists_typePESetup_kappaHall` and applies `typeP_sylow_not_le_kstar`. -/
theorem typeP_sylow_not_le_kstar_of_isHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  obtain ⟨E, E₁, E₂, E₃, h, hE1K, hKE, hE1ne⟩ := exists_typePESetup_kappaHall hG hM hP hKM hK
  have hKne : K ≠ ⊥ := fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))
  have hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M := fun p hp =>
    kappa_subset_tau1_union_tau3 (hK.1 p (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp))
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSle hSq hSmax

/-- **`C_M(H)` is a `κ(M)'`-group for every nontrivial Hall subgroup `H` of `M_σ`** (BG Corollary
15.3(a) start, mmd L4209 "By Proposition 14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group").  The
general-Hall analogue of `centralizer_msigma_isPiSubgroup_kappa_compl` (`H = M_σ`).

Proof.  If `p ∈ κ(M)` divided `|C_M(H)|`, take `x ∈ C_M(H)` of order `p`; then `X₀ = ⟨x⟩` is a
`κ`-subgroup lying in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes `H`, `H ≤ C_G(X₀) ≤
N_G(X₀)`, and Prop 14.2(b1) gives `N_G(X₀) ⊓ M = K ⊔ K*`; with `H ≤ M_σ`, the Dedekind identity
`M_σ ⊓ (K ⊔ K*) = K*` forces `H ≤ K*`.  As `H` is Hall in `M_σ`, a Sylow `q`-subgroup `S` of `M_σ`
(for `q ∈ π(H)`) lies in `H ≤ K*`, contradicting Prop 14.2(e)
(`typeP_sylow_not_le_kstar_of_isHall`, `S ⊄ K*`). -/
theorem centralizer_hall_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ (Subgroup.centralizer (H : Set G) ⊓ M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: `x ∈ C = C_G(H) ⊓ M` of order `p`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (H : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤ Subgroup.centralizer (H : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: `K* ≠ 1` and (b1) `N_M(X₀) = K ⊔ K*`.
  obtain ⟨_, hKstar_ne, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `H ≤ C_G(X₀) ≤ N_G(X₀)` (`x` centralizes `H`), and `H ≤ M`, so `H ≤ N_M(X₀) = K ⊔ K*`.
  have hH_le_N : H ≤ Subgroup.normalizer ((Subgroup.zpowers (x : G)) : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hH_le_KKstar : H ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    exact le_inf hH_le_N (hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`; with `H ≤ M_σ`, `H ≤ K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  have hH_le_Kstar : H ≤ Kstar := by
    have hHmem : H ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) := le_inf hHMσ hH_le_KKstar
    rwa [hdedekind] at hHmem
  -- A prime `q ∈ π(H)` and a Sylow `q`-subgroup `S` of `M_σ` with `S ≤ H ≤ K*`.
  obtain ⟨q, hq, hqdvd⟩ := (Nat.card ↥H).exists_prime_and_dvd
    (fun hc => hHne (Subgroup.card_eq_one.mp hc))
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q ↥H) := Sylow.nonempty
  set S : Subgroup G := (P : Subgroup ↥H).map H.subtype with hSdef
  have hS_le_H : S ≤ H := hSdef ▸ Subgroup.map_subtype_le _
  have hS_le_Mσ : S ≤ OddOrder.BG.Ch3.S10.Msigma M := hS_le_H.trans hHMσ
  have hScardH : Nat.card ↥S = q ^ (Nat.card ↥H).factorization q := by
    rw [hSdef, Subgroup.card_map_of_injective H.subtype_injective, P.card_eq_multiplicity]
  have hSq : IsPGroup q ↥S := IsPGroup.iff_card.mpr ⟨_, hScardH⟩
  -- Hall: `q ∤ [M_σ : H]`, so `v_q(|H|) = v_q(|M_σ|)`.
  have hqpiH : q ∈ piSet H := Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
  have hHcard : Nat.card ↥(H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHMσ).toEquiv
  have hq_ndvd_index : ¬ q ∣ (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := fun hdvd =>
    hHhall.index_no_pi q
      (Nat.mem_primeFactors.mpr ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqpiH
  have hfact_eq : (Nat.card ↥H).factorization q
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    have hsplit : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
        = Nat.card ↥H * (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := by
      rw [← hHcard]; exact (Subgroup.card_mul_index _).symm
    rw [hsplit, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_index, add_zero]
  have hScard : Nat.card ↥S = q ^ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    rw [hScardH, hfact_eq]
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hqdvdS : q ∣ Nat.card ↥S := by
      rw [hScardH]
      exact dvd_pow_self q (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hqdvdS
    exact hq.one_lt.ne' (Nat.dvd_one.mp hqdvdS)
  exact typeP_sylow_not_le_kstar_of_isHall hG hM hP hKM hKHall hKstardef hKstar_ne
    hSne hS_le_Mσ hSq hSmax (hS_le_H.trans hH_le_Kstar)

/-- **BG Corollary 14.3, branch-2 piece** (mmd L3858): if `x'` is a nonidentity `τ₂(M)`-element
of `M` with `C_{M_σ}(x') ≠ 1`, then `ℳ(C_G(x')) = {M}`.  This is Corollary 12.10(e)
(`nilpotent_sigmaComplement_abelian`, fifth conjunct) for an `E`-setup of `M`, with the prime
set `π(⟨x'⟩)` rewritten as `(orderOf x').primeFactors`. -/
theorem maximalContaining_centralizer_eq_singleton_of_tau2_element [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x' : G} (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M)
    (hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M} := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hcard : Nat.card ↥(Subgroup.closure {x'}) = orderOf x' := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact (nilpotent_sigmaComplement_abelian hG hsetup).2.2.2.2 x' hx'M hx'1
    (fun r hr => hx'τ2 r (by
      show r ∈ (Nat.card ↥(Subgroup.closure {x'})).primeFactors
      rw [hcard]; exact hr)) hC

/-- **`pi_of_cent_sigma` τ₂-case uniqueness** (Coq `BGsection14`:806, the `'M('C[y]) = [set M]`
half of the τ₂ branch of Corollary 14.3): for `x ∈ M_σ^#` and a `τ₂(M)`-element `x' ∈ (C_M[x])^#`,
the unique maximal subgroup containing `C_G(x')` is `M`.  The nonregularity side condition of
`maximalContaining_centralizer_eq_singleton_of_tau2_element` (`M_σ ⊓ C_G(x') ≠ 1`) is witnessed by
`x`: since `x'` centralizes `x`, `x` centralizes `x'`, and `x ∈ M_σ^#`.  This is the directly
discharged part of `pi_of_cent_sigma`'s τ₂ branch (the `ℓ_σ(x') = 1` part needs
`primes_norm_tau2Elem`, the κ branch needs `Ptype_structure`). -/
theorem pi_of_cent_sigma_tau2_uniqueness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cx : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure ({x'} : Set G)), p ∈ tau2 M) :
    maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M} := by
  have hcomm : x * x' = x' * x :=
    Subgroup.mem_centralizer_iff.mp hx'cx x rfl
  have hxcx' : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm.symm
  refine maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM hx'M hx'1 hx'τ2 ?_
  intro hbot
  have hxmem : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxMσ, hxcx'⟩
  rw [hbot, Subgroup.mem_bot] at hxmem
  exact hx1 hxmem

/-- **BG Lemma 15.1(c)** (mmd L4170): if `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M` and
`X` is a nonidentity subgroup of `U` with `C_{M_σ}(X) ≠ 1`, then `ℳ(C_G(X)) = {M}` and `X` is a
cyclic `τ₂(M)`-subgroup.

Proof (following BG L4176): since `X ≤ U`, every prime `p ∈ π(X)` lies in `(κ(M) ∪ σ(M))'`,
so `p ∉ σ(M)`, `p ∉ κ(M)`, and `p ∈ π(M)`.

*`π(X) ⊆ τ₂(M)`:* if some `p ∈ π(X)` had `p ∉ τ₂(M)`, then `r_p(M) = 1`, and a rank-one
elementary abelian `A ≤ X` (Cauchy) realizes the maximal rank, so Lemma 14.1
(`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`; centralizer antitonicity
(`A ≤ X`) yields `C_{M_σ}(X) ≤ C_{M_σ}(A) = 1`, contradicting `hCX`.

*`X` cyclic:* `X` is a `τ₂(M)`-subgroup of the solvable `M`, hence (Hall D) conjugate into the
abelian Hall `τ₂(M)`-subgroup `E₂` (Corollary 12.10(b)), so `X` is abelian.  Each Sylow `p` of `X`
is cyclic, for if it contained `A ∈ ℰ_p²(X)` then Theorem 12.5(d) (`Msigma_nilpotent_of_tau2`)
would give `C_{M_σ}(A) = 1` and again `C_{M_σ}(X) = 1`.  An abelian group with cyclic Sylow
subgroups is cyclic (`isCyclic_of_sylow_isCyclic`).

*`ℳ(C_G(X)) = {M}`:* with `X = ⟨x⟩` cyclic and `C_G(X) = C_G(x)`, apply Corollary 14.3 branch 2
(`maximalContaining_centralizer_eq_singleton_of_tau2_element`). -/
theorem typeP_hall_small_subgroup_cyclic_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {X : Subgroup G} (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) := by
  classical
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hXM : X ≤ M := hXU.trans hUM
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  -- Each prime of `X` lies in `(κ(M) ∪ σ(M))'`, hence `∉ σ`, `∉ κ`, and `∈ π(M)`.
  have hXprimes : ∀ p ∈ (Nat.card ↥X).primeFactors,
      p ∉ OddOrder.BG.Ch3.S10.sigma M ∧ p ∉ kappa M ∧ p ∈ piSet M := by
    intro p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    have hpdvdU : p ∣ Nat.card ↥U := hpdvdX.trans (Subgroup.card_dvd_of_le hXU)
    have hpdvdM : p ∣ Nat.card ↥M := hpdvdX.trans (Subgroup.card_dvd_of_le hXM)
    have hpUM : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvdU, Nat.card_pos.ne'⟩
    have hpcompl : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 p hpUM
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpcompl
    exact ⟨hpcompl.2, hpcompl.1, Nat.mem_primeFactors.mpr ⟨hpp, hpdvdM, Nat.card_pos.ne'⟩⟩
  -- **Part A**: `π(X) ⊆ τ₂(M)`.
  have hXτ2 : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpσ, hpκ, hpπ⟩ := hXprimes p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    -- `p ∉ τ₂(M)` with `p ∉ σ(M)` gives `r_p(M) ≠ 2`; rank bounds force `r_p(M) = 1`.
    have hr2 : pRank ↥M p ≠ 2 := fun h => hpτ2 ((mem_tau2_iff M p).mpr ⟨hpσ, h⟩)
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hpp hpπ hpσ
    have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpπ
    have hub : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
    have hr1 : pRank ↥M p = 1 := by omega
    -- A rank-one elementary abelian subgroup `A ≤ X` of maximal rank.
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpdvdX
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAX : A ≤ X := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective X.subtype X.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]
      exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    -- Lemma 14.1: `C_{M_σ}(A) = 1`; antitonicity gives `C_{M_σ}(X) = 1`, contradiction.
    obtain ⟨_, hCA, _⟩ :=
      msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA (hAX.trans hXM)
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- **Part B(i)**: `X` is abelian (conjugate into the abelian Hall `τ₂`-subgroup `E₂`).
  -- `X` is a `τ₂(M)`-subgroup, so `X.subgroupOf M` is a `τ₂(M)`-π-subgroup of `↥M`.
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ tau2 M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXτ2 q hq
  obtain ⟨H', hH'hall, hH'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  set HG : Subgroup G := H'.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup (tau2 M) (HG.subgroupOf M) := by
    rw [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hH'hall
  have hX_le_HG : X ≤ HG := by
    rw [hHGdef]
    refine le_trans ?_ (Subgroup.map_mono hH'ge)
    rw [Subgroup.map_subgroupOf_eq_of_le hXM]
  -- `E₂` is also a Hall `τ₂(M)`-subgroup of `M`.
  have hE₂_hall_M : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hsetup.E₂_le hsetup.E₂_hall (tau2_subset_sigma_compl M)
  -- Conjugate `HG` onto `E₂` (Hall C inside `↥M`).
  obtain ⟨w, _, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv hHG_le_M hsetup.E2_le_M
      hHG_hall hE₂_hall_M
  have hbE₂ : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG hsetup).2.1.1
  -- `conj w • X ≤ E₂`; commuting in `E₂` transports back to `X`.
  have hXwE₂ : (MulAut.conj w • X : Subgroup G) ≤ E₂ := by
    rw [← hw]
    exact Subgroup.map_mono hX_le_HG
  have hXab : IsMulCommutative ↥X := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    -- `w·a·w⁻¹` and `w·b·w⁻¹` lie in `conj w • X ≤ E₂`, hence commute.
    have haw : w * (a : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (a : G))).mpr a.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hbw : w * (b : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (b : G))).mpr b.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hcomm : (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹)
        = (w * (b : G) * w⁻¹) * (w * (a : G) * w⁻¹) :=
      congrArg Subtype.val (hbE₂.is_comm.comm ⟨_, haw⟩ ⟨_, hbw⟩)
    have hcancel := congrArg (fun u => w⁻¹ * u * w) hcomm
    simpa [mul_assoc] using hcancel
  haveI : IsMulCommutative ↥X := hXab
  -- **Part B(ii)**: every Sylow `p` of `X` is cyclic (else `ℰ_p²(X)` ↝ `C_{M_σ}(X) = 1`).
  have hSylcyc : ∀ p : ℕ, p.Prime → ∀ P : Sylow p ↥X, IsCyclic P := by
    intro p hp P
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hPnc
    -- `P` is noncyclic, hence nontrivial, so `p ∣ |X|` and (oddness of `G`) `p` is odd.
    have hpcardP : p ∣ Nat.card ↥(P : Subgroup ↥X) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · refine absurd ?_ hPnc
        haveI : Subsingleton ↥(P : Subgroup ↥X) :=
          (Nat.card_eq_one_iff_unique.mp (by rw [hn, h0, pow_zero])).1
        exact isCyclic_of_subsingleton
      · rw [hn]; exact dvd_pow_self p hpos.ne'
    have hpcardX : p ∣ Nat.card ↥X :=
      hpcardP.trans (Subgroup.card_subgroup_dvd_card _)
    have hodd : Odd p :=
      hG.odd.of_dvd_nat (hpcardX.trans (Subgroup.card_subgroup_dvd_card X))
    -- A noncyclic odd `p`-group contains a rank-two elementary abelian subgroup (BG Lemma 4.5(a)).
    obtain ⟨B, hBelem, hBcard⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        P.isPGroup' hodd hPnc
    -- Map `B ≤ P ≤ ↥X` up to `G`.
    set A : Subgroup G := (B.map (P : Subgroup ↥X).subtype).map X.subtype with hAdef
    have hAelem : A.IsElementaryAbelian p := by
      rw [hAdef]
      exact (hBelem.map (Subgroup.subtype_injective _)).map X.subtype_injective
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBcard]
    have hAX : A ≤ X := by
      rw [hAdef]
      exact le_trans (Subgroup.map_mono (Subgroup.map_subtype_le _)) (Subgroup.map_subtype_le _)
    have hA2 : A ∈ elemAbelianOfRank G p 2 := mem_elemAbelianOfRank.mpr ⟨hAelem, hAcard⟩
    -- `p ∈ τ₂(M)`, then Theorem 12.5(d): `C_{M_σ}(A) = 1`, contradicting `hCX`.
    have hpX : p ∈ (Nat.card ↥X).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      exact (dvd_pow_self p two_ne_zero).trans (hAcard ▸ Subgroup.card_dvd_of_le hAX)
    have hpτ2 : p ∈ tau2 M := hXτ2 p hpX
    have hCA := (Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 (hAX.trans hXM)).2.2.2.1
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- `X` abelian with cyclic Sylows ⟹ `X` cyclic.
  have hXcyc : IsCyclic ↥X := by
    letI : IsMulCommutative ↥X := hXab
    exact OddOrder.Isaacs.Ch06.isCyclic_of_sylow_isCyclic hSylcyc
  refine ⟨?_, hXcyc, fun p hp => hXτ2 p hp⟩
  -- **Part C**: `ℳ(C_G(X)) = {M}` via the cyclic generator `x`.
  obtain ⟨x₀, hx₀gen⟩ := hXcyc.exists_generator
  set x : G := (x₀ : G) with hxdef
  have hXeq : X = Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx₀gen ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [hxdef, ← Subgroup.coe_zpow, hk]
    · rw [Subgroup.zpowers_le, hxdef]; exact x₀.2
  have hxX : x ∈ X := hXeq ▸ Subgroup.mem_zpowers x
  have hxM : x ∈ M := hXM hxX
  -- `x ≠ 1` (else `X = ⟨1⟩ = ⊥`).
  have hx1 : x ≠ 1 := by
    intro hxe
    apply hXne
    rw [hXeq, hxe, Subgroup.zpowers_one_eq_bot]
  -- `π(⟨x⟩) ⊆ τ₂(M)`.
  have hxτ2 : ∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 M := by
    intro p hp
    refine hXτ2 p ?_
    have : Subgroup.closure {x} = X := by rw [← Subgroup.zpowers_eq_closure, ← hXeq]
    rwa [this] at hp
  -- `C_G(X) = C_G({x})`.
  have hCeq : Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [hXeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    rwa [hCeq] at hCX
  rw [hCeq]
  exact maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM hxM hx1 hxτ2 hCne

/-- The `σ`-set is conjugation-invariant: `σ(Mᵍ) = σ(M)` (both inclusions from `sigma_conj`;
non-primes lie in neither set). -/
theorem sigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.sigma (MulAut.conj g • M) = OddOrder.BG.Ch3.S10.sigma M := by
  ext p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    refine ⟨fun hmem => ?_, fun hmem => OddOrder.BG.Ch3.S10.sigma_conj g hmem⟩
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hmem
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  · exact ⟨fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp,
      fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp⟩

/-- `O_π` (`opiCoreInG`) commutes with conjugation (replicated from the private
`S07_Transitivity.conj_smul_opiCoreInG`). -/
private theorem conj_smul_opiCoreInG' [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]

/-- `M_σ` is conjugation-equivariant: `(Mᵍ)_σ = (M_σ)ᵍ`.  Used to move an element of `M*_σ` back to
its conjugate maximal subgroup when witnessing `ℓ_σ = 1`. -/
theorem Msigma_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [conj_smul_opiCoreInG', sigma_conj_smul_eq]

/-- **BG Corollary 14.3** (mmd L3852): for `x ∈ M_σ^#` and a nonidentity `σ(M)'`-element `x'`
of `C_M(x)`, either (1) `π(⟨x'⟩) ⊆ κ(M)` and `C_G(x) ⊆ M`, or (2) `π(⟨x'⟩) ⊆ τ₂(M)`,
`ℓ_σ(x') = 1`, and `𝓜(C_G(x')) = {M}`.

Proof sketch (gated on §13 via Prop 14.2): a prime `p ∈ π(⟨x'⟩) ∩ τ₂(M)'` lies in
`τ₁(M) ∪ τ₃(M)`, and `C_{M_σ}(X) ⊇ ⟨x⟩ ≠ 1` for `X ∈ ℰ_p¹(⟨x'⟩)` forces `p ∈ κ(M)`; then
Lemma 14.1(b) gives `x' ∈ K`, `x ∈ C_{M_σ}(K)`, and Proposition 14.2(c) yields `C_G(x) ⊆ M`
(branch 1).  Otherwise `x'` is a `τ₂(M)`-element with `C_{M_σ}(x') ≠ 1`, so Corollary 12.10(e)
gives `𝓜(C_G(x')) = {M}` and Lemma 12.11(a) gives `ℓ_σ(x') = 1` (branch 2).

**Faithfulness (2026-06-15):** reformulated to the verbatim BG statement.  The earlier scaffold
had an `x ↔ x'` transposition (branch 1's body asserted the impossible `x' ∈ M_σ`), a missing
`x'`-centralizes-`x` hypothesis, and dropped `C_G(x) ⊆ M`, `ℓ_σ(x')`, and `𝓜(C_G(x'))`.
`ℓ_σ(x')` is carried by the `SigmaDecompositionData` `D` (`D.length x' = 1`).  Proof deferred
(gated on §13).  See `notes/bg/s14_typeP_counting.md`. -/
theorem sigma_diagnostic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cent : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}),
      p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ kappa M) ∧
        Subgroup.centralizer ({x} : Set G) ≤ M) ∨
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M) ∧
        D.length x' = 1 ∧
        maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M}) := by
  classical
  -- `x ∈ M_σ`, `x ≠ 1`.
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  have hclos : Subgroup.closure ({x'} : Set G) = Subgroup.zpowers x' :=
    (Subgroup.zpowers_eq_closure x').symm
  -- `x` centralizes `x'`.
  have hxCx' : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)).symm
  -- `C_{M_σ}(x') ≠ 1` (it contains `x ≠ 1`).
  have hCx'ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥ :=
    fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCx'⟩))
  by_cases hτ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M
  · -- **Branch 2**: `x'` is a `τ₂(M)`-element.
    refine Or.inr ⟨hτ2, ?_, maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM
      hx'M hx'1 hτ2 hCx'ne⟩
    -- `ℓ_σ(x') = 1`: `x'` is a `σ(M*)`-element (Lemma 12.11(a)), hence `G`-conjugate into `M*_σ`
    -- (general Corollary 12.16(a)), so `𝓜_σ(x')` is nonempty.
    refine (D.length_one_iff x').mpr ⟨hx'1, ?_⟩
    -- `π(⟨x'⟩)` is nonempty (`x' ≠ 1`); pick a prime `q₀ ∈ π(⟨x'⟩) ⊆ τ₂(M)`.
    have hclosne : Subgroup.closure ({x'} : Set G) ≠ ⊥ := fun hbot =>
      hx'1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure (Set.mem_singleton x')))
    obtain ⟨q₀, hq₀mem⟩ : (piSet (Subgroup.closure ({x'} : Set G))).Nonempty :=
      Nat.nonempty_primeFactors.mpr (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')
        (Ne.symm fun h => hclosne (Subgroup.card_eq_one.mp h)))
    have hq₀prime : q₀.Prime := Nat.prime_of_mem_primeFactors hq₀mem
    haveI : Fact q₀.Prime := ⟨hq₀prime⟩
    have hq₀τ2 : q₀ ∈ tau2 M := hτ2 q₀ hq₀mem
    -- `E`-setup, a rank-2 `A ∈ ℰ_{q₀}²(E)` (push `ℰ_{q₀}²(M)` into `E₂`), and `M* ∈ ℳ(N_G(A))`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq₀prime hq₀τ2
    obtain ⟨w, _, hwle⟩ := exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₁M (by
        intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
          Nat.primeFactors_pow q₀ two_ne_zero, Nat.Prime.primeFactors hq₀prime] at hr
        rw [Finset.mem_singleton.mp hr]; exact hq₀τ2)
    have hA : MulAut.conj w • A₁ ∈ elemAbelianOfRank G q₀ 2 := conj_smul_mem_elemAbelianOfRank w hA₁
    have hAE : MulAut.conj w • A₁ ≤ E := hwle.trans hsetup.E₂_le
    have hAM : MulAut.conj w • A₁ ≤ M := hAE.trans hsetup.E_le
    have hAne : MulAut.conj w • A₁ ≠ ⊥ := by
      intro hbot
      have hc : Nat.card ↥(MulAut.conj w • A₁) = q₀ ^ 2 := hA.2
      rw [hbot, Subgroup.card_bot] at hc
      rcases Nat.pow_eq_one.mp hc.symm with h | h
      · exact hq₀prime.ne_one h
      · exact absurd h (by norm_num)
    obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
      OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
        hG hM hAne hAM
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining
        (Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
    -- Lemma 12.11(a): every prime of `π(⟨x'⟩) ⊆ τ₂(M)` lies in `σ(M*)`.
    have hx'piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)
        (Subgroup.closure ({x'} : Set G)) := fun p hp =>
      (tau2_prime_mem_sigma_diff_beta hG hsetup hq₀τ2 hA hAE hMstarMem
        (Nat.prime_of_mem_primeFactors hp) (hτ2 p hp)).1
    -- general Corollary 12.16(a): `⟨x'⟩` is `G`-conjugate into `M*_σ`.
    have hzplt : Subgroup.closure ({x'} : Set G) < ⊤ :=
      lt_of_le_of_lt (by rw [hclos, Subgroup.zpowers_le]; exact hx'M)
        (mem_maximalSubgroups.mp hM).lt_top
    obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hMstar_max hclosne hzplt hx'piMstar
      (fun hN hnc => sigma_disjoint_of_nonconjugate hG hMstar_max hN hnc)
    -- `M' = (M*)^{g⁻¹}` is maximal and contains `x'` in its `σ`-core.
    refine ⟨MulAut.conj g⁻¹ • Mstar,
      mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hMstar_max)), ?_⟩
    rw [Msigma_conj_smul]
    have hconj : MulAut.conj g • x' ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
      hg (Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Subgroup.closure ({x'} : Set G))
        (Subgroup.subset_closure (Set.mem_singleton x')))
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using hconj
  · -- **Branch 1**: some prime `p₀ ∈ π(⟨x'⟩)` lies in `τ₁(M) ∪ τ₃(M)`.
    left
    push Not at hτ2
    obtain ⟨p₀, hp₀mem, hp₀τ2⟩ := hτ2
    have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀mem
    haveI : Fact p₀.Prime := ⟨hp₀prime⟩
    have hp₀σ : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M := hx'sigma p₀ hp₀mem
    -- `⟨x'⟩ ≤ M`, so `p₀ ∣ |M|`, and `p₀ ∤ |M_σ|`, hence `p₀ ∈ π(E)`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    have hclosM : Subgroup.closure ({x'} : Set G) ≤ M := by
      rw [hclos, Subgroup.zpowers_le]; exact hx'M
    have hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.closure ({x'} : Set G)) :=
      (Nat.mem_primeFactors.mp hp₀mem).2.1
    have hp₀M : p₀ ∣ Nat.card ↥M := hp₀cardclos.trans (Subgroup.card_dvd_of_le hclosM)
    have hp₀nMσ : ¬ p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hp₀σ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p₀
        (Nat.mem_primeFactors.mpr ⟨hp₀prime, hdvd, Nat.card_pos.ne'⟩))
    have hp₀E : p₀ ∈ (Nat.card ↥E).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp₀prime, ?_, Nat.card_pos.ne'⟩
      have hdvdME : p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
        rw [hsetup.card_Msigma_mul_card_E]; exact hp₀M
      exact (hp₀prime.dvd_mul.mp hdvdME).resolve_left hp₀nMσ
    have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M := by
      rcases hsetup.mem_tau_union_of_mem_primeFactors hG hp₀E with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hp₀τ2
      · exact Or.inr h3
    -- `X₀ = ⟨w⟩` of order `p₀`, `≤ ⟨x'⟩`, with `x ∈ C_{M_σ}(X₀)`, so `p₀ ∈ κ(M)`.
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀
      (hclos ▸ hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.zpowers x'))
    set X₀ : Subgroup G := Subgroup.zpowers (w : G) with hX₀def
    have hX₀le_clos : X₀ ≤ Subgroup.closure ({x'} : Set G) := by
      rw [hX₀def, hclos, Subgroup.zpowers_le]; exact w.2
    have hX₀M : X₀ ≤ M := hX₀le_clos.trans hclosM
    have hwcard : Nat.card ↥X₀ = p₀ := by
      rw [hX₀def, Nat.card_zpowers]
      exact (orderOf_injective (Subgroup.zpowers x').subtype
        (Subgroup.zpowers x').subtype_injective w).trans hw
    have hX₀elem : X₀ ∈ elemAbelianOfRank G p₀ 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hwcard, by rw [hwcard, pow_one]⟩
    have hX₀le_zp : X₀ ≤ Subgroup.zpowers x' := by
      rw [hX₀def, Subgroup.zpowers_le]; exact w.2
    -- `x` centralizes `X₀` (it centralizes `x'`, and `X₀ ≤ ⟨x'⟩`).
    have hcomm : Commute x x' :=
      Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)
    have hxCw : Commute x (w : G) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
      rw [← hn]; exact hcomm.zpow_right n
    have hxCX₀ : x ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hxCw.zpow_right m).symm
    have hCX₀ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X₀ : Set G) ≠ ⊥ :=
      fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCX₀⟩))
    have hp₀κ : p₀ ∈ kappa M := ⟨hp₀prime, hp₀τ13, X₀, hX₀elem, hX₀M, hCX₀ne⟩
    -- A Hall `κ(M)`-subgroup `K ⊇ X₀`, a Hall `(κ∪σ)'`-subgroup `U`, and `Kstar = C_{M_σ}(K)`.
    have hX₀κ : ∀ q ∈ (Nat.card ↥X₀).primeFactors, q ∈ kappa M := by
      intro q hq
      rw [hwcard, hp₀prime.primeFactors, Finset.mem_singleton] at hq
      exact hq ▸ hp₀κ
    obtain ⟨K, hKM, hK, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
      ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
    have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
    have hP : IsTypeP M := ⟨p₀, hp₀κ⟩
    obtain ⟨_, _, hb1, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK
      (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) hU
    -- `C_M(x') ⊆ N_G(X₀) ⊓ M = K ⊔ K*` (Prop 14.2(b1)).
    have hb1X₀ := hb1 p₀ hp₀prime X₀ hX₀elem hX₀K
    have hCx'_le_CX₀ : Subgroup.centralizer ({x'} : Set G) ≤ Subgroup.centralizer (X₀ : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgw : Commute g (w : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
        rw [← hn]
        have hgx' : Commute x' g := Subgroup.mem_centralizer_iff.mp hg x' (Set.mem_singleton x')
        exact hgx'.symm.zpow_right n
      exact (hgw.zpow_right m).symm
    have hCMx'_le : Subgroup.centralizer ({x'} : Set G) ⊓ M ≤
        K ⊔ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hb1X₀]
      exact inf_le_inf_right _ (hCx'_le_CX₀.trans (Subgroup.centralizer_le_normalizer _))
    -- `x' ∈ K` (the `σ'`-part) and `x ∈ K*` (the `σ`-part) of `K ⊔ K* = K × K*`.
    set Kst : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      with hKstdef
    have hKstMσ : Kst ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
    have hKstC : Kst ≤ Subgroup.centralizer (K : Set G) := inf_le_right
    -- `K` is normal in `K ⊔ K*` (`K*` centralizes `K`), so elements decompose as `k · s`.
    have hKnorm : K ⊔ Kst ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (hKstC.trans (Subgroup.centralizer_le_normalizer _))
    haveI hKsNorm : ((K).subgroupOf (K ⊔ Kst)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
    have hsuptop : (K.subgroupOf (K ⊔ Kst)) ⊔ (Kst.subgroupOf (K ⊔ Kst)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hdecomp : ∀ z : G, z ∈ K ⊔ Kst → ∃ k ∈ K, ∃ s ∈ Kst, k * s = z := by
      intro z hz
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hsuptop ▸ Subgroup.mem_top (⟨z, hz⟩ : ↥(K ⊔ Kst)))
      exact ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb,
        by have := congrArg Subtype.val hab; simpa using this⟩
    -- `K ∩ M_σ = ⊥` (`K` is a `κ(M) ⊆ σ(M)'`-group, `M_σ` a `σ(M)`-group).
    have hKMσbot : K ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
      intro r hr hrK hrMσ
      have hrκ : r ∈ kappa M := hK.1 r (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
        exact Nat.mem_primeFactors.mpr ⟨hr, hrK, Nat.card_pos.ne'⟩)
      exact kappa_subset_sigmaCompl hrκ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
    have hcardclos : Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' := by
      rw [hclos, Nat.card_zpowers]
    -- `x ∈ K*`: `x = k · s` with `k ∈ K`, `s ∈ K* ≤ M_σ`; `x ∈ M_σ` forces `k ∈ K ∩ M_σ = ⊥`.
    have hxsup : x ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr ⟨hxCx', (OddOrder.BG.Ch3.S10.Msigma_le M) hxMσ⟩)
    have hxKstar : x ∈ Kst := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x hxsup
      have hkMσ : k ∈ OddOrder.BG.Ch3.S10.Msigma M := by
        have : k = x * s⁻¹ := by rw [← hks]; group
        rw [this]
        exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hxMσ
          ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem (hKstMσ hsKst))
      have hk1 : k = 1 := Subgroup.mem_bot.mp (hKMσbot ▸ Subgroup.mem_inf.mpr ⟨hkK, hkMσ⟩)
      rw [← hks, hk1, one_mul]; exact hsKst
    -- `x' ∈ K`: `x' = k · s` with `s ∈ K* ≤ M_σ`; `x'` is a `σ'`-element, so `s = 1`.
    have hx'sup : x' ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by rw [Set.mem_singleton_iff.mp hy]), hx'M⟩)
    have hx'K : x' ∈ K := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x' hx'sup
      have hcommks : Commute k s := Subgroup.mem_centralizer_iff.mp (hKstC hsKst) k hkK
      have hsM : s ∈ OddOrder.BG.Ch3.S10.Msigma M := hKstMσ hsKst
      -- `(k·s)^N = k^N · s^N = 1` (`N = orderOf x'`), so `k^N = (s^N)⁻¹ ∈ K ∩ M_σ = ⊥`.
      have hN : k ^ orderOf x' * s ^ orderOf x' = 1 := by
        rw [← hcommks.mul_pow, hks]; exact pow_orderOf_eq_one x'
      have hkN1 : k ^ orderOf x' = 1 := by
        have hmem : k ^ orderOf x' ∈ K ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
          Subgroup.mem_inf.mpr ⟨K.pow_mem hkK _, by
            rw [eq_inv_of_mul_eq_one_left hN]
            exact (OddOrder.BG.Ch3.S10.Msigma M).inv_mem
              ((OddOrder.BG.Ch3.S10.Msigma M).pow_mem hsM _)⟩
        exact Subgroup.mem_bot.mp (hKMσbot ▸ hmem)
      have hsN1 : s ^ orderOf x' = 1 := by
        have := hN; rw [hkN1, one_mul] at this; exact this
      -- `orderOf s ∣ orderOf x'` and `orderOf s ∣ |M_σ|`, which are coprime, so `s = 1`.
      have hcop : Nat.Coprime (orderOf x') (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) :=
        coprime_of_forall_prime_not_dvd (fun r hr hrx' hrMσ => by
          exact hx'sigma r (by
            rw [piSet, Set.mem_setOf_eq, hcardclos]
            exact Nat.mem_primeFactors.mpr ⟨hr, hrx', (orderOf_pos_iff.mpr
              (isOfFinOrder_of_finite x')).ne'⟩)
            (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
              (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩)))
      have hsord : orderOf s = 1 := by
        have hdvd1 : orderOf s ∣ orderOf x' := orderOf_dvd_of_pow_eq_one hsN1
        have hdvd2 : orderOf s ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
          have h := orderOf_dvd_natCard (⟨s, hsM⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M))
          rwa [← orderOf_injective (OddOrder.BG.Ch3.S10.Msigma M).subtype
            (OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨s, hsM⟩] at h
        have hg : orderOf s ∣ Nat.gcd (orderOf x')
            (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := Nat.dvd_gcd hdvd1 hdvd2
        rw [hcop] at hg
        exact Nat.dvd_one.mp hg
      have hs1 : s = 1 := orderOf_eq_one_iff.mp hsord
      rw [← hks, hs1, mul_one]; exact hkK
    refine ⟨?_, ?_⟩
    · -- `π(⟨x'⟩) ⊆ κ(M)`: `x' ∈ K`, `K` is a Hall `κ(M)`-subgroup.
      intro p hp
      rw [hclos] at hp
      have hpK : p ∈ (Nat.card ↥K).primeFactors := by
        refine Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, ?_, Nat.card_pos.ne'⟩
        exact ((Nat.mem_primeFactors.mp hp).2.1.trans
          (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx'K)))
      have hpKM : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact hK.1 p hpKM
    · -- `C_G(x) ⊆ M`: a rank-one `X₁ ≤ ⟨x⟩ ≤ K*` has `ℳ(C_G(X₁)) = {M}` (Prop 14.2(c)),
      -- and `C_G(x) ⊆ C_G(X₁) ⊆ M`.
      obtain ⟨p₁, hp₁, hp₁dvd⟩ := Nat.exists_prime_and_dvd
        (show orderOf x ≠ 1 from fun h => hx1 (orderOf_eq_one_iff.mp h))
      haveI : Fact p₁.Prime := ⟨hp₁⟩
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) p₁
        (by rw [Nat.card_zpowers]; exact hp₁dvd)
      have hvcard : Nat.card ↥(Subgroup.zpowers (v : G)) = p₁ := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective (Subgroup.zpowers x).subtype
          (Subgroup.zpowers x).subtype_injective v).trans hv
      have hX₁elem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G p₁ 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hvcard, by rw [hvcard, pow_one]⟩
      have hvx : (v : G) ∈ Subgroup.zpowers x := v.2
      have hX₁Kst : Subgroup.zpowers (v : G) ≤ Kst :=
        Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr hxKstar) hvx)
      have h𝓜 : maximalSubgroupsContaining
          (Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G)) = {M} :=
        hc p₁ hp₁ (Subgroup.zpowers (v : G)) hX₁elem hX₁Kst
      have hCX₁M : Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      refine le_trans ?_ hCX₁M
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgx : Commute g x := (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
      have hgv : Commute g (v : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hvx
        rw [← hn]; exact hgx.zpow_right n
      exact ((hgv.zpow_right m).symm)

/-- Centralizer of `⟨x⟩` equals centralizer of `{x}` (replicated private helper). -/
theorem centralizer_zpowers_eq_singleton' (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hc x (Subgroup.mem_zpowers x)
  · intro hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute x c from hc x rfl).zpow_left k).eq

/-- **Theorem 14.7 neighbour `κ`-transfer** (BG L3983-3991), step 1b of the §16-independent
pre-position: in the situation of `typeP_neighbor_embed`, every prime `q ∈ π(K*)` lies in
`κ(M_i)`.

Proof: take `X* = ⟨x'⟩ ∈ ℰ_q¹(K*)` (Cauchy).  Since `x ∈ X ⊆ M_{iσ}^#` centralizes `x'` (both
lie in `Z = K × K*` with `[K, K*] = 1`) and `x' ∈ K*` is a `σ(M_i)'`-element (Theorem 13.9 makes
`σ(M)` disjoint from `σ(M_i)`), Corollary 14.3 (`sigma_diagnostic`) applies to `(M_i, x, x')`.
Its branch 2 would give `ℳ(C_G(x')) = {M_i}`, contradicting Prop 14.2(c)'s `ℳ(C_G(x')) = {M}`
(`M ≠ M_i`); so branch 1 holds, giving `q ∈ π(⟨x'⟩) ⊆ κ(M_i)`.  (`sigma_diagnostic`'s `ℓ_σ`
carrier `D` is supplied by a dummy `SigmaDecompositionData`; only the branch dichotomy and its
`ℳ(C_G(x'))` clause are used, not `D.length`.) -/
theorem typeP_neighbor_kappa [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi := by
  classical
  obtain ⟨hnc, hZMi, hXMiσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMi
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hMiMax : Mi ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMi).1
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hMiMax hnc
  -- A dummy `ℓ_σ` carrier for `sigma_diagnostic`.
  let D : SigmaDecompositionData G :=
    { length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
      length_one_iff := by
        intro y; by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h] }
  -- An element `x ∈ X^#` lands in `M_{iσ}^#`.
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
  obtain ⟨xsub, hxsub⟩ := exists_ne (1 : ↥X)
  have hxX : (xsub : G) ∈ X := xsub.2
  have hxne : (xsub : G) ≠ 1 := fun h => hxsub (OneMemClass.coe_eq_one.mp h)
  have hxK : (xsub : G) ∈ K := hXK hxX
  have hxsharp : (xsub : G) ∈ sigmaSharp Mi := by
    rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨hXMiσ hxX, hxne⟩
  intro q hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- Cauchy: `x' ∈ K*` of order `q`.
  obtain ⟨x'sub, hx'ord⟩ := exists_prime_orderOf_dvd_card' q
    (Nat.dvd_of_mem_primeFactors hq : q ∣ Nat.card ↥Kstar)
  have hx'Kstar : (x'sub : G) ∈ Kstar := x'sub.2
  have hx'ord' : orderOf (x'sub : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x'sub).trans hx'ord
  have hx'ne : (x'sub : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx'ord'
    exact (Nat.prime_of_mem_primeFactors hq).ne_one hx'ord'.symm
  have hX'card : Nat.card ↥(Subgroup.zpowers (x'sub : G)) = q := by rw [Nat.card_zpowers, hx'ord']
  have hX'mem : Subgroup.zpowers (x'sub : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX'card, by rw [hX'card, pow_one]⟩
  have hX'Kstar : Subgroup.zpowers (x'sub : G) ≤ Kstar := Subgroup.zpowers_le.mpr hx'Kstar
  have hx'Mi : (x'sub : G) ∈ Mi := hZMi (Subgroup.mem_sup_right hx'Kstar)
  have hx'CK : (x'sub : G) ∈ Subgroup.centralizer (K : Set G) := by
    have h2 : (x'sub : G) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact hx'Kstar
    exact (Subgroup.mem_inf.mp h2).2
  have hxCx' : (x'sub : G) ∈ Subgroup.centralizer ({(xsub : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hx'CK (xsub : G) hxK
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr ⟨Fact.out,
      (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_dvd_of_le
        (by rw [hKstar]; exact inf_le_left : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M)),
      Nat.card_pos.ne'⟩)
  have hclos' : Subgroup.closure ({(x'sub : G)} : Set G) = Subgroup.zpowers (x'sub : G) :=
    (Subgroup.zpowers_eq_closure (x'sub : G)).symm
  have hcardclos : Nat.card ↥(Subgroup.closure ({(x'sub : G)} : Set G)) = q :=
    (congrArg (fun S : Subgroup G => Nat.card ↥S) hclos').trans hX'card
  have hx'sigma : ∀ r ∈ piSet (Subgroup.closure {(x'sub : G)}),
      r ∉ OddOrder.BG.Ch3.S10.sigma Mi := by
    intro r hr
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq),
      Finset.mem_singleton] at hr
    rw [hr]; exact Set.disjoint_left.mp hσdisj hqσM
  rcases sigma_diagnostic hG D hMiMax hxsharp hx'Mi hx'ne hxCx' hx'sigma with
    ⟨hπκ, _⟩ | ⟨_, _, hℳ⟩
  · refine hπκ q ?_
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq)]
    exact Finset.mem_singleton_self q
  · exfalso
    have hcX' := hc q (Nat.prime_of_mem_primeFactors hq) (Subgroup.zpowers (x'sub : G)) hX'mem
      hX'Kstar
    rw [centralizer_zpowers_eq_singleton'] at hcX'
    rw [hcX'] at hℳ
    exact hnc ((Set.singleton_eq_singleton_iff.mp hℳ) ▸ IsConjugateSubgroup.refl M)

end OddOrder.BG.Ch4.S14
