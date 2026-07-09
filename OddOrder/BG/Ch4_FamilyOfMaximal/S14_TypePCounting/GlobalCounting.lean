import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting.TypePDuality

/-!
# BG Lemma 14.11 - Lemma 14.13 — global counting + subnormal closure

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S14
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch3.S13
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### BG Lemma 14.11 — phase 1: `Q ⊄ F(E) ⟹ q ∈ τ₁(M)` and `C_{M_σ}(Q) = 1`

The proof of Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting` below) first locates the prime
`q` in the τ-partition and pins down its `M_σ`-centralizer.  These first steps are factored as
reusable lemmas; the remaining structure (the cyclic-normal `⁅E,Q⁆`, `τ₂(M) ≠ ∅`, and the
`M*`-dichotomy) is recorded in `issues/7007`. -/

/-- Build a `SubgroupESetup` on a *given* `M_σ`-complement `E` (converting the `IsComplement'`
hypothesis to the `M_σ ⊓ E = ⊥`, `M_σ ⊔ E = M` form expected by `subgroupESetup_of_complement`). -/
theorem esetup_of_isComplement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M) :
    ∃ E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hinf : OddOrder.BG.Ch3.S10.Msigma M ⊓ E = ⊥ := by
    have hd := hE.disjoint
    rw [disjoint_iff] at hd
    have h2 : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M = ⊥ := by
      have he : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M
          = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊓ E.subgroupOf M :=
        Subgroup.comap_inf _ _ M.subtype
      rw [he]; exact hd
    have h3 := congrArg (Subgroup.map M.subtype) h2
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_of_left_le hMσM), Subgroup.map_bot] at h3
  have hsup : OddOrder.BG.Ch3.S10.Msigma M ⊔ E = M := by
    have hs := hE.sup_eq_top
    have h3 := congrArg (Subgroup.map M.subtype) hs
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMσM,
      Subgroup.map_subgroupOf_eq_of_le hEM, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
    exact h3
  exact subgroupESetup_of_complement hG hM hEM hinf hsup

/-- BG Lemma 14.11 step S1: `q ∉ τ₂(M)`.  A rank-2 elem abelian `B ∈ ℰ_q²(E)` is normal in `E`
(Cor 12.6(a)) hence `≤ F(E)`; line-membership forces `Q ≤ B ≤ F(E)`, contradicting `Q ⊄ F(E)`. -/
theorem typeF_complement_q_notMem_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau2 M := by
  intro hτ2
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetup hτ2
  obtain ⟨⟨hENB, hline⟩, _⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hτ2 hB hBE
  have hQB : Q ≤ B := (hline Q hQ).mp hQE
  have hBnorm : (B.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mpr hENB
  have hBpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) B := by
    intro p hp
    rw [hB.2, Nat.primeFactors_prime_pow (by norm_num) (Fact.out : q.Prime),
      Finset.mem_singleton] at hp
    exact hp
  have hBF : B ≤ OddOrder.BG.Ch2.S08.fittingInG E :=
    OddOrder.BG.Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hBE hBnorm hBpi
  exact hQF (hQB.trans hBF)

/-- BG Lemma 14.11 step S2: `q ∉ τ₃(M)`.  The τ₃-Hall `E₃` is cyclic, normal in `E`, hence `≤ F(E)`
(`E3_le_fittingInG`); a `q`-subgroup with `q ∈ τ₃` lands in `E₃`, so `Q ≤ E₃ ≤ F(E)`. -/
theorem typeF_complement_q_notMem_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau3 M := by
  intro hτ3
  haveI hE₃norm : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsetup.E₃_le).mpr (hsetup.E3_normal hG)
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hQpiG : Ch03.Subgroup.IsPiGroup (tau3 M) (Q.subgroupOf E) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQcard,
      (Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hτ3
  have hle : Q.subgroupOf E ≤ E₃.subgroupOf E :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hsetup.E₃_hall hQpiG
  have hQE₃ : Q ≤ E₃ := by
    have := Subgroup.map_mono (f := E.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hQE,
      Subgroup.map_subgroupOf_eq_of_le hsetup.E₃_le] at this
  exact hQF (hQE₃.trans (E3_le_fittingInG hG hsetup))

/-- BG Lemma 14.11 steps S1–S3 + gap C: `Q ⊄ F(E)` with `M ∈ 𝓜_F` forces `q ∈ τ₁(M)` and
`C_{M_σ}(Q) = 1`.  (`q ∈ π(E) ⊆ σ(M)'` is τ-covered; S1/S2 rule out τ₂/τ₃; a nontrivial
`C_{M_σ}(Q)` would place `q ∈ κ(M) = ∅`.) -/
theorem typeF_complement_q_tau1_and_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∈ tau1 M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqτ1 : q ∈ tau1 M := by
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hqpf with (h | h) | h
    · exact h
    · exact absurd h (typeF_complement_q_notMem_tau2 hG hsetup hQ hQE hQF)
    · exact absurd h (typeF_complement_q_notMem_tau3 hG hsetup hQ hQE hQF)
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  refine ⟨hqτ1, ?_⟩
  by_contra hne
  exact Set.notMem_empty q (hF ▸ (⟨Fact.out, Or.inl hqτ1, Q, hQ, hQM, hne⟩ : q ∈ kappa M))

open scoped IsMulCommutative commutatorElement in
/-- **BG Lemma 14.11, step S5 (degenerate case).**  If `Q ≤ E` is abelian, `R := ⁅E, Q⁆` is
abelian, and `R` centralizes `Q` (equivalently `⁅⁅E, Q⁆, Q⁆ = 1`), then the normal closure
`Q ⊔ R` of `Q` in `E` is abelian and normal in `E`, hence `Q ≤ F(E)`.  This is used to rule out
`⁅⁅E, Q⁆, Q⁆ = 1` when `Q ⊄ F(E)`: the set of `x` with `⁅x, e⁆ ∈ Q ⊔ R` is a subgroup containing
the generators `Q` and `R`, so `Q ⊔ R` is `E`-normal; it is abelian by `R ≤ C_G(Q)`. -/
private theorem Q_le_fittingInG_of_commutator_centralizesQ [Finite G]
    {E Q : Subgroup G} (hQE : Q ≤ E) (hQab : IsMulCommutative ↥Q)
    (hRab : IsMulCommutative ↥(⁅E, Q⁆ : Subgroup G))
    (hC : (⁅E, Q⁆ : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) :
    Q ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  set R : Subgroup G := ⁅E, Q⁆ with hRdef
  have hRE : R ≤ E := (Subgroup.commutator_mono le_rfl hQE).trans (Subgroup.commutator_le_self E)
  have hNE : Q ⊔ R ≤ E := sup_le hQE hRE
  have hRnorm : E ≤ Subgroup.normalizer (R : Set G) :=
    hRdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q
  have hRE_comm : (⁅R, E⁆ : Subgroup G) ≤ R := Ch04.commutator_le_of_le_normalizer hRnorm
  have hC' : Q ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hC
  -- `Q ⊔ R` is normalized by `E`.
  have hEnormN : E ≤ Subgroup.normalizer ((Q ⊔ R : Subgroup G) : Set G) := by
    refine Ch04.le_normalizer_of_commutator_le ?_
    rw [Subgroup.commutator_le]
    intro n hn e he
    let Se : Subgroup G :=
      { carrier := {x | x ∈ (Q ⊔ R : Subgroup G) ∧ ⁅x, e⁆ ∈ (Q ⊔ R : Subgroup G)}
        one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          have hid : ⁅a * b, e⁆ = a * ⁅b, e⁆ * a⁻¹ * ⁅a, e⁆ := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (mul_mem ha.1 hb.2) (inv_mem ha.1)) ha.2⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
          have hid : ⁅a⁻¹, e⁆ = a⁻¹ * ⁅a, e⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (inv_mem ha.1) (inv_mem ha.2)) ha.1⟩ }
    have hQSe : Q ≤ Se := fun x hx => ⟨Subgroup.mem_sup_left hx, by
      refine Subgroup.mem_sup_right ?_
      rw [hRdef, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx he⟩
    have hRSe : R ≤ Se := fun x hx => ⟨Subgroup.mem_sup_right hx,
      Subgroup.mem_sup_right (hRE_comm (Subgroup.commutator_mem_commutator hx he))⟩
    exact ((sup_le hQSe hRSe : (Q ⊔ R) ≤ Se) hn).2
  haveI hNnorm : ((Q ⊔ R).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hEnormN
  have hNab : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := by
    refine isMulCommutative_of_le_centralizer ?_
    rw [centralizer_sup_eq]
    exact le_inf (sup_le (le_centralizer_of_le_of_le hQab le_rfl le_rfl) hC)
      (sup_le hC' (le_centralizer_of_le_of_le hRab le_rfl le_rfl))
  haveI : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := hNab
  haveI : Group.IsNilpotent ↥(Q ⊔ R : Subgroup G) := inferInstance
  haveI : Group.IsNilpotent ↥((Q ⊔ R).subgroupOf E) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNE).symm
  have hfit : (Q ⊔ R).subgroupOf E ≤ OddOrder.Isaacs.Ch01.fitting ↥E :=
    Ch01.nilpotent_normal_le_fitting
  have hNfitG : (Q ⊔ R : Subgroup G) ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    have hmap := Subgroup.map_mono (f := E.subtype) hfit
    rwa [Subgroup.map_subgroupOf_eq_of_le hNE] at hmap
  exact le_sup_left.trans hNfitG

open OddOrder.BG.Ch3.S10 in
/-- **BG Lemma 14.11, steps S4–S7**: under the Lemma 14.11 hypotheses (`M ∈ 𝓜_F`, `E` a
`M_σ`-complement, `q ∈ π(E)`, `Q ∈ ℰ_q¹(E)`, `Q ⊄ F(E)`), there is a nontrivial cyclic subgroup
`K' = ⁅⁅E, Q⁆, Q⁆ ≤ E` that is normal in `M`, contained in `C_G(M_σ)`, has all primes in `τ₂(M)`
(so `τ₂(M) ≠ ∅`), and on which `Q` acts fixed-point-freely (`C_{K'}(Q) = 1`).

`K := ⁅E, Q⁆` is an abelian (Cor 12.10(b)) `q'`-subgroup of `M` normalized by `Q`; Proposition
10.11(d) makes `K' := ⁅K, Q⁆` cyclic, normal in `M`, and contained in `C_G(M_σ)`.  If `K' = 1`
then `⁅E, Q⁆ ≤ C_G(Q)` and `Q ≤ F(E)` (the S5 helper), contradicting `Q ⊄ F(E)`; so `K' ≠ 1`.
A prime `p ∈ π(K')` lies in `τ₂(M)`: otherwise `p ∈ τ₁(M) ∪ τ₃(M)` has `r_p(M) = 1`, and a line
`A ∈ ℰ_p¹` of `K' ≤ C_G(M_σ)` would have `C_{M_σ}(A) = M_σ ≠ 1`, contradicting Lemma 14.1.  The
`C_{K'}(Q) = 1` fixed-point-freeness comes from the coprime identity `⁅K', Q⁆ = K'` (BG **G** 8.5.4,
`commutator_commutator_right_eq` in `↥E`) and the coprime complement `fitting_coprime_abelian_decomp`. -/
theorem exists_typeF_complement_cyclic_commutator [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ K' : Subgroup G,
      K' ≤ E ∧ K' ≠ ⊥ ∧ IsCyclic ↥K' ∧
      K' ≤ Subgroup.centralizer (Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer (K' : Set G) ∧
      (∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M) ∧
      Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
  classical
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  -- `K := ⁅E, Q⁆` is an abelian `q'`-subgroup of `M`, `σ(M)'`-subgroup.
  set K : Subgroup G := ⁅E, Q⁆ with hKdef
  have hK_le_derivedE : K ≤ derivedInG E := by
    rw [hKdef, show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E]
    exact Subgroup.commutator_mono le_rfl hQE
  have hKE : K ≤ E := hK_le_derivedE.trans (Subgroup.map_subtype_le _)
  have hKM : K ≤ M := hKE.trans hsetup.E_le
  have hK_le_derivedM : K ≤ derivedInG M := by
    rw [hKdef, show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono hsetup.E_le hQM
  have hKab : IsMulCommutative ↥K :=
    isMulCommutative_of_le ((nilpotent_sigmaComplement_abelian hG hsetup).2.1.2) hK_le_derivedE
  have hKσ' : Subgroup.IsPiSubgroup (sigma M)ᶜ K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hKE), Nat.card_pos.ne'⟩
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hpE with (h | h) | h
    · exact tau1_subset_sigma_compl M h
    · exact tau2_subset_sigma_compl M h
    · exact tau3_subset_sigma_compl M h
  have hKq' : Subgroup.IsPiSubgroup (({q} : Set ℕ)ᶜ) K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK_le_derivedM),
        Nat.card_pos.ne'⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact tau1_not_mem_derived_primeFactors hqτ1 hpM'
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) ⊓ M :=
    le_inf (hQE.trans (hKdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q)) hQM
  -- Proposition 10.11(d): `K' := ⁅K, Q⁆ ≤ C_G(M_σ)`, cyclic, `M ≤ N_G(K')`.
  obtain ⟨hK'cent, hK'cyc, hMNK'⟩ :=
    sigma_complement_commutator_cyclic_normal hG hsetup.mem_maximal hKM hKσ' hqτ1.1 hQ hQNK hCQ
      hKab hKq'
  set K' : Subgroup G := ⁅K, Q⁆ with hK'def
  have hK'_le_K : K' ≤ K := hK'def ▸ Ch04.commutator_le_of_le_normalizer (le_inf_iff.mp hQNK).1
  have hK'E : K' ≤ E := hK'_le_K.trans hKE
  -- S5: `K' ≠ ⊥` (else `Q ≤ F(E)`).
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    apply hQF
    have hQab : IsMulCommutative ↥Q := ⟨⟨hQ.1.comm⟩⟩
    rw [hK'def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Q_le_fittingInG_of_commutator_centralizesQ hQE hQab (hKdef ▸ hKab) (hKdef ▸ hbot)
  -- Every prime of `K'` lies in `τ₂(M)`.
  have hπτ2 : ∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK'E), Nat.card_pos.ne'⟩
    have hpτ : p ∈ tau1 M ∪ tau2 M ∪ tau3 M := hsetup.mem_tau_union_of_mem_primeFactors hG hpE
    have hr1 : pRank ↥M p = 1 := by
      rcases hpτ with (h | h) | h
      · exact h.2.2
      · exact absurd h hpτ2
      · exact h.2.2
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAK' : A ≤ K' := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective K'.subtype K'.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]; exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le (hK'E.trans hsetup.E_le)),
        Nat.card_pos.ne'⟩
    have hpσ : p ∉ sigma M := by
      rcases hpτ with (h | h) | h
      · exact tau1_subset_sigma_compl M h
      · exact tau2_subset_sigma_compl M h
      · exact tau3_subset_sigma_compl M h
    have hpκ : p ∉ kappa M := by rw [hF]; exact Set.notMem_empty p
    have hAM : A ≤ M := hAK'.trans (hK'E.trans hsetup.E_le)
    obtain ⟨_, hCA, _⟩ := msigma_structure_of_notMem_sigma_kappa hG hsetup.mem_maximal hpπ hpσ hpκ hA hAM
    have hAcent : A ≤ Subgroup.centralizer (Msigma M : Set G) := hAK'.trans hK'cent
    have hMσcentA : Msigma M ≤ Subgroup.centralizer (A : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hAcent
    have hinf : Msigma M ⊓ Subgroup.centralizer (A : Set G) = Msigma M :=
      inf_eq_left.mpr hMσcentA
    rw [hCA] at hinf
    exact Msigma_ne_bot hG hsetup.mem_maximal hinf.symm
  -- `Q` acts fixed-point-freely on `K'`: coprime identity `⁅K', Q⁆ = K'`.
  have hqprime : q.Prime := Fact.out
  haveI hK'ab : IsMulCommutative ↥K' := isMulCommutative_of_le (hKdef ▸ hKab) hK'_le_K
  have hQNK' : Q ≤ Subgroup.normalizer (K' : Set G) := hQM.trans hMNK'
  have hqnK : ¬ q ∣ Nat.card ↥K := fun hdvd =>
    hKq' q (Nat.mem_primeFactors.mpr ⟨hqprime, hdvd, Nat.card_pos.ne'⟩) rfl
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hcopKQ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK).symm
  have hqnK' : ¬ q ∣ Nat.card ↥K' := fun hdvd =>
    hqnK (hdvd.trans (Subgroup.card_dvd_of_le hK'_le_K))
  have hcopK'Q : Nat.Coprime (Nat.card ↥K') (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK').symm
  have hident : (⁅K', Q⁆ : Subgroup G) = K' := by
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    haveI : IsSolvable ↥(K ⊔ Q) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hKM hQM))
    have hid := commutator_commutator_right_eq_of_le_normalizer (D := K) (Q := Q)
      ‹IsSolvable ↥(K ⊔ Q)› (le_inf_iff.mp hQNK).1 hcopKQ
    rw [← hK'def] at hid
    exact hid
  have hFPF : Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
    obtain ⟨hdisj, -⟩ :=
      OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := K') (K := Q) hQNK' hcopK'Q
    rwa [hident, inf_assoc, inf_idem] at hdisj
  exact ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπτ2, hFPF⟩

/-- **BG Lemma 14.11, A-choice**: for a normal line `L ◁ M` of order `p` with `p ∈ τ₂(M)` and
`L ≤ E`, there is `A ∈ ℰ_p²(E)` with `L ≤ A`.

`N_G(L) = M` (as `M ≤ N_G(L) < ⊤` and `M` is maximal), so BG Lemma 10.5
(`pRank_eq_two_of_normalizer_le`) yields `A₀ ∈ ℰ_p²(G)` with `L ≤ A₀`; `A₀` is abelian and
contains `L`, so `A₀ ≤ C_G(L) ≤ N_G(L) = M`.  As a `τ₂`-subgroup of `M`, `A₀` conjugates into the
`τ₂`-Hall `E₂ ≤ E` by some `w ∈ M` (`exists_conj_smul_le_hallPiece`); `L` is `M`-invariant so
`L = L^w ≤ A₀^w`, and `A₀^w ∈ ℰ_p²(E)`. -/
theorem exists_elemAb_rank_two_le_E_containing_line [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hp : p ∈ tau2 M)
    (hLE : L ≤ E) (hLM_norm : M ≤ Subgroup.normalizer (L : Set G))
    (hL : L ∈ elemAbelianOfRank G p 1) :
    ∃ A ∈ elemAbelianOfRank G p 2, A ≤ E ∧ L ≤ A := by
  classical
  have hLM : L ≤ M := hLE.trans hsetup.E_le
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hM_coatom : IsCoatom M := hsetup.mem_maximal
  -- `N_G(L) = M`.
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hsetup.mem_maximal hLM hLne
  have hNLM : Subgroup.normalizer (L : Set G) ≤ M := by
    rcases eq_or_lt_of_le hLM_norm with heq | hlt
    · exact heq.ge
    · exact absurd (hM_coatom.2 _ hlt) hNL_lt.ne
  -- BG Lemma 10.5: `∃ A₀ ∈ ℰ_p²(G), L ≤ A₀`.
  obtain ⟨-, -, A₀, hA₀, hLA₀⟩ :=
    OddOrder.BG.Ch3.S10.pRank_eq_two_of_normalizer_le hG hsetup.mem_maximal
      (tau2_subset_sigma_compl M hp) hL hNLM
  have hA₀card : Nat.card ↥A₀ = p ^ 2 := hA₀.2
  have hA₀ab : IsMulCommutative ↥A₀ := ⟨⟨hA₀.1.comm⟩⟩
  -- `A₀ ≤ M` (abelian, contains `L`).
  have hA₀M : A₀ ≤ M :=
    (le_centralizer_of_le_of_le hA₀ab le_rfl hLA₀).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNLM)
  -- `A₀` is a `τ₂(M)`-subgroup.
  have hA₀pi : Ch03.Subgroup.IsPiGroup (tau2 M) (A₀.subgroupOf M) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv, hA₀card] at hr
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    rwa [(Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow hr_dvd)]
  -- Conjugate `A₀` into the `τ₂`-Hall `E₂`.
  obtain ⟨w, hwM, hw⟩ :=
    exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₀M hA₀pi
  refine ⟨MulAut.conj w • A₀, conj_smul_mem_elemAbelianOfRank w hA₀, hw.trans hsetup.E₂_le, ?_⟩
  have hLfix : MulAut.conj w • L = L := conj_smul_eq_self_of_mem_normalizer (hLM_norm hwM)
  calc L = MulAut.conj w • L := hLfix.symm
    _ ≤ MulAut.conj w • A₀ := by
        rw [mulAut_smul_eq_map, mulAut_smul_eq_map]; exact Subgroup.map_mono hLA₀

/-- **BG Lemma 14.11** (mmd L4086): for `M ∈ 𝓜_F` with `E` a complement of `M_σ` in `M`, a
prime `q ∈ π(E)`, and `Q ∈ ℰ_q¹(E)` with `Q ⊄ F(E)`, there is `M* ∈ 𝓜` with either
(1) `q ∈ τ₂(M*)` and `𝓜(C_G(Q)) = {M*}`, or (2) `q ∈ κ(M*)` and `M* ∈ 𝓜_{P₁}`.

"Of independent interest" (BG L4084); used here only by Corollary 14.12.  `F(E)` is the Fitting
subgroup of the complement `E`, taken in `G` via `fittingInG`.

Phase 1 (`q ∈ τ₁(M)`, `C_{M_σ}(Q) = 1`) is `typeF_complement_q_tau1_and_centralizer`.  The
remaining phases — `τ₂(M) ≠ ∅` via the cyclic-normal `⁅E,Q⁆` (Prop 10.11(d) +
`commutator_commutator_right_eq_of_le_normalizer` / a `Q^E`-nilpotent argument for `⁅E,Q⁆ ≠ 1`),
then Cor 12.9 (`commutator_decomp_of_tau1_action`) and the `M*`-dichotomy via Lemma 12.11
(`tau2_transfer_to_maximal`) — are tracked in `issues/7007`. -/
theorem exists_maximal_of_typeF_notMem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E Q : Subgroup G} {q : ℕ} (hM : M ∈ maximalSubgroups G) (hF : IsTypeF M)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ Mstar : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      ((q ∈ tau2 Mstar ∧
          maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar}) ∨
       (q ∈ kappa Mstar ∧ IsTypeP1 Mstar)) := by
  classical
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := esetup_of_isComplement hG hM hE hEM
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqprime : q.Prime := Fact.out
  obtain ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπK'τ2, hFPF⟩ :=
    exists_typeF_complement_cyclic_commutator hG hsetup hF hq hQ hQE hQF
  haveI : IsCyclic ↥K' := hK'cyc
  obtain ⟨p, hpp, hpd⟩ :=
    Nat.exists_prime_and_dvd (show Nat.card ↥K' ≠ 1 from fun h => hK'ne (Subgroup.card_eq_one.mp h))
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpτ2 : p ∈ tau2 M := hπK'τ2 p (Nat.mem_primeFactors.mpr ⟨hpp, hpd, Nat.card_pos.ne'⟩)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
  set L : Subgroup G := Subgroup.zpowers (a : G) with hLdef
  have haG : orderOf (a : G) = p :=
    (orderOf_injective K'.subtype K'.subtype_injective a).trans ha
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, haG]
  have hLK' : L ≤ K' := by rw [hLdef, Subgroup.zpowers_le]; exact a.2
  have hLE : L ≤ E := hLK'.trans hK'E
  have hLelem : L ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hLcard, by rw [hLcard, pow_one]⟩
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hLelem
  have hLM_norm : M ≤ Subgroup.normalizer (L : Set G) := by
    haveI : (L.subgroupOf K').Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro m hm
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := K') (C := L.subgroupOf K') (hMNK' hm)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLK'] at hmem
  have hLQ : (⁅L, Q⁆ : Subgroup G) ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun hLc => hLne (le_bot_iff.mp (hFPF ▸ le_inf hLc hLK'))
  obtain ⟨A, hA, hAE, hLA⟩ :=
    exists_elemAb_rank_two_le_E_containing_line hG hsetup hpτ2 hLE hLM_norm hLelem
  have hAQ : (⁅A, Q⁆ : Subgroup G) ≠ ⊥ := fun h =>
    hLQ (le_bot_iff.mp ((Subgroup.commutator_mono hLA le_rfl).trans h.le))
  have hAne : A ≠ ⊥ := by
    intro h; have h2 := hA.2; rw [h, Subgroup.card_bot] at h2
    exact (Nat.one_lt_pow (by norm_num) hpp.one_lt).ne' h2.symm
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  obtain ⟨-, -, hA₁elem, -, -⟩ :=
    commutator_decomp_of_tau1_action hG hsetup hpτ2 hqτ1 hA hAE hQ hQE hCQ hAQ
  have hA₁ne : A ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one hA₁elem
  obtain ⟨⟨hENA, -⟩, -, -⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hpτ2 hA hAE
  have hQNA : Q ≤ Subgroup.normalizer (A : Set G) := hQE.trans hENA
  have hQncA : ¬ Q ≤ Subgroup.centralizer (A : Set G) := fun h =>
    hAQ ((Subgroup.commutator_comm A Q).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h))
  have hNA_lt : Subgroup.normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM (hAE.trans hsetup.E_le) hAne
  obtain ⟨Mstar, hMstar_coatom, hMstar_le⟩ :=
    (eq_top_or_exists_le_coatom _).resolve_left hNA_lt.ne
  have hMstarmax : Mstar ∈ maximalSubgroups G := hMstar_coatom
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstar_coatom, hMstar_le⟩
  have hAMstar : A ≤ Mstar := Subgroup.le_normalizer.trans hMstar_le
  have hQMstar : Q ≤ Mstar := hQNA.trans hMstar_le
  have hqidx : q ∈
      (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
    set c : Subgroup G := E ⊓ Subgroup.centralizer (A : Set G) with hcdef
    have hcE : c ≤ E := inf_le_left
    have hENc : E ≤ Subgroup.normalizer (c : Set G) :=
      hcdef ▸ le_normalizer_inf Subgroup.le_normalizer
        (hENA.trans (normalizer_le_normalizer_centralizer A))
    haveI hcnorm : (c.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcE).mpr hENc
    have hQ'qg : IsPGroup q ↥(Q.subgroupOf E) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQ.2]⟩
    obtain ⟨P, hQ'P⟩ := hQ'qg.exists_le_sylow
    have hQ'nc : ¬ (Q.subgroupOf E ≤ c.subgroupOf E) := by
      intro hle
      apply hQncA
      have hQc : Q ≤ c := by
        have hmm := Subgroup.map_mono (f := E.subtype) hle
        rwa [Subgroup.map_subgroupOf_eq_of_le hQE, Subgroup.map_subgroupOf_eq_of_le hcE] at hmm
      exact hQc.trans inf_le_right
    have hPnc : ¬ (P : Subgroup ↥E) ≤ c.subgroupOf E := fun hPc => hQ'nc (hQ'P.trans hPc)
    exact Nat.mem_primeFactors.mpr
      ⟨hqprime, prime_dvd_index_of_sylow_not_le_of_normal P hPnc, Subgroup.index_ne_zero_of_finite⟩
  obtain ⟨hσβ, hτ12, -⟩ := tau2_transfer_to_maximal hG hsetup hpτ2 hA hAE hMstarmem
  have hpσβ : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar \ OddOrder.BG.Ch3.S10.beta Mstar := hσβ p hpp hpτ2
  have hqτ12 : q ∈ tau1 Mstar ∪ tau2 Mstar := hτ12 q hqidx
  have hApiσ : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma Mstar) A := by
    intro r hr
    rw [hA.2, Nat.mem_primeFactors] at hr
    exact ((Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)) ▸ hpσβ.1
  have hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma Mstar :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarmax) hAMstar hApiσ
  have hCMσQ : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := fun h =>
    hA₁ne (le_bot_iff.mp (h ▸ inf_le_inf hAMσ le_rfl))
  refine ⟨Mstar, hMstarmax, ?_⟩
  rcases hqτ12 with hτ1 | hτ2
  · refine Or.inr ⟨⟨hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩, ?_⟩
    have hPtype : IsTypeP Mstar := ⟨q, hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩
    rcases (isTypeP_iff_isTypeP1_or_isTypeP2).mp hPtype with h1 | h2
    · exact h1
    · exfalso
      haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
      obtain ⟨Ksub, hKsub⟩ := Ch03.hall_E_exists (G := ↥Mstar) (kappa Mstar)
      obtain ⟨Usub, hUsub⟩ :=
        Ch03.hall_E_exists (G := ↥Mstar) ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      have hKeq : (Ksub.map Mstar.subtype).subgroupOf Mstar = Ksub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Ksub
      have hUeq : (Usub.map Mstar.subtype).subgroupOf Mstar = Usub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Usub
      have hσeqβ :=
        ((typeP_structure hG hMstarmax hPtype (Subgroup.map_subtype_le _)
            (by rw [hKeq]; exact hKsub) rfl (by rw [hUeq]; exact hUsub)).2.2.2.2.1 h2).1
      exact hpσβ.2 (hσeqβ ▸ hpσβ.1)
  · refine Or.inl ⟨hτ2, ?_⟩
    have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) q (hQcard ▸ dvd_refl q)
    have hxG : orderOf (x : G) = q := (orderOf_injective Q.subtype Q.subtype_injective x).trans hx
    set X : G := (x : G) with hXdef
    have hXQ : X ∈ Q := x.2
    have hX1 : X ≠ 1 := by
      intro h; rw [h, orderOf_one] at hxG; exact hqprime.ne_one hxG.symm
    have hcl : Subgroup.closure ({X} : Set G) = Q := by
      rw [← Subgroup.zpowers_eq_closure]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hXQ)
        (le_of_eq (by rw [hQcard, Nat.card_zpowers, hxG]))
    have hCeq : Subgroup.centralizer ({X} : Set G) = Subgroup.centralizer (Q : Set G) := by
      rw [← hcl]; exact (Subgroup.centralizer_closure {X}).symm
    have hτ2cl : ∀ r ∈ piSet (Subgroup.closure ({X} : Set G)), r ∈ tau2 Mstar := by
      intro r hr
      rw [hcl, piSet, Set.mem_setOf_eq, hQcard, Nat.mem_primeFactors] at hr
      exact ((Nat.prime_dvd_prime_iff_eq hr.1 hqprime).mp hr.2.1) ▸ hτ2
    have hsingle := maximalContaining_centralizer_eq_singleton_of_tau2_element hG hMstarmax
      (hQMstar hXQ) hX1 hτ2cl (by rw [hCeq]; exact hCMσQ)
    rwa [hCeq] at hsingle

/-- **BG Theorem A(5), element form** (mmd L4280): for a type-`P` maximal subgroup `M` with cyclic
Hall `κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, the `M`-centralizer of every nonidentity `k ∈ K`
is the cyclic product `K ⊔ K*` (BG's `C_M(k) = K × K*`).

This sharpens Proposition 14.2(b1) (`typeP_structure`), which gives `N_M(X) = K ⊔ K*` only for the
rank-one `X ∈ ℰ¹(K)`, to the element-wise centralizer.  Bridge: `K` is cyclic, so `⟨k⟩ ≤ K` is
cyclic and contains a subgroup `X` of prime order `p ∣ |k|` with `X ≤ K`; then
`C_G(k) ≤ C_G(X) ≤ N_G(X)`, so `M ⊓ C_G(k) ≤ N_G(X) ⊓ M = K ⊔ K*`, while `K ≤ C_G(k)` (`K` abelian)
and `K* ≤ C_G(K) ≤ C_G(k)` give the reverse. -/
theorem typeP_centralizer_kappaElement_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar := by
  intro k hk hk1
  -- `⟨k⟩ ≤ K`.
  have hzk : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
  -- A prime `p ∣ |k|` and an element `v ∈ ⟨k⟩` of order `p`.
  have hord1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpk⟩ := (orderOf k).exists_prime_and_dvd hord1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpcard : p ∣ Nat.card ↥(Subgroup.zpowers k) := by rw [Nat.card_zpowers]; exact hpk
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hpcard
  -- `X = ⟨v⟩` is rank-one elementary abelian and `X ≤ K`.
  set X : Subgroup G := Subgroup.zpowers (v : G) with hXdef
  have hXcard : Nat.card ↥X = p := by
    rw [hXdef, Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.zpowers k).subtype_injective v).trans hv
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXzk : X ≤ Subgroup.zpowers k := by rw [hXdef]; exact Subgroup.zpowers_le.mpr v.2
  have hXK : X ≤ K := hXzk.trans hzk
  -- Proposition 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`.
  obtain ⟨_, _, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp X hXelem hXK
  -- `C_G(k) ≤ C_G(X)`: everything centralizing `k` centralizes `⟨k⟩ ⊇ X`.
  have hCkX : Subgroup.centralizer ({k} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hkCg : k ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) :=
      (Subgroup.zpowers_le.mpr hkCg) (hXzk hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp hyCg
  -- Forward `M ⊓ C_G(k) ≤ K ⊔ K*` via `C_G(k) ≤ C_G(X) ≤ N_G(X)`.
  have hfwd : M ⊓ Subgroup.centralizer ({k} : Set G) ≤ K ⊔ Kstar := by
    rw [← hNX]
    exact le_inf
      (inf_le_right.trans (hCkX.trans (Subgroup.centralizer_le_normalizer (X : Set G)))) inf_le_left
  -- Reverse `K ⊔ K* ≤ M ⊓ C_G(k)`.
  have hrev : K ⊔ Kstar ≤ M ⊓ Subgroup.centralizer ({k} : Set G) := by
    refine sup_le (le_inf hKM ?_) ?_
    · -- `K ≤ C_G(k)`: `K` cyclic ⟹ `K ≤ C_G(K) ≤ C_G(k)` (`k ∈ K`).
      exact le_trans (Subgroup.le_centralizer K)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk))
    · -- `K* ≤ M_σ ≤ M` and `K* ≤ C_G(K) ≤ C_G(k)`.
      rw [hKstar]
      exact le_inf (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
        (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk)))
  exact le_antisymm hfwd hrev

/-- **σ-part of a κ-branch element lies in `K*`** (the `Ks_y` step of κ→Ẑ): for a type-`P`
maximal `M`, a `σ(M)`-element `y` that centralizes a nonidentity `κ`-Hall element `y' ∈ K^#` lies
in `K* = M_σ ⊓ C_G(K)`.  Chain: `y ∈ M ⊓ C_G(y') = K ⊔ K*` (`typeP_centralizer_kappaElement_eq`,
conjunct (d)); since `K ⊔ K*` is cyclic (`typeP_Z_isCyclic`), `y` centralizes `K`
(`mem_centralizer_of_mem_sup_isCyclic`); with `y ∈ M_σ` this gives `y ∈ K*`. -/
theorem typeP_sigmaElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy'K : y' ∈ K) (hy'1 : y' ≠ 1)
    (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y ∈ Kstar := by
  haveI hcycZ : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI hcycK : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  have hyM : y ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hyMsigma
  have hyMC : y ∈ M ⊓ Subgroup.centralizer ({y'} : Set G) := Subgroup.mem_inf.mpr ⟨hyM, hcent⟩
  rw [typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU y' hy'K hy'1] at hyMC
  rw [hKstar]
  exact Subgroup.mem_inf.mpr ⟨hyMsigma, mem_centralizer_of_mem_sup_isCyclic hcycZ hyMC⟩

/-- **κ→Ẑ membership, core** (the `y'∈K` form): for a type-`P` maximal `M`, a nonidentity
`σ(M)`-element `y` and a nonidentity `κ`-Hall element `y' ∈ K^#` that commute have product
`y · y' ∈ Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`.  Combines `typeP_sigmaElement_mem_Kstar` (`y ∈ K*`) with
`mem_zTilde_of_mul` (using `K ⊓ K* = ⊥`, `kappaHall_inf_Kstar_eq_bot`).  The general κ-branch
element (Coq `mFT_partition` part 2) reduces to this by conjugating its `κ`-element into `K`. -/
theorem kappa_branch_mem_zTilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'K : y' ∈ K)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y * y' ∈ zTilde K Kstar :=
  mem_zTilde_of_mul (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)
    (typeP_sigmaElement_mem_Kstar hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hyMsigma hy'K hy'1 hcent)
    hy1 hy'K hy'1

/-- **κ→Ẑ membership, general form**: lifts `kappa_branch_mem_zTilde` to a `κ(M)`-element `y'` not
necessarily in the chosen Hall `K`, via conjugation.  Since `⟨y'⟩` is a `κ(M)`-subgroup of `M`, an
`a ∈ M` conjugates it into `K` (`exists_conj_smul_le_of_isHall`); then `aᵃ • (y · y')` lies in `Ẑ`
(applying the core to `aᵃ • y ∈ M_σ` and `aᵃ • y' ∈ K`), so `y · y' ∈ 𝒞_G(Ẑ)`.  This is the
κ-branch → `𝒞_G(Ẑ)` step of the NonType-I `G^#` cover (Coq `mFT_partition` part 2). -/
theorem kappa_branch_mem_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'M : y' ∈ M)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G))
    (hy'kappa : OddOrder.GroupTheory.IsPiElement (kappa M) y') :
    y * y' ∈ conjClassSet (zTilde K Kstar) := by
  classical
  -- `⟨y'⟩` is a `κ(M)`-subgroup of `M`; conjugate it into `K`.
  have hcloseM : Subgroup.closure ({y'} : Set G) ≤ M := by
    rw [Subgroup.closure_le]; exact Set.singleton_subset_iff.mpr hy'M
  have hcard : Nat.card ↥((Subgroup.closure ({y'} : Set G)).subgroupOf M) = orderOf y' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcloseM).toEquiv,
      ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hclosepi : Ch03.Subgroup.IsPiGroup (kappa M)
      ((Subgroup.closure ({y'} : Set G)).subgroupOf M) := fun p hp =>
    hy'kappa p (by rwa [hcard] at hp)
  obtain ⟨a, haM, hale⟩ := exists_conj_smul_le_of_isHall hG hM hKM hK hcloseM hclosepi
  have hay'K : MulAut.conj a • y' ∈ K :=
    hale (Subgroup.smul_mem_pointwise_smul y' (MulAut.conj a) _
      (Subgroup.subset_closure (Set.mem_singleton y')))
  -- `aᵃ • y ∈ M_σ`.
  have hMsigmaFix : MulAut.conj a • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [← Msigma_conj_smul, Subgroup.conj_smul_eq_self_of_mem haM]
  have hayMsigma : MulAut.conj a • y ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    hMsigmaFix ▸ Subgroup.smul_mem_pointwise_smul y (MulAut.conj a) _ hyMsigma
  have hay1 : MulAut.conj a • y ≠ 1 := fun h => hy1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  have hay'1 : MulAut.conj a • y' ≠ 1 := fun h => hy'1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  -- `aᵃ • y` centralizes `aᵃ • y'`.
  have haycent : MulAut.conj a • y ∈ Subgroup.centralizer ({MulAut.conj a • y'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, MulAut.smul_def, MulAut.smul_def, ← map_mul, ← map_mul]
    exact congrArg (MulAut.conj a) (Subgroup.mem_centralizer_iff.mp hcent y' (Set.mem_singleton y'))
  -- `aᵃ • (y·y') = (aᵃ • y)·(aᵃ • y') ∈ Ẑ`, so `y·y' ∈ 𝒞_G(Ẑ)`.
  have hzin : MulAut.conj a • (y * y') ∈ zTilde K Kstar := by
    rw [MulAut.smul_def, map_mul, ← MulAut.smul_def, ← MulAut.smul_def]
    exact kappa_branch_mem_zTilde hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hayMsigma hay1 hay'K hay'1 haycent
  exact ⟨MulAut.conj a • (y * y'), hzin, a⁻¹, by
    rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

/-- **κ-branch of the dichotomy → `𝒞_G(Ẑ)`**: the κ branch of `sigma_decomposition_dichotomy`
(`y` with `ℓ_σ(y)=1`, a maximal `N ∈ 𝓜_σ(y)`, `y⁻¹g ∈ (C_N[y])^#` a `κ(N)`-element) places `g`
in `𝒞_G(Ẑ)` for the type-`P` neighbour `N`'s exceptional subgroup `Ẑ`.  `N` is type-`P` (it has a
`κ`-element), so `exists_typeP_data`/`exists_partner` supply its Theorem 14.7 data, and
`kappa_branch_mem_conjClassSet_zTilde` finishes (`y · (y⁻¹g) = g`).  This is the κ branch of the
NonType-I `G^#` cover (Coq `mFT_partition` part 2). -/
theorem kappa_branch_dichotomy_mem_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {y g : G}
    (hyl : D.length y = 1) {N : Subgroup G}
    (hNmem : N ∈ maximalSigmaSubgroupsOfElement y)
    (hsharp : y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)))
    (hkappa : OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) :
    ∃ K Kstar : Subgroup G, g ∈ conjClassSet (zTilde K Kstar) := by
  obtain ⟨hNmax, hyNsigma⟩ := hNmem
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hyl).1
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_inf] at hsharp
  obtain ⟨⟨hy'N, hy'cent⟩, hy'1⟩ := hsharp
  have hycent : y ∈ Subgroup.centralizer ({y⁻¹ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hy'cent y (Set.mem_singleton y)).symm
  have hNP : IsTypeP N := by
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    exact ⟨p, hkappa p hp⟩
  obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hNmax
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hNmax hNP hKM hK hKstar hU
  refine ⟨K, Kstar, ?_⟩
  have hmem := kappa_branch_mem_conjClassSet_zTilde hG D hNmax hNP hKM hK hKstar hU hMstarmem
    hMstarne hpart hyNsigma hy1 hy'N hy'1 hycent hkappa
  rwa [mul_inv_cancel_left] at hmem

/-- **Fixed-`W` κ-branch**: the same conclusion as `kappa_branch_dichotomy_mem_conjClassSet_zTilde`,
but landing in the `Ẑ` of a *fixed* reference type-`P` maximal `Mref` (data `Kref, K*ref, Uref`)
rather than in the (existentially produced) type-`P` `N`'s own `Ẑ`.  The dichotomy's `N` is type-`P`,
so `conjClassSet_zTilde_eq_fixed_of_isTypeP` (fix-`W`) absorbs `N`'s `Ẑ` into `Ẑ(Mref)`. -/
theorem kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {y g : G} (hyl : D.length y = 1) {N : Subgroup G}
    (hNmem : N ∈ maximalSigmaSubgroupsOfElement y)
    (hsharp : y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)))
    (hkappa : OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) :
    g ∈ conjClassSet (zTilde Kref Kstarref) := by
  obtain ⟨hNmax, hyNsigma⟩ := hNmem
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hyl).1
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_inf] at hsharp
  obtain ⟨⟨hy'N, hy'cent⟩, hy'1⟩ := hsharp
  have hycent : y ∈ Subgroup.centralizer ({y⁻¹ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hy'cent y (Set.mem_singleton y)).symm
  have hNP : IsTypeP N := by
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    exact ⟨p, hkappa p hp⟩
  obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hNmax
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hNmax hNP hKM hK hKstar hU
  have hmem : g ∈ conjClassSet (zTilde K Kstar) := by
    have h := kappa_branch_mem_conjClassSet_zTilde hG D hNmax hNP hKM hK hKstar hU hMstarmem
      hMstarne hpart hyNsigma hy1 hy'N hy'1 hycent hkappa
    rwa [mul_inv_cancel_left] at h
  rwa [conjClassSet_zTilde_eq_fixed_of_isTypeP hG hMref hMPref hKMref hKref hKstarref hUref
    hNmax hNP hKM hK hKstar] at hmem

/-- **`G^#` cover dichotomy** (the `⊆` of BG Corollary 14.9's `G^#` partition, both cases): every
`g ≠ 1` lies in `𝒞_G(M̃)` for some maximal `M`, *or* in `𝒞_G(Ẑ)` for some exceptional pair `(K, K*)`.
Immediate from `sigma_decomposition_dichotomy`: the signalizer branch gives `g ∈ M̃`
(`mem_Mtilde_of_mem_coset`), the κ branch gives `g ∈ 𝒞_G(Ẑ)`
(`kappa_branch_dichotomy_mem_conjClassSet_zTilde`).  Unlike `exists_mem_conjClassSet_Mtilde_of_ne_one`
this needs no all-type-`F` hypothesis — it covers the κ branch with the `Ẑ` piece. -/
theorem exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {g : G} (hg : g ≠ 1) :
    (∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M))
    ∨ (∃ K Kstar : Subgroup G, g ∈ conjClassSet (zTilde K Kstar)) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact Or.inl ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · exact Or.inr (kappa_branch_dichotomy_mem_conjClassSet_zTilde hG D hyl hNmem hsharp hκ)

/-- **Fixed-`W` `G^#` cover** (the form BG Corollary 14.9 / the NonTypeICovering struct needs):
every `g ≠ 1` lies in `𝒞_G(M̃)` for some maximal `M`, or in `𝒞_G(Ẑ)` for the *fixed* exceptional
`Ẑ = zTilde Kref K*ref` of a reference type-`P` maximal `Mref`.  Same as
`exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`, but the κ branch is collapsed onto the single
fixed `Ẑ` via `kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde`. -/
theorem exists_mem_conjClassSet_Mtilde_or_fixed_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {g : G} (hg : g ≠ 1) :
    (∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M))
    ∨ g ∈ conjClassSet (zTilde Kref Kstarref) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact Or.inl ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · exact Or.inr (kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde hG D hMref hMPref hKMref
      hKref hKstarref hUref hyl hNmem hsharp hκ)

/-- **BG Theorem A(4)** (mmd L4279): `C_U(k) = 1` for `k ∈ K#` — the `(κ(M) ∪ σ(M))'`-Hall
complement `U` meets each `M`-centralizer `C_M(k) = K ⊔ K*` trivially.

**Faithfulness (issue 8017).** BG states A(4) for the *`K`-invariant* complement `U`, but the
conclusion holds for **every** `(κ ∪ σ)'`-Hall `U ≤ M`: by `typeP_centralizer_kappaElement_eq`,
`U ⊓ C_G(k) = U ⊓ (M ⊓ C_G(k)) = U ⊓ (K ⊔ K*)`, and `|U|` (a `(κ ∪ σ)'`-number) is coprime to
`|K ⊔ K*| = |K|·|K*|` (a `(κ ∪ σ)`-number, `K` Hall `κ`, `K* ≤ M_σ` Hall `σ`), so the intersection
is trivial.  No `K`-invariance of `U` is needed; the bug-suspect conjunct is faithful as stated. -/
theorem typeP_hall_inf_centralizer_kappaElement_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  intro k hk hk1
  -- `C_M(k) = K ⊔ K*`, hence `U ⊓ C_G(k) = U ⊓ (K ⊔ K*)` (`U ≤ M`).
  have hCM := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU k hk hk1
  have hstep : U ⊓ Subgroup.centralizer ({k} : Set G) = U ⊓ (K ⊔ Kstar) := by
    rw [← hCM, ← inf_assoc, inf_eq_left.mpr hUM]
  rw [hstep]
  -- `|U|` and `|K ⊔ K*| = |K|·|K*|` are coprime: `(κ∪σ)'` vs `κ∪σ`.
  apply Subgroup.inf_eq_bot_of_coprime
  have hcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
    card_kappaHall_sup_Kstar hKM hK hKstar
  refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
  · -- `|U|` is a `(κ∪σ)'`-number.
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  · -- every prime of `|K ⊔ K*|` lies in `κ ∪ σ`.
    intro p hp hpcompl
    rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
    rcases Finset.mem_union.mp hp with hpK | hpKstar
    · exact hpcompl (Or.inl (hK.1 p (by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv])))
    · refine hpcompl (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKstar_le_Mσ) Nat.card_pos.ne' hpKstar

/-- **`M_σ ∩ M* = K*`** (BG Theorem 14.7(d) kernel, Coq `defMsMstar`): for a type-`P₂` maximal
`M` with `κ`-Hall `K`, `K* = M_σ ⊓ C(K)`, and the dual partner `M*` (`K ≤ M*_σ`, `K* ≤ M*`, `M`
not conjugate to `M*`), the intersection `M_σ ⊓ M*` equals `K*`.

`⊇` is immediate (`K* ≤ M_σ`, `K* ≤ M*`).  For `⊆`: any `y ∈ M_σ ⊓ M*` has `⁅⟨y⟩, K⁆ ≤ M_σ`
(`K ≤ M ≤ N(M_σ)`, `y ∈ M_σ`) and `⁅⟨y⟩, K⁆ ≤ M*_σ` (`K ≤ M*_σ ◁ M*`, `y ∈ M* ≤ N(M*_σ)`), so
`⁅⟨y⟩, K⁆ ≤ M_σ ⊓ M*_σ = ⊥` (Lemma 10.12, `M_σ` nilpotent for type-`P₂`); hence `y` centralizes
`K`, i.e. `y ∈ M_σ ⊓ C(K) = K*`.  Avoids the embedding's σ(M)-Hall-of-M* clause. -/
private theorem msigma_inf_partner_eq_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMstarmax : Mstar ∈ maximalSubgroups G)
    (hKMsigmaMstar : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar) (hKstarMstar : Kstar ≤ Mstar)
    (hnc : ¬ IsConjugateSubgroup M Mstar) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar := by
  classical
  -- `M_σ` nilpotent (type-`P₂`) ⟹ `M_σ ⊓ M*_σ = ⊥` (Lemma 10.12).
  have hdisj : OddOrder.BG.Ch3.S10.Msigma M ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = ⊥ :=
    ((OddOrder.BG.Ch3.S10.disjoint_of_not_conj hG hM hMstarmax (fun h => hnc h)).2
      (msigma_isNilpotent_of_isTypeP2 hG hM hP2)).1
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMstarN : Mstar ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma Mstar : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma Mstar) Mstar
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyMσ, hyMstar⟩ := hy
    rw [hKstar, Subgroup.mem_inf]
    refine ⟨hyMσ, ?_⟩
    have hcle : (⁅Subgroup.zpowers y, K⁆ : Subgroup G) ≤ ⊥ := by
      rw [← hdisj, le_inf_iff]
      refine ⟨Subgroup.commutator_le.mpr ?_, Subgroup.commutator_le.mpr ?_⟩
      · intro a ha k hk
        have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := (Subgroup.zpowers_le.mpr hyMσ) ha
        have hkN := (Subgroup.mem_normalizer_iff.mp (hMN (hKM hk))) a⁻¹
        rw [commutatorElement_def]
        have hconj : k * a⁻¹ * k⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := hkN.mp (inv_mem haMσ)
        have : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
        rw [this]; exact mul_mem haMσ hconj
      · intro a ha k hk
        have haMstarσ : a ∈ Mstar := (Subgroup.zpowers_le.mpr hyMstar) ha
        have hkMσstar : k ∈ OddOrder.BG.Ch3.S10.Msigma Mstar := hKMsigmaMstar hk
        rw [commutatorElement_def]
        have hconj : a * k * a⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
          (Subgroup.mem_normalizer_iff.mp (hMstarN haMstarσ) k).mp hkMσstar
        have : a * k * a⁻¹ * k⁻¹ = (a * k * a⁻¹) * k⁻¹ := by group
        rw [this]; exact mul_mem hconj (inv_mem hkMσstar)
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcle
    exact hcle (Subgroup.mem_zpowers y)
  · exact le_inf (hKstar ▸ inf_le_left) hKstarMstar

/-- **The partner intersection `ziMMst` and `K`-uniqueness `sK_uniqMst`** (BG Theorem 14.7,
embedding internals), assembled here for the type-`F` classification of Corollary 14.12.

Applying `typeP_structure` to the partner `M*` (whose `κ`-Hall is `K*`, with `K = M*_σ ⊓ C(K*)`):
the `b1` clause at a characteristic order-`p` line of the cyclic `K*` gives `N_{M*}(K*) = K* ⊔ K`,
whence (via `M_σ ⊓ M* = K*`, here `hMsMst`) `M ⊓ M* = K ⊔ K*`; and the `K`-TI clause gives
`K ≤ M*^a ⟹ a ∈ M*`.  Mirrors Coq `Ptype_embedding`'s `ziMMst`/`sK_uniqMst` (BGsection14.v L1820,
L2278). -/
private theorem partner_inf_and_uniq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hMstmax : Mstar ∈ maximalSubgroups G) (hMstP : IsTypeP Mstar)
    (hKstarMst : Kstar ≤ Mstar)
    (hKstar_hall : Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar))
    (hK_eq : K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G))
    (hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar)
    (hKM : K ≤ M) (hKstarM : Kstar ≤ M)
    (hZcyc : IsCyclic ↥(K ⊔ Kstar)) (hKstarNe : Kstar ≠ ⊥) (hKNe : K ≠ ⊥)
    (hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar) :
    M ⊓ Mstar = K ⊔ Kstar ∧ (∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) := by
  classical
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstmax
  haveI := hZcyc
  -- A Hall `(κ(M*) ∪ σ(M*))'`-subgroup of `M*`, to feed `typeP_structure`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  have hstruct := typeP_structure hG hMstmax hMstP hKstarMst hKstar_hall hK_eq hU_Mstar
  -- `b1`: `N_G(X) ⊓ M* = K* ⊔ K` for rank-one `X ≤ K*`; TI: `g ∉ M* → K ⊓ M*^g = ⊥`.
  have hb1 := hstruct.2.2.1
  have hTI := hstruct.2.2.2.1
  -- `K ≤ C(K*)` (`Z = K ⊔ K*` cyclic ⟹ abelian).
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hkZ : k ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_left hk
    have hsZ : s ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_right hs
    exact congrArg Subtype.val (mul_comm (⟨s, hsZ⟩ : ↥(K ⊔ Kstar)) (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)))
  -- A characteristic order-`p` line `X ≤ K*` (cyclic `K*`).
  haveI hKstarcyc : IsCyclic ↥Kstar :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : Kstar ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥Kstar ≠ 1 from fun h => hKstarNe (Subgroup.card_eq_one.mp h))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Kstar) p hpd
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hxord : orderOf (x : G) = p :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x).trans hx
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord]
  have hXKstar : X ≤ Kstar := by rw [hXdef, Subgroup.zpowers_le]; exact x.2
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hNKstarX : Subgroup.normalizer (Kstar : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    haveI : (X.subgroupOf Kstar).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro g hg
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := Kstar) (C := X.subgroupOf Kstar) hg
    rwa [Subgroup.map_subgroupOf_eq_of_le hXKstar] at hmem
  -- `N_{M*}(K*) = K* ⊔ K = K ⊔ K*`.
  have hNMst : Subgroup.normalizer (Kstar : Set G) ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ ?_
    · calc Subgroup.normalizer (Kstar : Set G) ⊓ Mstar
          ≤ Subgroup.normalizer (X : Set G) ⊓ Mstar := inf_le_inf hNKstarX le_rfl
        _ = Kstar ⊔ K := hb1 p hp X hXelem hXKstar
        _ = K ⊔ Kstar := sup_comm _ _
    · refine le_inf (sup_le (hKcKstar.trans (Subgroup.centralizer_le_normalizer (Kstar : Set G)))
        Subgroup.le_normalizer) ?_
      exact sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst
  -- `ziMMst`: `M ⊓ M* = K ⊔ K*`.
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hziMMst : M ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ (le_inf (sup_le hKM hKstarM)
      (sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst))
    have hsub : M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) := by
      rw [← hMsMst]
      exact le_normalizer_inf (inf_le_left.trans hMN) (inf_le_right.trans Subgroup.le_normalizer)
    calc M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) ⊓ Mstar := le_inf hsub inf_le_right
      _ = K ⊔ Kstar := hNMst
  -- `sK_uniqMst`: `K ≤ M*^a ⟹ a ∈ M*`.
  refine ⟨hziMMst, fun a hKa => ?_⟩
  by_contra haMst
  exact hKNe (le_bot_iff.mp ((hTI a haMst) ▸ le_inf le_rfl hKa))

/-- **BG `defUK`** (Coq `P2type_signalizer`, BGsection14.v L2329): for a type-`P₂` maximal
subgroup `M` with cyclic Hall `κ(M)`-subgroup `K` and abelian `(κ(M) ∪ σ(M))'`-Hall complement
`U` normalized by `K`, the commutator `⁅U, K⁆` equals `U`.

The coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆` (`fitting_coprime_abelian_decomp`: `U`
abelian, `K ≤ N(U)`, `gcd(|U|,|K|) = 1`) collapses because `C_U(K) = C(K) ⊓ U = ⊥`.  Indeed
Theorem A(4) (`typeP_hall_inf_centralizer_kappaElement_eq_bot`) gives `U ⊓ C(k) = ⊥` for every
`k ∈ K#`, and `C(K) ⊓ U ≤ C(k) ⊓ U` for any such `k` (one exists since `K ≠ ⊥`).  `K` is cyclic
of prime order `q = |K|` by Proposition 14.2(g) (type-`P₂`). -/
theorem typeP2_kappaHall_commutator_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    (⁅U, K⁆ : Subgroup G) = U := by
  classical
  have hP : IsTypeP M := hP2.1
  -- `|K| = q` is prime (Prop 14.2(g) for type-`P₂`), so `K` is cyclic.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hKne
  -- `C(K) ⊓ U = ⊥` from Theorem A(4) at `k₀ ∈ K#` (`C(K) ⊓ U ≤ C(k₀) ⊓ U = U ⊓ C(k₀) = ⊥`).
  have hCUK_bot : Subgroup.centralizer (K : Set G) ⊓ U = ⊥ := by
    have hA4 := typeP_hall_inf_centralizer_kappaElement_eq_bot hG hM hP hKM hUM hK hKstar hU
      k₀ hk₀K hk₀ne
    rw [eq_bot_iff, ← hA4]
    exact le_inf inf_le_right
      (inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk₀K)))
  -- Coprime `|U|` (a `(κ∪σ)'`-number) and `|K|` (a `κ ⊆ κ∪σ` number).
  have hcopUK : Nat.Coprime (Nat.card ↥U) (Nat.card ↥K) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p _ => hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]))
      (fun p _ hpc => hpc (Or.inl (hK.1 p
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]))))
  -- Collapse the coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆`.
  haveI hUcomm_inst : IsMulCommutative ↥U :=
    ⟨⟨fun a b => Subtype.ext (hUab (a : G) a.2 (b : G) b.2)⟩⟩
  have hd := (OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := U) (K := K) hKNU hcopUK).2
  rwa [hCUK_bot, bot_sup_eq] at hd


/-- **Type-`P₂` is conjugation-invariant**. -/
theorem isTypeP2_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP2 (MulAut.conj g • M) ↔ IsTypeP2 M := by
  unfold IsTypeP2
  rw [kappa_conj_smul, sigmaComplementPrimes_conj_smul, isTypeP_conj_smul]

/-- In a finite nilpotent subgroup `N`, a subgroup `P ≤ N` that is self-normalizing in `N`
(`N_G(P) ⊓ N ≤ P`) must be all of `N` — the normalizer condition: proper subgroups of a
nilpotent group grow under normalization.  Generalizes `sylow_coe_eq_of_normalizer_inf_le`
(`P` need not be Sylow, only `N` nilpotent). -/
private theorem eq_of_isNilpotent_normalizer_inf_le [Finite G] {N P : Subgroup G}
    (hN : Group.IsNilpotent ↥N) (hPN : P ≤ N)
    (hle : Subgroup.normalizer (P : Set G) ⊓ N ≤ P) : N = P := by
  haveI : Group.IsNilpotent ↥N := hN
  have hnc : NormalizerCondition ↥N := Group.normalizerCondition_of_isNilpotent
  have hself : Subgroup.normalizer (P.subgroupOf N) = P.subgroupOf N := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPN]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_) <;>
      rw [Subgroup.mem_subgroupOf] at hx ⊢
    · exact hle ⟨hx, x.2⟩
    · exact P.le_normalizer hx
  have htop : P.subgroupOf N = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hPN

/-- **BG Corollary 14.12** (mmd L4035): for `M ∈ 𝓜_{P₂}` with `K`, `M*`, `K*` as in
Theorem 14.7 and `U` as in Proposition 14.2(a), `r ∈ π(U)`, `R` the Sylow `r`-subgroup of the
abelian `U`, and `H ∈ 𝓜(N_G(R))`: then `H ∈ 𝓜_F`, `U ⊆ H_σ`, `M ∩ H = U K`, `N_H(U) ⊄ M`,
`K ⊆ F(H ∩ M*)`, and `H ∩ M*` complements `H_σ` in `H`.

**Faithfulness (2026-06-22):** the hypotheses are tightened to BG — `U` is the specific
abelian Hall `(κ(M) ∪ σ(M))'`-factor of Proposition 14.2(a) and `R` is a *Sylow* `r`-subgroup
of `U` (`IsHallSubgroup {r}`), not an arbitrary `U ≤ M`, `R ≤ U` with `R ≠ ⊥` (under which the
conclusion fails).  The conclusion now also delivers `N_H(U) ⊄ M` (the FT-path clause consumed by
BG Theorem C(1) = `theoremC_paired_structure` conjunct 2): `N_H(U) = H ⊓ N_G(U) ≤ N_G(U)`, so
`N_H(U) ⊄ M ⟹ N_G(U) ⊄ M`.  The two remaining BG clauses `K ⊆ F(H ∩ M*)` and `σ(H)'-Hall(H)(H ∩ M*)`
(which require exposing the dual partner `M*` in the signature) are not consumed by any caller and
are omitted; the proof establishes `H ∩ M* = D` internally, so they are derivable if needed.
Translates the Coq `P2type_signalizer` (BGsection14.v L2243).  See `notes/bg/s14_typeP_counting.md`.
-/
theorem typeP2_neighbor_is_typeF_of_mem [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R H : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) ∧
      ∃ E E₁ E₂ E₃ : Subgroup G,
        OddOrder.BG.Ch3.S12.SubgroupESetup H E E₁ E₂ E₃ ∧ K ≤ E ∧
          K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  have hP : IsTypeP M := hP2.1
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `r ∉ σ(M)`: `r ∈ π(U)` and `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M`.
  have hrU' : r ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 r hrU'
  have hrσM : r ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hrκσ (Or.inr h)
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right
        hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- Setup: the dual partner `M*` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- `H ∈ 𝓜(N_G(R))` is now a hypothesis (`hH`); extract maximality and `N_G(R) ≤ H`.
  obtain ⟨hHmax, hNRH⟩ := mem_maximalSubgroupsContaining.mp hH
  -- `R ≤ H` (from `N_G(R) ≤ H`).
  have hRH : R ≤ H := (Subgroup.le_normalizer).trans hNRH
  -- `K ≤ H` (Coq `sEH`/`sKH`): `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow
  -- `r`-subgroup), so `K ≤ N(U) ⟹ K ≤ N(R) ≤ H`.  Uses the `kappa_complement` structure
  -- (`group_set (U*K)`, here `hKNU : K ≤ N(U)`).
  have hUcomm : ∀ a b : ↥U, a * b = b * a := fun a b =>
    Subtype.ext (hUab (a : G) a.2 (b : G) b.2)
  -- `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow `r`-subgroup), shared by
  -- `hKH`/`hUH`: `K, U ≤ N(U) ⟹ ≤ N(R) ≤ H`.
  have hRcardU : Nat.card ↥(R.subgroupOf U) = r ^ (Nat.card ↥U).factorization r := by
    have hpow : Nat.card ↥(R.subgroupOf U)
        = r ^ (Nat.card ↥(R.subgroupOf U)).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    have hfact : (Nat.card ↥U).factorization r
        = (Nat.card ↥(R.subgroupOf U)).factorization r := by
      have hidx : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidx, add_zero]
    rw [hfact]; exact hpow
  have hRUnorm : (R.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hUcomm g n]
        _ = n := by group
    rw [heq]; exact hn
  haveI hPchar : (R.subgroupOf U).Characteristic := by
    have hPn : ((Sylow.ofCard (R.subgroupOf U) hRcardU : Sylow r ↥U) : Subgroup ↥U).Normal := by
      rw [Sylow.coe_ofCard]; exact hRUnorm
    have h := Sylow.characteristic_of_normal (Sylow.ofCard (R.subgroupOf U) hRcardU) hPn
    rwa [Sylow.coe_ofCard] at h
  have hKH : K ≤ H := fun k hk => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (hKNU hk)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  have hUH : U ≤ H := fun u hu => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (Subgroup.le_normalizer hu)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  -- `H` is not conjugate to `M` (`r ∈ σ(H) ∖ σ(M)`) nor to its partner `M*` (coprime `K`/`R`).
  -- These two non-conjugacies drive both the type-`F` classification and `σ(H)'`-membership of `K`.
  have notMGH : ¬ IsConjugateSubgroup H M := by
    rintro ⟨a, ha⟩
    -- `|R| = r ^ (|U|).factorization r` (`R` is a Sylow `r`-subgroup of `U`).
    have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
    have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext
      intro q
      rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    -- `(|U|).factorization r = (|R|).factorization r` (`r ∤ [U : R]`).
    have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
      have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxU, add_zero, hSU]
    -- `(|U|).factorization r = (|M|).factorization r` (`r ∤ [M : U]`).
    have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
      have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrκσ)
      have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
      have hlag := Subgroup.card_mul_index (U.subgroupOf M)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxM, add_zero, hUcard]
    -- `|H| = |M|` (conjugate subgroups).
    have hcardHM : Nat.card ↥H = Nat.card ↥M := by
      rw [← ha]; exact (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
    -- `R` is a Sylow `r`-subgroup of `H`.
    have hRsylH : Nat.card ↥(R.subgroupOf H) = r ^ (Nat.card ↥H).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv, hcardHM, ← hfUM, hfUR]
      exact hRpow
    -- `r ∈ σ(H)` (`R` Sylow `r` of `H`, `N_G(R) ≤ H`), hence `r ∈ σ(M)` (conjugacy), contradiction.
    have hrH : r ∈ (Nat.card ↥H).primeFactors := by
      rw [hcardHM]
      exact Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hrσH : r ∈ OddOrder.BG.Ch3.S10.sigma H := by
      rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
      refine ⟨hrH, Sylow.ofCard (R.subgroupOf H) hRsylH, ?_⟩
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hRH]
      exact hNRH
    exact hrσM (by have h := OddOrder.BG.Ch3.S10.sigma_conj (M := H) a hrσH; rwa [ha] at h)
  have notMstGH : ¬ IsConjugateSubgroup H Mst := by
    -- `M_σ ∩ M* = K*` (the embedding's conjunct (d) kernel, avoiding the σ(M)-Hall-of-M* clause).
    have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
      (le_of_eq hMstpair.2.2).trans inf_le_left
    have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
      msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
    have hKstarM : Kstar ≤ M := by
      rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
    have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
    -- `ziMMst : M ⊓ M* = K ⊔ K*` and `sK_uniqMst : K ≤ M*^a ⟹ a ∈ M*`.
    obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
      hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
    -- `r ∤ |Z|`: `Z = K ⊔ K* = K · K*` (disjoint, commuting), `r ∉ π(K) ⊆ κ(M)`, `r ∉ π(K*) ⊆ σ(M)`.
    have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
      kappaHall_isPiSubgroup_sigmaCompl hKM hK
    have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
      Kstar_isPiSubgroup_sigma hKstardef
    have hrnK : ¬ r ∣ Nat.card ↥K := fun hd => (fun h => hrκσ (Or.inl h))
      (hK.1 r (Nat.mem_primeFactors.mpr ⟨hrprime, by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]; exact hd, Nat.card_pos.ne'⟩))
    have hrnKstar : ¬ r ∣ Nat.card ↥Kstar := fun hd =>
      hrσM (hKstarπ r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Nat.card_pos.ne'⟩))
    have hKKstar_bot : K ⊓ Kstar = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpσc := hKπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
      have hpσ := hKstarπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact hpσc hpσ
    have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
      haveI := hZcyc
      letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (mul_comm (⟨s, Subgroup.mem_sup_right hs⟩ : ↥(K ⊔ Kstar))
        (⟨k, Subgroup.mem_sup_left hk⟩))
    have hcardZ : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint
        (hKcKstar.trans (Subgroup.centralizer_le_normalizer _)) hKKstar_bot
    have hrnZ : ¬ r ∣ Nat.card ↥(K ⊔ Kstar) := by
      rw [hcardZ]; exact fun hd => (hrprime.dvd_mul.mp hd).elim hrnK hrnKstar
    have hrR : r ∣ Nat.card ↥R := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
        (show Nat.card ↥R ≠ 1 from fun h => hRne (Subgroup.card_eq_one.mp h))
      have hpmem : p ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv]; exact hpd, Nat.card_pos.ne'⟩
      exact (Set.mem_singleton_iff.mp (hR.1 p hpmem)) ▸ hpd
    -- If `H` were conjugate to `M*`, then `K ≤ H` and `sK_uniqMst` force `H = M*`, so
    -- `R ≤ M ⊓ M* = Z`, whence `r ∣ |Z|`, contradicting `r ∤ |Z|`.
    rintro ⟨a, ha⟩
    have hHeq : H = MulAut.conj a⁻¹ • Mst := by
      rw [← ha, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have haInvMst : a⁻¹ ∈ Mst := hsKuniq a⁻¹ (hHeq ▸ hKH)
    have hHMst : H = Mst := hHeq.trans (Subgroup.conj_smul_eq_self_of_mem haInvMst)
    have hRZ : R ≤ K ⊔ Kstar := hziMMst ▸ le_inf hRM (hHMst ▸ hRH)
    exact hrnZ (hrR.trans (Subgroup.card_dvd_of_le hRZ))
  -- ═══ Shared σ-decomposition infrastructure for conjuncts 2/3/4 (Coq `P2type_signalizer`) ═══
  -- Conjunct 1 (`IsTypeF H`), hoisted (also the `hF` input to Lemma 14.11 below): every type-`P`
  -- maximal is conjugate to `M` or `M*` (`hcover`), and `H` is conjugate to neither.
  have hFmaxH : IsTypeF H := by
    show kappa H = ∅
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hHP
    exact (hcover H hHmax hHP).elim notMGH notMstGH
  -- `|K| = q` is prime (Prop 14.2(g), type-`P₂`), so `K` is cyclic of prime order.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  -- `defUK : ⁅U, K⁆ = U` (BG `defUK`).
  have defUK : (⁅U, K⁆ : Subgroup G) = U :=
    typeP2_kappaHall_commutator_eq_self hG hM hP2 hKM hUM hK hKstardef hU hUab hKNU
  -- `K ≤ M*_σ` and `K` is a `σ(H)'`-group (Thm 13.9: `σ(H) ∩ σ(M*) = ∅`, `H` not conj. to `M*`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst := hMstpair.2.2.le.trans inf_le_left
  have hHMstdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma H) (OddOrder.BG.Ch3.S10.sigma Mst) :=
    sigma_disjoint_of_nonconjugate hG hHmax hMstmax notMstGH
  have hsH_K : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ K := by
    intro p hp
    rw [Set.mem_compl_iff]
    intro hpσH
    exact (Set.disjoint_left.mp hHMstdisj) hpσH
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKMsigmaMst) Nat.card_pos.ne' hp))
  -- `E`: a `σ(H)'`-Hall (E-setup) complement of `H_σ` in `H`, containing `K` (`Hall_superset`).
  obtain ⟨E, E₁, E₂, E₃, hEsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hHmax hKH hsH_K
  -- `q = |K| ∈ σ(M*)` (`K ≤ M*_σ`).
  have hqσMst : q ∈ OddOrder.BG.Ch3.S10.sigma Mst :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst q
      (Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKMsigmaMst,
        Nat.card_pos.ne'⟩)
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`, whose dual `K*` is `K`): `typeP_structure`
  -- conjunct 6 with the rank-one `K ∈ ℰ_q¹`.
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    haveI hMstsol : IsSolvable ↥Mst := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  -- `K ⊆ F(E)` (Coq `sK_FD`): otherwise Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting`)
  -- produces a maximal `M'` with `q ∈ τ₂(M')` and `𝓜(C(K)) = {M'}` (⟹ `M' = Mst`, but
  -- `q ∈ τ₂(Mst) ∩ σ(Mst) = ∅`), or `q ∈ κ(M')` with `M'` type-`P₁` (⟹ `M' ∼ M` makes `M`
  -- type-`P₁` against `M ∈ 𝓜_{P₂}`, or `M' ∼ Mst` gives `q ∈ κ(Mst) ⊆ σ(Mst)ᶜ`).
  have hsK_FE : K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    by_contra hnotKFE
    have hqpiE : q ∈ piSet E :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKE, Nat.card_pos.ne'⟩
    obtain ⟨Mstar', hMstar'max, hdich⟩ := exists_maximal_of_typeF_notMem_fitting hG hHmax hFmaxH
      hEsetup.isComplement'_subgroupOf hEsetup.E_le hqpiE hKelemq hKE hnotKFE
    rcases hdich with ⟨hqτ2, huniq'⟩ | ⟨hqκ', hP1'⟩
    · -- Case 1: `Mstar' = Mst` (both `= 𝓜(C(K))`), but `q ∈ τ₂(Mst)` and `q ∈ σ(Mst)`.
      have hMstar'eq : Mstar' = Mst :=
        Set.singleton_eq_singleton_iff.mp (huniq'.symm.trans huniqMst)
      exact tau2_subset_sigma_compl Mst (hMstar'eq ▸ hqτ2) hqσMst
    · -- Case 2: `Mstar'` type-`P₁`; `hcover` makes it conjugate to `M` or `Mst`.
      rcases hcover Mstar' hMstar'max hP1'.1 with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact not_isTypeP1_and_isTypeP2 ⟨hb ▸ (isTypeP1_conj_smul b Mstar').mpr hP1', hP2⟩
      · refine kappa_subset_sigmaCompl (M := Mst) ?_ hqσMst
        rw [← hb, kappa_conj_smul]; exact hqκ'
  -- ═══ Conjunct 2 (`U ≤ M_σ(H)`, Coq `sUHs`), hoisted: also feeds `U ⊆ F(H)` for conjuncts 3/4 ═══
  -- `U = ⁅U,K⁆ ≤ HsDq := M_σ(H) ⊔ O_q(F(E))`, and `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
  have hUMsH : U ≤ OddOrder.BG.Ch3.S10.Msigma H := by
    classical
    -- `q ∈ κ(M)`, `q ∉ σ(H)`, and `|U|` is a `{q}'`-number.
    have hqκM : q ∈ kappa M := hK.1 q (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
      exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
      hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hUq' : ∀ p ∈ (Nat.card ↥U).primeFactors, p ∈ ({q}ᶜ : Set ℕ) := by
      intro p hp hpq
      exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
        (Or.inl ((Set.mem_singleton_iff.mp hpq) ▸ hqκM))
    -- `O_q(F(E))`, `K ≤ O_q(F(E))`, `E ≤ N(O_q(F(E)))`.
    set Oq : Subgroup G := opiCoreInG ({q} : Set ℕ)
      (OddOrder.BG.Ch2.S08.fittingInG E) with hOqdef
    have hOqE : Oq ≤ E := (opiCoreInG_le _ _).trans
      (OddOrder.BG.Ch2.S08.fittingInG_le E)
    have hKOq : K ≤ Oq := OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E) hsK_FE (IsPGroup.of_card (by rw [hKcard, pow_one]))
    have hOqpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Oq :=
      isPiSubgroup_opiCoreInG _ _
    have hEnOq : E ≤ Subgroup.normalizer (Oq : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hOqE]
      exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal _ _
    -- `HsDq := M_σ(H) ⊔ O_q(F(E))`; `M_σ(H) ◁ H`, `HsDq ≤ H`, `H ≤ N(HsDq)`.
    set HsDq : Subgroup G := OddOrder.BG.Ch3.S10.Msigma H ⊔ Oq with hHsDqdef
    have hHsDqH : HsDq ≤ H := sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) (hOqE.trans hEsetup.E_le)
    haveI hMsHnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hHnMsH : H ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le H)).mp hMsHnorm
    have hHnHsDq : H ≤ Subgroup.normalizer (HsDq : Set G) := by
      calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
        _ ≤ Subgroup.normalizer (HsDq : Set G) :=
          sup_le (le_sup_left.trans Subgroup.le_normalizer)
            (le_normalizer_sup (hEsetup.E_le.trans hHnMsH) hEnOq)
    -- `U = ⁅U,K⁆ ≤ ⁅H, HsDq⁆ ≤ HsDq` (since `HsDq ◁ H`).
    have hUHsDq : U ≤ HsDq := by
      rw [← defUK]
      refine (Subgroup.commutator_mono hUH (hKOq.trans (le_sup_right : Oq ≤ HsDq))).trans ?_
      rw [Subgroup.commutator_comm H HsDq]
      exact Ch04.commutator_le_of_le_normalizer hHnHsDq
    -- `M_σ(H) ⊓ Oq = ⊥` (`σ(H)` vs `{q}`, `q ∉ σ(H)`), so `|HsDq| = |M_σ(H)|·|Oq|`.
    have hMsOqbot : OddOrder.BG.Ch3.S10.Msigma H ⊓ Oq = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := OddOrder.BG.Ch3.S10.sigma H)
        Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
        (fun p hp hpσ => ?_)
      exact hqσ'H ((Set.mem_singleton_iff.mp (hOqpi p hp)) ▸ hpσ)
    have hcardHsDq : Nat.card ↥HsDq = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma H) * Nat.card ↥Oq := by
      have hOqnMs : Oq ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
        (hOqE.trans hEsetup.E_le).trans hHnMsH
      have h := card_sup_eq_mul_of_le_normalizer_of_disjoint hOqnMs (by rw [inf_comm]; exact hMsOqbot)
      rw [hHsDqdef, sup_comm, h, Nat.mul_comm]
    -- `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
    haveI hMsHsDqnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hHsDqH.trans hHnMsH)
    have hidxOq : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).index = Nat.card ↥Oq := by
      have hlag := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv, hcardHsDq] at hlag
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
    have hMsHall : Ch03.IsHallSubgroup ({q}ᶜ : Set ℕ)
        ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq) := by
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv] at hp
        exact fun hpq => hqσ'H ((Set.mem_singleton_iff.mp hpq) ▸
          OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
      · rw [hidxOq] at hp
        exact fun hpc => hpc (hOqpi p hp)
    have hUpi : Ch03.Subgroup.IsPiGroup ({q}ᶜ : Set ℕ) (U.subgroupOf HsDq) := by
      intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUHsDq).toEquiv] at hp
      exact hUq' p hp
    have hfinal := OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hMsHall hUpi
    have hmapped := Subgroup.map_mono (f := HsDq.subtype) hfinal
    rwa [Subgroup.map_subgroupOf_eq_of_le hUHsDq, Subgroup.map_subgroupOf_eq_of_le
      (le_sup_left : OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)] at hmapped
  -- ═══ Shared structure for conjuncts 3/4: `H_σ ⊆ F(H)` and `Fu = O_{(κ∪σ)'(M)}(F(H))` ═══
  -- `q ∉ σ(H)` (`K` is a `σ(H)'`-group, `q ∣ |K|`) and `q ∈ π(H)` (`K ≤ H`, `|K| = q`).
  have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
    hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
  have hqπH : q ∈ piSet H :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKH, Nat.card_pos.ne'⟩
  -- `H_σ ⊆ F(H)` (Coq `sHsFH`): `H` is type-`F`, so `q ∉ κ(H) = ∅`; Lemma 14.1
  -- (`msigma_structure_of_notMem_sigma_kappa`) with a maximal-rank elementary abelian `q`-subgroup
  -- of `H` makes `M_σ(H)` nilpotent, hence `≤ F(H)`.
  have hHsFH : OddOrder.BG.Ch3.S10.Msigma H ≤ OddOrder.BG.Ch2.S08.fittingInG H := by
    have hκH : kappa H = ∅ := hFmaxH
    have hqκH : q ∉ kappa H := by rw [hκH]; exact Set.notMem_empty q
    obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥H) (p := q) (n := pRank ↥H q)
      (OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hqπH) (le_refl _)
    obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
    have hjeq : j = pRank ↥H q := by
      have hsq := le_antisymm (le_pRank B hBea) hBlog
      rwa [hj, Nat.log_pow hqprime.one_lt] at hsq
    have hAmem : B.map H.subtype ∈ elemAbelianOfRank G q (pRank ↥H q) :=
      ⟨Subgroup.IsElementaryAbelian.map H.subtype_injective hBea, by
        rw [Subgroup.card_map_of_injective H.subtype_injective, hj, hjeq]⟩
    have hAH : B.map H.subtype ≤ H := Subgroup.map_subtype_le _
    haveI h1 : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    haveI h2 : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma H) :=
      (msigma_structure_of_notMem_sigma_kappa hG hHmax hqπH hqσ'H hqκH hAmem hAH).2.2
    haveI h3 : Group.IsNilpotent ↥((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
    have h4 : (OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H ≤ OddOrder.Isaacs.Ch01.fitting ↥H :=
      OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    calc OddOrder.BG.Ch3.S10.Msigma H
        = ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype := Subgroup.map_mono h4
      _ = OddOrder.BG.Ch2.S08.fittingInG H := rfl
  -- `Fu := O_{(κ(M)∪σ(M))'}(F(H))`: normal in `H`, contains `U`, and `M ⊓ Fu = U` (Coq `defU`).
  set π : Set ℕ := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ with hπdef
  set Fu : Subgroup G := opiCoreInG π (OddOrder.BG.Ch2.S08.fittingInG H) with hFudef
  haveI hFHnil : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent H
  have hUFH : U ≤ OddOrder.BG.Ch2.S08.fittingInG H := hUMsH.trans hHsFH
  have hUπ : Ch03.Subgroup.IsPiGroup π U := by
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  have hUFu : U ≤ Fu := by
    have hUFHpi : Ch03.Subgroup.IsPiGroup π (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)) :=
      Ch03.Subgroup.IsPiGroup.subgroupOf hUFH hUπ
    have hHall : Ch03.IsHallSubgroup π
        (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)) :=
      OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
    have hle : U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H) ≤
        Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
      OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall hUFHpi
    calc U = (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hUFH).symm
      _ ≤ (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype := Subgroup.map_mono hle
      _ = Fu := rfl
  have hFuH : Fu ≤ H :=
    (opiCoreInG_le _ _).trans (OddOrder.BG.Ch2.S08.fittingInG_le H)
  have hHnFu : H ≤ Subgroup.normalizer (Fu : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hFuH]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal π H
  have hdefU : M ⊓ Fu = U := by
    refine le_antisymm ?_ (le_inf hUM hUFu)
    -- `V := M ⊓ Fu` is a `π`-subgroup of `M` containing the `π`-Hall `U`, so `V = U` (cardinality).
    have hVπ : ∀ p ∈ (Nat.card ↥(M ⊓ Fu)).primeFactors, p ∈ π := by
      intro p hp
      exact (isPiSubgroup_opiCoreInG _ (OddOrder.BG.Ch2.S08.fittingInG H)) p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne' hp)
    have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Subgroup.card_mul_index _
    have hcop : Nat.Coprime (Nat.card ↥(M ⊓ Fu)) (U.subgroupOf M).index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      exact (hU.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Subgroup.index_ne_zero_of_finite⟩))
        (hVπ p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩))
    have hVdvdU : Nat.card ↥(M ⊓ Fu) ∣ Nat.card ↥U :=
      hcop.dvd_of_dvd_mul_right (hlag ▸ Subgroup.card_dvd_of_le inf_le_left)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hUM hUFu)
      (Nat.le_of_dvd Nat.card_pos hVdvdU)).symm.le
  refine ⟨hFmaxH, hUMsH, ?_, ?_, E, E₁, E₂, E₃, hEsetup, hKE, hsK_FE⟩
  · -- Conjunct 3 (`M ⊓ H = U ⊔ K`, Coq L2375-2380): `⊇` is immediate; `⊆` is
    -- `M ⊓ H ⊆ N_M(U) = U ⊔ K` (`defNMU`, BG 6.5(b): `M = M_σ ⋊ (U⊔K)`, `C_{M_σ}(U) = 1`).
    classical
    refine le_antisymm ?_ (sup_le (le_inf hUM hUH) (le_inf hKM hKH))
    -- σ-decomposition `M = M_σ ⊔ (U ⊔ K)`: the σ-Hall `M_σ`, the κ-Hall `K`, and the
    -- `(κ∪σ)'`-Hall `U` cover all primes, so the index of their join in `M` has no prime divisor.
    have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
      OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
        (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
    have hJleM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) ≤ M :=
      sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM)
    have hJM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) = M := by
      have hidx1 : ((OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M).index = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hsub : ∀ S : Subgroup G, S ≤ OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) →
            p ∈ (S.subgroupOf M).index.primeFactors := by
          intro S hSJ
          refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Subgroup.index_ne_zero_of_finite⟩
          exact hpdvd.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M hSJ))
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
          hMσHall.2 p (hsub _ le_sup_left)
        have hpκσc : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
          hU.2 p (hsub _ (le_sup_right.trans' le_sup_left))
        have hpκ : p ∉ kappa M := hK.2 p (hsub _ (le_sup_right.trans' le_sup_right))
        exact hpκσc (Set.mem_compl (fun h => h.elim hpκ hpσ))
      have htop : (OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M = ⊤ :=
        Subgroup.index_eq_one.mp hidx1
      exact le_antisymm hJleM (Subgroup.subgroupOf_eq_top.mp htop)
    -- `C_{M_σ}(U) = ⊥` (Lemma 14.1): `R` is a Sylow `r`-subgroup of `M` (`r ∈ (κ∪σ)'`, `U` Hall),
    -- so a maximal-rank elementary abelian `A ≤ R ≤ U` makes `M_σ ⊓ C(A) = ⊥`; antitonicity lifts
    -- this to `M_σ ⊓ C(U) ≤ M_σ ⊓ C(A) = ⊥`.
    have hRM : R ≤ M := hRU.trans hUM
    have hrπM : r ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hCMsU : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
      have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
      have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
        apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
        apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
        by_cases hq : r = q
        · rw [if_pos hq, hq]
        · rw [if_neg hq]
          by_cases hqp : q.Prime
          · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
            exact (Set.mem_singleton_iff.mp (hR.1 q (Nat.mem_primeFactors.mpr
              ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩))).symm
          · exact Nat.factorization_eq_zero_of_not_prime _ hqp
      have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
        have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
        have hlag := Subgroup.card_mul_index (R.subgroupOf U)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxU, add_zero, hSU]
      have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
        have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrκσ)
        have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hlag := Subgroup.card_mul_index (U.subgroupOf M)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxM, add_zero, hUcard]
      have hRsylM : Nat.card ↥(R.subgroupOf M) = r ^ (Nat.card ↥M).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hRpow, ← hfUR, hfUM]
      have hpRankRM : pRank ↥R r = pRank ↥M r := by
        have h1 : pRank ↥(R.subgroupOf M) r = pRank ↥M r := by
          have := pRank_sylow_eq (Sylow.ofCard (R.subgroupOf M) hRsylM)
          rwa [Sylow.coe_ofCard] at this
        rw [← h1]; exact pRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRM).symm r
      have hRrankpos : 0 < pRank ↥R r := by
        rw [hpRankRM]; exact OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hrπM
      obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
        (G := ↥R) (p := r) (n := pRank ↥R r) hRrankpos (le_refl _)
      obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
      have hjeq : j = pRank ↥R r := by
        have hsq := le_antisymm (le_pRank B hBea) hBlog
        rwa [hj, Nat.log_pow hrprime.one_lt] at hsq
      have hAR : B.map R.subtype ≤ R := Subgroup.map_subtype_le _
      have hAmem : B.map R.subtype ∈ elemAbelianOfRank G r (pRank ↥M r) :=
        ⟨Subgroup.IsElementaryAbelian.map R.subtype_injective hBea, by
          rw [Subgroup.card_map_of_injective R.subtype_injective, hj, hjeq, hpRankRM]⟩
      have hrκ : r ∉ kappa M := fun h => hrκσ (Or.inl h)
      exact (msigma_centralizer_eq_bot_of_elemAb_le hG hM hrπM hrσM hrκ hAmem
        (hAR.trans hRM) (hAR.trans hRU)).1
    -- `M ⊓ H ⊆ N_M(U)` (geometric: `M ⊓ H ≤ N(M) ⊓ N(Fu) ≤ N(M ⊓ Fu) = N(U)`).
    have hMHnU : M ⊓ H ≤ Subgroup.normalizer (U : Set G) := by
      rw [← hdefU]
      exact le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans hHnFu)
    -- `defNMU`: BG 6.5(b) in `↥M` gives `N_{↥M}(U) = (C(U) ⊓ M_σ) · (N(U) ⊓ (U⊔K))`; the
    -- first factor is `C_{M_σ}(U) = 1`, so every `n ∈ N_M(U)` lies in `U ⊔ K`.
    have hKU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ (U ⊔ K).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM), hJM,
        Subgroup.subgroupOf_self]
    have hcop : Nat.Coprime (Nat.card ↥(U.subgroupOf M))
        (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      have hpU : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
        hU.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩)
      refine hpU (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Nat.card_pos.ne'⟩
    haveI hMsol : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    haveI hMσMnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hlem := OddOrder.BG.Ch1.S06.normalizer_eq_centralizerK_mul_normalizerU (G := ↥M)
      (K := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U := (U ⊔ K).subgroupOf M)
      (H := U.subgroupOf M) hKU (Subgroup.subgroupOf_mono M le_sup_left) hcop
    -- The first factor `C(U) ⊓ M_σ` is trivial in `↥M` (`C_{M_σ}(U) = 1`).
    have hfactor1 : Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ⊓
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_inf] at hc
      have hcCU : (M.subtype c) ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u huU
        have hcomm := (Subgroup.mem_centralizer_iff.mp hc.1) (⟨u, hUM huU⟩ : ↥M)
          (Subgroup.mem_subgroupOf.mpr huU)
        have := congrArg (M.subtype) hcomm
        simpa using this
      have hmem : (M.subtype c) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hc.2, hcCU⟩
      rw [hCMsU, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact M.subtype_injective (by rw [hmem, map_one])
    -- Conclude: `M ⊓ H ⊆ M ⊓ N_G(U)`, and each such `n` lies in `U ⊔ K`.
    refine le_trans (le_inf inf_le_left hMHnU) ?_
    intro n hn
    rw [Subgroup.mem_inf] at hn
    obtain ⟨hnM, hnNU⟩ := hn
    have hnbar : (⟨n, hnM⟩ : ↥M) ∈ Subgroup.normalizer (U.subgroupOf M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hUM, Subgroup.mem_subgroupOf]; exact hnNU
    have hnbarc := SetLike.mem_coe.mpr hnbar
    rw [hlem] at hnbarc
    obtain ⟨c, hc, u, hu, hcu⟩ := Set.mem_mul.mp hnbarc
    have hc1 : c = 1 :=
      Subgroup.mem_bot.mp (hfactor1 ▸ SetLike.mem_coe.mp hc)
    rw [hc1, one_mul] at hcu
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hu
    have hnUK : (M.subtype u) ∈ U ⊔ K := Subgroup.mem_subgroupOf.mp hu.2
    rw [hcu] at hnUK
    simpa using hnUK
  · -- Conjunct 4 (`N_H(U) ⊄ M`): suppose `N_H(U) = H ⊓ N_G(U) ≤ M`.  Then `N_Fu(U) = N_G(U) ⊓ Fu`
    -- lies in `M ⊓ Fu = U`, so `U` is self-normalizing in the nilpotent `Fu`, forcing `Fu = U`.
    -- Hence `H ≤ N_G(Fu) = N_G(U)`, so `H = H ⊓ N_G(U) ≤ M`, whence `H = M` (both maximal),
    -- contradicting `H` not conjugate to `M`.
    intro hNHU_M
    have hNFuU : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ U := by
      have h1 : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M :=
        le_trans (le_inf (le_trans inf_le_right hFuH) inf_le_left) hNHU_M
      calc Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M ⊓ Fu := le_inf h1 inf_le_right
        _ = U := hdefU
    haveI hFunil : Group.IsNilpotent ↥Fu :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe
        (opiCoreInG_le π (OddOrder.BG.Ch2.S08.fittingInG H)))
    have hFuU : Fu = U := eq_of_isNilpotent_normalizer_inf_le hFunil hUFu hNFuU
    have hHnU : H ≤ Subgroup.normalizer (U : Set G) := hFuU ▸ hHnFu
    have hHM : H ≤ M := le_trans (le_inf le_rfl hHnU) hNHU_M
    have hHeqM : H = M := by
      rcases lt_or_eq_of_le hHM with hlt | heq
      · exact absurd ((mem_maximalSubgroups.mp hHmax).2 M hlt) (mem_maximalSubgroups.mp hM).1
      · exact heq
    exact notMGH (by rw [hHeqM])

/-- **BG Corollary 14.12** (mmd L4230), existential form.  For a type-`P₂` maximal `M` with
`κ`-complement `K` and abelian Hall `(κ ∪ σ)′`-factor `U`, and a Sylow `r`-subgroup `R ≤ U`,
there is a maximal `H ⊇ N_G(R)` that is type-`F`, with `U ≤ H_σ`, `M ⊓ H = U ⊔ K`, and
`N_H(U) ⊄ M`.

Convenience wrapper over `typeP2_neighbor_is_typeF_of_mem`: it picks `H` as a maximal overgroup
of `N_G(R)` (via `eq_top_or_exists_le_coatom`) and drops the `E`-setup export.  Consumers needing
the σ(H)′-Hall `E` / `K ⊆ F(E)` clauses (Theorem 15.8) call `_of_mem` with their own `H`. -/
theorem typeP2_neighbor_is_typeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    ∃ H : Subgroup G,
      H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) ∧
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) := by
  classical
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp
        (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- `N_G(R) < ⊤` (since `R ≤ M`, `R ≠ ⊥`, `G` simple), so it has a maximal overgroup `H`.
  have hNR_lt : Subgroup.normalizer (R : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM hRM hRne
  obtain ⟨H, hHcoatom, hNRH⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNR_lt.ne
  have hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hHcoatom, hNRH⟩
  obtain ⟨hF, hUMsH, hMH, hnorm, -⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  exact ⟨H, hH, hF, hUMsH, hMH, hnorm⟩

/-- **BG Lemma 14.13** (mmd L4059): extension of Theorem 14.4.  In the specified
multi-maximal sigma-length-one situation, `M` is Frobenius type, `tau_2(M)` is
empty, and `M` is a Frobenius group with kernel `M_sigma`.

⚠ **STATEMENT MIS-ENCODED (do not prove vacuously, 2026-06-30)**: the Coq original
(`non_disjoint_signalizer_Frobenius`, BGsection14:2412) hypothesises `1 < |𝓜_σ(x)|` and `M` *not*
a `σ(N[x])′`-group (`N[x]` = the signalizer neighbour).  The Lean hypotheses `M, N ∈ 𝓜_σ(x)` with
`¬ IsConjugateSubgroup M N` are **inconsistent**: by Theorem 13.9 non-conjugate maximals have
`σ(M) ∩ σ(N) = ∅`, but `x ∈ M_σ ∩ N_σ` with `x ≠ 1` forces a common prime — so the premise is
vacuous (the two elements of `𝓜_σ(x)` are conjugate, not non-conjugate).  A faithful restatement
replaces `{N, hN, hMN, hinter}` by `1 < (𝓜_σ(x)).ncard` and the `σ(N[x])′`-group condition.
Orphaned (no consumers); not on the FT path.  See issue 8020. -/
theorem sigmaLength_one_frobenius_type [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {x : G} (hx : x ≠ 1) (hlen : D.length x = 1)
    {M N : Subgroup G} (hM : M ∈ maximalSigmaSubgroupsOfElement x)
    (hN : N ∈ maximalSigmaSubgroupsOfElement x)
    (hMN : ¬ IsConjugateSubgroup M N)
    (hinter : (OddOrder.BG.Ch3.S10.sigma N ∩ piSet M).Nonempty) :
    IsTypeF M ∧ tau2 M = ∅ ∧
      ∃ U : Subgroup G,
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
          (U.subgroupOf M) ∧
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) := by
  sorry

/-- **BG Corollary 14.10** (mmd L4008): global `σ`-length bound `ℓ_σ(g) ≤ 2`.

Assembled from the faithful `G#` cover.  The genuine `SigmaDecompositionData` is
`genuineSigmaDecomposition hG` (`length = sigmaLength`); `ℓ_σ(1) = 0` (`sigmaLength_eq_zero_iff`), and
for `g ≠ 1` the cover (`exists_mem_conjClassSet_Mtilde_or_fixed_zTilde` when a type-P maximal exists,
else `sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`) places `g` in `𝒞_G(M̃)` or
`𝒞_G(Ẑ)`; conjugation-invariance (`sigmaLength_conj`) reduces to the per-piece bounds
`sigmaLength_le_two_of_mem_Mtilde` (sorry-free) and `sigmaLength_le_two_of_mem_zTilde_of_isTypeP`
(gated on the type-P partner-duality residual). -/
theorem exists_sigmaDecomposition_length_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ D : SigmaDecompositionData G, ∀ g : G, D.length g ≤ 2 := by
  refine ⟨genuineSigmaDecomposition hG, fun g => ?_⟩
  show sigmaLength g ≤ 2
  by_cases hg1 : g = 1
  · have h0 : sigmaLength g = 0 := (sigmaLength_eq_zero_iff hG g).mpr hg1
    omega
  · -- The `M̃`-piece closes by `sigmaLength_le_two_of_mem_Mtilde` after `sigmaLength_conj`.
    have hMtilde : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) → sigmaLength g ≤ 2 := by
      intro M hMmax hgM
      obtain ⟨m, hm, c, hcm⟩ := mem_conjClassSet.mp hgM
      rw [← hcm, sigmaLength_conj]
      exact sigmaLength_le_two_of_mem_Mtilde hG hMmax hm
    by_cases hP : (maximalTypePFamily G).Nonempty
    · obtain ⟨Mref, hMref, hMPref⟩ := hP
      obtain ⟨Kref, Kstarref, Uref, hKMref, hKref, hKstarref, hUref⟩ := exists_typeP_data hG hMref
      rcases exists_mem_conjClassSet_Mtilde_or_fixed_zTilde hG hMref hMPref hKMref hKref hKstarref
          hUref hg1 with ⟨M, hMmax, hgM⟩ | hgZ
      · exact hMtilde M hMmax hgM
      · obtain ⟨z, hz, c, hcz⟩ := mem_conjClassSet.mp hgZ
        rw [← hcz, sigmaLength_conj]
        exact sigmaLength_le_two_of_mem_zTilde_of_isTypeP hG hMref hMPref hKMref hKref hKstarref
          hUref hz
    · have htypeF : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeF M := by
        intro M hM
        rw [isTypeF_iff_not_isTypeP]
        exact fun hMP => hP ⟨M, hM, hMP⟩
      have hgsharp : g ∈ sharpSubgroup (⊤ : Subgroup G) :=
        Set.mem_sdiff_singleton.mpr ⟨Subgroup.mem_top g, hg1⟩
      rw [sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF hG htypeF,
        Set.mem_iUnion₂] at hgsharp
      obtain ⟨M, hMmax, hgM⟩ := hgsharp
      exact hMtilde M hMmax hgM

/-! ### Subnormal closure into the `C(K)`-unique maximal (Coq `snK_sMst`)

Coq `P2type_signalizer` (BGsection14.v:2283) uses `snK_sMst L : K <|<| L → L ⊆ Mst`: any
subgroup `L` in which the `κ`-Hall `K` is *subnormal* is contained in the unique maximal `Mst`
over `C_G(K)`.  We port it here (S14 territory) via the base uniqueness `sK_uniqMst`
(`∀ a, K ≤ Mst^a → a ∈ Mst`) and a strong induction on `|L|` peeling normal layers
(`IsSubnormal.exists_normal_and_le_and_lt_top_of_ne`).  It supplies `E ⊆ Mst` (Coq `sDMst`)
for the signalizer decomposition Keystone C. -/

/-- **Coq `snK_sMst` single step**: if `N ⊆ Mstar`, `K ≤ N`, `L` normalizes `N`, and `K` has
the uniqueness property `∀ a, K ≤ Mstar^a → a ∈ Mstar` (Coq `sK_uniqMst`), then `L ⊆ Mstar`.
For `a ∈ L`, `a` normalizes `N`, so `N^{a⁻¹} = N`, whence `K^{a⁻¹} ≤ N^{a⁻¹} = N ⊆ Mstar`,
i.e. `K ≤ Mstar^a`, so `a ∈ Mstar`. -/
theorem le_partner_of_normalizes_of_le_of_uniq {K Mstar N L : Subgroup G}
    (hNMstar : N ≤ Mstar) (hKN : K ≤ N) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) :
    L ≤ Mstar := by
  intro a ha
  -- `a⁻¹` normalizes `N`, so `conj a⁻¹ • N = N`.
  have haN : MulAut.conj a⁻¹ • N = N :=
    OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer
      (Subgroup.inv_mem _ (hLN ha))
  -- `conj a⁻¹ • K ≤ conj a⁻¹ • N = N ≤ Mstar`.
  have hKconj : MulAut.conj a⁻¹ • K ≤ Mstar :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKN).trans (haN.le.trans hNMstar)
  -- Rewrite as `K ≤ conj a • Mstar` and apply the uniqueness hypothesis.
  have hKMstar : K ≤ MulAut.conj a • Mstar := by
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a).mpr hKconj
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at this
  exact huniq a hKMstar

/-- **Coq `snK_sMst`** (BGsection14.v:2283): if `K` is *subnormal* in `L` (`K ≤ L`,
`(K.subgroupOf L).IsSubnormal`), `K ≤ Mstar`, and `K` has the uniqueness property
`∀ a, K ≤ Mstar^a → a ∈ Mstar`, then `L ⊆ Mstar`.  Strong induction on `|L|`: if `K = L`,
done; otherwise peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`
(`exists_normal_and_le_and_lt_top_of_ne`), so `N := N̄.map L.subtype` is a proper subgroup with
`K ≤ N`, `K` subnormal in `N` (restriction), `L ≤ N_G(N)` (`N̄ ◁ ↥L`); the induction hypothesis
gives `N ⊆ Mstar`, and the single-step lemma lifts it to `L ⊆ Mstar`. -/
theorem le_partner_of_subnormal_of_uniq [Finite G] {K Mstar : Subgroup G}
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) (hKMstar : K ≤ Mstar) :
    ∀ L : Subgroup G, K ≤ L → (K.subgroupOf L).IsSubnormal → L ≤ Mstar := by
  intro L
  induction hcard : Nat.card ↥L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    intro hKL hsub
    by_cases hKLtop : K.subgroupOf L = ⊤
    · -- `K = L` (as `K ≤ L`), so `L = K ≤ Mstar`.
      have hLK : L ≤ K := by
        intro x hx
        have hmem : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := by rw [hKLtop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp hmem
      exact hLK.trans hKMstar
    · -- Peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`.
      obtain ⟨Nbar, hNbarnorm, hKNbar, hNbarlt⟩ :=
        hsub.exists_normal_and_le_and_lt_top_of_ne hKLtop
      haveI := hNbarnorm
      set N : Subgroup G := Nbar.map L.subtype with hNdef
      have hNL : N ≤ L := Subgroup.map_subtype_le _
      have hNbar_eq : N.subgroupOf L = Nbar :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective Nbar
      -- `K ≤ N`.
      have hKN : K ≤ N := by
        have hmm : (K.subgroupOf L).map L.subtype ≤ N := Subgroup.map_mono hKNbar
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL] at hmm
      -- `|N| < |L|` (proper).
      have hNlt : Nat.card ↥N < Nat.card ↥L := by
        have hNbne : N ≠ L := by
          intro h
          apply hNbarlt.ne
          rw [← hNbar_eq, h, Subgroup.subgroupOf_self]
        refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hNL))
          (fun heq => hNbne (Subgroup.eq_of_le_of_card_ge hNL heq.ge))
      -- `K` subnormal in `N` (restrict the subnormal series along `N ≤ L`).
      have hKNsub : (K.subgroupOf N).IsSubnormal := by
        have hcomap := hsub.comap (Subgroup.inclusion hNL)
        rwa [Subgroup.comap_inclusion_subgroupOf hNL] at hcomap
      -- Induction hypothesis: `N ⊆ Mstar`.
      have hNMstar : N ≤ Mstar := ih (Nat.card ↥N) (hcard ▸ hNlt) N rfl hKN hKNsub
      -- `L ≤ N_G(N)` (`N̄ ◁ ↥L`), so the single-step lemma gives `L ⊆ Mstar`.
      have hLnN : L ≤ Subgroup.normalizer (N : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hNL, hNbar_eq]
        exact hNbarnorm
      exact le_partner_of_normalizes_of_le_of_uniq hNMstar hKN hLnN huniq

/-! ### Subnormality in nilpotent groups (mathcomp `nilpotent_subnormal`)

Two general group-theory facts used to feed `le_partner_of_subnormal_of_uniq` in the signalizer
decomposition below (Coq `nilpotent_subnormal (Fitting_nil D) sK_FD`).  Not `S14`-specific. -/

/-- **Every subgroup of a finite nilpotent group is subnormal** (mathcomp `nilpotent_subnormal`).
Strong induction on the index: for `H ≠ ⊤` the normalizer condition
(`Group.normalizerCondition_of_isNilpotent`) gives `H < N(H)`, `H ⊴ N(H)` (`normal_in_normalizer`), and
`[Γ : N(H)] < [Γ : H]` (`index_strictAnti`), so the IH makes `N(H)` subnormal;
then `IsSubnormal.step`. -/
theorem isSubnormal_of_isNilpotent {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (H : Subgroup Γ) : H.IsSubnormal := by
  have hnc : NormalizerCondition Γ := Group.normalizerCondition_of_isNilpotent
  induction hidx : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHtop : H = ⊤
    · exact hHtop ▸ Subgroup.IsSubnormal.top
    · have hlt : H < Subgroup.normalizer (H : Set Γ) := hnc H (lt_top_iff_ne_top.mpr hHtop)
      have hidxlt : (Subgroup.normalizer (H : Set Γ)).index < n := by
        rw [← hidx]; exact Subgroup.index_strictAnti hlt
      have hstep : (Subgroup.normalizer (H : Set Γ)).IsSubnormal :=
        ih _ hidxlt (Subgroup.normalizer (H : Set Γ)) rfl
      exact Subgroup.IsSubnormal.step H (Subgroup.normalizer (H : Set Γ)) hlt.le hstep
        Subgroup.normal_in_normalizer

/-- **A subgroup contained in a normal, nilpotent subgroup is subnormal** in the ambient group
(mathcomp `nilpotent_subnormal` + `normal_subnormal` + transitivity): `H ≤ N ⊴ Γ` with `N` nilpotent
gives `H.subgroupOf N` subnormal in `↥N` (previous lemma), `N` subnormal in `Γ`
(`Normal.isSubnormal`), so `IsSubnormal.trans`. -/
theorem isSubnormal_of_le_normal_nilpotent {Γ : Type*} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hHN : H ≤ N) (hNnorm : N.Normal) (hNnil : Group.IsNilpotent ↥N) : H.IsSubnormal := by
  haveI := hNnil
  exact Subgroup.IsSubnormal.trans hHN (isSubnormal_of_isNilpotent (H.subgroupOf N))
    hNnorm.isSubnormal

/-- **Signalizer σ-decomposition `H_σ ⊔ (H ∩ M*) = H` for BG Theorem 15.8** (Coq
`tau2_P2type_signalizer`, `set D := H :&: L` + `sdprod_sigma maxH hallD`, BGsection15.v:1273/1374,
resting on `P2type_signalizer`, BGsection14.v:2283/2374): for the Corollary 14.12 signalizer
neighbour `H` of the type-`P₂` maximal `M` (with `M* ∈ 𝓜(C_G(K))`, `H ∈ 𝓜(N_G(R))`), the
`E`-setup complement `E` of `H_σ` (which contains `K` with `K ⊆ F(E)`, from
`typeP2_neighbor_is_typeF_of_mem`) lies in `M*`, so `H_σ ⊔ (H ∩ M*) ⊇ H_σ ⊔ E = H`.

**Proof (weaker than Coq's exact `H ∩ M* = D`).**  Coq proves the exact identity `H ∩ M* = D` (its
σ(H)′-Hall) via the harder `H_σ ∩ M* = 1` step, needed for its Hall/Fitting clauses.  The repo goal
is only the *join* `H_σ ⊔ (H ∩ M*) = H`, so the easy inclusion `E ⊆ H ∩ M*` suffices.  `E ⊆ M*`
comes from `le_partner_of_subnormal_of_uniq` (Coq `snK_sMst`): `K` is subnormal in `E`
(`K ⊆ F(E)`, `F(E)` normal nilpotent, `isSubnormal_of_le_normal_nilpotent`), `K ⊆ M*`
(`K ⊆ M*_σ`), and the uniqueness `K ≤ M*^a → a ∈ M*` (Coq `sK_uniqMst`, `partner_inf_and_uniq`);
`M* = Mst` (the dual partner) since `𝓜(C(K)) = {Mst}` (Prop 14.2(d)).  (issue 9017 更新 #12/#13.) -/
theorem signalizer_msigma_sup_inf_partner_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Mstar U K R H : Subgroup G} {r : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)))
    (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mstar) = H := by
  classical
  have hP : IsTypeP M := hP2.1
  -- Dual partner `Mst` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- Uniqueness `sK_uniqMst : K ≤ Mst^a → a ∈ Mst` (Coq), and `K ≤ M*_σ` (⟹ `K ≤ Mst`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
    (le_of_eq hMstpair.2.2).trans inf_le_left
  have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
    msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
  have hKstarM : Kstar ≤ M := by
    rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
  have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
    hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`), so `Mstar = Mst`.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard,
      by rw [hKcard, pow_one]⟩
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    haveI hMstsol : IsSolvable ↥Mst := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  have hMstarEq : Mstar = Mst := by
    have hmem := hMstar; rw [huniqMst] at hmem; exact Set.mem_singleton_iff.mp hmem
  rw [hMstarEq]
  -- `E`-setup from the neighbour lemma: `M_σ(H) ⊔ E = H`, `K ≤ E`, `K ≤ F(E)`.
  obtain ⟨-, -, -, -, E, E₁, E₂, E₃, hEsetup, hKE, hKFE⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  -- `E ≤ Mst` via subnormal closure (Coq `snK_sMst`): `K ⊴⊴ E`, `K ≤ Mst`, uniqueness.
  have hKMst : K ≤ Mst := hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mst)
  have hKsubnormal : (K.subgroupOf E).IsSubnormal := by
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
      OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E
    refine isSubnormal_of_le_normal_nilpotent
      (N := (OddOrder.BG.Ch2.S08.fittingInG E).subgroupOf E) ?_
      (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal E)
      (Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch2.S08.fittingInG_le E)).symm)
    exact Subgroup.comap_mono hKFE
  have hEMst : E ≤ Mst := le_partner_of_subnormal_of_uniq hsKuniq hKMst E hKE hKsubnormal
  -- Conclude: `E ⊆ H ∩ Mst` and `M_σ(H) ⊔ E = H`.
  refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) inf_le_left) ?_
  calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
    _ ≤ OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mst) :=
        sup_le_sup_left (le_inf hEsetup.E_le hEMst) _

end OddOrder.BG.Ch4.S14


