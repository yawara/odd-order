/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure
import OddOrder.BG.Ch3_MaximalSubgroups.S10_LocalCriteria
import OddOrder.BG.Ch3_MaximalSubgroups.S10_BetaRadical
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S01c_Omega1Rigidity

/-!
# BG §10 局所補題 (Lemmas 10.5/10.12/10.13, Prop 10.11)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §10。
Hall 構造 base (`S10_HallStructure`, Thm 10.1/10.2) に依存する補題群 (active frontier
leaves)。Prop 10.11(b) は Prop 10.10 (`normalizer_factorization`) を使うため spine
(`S10_BetaRadical`) も import する。Lemmas 10.3 / 10.4 (a)(b)(c) は spine の
de-axiomatization のため `S10_LocalCriteria` (`S10_ForwardFromKeystone` の上流) に在る。
mmd `references/bg/local-analysis.mmd` L2856-2894 周辺。
-/

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- A Sylow `p`-subgroup `P` of `G` contained in `K ≤ G` restricts to a Sylow `p`-subgroup of
`↥K` with carrier `P.subgroupOf K` (replicates the private `S07.sylow_subgroupOf_of_le`). Shared
by Proposition 10.11 and Lemma 10.12. -/
private theorem sylow_subgroupOf_of_le {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G)
    {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ∃ Q : Sylow p ↥K, (Q : Subgroup ↥K) = (P : Subgroup G).subgroupOf K := by
  have hpg : IsPGroup p ↥((P : Subgroup G).subgroupOf K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]; exact hn)
  have hidx : ¬ p ∣ ((P : Subgroup G).subgroupOf K).index := fun h =>
    P.not_dvd_index (dvd_trans h (Subgroup.relIndex_dvd_index_of_le hPK))
  exact ⟨hpg.toSylow hidx, hpg.toSylow_coe hidx⟩

/-! ## Proposition 10.11 — σ(M)'-部分群の rank (mmd L2886) -/

/-- The pointwise action of a `MulAut` on a subgroup is its image (replicates the private
`mulAut_smul_eq_map` of the BG `Ch1`/`Ch2` files). Shared by Prop 10.11(b)/(d). -/
private theorem conjSmul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by rw [Subgroup.pointwise_smul_def]; rfl

/-- **Cyclic uniqueness by order**: in a finite cyclic group, two subgroups of equal
cardinality coincide. (Each order-`d` subgroup equals the unique order-`d` kernel
`(powMonoidHom d).ker`.) Used in 10.11(c)/(d) to transport `M`-normalisation along the
cyclic `Z` to its subgroups.

This duplicates `S10_BetaRadical.cyclic_subgroup_eq_of_card_eq` (a sibling §10 leaf); the
shared helper should be hoisted into `S10_HallStructure` (public here since Lemma 12.18 uses it
for the `Ω₁` bookkeeping in `S12_Lemma1218`). -/
theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} (h : Nat.card H₁ = Nat.card H₂) : H₁ = H₂ := by
  letI : CommGroup C := IsCyclic.commGroup
  have key : ∀ {N : Subgroup C} {d : ℕ}, Nat.card N = d → N = (powMonoidHom d : C →* C).ker := by
    intro N d hN
    have hN_le : N ≤ (powMonoidHom d : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hN] at this
    have hd_dvd : d ∣ Nat.card C := hN ▸ N.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom d : C →* C).ker = d := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd_dvd]
    exact Subgroup.eq_of_le_of_card_ge hN_le (by rw [hker_card, hN])
  exact (key (d := Nat.card H₁) rfl).trans (key (d := Nat.card H₁) h.symm).symm

/-- In a minimal counterexample the trivial subgroup is *not* uniquely maximal: if `M₀` were
the unique maximal subgroup of `G`, every proper subgroup would lie in `M₀`, so any `g ∉ M₀`
would generate `G`, making `G` cyclic and hence solvable — contradiction. Degenerate-case
guard for Proposition 10.11(a). -/
private theorem not_isUniquelyMaximal_bot [Finite G] (hG : IsMinimalSimpleOdd G) :
    ¬ IsUniquelyMaximal (⊥ : Subgroup G) := by
  rintro ⟨-, M₀, ⟨hM₀co, -⟩, huniq⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M₀ := by
    by_contra h
    push Not at h
    exact hM₀co.1 (top_le_iff.mp fun x _ => h x)
  have hzp : Subgroup.zpowers g = ⊤ := by
    rcases eq_top_or_exists_le_coatom (Subgroup.zpowers g) with h | ⟨L, hLco, hzL⟩
    · exact h
    · have hLM₀ : L = M₀ := huniq L ⟨hLco, bot_le⟩
      exact absurd (hLM₀ ▸ hzL (Subgroup.mem_zpowers g)) hg
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top a)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top b)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact hG.notSolvable (isSolvable_of_comm hcomm)

/-- **BG Proposition 10.11(a)** (mmd L2886): `M ∈ ℳ` and `K` a `σ(M)'`-subgroup of `M` imply
`K ∉ 𝒰`. Exposed separately from `sigma_complement_rank_le_one` because part (b) reapplies it
to the rank-two witness `A ≤ C_K(M_σ)`.

Take a Hall `σ(M)'`-subgroup `E` of `M` containing `K`. Since `α(M) ⊆ σ(M)` forces
`r(E) ≤ 2`, the characteristic Sylow series of `E` (Theorem 4.20(c)) ends with a normal
Sylow `q`-subgroup `R ⊴ E`, which is in fact a Sylow `q`-subgroup of `M` (Hall index);
`q ∉ σ(M)` gives `N_G(R) ⊄ M`, while `K ≤ E ≤ N_G(R)`, so a maximal subgroup over `N_G(R)`
is a second maximal subgroup containing `K`. -/
theorem sigma_complement_not_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) : ¬ IsUniquelyMaximal K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  rcases eq_or_ne K ⊥ with rfl | hKbot
  · exact not_isUniquelyMaximal_bot hG
  -- Step 1: a Hall `σ(M)'`-subgroup `E` of `M` containing `K` (trivial operator group).
  have hKsubMpi : Ch03.Subgroup.IsPiGroup (sigma M)ᶜ (K.subgroupOf M) := fun p hp => by
    have hpK : p ∈ (Nat.card ↥K).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact hKpi p hpK
  have hKinv : Ch03.IsAInvariant (1 : Unit →* MulAut ↥M) (K.subgroupOf M) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro _ x hx
    simpa using hx
  obtain ⟨H, hHhall, -, hKH⟩ := OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
    (by simp : Nat.Coprime (Nat.card Unit) (Nat.card ↥M)) hKsubMpi hKinv
  set E : Subgroup G := H.map M.subtype with hEdef
  have hEM : E ≤ M := Subgroup.map_subtype_le H
  have hKE : K ≤ E := fun x hx => by
    rw [hEdef, Subgroup.mem_map]
    exact ⟨⟨x, hKM hx⟩, hKH (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  haveI : IsSolvable ↥E := solvable_of_solvable_injective (Subgroup.inclusion_injective hEM)
  have hcardE : Nat.card ↥E = Nat.card ↥H := by
    rw [hEdef, Subgroup.card_map_of_injective M.subtype_injective]
  have hEpi : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∈ (sigma M)ᶜ := fun r hr => by
    rw [hcardE] at hr
    exact hHhall.1 r hr
  -- Step 2: `r(E) ≤ 2`, because a prime of `p`-rank `≥ 3` would lie in `α(M) ⊆ σ(M)`.
  have hErank : rank ↥E ≤ 2 := by
    rw [rank_le_iff]
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hcon
    have h3E : 3 ≤ pRank ↥E p := by omega
    have h3M : 3 ≤ pRank ↥M p :=
      le_trans h3E (pRank_le_of_injective (Subgroup.inclusion_injective hEM))
    exact hEpi p (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))
      (alpha_subset_sigma hG hM ((mem_alpha_iff M p).mpr
        ⟨Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega), h3M⟩))
  -- Step 3: the characteristic Sylow series of `E` (Theorem 4.20(c)) has a terminal
  -- normal Sylow `q`-subgroup `Q ⊴ E` with `q ∈ π(E)`.
  have hEne : E ≠ ⊥ := fun h => hKbot (le_bot_iff.mp (hKE.trans_eq h))
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  have hEodd : Odd (Nat.card ↥E) :=
    hG.odd.of_dvd_nat ((Subgroup.card_dvd_of_le hEM).trans (Subgroup.card_subgroup_dvd_card M))
  have hErankF : rank ↥(Ch01.fitting ↥E) ≤ 2 :=
    le_trans (rank_le_of_injective (Subgroup.subtype_injective (Ch01.fitting ↥E))) hErank
  obtain ⟨pkg⟩ :=
    OddOrder.BG.Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
      hEodd hErankF
  -- Repackage the terminal layer: a prime `q ∈ π(E)` and (the ambient form of) a normal
  -- Sylow `q`-subgroup `R ⊴ E`, with `q ∤ [E : R]` and `E ≤ N_G(R)` (Step 6).
  obtain ⟨q, hq_prime, hqE, R, hRE, hRpg, hndvd_ER, hE_norm_R⟩ :
      ∃ q : ℕ, q.Prime ∧ q ∈ (Nat.card ↥E).primeFactors ∧
        ∃ R : Subgroup G, R ≤ E ∧ IsPGroup q ↥R ∧ ¬ q ∣ (R.subgroupOf E).index ∧
          E ≤ Subgroup.normalizer (R : Set G) := by
    obtain ⟨i, -, hqE, Q, hQnorm⟩ :=
      OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage.exists_terminal_normal_sylow pkg
    haveI : Fact (pkg.series.step i).q.Prime := (pkg.series.step i).q_prime
    haveI : (Q : Subgroup ↥E).Normal := hQnorm
    refine ⟨(pkg.series.step i).q, Fact.out, hqE,
      (Q : Subgroup ↥E).map E.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · exact Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ E.subtype E.subtype_injective)
    · have hRsub : ((Q : Subgroup ↥E).map E.subtype).subgroupOf E = (Q : Subgroup ↥E) := by
        rw [Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      rw [hRsub]
      exact Q.not_dvd_index
    · have hmap := Ch07.map_le_normalizer_map_of_normal
        (φ := E.subtype) (P := (⊤ : Subgroup ↥E)) (L := (Q : Subgroup ↥E))
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- Step 4: `R` is a Sylow `q`-subgroup of `M`: `q ∤ [E : R]` (Sylow) and `q ∤ [M : E]` (Hall).
  have hEsubM : E.subgroupOf M = H := by
    rw [hEdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hndvd_ME : ¬ q ∣ (E.subgroupOf M).index := fun hdvd => by
    rw [hEsubM] at hdvd
    exact hHhall.2 q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (hEpi q hqE)
  have hndvd_MR : ¬ q ∣ (R.subgroupOf M).index := by
    have hmul : R.relIndex E * E.relIndex M = R.relIndex M :=
      Subgroup.relIndex_mul_relIndex R E M hRE hEM
    intro hdvd
    rw [show (R.subgroupOf M).index = R.relIndex M from rfl, ← hmul] at hdvd
    rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h | h
    · exact hndvd_ER h
    · exact hndvd_ME h
  have hRpg_inM : IsPGroup q ↥(R.subgroupOf M) :=
    hRpg.of_equiv (Subgroup.subgroupOfEquivOfLe (hRE.trans hEM)).symm
  -- Step 5: `q ∉ σ(M)` forces `N_G(R) ⊄ M` (else `R` would witness `q ∈ σ(M)`).
  have hqσc : q ∉ sigma M := hEpi q hqE
  have hqM : q ∈ (Nat.card ↥M).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_dvd_of_le hEM) Nat.card_pos.ne' hqE
  have hNR_not_le : ¬ Subgroup.normalizer (R : Set G) ≤ M := by
    intro hNM
    apply hqσc
    rw [mem_sigma_iff]
    refine ⟨hqM, hRpg_inM.toSylow hndvd_MR, ?_⟩
    rwa [hRpg_inM.toSylow_coe hndvd_MR,
      Subgroup.map_subgroupOf_eq_of_le (hRE.trans hEM)]
  -- Step 7: a maximal subgroup over `N_G(R)` is a second maximal subgroup containing `K`.
  have hq_dvd_R : q ∣ Nat.card ↥R := by
    have hcard : Nat.card ↥(R.subgroupOf E) * (R.subgroupOf E).index = Nat.card ↥E :=
      Subgroup.card_mul_index _
    have hq_dvd_E : q ∣ Nat.card ↥E := (Nat.mem_primeFactors.mp hqE).2.1
    have hcardR : Nat.card ↥(R.subgroupOf E) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRE).toEquiv
    rcases (Nat.Prime.dvd_mul Fact.out).mp (hcard ▸ hq_dvd_E) with h | h
    · exact hcardR ▸ h
    · exact absurd h hndvd_ER
  have hRne : R ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hq_dvd_R
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp hq_dvd_R)
  have hNR_lt_top : Subgroup.normalizer (R : Set G) < ⊤ := by
    rcases (le_top : Subgroup.normalizer (R : Set G) ≤ ⊤).lt_or_eq with h | h
    · exact h
    · exfalso
      haveI : R.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases hG.simple.eq_bot_or_eq_top_of_normal R inferInstance with h' | h'
      · exact hRne h'
      · exact (mem_maximalSubgroups.mp hM).1
          (top_le_iff.mp (h' ▸ hRE.trans hEM : (⊤ : Subgroup G) ≤ M))
  obtain ⟨L, hLco, hNL⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (R : Set G))).resolve_left
      hNR_lt_top.ne
  have hLM : L ≠ M := fun h => hNR_not_le (h ▸ hNL)
  exact Ch2.S09.not_isUniquelyMaximal_of_le_inf_distinct_maximals hM
    (mem_maximalSubgroups.mpr hLco)
    (le_inf hKM ((hKE.trans hE_norm_R).trans hNL)) hLM

/-- **BG Proposition 10.11(b)** (mmd L2886): `r(C_K(M_σ)) ≤ 1` for a `σ(M)'`-subgroup `K ≤ M`.

By contradiction take `A ∈ ℰ_p²(C_K(M_σ))` and `q ∈ σ(M)`; the Sylow `q`-subgroup `S` of `G`
in `M_σ` satisfies `S ∈ ℋ_G*(A; q)`, `q ∈ π(C_G(A))`, `N_G(S) ⊆ M`. Part (a) gives `A ∉ 𝒰`,
so the Uniqueness Theorem (contrapositive of 9.6 and its `ℰ²`-corollary) yields
`r(C_G(A)) ≤ 2` and `A ∈ ℰ_p*(G)`. Any `r ∈ α(M)` would put a rank-3 elementary abelian
inside `M_σ ⊆ C_G(A)`, so `α(M) = ∅`, `r(M) ≤ 2`, and Theorem 4.20(a) makes
`M' ⊆ F(M)` nilpotent. Proposition 10.10 then plants a Sylow `p`-subgroup `P` of `G`
inside `N_G(S)' ⊆ M'`; as the normal Sylow subgroup of the nilpotent `M'` it is
`M`-invariant, forcing `M = N_G(P)` and `p ∈ σ(M)` — contradicting `p ∈ π(K) ⊆ σ(M)'`. -/
theorem rank_centralizer_Msigma_inf_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) :
    rank ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K) ≤ 1 := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set C : Subgroup G := Subgroup.centralizer (Msigma M : Set G) with hCdef
  by_contra hcon
  -- Extract `A ∈ ℰ_p²(G)` with `A ≤ C ⊓ K`.
  obtain ⟨p, hp, hpRank⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥(C ⊓ K)) (n := 2) (by norm_num) (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥(C ⊓ K)) (p := p) (n := 2) (by norm_num) hpRank
  set Abig : Subgroup G := A₀.map (C ⊓ K).subtype with hAbigdef
  have hAbig_ea : Abig.IsElementaryAbelian p := hA₀ea.map (C ⊓ K).subtype_injective
  have hAbig_le : Abig ≤ C ⊓ K := Subgroup.map_subtype_le _
  have hAbig_card : p ^ 2 ≤ Nat.card ↥Abig := by
    rw [hAbigdef, Subgroup.card_map_of_injective (C ⊓ K).subtype_injective]
    calc p ^ 2 ≤ p ^ (Nat.log p (Nat.card ↥A₀)) := Nat.pow_le_pow_right hp.pos hA₀log
    _ ≤ Nat.card ↥A₀ := Nat.pow_log_le_self p Nat.card_pos.ne'
  obtain ⟨A₁, hA₁ea, hA₁card⟩ :=
    OddOrder.GroupTheory.IsElementaryAbelian.exists_subgroup_card_prime_sq hp hAbig_ea
      hAbig_card
  set A : Subgroup G := A₁.map Abig.subtype with hAdef
  have hAea : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.map
    Abig.subtype_injective hA₁ea
  have hAcard : Nat.card ↥A = p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective Abig.subtype_injective]
    exact hA₁card
  have hA2 : A ∈ elemAbelianOfRank G p 2 := ⟨hAea, hAcard⟩
  have hA_le : A ≤ C ⊓ K := (Subgroup.map_subtype_le _).trans hAbig_le
  have hAC : A ≤ C := hA_le.trans inf_le_left
  have hAK : A ≤ K := hA_le.trans inf_le_right
  have hAM : A ≤ M := hAK.trans hKM
  have hpA : p ∈ (Nat.card ↥A).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨Fact.out, by rw [hAcard]; exact dvd_pow_self p two_ne_zero, Nat.card_pos.ne'⟩
  have hpK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_dvd_of_le hAK) Nat.card_pos.ne' hpA
  -- `M_σ ⊆ C_G(A)` (centralizer flip of `A ≤ C`).
  have hMσ_CA : Msigma M ≤ Subgroup.centralizer (A : Set G) := fun m hm => by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAC ha) m hm).symm
  -- Choose `q ∈ σ(M)` via `M_σ ≠ ⊥`, and the Sylow `q`-subgroup `S ≤ M_σ` with `N_G(S) ≤ M`.
  have hMσne : Msigma M ≠ ⊥ := Msigma_ne_bot hG hM
  haveI : Nontrivial ↥(Msigma M) := (Subgroup.nontrivial_iff_ne_bot _).mpr hMσne
  obtain ⟨q, hq⟩ : ∃ q, q ∈ (Nat.card ↥(Msigma M)).primeFactors := by
    rcases (Nat.card ↥(Msigma M)).primeFactors.eq_empty_or_nonempty with h | h
    · rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
      · exact absurd h0 Nat.card_pos.ne'
      · exact absurd h1 Finite.one_lt_card.ne'
    · exact h
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  have hqσ : q ∈ sigma M := Msigma_isPiGroup M q hq
  obtain ⟨S, hSM, hNS_M⟩ := exists_sylow_le_normalizer_le_of_mem_sigma hqσ
  have hSpi : Ch03.Subgroup.IsPiGroup (sigma M) (S : Subgroup G) := fun r hr => by
    have hrq : r ∈ ({q} : Set ℕ) :=
      isPiSubgroup_singleton_of_isPGroup S.isPGroup' r hr
    rwa [Set.mem_singleton_iff.mp hrq]
  have hS_Mσ : (S : Subgroup G) ≤ Msigma M :=
    sigma_subgroup_le_Msigma_of_isHall (Msigma_isHall hG hM) hSM hSpi
  -- `S ∈ ℋ_G*(A; q)`: `A` centralizes (hence normalizes) `S`, and `S` is Sylow-maximal.
  have hA_NS : A ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun s hs => hS_Mσ hs) (hAC ha))
  have hSstar : (S : Subgroup G) ∈ hInvariantStar ⊤ A {q} := by
    refine ⟨mem_hInvariant.mpr
      ⟨le_top, hA_NS, isPiSubgroup_singleton_of_isPGroup S.isPGroup'⟩, ?_⟩
    intro Q' hQ' hSQ'
    exact S.3 (isPGroup_of_isPiSubgroup_singleton (mem_hInvariant.mp hQ').2.2) hSQ'
  -- `q ∈ π(C_G(A))`: the nontrivial Sylow `S` lies in `M_σ ⊆ C_G(A)`.
  have hq_dvd_S : q ∣ Nat.card ↥(S : Subgroup G) := by
    have hcard : Nat.card ↥(S : Subgroup G) * (S : Subgroup G).index = Nat.card G :=
      Subgroup.card_mul_index _
    have hq_dvd_G : q ∣ Nat.card G :=
      ((Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le (Msigma_le M))).trans
        (Subgroup.card_subgroup_dvd_card M)
    rcases (Nat.Prime.dvd_mul Fact.out).mp (hcard ▸ hq_dvd_G) with h | h
    · exact h
    · exact absurd h S.not_dvd_index
  have hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out,
      hq_dvd_S.trans (Subgroup.card_dvd_of_le (hS_Mσ.trans hMσ_CA)), Nat.card_pos.ne'⟩
  -- `A ∉ 𝒰` by part (a); the Uniqueness Theorem in contrapositive forms.
  have hAnotU : ¬ IsUniquelyMaximal A :=
    sigma_complement_not_isUniquelyMaximal hG hM hAM (fun r hr =>
      hKpi r (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hAK) Nat.card_pos.ne' hr))
  have hAmax : IsMaximalElementaryAbelian p A := by
    by_contra hAns
    exact hAnotU (Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns)
  have h2A : 2 ≤ rank ↥A := by
    have hlog : Nat.log p (Nat.card ↥A) = 2 := by
      rw [hAcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
    exact le_trans (le_of_eq hlog.symm)
      (hAea.log_card_le_pRank.trans (pRank_le_rank (G := ↥A) p))
  have hAlt : A < ⊤ :=
    lt_of_le_of_lt hAM (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1)
  have hrCA : rank ↥(Subgroup.centralizer (A : Set G)) ≤ 2 := by
    by_contra hcon3
    exact hAnotU (Ch2.S09.uniquenessTheorem hG hAlt h2A (Or.inr (by omega)))
  -- `α(M) = ∅`, hence `r(M) ≤ 2`: a rank-3 elementary abelian for `r ∈ α(M)` would lie
  -- in `M_σ ⊆ C_G(A)` and contradict `r(C_G(A)) ≤ 2`.
  have hrankM : rank ↥M ≤ 2 := by
    rw [rank_le_iff]
    intro r hr
    haveI : Fact r.Prime := ⟨hr⟩
    by_contra hcon3
    have h3r : 3 ≤ pRank ↥M r := by omega
    obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
        (G := ↥M) (p := r) (n := 3) (by norm_num) h3r
    set B : Subgroup G := B₀.map M.subtype with hBdef
    have hBea : B.IsElementaryAbelian r := hB₀ea.map M.subtype_injective
    have hB_le_M : B ≤ M := Subgroup.map_subtype_le _
    have hBpi : Ch03.Subgroup.IsPiGroup (sigma M) B := fun s hs => by
      have hsr : s ∈ ({r} : Set ℕ) :=
        isPiSubgroup_singleton_of_isPGroup hBea.isPGroup s hs
      rw [Set.mem_singleton_iff.mp hsr]
      exact alpha_subset_sigma hG hM ((mem_alpha_iff M r).mpr
        ⟨Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega), h3r⟩)
    have hB_CA : B ≤ Subgroup.centralizer (A : Set G) :=
      (sigma_subgroup_le_Msigma_of_isHall (Msigma_isHall hG hM) hB_le_M hBpi).trans hMσ_CA
    have hcardB : Nat.card ↥B = Nat.card ↥B₀ := by
      rw [hBdef, Subgroup.card_map_of_injective M.subtype_injective]
    have h3CA : 3 ≤ pRank ↥(Subgroup.centralizer (A : Set G)) r := by
      refine le_trans ?_ (le_pRank (B.subgroupOf (Subgroup.centralizer (A : Set G)))
        (IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_CA).symm hBea))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_CA).toEquiv, hcardB]
      exact hB₀log
    have := h3CA.trans (pRank_le_rank (G := ↥(Subgroup.centralizer (A : Set G))) r)
    omega
  -- Theorem 4.20(a): `M' ⊆ F(M)`, so `M' = derivedInG M` is nilpotent.
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr
    (hG.ne_bot_of_isCoatom (mem_maximalSubgroups.mp hM))
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hderM : commutator ↥M ≤ Ch01.fitting ↥M :=
    OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hModd
      (le_trans (rank_le_of_injective (Subgroup.subtype_injective (Ch01.fitting ↥M))) hrankM)
  haveI hM'nil : Group.IsNilpotent ↥(derivedInG M) := by
    haveI : Group.IsNilpotent ↥(Ch01.fitting ↥M) := Ch01.fitting.isNilpotent
    haveI : Group.IsNilpotent ↥(commutator ↥M) :=
      nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hderM)
    exact nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective)
  -- Proposition 10.10: a Sylow `p`-subgroup `P` of `G` with `A ≤ P ≤ N_G(S)' ⊆ M'`.
  have hpq : p ≠ q := fun h => hKpi p hpK (h ▸ hqσ)
  obtain ⟨P, hAP, -, hP_der, -⟩ := normalizer_factorization hG hpq hA2 hAmax hSstar hqc
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hP_le_M' : (P : Subgroup G) ≤ derivedInG M := by
    refine hP_der.trans ?_
    rw [show derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) =
        ⁅Subgroup.normalizer ((S : Subgroup G) : Set G),
          Subgroup.normalizer ((S : Subgroup G) : Set G)⁆ from
        Subgroup.map_subtype_commutator _,
      show derivedInG M = ⁅(M : Subgroup G), M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono hNS_M hNS_M
  have hP_le_M : (P : Subgroup G) ≤ M := hP_le_M'.trans hM'_le_M
  -- `M` normalizes `M' = derivedInG M`, and the Sylow `p`-subgroup of the nilpotent `M'`
  -- is normal, hence unique, hence `M`-invariant: `M ≤ N_G(P)`.
  have hM_norm_M' : M ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) := by
    rw [derivedInG]
    have hle := Subgroup.le_normalizer_map (H := commutator ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  have hM_le_NP : M ≤ Subgroup.normalizer (((P : Subgroup G) : Subgroup G) : Set G) := by
    intro m hm
    refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
    -- `m • P` is another Sylow `p`-subgroup of `G` inside `M'` (as `m` normalizes `M'`),
    -- and the nilpotent `M'` has a unique (normal) Sylow `p`-subgroup.
    have hsmul_le : ((m • P : Sylow p G) : Subgroup G) ≤ derivedInG M := by
      rw [Sylow.coe_subgroup_smul, conjSmul_eq_map]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hM_norm_M' hm) x).mp (hP_le_M' hx)
    obtain ⟨Q₁, hQ₁⟩ := sylow_subgroupOf_of_le (m • P) hsmul_le
    obtain ⟨Q₂, hQ₂⟩ := sylow_subgroupOf_of_le P hP_le_M'
    haveI : (Q₁ : Subgroup ↥(derivedInG M)).Normal := Ch01.Sylow.normal_of_isNilpotent Q₁
    haveI : (Q₂ : Subgroup ↥(derivedInG M)).Normal := Ch01.Sylow.normal_of_isNilpotent Q₂
    obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq ↥(derivedInG M) Q₁ Q₂
    rw [Sylow.smul_eq_of_normal (g := g') (P := Q₁)] at hg'
    have hcarrier : ((m • P : Sylow p G) : Subgroup G).subgroupOf (derivedInG M) =
        (P : Subgroup G).subgroupOf (derivedInG M) := by
      rw [← hQ₁, ← hQ₂, hg']
    have hcoe := congrArg (Subgroup.map (derivedInG M).subtype) hcarrier
    rw [Subgroup.map_subgroupOf_eq_of_le hsmul_le,
      Subgroup.map_subgroupOf_eq_of_le hP_le_M'] at hcoe
    exact Sylow.ext hcoe
  -- `N_G(P) = M` (maximality), so `p ∈ σ(M)` — contradicting `p ∈ π(K) ⊆ σ(M)'`.
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro h
    have hAbot : A = ⊥ := le_bot_iff.mp (h ▸ hAP)
    rw [hAbot, Subgroup.card_bot] at hAcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hAcard.symm
  have hNP_lt_top : Subgroup.normalizer ((P : Subgroup G) : Set G) < ⊤ := by
    rcases (le_top : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ ⊤).lt_or_eq with h | h
    · exact h
    · exfalso
      haveI : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases hG.simple.eq_bot_or_eq_top_of_normal (P : Subgroup G) inferInstance with h' | h'
      · exact hPne h'
      · exact (mem_maximalSubgroups.mp hM).1
          (top_le_iff.mp (h' ▸ hP_le_M : (⊤ : Subgroup G) ≤ M))
  have hNP_eq : Subgroup.normalizer ((P : Subgroup G) : Set G) = M := by
    by_contra hne
    exact hNP_lt_top.ne ((mem_maximalSubgroups.mp hM).2 _
      (lt_of_le_of_ne hM_le_NP (Ne.symm hne)))
  have hpσ : p ∈ sigma M := by
    rw [mem_sigma_iff]
    refine ⟨Nat.primeFactors_mono (Subgroup.card_dvd_of_le hAM) Nat.card_pos.ne' hpA, ?_⟩
    obtain ⟨Psyl, hPsyl⟩ := sylow_subgroupOf_of_le P hP_le_M
    exact ⟨Psyl, by
      rw [hPsyl, Subgroup.map_subgroupOf_eq_of_le hP_le_M]
      exact hNP_eq.le⟩
  exact hKpi p hpK hpσ

/-- **BG Proposition 10.11 (a)(b)(c)** (mmd L2856): `M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群とする。
(a) `K ∉ 𝒰`; (b) `r(C_K(M_σ)) ≤ 1`; (c) `C_K(M_σ) ∩ M'` は cyclic で `M` に normal。
(原典 (d) は `sigma_complement_commutator_cyclic_normal` として別 theorem に露出。) -/
theorem sigma_complement_rank_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) :
    ¬ IsUniquelyMaximal K ∧
    rank ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K) ≤ 1 ∧
    (IsCyclic ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M) ∧
      M ≤ Subgroup.normalizer
        ((Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M : Subgroup G) :
          Set G)) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  refine ⟨sigma_complement_not_isUniquelyMaximal hG hM hKM hKpi,
    rank_centralizer_Msigma_inf_le_one hG hM hKM hKpi, ?_⟩
  -- Part (c). Set `Z := O_{σ(M)'}(F(M))`; `Z` is `M`-invariant.
  set F : Subgroup G := Ch2.S08.fittingInG M with hFdef
  set Z : Subgroup G := opiCoreInG (sigma M)ᶜ F with hZdef
  have hZ_le_F : Z ≤ F := opiCoreInG_le _ _
  have hZ_le_M : Z ≤ M := hZ_le_F.trans (Ch2.S08.fittingInG_le M)
  have hZpi : Subgroup.IsPiSubgroup (sigma M)ᶜ Z := isPiSubgroup_opiCoreInG _ _
  have hM_le_NF : M ≤ Subgroup.normalizer (F : Set G) := fun m hm =>
    Ch2.S08.zpowers_le_normalizer_fittingInG_of_mem hm (Subgroup.mem_zpowers m)
  have hM_le_NZ : M ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ hM_le_NF
  -- `[Z, M_σ] ≤ Z ⊓ M_σ = ⊥` (both are normal in `M`, with coprime π-types):
  -- `Z ≤ C_G(M_σ)`.
  have hM_le_NMσ : M ≤ Subgroup.normalizer (Msigma M : Set G) := by
    rw [Msigma]
    exact le_normalizer_opiCoreInG (sigma M) M
  haveI hZ_norm : (Z.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZ_le_M).mpr hM_le_NZ
  haveI hMσ_norm : ((Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Msigma_le M)).mpr hM_le_NMσ
  have hZ_le_C : Z ≤ Subgroup.centralizer (Msigma M : Set G) := by
    have hinf : (Msigma M).subgroupOf M ⊓ Z.subgroupOf M = ⊥ := by
      refine inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (π := sigma M) ?_ ?_
      · intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Msigma_le M)).toEquiv] at hr
        exact Msigma_isPiGroup M r hr
      · intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_M).toEquiv] at hr
        exact hZpi r hr
    have hcomm_bot : ⁅Z.subgroupOf M, (Msigma M).subgroupOf M⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅Z.subgroupOf M, (Msigma M).subgroupOf M⁆
          ≤ Z.subgroupOf M ⊓ (Msigma M).subgroupOf M :=
            Subgroup.commutator_le_inf (Z.subgroupOf M) ((Msigma M).subgroupOf M)
        _ = ⊥ := by rw [inf_comm]; exact hinf
    have hZ'C : Z.subgroupOf M ≤ Subgroup.centralizer ((Msigma M).subgroupOf M : Set ↥M) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := Subgroup.mem_centralizer_iff.mp
      (hZ'C (Subgroup.mem_subgroupOf.mpr hz : (⟨z, hZ_le_M hz⟩ : ↥M) ∈ Z.subgroupOf M))
      ⟨m, Msigma_le M hm⟩ (Subgroup.mem_subgroupOf.mpr hm)
    exact congrArg Subtype.val h
  -- Part (b) applied to `Z` (which lies in `C_G(M_σ)`): `r(Z) ≤ 1`, so `Z` is cyclic.
  have hZrank : rank ↥Z ≤ 1 := by
    have h := rank_centralizer_Msigma_inf_le_one hG hM hZ_le_M hZpi
    rwa [inf_eq_right.mpr hZ_le_C] at h
  haveI hFnil : Group.IsNilpotent ↥F := Ch2.S08.fittingInG_isNilpotent M
  haveI hZnil : Group.IsNilpotent ↥Z :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZ_le_F)
  have hZodd : Odd (Nat.card ↥Z) :=
    hG.odd.of_dvd_nat ((Subgroup.card_dvd_of_le hZ_le_M).trans
      (Subgroup.card_subgroup_dvd_card M))
  haveI hZcyc : IsCyclic ↥Z := by
    haveI : _root_.IsZGroup ↥Z := by
      rw [isZGroup_iff]
      intro r hr R
      haveI : Fact r.Prime := ⟨hr⟩
      rcases eq_or_ne r 2 with rfl | hrne
      · -- `|Z|` is odd, so the Sylow `2`-subgroup is trivial.
        have h2 : ¬ 2 ∣ Nat.card ↥Z := by
          rw [Nat.odd_iff] at hZodd
          omega
        have hR1 : Nat.card ↥(R : Subgroup ↥Z) = 1 := by
          obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · simpa using hk
          · exact absurd ((dvd_pow_self 2 hkpos.ne').trans
              (hk ▸ (R : Subgroup ↥Z).card_subgroup_dvd_card)) h2
        haveI : Subsingleton ↥(R : Subgroup ↥Z) :=
          (Nat.card_eq_one_iff_unique.mp hR1).1
        infer_instance
      · -- odd primes: `pRank ≤ rank Z ≤ 1` makes the Sylow cyclic.
        exact isCyclic_of_pRank_le_one R.isPGroup' (hr.odd_of_ne_two hrne)
          (le_trans (pRank_le_of_injective (Subgroup.subtype_injective _))
            (le_trans (pRank_le_rank (G := ↥Z) r) hZrank))
    infer_instance
  -- `M' ≤ C_G(Z)`: the conjugation map `M → Aut(Z)` kills commutators (Aut cyclic abelian).
  have hψ_apply : ∀ (m : ↥M) (z : ↥Z),
      (((Subgroup.normalizerMonoidHom Z).comp (Subgroup.inclusion hM_le_NZ) m) z : G) =
        (m : G) * (z : G) * (m : G)⁻¹ := fun m z => rfl
  have hAutComm : ∀ x y : MulAut ↥Z, x * y = y * x := fun x y => by
    apply (IsCyclic.mulAutMulEquiv (G := ↥Z)).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hM'_le_CZ : derivedInG M ≤ Subgroup.centralizer (Z : Set G) := by
    rw [show derivedInG M = ⁅(M : Subgroup G), M⁆ from Subgroup.map_subtype_commutator M,
      Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    set ψ : ↥M →* MulAut ↥Z :=
      (Subgroup.normalizerMonoidHom Z).comp (Subgroup.inclusion hM_le_NZ) with hψdef
    have h1 : ψ ⁅(⟨g₁, hg₁⟩ : ↥M), (⟨g₂, hg₂⟩ : ↥M)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (hAutComm _ _)
    have h2 : ((ψ ⁅(⟨g₁, hg₁⟩ : ↥M), (⟨g₂, hg₂⟩ : ↥M)⁆) ⟨z, hz⟩ : G) = z := by
      rw [h1]
      rfl
    rw [hψ_apply] at h2
    have hcoe : ((⁅(⟨g₁, hg₁⟩ : ↥M), (⟨g₂, hg₂⟩ : ↥M)⁆ : ↥M) : G) = ⁅g₁, g₂⁆ := rfl
    rw [hcoe] at h2
    calc z * ⁅g₁, g₂⁆ = (⁅g₁, g₂⁆ * z * ⁅g₁, g₂⁆⁻¹) * ⁅g₁, g₂⁆ := by rw [h2]
      _ = ⁅g₁, g₂⁆ * z := by group
  -- `X := C_K(M_σ) ∩ M'` centralizes `F(M) = O_σ(F)·Z` (it centralizes `M_σ ⊇ O_σ(F)`
  -- and `Z`), so `X ≤ C_M(F(M)) ≤ F(M)`; being a `σ'`-group, `X ≤ O_{σ'}(F(M)) = Z`.
  set X : Subgroup G := Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M
    with hXdef
  have hX_le_K : X ≤ K := inf_le_left.trans inf_le_right
  have hX_le_M : X ≤ M := hX_le_K.trans hKM
  have hX_le_CMσ : X ≤ Subgroup.centralizer (Msigma M : Set G) :=
    inf_le_left.trans inf_le_left
  have hX_le_M' : X ≤ derivedInG M := inf_le_right
  have hFσ_le_Mσ : opiCoreInG (sigma M) F ≤ Msigma M :=
    sigma_subgroup_le_Msigma_of_isHall (Msigma_isHall hG hM)
      ((opiCoreInG_le _ _).trans (Ch2.S08.fittingInG_le M))
      (isPiSubgroup_opiCoreInG _ _)
  have hX_le_CF : X ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    -- decompose `f = s * z` inside the nilpotent `F`
    haveI : (Ch03.oPiCore {p | p ∉ sigma M} ↥F).Normal := by
      haveI := Ch03.oPiCore.characteristic ({p | p ∉ sigma M} : Set ℕ) ↥F
      infer_instance
    have hf_sup : (⟨f, hf⟩ : ↥F) ∈
        Ch03.oPiCore (sigma M) ↥F ⊔ Ch03.oPiCore {p | p ∉ sigma M} ↥F :=
      top_le_oPiCore_sup_compl_of_isNilpotent (sigma M) (Subgroup.mem_top _)
    have hf_sup' : (⟨f, hf⟩ : ↥F) ∈
        ((Ch03.oPiCore (sigma M) ↥F : Subgroup ↥F) : Set ↥F) *
        ((Ch03.oPiCore {p | p ∉ sigma M} ↥F : Subgroup ↥F) : Set ↥F) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right
        (Ch03.oPiCore (sigma M) ↥F) (Ch03.oPiCore {p | p ∉ sigma M} ↥F)
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)]
      exact hf_sup
    obtain ⟨s, hs, zz, hzz, hszz⟩ := hf_sup'
    -- ambient versions: `↑s ∈ M_σ`, `↑zz ∈ Z`
    have hs_Mσ : (s : G) ∈ Msigma M := hFσ_le_Mσ ⟨s, hs, rfl⟩
    have hzz_Z : (zz : G) ∈ Z := ⟨zz, hzz, rfl⟩
    have hxs : (s : G) * x = x * (s : G) :=
      Subgroup.mem_centralizer_iff.mp (hX_le_CMσ hx) _ hs_Mσ
    have hxz : (zz : G) * x = x * (zz : G) :=
      Subgroup.mem_centralizer_iff.mp (hM'_le_CZ (hX_le_M' hx)) _ hzz_Z
    have hfsz : f = (s : G) * (zz : G) := by
      have := congrArg (Subtype.val : ↥F → G) hszz
      exact this.symm
    rw [hfsz, mul_assoc, hxz, ← mul_assoc, hxs, mul_assoc]
  have hX_le_F : X ≤ F := fun x hx =>
    Ch2.S08.centralizer_fittingInG_inf_le_fittingInG ⟨hX_le_CF hx, hX_le_M hx⟩
  have hX_le_Z : X ≤ Z := by
    haveI : (Ch03.oPiCore ((sigma M)ᶜ : Set ℕ) ↥F).Normal := by
      haveI := Ch03.oPiCore.characteristic ((sigma M)ᶜ : Set ℕ) ↥F
      infer_instance
    have hXsub : Ch03.Subgroup.IsPiGroup (sigma M)ᶜ (X.subgroupOf F) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_F).toEquiv] at hr
      exact hKpi r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hX_le_K) Nat.card_pos.ne' hr)
    have hle : X.subgroupOf F ≤ Ch03.oPiCore ((sigma M)ᶜ : Set ℕ) ↥F :=
      isPiGroup_le_of_normal_isHallSubgroup
        (oPiCore_isHall_of_isNilpotent ((sigma M)ᶜ : Set ℕ)) hXsub
    calc X = (X.subgroupOf F).map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hX_le_F).symm
      _ ≤ (Ch03.oPiCore ((sigma M)ᶜ : Set ℕ) ↥F).map F.subtype := Subgroup.map_mono hle
      _ = Z := rfl
  -- Conclude: `X` is cyclic (inside the cyclic `Z`) and `M`-invariant (cyclic uniqueness).
  refine ⟨Subgroup.isCyclic_of_le hX_le_Z, ?_⟩
  intro g hgM
  refine mem_normalizer_of_conj_smul_eq_self ?_
  have hgZ : MulAut.conj g • Z = Z := conj_smul_eq_self_of_mem_normalizer (hM_le_NZ hgM)
  have hle : MulAut.conj g • X ≤ Z := by
    rw [← hgZ]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX_le_Z
  have hcard : Nat.card ↥(MulAut.conj g • X) = Nat.card ↥X := by
    rw [conjSmul_eq_map]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective X _ (MulAut.conj g).injective).toEquiv).symm
  have h1 : (MulAut.conj g • X).subgroupOf Z = X.subgroupOf Z := by
    apply cyclic_subgroup_eq_of_card_eq (C := ↥Z)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_Z).toEquiv, hcard]
  have h2 := congrArg (Subgroup.map Z.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le hX_le_Z] at h2

/-! ## Helpers for Proposition 10.11(d) -/

/-- In a finite nilpotent group, two elements of coprime order commute.

A finite nilpotent group is the internal direct product of its Sylow subgroups
(`Sylow.directProductOfNormal`); two coprime-order elements have disjoint sets of relevant
primes, so in every Sylow factor at least one of their components is trivial. -/
theorem commute_of_coprime_orderOf_of_isNilpotent {L : Type*} [Group L] [Finite L]
    [Group.IsNilpotent L] {x y : L} (hxy : Nat.Coprime (orderOf x) (orderOf y)) :
    Commute x y := by
  classical
  haveI := Fintype.ofFinite L
  have hn : ∀ {q : ℕ} [Fact q.Prime] (Q : Sylow q L), Q.Normal := fun Q =>
    Ch01.Sylow.normal_of_isNilpotent Q
  set e := Sylow.directProductOfNormal hn with he
  -- Componentwise: the `(p, P)`-components of `e.symm x` and `e.symm y` commute in the
  -- `p`-group `↥P`, since at least one of them is trivial.
  have hcomp : ∀ (p : (Nat.card L).primeFactors) (P : Sylow (p : ℕ) L),
      Commute (e.symm x p P) (e.symm y p P) := by
    intro p P
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    -- The order of a component divides the order of the original element.
    have hdvd : ∀ z : L, orderOf (e.symm z p P) ∣ orderOf z := by
      intro z
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (e.symm z) ^ orderOf z = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 := congrFun (congrFun h1 p) P
      simpa [Pi.pow_apply, Pi.one_apply] using h2
    -- Each component has prime-power order (it lies in the `p`-group `↥P`).
    have hppow : ∀ z : L, ∃ k, orderOf (e.symm z p P) = (p : ℕ) ^ k := fun z =>
      (IsPGroup.iff_orderOf.mp P.isPGroup') (e.symm z p P)
    by_cases hpx : (p : ℕ) ∣ orderOf x
    · -- Then `p ∤ orderOf y`, so the `y`-component is trivial.
      have hpy : ¬ (p : ℕ) ∣ orderOf y := fun hpy =>
        (Nat.prime_of_mem_primeFactors p.2).ne_one (Nat.dvd_one.mp (hxy ▸ Nat.dvd_gcd hpx hpy))
      obtain ⟨k, hk⟩ := hppow y
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpy ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd y))
      have hy1 : e.symm y p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hy1]; exact Commute.one_right _
    · -- `p ∤ orderOf x`, so the `x`-component is trivial.
      obtain ⟨k, hk⟩ := hppow x
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpx ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd x))
      have hx1 : e.symm x p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hx1]; exact Commute.one_left _
  -- Assemble componentwise commutation, then transport along the isomorphism `e`.
  have hkey : e.symm x * e.symm y = e.symm y * e.symm x := by
    funext p P
    simpa [Pi.mul_apply] using hcomp p P
  have hcong := congrArg e hkey
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hcong


/-- **BG Lemma 10.5** (mmd MISSING_PAGE, PDF p.87): `p ∈ σ(M)'`, `X ∈ ℰ_p¹(G)`,
`N_G(X) ⊆ M` なら `r_p(M) = 2`、`p` は ideal でなく、`X ⊆ A` となる `A ∈ ℰ_p²(G)` が存在する。 -/
theorem pRank_eq_two_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∉ sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1)
    (hN : Subgroup.normalizer (X : Set G) ≤ M) :
    pRank ↥M p = 2 ∧ ¬ idealPrime p G ∧ ∃ A ∈ elemAbelianOfRank G p 2, X ≤ A := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hXea : X.IsElementaryAbelian p := hX.1
  have hXcard : Nat.card ↥X = p := by simpa using hX.2
  have hXM : X ≤ M := le_trans Subgroup.le_normalizer hN
  have hpdvdM : p ∣ Nat.card ↥M := by rw [← hXcard]; exact Subgroup.card_dvd_of_le hXM
  have hpπ : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, Nat.card_pos.ne'⟩
  have hodd : Odd p := hG.odd.of_dvd_nat (dvd_trans hpdvdM (Subgroup.card_subgroup_dvd_card M))
  have hpα : p ∉ alpha M := fun h => hp (alpha_subset_sigma hG hM h)
  have hr_le : pRank ↥M p ≤ 2 := by
    by_contra h
    exact hpα ⟨hpπ, by omega⟩
  -- Lift `X` into `↥M` and extend to a Sylow `PM` of `↥M`; `P` = its image in `G`.
  have hXMpg : IsPGroup p ↥(X.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hXcard, pow_one])
  obtain ⟨PM, hXPM⟩ := hXMpg.exists_le_sylow
  set P : Subgroup G := (PM : Subgroup ↥M).map M.subtype with hPdef
  have hXP : X ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXPM
  have hPpg : IsPGroup p ↥P := by
    obtain ⟨k, hk⟩ := PM.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [hPdef, ← Nat.card_congr (Subgroup.equivMapOfInjective (PM : Subgroup ↥M) M.subtype
      M.subtype_injective).toEquiv]
    exact hk
  have hPrank : pRank ↥P p = pRank ↥M p := by
    have e : ↥(PM : Subgroup ↥M) ≃* ↥P := by
      rw [hPdef]
      exact Subgroup.equivMapOfInjective (PM : Subgroup ↥M) M.subtype M.subtype_injective
    have h1 : pRank ↥P p ≤ pRank ↥(PM : Subgroup ↥M) p :=
      pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective
    have h2 : pRank ↥(PM : Subgroup ↥M) p ≤ pRank ↥P p :=
      pRank_le_of_injective (f := e.toMonoidHom) e.injective
    have h3 : pRank ↥(PM : Subgroup ↥M) p = pRank ↥M p := pRank_sylow_eq PM
    omega
  -- (i) `pRank = 2`: `≤ 2` from `p ∉ α`; `≥ 2` because rank `1` forces a cyclic Sylow whose
  -- `Ω₁` is `X`, giving `N_G(P) ≤ N_G(X) ≤ M`, i.e. `p ∈ σ(M)`, contrary to `p ∉ σ(M)`.
  have hr2 : pRank ↥M p = 2 := by
    rcases Nat.lt_or_ge (pRank ↥M p) 2 with hlt | hge
    · exfalso
      have hr1 : pRank ↥P p ≤ 1 := by rw [hPrank]; omega
      haveI : IsCyclic ↥P := isCyclic_of_pRank_le_one hPpg hodd hr1
      haveI : Nontrivial ↥P := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        calc 1 < p := (Fact.out : p.Prime).one_lt
          _ = Nat.card ↥X := hXcard.symm
          _ ≤ Nat.card ↥P := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hXP)
      have hWcard : Nat.card ↥(Omega (↥P) p 1) = p :=
        OddOrder.BG.Ch1.S04.card_omega1_eq_prime_of_isCyclic hPpg
      have hXsub : Nat.card ↥(X.subgroupOf P) = p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv, hXcard]
      have heq : X.subgroupOf P = Omega (↥P) p 1 :=
        cyclic_subgroup_eq_of_card_eq (by rw [hXsub, hWcard])
      have hXeq : X = (Omega (↥P) p 1).map P.subtype := by
        rw [← heq, Subgroup.map_subgroupOf_eq_of_le hXP]
      have hNPX : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) := by
        rw [hXeq]
        exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := P) (W := Omega (↥P) p 1)
      apply hp
      rw [mem_sigma_iff]
      exact ⟨hpπ, PM, le_trans hNPX hN⟩
    · omega
  have hnotideal : ¬ idealPrime p G := ((alpha_criterion hG hM).2 p Fact.out hp hr2).1
  refine ⟨hr2, hnotideal, ?_⟩
  -- (iii) `X ≤ A` for some `A ∈ ℰ_p²(G)`: take `A = X·Ω₁(Z(P))`.  Work inside `↥P` with
  -- `X' = X.subgroupOf P` and `Z' = Ω₁(Z(↥P))`; then push the join `A' = X' ⊔ Z'` to `G`.
  haveI : Nontrivial ↥P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p := (Fact.out : p.Prime).one_lt
      _ = Nat.card ↥X := hXcard.symm
      _ ≤ Nat.card ↥P := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hXP)
  have hPrank2 : pRank ↥P p = 2 := hPrank.trans hr2
  -- `X ≠ Ω₁(Z(P))` (else `N_G(P) ≤ N_G(X) ≤ M`, i.e. `p ∈ σ(M)`, contrary to `p ∉ σ(M)`).
  have hXZ₀ : X ≠ omega1CenterInG P p := by
    intro hXeqZ
    apply hp
    rw [mem_sigma_iff]
    refine ⟨hpπ, PM, ?_⟩
    have h1 := normalizer_le_normalizer_omega1CenterInG P p
    rw [← hXeqZ] at h1
    exact le_trans h1 hN
  set Z' : Subgroup ↥P := omega1OfAbelian ↥P (Subgroup.center ↥P) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm) with hZ'def
  set X' : Subgroup ↥P := X.subgroupOf P with hX'def
  have hX'card : Nat.card ↥X' = p := by
    rw [hX'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv, hXcard]
  have hX'ea : X'.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hX'card
  have hZ'ea : Z'.IsElementaryAbelian p := omega1OfAbelian_isElementaryAbelian
  have hX'centZ' : X' ≤ Subgroup.centralizer (Z' : Set ↥P) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (omega1OfAbelian_le hz) x).symm
  have hA'ea : (X' ⊔ Z').IsElementaryAbelian p :=
    hX'ea.sup_of_le_centralizer hZ'ea hX'centZ'
  -- `Z' ≠ ⊥` (center of the nontrivial `p`-group `↥P` has an element of order `p`).
  have hZ'nbot : Z' ≠ ⊥ := by
    obtain ⟨x, -, hxc, hx1, hxp⟩ :=
      exists_mem_omega1_center_of_normal_ne_bot (P := ↥P) hPpg (N := ⊤) top_ne_bot
    intro hbot
    have hxZ' : x ∈ Z' := by rw [hZ'def, mem_omega1OfAbelian]; exact ⟨hxc, hxp⟩
    rw [hbot, Subgroup.mem_bot] at hxZ'
    exact hx1 hxZ'
  -- `Z' ≰ X'` (else `Ω₁(Z(P)) ≤ X`, forcing equality since both are order `p`, contra `X ≠ Z₀`).
  have hZ'X' : ¬ Z' ≤ X' := by
    intro hle
    apply hXZ₀
    have hmap : Z'.map P.subtype ≤ X := by
      have h := Subgroup.map_mono (f := P.subtype) hle
      rwa [hX'def, Subgroup.map_subgroupOf_eq_of_le hXP] at h
    have hZ₀card : Nat.card ↥(Z'.map P.subtype) = p := by
      have hdvd : Nat.card ↥(Z'.map P.subtype) ∣ p := by
        rw [← hXcard]; exact Subgroup.card_dvd_of_le hmap
      rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hpp
      · exfalso
        apply hZ'nbot
        refine Subgroup.card_eq_one.mp ?_
        rwa [Subgroup.card_map_of_injective P.subtype_injective] at h1
      · exact hpp
    show X = omega1CenterInG P p
    have hOmEq : omega1CenterInG P p = Z'.map P.subtype := rfl
    rw [hOmEq]
    exact (Subgroup.eq_of_le_of_card_ge hmap (le_of_eq (by rw [hXcard, hZ₀card]))).symm
  have hX'lt : X' < X' ⊔ Z' := by
    refine lt_of_le_of_ne le_sup_left (fun h => hZ'X' ?_)
    rw [h]; exact le_sup_right
  -- `|A'| = p²`: it is a `p`-power `≤ p²` (`pRank ↥P = 2`) and `> p` (`X' ⊊ A'`).
  obtain ⟨k, hk⟩ := hA'ea.isPGroup.exists_card_eq
  have hub : k ≤ 2 := by
    have hle := le_pRank (X' ⊔ Z') hA'ea
    rwa [hk, Nat.log_pow (Fact.out : p.Prime).one_lt, hPrank2] at hle
  have hlb : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso
      interval_cases k
      · rw [pow_zero] at hk
        have hA'bot : (X' ⊔ Z') = ⊥ := Subgroup.card_eq_one.mp hk
        have hX'bot : X' = ⊥ := le_bot_iff.mp (hA'bot ▸ (le_sup_left : X' ≤ X' ⊔ Z'))
        rw [hX'bot, Subgroup.card_bot] at hX'card
        exact (Fact.out : p.Prime).ne_one hX'card.symm
      · rw [pow_one] at hk
        exact absurd (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [hk, hX'card])))
          (ne_of_lt hX'lt)
    · exact h
  have hA'card : Nat.card ↥(X' ⊔ Z') = p ^ 2 := by rw [hk]; congr 1; omega
  -- Push `A' = X' ⊔ Z'` to `G`.
  refine ⟨(X' ⊔ Z').map P.subtype, ⟨hA'ea.map P.subtype_injective, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hA'card]
  · calc X = X'.map P.subtype := by rw [hX'def, Subgroup.map_subgroupOf_eq_of_le hXP]
      _ ≤ (X' ⊔ Z').map P.subtype := Subgroup.map_mono le_sup_left

/-! ## Proposition 10.11(d) — commutators with `σ(M)'`-subgroups (mmd L2856) -/

/-- **BG Proposition 10.11(d)** (mmd L2856): `M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群とする。
`p ∈ σ(M)'`, `P ∈ ℰ_p¹(N_M(K))`, `C_{M_σ}(P)=1`, かつ `K` が abelian `p'`-group なら、
`[K,P]` は `M_σ` を中心化し、cyclic normal subgroup of `M` である。

This is exposed separately because later §12/§13 arguments need the commutator conclusion,
while Proposition 10.11(a)(b)(c) provides only the rank and cyclic-normal centralizer gate. -/
theorem sigma_complement_commutator_cyclic_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ sigma M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPN : P ≤ Subgroup.normalizer (K : Set G) ⊓ M)
    (hCP : Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hKab : IsMulCommutative ↥K) (hKp' : Subgroup.IsPiSubgroup (({p} : Set ℕ)ᶜ) K) :
    ⁅K, P⁆ ≤ Subgroup.centralizer ((Msigma M : Subgroup G) : Set G) ∧
    IsCyclic ↥(⁅K, P⁆ : Subgroup G) ∧
    M ≤ Subgroup.normalizer ((⁅K, P⁆ : Subgroup G) : Set G) := by
  classical
  haveI := hKab
  set K₀ : Subgroup G := ⁅K, P⁆ with hK₀def
  -- Basic facts about `P`: prime order, normalises `K`, lies in `M`.
  have hPcard : Nat.card ↥P = p := hP.2.trans (pow_one p)
  have hPnorm_K : P ≤ Subgroup.normalizer (K : Set G) := hPN.trans inf_le_left
  have hP_le_M : P ≤ M := hPN.trans inf_le_right
  -- `K` is a `p'`-group, so `(|K|, |P|)` are coprime.
  have hp_ndvd_K : ¬ p ∣ Nat.card ↥K := fun hdvd =>
    (hKp' p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
  have hcop_KP : Nat.Coprime (Nat.card ↥K) (Nat.card ↥P) := by
    rw [hPcard]; exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp_ndvd_K).symm
  -- Step 1: `K = C_K(P) × [K, P]` (coprime action on the abelian `p'`-group `K`).
  obtain ⟨hdec_inf, hdec_sup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := K) (K := P) hPnorm_K hcop_KP
  rw [← hK₀def] at hdec_inf hdec_sup
  -- Step 2: `K₀ = [K, P] ≤ K` and `C_{K₀}(P) = 1`.
  have hK₀_le_K : K₀ ≤ K := le_sup_right.trans_eq hdec_sup
  have hCK₀P : Subgroup.centralizer (P : Set G) ⊓ K₀ = ⊥ := by
    have heq : (Subgroup.centralizer (P : Set G) ⊓ K) ⊓ K₀
        = Subgroup.centralizer (P : Set G) ⊓ K₀ := by
      rw [inf_assoc, inf_eq_right.mpr hK₀_le_K]
    rw [← heq, hdec_inf]
  -- `M` normalises `M_σ` (since `M_σ ⊴ M`).
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((Msigma M) : Set G) := by
    rw [Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  have hK₀_norm_Mσ : K₀ ≤ Subgroup.normalizer ((Msigma M) : Set G) :=
    hK₀_le_K.trans (hKM.trans hM_norm_Mσ)
  -- `P` normalises `K₀ = [K, P]` (the commutator is `P`-invariant).
  have hsmul_K₀ : ∀ g ∈ P, MulAut.conj g • K₀ = K₀ := by
    intro g hg
    have hconjK : MulAut.conj g • K = K := conj_smul_eq_self_of_mem_normalizer (hPnorm_K hg)
    have hconjP : MulAut.conj g • P = P :=
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
    rw [hK₀def, conjSmul_eq_map, Subgroup.map_commutator, ← conjSmul_eq_map, ← conjSmul_eq_map,
      hconjK, hconjP]
  have hP_norm_K₀ : P ≤ Subgroup.normalizer (K₀ : Set G) :=
    fun g hg => mem_normalizer_of_conj_smul_eq_self (hsmul_K₀ g hg)
  -- `P` normalises `K₀ ⊔ M_σ`.
  have hP_norm_L : P ≤ Subgroup.normalizer ((K₀ ⊔ Msigma M : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_smul_eq_self ?_
    rw [Subgroup.smul_sup, hsmul_K₀ g hg,
      conj_smul_eq_self_of_mem_normalizer (hM_norm_Mσ (hP_le_M hg))]
  -- `K₀` and `M_σ` are coprime (`K₀ ≤ K` is `σ'`, `M_σ` is `σ`).
  have hK₀_pi' : ∀ q ∈ (Nat.card ↥K₀).primeFactors, q ∈ (sigma M)ᶜ := fun q hq =>
    hKpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hK₀_le_K) Nat.card_pos.ne' hq)
  have hMσ_sig : ∀ q ∈ (Nat.card ↥(Msigma M)).primeFactors, q ∈ sigma M := Msigma_isPiGroup M
  have hcop_K₀Mσ : Nat.Coprime (Nat.card ↥K₀) (Nat.card ↥(Msigma M)) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' hK₀_pi' (fun q hq hqc => hqc (hMσ_sig q hq))
  -- `K₀ ⊔ M_σ` is a `p'`-group (both factors are `p'`).
  have hK₀_p' : ∀ q ∈ (Nat.card ↥K₀).primeFactors, q ≠ p := fun q hq =>
    hKp' q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hK₀_le_K) Nat.card_pos.ne' hq)
  have hMσ_p' : ∀ q ∈ (Nat.card ↥(Msigma M)).primeFactors, q ≠ p :=
    fun q hq hqp => hp (hqp ▸ hMσ_sig q hq)
  have hL_p' : ¬ p ∣ Nat.card ↥(K₀ ⊔ Msigma M) := by
    intro hdvd
    have hcard_eq : Nat.card ↥(K₀ ⊔ Msigma M) * Nat.card ↥(K₀ ⊓ Msigma M)
        = Nat.card ↥K₀ * Nat.card ↥(Msigma M) := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card K₀ (Msigma M)
      rwa [show (↑K₀ * ↑(Msigma M) : Set G) = ↑(K₀ ⊔ Msigma M : Subgroup G) from
        (Subgroup.coe_mul_of_left_le_normalizer_right K₀ (Msigma M) hK₀_norm_Mσ).symm] at h_hk
    have hdvd_prod : p ∣ Nat.card ↥K₀ * Nat.card ↥(Msigma M) := by
      rw [← hcard_eq]; exact hdvd.mul_right _
    rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd_prod with hK₀d | hMσd
    · exact hK₀_p' p (Nat.mem_primeFactors.mpr ⟨Fact.out, hK₀d, Nat.card_pos.ne'⟩) rfl
    · exact hMσ_p' p (Nat.mem_primeFactors.mpr ⟨Fact.out, hMσd, Nat.card_pos.ne'⟩) rfl
  have hdisj : Disjoint (K₀ ⊔ Msigma M) P := by
    refine disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime ?_)
    rw [hPcard]; exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hL_p').symm
  -- Degenerate case: `K₀ ⊔ M_σ = 1` forces `K₀ = 1` and all conclusions are trivial.
  by_cases hLbot : (K₀ ⊔ Msigma M) = ⊥
  · have hK₀bot : K₀ = ⊥ := le_bot_iff.mp (le_sup_left.trans_eq hLbot)
    refine ⟨by rw [hK₀bot]; exact bot_le, by rw [hK₀bot]; infer_instance, ?_⟩
    rw [hK₀bot]
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    refine ⟨fun hh => by rw [hh]; group, fun hh => ?_⟩
    have h1 : g * h * g⁻¹ = g * 1 * g⁻¹ := by rw [hh]; group
    exact mul_left_cancel (mul_right_cancel h1)
  -- Main case.  Step 3-4: `P` acts fixed-point-freely on `K₀ ⊔ M_σ`, so it is nilpotent (Thm 3.7).
  have hPne : P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hPcard; exact (Fact.out : p.Prime).one_lt.ne hPcard
  have hK₀_inf_Mσ : K₀ ⊓ Msigma M = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop_K₀Mσ
  have hFPF : ∀ r ∈ P, r ≠ 1 → ∀ n ∈ (K₀ ⊔ Msigma M), n ≠ 1 → r * n * r⁻¹ ≠ n := by
    intro r hrP hr1 n hnL hn1 hcontra
    -- Decompose `n = k * m` with `k ∈ K₀`, `m ∈ M_σ`.
    have hnL' : n ∈ (↑K₀ * ↑(Msigma M) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₀ (Msigma M) hK₀_norm_Mσ]; exact hnL
    obtain ⟨k, hk, m, hm, hkm⟩ := hnL'
    replace hkm : k * m = n := hkm
    -- Conjugation by `r` preserves `K₀` and `M_σ`.
    have hrkr : r * k * r⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hP_norm_K₀ hrP) k).mp hk
    have hrmr : r * m * r⁻¹ ∈ Msigma M :=
      (Subgroup.mem_normalizer_iff.mp (hM_norm_Mσ (hP_le_M hrP)) m).mp hm
    -- `(r k r⁻¹)(r m r⁻¹) = k m` and the decomposition `K₀ × M_σ` is unique.
    have hrnr_eq : (r * k * r⁻¹) * (r * m * r⁻¹) = k * m := by
      rw [show (r * k * r⁻¹) * (r * m * r⁻¹) = r * (k * m) * r⁻¹ from by group, hkm, hcontra]
    have halg : k⁻¹ * (r * k * r⁻¹) = m * (r * m * r⁻¹)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hrnr_eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hz_mem : k⁻¹ * (r * k * r⁻¹) ∈ K₀ ⊓ Msigma M := by
      refine ⟨K₀.mul_mem (K₀.inv_mem hk) hrkr, ?_⟩
      rw [halg]; exact (Msigma M).mul_mem hm ((Msigma M).inv_mem hrmr)
    have hz1 : k⁻¹ * (r * k * r⁻¹) = 1 := by
      rw [hK₀_inf_Mσ, Subgroup.mem_bot] at hz_mem; exact hz_mem
    have hak : r * k * r⁻¹ = k := (inv_mul_eq_one.mp hz1).symm
    have hmb : r * m * r⁻¹ = m := by
      have hm1 : m * (r * m * r⁻¹)⁻¹ = 1 := by rw [← halg]; exact hz1
      exact (mul_inv_eq_one.mp hm1).symm
    -- `r` (order `p`) generates `P`, so `k, m ∈ C_G(P)`.
    have hzple : Subgroup.zpowers r ≤ P := Subgroup.zpowers_le.mpr hrP
    have hdvd_r : Nat.card ↥(Subgroup.zpowers r) ∣ p := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hzple
    have hne1 : Nat.card ↥(Subgroup.zpowers r) ≠ 1 := fun hh =>
      hr1 (Subgroup.zpowers_eq_bot.mp (Subgroup.eq_bot_of_card_eq _ hh))
    have hcardzp : Nat.card ↥(Subgroup.zpowers r) = p :=
      ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd_r).resolve_left hne1
    have hzp : Subgroup.zpowers r = P :=
      Subgroup.eq_of_le_of_card_ge hzple (hPcard.trans hcardzp.symm).le
    have hk_comm_r : Commute r k := mul_inv_eq_iff_eq_mul.mp hak
    have hm_comm_r : Commute r m := mul_inv_eq_iff_eq_mul.mp hmb
    have hkC : k ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [← hzp] at hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_left hk_comm_r j)
    have hmC : m ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [← hzp] at hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_left hm_comm_r j)
    -- `k ∈ C_{K₀}(P) = 1` and `m ∈ C_{M_σ}(P) = 1`, so `n = 1`, a contradiction.
    have hk1 : k = 1 := by
      have hmem : k ∈ Subgroup.centralizer (P : Set G) ⊓ K₀ := ⟨hkC, hk⟩
      rw [hCK₀P, Subgroup.mem_bot] at hmem; exact hmem
    have hm1 : m = 1 := by
      have hmem : m ∈ Msigma M ⊓ Subgroup.centralizer (P : Set G) := ⟨hm, hmC⟩
      rw [hCP, Subgroup.mem_bot] at hmem; exact hmem
    exact hn1 (by rw [← hkm, hk1, hm1, one_mul])
  -- Solvability of `(K₀ ⊔ M_σ) ⊔ P` (proper subgroup of the minimal simple group).
  have hLP_le_M : (K₀ ⊔ Msigma M) ⊔ P ≤ M :=
    sup_le (sup_le (hK₀_le_K.trans hKM) (Msigma_le M)) hP_le_M
  haveI hMsol : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI : IsSolvable ↥((K₀ ⊔ Msigma M) ⊔ P) :=
    solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLP_le_M).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLP_le_M).surjective
  haveI hLnil : Group.IsNilpotent ↥(K₀ ⊔ Msigma M) :=
    OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      hP_norm_L hdisj hLbot hPne ⟨p, Fact.out, hPcard⟩ hFPF
  -- Step 5: `K₀` centralises `M_σ` (coprime-order subgroups of the nilpotent `K₀ ⊔ M_σ` commute).
  have hstep5 : K₀ ≤ Subgroup.centralizer ((Msigma M) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hkL : k ∈ K₀ ⊔ Msigma M := Subgroup.mem_sup_left hk
    have hmL : m ∈ K₀ ⊔ Msigma M := Subgroup.mem_sup_right hm
    have hcop_km : Nat.Coprime (orderOf (⟨k, hkL⟩ : ↥(K₀ ⊔ Msigma M)))
        (orderOf (⟨m, hmL⟩ : ↥(K₀ ⊔ Msigma M))) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact (hcop_K₀Mσ.coprime_dvd_left (Subgroup.orderOf_dvd_natCard K₀ hk)).coprime_dvd_right
        (Subgroup.orderOf_dvd_natCard (Msigma M) hm)
    have hcomm := commute_of_coprime_orderOf_of_isNilpotent (L := ↥(K₀ ⊔ Msigma M))
      (x := ⟨k, hkL⟩) (y := ⟨m, hmL⟩) hcop_km
    exact (congrArg Subtype.val hcomm).symm
  -- Step 6: cite Proposition 10.11(c) and place `K₀` inside the cyclic normal `Z`.
  obtain ⟨-, -, hZcyc, hM_NZ⟩ := sigma_complement_rank_le_one hG hM hKM hKpi
  set Z : Subgroup G :=
    Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M with hZdef
  have hK₀_der : K₀ ≤ derivedInG M := by
    rw [hK₀def, show derivedInG M = ⁅(M : Subgroup G), M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono hKM hP_le_M
  have hK₀_le_Z : K₀ ≤ Z := le_inf (le_inf hstep5 hK₀_le_K) hK₀_der
  haveI : IsCyclic ↥Z := hZcyc
  refine ⟨hstep5, Subgroup.isCyclic_of_le hK₀_le_Z, ?_⟩
  -- `K₀` is characteristic in the cyclic `Z`, hence normalised by `M ≤ N_G(Z)`.
  intro g hgM
  refine mem_normalizer_of_conj_smul_eq_self ?_
  have hgZ : MulAut.conj g • Z = Z := conj_smul_eq_self_of_mem_normalizer (hM_NZ hgM)
  have hle : MulAut.conj g • K₀ ≤ Z := by
    rw [← hgZ]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hK₀_le_Z
  have hcard : Nat.card ↥(MulAut.conj g • K₀) = Nat.card ↥K₀ := by
    rw [conjSmul_eq_map]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective K₀ _ (MulAut.conj g).injective).toEquiv).symm
  have h1 : (MulAut.conj g • K₀).subgroupOf Z = K₀.subgroupOf Z := by
    apply cyclic_subgroup_eq_of_card_eq (C := ↥Z)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀_le_Z).toEquiv, hcard]
  have h2 := congrArg (Subgroup.map Z.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le hK₀_le_Z] at h2

/-! ## Helpers for Lemma 10.12 -/

/-- **Core of BG Lemma 10.12** (book p.79): if `p ∈ σ(M) ∩ σ(H)` with `M`, `H` non-conjugate
maximal subgroups, then `p ∉ α(M)` and `M_σ` is not nilpotent. The argument takes a common
Sylow `p`-subgroup `S` of `G` lying in `M` and in a conjugate `H^g` (`M ≠ H^g`); the Uniqueness
Theorem forces `r(S) ≤ 2` (whence `p ∉ α(M)`), and `N_G(S) ⊆ H^g ≠ M` makes `S` non-normal in
`M`, ruling out `M_σ` nilpotent (else its Sylow `S` would be characteristic in `M_σ ⊴ M`). -/
private theorem mem_sigma_inter_sigma_imp [Finite G] (hG : IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = H) {p : ℕ} [Fact p.Prime]
    (hpM : p ∈ sigma M) (hpH : p ∈ sigma H) :
    p ∉ alpha M ∧ ¬ Group.IsNilpotent ↥(Msigma M) := by
  classical
  obtain ⟨SM, hSM_le, _hSM_norm⟩ := exists_sylow_le_normalizer_le_of_mem_sigma hpM
  obtain ⟨SH, hSH_le, hSH_norm⟩ := exists_sylow_le_normalizer_le_of_mem_sigma hpH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SH SM
  set Hg : Subgroup G := MulAut.conj g • H with hHg
  have hSMeq : (SM : Subgroup G) = MulAut.conj g • (SH : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hS_le_Hg : (SM : Subgroup G) ≤ Hg := by
    rw [hSMeq, hHg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSH_le
  have hSnorm_Hg : Subgroup.normalizer ((SM : Subgroup G) : Set G) ≤ Hg := by
    have h1 : (SM : Subgroup G) = (SH : Subgroup G).map (MulAut.conj g : G →* G) :=
      hSMeq.trans (conjSmul_eq_map _ _)
    rw [h1, ← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hHg,
      show (MulAut.conj g • H) = H.map (MulAut.conj g : G →* G) from conjSmul_eq_map _ _]
    exact Subgroup.map_mono hSH_norm
  -- `M ≠ H^g` and both are maximal.
  have hHg_max : IsCoatom Hg := by
    rw [hHg, conjSmul_eq_map]
    exact (OrderIso.isCoatom_iff ((MulAut.conj g).mapSubgroup) H).mpr (mem_maximalSubgroups.mp hH)
  have hMne : M ≠ Hg := by
    intro heq
    exact hnc ⟨g⁻¹, by rw [heq, hHg, map_inv]; exact inv_smul_smul _ _⟩
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1
  refine ⟨?_, ?_⟩
  · -- `p ∉ α(M)`: otherwise `r(S) ≥ 3` makes `S` uniquely maximal, forcing `M = H^g`.
    rw [mem_alpha_iff]
    rintro ⟨-, hr3⟩
    have hrank3 : 3 ≤ rank ↥(SM : Subgroup G) := by
      obtain ⟨SM', hSM'⟩ := sylow_subgroupOf_of_le SM hSM_le
      have e2 : pRank ↥(SM' : Subgroup ↥M) p ≤ pRank ↥(SM : Subgroup G) p := by
        rw [hSM']
        exact pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSM_le).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hSM_le).injective
      calc (3 : ℕ) ≤ pRank ↥M p := hr3
        _ = pRank ↥(SM' : Subgroup ↥M) p := (pRank_sylow_eq SM').symm
        _ ≤ pRank ↥(SM : Subgroup G) p := e2
        _ ≤ rank ↥(SM : Subgroup G) := pRank_le_rank p
    have hSlt : (SM : Subgroup G) < ⊤ := lt_of_le_of_lt hSM_le hMlt
    have hSU : IsUniquelyMaximal (SM : Subgroup G) :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hSlt hrank3
    exact hMne (hSU.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hM) hSM_le hHg_max hS_le_Hg)
  · -- `M_σ` not nilpotent: otherwise `S` (Sylow of `M_σ`) is characteristic, so `M ≤ N_G(S) ⊆ H^g`.
    intro hnil
    have hM_norm_Mσ : M ≤ Subgroup.normalizer ((Msigma M) : Set G) := by
      rw [Msigma, OddOrder.GroupTheory.opiCoreInG]
      have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (sigma M) ↥M) M.subtype
      rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
    have hSM_pi : Ch03.Subgroup.IsPiGroup (sigma M) (SM : Subgroup G) := by
      intro q hq
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp SM.isPGroup'
      have hq_prime := (Nat.mem_primeFactors.mp hq).1
      have hqdvd : q ∣ p ^ k := hk ▸ (Nat.mem_primeFactors.mp hq).2.1
      have hqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq_prime (Fact.out : p.Prime)).mp
          (hq_prime.dvd_of_dvd_pow hqdvd)
      rw [hqp]; exact hpM
    have hS_le_Msigma : (SM : Subgroup G) ≤ Msigma M :=
      sigma_subgroup_le_Msigma_of_isHall (Msigma_isHall hG hM) hSM_le hSM_pi
    obtain ⟨SMσ, hSMσ⟩ := sylow_subgroupOf_of_le SM hS_le_Msigma
    haveI := hnil
    haveI hSMσ_normal : (SMσ : Subgroup ↥(Msigma M)).Normal := Ch01.Sylow.normal_of_isNilpotent SMσ
    haveI hSMσ_char : (SMσ : Subgroup ↥(Msigma M)).Characteristic :=
      Sylow.characteristic_of_normal SMσ hSMσ_normal
    have hSM_eq_map : (SMσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype = (SM : Subgroup G) := by
      rw [hSMσ, Subgroup.map_subgroupOf_eq_of_le hS_le_Msigma]
    have hM_le_NS : M ≤ Subgroup.normalizer ((SM : Subgroup G) : Set G) := by
      calc M ≤ Subgroup.normalizer ((Msigma M) : Set G) := hM_norm_Mσ
        _ ≤ Subgroup.normalizer
              (((SMσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) : Set G) :=
            OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
        _ = Subgroup.normalizer ((SM : Subgroup G) : Set G) := by rw [hSM_eq_map]
    have hMHg : M ≤ Hg := le_trans hM_le_NS hSnorm_Hg
    rcases eq_or_lt_of_le hMHg with heq | hlt
    · exact hMne heq
    · exact (mem_maximalSubgroups.mp hHg_max).1 ((mem_maximalSubgroups.mp hM).2 Hg hlt)

/-! ## Lemma 10.12 — 非共役 maximal の σ-disjointness (mmd L2885) -/

/-- **BG Lemma 10.12** (mmd L2885): `M, H ∈ ℳ` が `G` で非共役なら、
(a) `M_α ⊓ H_σ = 1` かつ `α(M) ∩ σ(H) = ∅`; (b) `M_σ` が nilpotent なら `M_σ ⊓ H_σ = 1` かつ
`σ(M) ∩ σ(H) = ∅`。 -/
theorem disjoint_of_not_conj [Finite G] (hG : IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    (Malpha M ⊓ Msigma H = ⊥ ∧ alpha M ∩ sigma H = ∅) ∧
    (Group.IsNilpotent ↥(Msigma M) →
      Msigma M ⊓ Msigma H = ⊥ ∧ sigma M ∩ sigma H = ∅) := by
  classical
  -- (a) prime-set disjointness from the core lemma.
  have hα_disj : alpha M ∩ sigma H = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hpα, hpσH⟩
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpα.1⟩
    exact (mem_sigma_inter_sigma_imp hG hM hH hnc (alpha_subset_sigma hG hM hpα) hpσH).1 hpα
  refine ⟨⟨?_, hα_disj⟩, ?_⟩
  · -- `M_α ⊓ H_σ = ⊥`: `π(M_α ⊓ H_σ) ⊆ α(M) ∩ σ(H) = ∅`.
    refine inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (π := alpha M)
      (fun q hq => Malpha_isPiGroup M q hq) (fun q hq hqα => ?_)
    have hmem : q ∈ alpha M ∩ sigma H := ⟨hqα, Msigma_isPiGroup H q hq⟩
    rw [hα_disj] at hmem
    exact absurd hmem (Set.notMem_empty q)
  · -- (b) under `M_σ` nilpotent.
    intro hMσnil
    have hσ_disj : sigma M ∩ sigma H = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro p ⟨hpσM, hpσH⟩
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpσM.1⟩
      exact (mem_sigma_inter_sigma_imp hG hM hH hnc hpσM hpσH).2 hMσnil
    refine ⟨?_, hσ_disj⟩
    refine inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (π := sigma M)
      (fun q hq => Msigma_isPiGroup M q hq) (fun q hq hqσM => ?_)
    have hmem : q ∈ sigma M ∩ sigma H := ⟨hqσM, Msigma_isPiGroup H q hq⟩
    rw [hσ_disj] at hmem
    exact absurd hmem (Set.notMem_empty q)

/-! ## Helpers for Lemma 10.13 — maximal elementary abelian centralizer traps -/

/-- Mutual commutation puts a subgroup inside the normalizer: if every element of `H`
commutes with every element of `K`, then `H ≤ N_G(K)`. -/
private theorem le_normalizer_of_forall_comm {H K : Subgroup G}
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have : h * k * h⁻¹ = k := by rw [hHK h hh k hk]; group
    rwa [this]
  · intro hk
    have hc := hHK h hh _ hk
    have : k = h * k * h⁻¹ := by
      calc k = h⁻¹ * (h * k * h⁻¹) * h := by group
        _ = h⁻¹ * (h * (h * k * h⁻¹)) := by rw [hc]; group
        _ = h * k * h⁻¹ := by group
    rwa [← this] at hk

/-- Elementwise commutativity of the join of two elementwise-commutative subgroups that
centralize each other (stated on ambient elements to avoid subtype plumbing). -/
private theorem comm_sup_of_comm_of_comm {H K : Subgroup G}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  have hmul : ∀ g ∈ H ⊔ K, ∃ h ∈ H, ∃ k ∈ K, h * k = g := by
    intro g hg
    refine Set.mem_mul.mp ?_
    rw [(Subgroup.coe_mul_of_left_le_normalizer_right H K
      (le_normalizer_of_forall_comm hHK)).symm]
    exact hg
  intro x hx y hy
  obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hmul x hx
  obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hmul y hy
  calc h₁ * k₁ * (h₂ * k₂) = h₁ * h₂ * (k₁ * k₂) := by
        rw [mul_assoc, mul_assoc, ← mul_assoc k₁, ← hHK h₂ hh₂ k₁ hk₁, mul_assoc]
    _ = h₂ * h₁ * (k₂ * k₁) := by rw [hH h₁ hh₁ h₂ hh₂, hK k₁ hk₁ k₂ hk₂]
    _ = h₂ * k₂ * (h₁ * k₁) := by
        rw [mul_assoc, mul_assoc, ← mul_assoc h₁, hHK h₁ hh₁ k₂ hk₂, mul_assoc]

/-- Every elementary abelian `p`-subgroup of `C_G(A)` lies in the *maximal* elementary
abelian `A`: the join `A ⊔ E` is elementary abelian and contains `A`. This is the engine
behind BG's display (10.4) (`A = Ω₁(C_S(A))`, `r(C_S(A)) = 2`) in Lemma 10.13. -/
private theorem elemAbelian_le_of_le_centralizer [Finite G] {p : ℕ}
    {A : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) {E : Subgroup G}
    (hEea : E.IsElementaryAbelian p) (hEC : E ≤ Subgroup.centralizer (A : Set G)) :
    E ≤ A := by
  have hA_le_CE : A ≤ Subgroup.centralizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) a ha).symm
  have hsup : (A ⊔ E).IsElementaryAbelian p := hAea.sup_of_le_centralizer hEea hA_le_CE
  have heq : A ⊔ E = A := hAmax.2 (A ⊔ E) hsup le_sup_left
  exact le_sup_right.trans heq.le

/-- An element of `C_G(A)` of order dividing `p` lies in the maximal elementary abelian `A`
(BG (10.4): `A = Ω₁(C_S(A))`, elementwise form). -/
private theorem mem_of_mem_centralizer_of_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) (hgp : g ^ p = 1) : g ∈ A := by
  rcases eq_or_ne g 1 with rfl | hg1
  · exact A.one_mem
  · exact elemAbelian_le_of_le_centralizer hAea hAmax
      (Subgroup.IsElementaryAbelian.of_card_prime
        (by rw [Nat.card_zpowers, orderOf_eq_prime hgp hg1]))
      (Subgroup.zpowers_le.mpr hg) (Subgroup.mem_zpowers g)

/-- `Ω₁(Z(P)) ≤ A` for a maximal elementary abelian `A ≤ P`: elements of `Ω₁(Z(P))`
centralize `A` and have order dividing `p`. -/
private theorem omega1CenterInG_le_of_maximal [Finite G] {p : ℕ} [Fact p.Prime]
    {A P : Subgroup G} (hAea : A.IsElementaryAbelian p)
    (hAmax : IsMaximalElementaryAbelian p A) (hAP : A ≤ P) :
    omega1CenterInG P p ≤ A := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨hzc, hzp⟩ := mem_omega1OfAbelian.mp hz'
  refine mem_of_mem_centralizer_of_pow_eq_one hAea hAmax ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨a, hAP ha⟩)
  · calc (P.subtype z') ^ p = P.subtype (z' ^ p) := by rw [map_pow]
      _ = 1 := by rw [hzp, map_one]

/-- Two distinct subgroups of prime order intersect trivially. -/
private theorem inf_eq_bot_of_card_prime_of_ne [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G}
    (hX : Nat.card ↥X = p) (hY : Nat.card ↥Y = p) (hne : X ≠ Y) : X ⊓ Y = ⊥ := by
  by_contra hbot
  obtain ⟨g, hg, hg1⟩ := (Subgroup.bot_or_exists_ne_one (X ⊓ Y)).resolve_left hbot
  have hzleX : Subgroup.zpowers g ≤ X := Subgroup.zpowers_le.mpr hg.1
  have hzleY : Subgroup.zpowers g ≤ Y := Subgroup.zpowers_le.mpr hg.2
  have hcard : Nat.card ↥(Subgroup.zpowers g) = p := by
    have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ p := by
      rw [← hX]; exact Subgroup.card_dvd_of_le hzleX
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h
    · exact absurd (Subgroup.card_eq_one.mp h1)
        (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h))
    · exact h
  exact hne ((Subgroup.eq_of_le_of_card_ge hzleX (by rw [hX, hcard])).symm.trans
    (Subgroup.eq_of_le_of_card_ge hzleY (by rw [hY, hcard])))

/-- A subgroup of order `p²` is the join of any two of its distinct order-`p` subgroups. -/
private theorem eq_sup_of_card_prime_of_ne [Finite G] {p : ℕ} [Fact p.Prime]
    {A X Y : Subgroup G} (hAcard : Nat.card ↥A = p ^ 2) (hXA : X ≤ A) (hYA : Y ≤ A)
    (hX : Nat.card ↥X = p) (hY : Nat.card ↥Y = p) (hne : X ≠ Y) : X ⊔ Y = A := by
  have hsupA : X ⊔ Y ≤ A := sup_le hXA hYA
  have hdvd1 : p ∣ Nat.card ↥(X ⊔ Y) := by
    rw [← hX]; exact Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(X ⊔ Y) ∣ p ^ 2 := by
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hsupA
  obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
  interval_cases k
  · rw [hkeq, pow_zero] at hdvd1
    exact absurd (Nat.dvd_one.mp hdvd1) (Fact.out : p.Prime).ne_one
  · exfalso
    have hXeq : X = X ⊔ Y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hX, hkeq, pow_one])
    have hYX : Y ≤ X := hXeq ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hYX (by rw [hX, hY])).symm
  · exact Subgroup.eq_of_le_of_card_ge hsupA (by rw [hAcard, hkeq])

/-- **(10.6) producer, low-rank case** (`r(S) ≤ 2`): Corollary 10.7(b) makes the Sylow `S` a
central product `P₁ ∘ P₂` (`P₁` extraspecial of order `p³` and exponent `p`, `P₂` cyclic with
`Ω₁(P₂) = Z(P₁)`); exponent-`p` elements of `S` are trapped in `P₁`, so `A ≤ P₁` is
self-centralizing in `P₁` and `C_S(A) = A ⊔ P₂ = A₀ ⊔ P₂` is abelian, with
`Z₀ = Ω₁(Z(P)) = Z(P₁) = Ω₁(P₂) ≤ P₂` of order `p`. -/
private theorem centralizer_sylow_decomp_of_rank_le_two [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A P A₀ : Subgroup G} (S : Sylow p G)
    (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P) (hPS : P ≤ (S : Subgroup G))
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = p) (hA₀ne : A₀ ≠ omega1CenterInG P p)
    (hrank : rank ↥(S : Subgroup G) ≤ 2) :
    ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
      A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
      (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
        ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
      Nat.card ↥(omega1CenterInG P p) = p := by
  classical
  have hA_le_S : A ≤ (S : Subgroup G) := hAP.trans hPS
  -- Corollary 10.7(b).
  rcases (sylow_structure hG S).2.1 hrank with hab |
    ⟨P₁, P₂, hP₁S, hP₂S, hP₁ex, hP₁card, hP₂cyc, hΩeq, hCP⟩
  · -- `S` abelian would make `P` abelian.
    refine absurd ⟨⟨fun a b => Subtype.ext ?_⟩⟩ hPnonab
    have h := congrArg Subtype.val
      (hab.is_comm.comm (⟨(a : G), hPS a.2⟩ : ↥(S : Subgroup G)) ⟨(b : G), hPS b.2⟩)
    simpa using h
  -- The two central factors commute elementwise.
  have hP₁P₂comm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := by
    intro x hx y hy
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCP.commutator_eq_bot hx
    exact (Subgroup.mem_centralizer_iff.mp h y hy).symm
  have hdecomp : ∀ s ∈ (S : Subgroup G), ∃ s₁ ∈ P₁, ∃ s₂ ∈ P₂, s₁ * s₂ = s := by
    intro s hs
    refine Set.mem_mul.mp ?_
    rw [(Subgroup.coe_mul_of_left_le_normalizer_right P₁ P₂
      (le_normalizer_of_forall_comm hP₁P₂comm)).symm, ← hCP.sup_eq]
    exact hs
  -- Exponent-`p` elements of `S` lie in `P₁` (`Ω₁(S) ≤ P₁`).
  have htrap : ∀ s ∈ (S : Subgroup G), s ^ p = 1 → s ∈ P₁ := by
    intro s hs hsp
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hdecomp s hs
    have hcomm : Commute s₁ s₂ := hP₁P₂comm s₁ hs₁ s₂ hs₂
    have hs₁p : s₁ ^ p = 1 := congrArg Subtype.val (hP₁ex.pow_eq_one (⟨s₁, hs₁⟩ : ↥P₁))
    have hs₂p : s₂ ^ p = 1 := by
      have h := hsp
      rw [hcomm.mul_pow, hs₁p, one_mul] at h
      exact h
    have hs₂P₁ : s₂ ∈ P₁ := by
      have hmem : s₂ ∈ (Omega ↥P₂ p 1).map P₂.subtype :=
        ⟨⟨s₂, hs₂⟩, Omega.mem_of_pow_eq_one (by
          rw [pow_one]
          exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hs₂p)), rfl⟩
      rw [hΩeq] at hmem
      exact Subgroup.map_subtype_le _ hmem
    exact P₁.mul_mem hs₁ hs₂P₁
  -- `A ≤ P₁`.
  have hA_le_P₁ : A ≤ P₁ := fun a ha => htrap a (hA_le_S ha)
    (congrArg Subtype.val (hAea.2 ⟨a, ha⟩))
  -- `C_{P₁}(A) = A` (the rank-two `A` is self-centralizing in the extraspecial `P₁`).
  have hCP₁A : Subgroup.centralizer (A : Set G) ⊓ P₁ = A := by
    have hA_le : A ≤ Subgroup.centralizer (A : Set G) ⊓ P₁ := by
      refine le_inf ?_ hA_le_P₁
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hAea.1 ⟨b, hb⟩ ⟨a, ha⟩)
    have hdvd : Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓ P₁) ∣ p ^ 3 := by
      rw [← hP₁card]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    have hp2le : p ^ 2 ≤ p ^ k := by
      rw [← hkeq, ← hAcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA_le)
    have hk2 : 2 ≤ k :=
      le_of_not_gt fun hlt =>
        absurd hp2le (not_le.mpr (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hlt))
    interval_cases k
    · exact (Subgroup.eq_of_le_of_card_ge hA_le (by rw [hAcard, hkeq])).symm
    · -- `|C_{P₁}(A)| = p³` would make `A` central in `P₁`, impossible (`|Z(P₁)| = p`).
      exfalso
      have hCeq : Subgroup.centralizer (A : Set G) ⊓ P₁ = P₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hP₁card, hkeq])
      have hAcent : A.subgroupOf P₁ ≤ Subgroup.center ↥P₁ := by
        intro a ha
        rw [Subgroup.mem_center_iff]
        intro x
        have hx : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
          have hx' : (x : G) ∈ Subgroup.centralizer (A : Set G) ⊓ P₁ := by
            rw [hCeq]; exact x.2
          exact hx'.1
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        exact (Subgroup.mem_centralizer_iff.mp hx (a : G)
          (Subgroup.mem_subgroupOf.mp ha)).symm
      have hcard_le : p ^ 2 ∣ p := by
        rw [← hAcard, ← hP₁ex.isExtraspecial.center_card]
        calc Nat.card ↥A = Nat.card ↥(A.subgroupOf P₁) :=
              (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_P₁).toEquiv).symm
          _ ∣ Nat.card ↥(Subgroup.center ↥P₁) := Subgroup.card_dvd_of_le hAcent
      have hp2 : p < p ^ 2 := by
        have h1 := (Fact.out : p.Prime).one_lt
        nlinarith
      exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hcard_le) (not_le.mpr hp2)
  -- `C_S(A) = A ⊔ P₂`.
  have hCSA : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A ⊔ P₂ := by
    apply le_antisymm
    · intro c hc
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hdecomp c hc.2
      have hc₂C : c₂ ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hP₁P₂comm a (hA_le_P₁ ha) c₂ hc₂
      have hc₁C : c₁ ∈ Subgroup.centralizer (A : Set G) := by
        have heq : c₁ = c₁ * c₂ * c₂⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ hc.1 (Subgroup.inv_mem _ hc₂C)
      have hc₁A : c₁ ∈ A := by
        have hmem : c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ P₁ := ⟨hc₁C, hc₁⟩
        rwa [hCP₁A] at hmem
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₁A) (Subgroup.mem_sup_right hc₂)
    · refine sup_le (le_inf ?_ hA_le_S) (le_inf ?_ hP₂S)
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact congrArg Subtype.val (hAea.1 ⟨b, hb⟩ ⟨a, ha⟩)
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hP₁P₂comm a (hA_le_P₁ ha) y hy
  -- `C_S(A)` is abelian.
  have hCab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁ := by
    rw [hCSA]
    refine comm_sup_of_comm_of_comm
      (fun x hx y hy => congrArg Subtype.val (hAea.1 ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx y hy => ?_)
      (fun x hx y hy => hP₁P₂comm x (hA_le_P₁ hx) y hy)
    haveI := hP₂cyc
    letI : CommGroup ↥P₂ := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥P₂) ⟨y, hy⟩)
  -- `Z₀ = Ω₁(Z(P))`: contained in `A`, nontrivial, proper in `A`, of order `p`.
  haveI hPnt : Nontrivial ↥P := by
    rcases subsingleton_or_nontrivial ↥P with hs | hn
    · exact absurd ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩ hPnonab
    · exact hn
  obtain ⟨z, -, hzc, hz1, hzp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPp (N := ⊤) top_ne_bot
  have hzZ₀ : (z : G) ∈ omega1CenterInG P p :=
    Subgroup.mem_map.mpr ⟨z, mem_omega1OfAbelian.mpr ⟨hzc, hzp⟩, rfl⟩
  have hZ₀A : omega1CenterInG P p ≤ A := omega1CenterInG_le_of_maximal hAea hAmax hAP
  have hAne : A ≠ omega1CenterInG P p := by
    intro heq
    apply hPnonab
    have hPC : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [heq] at ha
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp ha
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
        (mem_omega1OfAbelian.mp hz').1 ⟨x, hx⟩)).symm
    exact ⟨⟨fun a b => Subtype.ext
      (hCab _ ⟨hPC a.2, hPS a.2⟩ _ ⟨hPC b.2, hPS b.2⟩)⟩⟩
  have hZ₀card : Nat.card ↥(omega1CenterInG P p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG P p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₀A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      haveI hsub : Subsingleton ↥(omega1CenterInG P p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim (⟨(z : G), hzZ₀⟩ : ↥(omega1CenterInG P p))
        ⟨1, Subgroup.one_mem _⟩
      exact hz1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₀A (by rw [hAcard, hkeq])).symm hAne
  -- `Z(P₁)` (mapped to `G`) is contained in `A`, then in `Z₀`; equality by cardinality.
  have hZP₁card : Nat.card ↥((Subgroup.center ↥P₁).map P₁.subtype) = p := by
    rw [Subgroup.card_map_of_injective P₁.subtype_injective]
    exact hP₁ex.isExtraspecial.center_card
  have hZP₁pow : ∀ w ∈ (Subgroup.center ↥P₁).map P₁.subtype, w ^ p = 1 := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ↥((Subgroup.center ↥P₁).map P₁.subtype)) ^ p = 1 := by
      rw [← hZP₁card]
      exact pow_card_eq_one'
    have hcoe := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hcoe
  have hZP₁_le_A : (Subgroup.center ↥P₁).map P₁.subtype ≤ A := by
    intro w hw
    refine mem_of_mem_centralizer_of_pow_eq_one hAea hAmax ?_ (hZP₁pow w hw)
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw' ⟨a, hA_le_P₁ ha⟩)
  have hZP₁_le_Z₀ : (Subgroup.center ↥P₁).map P₁.subtype ≤ omega1CenterInG P p := by
    intro w hw
    have hwA : w ∈ A := hZP₁_le_A hw
    have hwS : ∀ s ∈ (S : Subgroup G), s * w = w * s := by
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
      intro s hs
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hdecomp s hs
      have h₁ : s₁ * P₁.subtype w' = P₁.subtype w' * s₁ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hw' ⟨s₁, hs₁⟩)
      have h₂ : s₂ * P₁.subtype w' = P₁.subtype w' * s₂ :=
        (hP₁P₂comm (P₁.subtype w') (Subgroup.map_subtype_le _ ⟨w', hw', rfl⟩) s₂ hs₂).symm
      calc s₁ * s₂ * P₁.subtype w' = s₁ * (P₁.subtype w' * s₂) := by rw [mul_assoc, h₂]
        _ = P₁.subtype w' * (s₁ * s₂) := by rw [← mul_assoc, h₁, mul_assoc]
    refine Subgroup.mem_map.mpr ⟨⟨w, hAP hwA⟩, mem_omega1OfAbelian.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hwS (g : G) (hPS g.2))
    · exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hZP₁pow w hw)
  have hZ₀eq : omega1CenterInG P p = (Subgroup.center ↥P₁).map P₁.subtype :=
    (Subgroup.eq_of_le_of_card_ge hZP₁_le_Z₀ (by rw [hZ₀card, hZP₁card])).symm
  have hZ₀_le_P₂ : omega1CenterInG P p ≤ P₂ := by
    rw [hZ₀eq, ← hΩeq]
    exact Subgroup.map_subtype_le _
  -- Assemble with `Y = P₂`.
  refine ⟨P₂, hP₂S, hP₂cyc, hZ₀_le_P₂, ?_, ?_, hCab, hZ₀card⟩
  · -- `A₀ ⊓ P₂ = ⊥`: an exponent-`p` element of `P₂` lies in `Ω₁(P₂) = Z₀ ≠ A₀`.
    rw [eq_bot_iff]
    intro x hx
    have hxp : x ^ p = 1 := by
      have h1 : (⟨x, hx.1⟩ : ↥A₀) ^ p = 1 := by
        rw [← hA₀card]
        exact pow_card_eq_one'
      have hcoe := congrArg Subtype.val h1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hcoe
    have hxZ₀ : x ∈ omega1CenterInG P p := by
      rw [hZ₀eq, ← hΩeq]
      exact ⟨⟨x, hx.2⟩, Omega.mem_of_pow_eq_one (by
        rw [pow_one]
        exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxp)), rfl⟩
    have hmem : x ∈ A₀ ⊓ omega1CenterInG P p := ⟨hx.1, hxZ₀⟩
    rwa [inf_eq_bot_of_card_prime_of_ne hA₀card hZ₀card hA₀ne] at hmem
  · -- `C_S(A) = A₀ ⊔ P₂` via `A = A₀ ⊔ Z₀` and `Z₀ ≤ P₂`.
    rw [hCSA, ← eq_sup_of_card_prime_of_ne hAcard hA₀A hZ₀A hA₀card hZ₀card hA₀ne,
      sup_assoc, sup_eq_right.mpr hZ₀_le_P₂]

/-- Bridge: the `↥S`-level centralizer of `L.subgroupOf S` is the `subgroupOf`-image of the
ambient `C_G(L) ⊓ S`. -/
private theorem centralizer_subgroupOf_inf_eq {S L : Subgroup G} (hLS : L ≤ S) :
    Subgroup.centralizer ((L.subgroupOf S : Subgroup ↥S) : Set ↥S)
      = (Subgroup.centralizer (L : Set G) ⊓ S).subgroupOf S := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    refine ⟨fun h hh => ?_, m.2⟩
    simpa using congrArg Subtype.val (hc ⟨h, hLS hh⟩ (Subgroup.mem_subgroupOf.mpr hh))
  · intro hc h hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hc.1 (h : G) (Subgroup.mem_subgroupOf.mp hh)

/-- **(10.6) producer, high-rank case** (`r_p(S) ≥ 3`): `S` is narrow with maximal elementary
abelian witness `A` (BG (10.4)), and BG Theorem 5.3(d) (`narrow_centralizer_decomp`) splits
`C_S(L) = L × C_T(L)` for each order-`p` line `L ≤ A` other than `Z₁ = Ω₁(Z(S))`; since
`C_S(L) = C_S(A)` (as `A = L ⊔ Z₁` with `Z₁` central in `S`) this gives the abelian
decomposition `C_S(A) = A₀ ⊔ Y`, and `Z₀ = Ω₁(Z(P)) = Z₁` has order `p`. -/
private theorem centralizer_sylow_decomp_of_three_le_rank [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A P A₀ : Subgroup G} (S : Sylow p G)
    (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P) (hPS : P ≤ (S : Subgroup G))
    (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = p) (hA₀ne : A₀ ≠ omega1CenterInG P p)
    (h3 : 3 ≤ pRank ↥(S : Subgroup G) p) :
    ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
      A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
      (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
        ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
      Nat.card ↥(omega1CenterInG P p) = p := by
  classical
  have hA_le_S : A ≤ (S : Subgroup G) := hAP.trans hPS
  have hp_odd : Odd p := hG.odd.of_dvd_nat
    ((show p ∣ Nat.card ↥A by rw [hAcard]; exact dvd_pow_self p two_ne_zero).trans
      (Subgroup.card_subgroup_dvd_card A))
  have hApow : ∀ g ∈ A, g ^ p = 1 := by
    intro g hg
    have h := congrArg Subtype.val (hAea.2 ⟨g, hg⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  -- `↥S`-level data for `A`: maximality is inherited.
  have hA'card : Nat.card ↥(A.subgroupOf (S : Subgroup G)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_S).toEquiv]
    exact hAcard
  have hA'ea : (A.subgroupOf (S : Subgroup G)).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA_le_S).symm hAea
  have hA'max : IsMaximalElementaryAbelian p (A.subgroupOf (S : Subgroup G)) := by
    refine ⟨hA'ea, ?_⟩
    intro F hFea hAF
    have hFmap : F.map (S : Subgroup G).subtype = A :=
      hAmax.2 _ (hFea.map (S : Subgroup G).subtype_injective) (by
        rw [← Subgroup.map_subgroupOf_eq_of_le hA_le_S]
        exact Subgroup.map_mono hAF)
    calc F = (F.map (S : Subgroup G).subtype).subgroupOf (S : Subgroup G) := by
          rw [Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective]
      _ = A.subgroupOf (S : Subgroup G) := by rw [hFmap]
  have hnarrow : IsNarrow p ↥(S : Subgroup G) :=
    (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp_odd S.isPGroup' h3).mpr
      ⟨A.subgroupOf (S : Subgroup G), hA'card, hA'max⟩
  -- BG (10.4): `r(C_S(A)) ≤ 2`, first at the ambient level, then at the `↥S` level.
  have hrank2G : pRank ↥(Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)) p ≤ 2 := by
    rw [pRank_le_iff]
    intro E hEea
    have hEmap_le_A :
        E.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype ≤ A :=
      elemAbelian_le_of_le_centralizer hAea hAmax
        (hEea.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype_injective)
        ((Subgroup.map_subtype_le _).trans inf_le_left)
    have hlog : Nat.log p (Nat.card ↥E) ≤ Nat.log p (Nat.card ↥A) := by
      apply Nat.log_mono_right
      have hEcard : Nat.card
          ↥(E.map (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype)
          = Nat.card ↥E :=
        Subgroup.card_map_of_injective
          (Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)).subtype_injective
      rw [← hEcard]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hEmap_le_A)
    rwa [hAcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hlog
  have hrank2' : pRank ↥(Subgroup.centralizer
      ((A.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
        Set ↥(S : Subgroup G))) p ≤ 2 := by
    rw [centralizer_subgroupOf_inf_eq hA_le_S]
    exact le_trans
      (pRank_le_of_injective
        (f := (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)
            ≤ (S : Subgroup G))).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe _).injective)
      hrank2G
  -- `Z₁ = Ω₁(Z(S))`: contained in `A`, of order exactly `p`.
  have hZ₁A : omega1CenterInG (S : Subgroup G) p ≤ A :=
    omega1CenterInG_le_of_maximal hAea hAmax hA_le_S
  have hZ₁S_comm : ∀ z ∈ omega1CenterInG (S : Subgroup G) p,
      ∀ s ∈ (S : Subgroup G), z * s = s * z := by
    intro z hz s hs
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (mem_omega1OfAbelian.mp hz').1 ⟨s, hs⟩)).symm
  haveI hSnt : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
      _ = Nat.card ↥A := hAcard.symm
      _ ≤ Nat.card ↥(S : Subgroup G) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA_le_S)
  obtain ⟨zS, -, hzSc, hzS1, hzSp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot S.isPGroup' (N := ⊤) top_ne_bot
  have hzSZ₁ : (zS : G) ∈ omega1CenterInG (S : Subgroup G) p :=
    Subgroup.mem_map.mpr ⟨zS, mem_omega1OfAbelian.mpr ⟨hzSc, hzSp⟩, rfl⟩
  have hZ₁ne_A : omega1CenterInG (S : Subgroup G) p ≠ A := by
    intro heq
    have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← heq] at ha
      exact hZ₁S_comm a ha s hs
    have hCS : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = (S : Subgroup G) :=
      inf_eq_right.mpr hSC
    rw [hCS] at hrank2G
    omega
  have hZ₁card : Nat.card ↥(omega1CenterInG (S : Subgroup G) p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG (S : Subgroup G) p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₁A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      haveI hsub : Subsingleton ↥(omega1CenterInG (S : Subgroup G) p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim
        (⟨(zS : G), hzSZ₁⟩ : ↥(omega1CenterInG (S : Subgroup G) p)) ⟨1, Subgroup.one_mem _⟩
      exact hzS1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₁A (by rw [hAcard, hkeq])) hZ₁ne_A
  -- Sub-producer: the Theorem 5.3(d) decomposition for any line `L ≤ A` other than `Z₁`.
  have key : ∀ L : Subgroup G, L ≤ A → Nat.card ↥L = p →
      L ≠ omega1CenterInG (S : Subgroup G) p →
      ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧
        omega1CenterInG (S : Subgroup G) p ≤ Y ∧ L ⊓ Y = ⊥ ∧
        Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = L ⊔ Y ∧
        (∀ l ∈ L, ∀ y ∈ Y, l * y = y * l) := by
    intro L hLA hLcard hLne
    have hL_le_S : L ≤ (S : Subgroup G) := hLA.trans hA_le_S
    have hLZcomm : ∀ x ∈ L, ∀ y ∈ omega1CenterInG (S : Subgroup G) p, x * y = y * x :=
      fun x hx y hy => (hZ₁S_comm y hy x (hL_le_S hx)).symm
    -- `C_S(A) = C_S(L)` (`A = L ⊔ Z₁` with `Z₁` central).
    have hCLA : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)
        = Subgroup.centralizer (L : Set G) ⊓ (S : Subgroup G) := by
      apply le_antisymm
      · exact inf_le_inf_right _ (Subgroup.centralizer_le (fun x hx => hLA hx))
      · intro c hc
        refine Subgroup.mem_inf.mpr ⟨?_, hc.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have haLZ : a ∈ (↑L * ↑(omega1CenterInG (S : Subgroup G) p) : Set G) := by
          rw [(Subgroup.coe_mul_of_left_le_normalizer_right L _
            (le_normalizer_of_forall_comm hLZcomm)).symm,
            eq_sup_of_card_prime_of_ne hAcard hLA hZ₁A hLcard hZ₁card hLne]
          exact ha
        obtain ⟨l, hl, z, hz, rfl⟩ := Set.mem_mul.mp haLZ
        have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.1 l hl
        have hcz : z * c = c * z := hZ₁S_comm z hz c hc.2
        calc l * z * c = l * (c * z) := by rw [mul_assoc, hcz]
          _ = c * (l * z) := by rw [← mul_assoc, hcl, mul_assoc]
    -- the `↥S`-level inputs for Theorem 5.3(d)
    have hL'card : Nat.card ↥(L.subgroupOf (S : Subgroup G)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le_S).toEquiv]
      exact hLcard
    have hrankL : pRank ↥(Subgroup.centralizer
        ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G))) p ≤ 2 := by
      rw [centralizer_subgroupOf_inf_eq hL_le_S, ← hCLA,
        ← centralizer_subgroupOf_inf_eq hA_le_S]
      exact hrank2'
    obtain ⟨hYcyc, -, hLT, hCdecomp⟩ :=
      Ch1.S05.narrow_centralizer_decomp hp_odd S.isPGroup' h3 hnarrow
        (L.subgroupOf (S : Subgroup G)) hL'card hrankL
    refine ⟨(Subgroup.centralizer
        ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G)) ⊓
      Subgroup.centralizer
        ((omega1UpperCentralTwo ↥(S : Subgroup G) p : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G))).map (S : Subgroup G).subtype,
      Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
    · -- cyclic
      haveI := hYcyc
      exact isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective _ _ (S : Subgroup G).subtype_injective).surjective
    · -- `Z₁ ≤ Y`
      intro z hz
      have hzS : z ∈ (S : Subgroup G) := omega1CenterInG_le (S : Subgroup G) p hz
      refine Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (hZ₁S_comm z hz (h : G) h.2).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (hZ₁S_comm z hz (h : G) h.2).symm
    · -- `L ⊓ Y = ⊥`
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ (S : Subgroup G) := hL_le_S hx.1
      have hxY := hx.2
      obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.mp hxY
      have hy'x : y' = ⟨x, hxS⟩ := Subtype.ext hyeq
      rw [hy'x] at hy'
      have hbot : (⟨x, hxS⟩ : ↥(S : Subgroup G)) ∈
          (⊥ : Subgroup ↥(S : Subgroup G)) := by
        rw [← hLT]
        exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, hy'.2⟩
      rw [Subgroup.mem_bot] at hbot
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val hbot
    · -- `C_G(A) ⊓ S = L ⊔ Y`
      have hmapL : (Subgroup.centralizer
            ((L.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
              Set ↥(S : Subgroup G))).map (S : Subgroup G).subtype
          = Subgroup.centralizer (L : Set G) ⊓ (S : Subgroup G) := by
        rw [centralizer_subgroupOf_inf_eq hL_le_S,
          Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      have hmap := congrArg (Subgroup.map (S : Subgroup G).subtype) hCdecomp
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hL_le_S, hmapL] at hmap
      rw [hCLA, hmap]
    · -- elements of `Y` centralize `L`
      intro l hl y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp hy'.1
        (⟨l, hL_le_S hl⟩ : ↥(S : Subgroup G)) (Subgroup.mem_subgroupOf.mpr hl)
      have hcoe := congrArg Subtype.val hcomm
      simpa using hcoe
  -- `Z₀ = Ω₁(Z(P))`: order `p` and equal to `Z₁`.
  obtain ⟨L₀g, hL₀A, hL₀Z₁⟩ : ∃ a ∈ A, a ∉ omega1CenterInG (S : Subgroup G) p := by
    by_contra h
    push Not at h
    exact hZ₁ne_A (le_antisymm hZ₁A h)
  have hL₀ne1 : L₀g ≠ 1 := fun h => hL₀Z₁ (by rw [h]; exact Subgroup.one_mem _)
  have hL₀card : Nat.card ↥(Subgroup.zpowers L₀g) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hApow L₀g hL₀A) hL₀ne1
  have hL₀ne : Subgroup.zpowers L₀g ≠ omega1CenterInG (S : Subgroup G) p := by
    intro h
    exact hL₀Z₁ (h ▸ Subgroup.mem_zpowers L₀g)
  obtain ⟨Y₀, hY₀S, hY₀cyc, hY₀Z₁, hL₀Y₀, hC₀, hL₀Y₀comm⟩ :=
    key (Subgroup.zpowers L₀g) (Subgroup.zpowers_le.mpr hL₀A) hL₀card hL₀ne
  -- `C_S(A)` is abelian (from the generic-line decomposition).
  have hCab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁ := by
    rw [hC₀]
    refine comm_sup_of_comm_of_comm (fun x hx y hy => ?_) (fun x hx y hy => ?_) hL₀Y₀comm
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Commute.zpow_zpow_self L₀g i j
    · haveI := hY₀cyc
      letI : CommGroup ↥Y₀ := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥Y₀) ⟨y, hy⟩)
  -- (10.5): `A ≠ Z₀`, hence `|Z₀| = p` and `Z₀ = Z₁`.
  haveI hPnt : Nontrivial ↥P := by
    rcases subsingleton_or_nontrivial ↥P with hs | hn
    · exact absurd ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩ hPnonab
    · exact hn
  obtain ⟨zP, -, hzPc, hzP1, hzPp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPp (N := ⊤) top_ne_bot
  have hzPZ₀ : (zP : G) ∈ omega1CenterInG P p :=
    Subgroup.mem_map.mpr ⟨zP, mem_omega1OfAbelian.mpr ⟨hzPc, hzPp⟩, rfl⟩
  have hZ₀A : omega1CenterInG P p ≤ A := omega1CenterInG_le_of_maximal hAea hAmax hAP
  have hAne : A ≠ omega1CenterInG P p := by
    intro heq
    apply hPnonab
    have hPC : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [heq] at ha
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp ha
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
        (mem_omega1OfAbelian.mp hz').1 ⟨x, hx⟩)).symm
    exact ⟨⟨fun a b => Subtype.ext
      (hCab _ ⟨hPC a.2, hPS a.2⟩ _ ⟨hPC b.2, hPS b.2⟩)⟩⟩
  have hZ₀card : Nat.card ↥(omega1CenterInG P p) = p := by
    have hdvd : Nat.card ↥(omega1CenterInG P p) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hZ₀A
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases k
    · exfalso
      haveI hsub : Subsingleton ↥(omega1CenterInG P p) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hkeq, pow_zero])).1
      have h1 := Subsingleton.elim (⟨(zP : G), hzPZ₀⟩ : ↥(omega1CenterInG P p))
        ⟨1, Subgroup.one_mem _⟩
      exact hzP1 (OneMemClass.coe_eq_one.mp (congrArg Subtype.val h1))
    · rw [hkeq, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZ₀A (by rw [hAcard, hkeq])).symm hAne
  have hZ₁_le_Z₀ : omega1CenterInG (S : Subgroup G) p ≤ omega1CenterInG P p := by
    intro z hz
    have hzA : z ∈ A := hZ₁A hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hAP hzA⟩, mem_omega1OfAbelian.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hZ₁S_comm z hz (g : G) (hPS g.2)).symm
    · exact Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact pow_eq_one_of_mem_omega1CenterInG hz)
  have hZ₀Z₁ : omega1CenterInG P p = omega1CenterInG (S : Subgroup G) p :=
    (Subgroup.eq_of_le_of_card_ge hZ₁_le_Z₀ (by rw [hZ₁card, hZ₀card])).symm
  -- final assembly with `L = A₀`
  obtain ⟨Y, hYS, hYcyc, hYZ₁, hA₀Y, hCY, hA₀Ycomm⟩ :=
    key A₀ hA₀A hA₀card (by rw [← hZ₀Z₁]; exact hA₀ne)
  refine ⟨Y, hYS, hYcyc, by rw [hZ₀Z₁]; exact hYZ₁, hA₀Y, hCY, ?_, hZ₀card⟩
  rw [hCY]
  refine comm_sup_of_comm_of_comm (fun x hx y hy => ?_) (fun x hx y hy => ?_) hA₀Ycomm
  · exact congrArg Subtype.val (hAea.1 ⟨x, hA₀A hx⟩ ⟨y, hA₀A hy⟩)
  · haveI := hYcyc
    letI : CommGroup ↥Y := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥Y) ⟨y, hy⟩)

/-- Generator of a subgroup of prime order. -/
private theorem exists_zpowers_eq_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hX : Nat.card ↥X = p) :
    ∃ a : G, a ∈ X ∧ orderOf a = p ∧ Subgroup.zpowers a = X := by
  have h1 : 1 < Nat.card ↥X := by rw [hX]; exact (Fact.out : p.Prime).one_lt
  haveI : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥X)
  have hane : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord_dvd : orderOf (a : G) ∣ p := by
    rw [← hX]
    exact Subgroup.orderOf_dvd_natCard X a.2
  have hord : orderOf (a : G) = p :=
    ((Nat.dvd_prime Fact.out).mp hord_dvd).resolve_left
      (fun h => hane (orderOf_eq_one_iff.mp h))
  refine ⟨a, a.2, hord, ?_⟩
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2)
    (by rw [hX, Nat.card_zpowers, hord])

/-- **GL₂(p)-transvection transitivity, multiplicative form** (core of Lemma 10.13(c)):
if the `p`-element `x` normalizes the rank-two elementary abelian `A` and centralizes the
order-`p` subgroup `Z₀ ≤ A` but not all of `A`, then the powers of `x` conjugate any order-`p`
subgroup `X ≤ A` other than `Z₀` onto any other such `Y`.

In coordinates `A = ⟨a⟩ × ⟨z₀⟩` (`a` a generator of `X`): conjugation by `x` fixes `z₀` and
sends `a ↦ a^{i₀} z₀^{j₀}`; iterating to `x^{orderOf x} = 1` forces `i₀ ≡ 1 (mod p)` (Fermat),
and `j₀ ≢ 0` since `x ∉ C_G(A)`, so `x^k a x^{-k} = a z₀^{k j₀}` sweeps through all lines
`⟨a^m z₀^s⟩ ≠ ⟨z₀⟩` as `k` runs (solve `k j₀ m ≡ s (mod p)` in the field `ZMod p`). -/
private theorem exists_conj_pow_eq_of_fixes_line [Finite G] {p : ℕ} [Fact p.Prime]
    {A Z₀ : Subgroup G} (hAea : A.IsElementaryAbelian p) (hAcard : Nat.card ↥A = p ^ 2)
    {x : G} (hxN : x ∈ Subgroup.normalizer (A : Set G)) {e : ℕ} (hxord : orderOf x = p ^ e)
    (hZ₀A : Z₀ ≤ A) (hZ₀card : Nat.card ↥Z₀ = p)
    (hxZ₀ : ∀ z ∈ Z₀, x * z = z * x)
    (hxnC : ¬ ∀ a ∈ A, x * a = a * x)
    {X Y : Subgroup G} (hXA : X ≤ A) (hXcard : Nat.card ↥X = p) (hXne : X ≠ Z₀)
    (hYA : Y ≤ A) (hYcard : Nat.card ↥Y = p) (hYne : Y ≠ Z₀) :
    ∃ k : ℕ, MulAut.conj (x ^ k) • X = Y := by
  classical
  obtain ⟨a, haX, haord, haz⟩ := exists_zpowers_eq_of_card_prime hXcard
  obtain ⟨z₀, hz₀Z, hz₀ord, hz₀z⟩ := exists_zpowers_eq_of_card_prime hZ₀card
  obtain ⟨b, hbY, hbord, hbz⟩ := exists_zpowers_eq_of_card_prime hYcard
  have haA : a ∈ A := hXA haX
  have hz₀A : z₀ ∈ A := hZ₀A hz₀Z
  have hbA : b ∈ A := hYA hbY
  have hAcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAea.1 ⟨g, hg⟩ ⟨h, hh⟩)
  have hcomm_az : Commute a z₀ := hAcomm a haA z₀ hz₀A
  -- coordinates along `A = X ⊔ Z₀`
  have hXZsup : X ⊔ Z₀ = A :=
    eq_sup_of_card_prime_of_ne hAcard hXA hZ₀A hXcard hZ₀card hXne
  have hcoord : ∀ g ∈ A, ∃ i j : ℤ, g = a ^ i * z₀ ^ j := by
    intro g hg
    have hmem : g ∈ (↑X * ↑Z₀ : Set G) := by
      rw [(Subgroup.coe_mul_of_left_le_normalizer_right X Z₀
        (le_normalizer_of_forall_comm (fun u hu v hv =>
          hAcomm u (hXA hu) v (hZ₀A hv)))).symm, hXZsup]
      exact hg
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem
    rw [← haz] at hu
    rw [← hz₀z] at hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ⟨i, j, rfl⟩
  -- coordinate separation: `a^i z₀^j = 1` forces `p ∣ i` and `p ∣ j`
  have hsep : ∀ i j : ℤ, a ^ i * z₀ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j hij
    have hzj_eq : a ^ i = (z₀ ^ j)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hij
    have hai : a ^ i ∈ X ⊓ Z₀ := by
      constructor
      · rw [← haz]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i
      · rw [hzj_eq, ← hz₀z]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) j)
    rw [inf_eq_bot_of_card_prime_of_ne hXcard hZ₀card hXne, Subgroup.mem_bot] at hai
    have hzj : z₀ ^ j = 1 := by
      have h := hij
      rw [hai, one_mul] at h
      exact h
    constructor
    · rw [← haord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hai
    · rw [← hz₀ord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hzj
  -- conjugation by `x` in coordinates
  have hxa_mem : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).mp haA
  obtain ⟨i₀, j₀, hxa⟩ := hcoord _ hxa_mem
  have hxz : ∀ j : ℤ, x * z₀ ^ j * x⁻¹ = z₀ ^ j := by
    intro j
    have hc : Commute x (z₀ ^ j) := (show Commute x z₀ from hxZ₀ z₀ hz₀Z).zpow_right j
    rw [hc.eq]
    group
  -- iterate to `x^{orderOf x} = 1`: the `X`-coordinate of `x^k a x^{-k}` is `i₀^k`
  have hiter : ∀ k : ℕ, ∃ jk : ℤ, x ^ k * a * (x ^ k)⁻¹ = a ^ (i₀ ^ k) * z₀ ^ jk := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨jn, hjn⟩ := ih
      refine ⟨j₀ * i₀ ^ n + jn, ?_⟩
      have h1 : x ^ (n + 1) * a * (x ^ (n + 1))⁻¹
          = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      have h2 : x * (a ^ i₀ ^ n * z₀ ^ jn) * x⁻¹
          = (x * a * x⁻¹) ^ (i₀ ^ n) * (x * z₀ ^ jn * x⁻¹) := by
        rw [conj_zpow]
        group
      have h3 : (a ^ i₀ * z₀ ^ j₀) ^ i₀ ^ n
          = a ^ (i₀ ^ (n + 1)) * z₀ ^ (j₀ * i₀ ^ n) := by
        rw [((hcomm_az.zpow_zpow i₀ j₀)).mul_zpow, ← zpow_mul, ← zpow_mul]
        congr 2
        rw [pow_succ]
        ring
      rw [h1, hjn, h2, hxz jn, hxa, h3, mul_assoc, ← zpow_add]
  obtain ⟨jN, hjN⟩ := hiter (orderOf x)
  rw [pow_orderOf_eq_one x] at hjN
  have hjN' : a = a ^ (i₀ ^ orderOf x) * z₀ ^ jN := by
    have h := hjN
    rw [one_mul, inv_one, mul_one] at h
    exact h
  -- Fermat: `i₀ ≡ 1 (mod p)`
  have hsep1 : (p : ℤ) ∣ (i₀ ^ orderOf x - 1) ∧ (p : ℤ) ∣ jN := by
    apply hsep
    have hswap : a⁻¹ * z₀ ^ jN = z₀ ^ jN * a⁻¹ := ((hcomm_az.zpow_right jN).inv_left).eq
    calc a ^ (i₀ ^ orderOf x - 1) * z₀ ^ jN
        = a ^ (i₀ ^ orderOf x) * a⁻¹ * z₀ ^ jN := by
          rw [zpow_sub, zpow_one]
      _ = a ^ (i₀ ^ orderOf x) * z₀ ^ jN * a⁻¹ := by
          rw [mul_assoc, hswap, mul_assoc]
      _ = a * a⁻¹ := by rw [← hjN']
      _ = 1 := mul_inv_cancel a
  have hi₀ : (p : ℤ) ∣ (i₀ - 1) := by
    have hcast : ((i₀ ^ orderOf x - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hsep1.1
    push_cast at hcast
    rw [sub_eq_zero, hxord] at hcast
    have hfermat : ∀ m : ℕ, ((i₀ : ZMod p)) ^ (p ^ m) = (i₀ : ZMod p) := by
      intro m
      induction m with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
    rw [hfermat e] at hcast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact hcast
  have hxa' : x * a * x⁻¹ = a * z₀ ^ j₀ := by
    have ha_i₀ : a ^ i₀ = a := by
      have h := (zpow_eq_zpow_iff_modEq (x := a) (m := i₀) (n := 1)).mpr (by
        rw [haord]
        exact (Int.modEq_iff_dvd.mpr hi₀).symm)
      simpa using h
    rw [hxa, ha_i₀]
  -- `j₀ ≢ 0 (mod p)`, else `x` would centralize `A`
  have hj₀ : ¬ (p : ℤ) ∣ j₀ := by
    intro hdvd
    apply hxnC
    have hza : z₀ ^ j₀ = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hz₀ord]; exact hdvd)
    have hcomm_xa : Commute x a := by
      have h := hxa'
      rw [hza, mul_one] at h
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [h]
    intro g hg
    obtain ⟨i, j, rfl⟩ := hcoord g hg
    exact ((hcomm_xa.zpow_right i).mul_right
      ((show Commute x z₀ from hxZ₀ z₀ hz₀Z).zpow_right j)).eq
  -- with `i₀ = 1`: `x^k a x^{-k} = a z₀^{k j₀}`
  have hiter' : ∀ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = a * z₀ ^ ((k : ℤ) * j₀) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have h1 : x ^ (n + 1) * a * (x ^ (n + 1))⁻¹
          = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      have h2 : x * (a * z₀ ^ ((n : ℤ) * j₀)) * x⁻¹
          = (x * a * x⁻¹) * (x * z₀ ^ ((n : ℤ) * j₀) * x⁻¹) := by group
      rw [h1, ih, h2, hxz, hxa', mul_assoc, ← zpow_add]
      congr 2
      push_cast
      ring
  -- coordinates of the target generator: `b = a^m z₀^s` with `p ∤ m`
  obtain ⟨m, sb, hbeq⟩ := hcoord b hbA
  have hm : ¬ (p : ℤ) ∣ m := by
    intro hdvd
    have ham : a ^ m = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [haord]; exact hdvd)
    have hbZ : b ∈ Z₀ := by
      rw [hbeq, ham, one_mul, ← hz₀z]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) sb
    apply hYne
    rw [← hbz]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbZ)
      (by rw [hZ₀card, Nat.card_zpowers, hbord])
  -- solve `k j₀ m ≡ s (mod p)` in the field `ZMod p`
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set u : ZMod p := (j₀ : ZMod p) * (m : ZMod p) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero
      (fun h => hj₀ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
      (fun h => hm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  refine ⟨((sb : ZMod p) * u⁻¹).val, ?_⟩
  set k : ℕ := ((sb : ZMod p) * u⁻¹).val with hk
  have hsolve : (p : ℤ) ∣ ((k : ℤ) * j₀ * m - sb) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    have hkcast : ((k : ℕ) : ZMod p) = (sb : ZMod p) * u⁻¹ := by
      rw [hk, ZMod.natCast_val, ZMod.cast_id]
    rw [hkcast, mul_assoc, ← hu, inv_mul_cancel_right₀ hu0]
  -- conclude: `conj (x^k) • X = ⟨a z₀^{k j₀}⟩ = Y`
  have hconj : MulAut.conj (x ^ k) • X = Subgroup.zpowers (x ^ k * a * (x ^ k)⁻¹) := by
    rw [← haz, conjSmul_eq_map, MonoidHom.map_zpowers]
    rfl
  rw [hconj, hiter' k]
  have htA : a * z₀ ^ ((k : ℤ) * j₀) ∈ A :=
    A.mul_mem haA (hZ₀A (by rw [← hz₀z]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z₀) _))
  have hbmem : b ∈ Subgroup.zpowers (a * z₀ ^ ((k : ℤ) * j₀)) := by
    have hpow : (a * z₀ ^ ((k : ℤ) * j₀)) ^ m = b := by
      rw [(hcomm_az.zpow_right ((k : ℤ) * j₀)).mul_zpow, ← zpow_mul, hbeq]
      congr 1
      rw [zpow_eq_zpow_iff_modEq, hz₀ord]
      refine (Int.modEq_iff_dvd.mpr ?_).symm
      exact hsolve
    rw [← hpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have htne : a * z₀ ^ ((k : ℤ) * j₀) ≠ 1 := by
    intro h
    have := (hsep 1 ((k : ℤ) * j₀) (by rw [zpow_one]; exact h)).1
    have h1 := Int.le_of_dvd one_pos this
    have h2 := (Fact.out : p.Prime).one_lt
    omega
  have htpow : (a * z₀ ^ ((k : ℤ) * j₀)) ^ p = 1 := by
    have h := congrArg Subtype.val (hAea.2 ⟨_, htA⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  have hzc : Nat.card ↥(Subgroup.zpowers (a * z₀ ^ ((k : ℤ) * j₀))) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htpow htne
  rw [← hbz]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbmem)
    (by rw [hzc, Nat.card_zpowers, hbord])).symm

/-! ## Lemma 10.13 — `Ω₁(Z(P))` と rank-two elementary abelian subgroup (PDF p.79) -/

/-- **BG Lemma 10.13** (mmd MISSING_PAGE, PDF p.79): `p ∈ π(G)`,
`A ∈ ℰ_p²(G) ∩ ℰ_p*(G)`, and `P` is a nonabelian `p`-subgroup of `G` containing
`A`. Let `Z₀ = Ω₁(Z(P))` and let `A₀ ∈ ℰ¹(A)` with `A₀ ≠ Z₀`. Then
(a) `Z₀ ∈ ℰ¹(A)`; (b) `C_P(A) = A₀ × Z` for a cyclic subgroup `Z` containing
`Z₀`; and (c) `N_P(A)` acts transitively by conjugation on `ℰ¹(A) - {Z₀}`.

Here `Z₀` is `omega1CenterInG P p`, `C_P(A)` is
`Subgroup.centralizer (A : Set G) ⊓ P`, and the internal product in (b) is encoded by
trivial intersection plus equality with the join, following the existing `IsNarrow` convention. -/
theorem nonabelian_pSubgroup_rankTwo_elemAbelian_structure [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hpG : p ∈ (Nat.card G).primeFactors)
    {A P A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P)
    (hA₀ : elemAbelianOfRankIn p 1 A A₀) (hA₀ne : A₀ ≠ omega1CenterInG P p) :
    elemAbelianOfRankIn p 1 A (omega1CenterInG P p) ∧
    (∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧ omega1CenterInG P p ≤ Z ∧
      A₀ ⊓ Z = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ P = A₀ ⊔ Z) ∧
    (∀ X Y : Subgroup G, elemAbelianOfRankIn p 1 A X → X ≠ omega1CenterInG P p →
      elemAbelianOfRankIn p 1 A Y → Y ≠ omega1CenterInG P p →
        ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ P, MulAut.conj n • X = Y) := by
  classical
  obtain ⟨hAea, hAcard⟩ := hA
  obtain ⟨⟨hA₀ea, hA₀card'⟩, hA₀A⟩ := hA₀
  have hA₀card : Nat.card ↥A₀ = p := by rw [hA₀card', pow_one]
  have hApow : ∀ g ∈ A, g ^ p = 1 := by
    intro g hg
    have h := congrArg Subtype.val (hAea.2 ⟨g, hg⟩)
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  -- a Sylow `p`-subgroup `S ⊇ P` and the (10.6) decomposition `C_S(A) = A₀ ⊔ Y`
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  obtain ⟨Ydec, hYS, hYcyc, hZ₀Y, hA₀Y, hCeq, hCab, hZ₀card⟩ :
      ∃ Y : Subgroup G, Y ≤ (S : Subgroup G) ∧ IsCyclic ↥Y ∧ omega1CenterInG P p ≤ Y ∧
        A₀ ⊓ Y = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = A₀ ⊔ Y ∧
        (∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G),
          ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G), c₁ * c₂ = c₂ * c₁) ∧
        Nat.card ↥(omega1CenterInG P p) = p := by
    rcases Nat.lt_or_ge (pRank ↥(S : Subgroup G) p) 3 with h2 | h3
    · refine centralizer_sylow_decomp_of_rank_le_two hG S hAea hAcard hAmax hPp hPnonab
        hAP hPS hA₀A hA₀card hA₀ne ?_
      rw [rank_le_iff]
      intro q hq
      haveI : Fact q.Prime := ⟨hq⟩
      rcases eq_or_ne q p with rfl | hqp
      · omega
      · rw [pRank_le_iff]
        intro E hEea
        obtain ⟨k, hk⟩ := hEea.isPGroup.exists_card_eq
        have hk0 : k = 0 := by
          by_contra hk0
          have hq_dvd : q ∣ Nat.card ↥(S : Subgroup G) := by
            refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
            rw [hk]
            exact dvd_pow_self q hk0
          obtain ⟨m', hm'⟩ := S.isPGroup'.exists_card_eq
          rw [hm'] at hq_dvd
          exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp
            (hq.dvd_of_dvd_pow hq_dvd))
        rw [hk, hk0, pow_zero, Nat.log_one_right]
        omega
    · exact centralizer_sylow_decomp_of_three_le_rank hG S hAea hAcard hAmax hPp hPnonab
        hAP hPS hA₀A hA₀card hA₀ne (by omega)
  -- (b): `C_P(A) = A₀ ⊔ (Y ⊓ P)` by the Dedekind argument
  have hA₀P : A₀ ≤ P := hA₀A.trans hAP
  have hA₀comm_Y : ∀ u ∈ A₀, ∀ v ∈ Ydec, u * v = v * u := by
    intro u hu v hv
    refine hCab u ?_ v ?_
    · rw [hCeq]; exact Subgroup.mem_sup_left hu
    · rw [hCeq]; exact Subgroup.mem_sup_right hv
  have hCP : Subgroup.centralizer (A : Set G) ⊓ P = A₀ ⊔ (Ydec ⊓ P) := by
    apply le_antisymm
    · intro c hc
      have hcS : c ∈ A₀ ⊔ Ydec := by
        rw [← hCeq]
        exact ⟨hc.1, hPS hc.2⟩
      have hmem : c ∈ (↑A₀ * ↑Ydec : Set G) := by
        rw [(Subgroup.coe_mul_of_left_le_normalizer_right A₀ Ydec
          (le_normalizer_of_forall_comm hA₀comm_Y)).symm]
        exact hcS
      obtain ⟨a₀, ha₀, y, hy, rfl⟩ := Set.mem_mul.mp hmem
      have hyP : y ∈ P := by
        have heq : y = a₀⁻¹ * (a₀ * y) := by group
        rw [heq]
        exact P.mul_mem (P.inv_mem (hA₀P ha₀)) hc.2
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₀)
        (Subgroup.mem_sup_right ⟨hy, hyP⟩)
    · refine sup_le (le_inf ?_ hA₀P) (le_inf ?_ inf_le_right)
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (hAea.1 ⟨g, hg⟩ ⟨u, hA₀A hu⟩)
      · intro v hv
        have hv' : v ∈ A₀ ⊔ Ydec := Subgroup.mem_sup_right hv.1
        rw [← hCeq] at hv'
        exact hv'.1
  refine ⟨⟨⟨?_, ?_⟩, omega1CenterInG_le_of_maximal hAea hAmax hAP⟩,
    ⟨Ydec ⊓ P, inf_le_right, ?_, le_inf hZ₀Y (omega1CenterInG_le P p), ?_, hCP⟩, ?_⟩
  · -- (a) elementary abelian
    exact omega1OfAbelian_isElementaryAbelian.map P.subtype_injective
  · -- (a) cardinality
    rw [pow_one]
    exact hZ₀card
  · -- (b) cyclicity of `Z = Y ⊓ P`
    haveI := hYcyc
    exact Subgroup.isCyclic_of_le inf_le_left
  · -- (b) `A₀ ⊓ Z = ⊥`
    rw [eq_bot_iff, ← hA₀Y]
    exact inf_le_inf_left A₀ inf_le_left
  -- (c): a non-centralizing element of `N_P(A)` exists, and its powers act transitively.
  intro X Yl hX hXne hYl hYlne
  have hCPab : ∀ c₁ ∈ Subgroup.centralizer (A : Set G) ⊓ P,
      ∀ c₂ ∈ Subgroup.centralizer (A : Set G) ⊓ P, c₁ * c₂ = c₂ * c₁ := by
    intro c₁ h₁ c₂ h₂
    exact hCab c₁ ⟨h₁.1, hPS h₁.2⟩ c₂ ⟨h₂.1, hPS h₂.2⟩
  have hCPlt : (Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hPle : P ≤ Subgroup.centralizer (A : Set G) ⊓ P :=
      Subgroup.subgroupOf_eq_top.mp htop
    exact hPnonab ⟨⟨fun a b => Subtype.ext (hCPab _ (hPle a.2) _ (hPle b.2))⟩⟩
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hgrow := normalizerCondition_of_isNilpotent (G := ↥P)
    ((Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P) hCPlt
  obtain ⟨w, hwN, hwC⟩ := SetLike.exists_of_lt hgrow
  -- `A` is exactly the set of exponent-`p` elements of `C_P(A)`
  have hAset : ∀ g : G, g ∈ A ↔ (g ∈ Subgroup.centralizer (A : Set G) ⊓ P ∧ g ^ p = 1) := by
    intro g
    constructor
    · intro hg
      refine ⟨Subgroup.mem_inf.mpr ⟨?_, hAP hg⟩, hApow g hg⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hAea.1 ⟨h, hh⟩ ⟨g, hg⟩)
    · rintro ⟨hg, hgp⟩
      exact mem_of_mem_centralizer_of_pow_eq_one hAea hAmax hg.1 hgp
  -- conjugation by normalizer elements of `C' = C_P(A).subgroupOf P` preserves `C_P(A)`
  have hconjC : ∀ w' : ↥P, w' ∈ Subgroup.normalizer
      (((Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P : Subgroup ↥P) : Set ↥P) →
      ∀ g ∈ Subgroup.centralizer (A : Set G) ⊓ P,
      (w' : G) * g * (w' : G)⁻¹ ∈ Subgroup.centralizer (A : Set G) ⊓ P := by
    intro w' hw' g hg
    have hg' : (⟨g, hg.2⟩ : ↥P) ∈ (Subgroup.centralizer (A : Set G) ⊓ P).subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr hg
    have h2 := (Subgroup.mem_normalizer_iff.mp hw' ⟨g, hg.2⟩).mp hg'
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hwgN : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hh1, hh2⟩ := (hAset h).mp hh
      refine (hAset _).mpr ⟨hconjC w hwN h hh1, ?_⟩
      rw [conj_pow, hh2, mul_one, mul_inv_cancel]
    · intro hh
      obtain ⟨hh1, hh2⟩ := (hAset _).mp hh
      have h3 := hconjC w⁻¹ (Subgroup.inv_mem _ hwN) _ hh1
      have h4 : ((w⁻¹ : ↥P) : G) * ((w : G) * h * (w : G)⁻¹) * ((w⁻¹ : ↥P) : G)⁻¹ = h := by
        push_cast
        group
      rw [h4] at h3
      refine (hAset _).mpr ⟨h3, ?_⟩
      have h5 : ((w : G) * h * (w : G)⁻¹) ^ p = 1 := hh2
      rw [conj_pow] at h5
      have h6 : h ^ p = (w : G)⁻¹ * 1 * (w : G) := by
        rw [← h5]
        group
      simpa using h6
  have hwgnC : ¬ ∀ a ∈ A, (w : G) * a = a * (w : G) := by
    intro hc
    apply hwC
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, w.2⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hc h hh).symm
  have hwgZ₀ : ∀ z ∈ omega1CenterInG P p, (w : G) * z = z * (w : G) := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (mem_omega1OfAbelian.mp hz').1 w)
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp hPp w
  have hword : orderOf (w : G) = p ^ e := by
    rw [← he]
    exact orderOf_injective P.subtype P.subtype_injective w
  obtain ⟨k, hk⟩ := exists_conj_pow_eq_of_fixes_line hAea hAcard hwgN hword
    (omega1CenterInG_le_of_maximal hAea hAmax hAP) hZ₀card hwgZ₀ hwgnC
    hX.2 (by have := hX.1.2; rwa [pow_one] at this) hXne
    hYl.2 (by have := hYl.1.2; rwa [pow_one] at this) hYlne
  exact ⟨(w : G) ^ k, ⟨Subgroup.pow_mem _ hwgN k, P.pow_mem w.2 k⟩, hk⟩


end OddOrder.BG.Ch3.S10
