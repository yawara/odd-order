import OddOrder.Peterfalvi.S14_MaximalI.WitnessSylowCyclic

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S14_MaximalI.MinimalCounterexample` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]



/-- **Peterfalvi (12.10) obligation B, minimality core** (pinned sorried §8/(12.8) obligation, hub
9003 Cluster A): for the type-I witness `L` of (12.9), every Sylow `q`-subgroup of `L` at a prime
`q` dividing `|U|` (`U =` the complement of `H = L_F`) is **cyclic**.

Peterfalvi's argument: a prime `q ∣ |L/H|` has `q < p` — in case (8.3.c) `q ∣ p−1`; in case
(8.3.b) a Sylow `p`-subgroup `P` of `H` is of rank `2` and (8.1.c) yields an order-`q` element of
`L` acting fixed-point-freely on `Ω₁(P)`, so `q ∣ p²−1`, hence `q ∣ p−1` or `q ∣ p+1`, giving
`q < p`.  By the minimality of `p` in (12.8) (no type-I maximal has a noncyclic Sylow `q`-subgroup
of its `M/M_F` for `q < p`), a Sylow `q`-subgroup of `L` is cyclic.

**Assembly** (proven): case (a) of the (8.3) alternative is excluded by
`witness_H_sharp_not_isTISubset_of_typeI`; case (b) is the counting core
`TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel` (`q ∣ p² − 1`) followed by
`prime_lt_of_odd_dvd_sq_sub_one` (`q < p`, using that `p`, `q` are odd); case (c) pairs the
exponent bound `exp U ∣ p − 1` at the prime `p ∣ |H|` with a Cauchy order-`q` element of `U`.
With `q < p`, a noncyclic Sylow `q`-subgroup `Q` of `L` would witness `InPi q` (its `L`-image has
full `q`-order, and `q ∣ [L : L_F] = |U|`), contradicting the (12.8) minimality `minimal_p`. -/
theorem witness_L_sylow_cyclic_of_dvd_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) {q : ℕ} (hq : q.Prime)
    (hqU : q ∣ Nat.card ↥typeI.typeF.U) (Q : Sylow q ↥data.L) :
    IsCyclic ↥(Q : Subgroup ↥data.L) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `P₀ ≤ H`, so `p ∣ |H|`.
  have hP0H : ctr.P0 ≤ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]; exact witness_P0_le_kernel hG data
  have hP0ne : ctr.P0 ≠ ⊥ := fun h => ctr.P0_noncyclic (h ▸ inferInstance)
  have hpH : ctr.p ∣ Nat.card ↥typeI.typeF.H := by
    obtain ⟨k, hk⟩ := ctr.P0_pGroup.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hP0ne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    exact (dvd_pow_self ctr.p hk0).trans (hk ▸ Subgroup.card_dvd_of_le hP0H)
  -- `p` and `q` are odd (divisors of the odd `|G|`).
  have hq_odd : Odd q :=
    hG.odd.of_dvd_nat (hqU.trans (Subgroup.card_subgroup_dvd_card _))
  have hp_odd : Odd ctr.p :=
    hG.odd.of_dvd_nat (hpH.trans (Subgroup.card_subgroup_dvd_card _))
  -- Step A: `q < p`, by the (8.3) alternative for the type-I witness `L`.
  have hqp : q < ctr.p := by
    rcases typeI.alternative with hTI | ⟨hab, hrank⟩ | ⟨hexp, _⟩
    · exact absurd hTI (witness_H_sharp_not_isTISubset_of_typeI hG data typeI)
    · exact prime_lt_of_odd_dvd_sq_sub_one ctr.p_prime hq hp_odd hq_odd
        (typeI.typeF.prime_dvd_sq_sub_one_of_abelian_kernel hab hrank.le hq hpH hqU)
    · have hpmem : ctr.p ∈ (Nat.card ↥typeI.typeF.H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpH, Nat.card_pos.ne'⟩
      haveI : Fintype ↥typeI.typeF.U := Fintype.ofFinite _
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥typeI.typeF.U) q
        (by rwa [← Nat.card_eq_fintype_card])
      have hqp1 : q ∣ ctr.p - 1 :=
        (hu ▸ Monoid.order_dvd_exponent u).trans (hexp ctr.p ctr.p_prime hpmem)
      have hp2 := ctr.p_prime.two_le
      have := Nat.le_of_dvd (by omega) hqp1
      omega
  -- Step B: minimality of `p` (12.8) — a noncyclic Sylow `q` of `L` would put `q ∈ π`.
  by_contra hnc
  refine absurd (ctr.minimal_p q hq ⟨data.L, data.L_maximal, ⟨typeI⟩,
    (Q : Subgroup ↥data.L).map data.L.subtype, Subgroup.map_subtype_le _,
    Q.2.map data.L.subtype, ?_, ?_, ?_⟩) (not_le.mpr hqp)
  · -- The image has full `q`-order in `L`: `¬ q ∣ [L : Q]`.
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective data.L.subtype_injective]
    exact Q.not_dvd_index
  · -- Noncyclicity transfers along `Q ≅ Q.map L.subtype`.
    intro hc
    haveI := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.surjective)
  · -- `q ∣ [L : L_F] = |U|`.
    rw [← typeI.typeF.H_eq, Subgroup.relIndex, typeI.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe typeI.typeF.U_le).toEquiv]
    exact hqU

/-- **Peterfalvi (12.10) obligation B**: the type-I witness `L`'s complement `U` is a Z-group.

**Assembly** (`sorry`-free modulo the (8.3)/(8.1.c)/(12.8) minimality core): to show every Sylow
`q`-subgroup `P` of `U` is cyclic, distinguish `q ∣ |U|` from `q ∤ |U|`.  If `q ∤ |U|` then `P` is
trivial (its order is a `q`-power dividing `|U|`, forcing order `1`), hence cyclic.  If `q ∣ |U|`,
embed `U ↪ L` (via `U_le`): `P` becomes a `q`-subgroup of `L`, contained in a Sylow `q`-subgroup `Q`
of `L`, which is cyclic by the minimality core `witness_L_sylow_cyclic_of_dvd_complement`; a subgroup
of a cyclic group is cyclic, so `P` is cyclic. -/
theorem witness_L_complement_isZGroup [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    _root_.IsZGroup ↥typeI.typeF.U := by
  classical
  rw [isZGroup_iff]
  intro q hq P
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqU : q ∣ Nat.card ↥typeI.typeF.U
  · -- `q ∣ |U|`: embed `P` into `L`, contain it in a cyclic Sylow `q`-subgroup of `L`.
    -- `P`, pushed along `U ↪ L`, is a `q`-subgroup of `L`.
    have hincl : Function.Injective (Subgroup.inclusion typeI.typeF.U_le) :=
      Subgroup.inclusion_injective _
    set PL : Subgroup ↥data.L :=
      (P : Subgroup ↥typeI.typeF.U).map (Subgroup.inclusion typeI.typeF.U_le) with hPL
    have hPLpg : IsPGroup q ↥PL :=
      (P.2.map (Subgroup.inclusion typeI.typeF.U_le))
    obtain ⟨Q, hQle⟩ := hPLpg.exists_le_sylow
    -- The containing Sylow `q`-subgroup of `L` is cyclic (minimality core).
    haveI hQcyc : IsCyclic ↥(Q : Subgroup ↥data.L) :=
      witness_L_sylow_cyclic_of_dvd_complement hG data typeI hq hqU Q
    -- A subgroup of a cyclic group is cyclic; `PL ≤ Q ≅ P`.
    haveI : IsCyclic ↥PL := Subgroup.isCyclic_of_le hQle
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective (P : Subgroup ↥typeI.typeF.U)
        (Subgroup.inclusion typeI.typeF.U_le) hincl).symm.surjective
  · -- `q ∤ |U|`: the Sylow `q`-subgroup is trivial, hence cyclic.
    have hcard : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) ∣ Nat.card ↥typeI.typeF.U :=
      (P : Subgroup ↥typeI.typeF.U).card_subgroup_dvd_card
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hqk : q ^ k ∣ Nat.card ↥typeI.typeF.U := hk ▸ hcard
    have hk0 : k = 0 := by
      by_contra hk0
      exact hqU ((dvd_pow_self q hk0).trans hqk)
    have hcard1 : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) = 1 := by rw [hk, hk0, pow_zero]
    haveI : Subsingleton ↥(P : Subgroup ↥typeI.typeF.U) :=
      (Finite.card_le_one_iff_subsingleton).mp (by omega)
    infer_instance

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is Frobenius with kernel
`L_F`.  **Assembly** (`sorry`-free modulo the two (12.10) obligations): `L` is Type I
(`witness_L_isTypeI`) and its complement `U` is a Z-group (`witness_L_complement_isZGroup`), so the
(8.2.b) bridge `typeI_frobenius_of_isZGroup_complement` yields the Frobenius structure with kernel
`H = L_F` (`typeF.H_eq`). -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  obtain ⟨typeI⟩ := witness_L_isTypeI hG data
  exact ⟨{ typeI := typeI
           complement := typeI.typeF.U.subgroupOf data.L
           kernel_eq_MF := typeI.typeF.H = maxNilpotentNormalHall data.L
           kernel_eq_MF_holds := typeI.typeF.H_eq
           frobenius := typeI_frobenius_of_isZGroup_complement typeI
             (witness_L_complement_isZGroup hG data typeI) },
         typeI.typeF.H_eq⟩

/-- The type-`τ` **main subgroup** `M_s` is contained in `M` (both `M_F` and `[M,M]` are). -/
theorem mainSubgroup_le (M : Subgroup G) (tau : OddOrder.GroupTheory.PeterfalviType) :
    OddOrder.GroupTheory.mainSubgroup M tau ≤ M := by
  cases tau <;>
    simp only [OddOrder.GroupTheory.mainSubgroup, OddOrder.GroupTheory.derivedInG] <;>
    first
      | exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le M
      | exact Subgroup.map_subtype_le _

/-- **Peterfalvi (12.11), first assertion**: `M ∩ L` complements `K = M_F` in `M`.  This is the
"first assertion follows from (12.9) and (8.13.c1)" step, with the (8.13)/BG roles swapped from
the (12.11) notation: the witness `x ∈ Ω₁(P₀)^# ⊆ L_F = L_σ` (type I) is a `σ`-sharp element of
`L` **escaping `L`** (`C_G(x) ⊄ L`), and its supporting maximal is `M` (`C_G(x) ≤ N_G(⟨x⟩) ≤ M`
pins `M` in the singleton `𝓜(C_G(x))`).

**Assembly** (proven): BG Theorem D(4) tail — "`M ∩ N` is a complement of `N_σ` in `N`" — is the
`IsComplement'` conjunct of `signalizer_structure_of_mem_sigmaSharp` (its unique `N` is `M` by the
singleton), applied at `M' := L ∈ 𝓜_σ(x)`; `N_σ = M_σ = M_F = K` is the type-I identification
`MF_eq_Msigma`. -/
theorem intersection_complements_K [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) := by
  classical
  -- The witness `L` is type I with `L_F = L_σ`, so `x ∈ P₀ ⊆ L_F` is `σ`-sharp in `L`.
  have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG data
  have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
      (Or.inl hLtypeI)
  have hxLσ : data.x ∈ OddOrder.BG.Ch3.S10.Msigma data.L :=
    hLF_eq ▸ witness_P0_le_kernel hG data data.x_mem_P0
  have hxσ : data.x ∈ OddOrder.BG.Ch4.S14.sigmaSharp data.L :=
    ⟨hxLσ, by simpa using data.x_ne_one⟩
  -- `C_G(x) ≤ M` (via `N_G(⟨x⟩) ≤ M`), so `M` is THE maximal subgroup over `C_G(x)`.
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG data.L_maximal hxσ data.centralizer_x_not_le_L
  have hMN₀ : ctr.M = N₀ := by
    have hMin : ctr.M ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨ctr.M_maximal, hCM⟩
    rw [hN₀] at hMin
    exact hMin
  -- The signalizer structure at the escaping `σ`-sharp `x`; its unique `N` is `M`.
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x).ncard := by
    by_contra h
    push Not at h
    exact data.centralizer_x_not_le_L
      (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG data.L_maximal hxLσ
        data.x_ne_one h)
  obtain ⟨N, ⟨hNmax, hCN, -, -, -, -, hforall⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG data.L_maximal hxσ hgt
  have hNM : N = ctr.M := by
    have hNin : N ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨hNmax, hCN⟩
    rw [hN₀] at hNin
    rw [hNin, ← hMN₀]
  -- `L ∈ 𝓜_σ(x)`: apply the Theorem D(4) complement conjunct at `M' = L`.
  have hLin : data.L ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x :=
    ⟨data.L_maximal, hxLσ⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall data.L hLin
  rw [hNM, ← MF_eq_Msigma hG ctr,
    show data.L ⊓ ctr.M = ctr.M ⊓ data.L from inf_comm .. ] at hcompl
  exact hcompl

/-- **`|M ∩ L|` is coprime to `|K|`** (from the first assertion (12.11) + `M_F` Hall).  `M ∩ L`
complements `K = M_F` in `M` (`intersection_complements_K`), so `|M ∩ L| = [M : K]`, which is
coprime to `|K|` because `K = M_F` is a Hall subgroup of `M`. -/
theorem card_MinfL_coprime_card_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nat.Coprime (Nat.card ↥(ctr.M ⊓ data.L)) (Nat.card ↥ctr.K) := by
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hcompl := intersection_complements_K hG data
  have hHall := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
  rw [← ctr.K_eq_MF] at hHall
  -- `hHall : Coprime |K| [M : K]`;  `[M : K] = |M ∩ L|` by the complement.
  have hidx : (ctr.K.subgroupOf ctr.M).index = Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) :=
    hcompl.symm.index_eq_card
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hHall
  exact hHall.symm

/-- **Peterfalvi (12.11), core of the second assertion**: a subgroup `A ≤ M ∩ L` meeting the
witness kernel `H = L_F` trivially (`A ⊓ H = ⊥`, i.e. of order prime to `|H|`) is trivial.

The genuine (12.11) argument, now fully assembled from the landed infrastructure.  Put
`P = O_p(H) ∩ M` (an `A`-invariant `p`-subgroup of `H` containing `P₀`, via the nilpotent core
`opiCoreInG`); then:
* `P` does not centralize `K` (`P₀_not_le_centralizer_K`, `P₀ ≤ P`);
* `P ⊔ A` is Frobenius with kernel `P` (from `L`'s Frobenius structure), acts coprimely on `K`
  (`P ⊔ A ≤ M ∩ L`, coprime to `|K|`), so by Wielandt (9.1)
  `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes` gives `C_K(A) ≠ 1`;
* `C_K(x) ≠ 1` by (12.9) (`ctr.CKx_not_le_Kprime`);
* since `M ∩ L` complements `K` in `M` (first assertion), `A` and `x` land in a common abelian
  subgroup `W` (`exists_abelian_centralizer_le_of_isComplement` with `V = M ∩ L`), so `A`
  centralizes `x`;
* by `L`'s Frobenius condition (4) (`centralizer_kernel_le`, `x ∈ H^#`), `A ≤ C_L(x) ⊆ H`, so
  `A ⊆ H`, forcing `A = A ⊓ H = ⊥`. -/
theorem witness_MinfL_pprime_subgroup_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) {A : Subgroup G}
    (hAML : A ≤ ctr.M ⊓ data.L) (hAH : A ⊓ maxNilpotentNormalHall data.L = ⊥) (hAne : A ≠ ⊥) :
    False := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hAM : A ≤ ctr.M := hAML.trans inf_le_left
  have hAL : A ≤ data.L := hAML.trans inf_le_right
  haveI hHnilp : Group.IsNilpotent ↥H := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent data.L
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hHnorm : data.L ≤ Subgroup.normalizer (H : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L
  -- Frobenius structure of `L` with kernel `H` (upstream of this theorem).
  obtain ⟨frob, _⟩ := witness_L_frobenius hG data
  have hHfrob : frob.typeI.typeF.H = H := frob.typeI.typeF.H_eq
  have hFrobL : ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (H.subgroupOf data.L) C :=
    ⟨frob.complement, hHfrob ▸ frob.frobenius⟩
  -- `x ∈ H^#` and `x ∈ M ∩ L`.
  have hxH : data.x ∈ H := witness_P0_le_kernel hG data data.x_mem_P0
  have hxML : data.x ∈ ctr.M ⊓ data.L := ⟨ctr.P0_le_M data.x_mem_P0, hHL hxH⟩
  -- `P = O_p(H) ∩ M` contains `P₀`, sits inside `H` and `M`.
  set P : Subgroup G := opiCoreInG ({ctr.p} : Set ℕ) H ⊓ ctr.M with hPdef
  have hP0_le_P : ctr.P0 ≤ P :=
    le_inf (pGroup_le_opiCoreInG_of_le_of_isNilpotent ctr.P0_pGroup (witness_P0_le_kernel hG data))
      ctr.P0_le_M
  have hP_le_H : P ≤ H := inf_le_left.trans (opiCoreInG_le _ _)
  have hP_le_M : P ≤ ctr.M := inf_le_right
  have hP0ne : ctr.P0 ≠ ⊥ := fun hb => ctr.P0_noncyclic (hb ▸ isCyclic_of_subsingleton)
  have hPne : P ≠ ⊥ := fun hb => hP0ne (le_bot_iff.mp (hb ▸ hP0_le_P))
  -- `A` normalises `P` (normalises `O_p(H)` and `M`).
  have hAnorm_opi : A ≤ Subgroup.normalizer (opiCoreInG ({ctr.p} : Set ℕ) H) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ (hAL.trans hHnorm)
  have hAnorm_M : A ≤ Subgroup.normalizer (ctr.M : Set G) := hAM.trans Subgroup.le_normalizer
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hOpi := (Subgroup.mem_normalizer_iff.mp (hAnorm_opi ha)) y
    have hM := (Subgroup.mem_normalizer_iff.mp (hAnorm_M ha)) y
    simp only [hPdef, Subgroup.mem_inf]
    rw [hOpi, hM]
  -- `P ⊔ A ≤ N_G(K)` and `≤ M ∩ L`.
  have hMnorm_K : ctr.M ≤ Subgroup.normalizer (ctr.K : Set G) :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M
  have hPAK : P ⊔ A ≤ Subgroup.normalizer (ctr.K : Set G) :=
    sup_le (hP_le_M.trans hMnorm_K) (hAM.trans hMnorm_K)
  have hPA_ML : P ⊔ A ≤ ctr.M ⊓ data.L :=
    sup_le (le_inf hP_le_M (hP_le_H.trans hHL)) hAML
  -- `K` is solvable (subgroup of the solvable maximal `M`).
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  haveI hMsolv : IsSolvable ↥ctr.M := hG.solvable_of_mem_maximalSubgroups ctr.M_maximal
  haveI hKsolv : IsSolvable ↥ctr.K :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hKM)
  -- Coprimality of the `P ⊔ A`-action on `K`.
  have hcop : Nat.Coprime (Nat.card ↥ctr.K) (Nat.card ↥(P ⊔ A)) :=
    (card_MinfL_coprime_card_K hG data).symm.coprime_dvd_right (Subgroup.card_dvd_of_le hPA_ML)
  -- `P` does not centralize `K`.
  have hPnc : ¬ P ≤ Subgroup.centralizer (ctr.K : Set G) := fun hPc =>
    P0_not_le_centralizer_K hG ctr (hP0_le_P.trans hPc)
  -- **`C_K(A) ≠ 1`** (Wielandt (9.1) via the sub-Frobenius engine).
  obtain ⟨n, hnK, hn1, hnA⟩ := exists_ne_one_centralized_by_complement_of_kernel_not_centralizes
    hHL hFrobL hP_le_H hPne hAL hAH hAne hAP hPAK hKsolv hcop hPnc
  -- **`C_K(x) ≠ 1`** (Peterfalvi (12.9)).
  obtain ⟨n', hn'mem, hn'K'⟩ := SetLike.not_le_iff_exists.mp data.CKx_not_le_Kprime
  obtain ⟨hn'C, hn'K⟩ := Subgroup.mem_inf.mp hn'mem
  have hn'1 : n' ≠ 1 := fun h => hn'K' (by rw [h]; exact Subgroup.one_mem _)
  -- **`A` and `x` in a common abelian `W ≤ M ∩ L`** (step (8.1.b), `V = M ∩ L`).
  obtain ⟨typeIM⟩ := ctr.M_typeI
  have htypeFH : typeIM.typeF.H = ctr.K := ctr.K_eq_MF ▸ typeIM.typeF.H_eq
  obtain ⟨W, hWab, hWle⟩ := exists_abelian_centralizer_le_of_isComplement hMsolv typeIM.typeF
    (V := ctr.M ⊓ data.L) inf_le_left (htypeFH ▸ intersection_complements_K hG data)
  have hnFH : n ∈ typeIM.typeF.H := by rw [htypeFH]; exact hnK
  have hn'FH : n' ∈ typeIM.typeF.H := by rw [htypeFH]; exact hn'K
  have hA_W : A ≤ W := by
    intro a haA
    have haC : (a : G) ∈ Subgroup.centralizer ({n} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hnA a haA))
    exact hWle n hnFH hn1 ⟨hAML haA, haC⟩
  have hx_W : data.x ∈ W := by
    have hxC : data.x ∈ Subgroup.centralizer ({n'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hn'C).symm
    exact hWle n' hn'FH hn'1 ⟨hxML, hxC⟩
  -- **`A` centralizes `x`** (both in abelian `W`), then **`A ⊆ H`** by Frobenius condition (4).
  have hA_H : A ≤ H := by
    intro a haA
    have hax : (a : G) * data.x = data.x * a :=
      congrArg Subtype.val (hWab.is_comm.comm ⟨a, hA_W haA⟩ ⟨data.x, hx_W⟩)
    have hxHfrob : (⟨data.x, hHL hxH⟩ : ↥data.L) ∈ frob.typeI.typeF.H.subgroupOf data.L := by
      rw [Subgroup.mem_subgroupOf, hHfrob]; exact hxH
    have hx1 : (⟨data.x, hHL hxH⟩ : ↥data.L) ≠ 1 :=
      fun h => data.x_ne_one (by simpa using congrArg Subtype.val h)
    have hcent := frob.frobenius.centralizer_kernel_le _ hxHfrob hx1
    have haC : (⟨a, hAL haA⟩ : ↥data.L) ∈
        Subgroup.centralizer ({(⟨data.x, hHL hxH⟩ : ↥data.L)} : Set ↥data.L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa using hax)
    have haH := hcent haC
    rw [Subgroup.mem_subgroupOf, hHfrob] at haH
    exact haH
  exact hAne (le_bot_iff.mp (hAH ▸ le_inf le_rfl hA_H))

/-- **Peterfalvi (12.11), second assertion**: `M ∩ L ⊆ H = L_F`.  `M ∩ L` has no nontrivial
subgroup meeting `H` trivially (`witness_MinfL_pprime_subgroup_eq_bot`), so its order is coprime to
`[L : H]` (any common prime would give a nontrivial Sylow subgroup meeting `H` trivially), and the
normal-Hall reduction `le_of_coprime_card_index_of_normal` places `M ∩ L` inside `H`. -/
theorem intersection_le_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hMLL : ctr.M ⊓ data.L ≤ data.L := inf_le_right
  haveI hHnorm : (H.subgroupOf data.L).Normal :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- `|M ∩ L|` is coprime to `[L : H]`.
  have hcop : Nat.Coprime (Nat.card ↥((ctr.M ⊓ data.L).subgroupOf data.L))
      (H.subgroupOf data.L).index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMLL).toEquiv, Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd
    haveI : Fact q.Prime := ⟨hq⟩
    rw [Nat.dvd_gcd_iff] at hqdvd
    obtain ⟨hqML, hqidx⟩ := hqdvd
    -- A Sylow `q`-subgroup `Q` of `M ∩ L` is nontrivial, meets `H` trivially, contradicts the core.
    obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥(ctr.M ⊓ data.L)))
    set A : Subgroup G := (Q : Subgroup ↥(ctr.M ⊓ data.L)).map (ctr.M ⊓ data.L).subtype with hAdef
    have hApg : IsPGroup q ↥A := Q.2.map _
    have hAML : A ≤ ctr.M ⊓ data.L := Subgroup.map_subtype_le _
    -- `q ∉ π(H)` (as `q ∣ [L : H]` and `H` is Hall in `L`), so `A ⊓ H = ⊥`.
    have hqH : ¬ q ∣ Nat.card ↥H := by
      have hHallL := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall data.L).coprime_index
      intro hdvd
      have hdvd' : q ∣ Nat.card ↥(H.subgroupOf data.L) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]; exact hdvd
      have hg : q ∣ Nat.gcd (Nat.card ↥(H.subgroupOf data.L)) (H.subgroupOf data.L).index :=
        Nat.dvd_gcd hdvd' hqidx
      rw [hHallL] at hg
      exact hq.one_lt.ne' (Nat.dvd_one.mp hg)
    have hAH : A ⊓ H = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzA, hzH⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_bot]
      by_contra hzne
      apply hqH
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hApg) ⟨z, hzA⟩
      have hoz : orderOf z = q ^ k := by
        rw [← hk]; exact orderOf_injective A.subtype A.subtype_injective ⟨z, hzA⟩
      have hk0 : k ≠ 0 := fun h => hzne (orderOf_eq_one_iff.mp (by rw [hoz, h, pow_zero]))
      have hqoz : q ∣ Nat.card ↥(Subgroup.zpowers z) := by
        rw [Nat.card_zpowers, hoz]; exact dvd_pow_self q hk0
      exact hqoz.trans (Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hzH))
    have hAne : A ≠ ⊥ := by
      have hqQ : q ∣ Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) := by
        have hmul := Subgroup.card_mul_index (Q : Subgroup ↥(ctr.M ⊓ data.L))
        rcases (Nat.Prime.dvd_mul hq).mp (hmul ▸ hqML) with h | h
        · exact h
        · exact absurd h Q.not_dvd_index
      intro hb
      have hA1 : Nat.card ↥A = Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (ctr.M ⊓ data.L).subtype_injective).toEquiv).symm
      rw [hb, Subgroup.card_bot] at hA1
      rw [← hA1] at hqQ
      exact hq.one_lt.ne' (Nat.dvd_one.mp hqQ)
    exact witness_MinfL_pprime_subgroup_eq_bot hG data hAML hAH hAne
  -- Apply the normal-Hall reduction.
  have hle := Subgroup.le_of_coprime_card_index_of_normal hcop
  intro z hz
  have : (⟨z, hMLL hz⟩ : ↥data.L) ∈ H.subgroupOf data.L :=
    hle (Subgroup.mem_subgroupOf.mpr hz)
  exact Subgroup.mem_subgroupOf.mp this

/-- **Peterfalvi (12.11)**: `M ∩ L` complements `K` in `M` and lies in the Fitting kernel
`H = L_F` of the witness subgroup `L`.

**Assembly**: the two textbook assertions of (12.11) are `intersection_complements_K` (from (12.9)
and (8.13.c1)) and `intersection_le_kernel` (the (8.1.b/c)+(9.1)+(12.10) `A = 1` argument),
combined here. -/
theorem intersection_complement_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L :=
  ⟨intersection_complements_K hG data, intersection_le_kernel hG data⟩

/-- **Peterfalvi (12.10), non-TI clause**: for the (12.9) witness `L`, its Frobenius kernel
`H = L_F` has `H^#` **not** a TI-subset of `G`.  This is the "By (12.9), `H^#` is not a TI-subset"
step of (12.10): the rank-two witness `x ∈ Ω₁(P₀)^#` has `C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`)
while `N_G(H) = L` (maximality of `L` + `H = L_F` normal); pick `g ∈ C_G(x) ∖ L`, then `g ∉ N_G(H)`
yet `g x g⁻¹ = x ∈ H^#`, witnessing the TI failure (`x ∈ H^# ∩ (H^#)^g`).

This is the honest (12.9)/(12.10) prerequisite of the *witness* coherence route: with it,
`witness_L_coherent` dispatches only through the (b)/(c) cases of (12.6) (which are `sorry`-free),
never the TI-only case (a) — so the witness coherence depends on this genuine (12.9) fact rather
than on the (8.18.c) geometry that case (a) (`sibleyTarget_frobI`) transitively needs.

Specialization of the `TypeIData`-form `witness_H_sharp_not_isTISubset_of_typeI` to the
Frobenius witness (whose `x ∈ H` route is the upstream `witness_P0_le_kernel`, not (12.11)). -/
theorem witness_H_sharp_not_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup frob.typeI.typeF.H)
        (Subgroup.normalizer (frob.typeI.typeF.H : Set G)) :=
  witness_H_sharp_not_isTISubset_of_typeI hG data frob.typeI

/-- **Peterfalvi (12.1) for the witness subgroup `L`, with its Frobenius witness**: the second
maximal subgroup `L` of (12.9) carries the (12.1) Hypothesis together with an explicit Frobenius
decomposition of its kernel `H = L_F`.  Since `L` is type I (Frobenius, by (12.10)
`witness_L_frobenius`), `hypothesis_of_typeIData` applied to the recovered `TypeIData` yields the
Hypothesis whose `typeI` is that very data, so the Frobenius group structure `frob.frobenius`
transfers to `hyp.H`.  This Frobenius witness is the structural input to coherence (12.6). -/
theorem witness_L_hypothesis_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (hyp.H.subgroupOf data.L) C ∧
      ¬ OddOrder.GroupTheory.IsTISubset
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
          (Subgroup.normalizer (hyp.typeI.typeF.H : Set G)) := by
  obtain ⟨frob, hker⟩ := witness_L_frobenius hG data
  obtain ⟨hyp, hhyp⟩ := hypothesis_of_typeIData hG data.L_maximal frob.typeI
  have hH : hyp.typeI.typeF.H = frob.typeI.typeF.H := by rw [hhyp]
  refine ⟨hyp, frob.complement, ?_, ?_⟩
  · rw [show hyp.H = hyp.typeI.typeF.H from rfl, hH]
    exact frob.frobenius
  · rw [hH]
    exact witness_H_sharp_not_isTISubset hG data frob

/-- **Peterfalvi (12.1) Hypothesis for the witness subgroup `L`** (forgetful form of
`witness_L_hypothesis_frobenius`). -/
theorem witness_L_hypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nonempty (Hypothesis data.L) := by
  obtain ⟨hyp, _⟩ := witness_L_hypothesis_frobenius hG data
  exact ⟨hyp⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) for the witness subgroup `L`**: the type-I family `S` of `L` is coherent.
Combines the Hypothesis + Frobenius witness of `witness_L_hypothesis_frobenius` with the (12.6)
Frobenius-case coherence.  Crucially the witness dispatches only through the **(b)/(c)** cases
(both `sorry`-free): its `H^#` is *not* TI (Peterfalvi (12.10), `witness_H_sharp_not_isTISubset`),
so the TI-only case (a) `sibleyTarget_frobI` is excluded — hence this coherence never depends on the
(8.18.c) geometry that case (a) transitively needs, only on the genuine (12.9)/(12.10) witness facts.
This is the coherence input "`S` coherent" of the (12.16) Dade calculation — it feeds the `(7.8.b)`
norm bound `hB` of `CounterexampleDadeData` via the §7 `Hypothesis78`/`NormEstimates`. -/
theorem witness_L_coherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  obtain ⟨hyp, C, hC, hNonTI⟩ := witness_L_hypothesis_frobenius hG data
  refine ⟨hyp, ?_⟩
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact absurd hTI hNonTI
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp ⟨C, hC⟩ hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp ⟨C, hC⟩ hexp


/-- **(12.12) Case A core.**  A finite group `E` acting faithfully on a one-dimensional
`𝔽_p`-space `V` is cyclic, with `|E| ∣ |V| - 1 = p - 1`.  This is the reducible / rank-one case
of Peterfalvi (12.12): `End_{𝔽_p}(V) ≅ 𝔽_p` (every endomorphism of a line is a homothety), so
`E ↪ End(V)ˣ ≅ (ℤ/p)ˣ`, a cyclic group of order `p - 1`. -/
theorem isCyclic_and_card_dvd_of_faithful_one_dim
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `End_{𝔽_p}(V) ≅ 𝔽_p` via `algebraMap` (bijective in dimension one: every endo is `c • id`).
  have hsurj : Function.Surjective (algebraMap (ZMod p) (Module.End (ZMod p) V)) := by
    intro u
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) V)) :=
    (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective
  let eRing : ZMod p ≃+* Module.End (ZMod p) V := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  -- `E ↪ End(V)ˣ ≃ (ℤ/p)ˣ`.
  let φ : E →* (ZMod p)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).symm.toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hfaith
    have h1 : (MonoidHom.toHomUnits ρ) a = (MonoidHom.toHomUnits ρ) b :=
      (Units.mapEquiv eRing.toMulEquiv).symm.injective (by simpa [φ] using hab)
    simpa using congrArg (Units.val) h1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : IsCyclic φ.range := inferInstance
  have hcardV : Nat.card V = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, pow_one, Nat.card_eq_fintype_card,
      ZMod.card]
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
      (MonoidHom.ofInjective hφinj).symm.surjective, ?_⟩
  rw [hcardV]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

/-- **(12.12) irreducible-case core.**  An odd-order group `E` acting faithfully and
irreducibly on a two-dimensional `𝔽_p`-space `V` (with `p ∤ |E|`) is cyclic, with
`|E| ∣ |V| - 1 = p² - 1`.  This is the rank-two irreducible case of Peterfalvi (12.12):
BG Theorem 2.6(a) (`odd_two_dim_abelian`) abelianizes `E`, and the commutativity-free Singer
mechanism (`isCyclic_and_card_dvd_of_faithful_irreducible_comm`) then realizes `E` inside the
units of the Singer field `𝔽_p[E] ⧸ I ≅ 𝔽_{p²}`. -/
theorem isCyclic_and_card_dvd_of_odd_two_dim_irreducible
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- BG 2.6(a): a faithful odd two-dimensional representation has abelian image.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  -- Give `V` the `𝔽_p[E]`-module structure of the representation *directly* (this is
  -- definitionally `ρ.asModule`'s instance, but stated on `V` so that instance synthesis does
  -- not choke on the `ρ.asModule` notation — which it does once `IsIrreducible ρ` is around).
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  exact isCyclic_and_card_dvd_of_faithful_irreducible_comm (M := V) hcomm hfaith'

/-- **(12.12) `p + 1` refinement, irreducible case.**  An odd-order group `E` (`p ∤ |E|`) acting
faithfully and irreducibly on a two-dimensional `𝔽_p`-space `V`, with **no nontrivial element
acting as an `𝔽_p`-scalar** (`hnonscalar`), is cyclic with `|E| ∣ p + 1`.

This is the rank-two refinement of Peterfalvi (12.12): the plain irreducible core
(`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`) only bounds `|E| ∣ p² - 1`.  The Singer
realization places `E` inside the cyclic group `𝔽_{p²}ˣ` (order `p² - 1`), where the non-scalar
hypothesis makes it meet the scalar subgroup `𝔽_pˣ` (order `p - 1`) trivially, so
`coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar` gives `Coprime |E| (p - 1)`.  Together
with `|E| ∣ p² - 1 = (p - 1)(p + 1)`, coprimality to the first factor forces `|E| ∣ p + 1`. -/
theorem isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E)
    (hnonscalar : ∀ e : E, (∃ n : ℕ, ∀ x : V, ρ e x = n • x) → e = 1) :
    IsCyclic E ∧ Nat.card E ∣ p + 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `|E| ∣ p² - 1` and cyclicity from the irreducible core.
  obtain ⟨hcyc, hdvd_sq⟩ :=
    isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  have hcardV : Nat.card V = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, Nat.card_eq_fintype_card, ZMod.card]
  rw [hcardV] at hdvd_sq
  -- Singer non-scalar core ⟹ `Coprime |E| (p - 1)`.  Reuse the `𝔽ₚ[E]`-module setup of the core.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  have hns' : ∀ e : E,
      (∃ n : ℕ, ∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = n • x) → e = 1 := by
    rintro e ⟨n, hn⟩
    exact hnonscalar e ⟨n, fun x => by rw [← hsmul e x]; exact hn x⟩
  have hcop : Nat.Coprime (Nat.card E) (p - 1) :=
    OddOrder.RepresentationTheory.coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar
      hcomm hfaith' hns'
  -- `|E| ∣ (p - 1)(p + 1) = p² - 1` and `Coprime |E| (p - 1)` force `|E| ∣ p + 1`.
  have hpq : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := (Fact.out (p := p.Prime)).two_le; omega⟩
    show (n + 1) * (n + 3) = (n + 2) ^ 2 - 1
    have hexp : (n + 2) ^ 2 = (n + 1) * (n + 3) + 1 := by ring
    omega
  rw [← hpq] at hdvd_sq
  exact hcop.dvd_of_dvd_mul_left hdvd_sq

/-- **(12.12) rep-theory core (dichotomy form).**  A finite odd-order group `E` (`p ∤ |E|`)
acting **fixed-point-freely** on an `𝔽_p`-space `V` of dimension `1` or `2` is **cyclic**, and
either `|E| ∣ p − 1`, or the action is `2`-dimensional **irreducible** with `|E| ∣ p² − 1`.
Dim 1 and the reducible dim-2 case (an `E`-invariant line) go through Case A
(`isCyclic_and_card_dvd_of_faithful_one_dim`); irreducible dim 2 is Case B
(`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`).  The FPF hypothesis makes `E` faithful on
every nonzero invariant subspace.  The dichotomy (rather than the combined `|E| ∣ |V| − 1`)
retains the irreducibility needed by the (12.12) `p + 1` refinement
(`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`). -/
theorem isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨
      (Module.finrank (ZMod p) V = 2 ∧ Representation.IsIrreducible ρ ∧
        Nat.card E ∣ p ^ 2 - 1)) := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- Step 1: the FPF hypothesis makes `ρ` faithful.
  -- `V` is nontrivial because `finrank V ≥ 1`, so it has a nonzero vector; a nontrivial element in
  -- the kernel would fix that vector, contradicting `hfpf`.
  haveI hVnt : Nontrivial V := by
    rcases hdim with h | h
    · exact Module.nontrivial_of_finrank_eq_succ h
    · exact Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [h])
  have hfaith : Function.Injective ρ := by
    intro a b hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (hfpf (b⁻¹ * a) hba v ?_)
    rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rcases hdim with hd1 | hd2
  · -- dim 1: Case A; `|V| = p`.
    obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_faithful_one_dim ρ hfaith hd1
    have hcardV : Nat.card V = p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd1, pow_one, Nat.card_eq_fintype_card,
        ZMod.card]
    exact ⟨hcyc, Or.inl (by rwa [hcardV] at hdvd)⟩
  · -- dim 2.
    by_cases hirr : Representation.IsIrreducible ρ
    · -- irreducible: Case B; `|V| = p²`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hd2 hp_ndvd
      have hcardV : Nat.card V = p ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
      exact ⟨hcyc, Or.inr ⟨hd2, hirr, by rwa [hcardV] at hdvd⟩⟩
    · -- reducible: a proper nonzero invariant line `W` exists; Case A on `W.toRepresentation`.
      have hbnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
        bot_ne_top (congrArg Subrepresentation.toSubmodule h)
      haveI : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
      have hnotall : ¬ ∀ W : Subrepresentation ρ, W = ⊥ ∨ W = ⊤ := fun H =>
        hirr { eq_bot_or_eq_top := H }
      push Not at hnotall
      obtain ⟨W, hWbot, hWtop⟩ := hnotall
      -- `W` is a proper nonzero subrepresentation; its submodule has `finrank = 1`.
      have hWsub_bot : W.toSubmodule ≠ ⊥ := fun h =>
        hWbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      have hWsub_top : W.toSubmodule ≠ ⊤ := fun h =>
        hWtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      haveI : Finite ↥W.toSubmodule := Subtype.finite
      haveI : Module.Finite (ZMod p) ↥W.toSubmodule := Module.Finite.of_finite
      have hpos : 0 < Module.finrank (ZMod p) ↥W.toSubmodule := by
        have := Submodule.finrank_lt_finrank_of_lt (s := (⊥ : Submodule (ZMod p) V))
          (t := W.toSubmodule) (lt_of_le_of_ne bot_le (Ne.symm hWsub_bot))
        simpa using this
      have hlt : Module.finrank (ZMod p) ↥W.toSubmodule < Module.finrank (ZMod p) V :=
        Submodule.finrank_lt hWsub_top
      have hWdim : Module.finrank (ZMod p) ↥W.toSubmodule = 1 := by
        rw [hd2] at hlt; omega
      -- faithfulness of `W.toRepresentation` from `hfpf` restricted to `W`.
      have hfaithW : Function.Injective W.toRepresentation := by
        intro a b hab
        by_contra hne
        have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
        -- every element of `W` is fixed by `ρ (b⁻¹ a)`, hence is `0` by `hfpf`; so `W = ⊥`.
        apply hWsub_bot
        rw [Submodule.eq_bot_iff]
        intro w hw
        have hfix : W.toRepresentation (b⁻¹ * a) ⟨w, hw⟩ = ⟨w, hw⟩ := by
          rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
            inv_mul_cancel, map_one, Module.End.one_apply]
        have hfixV : ρ (b⁻¹ * a) w = w := by
          have := congrArg Subtype.val hfix
          simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply] using this
        exact hfpf (b⁻¹ * a) hba w hfixV
      -- Case A on `W.toRepresentation` gives `IsCyclic E ∧ |E| ∣ p - 1`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_faithful_one_dim W.toRepresentation hfaithW hWdim
      have hcardW : Nat.card ↥W.toSubmodule = p := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hWdim, pow_one, Nat.card_eq_fintype_card,
          ZMod.card]
      exact ⟨hcyc, Or.inl (by rwa [hcardW] at hdvd)⟩

/-- **(12.12) rep-theory core (combined).**  A finite odd-order group `E` (`p ∤ |E|`) acting
**fixed-point-freely** (no nonzero vector is fixed by a nontrivial element) on an `𝔽_p`-space `V`
of dimension `1` or `2` is **cyclic**, with `|E| ∣ |V| - 1`.  Forgetful form of the dichotomy
`isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two` (`p − 1` divides `|V| − 1` in both dims). -/
theorem isCyclic_and_card_dvd_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two hodd ρ hfpf hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  have hsub_dvd : (p - 1 : ℕ) ∣ p ^ 2 - 1 := by
    have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    refine ⟨k + 2, ?_⟩
    have hsq : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    rw [hsq, Nat.add_sub_cancel, Nat.add_sub_cancel]
  rcases hdim with hd1 | hd2
  · have hcardV : Nat.card V = p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd1, pow_one, Nat.card_eq_fintype_card,
        ZMod.card]
    rw [hcardV]
    rcases hdvd with h1 | ⟨hd2, -, -⟩
    · exact h1
    · rw [hd1] at hd2; omega
  · have hcardV : Nat.card V = p ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
    rw [hcardV]
    rcases hdvd with h1 | ⟨-, -, hsq⟩
    · exact h1.trans hsub_dvd
    · exact hsq

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form).**  A finite odd-order group
`E` (`p ∤ |E|`) acting **fixed-point-freely** on an elementary abelian `p`-group `M` — encoded by
a `ZMod p`-module structure on `Additive M` — of `𝔽_p`-dimension `1` or `2` is **cyclic**, with
`|E| ∣ |M| - 1`.

This lifts `isCyclic_and_card_dvd_of_fpf_dim_le_two` from an abstract `Representation` to a
`MulDistribMulAction` (via `Representation.ofDistribMulAction`), which is the form that a
conjugation action of `E` on an elementary abelian subgroup supplies. -/
theorem isCyclic_and_card_dvd_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The fixed-point-free hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    -- `e • v = Additive.ofMul (e • v.toMul)` definitionally; pass to the multiplicative action.
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  exact ⟨hcyc, by rwa [Nat.card_congr (Additive.toMul (α := M))] at hdvd⟩

/-- **(12.12) rep-theory bridge (conjugation form).**  Let a finite group `E` normalize an
elementary abelian `p`-subgroup `T` of order `p` or `p²` of `G`, with `|E|` odd and coprime to `p`,
and let `E` act **fixed-point-freely on `T` by conjugation** (no nontrivial element of `T` is fixed
by a nontrivial element of `E`).  Then `E` is **cyclic** and `|E|` divides `p - 1` or `p² - 1`.

This is the `§8`-free structural core of Peterfalvi (12.12): there `T = Ω₁(Z(O_p(H)))` is the
rank `≤ 2` elementary abelian subgroup and `E` the Frobenius complement of `L`, acting FPF on `T`
by (12.10).  The `p + 1` refinement of (12.12) is separate (it consumes (12.9)/(12.11)). -/
theorem isCyclic_and_card_dvd_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p ^ 2 - 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpf' : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_of_fpf_mulDistribMulAction hodd hp_ndvd hdim hfpf'
  refine ⟨hcyc, ?_⟩
  rcases hT_card with h | h
  · exact Or.inl (by rwa [h] at hdvd)
  · exact Or.inr (by rwa [h] at hdvd)

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form), `p ± 1` refinement.**
As in `isCyclic_and_card_dvd_of_fpf_mulDistribMulAction`, but with the **non-scalar** input in
the rank-two case — no nontrivial `e : E` acts on `M` as a uniform power `m ↦ m ^ n` — which
upgrades the rank-two branch to `|E| ∣ p + 1` (Singer,
`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`); the rank-one and reducible
branches give `|E| ∣ p − 1` outright (dichotomy core,
`isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two`). -/
theorem isCyclic_and_card_dvd_sub_or_add_one_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1)
    (hnonscalar : Module.finrank (ZMod p) (Additive M) = 2 →
      ∀ e : E, (∃ n : ℕ, ∀ m : M, e • m = m ^ n) → e = 1) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The FPF hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  rcases hdvd with h1 | ⟨hd2, hirr, -⟩
  · exact Or.inl h1
  · -- Irreducible rank-two branch: supply the non-scalar input and apply Singer.
    have hfaith :
        Function.Injective (Representation.ofDistribMulAction (ZMod p) E (Additive M)) := by
      intro a b hab
      by_contra hne
      have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
      haveI : Nontrivial (Additive M) :=
        Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [hd2])
      obtain ⟨v, hv⟩ := exists_ne (0 : Additive M)
      refine hv (hfpf' (b⁻¹ * a) hba v ?_)
      rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hns : ∀ e : E, (∃ n : ℕ, ∀ v : Additive M,
        (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = n • v) → e = 1 := by
      rintro e ⟨n, hn⟩
      refine hnonscalar hd2 e ⟨n, fun m => ?_⟩
      have h1 := hn (Additive.ofMul m)
      rw [Representation.ofDistribMulAction_apply_apply] at h1
      have := congrArg Additive.toMul h1
      rw [show Additive.toMul (e • Additive.ofMul m) = e • m from rfl] at this
      simpa using this
    obtain ⟨-, hp1⟩ :=
      isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar hodd
        (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfaith hirr hd2 hp_ndvd hns
    exact Or.inr hp1

/-- **(12.12) rep-theory bridge (conjugation form), `p ± 1` refinement.**  As in
`isCyclic_and_card_dvd_of_fpf_conj_elemAbelian`, but with the **non-scalar** input — no
nontrivial `e ∈ E` conjugates every `t ∈ T` to the same power `t^n` — which upgrades the
`|T| = p²` branch to `|E| ∣ p + 1` (Singer,
`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`); the reducible/`|T| = p`
branches give `|E| ∣ p − 1` outright (dichotomy core). -/
theorem isCyclic_and_card_dvd_sub_or_add_one_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1)
    (hnonscalar : Nat.card ↥T = p ^ 2 →
      ∀ e : G, e ∈ E → (∃ n : ℕ, ∀ t : G, t ∈ T → e * t * e⁻¹ = t ^ n) → e = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p + 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpfM : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  -- The conjugation non-scalar hypothesis, transported to the `MulDistribMulAction` form.
  have hnsM : Module.finrank (ZMod p) (Additive ↥T) = 2 →
      ∀ ε : ↥E, (∃ n : ℕ, ∀ τ : ↥T, ε • τ = τ ^ n) → ε = 1 := by
    rintro hd2 ε ⟨n, hn⟩
    have hcardT : Nat.card ↥T = p ^ 2 := by rw [← hcard_pow, hd2]
    refine Subtype.ext (hnonscalar hcardT (ε : G) ε.2 ⟨n, fun t ht => ?_⟩)
    have hcoe := congrArg Subtype.val (hn ⟨t, ht⟩)
    rw [hsmul_coe] at hcoe
    simpa using hcoe
  exact isCyclic_and_card_dvd_sub_or_add_one_of_fpf_mulDistribMulAction hodd hp_ndvd hdim
    hfpfM hnsM

/-- **Peterfalvi (12.12), the `p + 1` refinement**: if the witness Frobenius complement's order
`e = |E|` divides `p² − 1`, then it divides `p − 1` or `p + 1`.

Peterfalvi's argument (the second half of the (12.12) proof): `E` is cyclic acting on
`T = Ω₁(P₀)` of order `p²`; identifying `T ⋊ E ↪ 𝔽_{p²} ⋊ 𝔽_{p²}^*` (Schur, as in (9.7.b)), the
subgroup `A ≤ E` of order `gcd(e, p−1)` lands in `𝔽_p^* `, so it normalizes every order-`p`
subgroup of `T` — in particular `⟨x⟩` for the (12.9) witness `x ∈ T`.  Then `A ⊆ N_G(⟨x⟩) ⊆ M`
by (12.9), so `A ⊆ M ∩ L ⊆ H` by (12.11), while `A ≤ E` meets `H` trivially — `A = 1`.  Hence
`gcd(e, p−1) = 1` and `e ∣ p + 1`.

**Assembly** (proven): instead of the Singer-cyclic identification, the rep-theory core
`isCyclic_and_card_dvd_sub_or_add_one_of_fpf_conj_elemAbelian` reduces the dichotomy to the
**nonscalar** hypothesis — no `e ∈ E` acts as a power map `t ↦ tⁿ` on a `T` of order `p²` —
which is exactly Peterfalvi's `A = 1` argument, elementwise: a scalar-acting `e` normalizes
every subgroup of `T`; the bookkeeping `|T| = p²` forces `T = Ω₁(P₀) ∋ x` (both are elementary
abelian sandwiched in the rank-`2` abelian `P₀`, so `T ⊆ Ω₁(P₀)` with `|Ω₁(P₀)| ≤ p² = |T|`),
so `e ∈ N_G(⟨x⟩) ⊆ M` by (12.9), hence `e ∈ M ∩ L ⊆ H = L_F` by (12.11)
(`intersection_le_kernel`), and the Frobenius disjointness `H ∩ E = 1` gives `e = 1`. -/
theorem witness_complement_dvd_p_sub_or_add_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L)
    {T : Subgroup G} (hTelem : T.IsElementaryAbelian ctr.p) (hTP0 : T ≤ ctr.P0) (hTne : T ≠ ⊥)
    (hEnorm : frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G))
    (hfpf : ∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
      ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    Nat.card ↥frob.complement ∣ ctr.p - 1 ∨ Nat.card ↥frob.complement ∣ ctr.p + 1 := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hEcard : Nat.card ↥(frob.complement.map data.L.subtype) = Nat.card ↥frob.complement :=
    Subgroup.card_map_of_injective (K := frob.complement) data.L.subtype_injective
  -- `|T| ∈ {p, p²}` from `T ≤ P₀` of rank `2`.
  have hTcard : Nat.card ↥T = ctr.p ∨ Nat.card ↥T = ctr.p ^ 2 :=
    OddOrder.GroupTheory.card_eq_prime_or_sq_of_isElementaryAbelian_le hTelem hTP0
      (counterexample_P0_K_structure hG ctr).2.le hTne
  -- Odd order of the realized complement `E' = E.map L.subtype`.
  have hodd : Odd (Nat.card ↥(frob.complement.map data.L.subtype)) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- `T ≤ H` through `P₀ ≤ L_F` (12.10).
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall data.L := frob.typeI.typeF.H_eq
  have hTH : T ≤ frob.typeI.typeF.H := by
    refine hTP0.trans ?_
    rw [hHeq]
    exact witness_P0_le_kernel hG data
  -- `p ∤ |E'|`: Frobenius kernel/complement coprimality with `p ∣ |T| ∣ |H|`.
  have hp_ndvd : ¬ ctr.p ∣ Nat.card ↥(frob.complement.map data.L.subtype) := by
    have hpT : ctr.p ∣ Nat.card ↥T := by
      rcases hTcard with h | h
      · rw [h]
      · rw [h]; exact dvd_pow_self ctr.p two_ne_zero
    have hcopLL : Nat.Coprime (Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L))
        (Nat.card ↥frob.complement) := frob.frobenius.coprime_card_kernel_complement
    have hpHL : ctr.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe frob.typeI.typeF.H_le).toEquiv]
      exact hpT.trans (Subgroup.card_dvd_of_le hTH)
    rw [hEcard]
    intro hpE
    exact ctr.p_prime.not_dvd_one (hcopLL ▸ Nat.dvd_gcd hpHL hpE)
  -- The **nonscalar** hypothesis — Peterfalvi's (12.11) `A = 1` argument, elementwise.
  have hnonscalar : Nat.card ↥T = ctr.p ^ 2 →
      ∀ e : G, e ∈ frob.complement.map data.L.subtype →
        (∃ n : ℕ, ∀ t : G, t ∈ T → e * t * e⁻¹ = t ^ n) → e = 1 := by
    intro hT2 e heE hsc
    obtain ⟨n, hn⟩ := hsc
    -- Bookkeeping: `|T| = p²` forces `T = Ω₁(P₀)`, so the (12.9) witness `x` lies in `T`.
    obtain ⟨hP0ab, hP0rank⟩ := counterexample_P0_K_structure hG ctr
    have hP0comm : ∀ y ∈ ctr.P0, ∀ z ∈ ctr.P0, y * z = z * y := fun y hy z hz =>
      congrArg Subtype.val (hP0ab.is_comm.comm (⟨y, hy⟩ : ↥ctr.P0) ⟨z, hz⟩)
    have hxOm : data.x ∈ OddOrder.GroupTheory.omega1OfAbelian G ctr.P0 ctr.p hP0comm :=
      ⟨data.x_mem_P0, data.x_mem_omega1⟩
    have hTOm : T ≤ OddOrder.GroupTheory.omega1OfAbelian G ctr.P0 ctr.p hP0comm := fun t ht =>
      ⟨hTP0 ht, by simpa using congrArg Subtype.val (hTelem.2 (⟨t, ht⟩ : ↥T))⟩
    have hOmne : OddOrder.GroupTheory.omega1OfAbelian G ctr.P0 ctr.p hP0comm ≠ ⊥ := fun hbot =>
      data.x_ne_one (Subgroup.mem_bot.mp (hbot ▸ hxOm))
    have hOmcard := OddOrder.GroupTheory.card_eq_prime_or_sq_of_isElementaryAbelian_le
      OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      OddOrder.GroupTheory.omega1OfAbelian_le hP0rank.le hOmne
    have hTeq : T = OddOrder.GroupTheory.omega1OfAbelian G ctr.P0 ctr.p hP0comm := by
      refine Subgroup.eq_of_le_of_card_ge hTOm ?_
      rw [hT2]
      rcases hOmcard with h | h
      · rw [h]; exact Nat.le_self_pow two_ne_zero ctr.p
      · rw [h]
    have hxT : data.x ∈ T := by rw [hTeq]; exact hxOm
    -- `orderOf x = p`; the scalar exponent `n` is prime to `p` (else conjugation kills `x`).
    have hordx : orderOf data.x = ctr.p := orderOf_eq_prime data.x_mem_omega1 data.x_ne_one
    have hexn : e * data.x * e⁻¹ = data.x ^ n := hn data.x hxT
    have hxnne : data.x ^ n ≠ 1 := fun h1 => by
      have : e * data.x * e⁻¹ = 1 := by rw [hexn, h1]
      exact data.x_ne_one (by
        calc data.x = e⁻¹ * (e * data.x * e⁻¹) * e := by group
          _ = 1 := by rw [this]; group)
    have hordxn : orderOf (data.x ^ n) = ctr.p := by
      have hdvd : orderOf (data.x ^ n) ∣ ctr.p :=
        orderOf_dvd_iff_pow_eq_one.mpr (by
          rw [← pow_mul, mul_comm n ctr.p, pow_mul, data.x_mem_omega1, one_pow])
      rcases (Nat.Prime.eq_one_or_self_of_dvd ctr.p_prime _ hdvd) with h1 | hp
      · exact absurd (orderOf_eq_one_iff.mp h1) hxnne
      · exact hp
    -- `zpowers (xⁿ) = zpowers x` (both have order `p`), so `e` normalizes `⟨x⟩`.
    have hzp : Subgroup.zpowers (data.x ^ n) = Subgroup.zpowers data.x := by
      refine Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers data.x) n)) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hordx, hordxn]
    have heN : e ∈ Subgroup.normalizer
        ((Subgroup.closure ({data.x} : Set G) : Subgroup G) : Set G) := by
      rw [← Subgroup.zpowers_eq_closure, Subgroup.mem_set_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hh)
        refine SetLike.mem_coe.mpr ?_
        rw [← conj_zpow, hexn]
        exact hzp ▸ Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      · intro hh
        have hh' : e * h * e⁻¹ ∈ Subgroup.zpowers (data.x ^ n) := by
          rw [hzp]; exact SetLike.mem_coe.mp hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh'
        rw [← hexn, conj_zpow] at hk
        exact SetLike.mem_coe.mpr (Subgroup.mem_zpowers_iff.mpr
          ⟨k, mul_left_cancel (mul_right_cancel hk)⟩)
    -- (12.9): `e ∈ N_G(⟨x⟩) ⊆ M`; with `e ∈ L`, (12.11) places `e ∈ H = L_F`.
    have heM : e ∈ ctr.M := data.normalizer_closure_x_le_M heN
    have heL : e ∈ data.L := Subgroup.map_subtype_le _ heE
    have heH : e ∈ frob.typeI.typeF.H := by
      rw [hHeq]
      exact intersection_le_kernel hG data ⟨heM, heL⟩
    -- Frobenius disjointness: `e ∈ E ∩ H = 1`.
    obtain ⟨a, haC, rfl⟩ := heE
    have haH : a ∈ frob.typeI.typeF.H.subgroupOf data.L :=
      Subgroup.mem_subgroupOf.mpr heH
    have ha1 : a = 1 :=
      Subgroup.disjoint_def.mp frob.frobenius.isComplement.disjoint haH haC
    rw [ha1, map_one]
  -- The proven rep-theory dichotomy, with the scalar case excluded.
  obtain ⟨-, hdvd⟩ := isCyclic_and_card_dvd_sub_or_add_one_of_fpf_conj_elemAbelian
    hTelem hEnorm hodd hp_ndvd hTcard hfpf hnonscalar
  rwa [hEcard] at hdvd

/-- **Peterfalvi (12.12), structural input from (12.9)/(12.10)/(12.11)** (pinned sorried §8/§9
obligation, hub 9003 Cluster A).  For the (12.9) witness `L` (type-I Frobenius, kernel `H = L_F`),
with `E := frob.complement.map L.subtype` the Frobenius complement realized in `G`, there is a
subgroup `T ≤ G` — Peterfalvi's `T = Ω₁Z(O_p(H))` — that is
* **elementary abelian** of order `p` or `p²` (`P₀` is abelian of rank `2` by (12.9), so `Ω₁Z(P)`
  has order `p` or `p²`);
* **normalized by `E`** (`E` normalizes `O_p(H)`, its center, and the `Ω₁`);
* on which `E` acts **fixed-point-freely by conjugation** (Peterfalvi (12.10): as `L` is Frobenius
  with kernel `H`, the complement `E` fixes no nonidentity element of `H`, a fortiori none of
  `T ⊆ H`),

and, encoding the `p+1` refinement of (12.12) (the (12.11) step `A ⊆ M ⟹ A = 1` for `A ≤ E` of
order dividing `p-1`), if `|E|` divides `p² - 1` then in fact `|E|` divides `p - 1` or `p + 1`.  We
also record `T ≤ H` (`Ω₁Z(O_p(H)) ⊆ H`), used to see `p ∣ |H|`.

**Assembly** (proven, modulo the `p+1` refinement pin): `P := O_p(H)` contains `P₀` (nilpotent
`H`), and `T := Ω₁(Z(P))` is elementary abelian (`omega1OfAbelian`).  The elided order bound is
the (12.9) control: `T ⊆ Z(P) ⊆ C_G(x) ≤ N_G(⟨x⟩) ≤ M` and `T` centralizes `P₀ ≤ P`, so the
abelian `p`-subgroup `T ⊔ P₀ ≤ M` lies in the full `p`-part `P₀`, whence `T ⊆ P₀` (abelian of
rank `2`) and `|T| ∈ {p, p²}` (`card_eq_prime_or_sq_of_isElementaryAbelian_le`).  `E` normalizes
`T` through the characteristic chain `N(H) ≤ N(O_p(H)) ≤ N(Z(O_p(H))) ≤ N(Ω₁(...))`, and acts
fixed-point-freely on `T ⊆ H` by the Frobenius structure.  The `p+1` refinement is the pinned
`witness_complement_dvd_p_sub_or_add_one`. -/
theorem exists_center_omega1_elemAbelian_fpf_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    ∃ T : Subgroup G, IsElementaryAbelian ctr.p ↥T ∧
      (frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G)) ∧
      (Nat.card ↥T = ctr.p ∨ Nat.card ↥T = ctr.p ^ 2) ∧
      T ≤ frob.typeI.typeF.H ∧
      (∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
        ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) ∧
      (Nat.card ↥frob.complement ∣ ctr.p ^ 2 - 1 →
        Nat.card ↥frob.complement ∣ ctr.p - 1 ∨ Nat.card ↥frob.complement ∣ ctr.p + 1) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `H = L_F` is nilpotent and contains `P₀`; set `P := O_p(H) ⊇ P₀`.
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall data.L := frob.typeI.typeF.H_eq
  haveI hHnilp : Group.IsNilpotent ↥frob.typeI.typeF.H := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent data.L
  have hP0H : ctr.P0 ≤ frob.typeI.typeF.H := by
    rw [hHeq]; exact witness_P0_le_kernel hG data
  set P : Subgroup G := opiCoreInG ({ctr.p} : Set ℕ) frob.typeI.typeF.H with hPdef
  have hP0P : ctr.P0 ≤ P := pGroup_le_opiCoreInG_of_le_of_isNilpotent ctr.P0_pGroup hP0H
  have hPH : P ≤ frob.typeI.typeF.H := opiCoreInG_le _ _
  have hPp : IsPGroup ctr.p ↥P := isPGroup_opiCoreInG_singleton _
  -- `Z := Z(P)` in `G` (abelian), `T := Ω₁(Z)`.
  set Z : Subgroup G := (Subgroup.center ↥P).map P.subtype with hZdef
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_center_map_subtype_iff.mp hx).2 y
      (Subgroup.mem_center_map_subtype_iff.mp hy).1).symm
  set T : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G Z ctr.p hZcomm with hTdef
  have hTZ : T ≤ Z := OddOrder.GroupTheory.omega1OfAbelian_le
  have hZP : Z ≤ P := hZdef ▸ Subgroup.map_subtype_le _
  have hTH : T ≤ frob.typeI.typeF.H := hTZ.trans (hZP.trans hPH)
  have hTelem : T.IsElementaryAbelian ctr.p :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
  -- `T ≠ ⊥`: the nontrivial `p`-group `P` has nontrivial center, whose Cauchy `p`-element
  -- lies in `Ω₁(Z)`.
  have hP0ne : ctr.P0 ≠ ⊥ := fun h => ctr.P0_noncyclic (h ▸ inferInstance)
  have hPne : P ≠ ⊥ := fun h => hP0ne (le_bot_iff.mp (h ▸ hP0P))
  have hTne : T ≠ ⊥ := by
    haveI : Nontrivial ↥P := P.nontrivial_iff_ne_bot.mpr hPne
    haveI : Nontrivial (Subgroup.center ↥P) := hPp.center_nontrivial
    have hZne : Z ≠ ⊥ := by
      intro hbot
      obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥P)
      refine hz1 (Subtype.ext (Subtype.ext ?_))
      have hzZ : ((z : ↥P) : G) ∈ Z := hZdef ▸ ⟨z, z.2, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hzZ
      exact hzZ
    have hZp : IsPGroup ctr.p ↥Z := hPp.to_le hZP
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    have hkpos : k ≠ 0 := by
      rintro rfl
      exact hZne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    haveI : Fintype ↥Z := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥Z) ctr.p
      (by rw [← Nat.card_eq_fintype_card, hk]; exact dvd_pow_self _ hkpos)
    have hg_ord : orderOf (g : G) = ctr.p := by
      rw [← hg]; exact orderOf_injective Z.subtype Z.subtype_injective g
    have hgT : (g : G) ∈ T := ⟨g.2, by rw [← hg_ord]; exact pow_orderOf_eq_one _⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hgT
    rw [hgT, orderOf_one] at hg_ord
    exact ctr.p_prime.one_lt.ne' hg_ord.symm
  -- The (12.9) control: `T ⊆ Z(P) ⊆ C_G(x) ≤ M`, and `T` centralizes `P₀`, so the abelian
  -- `p`-subgroup `T ⊔ P₀ ≤ M` lies in the full `p`-part `P₀`; hence `T ⊆ P₀` of rank `2`.
  have hxP : data.x ∈ P := hP0P data.x_mem_P0
  have hTCx : T ≤ Subgroup.centralizer ({data.x} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_center_map_subtype_iff.mp (hTZ ht)).2 data.x hxP).symm
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hTM : T ≤ ctr.M := hTCx.trans hCM
  have hTcent : T ≤ Subgroup.centralizer (ctr.P0 : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_center_map_subtype_iff.mp (hTZ ht)).2 w (hP0P hw)
  have hTp : IsPGroup ctr.p ↥T := hPp.to_le (hTZ.trans hZP)
  have hsup_p : IsPGroup ctr.p ↥(T ⊔ ctr.P0) :=
    IsPGroup.to_sup_of_normal_right' hTp ctr.P0_pGroup
      (hTcent.trans (Subgroup.centralizer_le_normalizer _))
  have hsup_eq : T ⊔ ctr.P0 = ctr.P0 := by
    have hle_M : T ⊔ ctr.P0 ≤ ctr.M := sup_le hTM ctr.P0_le_M
    obtain ⟨m, hm⟩ := hsup_p.exists_card_eq
    have hdvd_M : (ctr.p : ℕ) ^ m ∣ Nat.card ↥ctr.M := by
      rw [← hm]; exact Subgroup.card_dvd_of_le hle_M
    have hMsplit : Nat.card ↥ctr.M = Nat.card ↥ctr.P0 * ctr.P0.relIndex ctr.M := by
      rw [Subgroup.relIndex, ← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv]
      exact ((ctr.P0.subgroupOf ctr.M).card_mul_index).symm
    have hcop : Nat.Coprime (ctr.p ^ m) (ctr.P0.relIndex ctr.M) :=
      Nat.Coprime.pow_left m
        (ctr.p_prime.coprime_iff_not_dvd.mpr ctr.P0_sylow)
    have hdvd_P0 : (ctr.p : ℕ) ^ m ∣ Nat.card ↥ctr.P0 :=
      hcop.dvd_of_dvd_mul_right (hMsplit ▸ hdvd_M)
    refine (Subgroup.eq_of_le_of_card_ge le_sup_right ?_).symm
    rw [hm]
    exact Nat.le_of_dvd Nat.card_pos hdvd_P0
  have hTP0 : T ≤ ctr.P0 := hsup_eq ▸ le_sup_left
  have hTcard : Nat.card ↥T = ctr.p ∨ Nat.card ↥T = ctr.p ^ 2 :=
    OddOrder.GroupTheory.card_eq_prime_or_sq_of_isElementaryAbelian_le hTelem hTP0
      (counterexample_P0_K_structure hG ctr).2.le hTne
  -- `E` normalizes `T`: through `N(H) ≤ N(O_p(H)) ≤ N(Z(O_p(H))) ≤ N(Ω₁(Z))`.
  have hEnorm : frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G) := by
    have hchain : Subgroup.normalizer ((frob.typeI.typeF.H : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T : Subgroup G) : Set G) := by
      intro g hg
      have hgP : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
        le_normalizer_opiCoreInG_of_le_normalizer ({ctr.p} : Set ℕ) le_rfl hg
      have hgZ : g ∈ Subgroup.normalizer ((Z : Subgroup G) : Set G) :=
        hZdef ▸ Subgroup.mem_normalizer_center_map_of_mem_normalizer hgP
      exact OddOrder.GroupTheory.mem_normalizer_omega1OfAbelian hgZ
    refine le_trans ?_ hchain
    intro e he
    obtain ⟨a, -, rfl⟩ := he
    have hLN : data.L ≤ Subgroup.normalizer ((frob.typeI.typeF.H : Subgroup G) : Set G) := by
      rw [hHeq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L
    exact hLN a.2
  -- Fixed-point-freeness on `T ⊆ H` from the Frobenius structure of `L`.
  have hfpf : ∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
      ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1 := by
    intro e he hene t ht hconj
    obtain ⟨a, haC, rfl⟩ := he
    have htH : t ∈ frob.typeI.typeF.H := hTH ht
    have htL : t ∈ data.L := frob.typeI.typeF.H_le htH
    by_contra htne
    have hane : a ≠ 1 := fun h => hene (by rw [h]; rfl)
    exact frob.frobenius.conj_frobenius a haC hane ⟨t, htL⟩
      (Subgroup.mem_subgroupOf.mpr htH) (fun h => htne (congrArg Subtype.val h))
      (Subtype.ext hconj)
  exact ⟨T, hTelem, hEnorm, hTcard, hTH, hfpf, fun _ =>
    witness_complement_dvd_p_sub_or_add_one hG data frob hTelem hTP0 hTne hEnorm hfpf⟩

/-- **Peterfalvi (12.12)**: the Frobenius complement `E` in the (12.9) witness subgroup `L` is
cyclic, with order `e = |E|` dividing `p - 1` or `p + 1`.

**Assembly** (`sorry`-free modulo the (12.9)/(12.10)/(12.11) structural package): from
`exists_center_omega1_elemAbelian_fpf_of_witness` we obtain `T = Ω₁Z(O_p(H))` — elementary abelian
of order `p` or `p²`, normalized by `E` (realized in `G` as `E' = frob.complement.map L.subtype`),
with `E'` acting fixed-point-freely on `T` by conjugation.  The proven rep-theory core
`isCyclic_and_card_dvd_of_fpf_conj_elemAbelian` then gives `IsCyclic E' ∧ (|E'| ∣ p-1 ∨ |E'| ∣ p²-1)`
(the `§8`-free Singer/Case-A+B mechanism).  Transporting cyclicity back along `L.subtype` (`E ≅ E'`)
and applying the packaged `p+1` refinement to the `p²-1` branch yields the (12.12) conclusion. -/
theorem complement_cyclic_order_dvd [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- The Frobenius complement, realized as a subgroup `E'` of the ambient `G`.
  set E' : Subgroup G := frob.complement.map data.L.subtype with hE'
  -- `E ≅ E'` (injective image), so cardinalities agree.
  have hEcard : Nat.card ↥E' = Nat.card ↥frob.complement :=
    Subgroup.card_map_of_injective (K := frob.complement) data.L.subtype_injective
  -- The (12.9)/(12.10)/(12.11) structural package for the witness complement.
  obtain ⟨T, hTelem, hEnorm, hTcard, hTleH, hfpf, hrefine⟩ :=
    exists_center_omega1_elemAbelian_fpf_of_witness hG data frob
  -- Odd order of `E'` (a subgroup of the odd-order `G`).
  have hodd : Odd (Nat.card ↥E') :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E')
  -- `p ∤ |E'|`: `E'` is a Frobenius complement, coprime to the kernel `H ⊇ T` which has order
  -- divisible by `p` (`|T| = p` or `p²`).  Concretely `|T| ∣ |kernel|` and `p ∣ |T|`, while
  -- `Coprime |kernel| |complement|`, so `p ∤ |E'|`.
  have hp_ndvd : ¬ ctr.p ∣ Nat.card ↥E' := by
    -- `p ∣ |T|` (order `p` or `p²`).
    have hpT : ctr.p ∣ Nat.card ↥T := by
      rcases hTcard with h | h
      · rw [h]
      · rw [h]; exact dvd_pow_self ctr.p (by norm_num)
    -- `T ≤ H` (`T = Ω₁Z(O_p(H)) ⊆ H`); realize via the FPF hypothesis: `T`'s elements are moved by
    -- every nontrivial element of `E'`, and `E'`, `H` are Frobenius-coprime.  We use the abstract
    -- coprimality of the Frobenius pair on `↥L`.
    have hcopLL : Nat.Coprime (Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L))
        (Nat.card ↥frob.complement) := frob.frobenius.coprime_card_kernel_complement
    -- It suffices that `p ∣ |H|` and `Coprime |H| |E'|` (via `|E'| = |E|`), then `p ∤ |E'|`.
    -- `|H_L| = |H|` where `H_L = H.subgroupOf L`.
    have hHcard : Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L)
        = Nat.card ↥frob.typeI.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe frob.typeI.typeF.H_le).toEquiv
    -- `p ∣ |H|`: `T ≤ H` (`hTleH`, from the package), and `p ∣ |T| ∣ |H|`.
    have hpH : ctr.p ∣ Nat.card ↥frob.typeI.typeF.H :=
      hpT.trans (Subgroup.card_dvd_of_le hTleH)
    have hpHL : ctr.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L) := by
      rw [hHcard]; exact hpH
    rw [hEcard]
    intro hpE
    exact ctr.p_prime.not_dvd_one (hcopLL ▸ Nat.dvd_gcd hpHL hpE)
  -- The proven rep-theory core: `E'` cyclic and `|E'| ∣ p-1 ∨ |E'| ∣ p²-1`.
  obtain ⟨hcycE', hdvdE'⟩ :=
    isCyclic_and_card_dvd_of_fpf_conj_elemAbelian hTelem hEnorm hodd (hEcard ▸ hp_ndvd) hTcard hfpf
  -- Transport cyclicity `E' ≅ E` back to `E`.
  have hcyc : IsCyclic ↥frob.complement :=
    isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective frob.complement data.L.subtype
        data.L.subtype_injective).symm.surjective
  refine ⟨hcyc, ?_⟩
  -- Rewrite `|E'| = |E|` in the divisibility and apply the `p+1` refinement.
  rw [hEcard] at hdvdE'
  rcases hdvdE' with h | h
  · exact Or.inl h
  · exact hrefine h

/-- **Peterfalvi (12.12) → (12.16) numeric input: `2e ≤ p + 1`** ("Also `2e ≤ p+1` by (12.12)").
The witness complement order `e = |E|` is odd (a subgroup of the odd-order `G`) and divides
`p − 1` or `p + 1` by (12.12); an odd divisor of the even number `p ∓ 1` divides its half, so
`2e ≤ p ∓ 1 ≤ p + 1`.  This is the `h2e` field of `CounterexampleDadeData`, in `ℕ` form. -/
theorem two_mul_card_complement_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    2 * Nat.card ↥frob.complement ≤ ctr.p + 1 := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨-, hdvd⟩ := complement_cyclic_order_dvd hG data frob
  -- `e = |E|` is odd.
  have hodd : Odd (Nat.card ↥frob.complement) :=
    hG.odd.of_dvd_nat ((Subgroup.card_subgroup_dvd_card frob.complement).trans
      (Subgroup.card_subgroup_dvd_card data.L))
  -- `p` is odd and `≥ 3` (`p ∣ |G|` odd).
  have hpG : ctr.p ∣ Nat.card G := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at this
    exact (h1.trans (Subgroup.index_dvd_card _)).trans
      (Subgroup.card_subgroup_dvd_card ctr.M)
  have hpodd : Odd ctr.p := hG.odd.of_dvd_nat hpG
  have hp3 : 3 ≤ ctr.p := by
    have h2 := ctr.p_prime.two_le
    have hne : ctr.p ≠ 2 := fun h => by
      rw [h] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    omega
  -- An odd divisor of an even number divides its half.
  have he_mod : Nat.card ↥frob.complement % 2 = 1 := Nat.odd_iff.mp hodd
  have key : ∀ m : ℕ, 0 < m → Even m → Nat.card ↥frob.complement ∣ m →
      2 * Nat.card ↥frob.complement ≤ m := by
    intro m hm hme hdvd'
    obtain ⟨k, hk⟩ := hme
    have hm2k : m = 2 * k := by omega
    have hcop : Nat.Coprime (Nat.card ↥frob.complement) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (fun h => by omega)).symm
    have hdvd_k : Nat.card ↥frob.complement ∣ k :=
      Nat.Coprime.dvd_of_dvd_mul_left hcop (hm2k ▸ hdvd')
    have hkpos : 0 < k := by omega
    have := Nat.le_of_dvd hkpos hdvd_k
    omega
  rcases hdvd with h | h
  · -- `e ∣ p − 1`: `2e ≤ p − 1 ≤ p + 1`.
    have := key (ctr.p - 1) (by omega) (Nat.Odd.sub_odd hpodd odd_one) h
    omega
  · -- `e ∣ p + 1`: `2e ≤ p + 1`.
    exact key (ctr.p + 1) (by omega) (Odd.add_one hpodd) h

end OddOrder.Peterfalvi.S14

