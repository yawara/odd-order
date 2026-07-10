/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_TypeIICrossIsometryPair
import OddOrder.Peterfalvi.S14_MaximalI.WitnessSylowCyclic

/-!
# S12_Noncoherence — the unconditional Peterfalvi (10.8)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 10, Theorem (10.8), pp. 59–60.

The unconditional form of `S12.S_not_coherent_of_partner`: the type-II partner and its
supply facts are assembled here from the `M`-seeded order-free pair
(`exists_section16MaximalPairCore_around`, issue 1020 Phase 1a), the reconciled
`TypePData` (`exists_reconciled_conj_typePData_S`), the `K = W₂` identification
(`typePData_Msigma_inf_centralizer_W1_eq_W2`), Peterfalvi (8.11)
(`hall_maxNilpotentNormalHall_and_mainSubgroup`), (8.16)/(8.6.a)
(`typeII_centralizer_le_of_mem_mainSubgroup`), and the general (10.7)
(`typeII_HU_frobenius_of_coherent'`).  This leaf sits **below** the pair machinery, so it can
consume the honest (10.7) without the import cycle that gated the `S12_MaximalBasic` original
(issue 1020); every input is axiom-clean.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.8), unconditional**: under Hypothesis (10.1), the character family `𝒮`
is not coherent — with the type-II partner supply assembled internally (issue 1020 Phase 3).
Every ingredient is axiom-clean; this is the honest heir of `S_not_coherent`. -/
theorem S_not_coherent_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  rintro ⟨hcoh⟩
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  let coh : CoherentHypothesis hyp params := ⟨hcoh⟩
  -- the `M`-seeded order-free pair and the reconciled partner datum
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M := hyp.bgTypeP hG
  have hnotP2 := not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt
  obtain ⟨mp₀, hT₀, hK₀⟩ := exists_section16MaximalPairCore_around hG hyp.maximal hP hnotP2
    hyp.typeP.W1_le (typePData_W1_isHallSubgroup_kappa hG hyp.maximal hP hyp.typeP)
  obtain ⟨dII₀⟩ := section16_S_isTypeII hG mp₀
  obtain ⟨mp, u, dataS, hT, hKstar, huS, hSW1, hSW2, hH, hU⟩ :=
    exists_reconciled_conj_typePData_S hG hyp mp₀.S_maximal
      (section16_S_isTypeII hG mp₀) dII₀.typeP
  have hSmax := mp.S_maximal
  have hSII : IsTypeII mp.S := section16_S_isTypeII hG mp
  -- `K = W₂(M)`: the pair-linkage card identities
  have hKW2 : mp.K = hyp.typeP.W2 := by
    rw [mp.K_eq, hT, hKstar]
    exact typePData_Msigma_inf_centralizer_W1_eq_W2 hG hyp.maximal hyp.typeP
  have hKcard : Nat.card ↥mp.K = hyp.w2 := by rw [hKW2]; rfl
  have hKstarcard : Nat.card ↥mp.Kstar = hyp.w1 := by rw [hKstar]; rfl
  -- supply: the derived index of the partner is `w₂`
  have hSidx : ((derivedInG mp.S).subgroupOf mp.S).index = hyp.w2 := by
    rw [← dataS.card_W1_eq_derived_index, hSW1, hKcard]
  have hW1card : Nat.card ↥dataS.W1 = hyp.w2 := by rw [hSW1, hKcard]
  -- supply: `|U| ≥ 7` (the odd-order forcing on the reconciled datum)
  have hUcard : Nat.card ↥dataS.U = Nat.card ↥dII₀.typeP.U := by
    rw [hU, pointwise_mulAut_smul_eq_map]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective dII₀.typeP.U
      (MulAut.conj u).toMonoidHom (MulAut.conj u).injective).toEquiv).symm
  have hUne : dataS.U ≠ ⊥ := by
    intro hbot
    have h1 : 1 < Nat.card ↥dII₀.typeP.U :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr dII₀.common.1
    rw [← hUcard, hbot, Subgroup.card_bot] at h1
    omega
  have hU7 : 7 ≤ Nat.card ↥dataS.U := by
    have hUlt : 1 < Nat.card ↥dataS.U := (Subgroup.one_lt_card_iff_ne_bot _).mpr hUne
    have hfrobUW := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius dataS hUne
    have hmod := hfrobUW.card_kernel_modEq_one
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hmod
    have hdvd : Nat.card ↥dataS.W1 ∣ Nat.card ↥dataS.U - 1 :=
      (Nat.modEq_iff_dvd' hUlt.le).mp hmod.symm
    have hUodd : Odd (Nat.card ↥dataS.U) :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dataS.U)
    have hW1odd : Odd (Nat.card ↥dataS.W1) :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dataS.W1)
    have hge := OddOrder.Peterfalvi.S08.two_mul_add_one_le_of_odd_dvd hW1odd hUodd hdvd hUlt
    rw [hW1card] at hge
    have hw2prime : (hyp.w2).Prime := hyp.w2_prime hG
    have hw2odd : Odd hyp.w2 := hW1card ▸ hW1odd
    have hw2ge : 3 ≤ hyp.w2 := by
      have h2 := hw2prime.two_le
      obtain ⟨k, hk⟩ := hw2odd; omega
    omega
  -- supply: `|W₁(S)|` prime, coprime to `|[S,S]|`
  have hprime : (Nat.card ↥dataS.W1).Prime := by
    rw [hW1card]; exact hyp.w2_prime hG
  have hcop := typePData_W1_hall_coprime hG hSmax mp.S_typeP dataS
  -- supply: (8.11) — `H = S_F` is a Hall subgroup of `G`
  have hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      (Nat.card ↥dataS.H).primeFactors dataS.H := by
    have h := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hSmax
      (show HasPeterfalviType PeterfalviType.II mp.S from hSII)).1
    rw [dataS.H_eq]
    exact h
  -- supply: (8.16)/(8.6.a) — centralizers of `H#`-elements land in `S`
  have hcent : ∀ b ∈ dataS.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ mp.S := by
    intro b hb hb1
    refine OddOrder.Peterfalvi.S14.typeII_centralizer_le_of_mem_mainSubgroup hG hSmax hSII
      ?_ hb1
    show b ∈ mainSubgroup mp.S PeterfalviType.II
    have : mainSubgroup mp.S PeterfalviType.II = maxNilpotentNormalHall mp.S := rfl
    rw [this, ← dataS.H_eq]
    exact hb
  -- supply: the (10.7) Frobenius-kernel capture
  have hfrobcap : ∀ b ∈ dataS.H, b ≠ 1 → ∀ y ∈ derivedInG mp.S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ dataS.H := by
    have hfrob := typeII_HU_frobenius_of_coherent' hG coh
      (data := { maximal := hSmax
                 typeP := dataS
                 nontrivial := hSII.some.common.transfer dataS
                 type_alt := Or.inl hSII }) hSII
    intro b hb hb1 y hy hyc
    have hbS' : b ∈ derivedInG mp.S := dataS.H_le hb
    have hbmem : (⟨b, hbS'⟩ : ↥(derivedInG mp.S)) ∈ dataS.H.subgroupOf (derivedInG mp.S) :=
      Subgroup.mem_subgroupOf.mpr hb
    have hbne : (⟨b, hbS'⟩ : ↥(derivedInG mp.S)) ≠ 1 := by
      intro h; exact hb1 (congrArg Subtype.val h)
    have hyC : (⟨y, hy⟩ : ↥(derivedInG mp.S))
        ∈ Subgroup.centralizer ({(⟨b, hbS'⟩ : ↥(derivedInG mp.S))} : Set ↥(derivedInG mp.S)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc b rfl).symm
    have := hfrob.centralizer_kernel_le _ hbmem hbne hyC
    exact Subgroup.mem_subgroupOf.mp this
  -- supply: the pair-linkage card identities for `W₂` and `W`
  have hW2card : Nat.card ↥dataS.W2 = hyp.w1 := by rw [hSW2, hKstarcard]
  have hWcard : Nat.card ↥dataS.W = hyp.w1 * hyp.w2 := by
    have hinf : mp.K ⊓ mp.Kstar = ⊥ := by
      rw [← hSW1, ← hSW2]
      exact disjoint_iff.mp (typePData_disjoint_W1_W2 dataS)
    have hmul := card_mul_eq_of_disjoint_sup_le_isCyclic (W := mp.K ⊔ mp.Kstar)
      mp.Z_cyclic le_sup_left le_sup_right rfl hinf
    have hWKK : dataS.W = mp.K ⊔ mp.Kstar := by rw [dataS.W_eq, hSW1, hSW2]
    rw [hWKK, ← hmul, hKcard, hKstarcard, Nat.mul_comm]
  -- the partner-supplied estimate and the arithmetic contradiction
  have hw1odd : Odd hyp.w1 :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hw1gt : 1 < hyp.w1 :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hw1 : 3 ≤ hyp.w1 := by
    obtain ⟨k, hk⟩ := hw1odd; omega
  have hw2 : 1 ≤ hyp.w2 := Nat.card_pos
  have hMp : (2 * hyp.w1 + 1) * hyp.w2 ≤ Nat.card ↥(derivedInG M) := hyp.card_derived_ge hG
  obtain ⟨u', hu7', hbound⟩ := typeII_coherence_contradiction_estimate_of_partner hG coh dataS
    hSidx hU7 hprime hcop hHall hcent hfrobcap hW2card hWcard
  exact typeII_noncoherence_arithmetic hw1 hu7' hw2 hMp hbound

end OddOrder.Peterfalvi.S12
