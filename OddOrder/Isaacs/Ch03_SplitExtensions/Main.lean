/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.CrossedHomomorphism
import OddOrder.Isaacs.Ch03_SplitExtensions.PiSeparableSeries
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch03_SplitExtensions.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch03
open SemidirectProduct
open scoped Pointwise

section /- 3D: π-separable + Hall-Higman (pp. 89-95) -/
variable {G : Type*} [Group G]


/-! **Isaacs Lemma 3.18** の役割は本実装では subgroup / quotient 閉包 instance が果たす
(別 issue で追加予定). 現状は `isPiSeparable_of_solvable` で十分. -/

/-- **Isaacs Cor 3.19**: `G` 有限 solvable ⇒ 全 π について π-separable. instance 形.

戦略: `Nat.card G ≤ Nat.card (Fₙ) + k` の `k` についての強誘導. 各ステップで
`Fₙ < ⊤` なら `G/Fₙ` 非自明可解で `exists_oPiCore_ne_bot_or_oPi'Core_ne_bot` 適用,
`Fₙ < F_{n+1}` ⇒ `|Fₙ| < |F_{n+1}|` で measure 単調減少. -/
instance isPiSeparable_of_solvable (π : Set ℕ) (G : Type*) [Group G] [Finite G] [IsSolvable G] :
    IsPiSeparable π G where
  exists_top := by
    classical
    suffices h : ∀ (k : ℕ) (n : ℕ),
        Nat.card G ≤ Nat.card (piFittingSeries π G n) + k →
        ∃ m, piFittingSeries π G m = ⊤ from
      h (Nat.card G) 0 (by simp)
    intro k
    induction k with
    | zero =>
      intro n hk
      refine ⟨n, ?_⟩
      have hle : piFittingSeries π G n ≤ (⊤ : Subgroup G) := le_top
      apply Subgroup.eq_of_le_of_card_ge hle
      have hcardTop : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      omega
    | succ k ih =>
      intro n hk
      by_cases h_top : piFittingSeries π G n = ⊤
      · exact ⟨n, h_top⟩
      · have hFn_lt_top : piFittingSeries π G n < ⊤ := lt_of_le_of_ne le_top h_top
        haveI : Nontrivial (G ⧸ piFittingSeries π G n) := by
          rw [QuotientGroup.nontrivial_iff]
          exact ne_of_lt hFn_lt_top
        haveI : IsSolvable (G ⧸ piFittingSeries π G n) := inferInstance
        have hOplus : oPiCore π (G ⧸ piFittingSeries π G n) ⊔
            oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n) ≠ ⊥ := by
          rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot (G := G ⧸ piFittingSeries π G n) π with
            hπ | hπ'
          · intro h; exact hπ (le_bot_iff.mp (h ▸ le_sup_left))
          · intro h; exact hπ' (le_bot_iff.mp (h ▸ le_sup_right))
        have hFn_lt : piFittingSeries π G n < piFittingSeries π G (n + 1) :=
          (piFittingSeries_lt_succ_iff π n).mpr hOplus
        have hcard_lt : Nat.card (piFittingSeries π G n) <
            Nat.card (piFittingSeries π G (n + 1)) := by
          rcases lt_iff_le_and_ne.mp hFn_lt with ⟨hle, hne⟩
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) ?_
          intro hcard_eq
          exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm))
        apply ih (n + 1)
        omega

/-- A minimal normal subgroup of a finite π-separable group is either a π-group
or a π'-group. -/
private theorem minimal_normal_isPiGroup_or_isPiGroup_compl_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    {M : Subgroup G} (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    Subgroup.IsPiGroup π M ∨ Subgroup.IsPiGroup {p | p ∉ π} M := by
  haveI hM_normal : M.Normal := hM.1
  haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM.2.1
  haveI hM_piSep : IsPiSeparable π ↥M := normalSubgroup_isPiSeparable π G M
  let liftCore (ρ : Set ℕ) (hcore : oPiCore ρ ↥M ≠ ⊥) :
      Subgroup.IsPiGroup ρ M := by
    have hmap_ne_bot : (oPiCore ρ ↥M).map M.subtype ≠ ⊥ := by
      intro hmap
      exact hcore ((Subgroup.map_eq_bot_iff_of_injective
        (H := oPiCore ρ ↥M) M.subtype_injective).mp hmap)
    haveI hmap_normal : ((oPiCore ρ ↥M).map M.subtype).Normal := inferInstance
    have hmap_le_M : (oPiCore ρ ↥M).map M.subtype ≤ M := by
      simpa [M.range_subtype] using (oPiCore ρ ↥M).map_le_range M.subtype
    have hmap_eq_M : (oPiCore ρ ↥M).map M.subtype = M := by
      rcases hM.2.2 _ hmap_normal hmap_le_M with hbot | htop
      · exact absurd hbot hmap_ne_bot
      · exact htop
    have hcore_top : oPiCore ρ ↥M = ⊤ := by
      apply (Subgroup.map_subtype_inj (H := M)).mp
      rw [hmap_eq_M]
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    intro p hp
    have hpiTop : Subgroup.IsPiGroup ρ (⊤ : Subgroup ↥M) := by
      rw [← hcore_top]
      exact oPiCore.isPiGroup ρ
    rw [← Subgroup.card_top (G := ↥M)] at hp
    exact hpiTop p hp
  rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable
      (G := ↥M) π with hπ | hπ'
  · exact Or.inl (liftCore π hπ)
  · exact Or.inr (liftCore {p | p ∉ π} hπ')

/-- Strong-induction core for Hall existence in finite π-separable groups. -/
private theorem hall_exists_of_piSeparable_aux (π : Set ℕ) : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G], IsPiSeparable π G → Nat.card G ≤ n →
      ∃ H : Subgroup G, IsHallSubgroup π H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ hPiSep hcard
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hPiSep hsmall
    by_cases hG_one : Nat.card G = 1
    · exact ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one⟩
    haveI hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    haveI hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]
        exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    haveI hQuot_piSep : IsPiSeparable π (G ⧸ M) :=
      quotient_isPiSeparable π G M
    obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ M) hQuot_piSep hquot_card
    rcases minimal_normal_isPiGroup_or_isPiGroup_compl_of_isPiSeparable π hM with
      hM_pi | hM_pi'
    · -- If M is a π-group, the pullback of a π-Hall of G/M is π-Hall in G.
      set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
      have hH_index : H.index = Hbar.index :=
        Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
      have hHbar_idx_pos : 0 < Hbar.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
        have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
        have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
          Subgroup.card_mul_index Hbar
        have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
        have h_eq : Nat.card H * Hbar.index = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
          calc Nat.card H * Hbar.index
              = Nat.card H * H.index := by rw [hH_index]
            _ = Nat.card G := eq1
            _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
            _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
            _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
        exact Nat.mul_right_cancel hHbar_idx_pos h_eq
      refine ⟨H, ?_, ?_⟩
      · intro q hq_pf
        rw [hH_card_eq] at hq_pf
        rw [Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
        · exact hHbar.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩)
        · exact hM_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩)
      · rw [hH_index]
        exact hHbar.2
    · -- If M is a π'-group, split the pullback by Schur-Zassenhaus.
      set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
      have hH_index : H.index = Hbar.index :=
        Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
      have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
      have h_card_MH : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
      have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card Hbar) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hq_Hbar_pf : q ∈ (Nat.card Hbar).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hM_pi' q hq_M_pf (hHbar.1 q hq_Hbar_pf)
      have h_idx_MH : (M.subgroupOf H).index = Nat.card Hbar := by
        have hMH_lag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
          Subgroup.card_mul_index (M.subgroupOf H)
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have hHbar_idx_pos : 0 < Hbar.index :=
            Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
          have h_eq : Nat.card H * Hbar.index =
              (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        rw [h_card_MH, hH_card_eq] at hMH_lag
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card Hbar := by
          rw [hMH_lag, mul_comm (Nat.card Hbar)]
        exact Nat.mul_left_cancel hM_pos this
      have h_coprime_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
        rw [h_card_MH, h_idx_MH]
        exact h_coprime_M_Hbar
      haveI : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
      obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_MH
      have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
      have hK_card : Nat.card ↥K = Nat.card Hbar := by
        have := hK.card_mul
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have hHbar_idx_pos : 0 < Hbar.index :=
            Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
          have h_eq : Nat.card H * Hbar.index =
              (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        rw [h_card_MH, hH_card_eq] at this
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card Hbar := by
          rw [this, mul_comm (Nat.card Hbar)]
        exact Nat.mul_left_cancel hM_pos h_eq
      have hKlift_card : Nat.card ↥(K.map H.subtype) = Nat.card Hbar := by
        rw [Subgroup.card_subtype, hK_card]
      have hKlift_index : (K.map H.subtype).index = Nat.card ↥M * Hbar.index := by
        rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK_index, h_card_MH,
            Subgroup.range_subtype, hH_index]
      refine ⟨K.map H.subtype, ?_, ?_⟩
      · intro q hq_pf
        rw [hKlift_card] at hq_pf
        exact hHbar.1 q hq_pf
      · intro q hq_pf hq_pi
        rw [hKlift_index] at hq_pf
        rw [Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
        · have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
          exact hM_pi' q hq_in_M_pf hq_pi
        · have hq_in_HbarIdx_pf : q ∈ Hbar.index.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩
          exact hHbar.2 q hq_in_HbarIdx_pf hq_pi

/-- **Isaacs Thm 3.20**: finite π-separable groups have π-Hall subgroups. -/
theorem hall_exists_of_piSeparable [Finite G] (π : Set ℕ) [IsPiSeparable π G] :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  hall_exists_of_piSeparable_aux π (Nat.card G) G ‹IsPiSeparable π G› le_rfl

/-- **`C/B` nontrivial when `B < C`**:
`B < C` strict + `B ⊴ G` ⇒ `C.map (QuotientGroup.mk' B) ≠ ⊥`. -/
theorem Subgroup.map_quotientGroup_mk_ne_bot_of_lt {G : Type*} [Group G]
    {B C : Subgroup G} [B.Normal] (hBC : B < C) :
    C.map (QuotientGroup.mk' B) ≠ ⊥ := by
  intro h
  have hCleB : C ≤ B := by
    intro c hc
    have hmem : (QuotientGroup.mk' B) c ∈ C.map (QuotientGroup.mk' B) := ⟨c, hc, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact absurd hCleB (fun hCB => (lt_irrefl _) (hBC.trans_le hCB))

/-- **Hall-Higman 3.21 setup**:
`¬ centralizer(O) ≤ O ⇒ B := centralizer(O) ⊓ O < centralizer(O)`. -/
theorem hall_higman_B_lt_C_of_not_le {G : Type*} [Group G] (π : Set ℕ)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G) :
    Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G <
      Subgroup.centralizer (oPiCore π G : Set G) := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro h
  apply h_not_le
  rw [show Subgroup.centralizer (oPiCore π G : Set G) =
       Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G from h.symm]
  exact inf_le_right

/-- **Hall-Higman 3.21 case π closure**: K, B, C 関係 + K/B π-group + B < K ⇒ False. -/
theorem hall_higman_case_pi_contradiction
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    {K : Subgroup G} [K.Normal]
    (hKle : K ≤ Subgroup.centralizer (oPiCore π G : Set G))
    (hBle : Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G ≤ K)
    (hQpi : ∀ p ∈ (Nat.card ((↥K) ⧸
        (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G).subgroupOf K)).primeFactors,
      p ∈ π)
    (hStrict : Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G < K) :
    False := by
  have hBpi : Subgroup.IsPiGroup π
      (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G) :=
    Subgroup.IsPiGroup.le inf_le_right (oPiCore.isPiGroup π)
  have hBsubpi : Subgroup.IsPiGroup π
      ((Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G).subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hBle hBpi
  have hKpi : Subgroup.IsPiGroup π K := fun p hp =>
    IsPiGroup.of_normal_quotient _ hBsubpi hQpi p hp
  have hKle_B := hall_higman_case_pi_K_le_B π hKpi hKle
  exact absurd hKle_B (lt_irrefl _ ∘ hStrict.trans_le)

/-- **Hall-Higman 3.21 case π body**: case π での K construction + 矛盾.
case π 仮定 (`oPiCore π (↥CB) ≠ ⊥`) から K = preimage of K_quot を構築し
`hall_higman_case_pi_contradiction` で False を導出. -/
private theorem hall_higman_case_pi_body
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G)
    (hCπ : oPiCore π ↥((Subgroup.centralizer (oPiCore π G : Set G)).map
        (QuotientGroup.mk' (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G))) ≠ ⊥) :
    False := by
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  set K_quot : Subgroup ↥CB := oPiCore π ↥CB
  haveI hKq_norm : K_quot.Normal := inferInstance
  haveI hKq_char : K_quot.Characteristic := inferInstance
  set K_GB : Subgroup (G ⧸ B) := K_quot.map CB.subtype with hKGB_def
  haveI hKGB_norm : K_GB.Normal := inferInstance
  set K : Subgroup G := K_GB.comap (QuotientGroup.mk' B) with hK_def
  haveI hK_norm : K.Normal := inferInstance
  have hKGB_le_CB : K_GB ≤ CB := by
    have hRangEq : CB = (⊤ : Subgroup ↥CB).map CB.subtype := by
      rw [← MonoidHom.range_eq_map]; exact CB.range_subtype.symm
    rw [hRangEq]; exact Subgroup.map_mono le_top
  have hKle_C : K ≤ C := Subgroup.comap_le_of_le_map_quotient inf_le_left hKGB_le_CB
  have hBle_K : B ≤ K := by
    intro x hx
    simp only [hK_def, Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' B) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact K_GB.one_mem
  have hBK_lt : B < K := by
    refine lt_of_le_of_ne hBle_K ?_
    intro hBKeq
    apply hCπ
    have hKGB_bot : K_GB = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxy⟩ := QuotientGroup.mk_surjective y
      rw [← hxy] at hy ⊢
      have hx_K : x ∈ K := Subgroup.mem_comap.mpr hy
      rw [← hBKeq] at hx_K
      exact (QuotientGroup.eq_one_iff x).mpr hx_K
    apply Subgroup.map_injective CB.subtype_injective
    rw [Subgroup.map_bot]
    exact hKGB_bot
  have hQpi : ∀ p ∈ (Nat.card ((↥K) ⧸ (B.subgroupOf K))).primeFactors, p ∈ π := by
    intro p hp
    rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map B K] at hp
    have hKmap_eq : K.map (QuotientGroup.mk' B) = K_GB :=
      Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective K_GB
    rw [hKmap_eq] at hp
    have hcard : Nat.card ↥K_GB = Nat.card ↥K_quot :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective K_quot CB.subtype CB.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact (oPiCore.isPiGroup (G := ↥CB) π) p hp
  exact hall_higman_case_pi_contradiction π hKle_C hBle_K hQpi hBK_lt

/-- **Hall-Higman 3.21 case π' body**: case π' での K + Schur-Zassenhaus + H' ⊴ K + 矛盾. -/
private theorem hall_higman_case_pi'_body
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (hπ' : oPiCore {p | p ∉ π} G = ⊥)
    (h_not_le : ¬ Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G)
    (hCπ' : oPiCore {p | p ∉ π} ↥((Subgroup.centralizer (oPiCore π G : Set G)).map
        (QuotientGroup.mk' (Subgroup.centralizer (oPiCore π G : Set G) ⊓ oPiCore π G))) ≠ ⊥) :
    False := by
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  set K_quot : Subgroup ↥CB := oPiCore {p | p ∉ π} ↥CB
  haveI hKq_norm : K_quot.Normal := inferInstance
  haveI hKq_char : K_quot.Characteristic := inferInstance
  set K_GB : Subgroup (G ⧸ B) := K_quot.map CB.subtype with hKGB_def
  haveI hKGB_norm : K_GB.Normal := inferInstance
  set K : Subgroup G := K_GB.comap (QuotientGroup.mk' B) with hK_def
  haveI hK_norm : K.Normal := inferInstance
  have hKGB_le_CB : K_GB ≤ CB := by
    have hRangEq : CB = (⊤ : Subgroup ↥CB).map CB.subtype := by
      rw [← MonoidHom.range_eq_map]; exact CB.range_subtype.symm
    rw [hRangEq]; exact Subgroup.map_mono le_top
  have hKle_C : K ≤ C := Subgroup.comap_le_of_le_map_quotient inf_le_left hKGB_le_CB
  have hBle_K : B ≤ K := by
    intro x hx
    simp only [hK_def, Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' B) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact K_GB.one_mem
  have hBK_lt : B < K := by
    refine lt_of_le_of_ne hBle_K ?_
    intro hBKeq
    apply hCπ'
    have hKGB_bot : K_GB = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxy⟩ := QuotientGroup.mk_surjective y
      rw [← hxy] at hy ⊢
      have hx_K : x ∈ K := Subgroup.mem_comap.mpr hy
      rw [← hBKeq] at hx_K
      exact (QuotientGroup.eq_one_iff x).mpr hx_K
    apply Subgroup.map_injective CB.subtype_injective
    rw [Subgroup.map_bot]
    exact hKGB_bot
  have hBpi : Subgroup.IsPiGroup π B :=
    Subgroup.IsPiGroup.le inf_le_right (oPiCore.isPiGroup π)
  have hBsub_pi : Subgroup.IsPiGroup π (B.subgroupOf K) :=
    Subgroup.IsPiGroup.subgroupOf hBle_K hBpi
  have hKBindex_pi' : ∀ p ∈ (B.subgroupOf K).index.primeFactors, p ∉ π := by
    intro p hp
    have hindex_eq : (B.subgroupOf K).index = Nat.card ↥K_GB := by
      change Nat.card (↥K ⧸ (B.subgroupOf K)) = _
      rw [Subgroup.nat_card_quotient_subgroupOf_eq_card_map B K]
      have hKmap_eq : K.map (QuotientGroup.mk' B) = K_GB :=
        Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective K_GB
      rw [hKmap_eq]
    rw [hindex_eq] at hp
    have hcard : Nat.card ↥K_GB = Nat.card ↥K_quot :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective K_quot CB.subtype CB.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact (oPiCore.isPiGroup (G := ↥CB) {p | p ∉ π}) p hp
  haveI hBsub_K_normal : (B.subgroupOf K).Normal := inferInstance
  have hCoprime : Nat.Coprime (Nat.card ↥(B.subgroupOf K)) (B.subgroupOf K).index :=
    Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne'
      Subgroup.index_ne_zero_of_finite hBsub_pi hKBindex_pi'
  obtain ⟨H', hH'_compl⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := B.subgroupOf K) hCoprime
  have hCommute : ∀ n ∈ B.subgroupOf K, ∀ h ∈ H', n * h = h * n := by
    intro n hn h _
    apply Subtype.ext
    change n.val * h.val = h.val * n.val
    have hnB : n.val ∈ B := hn
    have hnO : n.val ∈ O := by
      rw [hB_def, Subgroup.mem_inf] at hnB
      exact hnB.2
    have hh_in_K : h.val ∈ K := h.property
    have hh_in_C : h.val ∈ C := hKle_C hh_in_K
    exact (Subgroup.mem_centralizer_iff.mp hh_in_C) n.val hnO
  haveI hH'_normal : H'.Normal := Subgroup.normal_complement_of_commute hH'_compl hCommute
  have hH'_card : Nat.card ↥H' = (B.subgroupOf K).index := by
    have hCompl_card : Nat.card ↥(B.subgroupOf K) * Nat.card ↥H' = Nat.card ↥K := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (Subgroup.IsComplement.equiv hH'_compl).symm
    have hKcard : Nat.card ↥K =
        Nat.card (↥K ⧸ B.subgroupOf K) * Nat.card ↥(B.subgroupOf K) :=
      (B.subgroupOf K).card_eq_card_quotient_mul_card_subgroup
    have hpos : 0 < Nat.card ↥(B.subgroupOf K) := Nat.card_pos
    have heq : Nat.card ↥H' * Nat.card ↥(B.subgroupOf K) =
        (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K) := by
      rw [Nat.mul_comm (Nat.card ↥H') _, hCompl_card, hKcard]
      change (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K) =
           (B.subgroupOf K).index * Nat.card ↥(B.subgroupOf K)
      rfl
    exact Nat.eq_of_mul_eq_mul_right hpos heq
  have hH'_pi' : Subgroup.IsPiGroup {p | p ∉ π} H' := by
    intro p hp
    rw [hH'_card] at hp
    exact hKBindex_pi' p hp
  have hH'_le : H' ≤ oPiCore {p | p ∉ π} ↥K := hH'_pi'.le_oPiCore
  haveI hOpi'_KG_normal : ((oPiCore {p | p ∉ π} ↥K).map K.subtype).Normal := inferInstance
  have hOpi'_KG_pi' : Subgroup.IsPiGroup {p | p ∉ π}
      ((oPiCore {p | p ∉ π} ↥K).map K.subtype) := by
    intro p hp
    have hcard : Nat.card ↥((oPiCore {p | p ∉ π} ↥K).map K.subtype) =
        Nat.card ↥(oPiCore {p | p ∉ π} ↥K) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact oPiCore.isPiGroup (G := ↥K) {p | p ∉ π} p hp
  have hKG_le_bot : (oPiCore {p | p ∉ π} ↥K).map K.subtype = ⊥ :=
    eq_bot_of_isPiGroup_of_oPiCore_eq_bot {p | p ∉ π} hOpi'_KG_pi' hπ'
  have hOpi'_K_bot : oPiCore {p | p ∉ π} ↥K = ⊥ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_bot]
    exact hKG_le_bot
  have hH'_bot : H' = ⊥ := le_bot_iff.mp (hH'_le.trans (le_of_eq hOpi'_K_bot))
  have hBsub_ne_top : B.subgroupOf K ≠ ⊤ := by
    intro hEq
    rw [Subgroup.subgroupOf_eq_top] at hEq
    exact absurd hEq (fun hKleB => (lt_irrefl _) (hBK_lt.trans_le hKleB))
  have hH'_card_gt : 1 < Nat.card ↥H' := by
    rw [hH'_card]
    exact Subgroup.one_lt_index_of_ne_top hBsub_ne_top
  have hH'_card_one : Nat.card ↥H' = 1 := by
    rw [hH'_bot, Subgroup.card_bot]
  omega

/-- **Isaacs Thm 3.21 Hall-Higman 1.2.3** ⭐ **FT クリティカル**.
`G` π-separable + `O_{π'}(G) = ⊥` ⇒ `C_G(O_π(G)) ≤ O_π(G)`.

**所在**: Isaacs PDF p.94 の証明は **Ch.3 内部資産で完結** — π-separable normal series +
`Subgroup.centralizer` + Schur-Zassenhaus + Sylow のみを使う.

**証明戦略** (Isaacs p.94, 5 段階):
1. `C := C_G(O_π(G))`, `B := C ⊓ O_π(G)`. 目標 `B = C`. 背理法で `B < C`.
2. `B` は π-group, `B, C` は G で正規 (characteristic も).
3. `C/B` 非自明 π-separable ⇒ 非自明 characteristic 部分群 `K/B` で π-group か π'-group.
   - `K/B ⊴ G/B` ⇒ `K ⊴ G`.
4. Case `K/B` π-group: `K` 正規 π-subgroup (B π-group + K/B π-group). `K ⊆ O_π(G)` で
   `B < K ⊆ C` だが `B = C ⊓ O_π(G)` で矛盾.
5. Case `K/B` π'-group: Schur-Zassenhaus で複合 `K = B ⋊ H`, `H > 1` π'-group.
   `H ⊆ C ⊆ C_G(B)` で `H ⊴ K`. `H ⊆ O_{π'}(K) ⊴ G` で `O_{π'}(G) = ⊥` 矛盾.

**下流被引用**: Ch.4 Thm 4.33 (mmd L2659), Ch.7 Thm 7.5 (L3853), Thm 7.6 (L3802) の 3 箇所.

**実装状態** ⭐ sorry-free. case π body + case π' body を
`exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable` (↥CB に対して) で場合分けして組み立て.
-/
theorem hall_higman_1_2_3 [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hπ' : oPiCore {p | p ∉ π} G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G := by
  by_contra h_not_le
  set O : Subgroup G := oPiCore π G with hO_def
  set C : Subgroup G := Subgroup.centralizer (O : Set G) with hC_def
  set B : Subgroup G := C ⊓ O with hB_def
  haveI hO_normal : O.Normal := inferInstance
  haveI hC_normal : C.Normal := Subgroup.normal_centralizer
  haveI hB_normal : B.Normal := by rw [hB_def]; infer_instance
  have hBC_lt : B < C := hall_higman_B_lt_C_of_not_le π h_not_le
  set CB : Subgroup (G ⧸ B) := C.map (QuotientGroup.mk' B) with hCB_def
  have hCB_ne_bot : CB ≠ ⊥ := Subgroup.map_quotientGroup_mk_ne_bot_of_lt hBC_lt
  haveI hCB_nontrivial : Nontrivial ↥CB := (Subgroup.nontrivial_iff_ne_bot CB).mpr hCB_ne_bot
  haveI hCB_normal : CB.Normal := hC_normal.map _ QuotientGroup.mk_surjective
  haveI hQuot_piSeparable : IsPiSeparable π (G ⧸ B) :=
    quotient_isPiSeparable π G B
  haveI hCB_piSeparable : IsPiSeparable π ↥CB :=
    normalSubgroup_isPiSeparable π (G ⧸ B) CB
  rcases exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable (G := ↥CB) π with
    hπCase | hπ'Case
  · exact hall_higman_case_pi_body π h_not_le hπCase
  · exact hall_higman_case_pi'_body π hπ' h_not_le hπ'Case

/-- **Hall-Higman 1.2.3 系**: `G` π-separable + `O_{π'}(G) = ⊥` ⇒
`C_G(O_π(G)) = Z(O_π(G))` (i.e., centralizer of O_π is the center of O_π).

`C_G(O_π(G)) ≤ O_π(G)` (Hall-Higman 3.21) + 一般 `Z(H) = H ⊓ C_G(H)` から従う. -/
theorem centralizer_oPiCore_eq_center [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hπ' : oPiCore {p | p ∉ π} G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) =
      (Subgroup.center ↥(oPiCore π G)).map (oPiCore π G).subtype := by
  apply le_antisymm
  · -- C_G(O) ⊆ O (Hall-Higman) so g ∈ C_G(O) ⇒ ⟨g, _⟩ ∈ Z(↥O)
    intro g hg
    have hg_O : g ∈ oPiCore π G := hall_higman_1_2_3 π hπ' hg
    refine ⟨⟨g, hg_O⟩, ?_, rfl⟩
    change (⟨g, hg_O⟩ : ↥(oPiCore π G)) ∈ Subgroup.center ↥(oPiCore π G)
    rw [Subgroup.mem_center_iff]
    rintro ⟨h, hh⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hg h hh
  · -- Z(↥O) image ⊆ C_G(O) trivially
    rintro _ ⟨⟨g, hg_O⟩, hg_center, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc : (⟨h, hh⟩ : ↥(oPiCore π G)) * ⟨g, hg_O⟩ = ⟨g, hg_O⟩ * ⟨h, hh⟩ :=
      Subgroup.mem_center_iff.mp hg_center ⟨h, hh⟩
    exact congr_arg Subtype.val hc

/-- `O_{π',π}(G)`: the preimage of `O_π(G/O_{π'}(G))`.

This is the subgroup appearing in Isaacs Thm 3.22.  The theorem is usually stated as
`[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`, equivalent to π-length at most one. -/
def oPiPrimePiCore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' (oPiCore {p | p ∉ π} G))
    (oPiCore π (G ⧸ oPiCore {p | p ∉ π} G))

instance oPiPrimePiCore.normal (π : Set ℕ) (G : Type*) [Group G] :
    (oPiPrimePiCore π G).Normal := by
  rw [oPiPrimePiCore]
  infer_instance

/-- The lower `O_{π'}` layer is contained in `O_{π',π}`. -/
theorem oPiCore_compl_le_oPiPrimePiCore (π : Set ℕ) (G : Type*) [Group G] :
    oPiCore {p | p ∉ π} G ≤ oPiPrimePiCore π G := by
  intro g hg
  rw [oPiPrimePiCore, Subgroup.mem_comap]
  rw [show (QuotientGroup.mk' (oPiCore {p | p ∉ π} G)) g = 1
      from (QuotientGroup.eq_one_iff g).mpr hg]
  exact (oPiCore π (G ⧸ oPiCore {p | p ∉ π} G)).one_mem

open scoped commutatorElement in
/-- **Isaacs Thm 3.22 (片向き; π-length ≤ 1 の Hall-Higman 系)**:
`G` π-separable + abelian な π-Hall ⇒ `[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`.

`O_{π',π}(G)` (= `π` を `O_{π'}(G)` 上に乗せた π-層) の交換子部分群が `O_{π'}(G)` に
含まれる, つまり π-length ≤ 1 と同値. -/
theorem piLength_le_one_of_abelian_pi_hall [Finite G] (π : Set ℕ) [IsPiSeparable π G]
    (hAb : ∀ (H : Subgroup G) (_ : IsHallSubgroup π H), ∀ a ∈ H, ∀ b ∈ H,
      a * b = b * a) :
    ⁅oPiPrimePiCore π G, oPiPrimePiCore π G⁆ ≤ oPiCore {p | p ∉ π} G := by
  let N : Subgroup G := oPiCore {p | p ∉ π} G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let O : Subgroup (G ⧸ N) := oPiCore π (G ⧸ N)
  let K : Subgroup G := oPiPrimePiCore π G
  have hK_def : K = O.comap q := by
    dsimp [K, O, q, N, oPiPrimePiCore]
  obtain ⟨H, hH⟩ := hall_exists_of_piSeparable π (G := G)
  let Hbar : Subgroup (G ⧸ N) := H.map q
  have hHbar : IsHallSubgroup π Hbar := hH.map_quotient
  have hO_le_Hbar : O ≤ Hbar :=
    Subgroup.IsPiGroup.normal_le_hall (oPiCore.isPiGroup π) hHbar
  have hHbar_ab : ∀ a ∈ Hbar, ∀ b ∈ Hbar, a * b = b * a := by
    intro a ha b hb
    rcases ha with ⟨a₀, ha₀, rfl⟩
    rcases hb with ⟨b₀, hb₀, rfl⟩
    simpa using congrArg q (hAb H hH a₀ ha₀ b₀ hb₀)
  have hO_comm : ⁅O, O⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hc : ⁅a, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hHbar_ab a (hO_le_Hbar ha) b (hO_le_Hbar hb))
    simpa [Subgroup.mem_bot] using hc
  have hK_map : K.map q = O := by
    rw [hK_def]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) O
  have hmap_comm : (⁅K, K⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, hK_map, hO_comm]
  have hle_ker : ⁅K, K⁆ ≤ q.ker := (Subgroup.map_eq_bot_iff ⁅K, K⁆).mp hmap_comm
  simpa [K, q, N, QuotientGroup.ker_mk'] using hle_ker

end -- 3D

section /- 3E: Coprime action (pp. 96-104) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3E (Coprime action)

`A` が `G` に作用し `gcd(|A|, |G|) = 1` の場合の構造論. BG/Peterfalvi 全体で頻用.

**含まれる結果**:
- Thm 3.23: coprime action ⇒ A-invariant Sylow 存在・共役・unique up to A-action.
- Lemma 3.24 (Glauberman lemma): A 作用 + transitive G 作用 のコンパチで A-fixed 元存在.
- Thm 3.25-3.27: A-不変部分群と商の対応 (`C_G(A)` 経由).
- Thm 3.28: A-不変 Sylow と `C_G(A)` の Sylow の対応.
- Thm 3.29-3.31: 軌道構造 (Hartley-Turull, orbit-size 主張).
- Thm 3.32-3.34: テクニカル系 (`[G,A,A] = [G,A]` Three-Subgroup Lemma 経由 等).

**形式化状態**: 全 stub.  完全実装は ~8-12 週の大規模作業 (mathlib coprime action machinery
の活用 + Isaacs 流の細部). 別 phase で進める. -/

/-- **A-不変部分群**: `φ : A →* MulAut G` の作用下で `H ≤ G` が `A`-不変.
i.e., `∀ a ∈ A, φ(a) • H = H`. -/
def IsAInvariant {A : Type*} [Group A] (φ : A →* MulAut G) (H : Subgroup G) : Prop :=
  ∀ a : A, (φ a : MulAut G) • H = H

/-- A-不変な H に対し, 要素レベルで `(φ a) g ∈ H` が成立. -/
theorem IsAInvariant.smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) (a : A) {g : G} (hg : g ∈ H) : (φ a) g ∈ H := by
  have : (φ a) g ∈ (φ a) • H := ⟨g, hg, rfl⟩
  rwa [hH a] at this

/-- **A-不変の特徴付け**: `IsAInvariant φ H ↔ ∀ a g, g ∈ H ⇒ (φ a) g ∈ H`. -/
theorem isAInvariant_iff_smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G} :
    IsAInvariant φ H ↔ ∀ a : A, ∀ g, g ∈ H → (φ a) g ∈ H := by
  refine ⟨fun hH a g hg => hH.smul_mem a hg, fun h a => ?_⟩
  -- (φ a) • H = H. Show le_antisymm.
  apply le_antisymm
  · -- (φ a) • H ≤ H: image is in H by assumption
    rintro _ ⟨g, hg, rfl⟩
    exact h a g hg
  · -- H ≤ (φ a) • H: take h, find preimage via (φ a)⁻¹
    intro g hg
    refine ⟨(φ a)⁻¹ g, ?_, MulAut.apply_inv_self G (φ a) g⟩
    -- (φ a)⁻¹ g ∈ H: use h with a := a⁻¹, since φ is a hom, (φ a⁻¹) = (φ a)⁻¹
    have hg' : (φ a⁻¹) g ∈ H := h a⁻¹ g hg
    rw [φ.map_inv] at hg'
    exact hg'

/-- A-不変な H に対し, 要素レベルで `(φ a)⁻¹ g ∈ H` が成立 (= 逆作用 a⁻¹ で smul_mem). -/
theorem IsAInvariant.inv_smul_mem {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) (a : A) {g : G} (hg : g ∈ H) : (φ a)⁻¹ g ∈ H := by
  have hHinv : (φ a⁻¹) • H = H := hH a⁻¹
  rw [φ.map_inv] at hHinv
  have : (φ a)⁻¹ g ∈ (φ a)⁻¹ • H := ⟨g, hg, rfl⟩
  rwa [hHinv] at this

/-- If an invariant subgroup of `W` is acted on by an automorphism whose underlying value is
conjugation by `g` in the ambient group, then `g` normalizes its image under `W.subtype`. -/
theorem IsAInvariant.mem_normalizer_map_subtype_of_smul_val {W : Subgroup G}
    {A : Type*} [Group A] {φ : A →* MulAut W} {L : Subgroup W}
    (hL : IsAInvariant φ L) {a : A} {g : G}
    (hval : ∀ k : W, ((φ a k : W) : G) = g * (k : G) * g⁻¹) :
    g ∈ Subgroup.normalizer ((L.map W.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨φ a k, hL.smul_mem _ hk, hval k⟩
  · rintro ⟨k, hk, hkeq⟩
    refine ⟨(φ a)⁻¹ k, hL.inv_smul_mem _ hk, ?_⟩
    have hv2 := hval ((φ a)⁻¹ k)
    rw [MulAut.apply_inv_self] at hv2
    have h3 := hv2.symm.trans hkeq
    exact mul_left_cancel (mul_right_cancel h3)

/-- ⊤ は常に A-不変. -/
theorem IsAInvariant.top {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (⊤ : Subgroup G) := fun a => by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_top]

/-- ⊥ は常に A-不変. -/
theorem IsAInvariant.bot {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (⊥ : Subgroup G) := fun _ => Subgroup.smul_bot _

/-- A-不変部分群の交わりは A-不変. -/
theorem IsAInvariant.inf {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) : IsAInvariant φ (H ⊓ K) := fun a => by
  rw [Subgroup.smul_inf, hH a, hK a]

/-- A-不変部分群の sup は A-不変. -/
theorem IsAInvariant.sup {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) : IsAInvariant φ (H ⊔ K) := fun a => by
  rw [Subgroup.smul_sup, hH a, hK a]

/-- Conjugating an `A`-invariant subgroup by an `A`-fixed element preserves invariance. -/
theorem IsAInvariant.mulAut_conj_smul_of_fixed {A : Type*} [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) {c : G} (hc : ∀ a : A, (φ a) c = c) :
    IsAInvariant φ (MulAut.conj c • H) := by
  rw [isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(φ a) y, hH.smul_mem a hy, ?_⟩
  simp [MulAut.conj_apply, map_mul, map_inv, hc a]

/-- **Characteristic 部分群は常に A-不変**: H.Characteristic ⇒ IsAInvariant φ H for any φ.
mathlib `characteristic_iff_map_eq` 経由. -/
theorem IsAInvariant.of_characteristic {A : Type*} [Group A] (φ : A →* MulAut G)
    {H : Subgroup G} [hH : H.Characteristic] : IsAInvariant φ H := fun a => by
  change H.map (φ a).toMonoidHom = H
  exact (Subgroup.characteristic_iff_map_eq.mp hH) (φ a)

/-- `derivedSeries G n` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.derivedSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ (derivedSeries G n) :=
  IsAInvariant.of_characteristic φ

/-- `(⊤ : Subgroup G).lowerCentralSeries n` (旧 `lowerCentralSeries G n`) は A-不変
(characteristic instance 経由). -/
theorem IsAInvariant.lowerCentralSeries {A : Type*} [Group A] (φ : A →* MulAut G) (n : ℕ) :
    IsAInvariant φ ((⊤ : Subgroup G).lowerCentralSeries n) :=
  IsAInvariant.of_characteristic φ

/-- `Subgroup.center G` は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.center {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (Subgroup.center G) :=
  IsAInvariant.of_characteristic φ

/-- `fitting G` (Fitting subgroup) は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.fittingSubgroup {A : Type*} [Group A] [Finite G] (φ : A →* MulAut G) :
    IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting G) :=
  IsAInvariant.of_characteristic φ

/-- `commutator G = G'` は A-不変 (derivedSeries 1 経由). -/
theorem IsAInvariant.commutator_self {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (commutator G) := by
  rw [← derivedSeries_one]
  exact IsAInvariant.derivedSeries φ 1

/-- `frattini G` (Frattini subgroup, mathlib def) は A-不変 (characteristic instance 経由). -/
theorem IsAInvariant.frattini {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (_root_.frattini G) :=
  IsAInvariant.of_characteristic φ

/-- A-不変な集合 S の生成部分群 `Subgroup.closure S` は A-不変. -/
theorem IsAInvariant.closure_of_invariant_set {A : Type*} [Group A] {φ : A →* MulAut G}
    {S : Set G} (hS : ∀ a : A, (φ a) '' S = S) :
    IsAInvariant φ (Subgroup.closure S) := fun a => by
  change (Subgroup.closure S).map (φ a).toMonoidHom = Subgroup.closure S
  rw [MonoidHom.map_closure]
  congr 1
  exact hS a

/-- A-不変 + A-不変 の commutator は A-不変 (`Subgroup.map_commutator`). -/
theorem IsAInvariant.commutator {A : Type*} [Group A] {φ : A →* MulAut G} {H K : Subgroup G}
    (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) :
    IsAInvariant φ ⁅H, K⁆ := fun a => by
  change ⁅H, K⁆.map (φ a).toMonoidHom = ⁅H, K⁆
  rw [Subgroup.map_commutator]
  rw [show H.map (φ a).toMonoidHom = H from hH a,
      show K.map (φ a).toMonoidHom = K from hK a]

/-- A-不変部分群の normalizer は A-不変 (`Subgroup.map_normalizer_eq_of_bijective`). -/
theorem IsAInvariant.normalizer {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : IsAInvariant φ (Subgroup.normalizer H) := fun a => by
  change (Subgroup.normalizer H).map (φ a).toMonoidHom = Subgroup.normalizer H
  rw [Subgroup.map_normalizer_eq_of_bijective H (φ a).bijective,
      show H.map (φ a).toMonoidHom = H from hH a]

/-- A-不変部分群の centralizer は A-不変. `Subgroup.map_centralizer_eq_of_bijective` +
`hH a` で (φ a) '' H = H が言えるので clean. -/
theorem IsAInvariant.centralizer {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) :
    IsAInvariant φ (Subgroup.centralizer (H : Set G)) := fun a => by
  change (Subgroup.centralizer (H : Set G)).map (φ a).toMonoidHom
      = Subgroup.centralizer (H : Set G)
  rw [Subgroup.map_centralizer_eq_of_bijective _ _ (φ a).bijective]
  congr 1
  -- want: (φ a).toMonoidHom '' (H : Set G) = (H : Set G)
  have hH_set : ((H.map (φ a).toMonoidHom : Subgroup G) : Set G) = (H : Set G) := by
    rw [show H.map (φ a).toMonoidHom = H from hH a]
  exact hH_set

/-- A-不変部分群族の iSup は A-不変. -/
theorem IsAInvariant.iSup {A : Type*} [Group A] {φ : A →* MulAut G} {ι : Sort*}
    {f : ι → Subgroup G} (hf : ∀ i, IsAInvariant φ (f i)) :
    IsAInvariant φ (⨆ i, f i) := fun a => by
  change (⨆ i, f i).map (φ a).toMonoidHom = ⨆ i, f i
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => hf i a

/-- A-不変部分群族の iInf は A-不変 (非空 ι が必要; `(φ a)` 単射性を利用). -/
theorem IsAInvariant.iInf {A : Type*} [Group A] {φ : A →* MulAut G} {ι : Sort*} [Nonempty ι]
    {f : ι → Subgroup G} (hf : ∀ i, IsAInvariant φ (f i)) :
    IsAInvariant φ (⨅ i, f i) := fun a => by
  change (⨅ i, f i).map (φ a).toMonoidHom = ⨅ i, f i
  rw [Subgroup.map_iInf _ (φ a).injective]
  exact iInf_congr fun i => hf i a

/-- **A-不変部分群への制限作用**: `φ : A →* MulAut G` + A-inv `H` から
`A →* MulAut ↥H` を構成する. 各 `a : A` で `(φ a)` は `H` を保つので
restricted MulEquiv ↥H ↥H を作る. -/
def IsAInvariant.restrict {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : A →* MulAut ↥H where
  toFun a := {
    toFun := fun h => ⟨(φ a) h.val, hH.smul_mem a h.property⟩
    invFun := fun h => ⟨(φ a)⁻¹ h.val, hH.inv_smul_mem a h.property⟩
    left_inv := fun h => Subtype.ext (MulAut.inv_apply_self G (φ a) h.val)
    right_inv := fun h => Subtype.ext (MulAut.apply_inv_self G (φ a) h.val)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    apply MulEquiv.ext
    intro ⟨g, hg⟩
    apply Subtype.ext
    change (φ 1) g = g
    rw [φ.map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro ⟨g, hg⟩
    apply Subtype.ext
    change (φ (a * b)) g = (φ a) ((φ b) g)
    rw [φ.map_mul]
    rfl

/-- restrict の値域への射影: A-inv H に対し, `(IsAInvariant.restrict hH a) h` の underlying
要素は `(φ a) h.val`. -/
@[simp]
theorem IsAInvariant.restrict_apply_val {A : Type*} [Group A] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) (a : A) (h : ↥H) :
    ((hH.restrict a) h).val = (φ a) h.val := rfl

/-- A-不変 H の normalCore は A-不変. proof: `normalCore_eq_iInf_conjAct` で
`normalCore H = ⨅ g : ConjAct G, g • H`. (φ a) は inner action と可換でないが,
element-level の `b * x * b⁻¹ ∈ H` を通して直接示せる. -/
theorem IsAInvariant.normalCore {A : Type*} [Group A] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : IsAInvariant φ H) : IsAInvariant φ H.normalCore := fun a => by
  change H.normalCore.map (φ a).toMonoidHom = H.normalCore
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- hy : y ∈ normalCore H = {a : ∀ b, b * a * b⁻¹ ∈ H}
    change ∀ b, b * (φ a) y * b⁻¹ ∈ H
    intro b
    have hcyc : ((φ a)⁻¹ b) * y * ((φ a)⁻¹ b)⁻¹ ∈ H := hy ((φ a)⁻¹ b)
    have h_apply : (φ a) (((φ a)⁻¹ b) * y * ((φ a)⁻¹ b)⁻¹) ∈ H := hH.smul_mem a hcyc
    simp only [map_mul, MulAut.apply_inv_self, map_inv] at h_apply
    exact h_apply
  · intro hx
    -- hx : x ∈ normalCore H = {a : ∀ b, b * a * b⁻¹ ∈ H}
    refine ⟨(φ a)⁻¹ x, ?_, MulAut.apply_inv_self G (φ a) x⟩
    change ∀ b, b * ((φ a)⁻¹ x) * b⁻¹ ∈ H
    intro b
    have hcxc : ((φ a) b) * x * ((φ a) b)⁻¹ ∈ H := hx ((φ a) b)
    have h_apply : (φ a)⁻¹ (((φ a) b) * x * ((φ a) b)⁻¹) ∈ H := hH.inv_smul_mem a hcxc
    simp only [map_mul, map_inv,
      show ∀ y : G, ((φ a)⁻¹ : MulAut G) ((φ a) y) = y from
        fun y => MulAut.inv_apply_self G (φ a) y] at h_apply
    exact h_apply

/-- A-不変 H と K (`K ≤ G`) に対し, `K.subgroupOf H` は restricted action `hH.restrict`
下で A-不変. -/
theorem IsAInvariant.subgroupOf {A : Type*} [Group A] {φ : A →* MulAut G}
    {H K : Subgroup G} (hH : IsAInvariant φ H) (hK : IsAInvariant φ K) :
    IsAInvariant hH.restrict (K.subgroupOf H) := fun a => by
  ext ⟨g, hg⟩
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf]
  constructor
  · intro hmem
    -- hmem : ((hH.restrict a)⁻¹ • ⟨g, hg⟩).val ∈ K
    -- We have ((hH.restrict a)⁻¹ ⟨g, hg⟩).val = (φ a)⁻¹ g
    -- So (φ a)⁻¹ g ∈ K (via hmem). Apply (φ a) to get g ∈ K.
    change g ∈ K
    have h1 : ((hH.restrict a)⁻¹ • (⟨g, hg⟩ : ↥H)).val = (φ a)⁻¹ g := rfl
    have h2 : (φ a)⁻¹ g ∈ K := h1 ▸ hmem
    have : (φ a) ((φ a)⁻¹ g) ∈ K := hK.smul_mem a h2
    rwa [MulAut.apply_inv_self] at this
  · intro hg_K
    -- g ∈ K
    -- Want ((hH.restrict a)⁻¹ ⟨g, hg⟩).val ∈ K, i.e., (φ a)⁻¹ g ∈ K.
    change ((hH.restrict a)⁻¹ • (⟨g, hg⟩ : ↥H)).val ∈ K
    change (φ a)⁻¹ g ∈ K
    exact hK.inv_smul_mem a hg_K

/-- Lift a Hall subgroup found inside an invariant overgroup back to the ambient group. -/
theorem lift_hall_from_invariant_overgroup [Finite G] {A : Type*} [Group A]
    {φ : A →* MulAut G} {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_le_H : K ≤ H) {L : Subgroup H}
    (hL_hall : IsHallSubgroup π L)
    (hL_inv : IsAInvariant hH_inv.restrict L)
    (hK_sub_le_L : K.subgroupOf H ≤ L) :
    ∃ Lg : Subgroup G, IsHallSubgroup π Lg ∧ IsAInvariant φ Lg ∧ K ≤ Lg := by
  refine ⟨L.map H.subtype, hL_hall.map_subtype_of_index_no_pi hH_index, ?_, ?_⟩
  · rw [isAInvariant_iff_smul_mem]
    rintro a _ ⟨l, hl, rfl⟩
    exact ⟨(hH_inv.restrict a) l, hL_inv.smul_mem a hl,
      IsAInvariant.restrict_apply_val hH_inv a l⟩
  · intro k hk
    rw [Subgroup.mem_map]
    exact ⟨⟨k, hK_le_H hk⟩, hK_sub_le_L (by simpa [Subgroup.mem_subgroupOf] using hk), rfl⟩

/-- Assemble a proper invariant-overgroup induction step for invariant Hall overgroups. -/
theorem proper_overgroup_branch_frame [Finite G] {A : Type*} [Group A]
    {φ : A →* MulAut G} {π : Set ℕ} {K H : Subgroup G}
    (hH_inv : IsAInvariant φ H)
    (hH_index : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hK_pi : Subgroup.IsPiGroup π K)
    (hK_inv : IsAInvariant φ K)
    (hK_le_H : K ≤ H)
    (hIH_H : ∀ {Ksub : Subgroup H},
      Subgroup.IsPiGroup π Ksub →
        IsAInvariant hH_inv.restrict Ksub →
        ∃ L : Subgroup H, IsHallSubgroup π L ∧
          IsAInvariant hH_inv.restrict L ∧ Ksub ≤ L) :
    ∃ Lg : Subgroup G, IsHallSubgroup π Lg ∧ IsAInvariant φ Lg ∧ K ≤ Lg := by
  let Ksub : Subgroup H := K.subgroupOf H
  have hKsub_pi : Subgroup.IsPiGroup π Ksub :=
    Subgroup.IsPiGroup.subgroupOf hK_le_H hK_pi
  have hKsub_inv : IsAInvariant hH_inv.restrict Ksub :=
    hH_inv.subgroupOf hK_inv
  obtain ⟨L, hL_hall, hL_inv, hKsub_le_L⟩ := hIH_H hKsub_pi hKsub_inv
  exact lift_hall_from_invariant_overgroup hH_inv hH_index hK_le_H
    hL_hall hL_inv hKsub_le_L

/-- `fixedPointsOfMulAut φ` は (同じ) `φ` 作用下で A-不変 (定義より trivially). -/
theorem IsAInvariant.fixedPointsOfMulAut {A : Type*} [Group A] (φ : A →* MulAut G) :
    IsAInvariant φ (Subgroup.fixedPointsOfMulAut φ) := fun a => by
  change (Subgroup.fixedPointsOfMulAut φ).map (φ a).toMonoidHom = Subgroup.fixedPointsOfMulAut φ
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_fixedPointsOfMulAut]
  refine ⟨?_, fun hy => ⟨y, hy, hy a⟩⟩
  rintro ⟨x, hx, rfl⟩
  -- (MulEquiv.toMonoidHom (φ a)) x = (φ a) x; need to show ∀ b, (φ b) ((φ a) x) = (φ a) x
  change ∀ b, (φ b) ((φ a) x) = (φ a) x
  intro b
  rw [show (φ a) x = x from hx a]
  exact hx b

/-! **Isaacs Thm 3.23, 3.24 (Coprime action)** ⭐ **FT クリティカル**.
A coprime action ⇒ A-不変 Sylow 存在 (3.23a), 共役 (3.23b), Glauberman fixed point (3.24).

**Forward dep**: Ch.4 §4C-§4D (coprime action machinery) を要する. ~8-12 週の大規模.
所在: `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean` (placeholder). -/

end -- 3E

section /- 3F: 巡回商 lift (pp. 105-112) -/

variable {G : Type*} [Group G]

/-! ### Isaacs §3F (Cyclic quotient lift)

3.35-3.36: `H ⊴ G` で `G/H` 巡回 (位数 n) のとき, `H ≤ K ≤ G` で `G = HK` かつ
`|K/H| = n` となる `K` が存在 (3.35 lift, 3.36 specialization).

FT 経路では優先度低 (Peterfalvi で散発使用).

**形式化状態**: stub. 全 lifted 結果は SemidirectProduct (mathlib) との接続で得られる
可能性が高い. -/

/-- **Isaacs Thm 3.35 (cyclic lift; generator)**: `H ⊴ G`, `G/H` cyclic ⇒ ある `g ∈ G` が
`G/H` の生成元の lift で, `⟨g⟩ ⊔ H = G`. (Thm 3.35 強版の uniqueness の前提.) -/
theorem cyclic_quotient_lift [Finite G] {H : Subgroup G} [H.Normal]
    (hCyclic : IsCyclic (G ⧸ H)) :
    ∃ g : G, Subgroup.zpowers g ⊔ H = ⊤ := by
  obtain ⟨gbar, hgbar⟩ := hCyclic.exists_generator
  -- gbar : G ⧸ H, hgbar : ∀ x, x ∈ Subgroup.zpowers gbar.
  -- Lift to g ∈ G.
  obtain ⟨g, hg_proj⟩ := QuotientGroup.mk_surjective gbar
  refine ⟨g, ?_⟩
  rw [eq_top_iff]
  intro x _
  -- ⟦x⟧ ∈ ⟨gbar⟩, so ⟦x⟧ = gbar^n for some n. So x = g^n · h for some h ∈ H.
  have hx : (x : G ⧸ H) ∈ Subgroup.zpowers gbar := hgbar _
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, hn⟩ := hx
  -- hn : gbar ^ n = (x : G ⧸ H). Substituting gbar = ⟦g⟧: ⟦g⟧^n = ⟦g^n⟧ = ⟦x⟧.
  have h_in_H : x * (g ^ n)⁻¹ ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← hg_proj] at hn
    -- hn : (↑g : G ⧸ H) ^ n = ↑x
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, ← hn]
    group
  -- x = (x · (g^n)⁻¹) · g^n with first factor in H and second in ⟨g⟩.
  rw [show x = (x * (g ^ n)⁻¹) * g ^ n by group, sup_comm]
  exact Subgroup.mul_mem_sup h_in_H (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n)

/-- **Isaacs Thm 3.35 (uniqueness)** ⭐: `N ⊴ G` で `gN` が `G/N` の生成元のとき,
`G →* G₀` の準同型は `N` 上での値と `g ↦ g₀` から **一意に決定**.

Isaacs §3F の主結果 (extension uniqueness). 任意 `u ∈ G` は `u = (u·(g^i)⁻¹) · g^i` の
形に一意分解 (`u·(g^i)⁻¹ ∈ N`, `i` は `gN` の zpowers での representation).
両 θ, θ' が同じ extension を与えるなら値が一致.

**注**: existence (Thm 3.36 cyclic extension) は別途 (Sym(Ω) realization), Phase 4 予定. -/
theorem cyclic_quotient_extension_unique
    {G G₀ : Type*} [Group G] [Group G₀]
    {N : Subgroup G} [N.Normal]
    (g : G) (g₀ : G₀)
    (hg_gen : Subgroup.zpowers ((g : G ⧸ N)) = ⊤)
    {θ θ' : G →* G₀}
    (hθ_ext : ∀ x ∈ N, θ x = θ' x) (hθ_g : θ g = g₀) (hθ'_g : θ' g = g₀) :
    θ = θ' := by
  ext u
  -- ⟦u⟧ ∈ ⟨⟦g⟧⟩, so ⟦u⟧ = ⟦g⟧^i for some i ∈ ℤ.
  have hu_mem : (u : G ⧸ N) ∈ Subgroup.zpowers ((g : G ⧸ N)) := hg_gen ▸ Subgroup.mem_top _
  rw [Subgroup.mem_zpowers_iff] at hu_mem
  obtain ⟨i, hi⟩ := hu_mem
  -- hi : (↑g)^i = ↑u in G ⧸ N, i.e., x := u * (g^i)⁻¹ ∈ N.
  set x : G := u * (g^i)⁻¹ with hxdef
  have hx_mem : x ∈ N := by
    rw [hxdef, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, ← hi]
    group
  -- u = x * g^i.
  have hu_decomp : u = x * g^i := by rw [hxdef]; group
  rw [hu_decomp, map_mul θ, map_mul θ', map_zpow θ, map_zpow θ', hθ_g, hθ'_g, hθ_ext _ hx_mem]

/-! ### Isaacs Thm 3.36 (cyclic extension existence)

`N` 群, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` で `σ a = a` かつ `σ^m = MulAut.conj a` を満たすとき,
`N ⊴ G` で `G/N` cyclic of order `m`, generator `g` で `g^m = a` かつ `x^g = σ x`
となる群 `G` が存在.

構成: `preG := N ⋊_σ (Multiplicative ℤ)` を quotient by `K := ⟨(a⁻¹, m)⟩`.
`hσa, hσm` から `(a⁻¹, m)` が `preG` の中心元 ⇒ `K ⊴ preG`. 各性質は商計算. -/
/-- Twist hom: `Multiplicative ℤ →* MulAut N` sending `ofAdd k ↦ σ^k`. -/
private noncomputable def cyclicExtPhi {N : Type*} [Group N] (σ : MulAut N) :
    Multiplicative ℤ →* MulAut N :=
  zpowersHom (MulAut N) σ

@[simp] private lemma cyclicExtPhi_apply {N : Type*} [Group N] (σ : MulAut N)
    (k : Multiplicative ℤ) : cyclicExtPhi σ k = σ ^ k.toAdd := rfl

/-- The pre-quotient group `N ⋊_σ ℤ`. -/
private abbrev CyclicExtPreG (N : Type*) [Group N] (σ : MulAut N) : Type _ :=
  SemidirectProduct N (Multiplicative ℤ) (cyclicExtPhi σ)

/-- The "central" element `(a⁻¹, m)` in `preG`. -/
private noncomputable def cyclicExtK {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : CyclicExtPreG N σ :=
  SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))

/-- Under `hσa` and `hσm`, the element `(a⁻¹, m)` is fixed by conjugation. -/
private lemma cyclicExtK_centralized {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∀ y : CyclicExtPreG N σ, y * cyclicExtK m a σ * y⁻¹ = cyclicExtK m a σ := by
  intro y
  -- σ^k fixes a (and a⁻¹) for any k : ℤ (since σ ∈ stabilizer a).
  have hσka : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
    (Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
      (MulAction.mem_stabilizer_iff.mpr hσa) k : _)
  have hσka_inv : ∀ k : ℤ, (σ ^ k) a⁻¹ = a⁻¹ := fun k => by rw [map_inv, hσka k]
  -- σ^m sends x to a * x * a⁻¹ (from hσm).
  have hσm_apply : ∀ x : N, ((σ ^ m : MulAut N)) x = a * x * a⁻¹ := fun x => by
    rw [hσm]; rfl
  -- (cyclicExtK).left = a⁻¹, .right = ofAdd m.
  have h_K_left : (cyclicExtK m a σ).left = a⁻¹ := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).left = _
    simp [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          SemidirectProduct.left_inr]
  have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
    change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
    simp [SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr]
  ext
  · -- Left component.
    change ((y * cyclicExtK m a σ) * y⁻¹).left = (cyclicExtK m a σ).left
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
               SemidirectProduct.inv_left,
               h_K_left, h_K_right, cyclicExtPhi_apply]
    -- Goal (approx): y.left * (σ^l.toAdd) a⁻¹ * (σ^(l.toAdd+m)) ((σ^(-l.toAdd)) y.left⁻¹) = a⁻¹.
    rw [hσka_inv]
    -- Compose σ chain.
    have hcompose : (σ ^ ((y.right * Multiplicative.ofAdd (m : ℤ)).toAdd))
        ((σ ^ ((y.right⁻¹ : Multiplicative ℤ).toAdd)) y.left⁻¹) =
          ((σ : MulAut N) ^ m) y.left⁻¹ := by
      change (σ ^ ((y.right.toAdd + (m : ℤ)) : ℤ))
            ((σ ^ ((-y.right.toAdd) : ℤ)) y.left⁻¹) = _
      rw [← MulAut.mul_apply, ← zpow_add,
          show (y.right.toAdd + (m : ℤ)) + (-y.right.toAdd) = (m : ℤ) by ring,
          zpow_natCast]
    rw [hcompose, hσm_apply]
    group
  · -- Right component (Multiplicative ℤ abelian).
    change ((y * cyclicExtK m a σ) * y⁻¹).right = (cyclicExtK m a σ).right
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [mul_comm y.right _, mul_assoc, mul_inv_cancel, mul_one]

/-- The kernel subgroup `K = ⟨(a⁻¹, m)⟩`. -/
private noncomputable abbrev cyclicExtKSubgroup {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N) : Subgroup (CyclicExtPreG N σ) :=
  Subgroup.zpowers (cyclicExtK m a σ)

private lemma cyclicExtKSubgroup_normal {N : Type*} [Group N]
    (m : ℕ) (a : N) (σ : MulAut N)
    (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    (cyclicExtKSubgroup m a σ).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_zpowers_iff] at hn
  obtain ⟨j, hj⟩ := hn
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← hj]
  have h_conj_zpow : y * (cyclicExtK m a σ)^j * y⁻¹ = (y * cyclicExtK m a σ * y⁻¹)^j := by
    have h : (MulAut.conj y) ((cyclicExtK m a σ)^j) = ((MulAut.conj y) (cyclicExtK m a σ))^j :=
      map_zpow (MulAut.conj y) _ _
    simpa only [MulAut.conj_apply] using h
  rw [h_conj_zpow, cyclicExtK_centralized m a σ hσa hσm]

/-- **Isaacs Thm 3.36 (cyclic extension existence)** ⭐:
given `N`, `m > 0`, `a ∈ N`, `σ ∈ Aut(N)` with `σ a = a` and `σ^m = MulAut.conj a`,
there exists a group `G` with `N ⊴ G` (via iso `ι`), `G/N` cyclic of order `m` generator `g`,
`g^m = ι a` and `g · ι x · g⁻¹ = ι (σ x)`.

Construction: `G := (N ⋊_σ ℤ) / ⟨(a⁻¹, m)⟩`. The element `(a⁻¹, m)` is central (proven in
`cyclicExtK_centralized` using `σ a = a` and `σ^m = MulAut.conj a`), so its zpowers form
a normal subgroup. Quotienting gives `G` with the desired cyclic-extension structure. -/
theorem cyclic_extension_exists.{u} {N : Type u} [Group N] {m : ℕ} (_hm : 0 < m)
    (a : N) (σ : MulAut N) (hσa : σ a = a) (hσm : σ ^ m = MulAut.conj a) :
    ∃ (G : Type u) (_ : Group G) (N₀ : Subgroup G) (_ : N₀.Normal)
      (ι : N ≃* ↥N₀) (g : G),
      Subgroup.zpowers ((g : G ⧸ N₀)) = ⊤ ∧
      g ^ m = (ι a : G) ∧
      ∀ x : N, g * (ι x : G) * g⁻¹ = (ι (σ x) : G) := by
  haveI hK_norm : (cyclicExtKSubgroup m a σ).Normal :=
    cyclicExtKSubgroup_normal m a σ hσa hσm
  -- G := preG ⧸ K with the natural Group instance.
  let G := CyclicExtPreG N σ ⧸ cyclicExtKSubgroup m a σ
  -- inl_to_G : N →* G via inl then quotient.
  let inl_to_G : N →* G :=
    (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)).comp SemidirectProduct.inl
  -- inl_to_G is injective: ker = inl⁻¹(K) = ⊥.
  have h_inj : Function.Injective inl_to_G := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h_in_K : (SemidirectProduct.inl x : CyclicExtPreG N σ) ∈ cyclicExtKSubgroup m a σ := by
      have heq : inl_to_G x = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
          (SemidirectProduct.inl x) := rfl
      rw [heq] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_zpowers_iff] at h_in_K
    obtain ⟨j, hj⟩ := h_in_K
    have h_K_right : (cyclicExtK m a σ).right = Multiplicative.ofAdd (m : ℤ) := by
      change (SemidirectProduct.inl a⁻¹ * SemidirectProduct.inr _).right = _
      simp
    have h_jm_eq_zero : (j • (m : ℤ)) = 0 := by
      have h_right_of_inl : (SemidirectProduct.inl x : CyclicExtPreG N σ).right = 1 :=
        SemidirectProduct.right_inl x
      have h_zpow_right : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right =
          (Multiplicative.ofAdd (m : ℤ)) ^ j := by
        have hmap : SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) =
            SemidirectProduct.rightHom (cyclicExtK m a σ) ^ j := map_zpow _ _ _
        change SemidirectProduct.rightHom ((cyclicExtK m a σ) ^ j) = _
        rw [hmap]; congr 1
      have h_one : ((cyclicExtK m a σ) ^ j : CyclicExtPreG N σ).right = 1 := by
        rw [hj]; exact h_right_of_inl
      rw [h_zpow_right] at h_one
      rw [← ofAdd_zsmul, ofAdd_eq_one] at h_one
      exact h_one
    have hj_zero : j = 0 := by
      rw [smul_eq_mul] at h_jm_eq_zero
      rcases mul_eq_zero.mp h_jm_eq_zero with h | h
      · exact h
      · exfalso
        have hm_pos : (m : ℤ) > 0 := Int.natCast_pos.mpr _hm
        exact (ne_of_gt hm_pos) h
    subst hj_zero
    rw [zpow_zero] at hj
    have h_inl_one : (SemidirectProduct.inl x : CyclicExtPreG N σ) = 1 := hj.symm
    have : SemidirectProduct.inl x = (SemidirectProduct.inl (1 : N) : CyclicExtPreG N σ) := by
      rw [(SemidirectProduct.inl : N →* CyclicExtPreG N σ).map_one]; exact h_inl_one
    exact SemidirectProduct.inl_injective this
  -- N₀ := range of inl_to_G.
  let N₀ : Subgroup G := inl_to_G.range
  haveI hN₀_norm : N₀.Normal := by
    have h_range_eq : (inl_to_G.range : Subgroup G) =
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.map
          (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) :=
      MonoidHom.range_comp _ _
    change N₀.Normal
    rw [show N₀ = inl_to_G.range from rfl, h_range_eq]
    have h_inl_range_normal :
        (SemidirectProduct.inl : N →* CyclicExtPreG N σ).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact (SemidirectProduct.rightHom : CyclicExtPreG N σ →* Multiplicative ℤ).normal_ker
    exact h_inl_range_normal.map _ (QuotientGroup.mk'_surjective _)
  -- ι := N ≃* N₀.
  let ι : N ≃* ↥N₀ := MonoidHom.ofInjective h_inj
  -- g := ⟦inr (ofAdd 1)⟧.
  let g : G := QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))
  refine ⟨G, inferInstance, N₀, hN₀_norm, ι, g, ?_, ?_, ?_⟩
  · -- zpowers ⟦g⟧ = ⊤ in G/N₀: every G/N₀ element lifts to preG, decompose y = inl·inr;
    -- inl part vanishes in G/N₀, inr part is ⟦g⟧^(y.right.toAdd).
    rw [Subgroup.eq_top_iff']
    intro z
    obtain ⟨zG, rfl⟩ : ∃ zG : G, QuotientGroup.mk' N₀ zG = z :=
      QuotientGroup.mk'_surjective _ z
    obtain ⟨y, rfl⟩ : ∃ y : CyclicExtPreG N σ,
        QuotientGroup.mk' (cyclicExtKSubgroup m a σ) y = zG :=
      QuotientGroup.mk'_surjective _ zG
    rw [show y = SemidirectProduct.inl y.left * SemidirectProduct.inr y.right from
      (SemidirectProduct.inl_left_mul_inr_right y).symm,
      map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_mul (QuotientGroup.mk' N₀)]
    have h_in_N₀ : (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl y.left)) ∈ N₀ := ⟨y.left, rfl⟩
    have h_first_one : (QuotientGroup.mk' N₀ : G →* G ⧸ N₀)
        ((QuotientGroup.mk' (cyclicExtKSubgroup m a σ)) (SemidirectProduct.inl y.left)) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact h_in_N₀
    rw [h_first_one, one_mul]
    have h_right_eq : y.right = (Multiplicative.ofAdd (1 : ℤ)) ^ y.right.toAdd := by
      conv_lhs => rw [← ofAdd_toAdd y.right]
      rw [← ofAdd_zsmul]; congr 1; simp
    rw [h_right_eq, map_zpow (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ),
      map_zpow (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
      map_zpow (QuotientGroup.mk' N₀)]
    exact Subgroup.zpow_mem_zpowers _ _
  · -- g^m = ι a.
    -- g^m = mk' K (inr (ofAdd m)). (ι a : G) = mk' K (inl a).
    -- (inr (ofAdd m))⁻¹ * inl a = (a, ofAdd(-m)) = cExt⁻¹ ∈ K (using σ^k a = a ∀ k).
    have h_iota_a : (ι a : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl a) := rfl
    rw [h_iota_a]
    have h_g_pow : (g ^ m : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))) := by
      change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) ^ m = _
      rw [← map_pow]; congr 1
      rw [← map_pow]; congr 1
      rw [← ofAdd_nsmul]; congr 1; simp
    rw [h_g_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hσa_zpow : ∀ k : ℤ, (σ ^ k) a = a := fun k =>
      Subgroup.zpow_mem (MulAction.stabilizer (MulAut N) a)
        (MulAction.mem_stabilizer_iff.mpr hσa) k
    have h_eq_inv : (SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ))
        : CyclicExtPreG N σ)⁻¹ * SemidirectProduct.inl a = (cyclicExtK m a σ)⁻¹ := by
      apply SemidirectProduct.ext
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).left = (cyclicExtK m a σ)⁻¹.left
        unfold cyclicExtK
        simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
          SemidirectProduct.inv_right, cyclicExtPhi_apply]
      · change ((SemidirectProduct.inr (Multiplicative.ofAdd (m : ℤ)))⁻¹ *
            SemidirectProduct.inl a : CyclicExtPreG N σ).right = (cyclicExtK m a σ)⁻¹.right
        unfold cyclicExtK
        simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
          SemidirectProduct.right_inl, SemidirectProduct.right_inr, one_mul, mul_one]
    rw [h_eq_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · -- Conjugation: g · ι x · g⁻¹ = ι (σ x) via SemidirectProduct.inl_aut.
    intro x
    have h_iota_x : (ι x : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl x) := rfl
    have h_iota_σx : (ι (σ x) : G) = QuotientGroup.mk' (cyclicExtKSubgroup m a σ)
        (SemidirectProduct.inl (σ x)) := rfl
    rw [h_iota_x, h_iota_σx]
    change (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)))) *
        (QuotientGroup.mk' _ (SemidirectProduct.inl x)) *
        (QuotientGroup.mk' _ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))))⁻¹ =
      QuotientGroup.mk' _ (SemidirectProduct.inl (σ x))
    rw [← map_inv (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ)),
        ← map_mul (QuotientGroup.mk' (cyclicExtKSubgroup m a σ))]
    congr 1
    -- Goal: inr (ofAdd 1) * inl x * (inr (ofAdd 1))⁻¹ = inl (σ x)
    have h_phi : (cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) = σ := by
      change σ ^ (Multiplicative.ofAdd (1 : ℤ)).toAdd = σ
      exact zpow_one σ
    have h_inl_aut : (SemidirectProduct.inl ((cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x)
        : CyclicExtPreG N σ) =
        SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) * SemidirectProduct.inl x *
          SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))⁻¹ :=
      SemidirectProduct.inl_aut (φ := cyclicExtPhi σ) (Multiplicative.ofAdd (1 : ℤ)) x
    rw [h_phi] at h_inl_aut
    rw [← (SemidirectProduct.inr : Multiplicative ℤ →* CyclicExtPreG N σ).map_inv] at *
    exact h_inl_aut.symm

end -- 3F

end OddOrder.Isaacs.Ch03

