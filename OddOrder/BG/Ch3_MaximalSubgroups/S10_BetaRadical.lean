/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure
import OddOrder.BG.Ch3_MaximalSubgroups.S10_ForwardFromKeystone
import OddOrder.BG.Ch1_Preliminary.PLengthTransfer

/-!
# BG §10 β-radical spine (Thm 10.6/10.7/10.8, Cor 10.9, Prop 10.10/10.14)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §10。
直列スパイン: `proper_hasPLengthOne` (10.6) → `sylow_structure` (10.7) → `isHall_Mbeta` (10.8)
→ `beta_global_structure` (Prop 10.14) → Cor 10.9 / Prop 10.10。Hall 構造 base
(`S10_HallStructure`) に依存。mmd `references/bg/local-analysis.mmd` L2779-2894。
-/

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorem 10.6 — proper subgroup は p-length one (mmd L2779) -/

/-- **BG Theorem 10.6** (mmd L2779): `p` prime、`H` を `G` の真部分群とすると、`H` は `p`-length
one を持つ。`M ∈ ℳ(H)` を取り `M` で示す: `r_p(M) ≤ 2` は Thm 4.18、`≥ 3` は Thm 10.2 +
Lem 6.3/10.4 + Thm 3.6。 -/
theorem proper_hasPLengthOne [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hH : H < ⊤) :
    Ch1.hasPLengthOne p ↥H := by
  classical
  -- Reduce to a maximal subgroup `M ⊇ H`: `p`-length one passes to subgroups (Lemma 1.21(a)).
  obtain ⟨M, hMco, hHM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH.ne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  suffices hMpl : Ch1.hasPLengthOne p ↥M by
    exact Ch1.hasPLengthOne_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHM)
      (Ch1.hasPLengthOne_subgroup hMpl (H.subgroupOf M))
  by_cases hpα : p ∈ alpha M
  · -- `r_p(M) ≥ 3` branch (`p ∈ α(M)`): the representation-theory keystone (BG Theorem 3.6).
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
    have hp_dvd_M : p ∣ Nat.card ↥M :=
      (Nat.mem_primeFactors.mp (alpha_subset_primeFactors M hpα)).2.1
    haveI hMnt : Nontrivial ↥M := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hp_dvd_M)
    -- `N := M_α` viewed inside `↥M`: a normal Hall `α(M)`-subgroup.
    set N : Subgroup ↥M := (Malpha M).subgroupOf M with hN_def
    haveI hNnorm : N.Normal := by rw [hN_def]; infer_instance
    have hHallN : Ch03.IsHallSubgroup (alpha M) N := by
      rw [hN_def]; exact Malpha_subgroupOf_isHall_of_isHall (Malpha_isHall hG hM)
    have hcoprime : Nat.Coprime (Nat.card ↥N) N.index := hHallN.coprime_index
    -- `N ≤ ↥M'` (Theorem 10.2: `M_α ⊆ M_σ ⊆ M'`); and `↥M'` is proper (solvable, nontrivial).
    have hN_der : N ≤ commutator ↥M := by
      have h1 : Malpha M ≤ derivedInG M :=
        (Malpha_le_Msigma hG hM).trans (Msigma_le_derived hG hM)
      rw [derivedInG] at h1
      rw [hN_def, Subgroup.subgroupOf]
      calc (Malpha M).comap M.subtype
          ≤ ((commutator ↥M).map M.subtype).comap M.subtype := Subgroup.comap_mono h1
        _ = commutator ↥M :=
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
    have hN_lt : N < ⊤ :=
      lt_of_le_of_lt hN_der (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M))
    -- `p ∣ |N|` (Hall + `p ∈ α(M)`), hence `M_α ≠ 1`.
    have hp_dvd_N : p ∣ Nat.card ↥N := by
      have hp_prod : p ∣ Nat.card ↥N * N.index := by
        rw [Subgroup.card_mul_index]; exact hp_dvd_M
      rcases (Nat.Prime.dvd_mul Fact.out).mp hp_prod with h | h
      · exact h
      · exact absurd hpα (hHallN.index_no_pi p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, h, Subgroup.index_ne_zero_of_finite⟩))
    have hMα_ne : Malpha M ≠ ⊥ := by
      intro hbot
      have hN_bot : N = ⊥ := by rw [hN_def, hbot]; simp
      rw [hN_bot, Subgroup.card_bot] at hp_dvd_N
      exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hp_dvd_N)
    -- Schur–Zassenhaus: a complement `K` to `N` in `↥M`; `K ≠ ⊥` (else `N = ⊤`).
    obtain ⟨K, hKcompl⟩ := Subgroup.exists_right_complement'_of_coprime hcoprime
    have hK_ne : K ≠ ⊥ := by
      intro hKbot
      have hsup := hKcompl.isCompl.sup_eq_top
      rw [hKbot, sup_bot_eq] at hsup
      exact hN_lt.ne hsup
    -- Choose a prime `q ∈ π(K/K')` (`K` is solvable and nontrivial, hence not perfect).
    haveI hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne
    haveI hKsolv : IsSolvable ↥K := solvable_of_solvable_injective K.subtype_injective
    have hidx_ne1 : (commutator ↥K).index ≠ 1 := fun h =>
      (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)).ne
        (Subgroup.index_eq_one.mp h)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hidx_ne1
    have hqK' : q ∈ ((commutator ↥K).index).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Subgroup.index_ne_zero_of_finite⟩
    -- Lemma 10.4(b): an order-`q` element `x ∈ K` with `C_{M_α}(⟨x⟩)` a `Z`-group.
    obtain ⟨x, hxK, hxord, hxZ⟩ :=
      exists_prime_orderOf_zgroupCentralizer_of_complement hG hM hMα_ne hKcompl hq hqK'
    -- Theorem 3.6: `⁅N, K⁆` has `p`-length one (with `R₀ = ⟨x⟩`).
    have hR₀le : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hR₀prime : (Nat.card ↥(Subgroup.zpowers x)).Prime := by
      rw [Nat.card_zpowers, hxord]; exact hq
    have hpl_comm : Ch1.hasPLengthOne p ↥⁅N, K⁆ :=
      pLengthOne_commutator_of_zgroupCentralizer hMsolv hoddM hNnorm hcoprime hKcompl
        hR₀le hR₀prime hxZ p
    -- Lemma 6.3(a): `⁅N, K⁆ = N` (since `N ≤ ↥M'`).
    rw [Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator hKcompl hN_der] at hpl_comm
    -- Lift `N`'s `p`-length one to `↥M` along the `p'`-quotient `↥M/N` (`p ∈ α(M)`).
    have hquot : ¬ p ∣ Nat.card (↥M ⧸ N) := fun hdvd => hHallN.index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpα
    exact Ch1.hasPLengthOne_of_normal_pPrime_quotient hquot hpl_comm
  · -- `r_p(M) ≤ 2` branch (`p ∉ α(M)`): BG Theorem 4.18 (landed).
    exact maximal_hasPLengthOne_of_not_mem_alpha hG hM hpα
/-! ## Corollary 10.7 — Sylow `p`-部分群の構造 (mmd L2787) -/

/-- **BG Corollary 10.7** (mmd L2787): `p` prime, `P ∈ Syl_p(G)`。
(a) `V` を `N_G(P)` 内の `P` の補群 (`P⊓V=1`, `P⊔V=N_G(P)`) とすると `P=[P,V]⊆N_G(P)'`;
(b) `r(P)≤2` ⇒ `P` abelian、または `P` は位数 `p³` exp `p` の nonabelian `P₁` と cyclic `P₂`
  (`Ω₁(P₂)=Z(P₁)`) の central product;
(c) `Q⊆P`, `Q^x⊆P` ⇒ `Q^x=Q^y` (`y∈N_G(P)`);
(d) 任意の `Q≤P` で `N_P(Q)` (= `N_G(Q)⊓P`) は `N_G(Q)` の Sylow `p`-部分群;
(e) `R` `p`-部分群, `Q⊆P∩R`, `Q⊴N_G(P)` (= `N_G(P)≤N_G(Q)`) ⇒ `Q⊴N_G(R)`。 -/
theorem sylow_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    (∀ V : Subgroup G, V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) ⊓ V = ⊥ →
      (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) = ⁅(P : Subgroup G), V⁆ ∧
        (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G))) ∧
    (rank ↥(P : Subgroup G) ≤ 2 →
      IsMulCommutative (P : Subgroup G) ∨
      ∃ P₁ P₂ : Subgroup G, P₁ ≤ (P : Subgroup G) ∧ P₂ ≤ (P : Subgroup G) ∧
        IsExpPExtraspecial p ↥P₁ ∧ Nat.card ↥P₁ = p ^ 3 ∧ IsCyclic ↥P₂ ∧
        (Omega ↥P₂ p 1).map P₂.subtype = (Subgroup.center ↥P₁).map P₁.subtype ∧
        IsCentralProduct (P : Subgroup G) P₁ P₂) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) → ∀ x : G, MulAut.conj x • Q ≤ (P : Subgroup G) →
      ∃ y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), MulAut.conj x • Q = MulAut.conj y • Q) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) →
      ∃ S : Sylow p ↥(Subgroup.normalizer (Q : Set G)),
        (S : Subgroup ↥(Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype =
          Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G)) ∧
    (∀ R Q : Subgroup G, IsPGroup p ↥R → Q ≤ (P : Subgroup G) ⊓ R →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.normalizer (Q : Set G) →
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G)) := by
  sorry

/-- **Narrowness of Sylow `p` of `M` for `p ∈ π(M) - β(M)`** (BG Lemma 10.8 setup, mmd L2812):
if `p ∈ π(M)` and `p ∉ β(M)`, then every Sylow `p`-subgroup of `M` is narrow.

If `p ∉ α(M)` then `r_p(M) ≤ 2`, so the Sylow has rank `≤ 2` and is narrow directly. If
`p ∈ α(M) ⊆ σ(M)`, then a Sylow `p`-subgroup of `M` *is* a Sylow `p`-subgroup of `G`
(`isSylow_sylowMap_of_mem_sigma`: no normalizer growth out of `M`); and `p ∈ α(M)` with
`p ∉ β(M)` forces `¬ idealPrime p G`, which (with `r_p(G) ≥ 3`) means some — hence every, by
conjugacy — Sylow `p`-subgroup of `G` has a maximal elementary abelian subgroup of order `p²`,
i.e. is narrow (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`). -/
private theorem isNarrow_sylow_of_not_mem_beta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M) (P : Sylow p ↥M) :
    IsNarrow p ↥(P : Subgroup ↥M) := by
  have hp_prime : p.Prime := Fact.out
  have hp_odd : Odd p := hG.odd.of_dvd_nat (dvd_trans (Nat.mem_primeFactors.mp hpπ).2.1
    (Subgroup.card_subgroup_dvd_card M))
  by_cases hpα : p ∈ alpha M
  · -- `p ∈ α(M) ⊆ σ(M)`: the Sylow of `M` is a Sylow of `G`, narrow from `¬ idealPrime`.
    have hpσ : p ∈ sigma M := alpha_subset_sigma hG hM hpα
    have h3M : 3 ≤ pRank ↥M p := ((mem_alpha_iff M p).mp hpα).2
    have h3G : 3 ≤ pRank G p := le_trans h3M (pRank_le_of_injective M.subtype_injective)
    -- `S` is a Sylow `p`-subgroup of `G` isomorphic to `P`.
    obtain ⟨S, hS_eq⟩ := isSylow_sylowMap_of_mem_sigma hpσ P
    have ePS : ↥(P : Subgroup ↥M) ≃* ↥(S : Subgroup G) :=
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr hS_eq.symm)
    -- `¬ idealPrime p G` (else `p ∈ β(M)`).
    have hnotideal : ¬ idealPrime p G := fun hideal => hpβ ⟨hpα, hideal⟩
    -- `¬ idealPrime` with `3 ≤ pRank G p` yields a narrow Sylow `Q` of `G`.
    rw [mem_idealPrime_iff, not_and_or] at hnotideal
    rcases hnotideal with h3 | hQex
    · exact absurd h3G h3
    · push_neg at hQex
      obtain ⟨Q, A, hAcard, hAmax⟩ := hQex
      have h3Q : 3 ≤ pRank ↥(Q : Subgroup G) p := by rw [pRank_sylow_eq Q]; exact h3G
      have hQnarrow : IsNarrow p ↥(Q : Subgroup G) :=
        (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp_odd Q.2 h3Q).mpr
          ⟨A, hAcard, hAmax⟩
      -- Transfer narrowness `Q → S` (conjugate Sylows) then `S → P`.
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
      have hgeq : MulAut.conj g • (Q : Subgroup G) = (S : Subgroup G) := by
        rw [← Sylow.coe_subgroup_smul, hg]
      have eQS : ↥(Q : Subgroup G) ≃* ↥(S : Subgroup G) :=
        (Subgroup.equivSMul (MulAut.conj g) (Q : Subgroup G)).trans
          (MulEquiv.subgroupCongr hgeq)
      exact IsNarrow.of_mulEquiv ePS.symm (IsNarrow.of_mulEquiv eQS hQnarrow)
  · -- `p ∉ α(M)`: `r_p(M) ≤ 2`, so the Sylow has rank `≤ 2`.
    have hr2 : pRank ↥M p ≤ 2 := by
      by_contra h
      exact hpα ⟨hpπ, by omega⟩
    exact isNarrow_of_pRank_le_two (by rw [pRank_sylow_eq P]; exact hr2)

/-- **`HasNormalPComplement` is invariant under group isomorphism.** Transport the normal
complement `N` to `N.map e`; each Sylow `Q` of the target pulls back along `e` to a Sylow of the
source, where it complements `N`, and the cardinalities/coprimality transfer. (Public form of the
private helper in `S7B2_NormalJ_PComplement`; needed to move `HasNormalPComplement` between
`↥(commutator ↥M)` and `↥(derivedInG M)`.) -/
theorem hasNormalPComplement_of_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime] (e : A ≃* B)
    (hA : Ch05.HasNormalPComplement p A) : Ch05.HasNormalPComplement p B := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hA
  refine ⟨N.map e.toMonoidHom, Subgroup.Normal.map hN_normal _ e.surjective, fun Q => ?_⟩
  have h_range_top : (e.toMonoidHom).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hQ_le_range : (Q : Subgroup B) ≤ (e.toMonoidHom).range := by rw [h_range_top]; exact le_top
  let Q' : Sylow p A := Q.comapOfInjective e.toMonoidHom e.injective hQ_le_range
  have hQ'_compl : Subgroup.IsComplement' N (Q' : Subgroup A) := hN_compl Q'
  have hQ'_eq : (Q' : Subgroup A) = (Q : Subgroup B).comap e.toMonoidHom := by
    simp [Q', Sylow.coe_comapOfInjective]
  have hQ_map : (Q' : Subgroup A).map e.toMonoidHom = (Q : Subgroup B) := by
    rw [hQ'_eq, Subgroup.map_comap_eq, h_range_top, top_inf_eq]
  have hG_card : Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
  have hN_card : Nat.card (N.map e.toMonoidHom : Subgroup B) = Nat.card N :=
    (Nat.card_congr (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).toEquiv).symm
  have hQ_card : Nat.card (Q : Subgroup B) = Nat.card (Q' : Subgroup A) := by
    rw [← hQ_map]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
  have h_card_eq : Nat.card N * Nat.card (Q' : Subgroup A) = Nat.card A := hQ'_compl.card_mul_card
  have h_card_H : Nat.card (N.map e.toMonoidHom : Subgroup B) * Nat.card (Q : Subgroup B) =
      Nat.card B := by rw [hN_card, hQ_card, h_card_eq, hG_card]
  have hp_ndvd_N : ¬ p ∣ Nat.card N := by
    rw [← hQ'_compl.index_eq_card]; exact Q'.not_dvd_index
  obtain ⟨k, hQ'_pow⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
  have hp_prime : p.Prime := Fact.out
  have h_coprime' : Nat.Coprime (Nat.card N) (Nat.card (Q' : Subgroup A)) := by
    rw [hQ'_pow]; exact ((hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
  have h_coprime : Nat.Coprime (Nat.card (N.map e.toMonoidHom : Subgroup B))
      (Nat.card (Q : Subgroup B)) := by rw [hN_card, hQ_card]; exact h_coprime'
  exact Subgroup.isComplement'_of_coprime h_card_H h_coprime

/-- **BG Lemma 10.8(c) — normal `p`-complements** (mmd L2812), forward-conditional on the keystone
(via Theorem 10.6): for `p ∈ π(M) - β(M)`, both `M'` and `M_σ` have normal `p`-complements.

A Sylow `p`-subgroup of `M` is narrow (`isNarrow_sylow_of_not_mem_beta`) and `M` has `p`-length
one (Theorem 10.6 — `proper_hasPLengthOne`), so Theorem 5.6(c)
(`narrow_sylow_solvable_structure`) gives a normal `p`-complement for `↥(commutator ↥M)`;
transport it to `↥(derivedInG M)` by isomorphism, and inherit it for `↥(Msigma M)`
(`Msigma ⊆ M'`, `hasNormalPComplement_of_subgroup`). -/
theorem derived_msigma_hasNormalPComplement_of_not_mem_beta [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ}
    [Fact p.Prime] (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M) :
    Ch05.HasNormalPComplement p ↥(derivedInG M) ∧ Ch05.HasNormalPComplement p ↥(Msigma M) := by
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hp_dvd : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπ).2.1
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1
  -- Some Sylow `p`-subgroup of `M`, narrow; `M` has `p`-length one (Theorem 10.6).
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  have hPnarrow : IsNarrow p ↥(P : Subgroup ↥M) := isNarrow_sylow_of_not_mem_beta hG hM hpπ hpβ P
  have hpl : 3 ≤ pRank ↥(P : Subgroup ↥M) p → Ch1.hasPLengthOne p ↥M :=
    fun _ => proper_hasPLengthOne hG M hM_lt
  -- Theorem 5.6(c): `↥(commutator ↥M)` has a normal `p`-complement.
  have hNPC_comm : Ch05.HasNormalPComplement p ↥(commutator ↥M) :=
    (Ch1.S05.narrow_sylow_solvable_structure hoddM hp_dvd P hPnarrow hpl).2.2.1
  -- Transport to `↥(derivedInG M) = ↥((commutator ↥M).map M.subtype)`.
  have hNPC_der : Ch05.HasNormalPComplement p ↥(derivedInG M) :=
    hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective) hNPC_comm
  refine ⟨hNPC_der, ?_⟩
  -- `M_σ ⊆ M'`: inherit the complement, then transport to `↥(Msigma M)`.
  have hMσ_le : Msigma M ≤ derivedInG M := Msigma_le_derived hG hM
  exact hasNormalPComplement_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσ_le)
    (Ch05.hasNormalPComplement_of_subgroup hNPC_der ((Msigma M).subgroupOf (derivedInG M)))

/-! ## Lemma 10.8 — `M_β` の Hall 性 (mmd L2810) -/

/-- **BG Lemma 10.8** (mmd L2810): `M ∈ ℳ`。
(a) `M_β` は `M` および `G` の Hall 部分群;
(b) `M'` と `M_σ` は nilpotent な Hall `β(M)'`-部分群を持つ;
(c) `p ∈ π(M)−β(M)` ⇒ `M'` と `M_σ` は normal `p`-complement を持つ (`M_β` を含む)。
(原典 (c) はさらに「`p` は `|M/O_{p'}(M)|` の最大素因子」を含む — quotient 型整備後に追加予定。) -/
theorem isHall_Mbeta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (beta M) (Mbeta M) ∧
    (∃ W : Subgroup G, W ≤ derivedInG M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (derivedInG M)) ∧
      Group.IsNilpotent ↥W) ∧
    (∃ W : Subgroup G, W ≤ Msigma M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (Msigma M)) ∧ Group.IsNilpotent ↥W) ∧
    (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥M).primeFactors → p ∉ beta M →
      Ch05.HasNormalPComplement p ↥(derivedInG M) ∧
      Ch05.HasNormalPComplement p ↥(Msigma M)) := by
  sorry

/-! ## Proposition 10.14 — β(G)-prime の global 構造 (mmd L2894) -/

/-- **Cyclic uniqueness by order**: in a finite cyclic group, two subgroups of equal
cardinality coincide. (Each order-`d` subgroup equals the unique order-`d` kernel
`(powMonoidHom d).ker`; this is the order-`d` generalisation of the order-`p` argument in
`OddOrder.BG.Ch1_Preliminary.S04`.) Used in Prop 10.14(c): a subgroup of the cyclic `N_P(X)`
is characteristic. -/
private theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {K L : Subgroup C} (h : Nat.card K = Nat.card L) : K = L := by
  letI : CommGroup C := IsCyclic.commGroup
  -- Each order-`d` subgroup `M` equals the unique order-`d` kernel `(powMonoidHom d).ker`.
  have key : ∀ {M : Subgroup C} {d : ℕ}, Nat.card M = d → M = (powMonoidHom d : C →* C).ker := by
    intro M d hM
    have hM_le : M ≤ (powMonoidHom d : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    have hd_dvd : d ∣ Nat.card C := hM ▸ M.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom d : C →* C).ker = d := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd_dvd]
    exact Subgroup.eq_of_le_of_card_ge hM_le (by rw [hker_card, hM])
  exact (key (d := Nat.card K) rfl).trans (key (d := Nat.card K) h.symm).symm

/-- **Monotonicity of `𝒰` under inclusion within a proper subgroup** (the fiddly lemma of
Prop 10.14(b)): if `A ∈ 𝒰`, `A ≤ R`, and `R` is proper, then `R ∈ 𝒰`. The unique maximal
`M ⊇ A` is the unique maximal `⊇ R`: any coatom `⊇ R` also `⊇ A`, hence equals it; and `R`
proper lies in some coatom (`IsCoatomic`). -/
private theorem isUniquelyMaximal_of_le [Finite G] {A R : Subgroup G}
    (hA : IsUniquelyMaximal A) (hAR : A ≤ R) (hR : R < ⊤) : IsUniquelyMaximal R := by
  obtain ⟨_, M, ⟨hMc, _⟩, hMu⟩ := hA
  refine ⟨hR, M, ?_, ?_⟩
  · -- `M` is a coatom containing `R`: it contains some coatom `⊇ R`, which `⊇ A`, hence `= M`.
    obtain ⟨N, hNc, hRN⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom R).resolve_left hR.ne
    have hNeqM : N = M := hMu N ⟨hNc, hAR.trans hRN⟩
    exact ⟨hNeqM ▸ hNc, hNeqM ▸ hRN⟩
  · -- Uniqueness: any coatom `⊇ R` also `⊇ A`, so equals `M`.
    intro N hN
    exact hMu N ⟨hN.1, hAR.trans hN.2⟩

/-- A finite cyclic group has `rank ≤ 1`: any elementary abelian `q`-subgroup `A` is cyclic
(subgroup of cyclic), so its exponent equals its order and divides `q`, whence `|A| ≤ q` and
`log_q |A| ≤ 1`. Contrapositive used in Prop 10.14(b): `2 ≤ rank ↥R ⇒ R` noncyclic. -/
private theorem rank_le_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    rank C ≤ 1 := by
  rw [rank_le_iff]
  intro q hq
  rw [pRank_le_iff]
  intro A hA
  -- `A` is cyclic, elementary abelian `q`, so `|A| = exponent A ∣ q`, hence `|A| ≤ q`.
  haveI : IsCyclic ↥A := Subgroup.isCyclic A
  have hexp : Monoid.exponent ↥A ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => hA.pow_eq_one g)
  rw [IsCyclic.exponent_eq_card (α := ↥A)] at hexp
  have hcard_le : Nat.card ↥A ≤ q := Nat.le_of_dvd hq.pos hexp
  calc Nat.log q (Nat.card ↥A) ≤ Nat.log q q := Nat.log_mono_right hcard_le
    _ = 1 := by simpa using (Nat.log_pow hq.one_lt 1)

/-- **BG Proposition 10.14 (a)(b)(c)** (mmd L2894): `p` ideal (`p ∈ β(G)`), `P ∈ Syl_p(G)`。
(a) `ℰ_p²(G) ∩ ℰ_p*(G) = ∅`; (b) `p`-部分群 `R` で `r(R) ≥ 2` なら `R ∈ 𝒰`;
(c) 任意の `X ≤ P` で `N_P(X) ∈ 𝒰`。(原典 (d) は
`normalizer_le_of_nontrivial_beta_subgroup` として別 theorem に露出。)

Proof: (a) `A ∈ ℰ²(G) ∩ ℰ*(G)` ⇒ `A ≤ Q` for some Sylow `Q` (`exists_le_sylow`), `A.subgroupOf Q`
maximal-elem-ab of order `p²` in `↥Q`, contradicting `idealPrime`. (b) `2 ≤ rank ↥R` ⇒ `R`
noncyclic ⇒ `A ∈ ℰ²(R)` (S04), not maximal by (a), so `A ∈ 𝒰` by §9's
`isUniquelyMaximal_of_mem_e2_not_maximal` (Uniqueness Theorem — cited), lifted to `R` by
`isUniquelyMaximal_of_le`. (c) `Q = N_P(X)`: if `r(Q) ≥ 2` use (b); else `Q` cyclic, `X char Q`
(cyclic uniqueness), `N_P(Q) ⊆ N_P(X) = Q`, so `Q = P` by the nilpotent normalizer condition,
contradicting `3 ≤ pRank G p ≤ rank ↥P`. -/
theorem beta_global_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hp : idealPrime p G) (P : Sylow p G) :
    (¬ ∃ A : Subgroup G, A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A) ∧
    (∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R) ∧
    (∀ X : Subgroup G, X ≤ (P : Subgroup G) →
      IsUniquelyMaximal (Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G))) := by
  obtain ⟨hpRank3, hpIdeal⟩ := hp
  have hp_prime : p.Prime := Fact.out
  -- `p ∣ |G|` (from `pRank G p ≥ 3 > 0`), hence `p` is odd.
  have hp_odd : Odd p := by
    -- `¬ pRank G p ≤ 0` gives an elem-ab `A` with `1 ≤ log_p |A|`, so `p ≤ |A|`.
    have hnle : ¬ pRank G p ≤ 0 := by omega
    rw [pRank_le_iff] at hnle
    simp only [not_forall, not_le] at hnle
    obtain ⟨A, hA_elem, hAlog⟩ := hnle
    have hp_le_A : p ≤ Nat.card ↥A := by
      have h1 : 1 ≤ Nat.log p (Nat.card ↥A) := by omega
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ Nat.card ↥A := Nat.pow_le_of_le_log Nat.card_pos.ne' h1
    have hp_dvd_A : p ∣ Nat.card ↥A := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).mp hA_elem.isPGroup
      have hjpos : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · rw [hj, hj0, pow_zero] at hp_le_A
          exact absurd hp_le_A (by have := hp_prime.one_lt; omega)
        · exact hjpos
      rw [hj]; exact dvd_pow_self p (by omega : j ≠ 0)
    have hp_dvd_G : p ∣ Nat.card G := hp_dvd_A.trans A.card_subgroup_dvd_card
    exact hG.odd.of_dvd_nat hp_dvd_G
  -- ===== Part (a) =====
  have partA : ¬ ∃ A : Subgroup G,
      A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A := by
    rintro ⟨A, hA2, hAmax⟩
    rw [mem_elemAbelianOfRank] at hA2
    obtain ⟨hA_elem, hA_card⟩ := hA2
    -- `A` is a `p`-group, land it in a Sylow `Q`.
    obtain ⟨Q, hAQ⟩ := hA_elem.isPGroup.exists_le_sylow
    -- `A.subgroupOf Q` has order `p²` and is maximal-elem-ab in `↥Q`, contradicting `idealPrime`.
    refine hpIdeal Q ⟨A.subgroupOf (Q : Subgroup G), ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective (Q : Subgroup G).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hAQ, hA_card]
    · refine ⟨?_, ?_⟩
      · apply Subgroup.IsElementaryAbelian.of_map (f := (Q : Subgroup G).subtype)
          (Q : Subgroup G).subtype_injective
        rwa [Subgroup.map_subgroupOf_eq_of_le hAQ]
      · intro F' hF'_elem hF'_ge
        -- map `F' ≤ ↥Q` to `G`; it is elem-ab, ⊇ `A`, so `= A` by `G`-maximality.
        have hF_elem : (F'.map (Q : Subgroup G).subtype).IsElementaryAbelian p :=
          hF'_elem.map (Q : Subgroup G).subtype_injective
        have hAF : A ≤ F'.map (Q : Subgroup G).subtype := by
          calc A = (A.subgroupOf (Q : Subgroup G)).map (Q : Subgroup G).subtype :=
                (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
            _ ≤ F'.map (Q : Subgroup G).subtype := Subgroup.map_mono hF'_ge
        have hFeqA : F'.map (Q : Subgroup G).subtype = A := hAmax.2 _ hF_elem hAF
        -- inject back: `F' = A.subgroupOf Q`.
        have := hFeqA.trans (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
        exact Subgroup.map_injective (Q : Subgroup G).subtype_injective this
  -- ===== Part (b) =====
  have partB : ∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R := by
    intro R hR_pg hR_rank
    -- `2 ≤ rank ↥R` ⇒ `R` noncyclic ⇒ `R` has `E ∈ ℰ²(↥R)` (S04).
    have hR_nc : ¬ IsCyclic ↥R := by
      intro hRc
      haveI := hRc
      have : rank ↥R ≤ 1 := rank_le_one_of_isCyclic (C := ↥R)
      omega
    obtain ⟨E, hE_elem, hE_card⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        hR_pg hp_odd hR_nc
    -- map `E ≤ ↥R` to `A ≤ R` in `G`.
    set A : Subgroup G := E.map R.subtype with hA_def
    have hAR : A ≤ R := Subgroup.map_subtype_le E
    have hA_elem : A.IsElementaryAbelian p :=
      hE_elem.map R.subtype_injective
    have hA_card : Nat.card ↥A = p ^ 2 := by
      rw [hA_def, Subgroup.card_map_of_injective R.subtype_injective, hE_card]
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by
      rw [mem_elemAbelianOfRank]; exact ⟨hA_elem, hA_card⟩
    -- By (a), `A` is not maximal-elem-ab, so `A ∈ 𝒰` (§9 Uniqueness Theorem corollary).
    have hAns : ¬ IsMaximalElementaryAbelian p A := fun hAmax => partA ⟨A, hA2, hAmax⟩
    have hAU : IsUniquelyMaximal A :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
    -- `R` is proper (`R = ⊤` ⇒ `G` is a solvable `p`-group, contradiction), so lift `A ∈ 𝒰`.
    have hR_lt : R < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hRtop
      have hGpg : IsPGroup p G :=
        hR_pg.of_equiv (hRtop ▸ Subgroup.topEquiv : (↥R : Type _) ≃* G)
      haveI : Group.IsNilpotent G := hGpg.isNilpotent
      exact hG.notSolvable inferInstance
    exact isUniquelyMaximal_of_le hAU hAR hR_lt
  -- ===== Part (c) =====
  refine ⟨partA, partB, ?_⟩
  intro X hXP
  set Q : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G) with hQ_def
  -- `Q ≤ P`, so `Q` is a `p`-group.
  have hQP : Q ≤ (P : Subgroup G) := inf_le_right
  have hQ_pg : IsPGroup p ↥Q :=
    P.2.of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP)
  by_cases hrank : 2 ≤ rank ↥Q
  · exact partB Q hQ_pg hrank
  · -- `rank ↥Q ≤ 1`; derive a contradiction (`Q = P` but `rank ↥P ≥ 3`).
    exfalso
    -- `Q` is cyclic: else it has an `E_{p²}`, forcing `rank ↥Q ≥ 2`.
    have hQ_cyclic : IsCyclic ↥Q := by
      by_contra hQnc
      obtain ⟨E, hE_elem, hE_card⟩ :=
        OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
          hQ_pg hp_odd hQnc
      have : 2 ≤ pRank ↥Q p := pow_le_card_of_le_pRank E hE_elem hE_card
      have : 2 ≤ rank ↥Q := le_trans this (pRank_le_rank p)
      omega
    -- `X ≤ Q` (`X` normalizes itself and `X ≤ P`).
    have hXQ : X ≤ Q := by
      rw [hQ_def, le_inf_iff]
      exact ⟨Subgroup.le_normalizer, hXP⟩
    -- `N_G(Q) ⊓ P ≤ Q`: any `g ∈ P` normalizing `Q` normalizes the characteristic `X`.
    have hself : Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G) ≤ Q := by
      rintro g ⟨hgN, hgP⟩
      rw [hQ_def, Subgroup.mem_inf]
      refine ⟨?_, hgP⟩
      -- `g` normalizes `Q`: `∀ n, n ∈ Q ↔ g n g⁻¹ ∈ Q`.
      have hgN' : ∀ n, n ∈ (Q : Set G) ↔ g * n * g⁻¹ ∈ (Q : Set G) :=
        Subgroup.mem_set_normalizer_iff.mp hgN
      -- `X' = gXg⁻¹` is a subgroup of `Q` of order `|X|`, so `X' = X` (cyclic uniqueness in `↥Q`).
      set X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hX'_def
      have hX'Q : X' ≤ Q := by
        rw [hX'_def]
        rintro y ⟨x, hx, rfl⟩
        have hxQ : (x : G) ∈ (Q : Set G) := hXQ hx
        have : g * x * g⁻¹ ∈ (Q : Set G) := (hgN' x).mp hxQ
        simpa [MulAut.conj_apply] using this
      have hX'_card : Nat.card ↥X' = Nat.card ↥X := by
        rw [hX'_def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      -- Inside `↥Q`: the two `subgroupOf`s have equal card, hence are equal.
      have hsubOf_card : Nat.card ↥(X'.subgroupOf Q) = Nat.card ↥(X.subgroupOf Q) := by
        rw [← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hX'Q,
          ← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hXQ, hX'_card]
      have hsubOf_eq : X'.subgroupOf Q = X.subgroupOf Q :=
        cyclic_subgroup_eq_of_card_eq (C := ↥Q) hsubOf_card
      -- Map back along `Q.subtype`: `X' = X`.
      have hX'eqX : X' = X := by
        have hmap : (X'.subgroupOf Q).map Q.subtype = (X.subgroupOf Q).map Q.subtype :=
          congrArg (Subgroup.map Q.subtype) hsubOf_eq
        rwa [Subgroup.map_subgroupOf_eq_of_le hX'Q,
          Subgroup.map_subgroupOf_eq_of_le hXQ] at hmap
      -- `X.map (conj g) = X` gives `g h g⁻¹ ∈ X ↔ h ∈ X`.
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : g * h * g⁻¹ ∈ X' := by
          rw [hX'_def, Subgroup.mem_map]
          exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
        rwa [hX'eqX] at this
      · intro hh
        rw [← hX'eqX, hX'_def, Subgroup.mem_map] at hh
        obtain ⟨x, hx, hxeq⟩ := hh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxeq
        -- `g * x * g⁻¹ = g * h * g⁻¹` ⇒ `x = h`.
        have hxh : x = h := by
          have h1 : g * x = g * h := mul_right_cancel hxeq
          exact mul_left_cancel h1
        rwa [← hxh]
    -- `Q = P` by the nilpotent normalizer condition.
    have hQeqP : Q = (P : Subgroup G) := by
      by_contra hQne
      have hQlt : Q < (P : Subgroup G) := lt_of_le_of_ne hQP hQne
      haveI : Group.IsNilpotent ↥(P : Subgroup G) := P.2.isNilpotent
      have hNC : NormalizerCondition ↥(P : Subgroup G) :=
        normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))
      have hQsub_lt : Q.subgroupOf (P : Subgroup G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        rw [Subgroup.subgroupOf_eq_top] at htop
        exact hQne (le_antisymm hQP htop)
      obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hQsub_lt)
      rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at ht_norm
      rw [Subgroup.mem_subgroupOf] at ht_not
      -- `↑t ∈ N_G(Q) ⊓ P ≤ Q`, so `↑t ∈ Q`, contradicting `t ∉ Q.subgroupOf P`.
      exact ht_not (hself ⟨ht_norm, t.2⟩)
    -- But `rank ↥P ≥ 3 > 1 ≥ rank ↥Q = rank ↥P`.
    have hPrank : 3 ≤ rank ↥(P : Subgroup G) :=
      le_trans (le_trans hpRank3 (pRank_le_pRank_sylow P)) (pRank_le_rank p)
    rw [hQeqP] at hrank
    omega

/-! ## Proposition 10.14(d) — nontrivial `β(M)`-subgroup normalizers (mmd L2894) -/

/-- **BG Proposition 10.14(d)** (mmd L2894): `M ∈ ℳ` とし、`Y` を `M` の非自明
`β(M)`-部分群とする。このとき `N_G(Y) ⊆ M`。

This is the §13-facing clause used in Lemma 13.8 and Theorem 13.10. The proof is still a
§10 proof gate: BG chooses a prime `q ∈ π(F(Y))`, reduces to `q ∈ β(M)`, applies
Proposition 10.14(c) to `O_q(Y)`, and then obtains the ambient normalizer containment.
It is intentionally exposed as a theorem, not hoisted into any downstream setup field. -/
theorem normalizer_le_of_nontrivial_beta_subgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYne : Y ≠ ⊥) (hYβ : Subgroup.IsPiSubgroup (beta M) Y) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  have hM_co : IsCoatom M := mem_maximalSubgroups.mp hM
  -- `↥Y` is finite, solvable and nontrivial, so `F(↥Y) ≠ 1` and `q ∣ |F(↥Y)|` for some prime `q`.
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hYsolv : IsSolvable ↥Y :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hYM)
  haveI hYnt : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  have hFne : Ch01.fitting ↥Y ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial ↥Y
  haveI hFnt : Nontrivial ↥(Ch01.fitting ↥Y) := (Subgroup.nontrivial_iff_ne_bot _).mpr hFne
  obtain ⟨q, hq_prime, hq_dvdF⟩ :=
    (Nat.card ↥(Ch01.fitting ↥Y)).exists_prime_and_dvd
      (by have := Finite.one_lt_card_iff_nontrivial.mpr hFnt; omega)
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- `q ∈ π(F(↥Y)) ⊆ π(Y)`, hence `q ∈ β(M)`: `idealPrime q G` and `q ∈ α(M) ⊆ σ(M)`.
  have hq_piY : q ∈ (Nat.card ↥Y).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvdF.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_subgroup_dvd_card _
  have hqβ : q ∈ beta M := hYβ q hq_piY
  rw [mem_beta_iff] at hqβ
  obtain ⟨hqα, hq_ideal⟩ := hqβ
  have hqσ : q ∈ sigma M := alpha_subset_sigma hG hM hqα
  -- `X := O_q(↥Y)` realised in `G`: a `q`-subgroup, `≤ Y ≤ M`, and characteristic in `Y`.
  set X : Subgroup G := opiCoreInG ({q} : Set ℕ) Y with hXdef
  have hX_pg : IsPGroup q ↥X := isPGroup_opiCoreInG_singleton Y
  have hXY : X ≤ Y := opiCoreInG_le _ _
  have hXM : X ≤ M := hXY.trans hYM
  -- `X ≠ ⊥`: a `q`-element of `F(↥Y)` lies in `O_q(↥Y)` (`mem_opCore_of_le_fitting`).
  have hXne : X ≠ ⊥ := by
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvdF
    set K : Subgroup ↥Y := (Subgroup.zpowers x).map (Ch01.fitting ↥Y).subtype with hKdef
    have hKcard : Nat.card ↥K = q := by
      rw [hKdef, Subgroup.card_map_of_injective (Ch01.fitting ↥Y).subtype_injective,
        Nat.card_zpowers, hx_ord]
    have hK_pg : IsPGroup q ↥K := by
      rw [IsPGroup.iff_card]; exact ⟨1, by rw [hKcard, pow_one]⟩
    have hK_fit : K ≤ Ch01.fitting ↥Y := Subgroup.map_subtype_le _
    have hK_op : K ≤ Ch01.opCore q ↥Y :=
      Ch02.mem_opCore_of_le_fitting_of_isPGroup hK_pg hK_fit
    have hop_ne : Ch01.opCore q ↥Y ≠ ⊥ := by
      intro hbot
      rw [hbot, le_bot_iff] at hK_op
      have h1 : Nat.card ↥K = 1 := by simp [hK_op]
      have := hq_prime.two_le
      omega
    have hbridge : X = (Ch01.opCore q ↥Y).map Y.subtype := by
      rw [hXdef, OddOrder.GroupTheory.opiCoreInG, Ch04.oPiCore_singleton_eq_opCore]
    rw [hbridge, Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
    exact hop_ne
  -- Land `X` in a Sylow `q`-subgroup `S` of `G` that lies in `M` (using `q ∈ σ(M)`).
  have hXMsub_pg : IsPGroup q ↥(X.subgroupOf M) :=
    hX_pg.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  obtain ⟨P, hXP⟩ := hXMsub_pg.exists_le_sylow
  obtain ⟨S, hS_eq⟩ := isSylow_sylowMap_of_mem_sigma hqσ P
  have hS_le_M : (S : Subgroup G) ≤ M := by rw [hS_eq]; exact Subgroup.map_subtype_le _
  have hXS : X ≤ (S : Subgroup G) := by
    rw [hS_eq, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXP
  -- Proposition 10.14(c): `N_G(X) ⊓ S` is uniquely maximal, with unique coatom `M`.
  obtain ⟨_, M', ⟨hM'co, _⟩, hM'uniq⟩ := (beta_global_structure hG hq_ideal S).2.2 X hXS
  have hcap_le_M : Subgroup.normalizer (X : Set G) ⊓ (S : Subgroup G) ≤ M :=
    le_trans inf_le_right hS_le_M
  have hM_eq : M = M' := hM'uniq M ⟨hM_co, hcap_le_M⟩
  -- `N_G(X)` is proper (else `X ⊴ G`, contradicting `G` simple with `⊥ ≠ X ≠ ⊤`).
  have hNX_lt : Subgroup.normalizer (X : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases (hG.simple).eq_bot_or_eq_top_of_normal X hXnormal with hb | ht
    · exact hXne hb
    · exact hM_co.1 (top_le_iff.mp (ht ▸ hXM))
  -- A coatom `C ⊇ N_G(X)` exists; it contains `N_G(X) ⊓ S`, so `C = M' = M`.
  obtain ⟨C, hCco, hNXC⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left
      hNX_lt.ne
  have hCeq : C = M' := hM'uniq C ⟨hCco, le_trans inf_le_left hNXC⟩
  -- `N_G(Y) ≤ N_G(X) ≤ C = M` (characteristic core normalizer).
  have hNYNX : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) (le_refl _)
  calc Subgroup.normalizer (Y : Set G)
      ≤ Subgroup.normalizer (X : Set G) := hNYNX
    _ ≤ C := hNXC
    _ = M := by rw [hCeq, ← hM_eq]

/-! ## Corollary 10.9 — β(M)'-部分群の centralization (mmd L2826) -/

/-- **BG Corollary 10.9 (a)(1)(2)** (mmd L2826): `M ∈ ℳ`, `p, q ∈ β(M)'` distinct, `X` を `M` の
`q`-部分群で `X ⊆ M'` または `p < q` とする。(1) `X` は `M_σ` の Sylow `p`-部分群を中心化する;
(2) `p ∈ α(M)` なら `C_M(X) ∈ 𝒰`。原典 (a)(3)/(b) は
`beta_complement_normalizer_derived_contains_sylow` と
`beta_factorization_of_sylow_normalizer_in_intersection` として別 theorem に露出。 -/
theorem beta_complement_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    {X : Subgroup G} (hXM : X ≤ M) (hXq : IsPGroup q ↥X)
    (hcase : X ≤ derivedInG M ∨ p < q) :
    (∃ S : Sylow p ↥(Msigma M),
      X ≤ Subgroup.centralizer
        (((S : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) : Set G)) ∧
    (p ∈ alpha M → IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M)) := by
  sorry

/-! ## Corollary 10.9(a)(3)/(b) — β(M)'-normalizer gates (mmd L2826) -/

/-- **BG Corollary 10.9(a)(3)** (mmd L2826): in the setup of Corollary 10.9(a), if `X` is a
Sylow `q`-subgroup of `M'`, then `N_M(X)'` contains a Sylow `p`-subgroup of `M'`.

Here `X` is represented as a Sylow subgroup of `↥(M')`, mapped back to the ambient group `G`,
and `N_M(X)` is encoded as `N_G(X) ∩ M`. -/
theorem beta_complement_normalizer_derived_contains_sylow [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    (X : Sylow q ↥(derivedInG M)) :
    ∃ S : Sylow p ↥(derivedInG M),
      ((S : Subgroup ↥(derivedInG M)).map (derivedInG M).subtype : Subgroup G) ≤
        derivedInG
          (Subgroup.normalizer
              (((X : Subgroup ↥(derivedInG M)).map (derivedInG M).subtype : Subgroup G) :
                Set G) ⊓
            M) := by
  sorry

/-- **BG Corollary 10.9(b)** (mmd L2826): if `H ∈ ℳ - {M}` and `N_G(S) ⊆ H ∩ M` for some
Sylow subgroup `S` of `G`, then `M = (H ∩ M)M_β` and `α(M)=β(M)`.

The product is encoded as subgroup join, matching the existing convention for normal-factor
statements in §12. -/
theorem beta_factorization_of_sylow_normalizer_in_intersection [Finite G]
    (hG : IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G) (hHM : H ≠ M)
    {q : ℕ} [Fact q.Prime] (S : Sylow q G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H ⊓ M) :
    M = (H ⊓ M) ⊔ Mbeta M ∧ alpha M = beta M := by
  sorry

/-! ## Proposition 10.10 — N_G(P) の分解 (mmd L2844) -/

/-- **BG Proposition 10.10 (a)(b)(c)** (mmd L2844): `p ≠ q`, `A ∈ ℰ_p²(G)∩ℰ_p*(G)`,
`Q ∈ ℋ_G*(A;q)`, `q ∈ π(C_G(A))`。すると `A ⊆ P` となるある `P ∈ Syl_p(G)` で、
(a) `N_G(P) = O_{p'}(C_G(P))·(N_G(P)∩N_G(Q))`; (b) `P ⊆ N_G(Q)'`;
(c) `Q` が cyclic または `ℰ²(Q)∩ℰ*(Q) ≠ ∅` なら `P` は `Q` を中心化する。 -/
theorem normalizer_factorization [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAmax : IsMaximalElementaryAbelian p A)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A {q})
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
        ∃ c ∈ opiCoreInG {p}ᶜ (Subgroup.centralizer ((P : Subgroup G) : Set G)),
          ∃ m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.normalizer (Q : Set G), n = c * m) ∧
      (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer (Q : Set G)) ∧
      ((IsCyclic ↥Q ∨ ∃ B : Subgroup ↥Q, Nat.card ↥B = q ^ 2 ∧ IsMaximalElementaryAbelian q B) →
        (P : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) := by
  sorry


end OddOrder.BG.Ch3.S10
