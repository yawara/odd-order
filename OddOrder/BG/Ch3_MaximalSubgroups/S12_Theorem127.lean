/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary126

/-!
# BG §12: Theorem 12.7 — the nonabelian Sylow `p`-subgroup case

**スコープ**: BG Chapter III §12, Theorem 12.7 (pp. 86-87, mmd L3201-3251)。
`p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` で `G` の Sylow `p`-部分群が非可換のとき:
(a) `τ₂(M) = {p}`; (b) `A₀ = C_A(M_σ)` は位数 `p` で `F(M) = M_σ × A₀`;
(c) `X ∈ ℰ_p¹(E) − {A₀}` は `C_{M_σ}(X) = 1` かつ `C_G(X) ⊄ M`;
(d) `A₀` は `E` 内に補群 `E₀` を持ち; (e) `π(C_{E₀}(x)) ⊆ τ₁(M)` (`x ∈ M_σ#`)。

⚠ **(a) の faithful 化**: repo の `tau2` は素数性を要求しないため、集合等式
`tau2 M = {p}` ではなく素数限定形 `∀ q, q.Prime → q ∈ tau2 M → q = p` で述べる
(BG の τ₂ は暗黙に素数集合; 下流 (12.8 以降) が要るのは素数形のみ)。

## 主要消費

- Lemma 10.13 = `S10.nonabelian_pSubgroup_rankTwoElemAbelian_structure` ((b)(c) で)。
- Proposition 10.10(c) = `S10.normalizer_factorization` ((a) で)。
- Theorem 12.5 / Corollary 12.6 (前 leaf 群)。
- Maschke = `Ch1_Preliminary.exists_aInvariant_complement_in_omega1_quotient` ((d) で)。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Setup helpers: the `p`-part of `M` lives in `E` -/

/-- `|M| = |M_σ| · |E|` for the §12 complement setup. -/
theorem card_Msigma_mul_card_E [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
  have h1 := card_sup_eq_mul_of_le_normalizer_of_disjoint
    (A := E) (B := S10.Msigma M)
    (h.E_le.trans (le_normalizer_opiCoreInG _ _))
    (by rw [← h.E_compl_inf, inf_comm])
  rw [sup_comm, h.E_compl_sup] at h1
  rw [h1, Nat.mul_comm]

/-- For `p ∉ σ(M)`, the `p`-parts of `|M|` and `|E|` agree. -/
theorem factorization_card_eq_of_notMem_sigma [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∉ S10.sigma M) :
    (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
  have hcard := card_Msigma_mul_card_E h
  have hMσ : (Nat.card ↥(S10.Msigma M)).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hp (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, hMσ, Nat.zero_add]

/-- The image in `G` of a Sylow `p`-subgroup of `E` is `p`-maximal in `M` (`p ∉ σ(M)`). -/
theorem map_sylow_E_maximal_in_M [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∉ S10.sigma M) (PE : Sylow p ↥E)
    {T : Subgroup G} (hPT : (PE : Subgroup ↥E).map E.subtype ≤ T) (hTM : T ≤ M)
    (hTp : IsPGroup p ↥T) :
    T = (PE : Subgroup ↥E).map E.subtype := by
  have hcardP : Nat.card ↥((PE : Subgroup ↥E).map E.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
      factorization_card_eq_of_notMem_sigma h hp]
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  have hk_le : k ≤ (Nat.card ↥M).factorization p := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
    exact Subgroup.card_dvd_of_le hTM
  refine (Subgroup.eq_of_le_of_card_ge hPT ?_).symm
  rw [hcardP, hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk_le

/-- For `q ∈ τ₂(M)` (q prime) there is a rank-two elementary abelian `q`-subgroup
inside `E`: realize one inside `M` from `r_q(M) = 2` and conjugate it into a Sylow
`q`-subgroup of `M` coming from `E`. -/
theorem exists_elemAb_rank_two_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M) :
    ∃ B ∈ elemAbelianOfRank G q 2, B ≤ E := by
  classical
  have hr2 : pRank ↥M q = 2 := tau2_pRank_eq_two hq
  have hqσ : q ∉ S10.sigma M := tau2_subset_sigma_compl M hq
  -- a rank-two elementary abelian `q`-subgroup `B₁ ≤ M`.
  obtain ⟨B', hB'ea, hB'log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := q) (n := 2)
      (by norm_num) (by rw [hr2])
  have hB'nc : ¬ IsCyclic ↥B' :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hB'ea hB'log
  have hq_odd : Odd q := by
    obtain ⟨j, hj⟩ := hB'ea.isPGroup.exists_card_eq
    have hj2 : 2 ≤ j := by
      rw [hj, Nat.log_pow (Fact.out : q.Prime).one_lt] at hB'log
      exact hB'log
    have hqdvd : q ∣ Nat.card ↥B' := by
      rw [hj]; exact dvd_pow_self q (by omega)
    exact hG.odd.of_dvd_nat
      ((hqdvd.trans (Subgroup.card_subgroup_dvd_card B')).trans
        (Subgroup.card_subgroup_dvd_card M))
  obtain ⟨B'', hB''ea, hB''card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hB'ea.isPGroup hq_odd hB'nc
  set B₁ : Subgroup G := (B''.map B'.subtype).map M.subtype with hB₁def
  have hB₁M : B₁ ≤ M := Subgroup.map_subtype_le _
  have hB₁mem : B₁ ∈ elemAbelianOfRank G q 2 := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.IsElementaryAbelian.map M.subtype_injective
        (Subgroup.IsElementaryAbelian.map B'.subtype_injective hB''ea)
    · rw [hB₁def, Subgroup.card_map_of_injective M.subtype_injective,
        Subgroup.card_map_of_injective B'.subtype_injective, hB''card]
  -- a Sylow `q`-subgroup of `↥M` containing `B₁`, and one coming from `E`.
  have hB₁pg : IsPGroup q ↥B₁ := hB₁mem.1.isPGroup
  obtain ⟨TM, hB₁TM⟩ := hB₁pg.comap_subtype.exists_le_sylow (G := M)
  obtain ⟨TE⟩ := (inferInstance : Nonempty (Sylow q ↥E))
  set T : Subgroup G := (TE : Subgroup ↥E).map E.subtype with hTdef
  have hT_le_E : T ≤ E := Subgroup.map_subtype_le _
  have hT_le_M : T ≤ M := hT_le_E.trans h.E_le
  have hT_card : Nat.card ↥(T.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_M).toEquiv, hTdef,
      Subgroup.card_map_of_injective E.subtype_injective, TE.card_eq_multiplicity,
      factorization_card_eq_of_notMem_sigma h hqσ]
  set TS : Sylow q ↥M := Sylow.ofCard (T.subgroupOf M) hT_card with hTSdef
  -- conjugate `TM` onto `TS` inside `↥M`.
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M TM TS
  refine ⟨MulAut.conj (m : G) • B₁, ⟨?_, ?_⟩, ?_⟩
  · rw [mulAut_smul_eq_map]
    exact Subgroup.IsElementaryAbelian.map (MulAut.conj (m : G)).injective hB₁mem.1
  · rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective]
    exact hB₁mem.2
  · -- `conj m • B₁ ≤ conj m • TM-image = TS-image = T ≤ E`.
    have hB₁_le_TM : B₁ ≤ (TM : Subgroup ↥M).map M.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hB₁M]
      exact Subgroup.map_mono hB₁TM
    have hsmul_eq : MulAut.conj (m : G) • ((TM : Subgroup ↥M).map M.subtype) = T := by
      have h1 : ((m • TM : Sylow q ↥M) : Subgroup ↥M).map M.subtype = T := by
        rw [hm, hTSdef]
        show (T.subgroupOf M).map M.subtype = T
        exact Subgroup.map_subgroupOf_eq_of_le hT_le_M
      rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
        Subgroup.pointwise_smul_def, Subgroup.map_map, Subgroup.map_map]
      rfl
    calc MulAut.conj (m : G) • B₁
        ≤ MulAut.conj (m : G) • ((TM : Subgroup ↥M).map M.subtype) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hB₁_le_TM
      _ = T := hsmul_eq
      _ ≤ E := hT_le_E

/-! ## Theorem 12.7(a): `τ₂(M)` consists of `p` alone -/

/-- **BG Theorem 12.7(a)** (mmd L3203, L3216-3218): if `G` has nonabelian Sylow
`p`-subgroups and `p ∈ τ₂(M)`, then `p` is the only **prime** in `τ₂(M)`.
For a second prime `q`, a rank-two `B ∈ ℰ_q²(E)` is normal in `E` alongside `A`
(Corollary 12.6(a)), so `A` centralizes `B`; both are maximal elementary abelian
(Lemma 12.1(g)), so Proposition 10.10(c) plants a full Sylow `p`-subgroup of `G`
inside `C_G(B) ≤ E` (Corollary 12.6(b)) — but then it would be an abelian Sylow
`p`-subgroup of `G` (Theorem 12.5(b)), contradicting the hypothesis. -/
theorem tau2_prime_eq_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hq : q ∈ tau2 M) : q = p := by
  classical
  haveI : Fact q.Prime := ⟨hq_prime⟩
  by_contra hqp
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `B ∈ ℰ_q²(E)`, normal in `E` together with `A`, hence centralized by `A`.
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hq
  have hBM : B ≤ M := hBE.trans h.E_le
  have hAnorm : E ≤ Subgroup.normalizer (A : Set G) :=
    E_le_normalizer_of_tau2 hG h hp hA hAE
  have hBnorm : E ≤ Subgroup.normalizer (B : Set G) :=
    E_le_normalizer_of_tau2 hG h hq hB hBE
  have hAB_bot : A ⊓ B = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ B : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A ⊓ B : Subgroup G) ∣ q ^ 2 := by
      rw [← hB.2]; exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow Fact.out).mp h1
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rwa [pow_zero] at hicard
    · exfalso
      have hpdvd : p ∣ Nat.card ↥(A ⊓ B : Subgroup G) := by
        rw [hicard]; exact dvd_pow_self p hipos.ne'
      have := (Nat.prime_dvd_prime_iff_eq Fact.out hq_prime).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow (hpdvd.trans h2))
      exact hqp this.symm
  have hAcentB : A ≤ Subgroup.centralizer (B : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hAB_bot]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hAnorm (hBE hb)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (b * a⁻¹ * b⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * b * a⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hBnorm (hAE ha)) b).mp hb
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hb)
      rwa [commutatorElement_def]
  -- extend `B` to a maximal `A`-invariant `q`-subgroup `Qs` of `G`.
  have hB_inv : B ∈ hInvariant ⊤ A {q} := by
    refine ⟨le_top, hAcentB.trans (Subgroup.centralizer_le_normalizer _), ?_⟩
    exact isPiSubgroup_of_isPGroup_of_mem hB.1.isPGroup rfl
  obtain ⟨Qs, hQs, hBQs⟩ := exists_le_hInvariantStar hB_inv
  -- `q ∈ π(C_G(A))` and `A` is maximal elementary abelian (Lemma 12.1(g)).
  have hBC : B ≤ Subgroup.centralizer (A : Set G) := le_centralizer_swap hAcentB
  have hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩
    have h1 : (q : ℕ) ∣ Nat.card ↥B := by
      rw [hB.2]; exact dvd_pow_self q two_ne_zero
    exact h1.trans (Subgroup.card_dvd_of_le hBC)
  have hAmax : IsMaximalElementaryAbelian p A :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal Fact.out hp hAM hA).1
  have hBmax : IsMaximalElementaryAbelian q B :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal hq_prime hq hBM hB).1
  -- Proposition 10.10(c): a full Sylow `p`-subgroup of `G` centralizes `Qs`.
  obtain ⟨P', hAP', -, -, hPcent⟩ :=
    S10.normalizer_factorization hG (Ne.symm hqp) hA hAmax hQs hqc
  have hP'C : (P' : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
    refine le_trans (hPcent (Or.inr ?_)) (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hBQs))
    -- `B.subgroupOf Qs` is maximal elementary abelian of order `q²` inside `↥Qs`.
    refine ⟨B.subgroupOf Qs, ?_, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQs).toEquiv]
      exact hB.2
    · exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hBQs).symm hB.1
    · intro F' hF' hBF'
      have hFle : F'.map Qs.subtype ≤ Qs := Subgroup.map_subtype_le _
      have hBF : B ≤ F'.map Qs.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hBQs]
        exact Subgroup.map_mono hBF'
      have hFea : (F'.map Qs.subtype).IsElementaryAbelian q :=
        Subgroup.IsElementaryAbelian.map Qs.subtype_injective hF'
      have hFeq : F'.map Qs.subtype = B := hBmax.2 _ hFea hBF
      apply Subgroup.map_injective Qs.subtype_injective
      rw [hFeq, Subgroup.map_subgroupOf_eq_of_le hBQs]
  -- `C_G(B) ≤ E` (Corollary 12.6(b)), so `P'` is an abelian Sylow `p`-subgroup of `G`.
  have hP'E : (P' : Subgroup G) ≤ E :=
    hP'C.trans (centralizer_le_E_of_tau2 hG h hq hB hBE).1
  -- but then a Sylow `p`-subgroup of `E` has full `G`-order, and is abelian by 12.5(b),
  -- while all Sylow `p`-subgroups of `G` are nonabelian.
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  obtain ⟨PE, hP'PE⟩ := (P'.isPGroup'.comap_subtype (K := E)).exists_le_sylow
  set Pmap : Subgroup G := (PE : Subgroup ↥E).map E.subtype with hPmapdef
  have hP'_le_Pmap : (P' : Subgroup G) ≤ Pmap := by
    rw [hPmapdef, ← Subgroup.map_subgroupOf_eq_of_le hP'E]
    exact Subgroup.map_mono hP'PE
  have hPmap_card : Nat.card ↥Pmap = p ^ (Nat.card G).factorization p := by
    have hle : Nat.card ↥Pmap ∣ p ^ (Nat.card G).factorization p := by
      obtain ⟨k, hk⟩ := (PE.isPGroup'.map E.subtype).exists_card_eq
      rw [← hPmapdef] at hk
      have hdvd : (p : ℕ) ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card Pmap
      have hk_le : k ≤ (Nat.card G).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
      rw [hk]
      exact pow_dvd_pow p hk_le
    have hge : p ^ (Nat.card G).factorization p ∣ Nat.card ↥Pmap := by
      rw [← P'.card_eq_multiplicity]
      exact Subgroup.card_dvd_of_le hP'_le_Pmap
    exact Nat.dvd_antisymm hle hge
  set PS : Sylow p G := Sylow.ofCard Pmap hPmap_card with hPSdef
  -- abelian (Theorem 12.5(b) via the Sylow of `↥M`):
  have hPmap_le_M : Pmap ≤ M := (Subgroup.map_subtype_le _).trans h.E_le
  have hPmap_ab : IsMulCommutative ↥Pmap := by
    have hcardM : Nat.card ↥(Pmap.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmap_le_M).toEquiv, hPmapdef,
        Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
        factorization_card_eq_of_notMem_sigma h hpσ]
    have h125b := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.1.1
      (Sylow.ofCard (Pmap.subgroupOf M) hcardM)
    have e : ↥(Pmap.subgroupOf M) ≃* ↥Pmap := Subgroup.subgroupOfEquivOfLe hPmap_le_M
    exact S11.isMulCommutative_of_mulEquiv e h125b
  -- nonabelian (hypothesis + Sylow conjugacy):
  obtain ⟨S₀, hS₀⟩ := hnonab
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS S₀
  apply hS₀
  have hcoe : (S₀ : Subgroup G) = MulAut.conj g • Pmap := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def]
    rfl
  rw [hcoe, mulAut_smul_eq_map]
  exact S11.isMulCommutative_of_mulEquiv
    (Subgroup.equivMapOfInjective Pmap _ (MulAut.conj g).injective) hPmap_ab

end OddOrder.BG.Ch3.S12
