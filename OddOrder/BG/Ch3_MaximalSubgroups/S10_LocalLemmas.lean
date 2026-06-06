/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37

/-!
# BG §10 局所補題 (Lemmas 10.3/10.4/10.5/10.12/10.13, Prop 10.11)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §10。
Hall 構造 base (`S10_HallStructure`, Thm 10.1/10.2) のみに依存し互いに独立な補題群
(active frontier leaves)。spine (`S10_BetaRadical`) とは独立に並行作業可能。
mmd `references/bg/local-analysis.mmd` L2856-2894 周辺。
-/

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Lemma 10.3 / 10.5 — centralizer と normalizer (mmd gap, PDF p.87 回収) -/

/-- **BG Lemma 10.3** (mmd MISSING_PAGE, PDF p.87): `M ∈ ℳ`, `X` を `M` の `α(M)'`-部分群とし
`r(C_{M_α}(X)) ≥ 2` なら `C_M(X) ∈ 𝒰`。 -/
theorem centralizer_isUniquelyMaximal_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Subgroup.IsPiSubgroup (alpha M)ᶜ X)
    (hr : 2 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M)) :
    IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M) := by
  sorry

/-- **BG Lemma 10.5** (mmd MISSING_PAGE, PDF p.87): `p ∈ σ(M)'`, `X ∈ ℰ_p¹(G)`,
`N_G(X) ⊆ M` なら `r_p(M) = 2`、`p` は ideal でなく、`X ⊆ A` となる `A ∈ ℰ_p²(G)` が存在する。 -/
theorem pRank_eq_two_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∉ sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1)
    (hN : Subgroup.normalizer (X : Set G) ≤ M) :
    pRank ↥M p = 2 ∧ ¬ idealPrime p G ∧ ∃ A ∈ elemAbelianOfRank G p 2, X ≤ A := by
  sorry

/-! ## Lemma 10.4 — α(M) の判定 (mmd MISSING_PAGE, PDF p.87) -/

/-- **BG Lemma 10.4 (a)(c)** (mmd MISSING_PAGE, PDF p.87): `M ∈ ℳ`。
(a) `p ∣ |M/M'|` ⇒ `p ∉ α(M)`; (c) `p ∈ α(M)`, `r_p(M) = 2` ⇒ `p` は ideal でなく、`M` の位数 `p²`
elem-ab はすべて `G` の極大 elem-ab。
(原典 (b): `p∈α(M), M_α≠1` ⇒ `∃ x∈Ω₁(Z(P))#: ℳ(C_G(x))={M} ∧ C_{M_α}(x) Z-group` —
`Ω₁(Z(P))` の入れ子 encoding は後続。`IsZGroup`/`maximalSubgroupsContaining` は整備済。) -/
theorem alpha_criterion [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (∀ p : ℕ, p.Prime → p ∣ (commutator ↥M).index → p ∉ alpha M) ∧
    (∀ p : ℕ, p.Prime → p ∈ alpha M → pRank ↥M p = 2 →
      ¬ idealPrime p G ∧
      ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A) := by
  sorry

/-! ## Proposition 10.11 — σ(M)'-部分群の rank (mmd L2856) -/

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
  sorry

/-! ## Helpers for Proposition 10.11(d) -/

/-- In a finite nilpotent group, two elements of coprime order commute.

A finite nilpotent group is the internal direct product of its Sylow subgroups
(`Sylow.directProductOfNormal`); two coprime-order elements have disjoint sets of relevant
primes, so in every Sylow factor at least one of their components is trivial. -/
private theorem commute_of_coprime_orderOf_of_isNilpotent {L : Type*} [Group L] [Finite L]
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

/-- **Cyclic uniqueness by order**: in a finite cyclic group, two subgroups of equal
cardinality coincide. (Each order-`d` subgroup equals the unique order-`d` kernel
`(powMonoidHom d).ker`.) Used in 10.11(d) to transport normalisation from the cyclic
`C_K(M_σ) ∩ M'` to its subgroup `[K, P]`.

This duplicates `S10_BetaRadical.cyclic_subgroup_eq_of_card_eq` (a sibling §10 leaf); the
shared helper should be hoisted into `S10_HallStructure` once the parallel §10 lanes merge. -/
private theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
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

/-- The pointwise action of a `MulAut` on a subgroup is its image (replicates the private
`mulAut_smul_eq_map` of the BG `Ch1`/`Ch2` files). -/
private theorem conjSmul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by rw [Subgroup.pointwise_smul_def]; rfl

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
    have hconjP : MulAut.conj g • P = P := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
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
    exact (Nat.card_congr (Subgroup.equivMapOfInjective K₀ _ (MulAut.conj g).injective).toEquiv).symm
  have h1 : (MulAut.conj g • K₀).subgroupOf Z = K₀.subgroupOf Z := by
    apply cyclic_subgroup_eq_of_card_eq (C := ↥Z)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀_le_Z).toEquiv, hcard]
  have h2 := congrArg (Subgroup.map Z.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le hK₀_le_Z] at h2

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
  sorry

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
  sorry


end OddOrder.BG.Ch3.S10
