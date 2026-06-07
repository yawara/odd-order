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

/-- A Sylow `p`-subgroup `P` of `G` contained in `K ≤ G` restricts to a Sylow `p`-subgroup of
`↥K` with carrier `P.subgroupOf K` (replicates the private `S07.sylow_subgroupOf_of_le`). Shared
by Lemmas 10.4 and 10.12. -/
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

/-- **Converse of BG Lemma 4.5**: a finite `p`-group (`p` odd) of `p`-rank `≤ 1` is cyclic.
Contrapositive of `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (a noncyclic odd
`p`-group has a rank-`2` elementary abelian subgroup, forcing `pRank ≥ 2`). Used in Lemma 10.5. -/
private theorem isCyclic_of_pRank_le_one {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsPGroup p Q) (hodd : Odd p) (hr : pRank Q p ≤ 1) : IsCyclic Q := by
  by_contra hnc
  obtain ⟨E, hEea, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hQ hodd hnc
  have hle : Nat.log p (Nat.card ↥E) ≤ pRank Q p := le_pRank E hEea
  rw [hEcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
  omega

/-- `N_G(P) ≤ N_G(Ω₁(Z(P)))` (`Z₀ = omega1CenterInG P p`): the inner `Ω₁(Z(↥P))` is
characteristic in `↥P` (the center is characteristic and `g ^ p = 1` is automorphism-stable),
so `AppB.normalizer_le_normalizer_map_of_characteristic` applies. Replicates the private
`CriticalSubgroup.omega1Center.characteristic`. Used in Lemma 10.5. -/
private theorem normalizer_le_normalizer_omega1CenterInG (P : Subgroup G) (p : ℕ) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((omega1CenterInG P p : Subgroup G) : Set G) := by
  haveI hchar : (omega1OfAbelian ↥P (Subgroup.center ↥P) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).Characteristic := by
    rw [Subgroup.characteristic_iff_comap_eq]
    intro φ
    have hcZ : ∀ g : ↥P, φ g ∈ Subgroup.center ↥P ↔ g ∈ Subgroup.center ↥P := by
      intro g
      rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
      constructor
      · intro h h'
        have := h (φ h')
        rwa [← map_mul, ← map_mul, φ.injective.eq_iff] at this
      · intro h h'
        obtain ⟨h'', rfl⟩ := φ.surjective h'
        rw [← map_mul, ← map_mul, φ.injective.eq_iff]
        exact h h''
    ext g
    simp only [Subgroup.mem_comap, mem_omega1OfAbelian, MulEquiv.coe_toMonoidHom]
    rw [hcZ g]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hpow
      have := congrArg φ.symm hpow
      rwa [map_pow, φ.symm_apply_apply, map_one] at this
    · intro hpow
      rw [← map_pow, hpow, map_one]
  exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic (K := P)
    (W := omega1OfAbelian ↥P (Subgroup.center ↥P) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm))

/-! ## Lemma 10.3 — centralizer of a 2-rank subgroup (mmd gap, PDF p.87 回収) -/

/-- **BG Lemma 10.3** (mmd MISSING_PAGE, PDF p.87): `M ∈ ℳ`, `X` を `M` の `α(M)'`-部分群とし
`r(C_{M_α}(X)) ≥ 2` なら `C_M(X) ∈ 𝒰`。 -/
theorem centralizer_isUniquelyMaximal_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Subgroup.IsPiSubgroup (alpha M)ᶜ X)
    (hr : 2 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M)) :
    IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M) := by
  sorry

/-! ## Lemma 10.4 — α(M) の判定 (mmd MISSING_PAGE, PDF p.87) -/

/-- **BG Lemma 10.4 (a)(c)** (mmd MISSING_PAGE, PDF p.74 = PDF page 87; recovered 2026-06-07):
`M ∈ ℳ`。(a) `p ∣ |M/M'|` ⇒ `p ∉ σ(M)`; (c) `p ∉ σ(M)`, `r_p(M) = 2` ⇒ `p` は ideal でなく、
`M` の位数 `p²` elem-ab はすべて `G` の極大 elem-ab (`ℰ_p²(M) ⊆ ℰ_p*(G)`)。

**注意**: 旧 scaffold は (a) を `p ∉ α(M)` (弱い) に、(c) の仮定を `p ∈ α(M)` (⇒ `pRank ≥ 3`
で `pRank = 2` と矛盾 = vacuous) に誤記していた。原典 Lemma 10.4 に合わせ `σ(M)` 版へ修正
(downstream 未使用を確認済)。原典 (b) (`Ω₁(Z(P))` 入れ子 encoding) は後続。 -/
theorem alpha_criterion [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (∀ p : ℕ, p.Prime → p ∣ (commutator ↥M).index → p ∉ sigma M) ∧
    (∀ p : ℕ, p.Prime → p ∉ sigma M → pRank ↥M p = 2 →
      ¬ idealPrime p G ∧
      ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A) := by
  refine ⟨fun p hp hdvd hpσ => ?_, fun p hp hpσ hr2 => ?_⟩
  · -- (a) `p ∣ |M/M'|` and `p ∈ σ(M)` are contradictory: a Sylow `p` of `M` lies in `M'`.
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, -⟩ := hpσ.2
    have hPder : (P : Subgroup ↥M) ≤ commutator ↥M := by
      have h := sylow_le_derived_of_mem_sigma hG hM hpσ P
      rwa [derivedInG, Subgroup.map_le_map_iff_of_injective M.subtype_injective] at h
    exact P.not_dvd_index (dvd_trans hdvd (Subgroup.index_dvd_of_le hPder))
  · -- (c)
    haveI : Fact p.Prime := ⟨hp⟩
    -- ∀-part: a rank-`2` elementary abelian `A ≤ M` is `G`-maximal
    -- (else `A ∈ 𝒰` forces `p ∈ σ(M)`).
    have hmax : ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A := by
      intro A hAM hA2
      by_contra hAns
      have hAU := OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
      obtain ⟨PG, hAPG⟩ := hA2.1.isPGroup.exists_le_sylow
      have hAne : A ≠ ⊥ := by
        intro hb
        have h1 : Nat.card ↥A = 1 := by rw [hb]; exact Subgroup.card_bot
        rw [hA2.2] at h1
        exact hp.ne_one ((Nat.pow_eq_one.mp h1).resolve_right two_ne_zero)
      have hPGne : (PG : Subgroup G) ≠ ⊥ := fun hb => hAne (le_bot_iff.mp (hAPG.trans_eq hb))
      have hNlt : Subgroup.normalizer ((PG : Subgroup G) : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have hPGnormal : (PG : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases hG.simple.eq_bot_or_eq_top_of_normal _ hPGnormal with hbot | htop'
        · exact hPGne hbot
        · have hsolv : IsSolvable ↥(PG : Subgroup G) := by
            haveI := (PG.isPGroup').isNilpotent; infer_instance
          rw [htop'] at hsolv
          haveI := hsolv
          exact hG.notSolvable (solvable_of_surjective
            (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective)
      have hAN : A ≤ Subgroup.normalizer ((PG : Subgroup G) : Set G) :=
        hAPG.trans Subgroup.le_normalizer
      obtain ⟨K, hKco, hNK⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer ((PG : Subgroup G) : Set G))).resolve_left
          hNlt.ne
      have hNM : Subgroup.normalizer ((PG : Subgroup G) : Set G) ≤ M := by
        have hKeqM : K = M :=
          (hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hKco (hAN.trans hNK)).trans
            (hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hM) hAM).symm
        exact hKeqM ▸ hNK
      have hPGM : (PG : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
      apply hpσ
      rw [mem_sigma_iff]
      refine ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩, ?_⟩
      · exact dvd_trans (by rw [hA2.2]; exact dvd_pow_self p two_ne_zero)
          ((Subgroup.card_dvd_of_le hAM))
      · obtain ⟨Q, hQ⟩ := sylow_subgroupOf_of_le PG hPGM
        exact ⟨Q, by rw [hQ, Subgroup.map_subgroupOf_eq_of_le hPGM]; exact hNM⟩
    refine ⟨?_, hmax⟩
    -- `¬ idealPrime`: `r_p(M) = 2` gives `A ∈ ℰ_p²(M)`, maximal by `hmax` — a non-ideality witness.
    intro hideal
    obtain ⟨A0, hA0ea, hA0log⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p) (n := 2)
        (by norm_num) (le_of_eq hr2.symm)
    have hA0card : Nat.card ↥A0 = p ^ 2 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA0ea.isPGroup
      have hlog : Nat.log p (Nat.card ↥A0) = k := by
        rw [hk, Nat.log_pow (Fact.out : p.Prime).one_lt]
      have hle : Nat.log p (Nat.card ↥A0) ≤ pRank ↥M p := le_pRank A0 hA0ea
      rw [hr2, hlog] at hle
      rw [hlog] at hA0log
      rw [hk, le_antisymm hle hA0log]
    set A : Subgroup G := A0.map M.subtype with hAdef
    have hAea : A.IsElementaryAbelian p := hA0ea.map M.subtype_injective
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective M.subtype_injective]; exact hA0card
    have hAM : A ≤ M := Subgroup.map_subtype_le _
    have hAmax : IsMaximalElementaryAbelian p A := hmax A hAM ⟨hAea, hAcard⟩
    obtain ⟨PG, hAPG⟩ := hAea.isPGroup.exists_le_sylow
    refine hideal.2 PG ⟨A.subgroupOf PG, ?_, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPG).toEquiv]; exact hAcard
    · exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAPG).symm hAea
    · intro F hFea hFle
      have hmapF : F.map (PG : Subgroup G).subtype = A := by
        refine hAmax.2 _ (hFea.map (PG : Subgroup G).subtype_injective) ?_
        rw [← Subgroup.map_subgroupOf_eq_of_le hAPG]
        exact Subgroup.map_mono hFle
      have hF_eq : F = (F.map (PG : Subgroup G).subtype).subgroupOf (PG : Subgroup G) := by
        rw [Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (PG : Subgroup G).subtype_injective]
      rw [hF_eq, hmapF]

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
