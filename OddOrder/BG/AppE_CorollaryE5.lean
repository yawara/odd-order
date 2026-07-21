/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_PropE4
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient

/-!
# BG Corollary E.5: the local data `(E.29)`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 164–166.

Corollary E.5 opens with *"Note that we are in the situation of Corollary 15.9"* and
collects, from that proof, the display

> `(E.29)`  `C_{N_σ}(x) > 1`, `M ∩ N` is a complement to `N_σ` in `N`, `|K₁|` is prime,
> and `R` is contained in an abelian normal complement `U₁` to `K₁` in `M ∩ N`.

This leaf assembles the corollary in stages (issue 3028):

* **`e5_neighbour_data` (this file, WP1)** — the `(E.29)` bundle: replaying the opening of
  the proved Corollary 15.9 (`centralizer_escape_final_local`,
  `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TaxonomyOutput.lean`) through its public
  ingredients: `signalizer_structure_of_mem_sigmaSharp`, `subgroupESetup_of_complement`,
  `typeP2_matched_kappa_hall_pair_of_esetup`, and `card_kappaHall_prime_of_isTypeP2`.
  `K₁` is BG's Hall `κ(N)`-subgroup of `M ∩ N` and `U₁` its abelian partner Hall
  `(κ(N) ∪ σ(N))'`-subgroup; the `R ≤ U₁` clause of `(E.29)` is deferred to the `(E.30)`
  stage, where `R` is produced.
* Later stages (issue 3028 WP2–WP5): `(E.30)`–`(E.32)`, the `RegularOperatorSetup`
  instantiation for `(O_p(M), K₁, E)`, `(ii) ∧ hdc ⟹ (i)` via Theorem E.3 and the
  corrected Proposition E.4 (`AppE_PropE4.lean`), and the `(E.33)`/`(E.34)` counting.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S16
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **A `p`-element of a nilpotent normal subgroup lies in the `p`-core**: if `W ≤ M` is
nilpotent, `W ⊴ M` (as `subgroupOf`), and `x ∈ W` has order `p`, then `x ∈ O_p(M)`.

The Sylow `p`-subgroup of the nilpotent `W` is normal, hence characteristic, in `W`, so
its image is a normal `p`-subgroup of `M` — and it absorbs `x`.  This is the `(E.30)`
ingredient *"`O_p(M)` is a Sylow `p`-subgroup of `M_σ`"* in the form actually consumed:
`x ∈ M_σ` of order `p` lands in `O_p(M)` (with `W = M_σ`, nilpotent as the kernel of the
Frobenius group `M` from Corollary 15.9). -/
theorem mem_opiCoreInG_singleton_of_nilpotent [Finite G] {p : ℕ} (hp : p.Prime)
    {M W : Subgroup G} (hWM : W ≤ M) (hWnorm : (W.subgroupOf M).Normal)
    (hWnil : Group.IsNilpotent ↥W) {x : G} (hxW : x ∈ W) (hord : orderOf x = p) :
    x ∈ opiCoreInG {p} M := by
  haveI : Fact p.Prime := ⟨hp⟩
  set W' : Subgroup ↥M := W.subgroupOf M with hW'def
  haveI : W'.Normal := hWnorm
  haveI : Group.IsNilpotent ↥W' :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hWM)).mpr hWnil
  have hxM : x ∈ M := hWM hxW
  set ξ : ↥W' := ⟨⟨x, hxM⟩, by rwa [Subgroup.mem_subgroupOf]⟩ with hξdef
  have hordξ : orderOf ξ = p := by
    have h1 := orderOf_injective W'.subtype W'.subtype_injective ξ
    have h2 := orderOf_injective M.subtype M.subtype_injective (W'.subtype ξ)
    rw [← hord]
    rw [← h1, ← h2]
    rfl
  -- `⟨ξ⟩` is a `p`-group; put it inside a Sylow `p`-subgroup of the nilpotent `W'`.
  have hpg : IsPGroup p ↥(Subgroup.zpowers ξ) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hordξ, pow_one])
  obtain ⟨P, hξP⟩ := hpg.exists_le_sylow
  have hPchar : (P : Subgroup ↥W').Characteristic :=
    Sylow.characteristic_of_normal P inferInstance
  -- Its image in `↥M` is a normal `p`-subgroup; push to the ambient group.
  have hQnorm : (((P : Subgroup ↥W').map W'.subtype)).Normal :=
    OddOrder.GroupTheory.normal_map_subtype_of_characteristic hPchar
  obtain ⟨n, hn⟩ := P.2.exists_card_eq
  set Qamb : Subgroup G := ((P : Subgroup ↥W').map W'.subtype).map M.subtype with hQdef
  have hQambM : Qamb ≤ M := Subgroup.map_subtype_le _
  have hQsub : Qamb.subgroupOf M = (P : Subgroup ↥W').map W'.subtype :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hQnorm' : (Qamb.subgroupOf M).Normal := hQsub ▸ hQnorm
  have hQcard : Nat.card ↥Qamb = p ^ n := by
    rw [hQdef, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective W'.subtype_injective, hn]
  have hQpi : Subgroup.IsPiSubgroup {p} Qamb := by
    intro r hr
    rw [hQcard] at hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ p ^ n := Nat.dvd_of_mem_primeFactors hr
    exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow hrdvd)
  refine le_opiCoreInG_of_normal_of_isPiSubgroup hQambM hQnorm' hQpi ?_
  exact ⟨W'.subtype ξ, ⟨ξ, hξP (Subgroup.mem_zpowers ξ), rfl⟩, rfl⟩

/-- A `τ₂(N)`-prime avoids both `κ(N)` and `σ(N)` — the prime of BG's `x` is a
`(κ(N) ∪ σ(N))'`-prime (the `p`-rank separates `τ₂` from `τ₁ ∪ τ₃ ⊇ κ`). -/
theorem mem_kappa_sigma_compl_of_mem_tau2 [Finite G] {N : Subgroup G} {p : ℕ}
    (h2 : p ∈ tau2 N) :
    p ∈ (OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ := by
  rw [Set.mem_compl_iff, Set.mem_union, not_or]
  refine ⟨fun hκ => ?_, h2.1⟩
  rcases OddOrder.BG.Ch4.S14.kappa_subset_tau1_union_tau3 hκ with h | h
  · exact absurd ((tau2_pRank_eq_two h2).symm.trans (tau1_pRank_eq_one h)) (by norm_num)
  · exact absurd ((tau2_pRank_eq_two h2).symm.trans (tau3_pRank_eq_one h)) (by norm_num)

/-- **A `p`-subgroup lands in a normal subgroup of `p'`-index**: if `H ≤ K`, `L ≤ K` with
`L ⊴ K` (as `subgroupOf`), `H` a `p`-group, and `p ∤ [K : L]`, then `H ≤ L` — the image of
any `h ∈ H` in `K/L` has order dividing both a `p`-power and the `p'`-number `[K : L]`. -/
theorem le_of_isPGroup_of_not_dvd_relIndex [Finite G] {p : ℕ} (hp : p.Prime)
    {H K L : Subgroup G} (hHK : H ≤ K) (_hLK : L ≤ K)
    (hnorm : (L.subgroupOf K).Normal) (hpH : IsPGroup p ↥H)
    (hnd : ¬ p ∣ L.relIndex K) : H ≤ L := by
  intro g hg
  haveI := hnorm
  set gbar : ↥K ⧸ L.subgroupOf K := QuotientGroup.mk' _ ⟨g, hHK hg⟩ with hgbardef
  obtain ⟨k, hk⟩ := hpH ⟨g, hg⟩
  have hcoe : ((⟨g, hHK hg⟩ : ↥K) ^ p ^ k) = 1 := by
    have h1 := congrArg (fun z : ↥H => (z : G)) hk
    exact Subtype.ext (by simpa using h1)
  have hord1 : gbar ^ p ^ k = 1 := by rw [hgbardef, ← map_pow, hcoe, map_one]
  have hdvd1 : orderOf gbar ∣ p ^ k := orderOf_dvd_of_pow_eq_one hord1
  have hdvd2 : orderOf gbar ∣ L.relIndex K := by
    have h := orderOf_dvd_natCard gbar
    rwa [← Subgroup.index_eq_card] at h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd1
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · have h1 : gbar = 1 := orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
    have hmem : (⟨g, hHK hg⟩ : ↥K) ∈ L.subgroupOf K := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp hmem
  · exact absurd ((dvd_pow_self p hjpos.ne').trans (hj ▸ hdvd2)) hnd

/-- **BG `(E.30)`** (p. 165): `x ∈ O_p(M)`, the `p`-part `O_p(M) ∩ N` of `M ∩ N` is
absorbed by the abelian `U₁`, and

> `O_p(M) ∩ N = C_{O_p(M)}(x)`.

`⊇` is `C_G(x) ≤ N`; `⊆` is the abelianity of `U₁`, which contains both `x` and
`O_p(M) ∩ N` (the `(E.29)` clause *"`R` is contained in … `U₁`"*, delivered here by the
`p'`-index absorption `le_of_isPGroup_of_not_dvd_relIndex`, since `U₁` is Hall
`(κ(N) ∪ σ(N))'` in `N` and `p ∈ (κ(N) ∪ σ(N))ᶜ`).  The nilpotency of `M_σ` (Frobenius
kernel of `M`, from Corollary 15.9) feeds `x ∈ O_p(M)`. -/
theorem e5_R_eq_centralizer [Finite G]
    {M N : Subgroup G} {x : G} {p : ℕ} (hp : p.Prime)
    (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hord : orderOf x = p) (hxN : x ∈ N)
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ N)
    (hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M))
    {K₁ U₁ : Subgroup G} (hU₁MN : U₁ ≤ M ⊓ N)
    (hU₁hall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ) (U₁.subgroupOf N))
    (hU₁ab : IsMulCommutative ↥U₁)
    (hK₁norm : K₁ ≤ Subgroup.normalizer ((U₁ : Subgroup G) : Set G))
    (hsupMN : M ⊓ N = K₁ ⊔ U₁)
    (hpκσ : p ∈ (OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ) :
    x ∈ opiCoreInG {p} M ∧
      opiCoreInG {p} M ⊓ N ≤ U₁ ∧
      opiCoreInG {p} M ⊓ N = opiCoreInG {p} M ⊓ Subgroup.centralizer ({x} : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `x ∈ O_p(M)`, through the nilpotent `M_σ ⊴ M`.
  have hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]
    infer_instance
  have hxOp : x ∈ opiCoreInG {p} M :=
    mem_opiCoreInG_singleton_of_nilpotent hp (OddOrder.BG.Ch3.S10.Msigma_le M) hMσnorm
      hMσnil hxMσ hord
  -- `U₁ ⊴ M ∩ N`, since `M ∩ N = K₁ ⊔ U₁` normalizes `U₁`.
  have hMNle : M ⊓ N ≤ Subgroup.normalizer ((U₁ : Subgroup G) : Set G) := by
    rw [hsupMN]
    exact sup_le hK₁norm Subgroup.le_normalizer
  have hU₁norm : (U₁.subgroupOf (M ⊓ N)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hk := Subgroup.mem_normalizer_iff.mp (hMNle k.2) (n : G)
    simpa using hk.mp hn
  -- Absorption: `O_p(M) ∩ N` is a `p`-subgroup of `M ∩ N`, and `p ∤ [M ∩ N : U₁]`.
  have hOpN_MN : opiCoreInG {p} M ⊓ N ≤ M ⊓ N :=
    le_inf (inf_le_left.trans (opiCoreInG_le _ _)) inf_le_right
  have hPpg : IsPGroup p ↥(opiCoreInG {p} M ⊓ N) :=
    (isPGroup_opiCoreInG_singleton M).to_le inf_le_left
  have hnd : ¬ p ∣ U₁.relIndex (M ⊓ N) := by
    intro hdvd
    have h1 : U₁.relIndex (M ⊓ N) ∣ U₁.relIndex N :=
      ⟨(M ⊓ N).relIndex N, (Subgroup.relIndex_mul_relIndex U₁ (M ⊓ N) N hU₁MN inf_le_right).symm⟩
    exact (hU₁hall.2 p (Nat.mem_primeFactors.mpr
      ⟨hp, hdvd.trans h1, Subgroup.index_ne_zero_of_finite⟩)) hpκσ
  have habs : opiCoreInG {p} M ⊓ N ≤ U₁ :=
    le_of_isPGroup_of_not_dvd_relIndex hp hOpN_MN hU₁MN hU₁norm hPpg hnd
  have hxU₁ : x ∈ U₁ := habs ⟨hxOp, hxN⟩
  refine ⟨hxOp, habs, le_antisymm (fun u hu => ⟨hu.1, ?_⟩) (inf_le_inf_left _ hCN)⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  rw [Set.mem_singleton_iff.mp hy]
  exact congrArg Subtype.val (hU₁ab.is_comm.comm (⟨x, hxU₁⟩ : ↥U₁) ⟨u, habs hu⟩)

/-- **BG Corollary 15.9(c), the collapse `E ∩ N = K₁`** (BG p. 123): once the cyclic
Frobenius complement `E` has been chosen to contain `K₁`, its intersection with `N`
collapses onto `K₁`.

`K₁ ≤ E ∩ N ≤ M ∩ N = K₁ ⊔ U₁`; any `c ∈ E ∩ N` commutes with a nontrivial `k₀ ∈ K₁`
(both live in the cyclic `E`), and in the decomposition `c = k·u` (`U₁ ⊴ M ∩ N`) the
`U₁`-part commutes with `k₀` too, hence dies by BG Theorem A(4) (`C_{U₁}(k₀) = 1`).
Coq drops all of 15.9(c) (BGsection15.v: *"not used later"* — Coq has no Appendix E),
so this is formalized here for the first time (issue 3028 WP2.5). -/
theorem inf_eq_kappaHall_of_le_cyclic [Finite G]
    {M N E K₁ U₁ : Subgroup G}
    (hEM : E ≤ M) (hEcyc : IsCyclic ↥E) (hK₁E : K₁ ≤ E) (hK₁N : K₁ ≤ N)
    (hK₁ne : K₁ ≠ ⊥)
    (hU₁norm : (U₁.subgroupOf (M ⊓ N)).Normal)
    (hsupMN : M ⊓ N = K₁ ⊔ U₁)
    (hCU₁ : ∀ k ∈ K₁, k ≠ 1 → U₁ ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) :
    E ⊓ N = K₁ := by
  classical
  haveI : Nontrivial ↥K₁ := (Subgroup.nontrivial_iff_ne_bot K₁).mpr hK₁ne
  obtain ⟨k₀', hk₀ne'⟩ := exists_ne (1 : ↥K₁)
  have hk₀K₁ : (k₀' : G) ∈ K₁ := k₀'.2
  have hk₀ne : (k₀' : G) ≠ 1 := fun h => hk₀ne' (Subtype.ext h)
  -- Elements of `E` commute (cyclic ⇒ abelian).
  have hEcomm : ∀ a b : G, a ∈ E → b ∈ E → Commute a b := by
    intro a b ha hb
    letI : CommGroup ↥E := IsCyclic.commGroup
    have h2 : a * b = b * a := by
      have h := mul_comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩
      simpa using congrArg (fun z : ↥E => (z : G)) h
    exact h2
  refine le_antisymm ?_ (le_inf hK₁E hK₁N)
  intro c hc
  have hcMN : c ∈ M ⊓ N := ⟨hEM hc.1, hc.2⟩
  -- Decompose `c = k * u` inside `↥(M ⊓ N)`, where `U₁` is normal.
  haveI := hU₁norm
  have hK₁le : K₁ ≤ M ⊓ N := hsupMN ▸ le_sup_left
  have hU₁le : U₁ ≤ M ⊓ N := hsupMN ▸ le_sup_right
  have hsubSup : (K₁.subgroupOf (M ⊓ N)) ⊔ (U₁.subgroupOf (M ⊓ N)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK₁le hU₁le, ← hsupMN, Subgroup.subgroupOf_self]
  have hcprod : (⟨c, hcMN⟩ : ↥(M ⊓ N)) ∈
      (K₁.subgroupOf (M ⊓ N) : Set ↥(M ⊓ N)) * (U₁.subgroupOf (M ⊓ N) : Set ↥(M ⊓ N)) := by
    rw [← Subgroup.mul_normal, hsubSup]
    exact Subgroup.mem_top _
  obtain ⟨k', hk', u', hu', hprod⟩ := hcprod
  have hkK₁ : ((k' : ↥(M ⊓ N)) : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hk'
  have huU₁ : ((u' : ↥(M ⊓ N)) : G) ∈ U₁ := Subgroup.mem_subgroupOf.mp hu'
  have hcku : c = ((k' : ↥(M ⊓ N)) : G) * ((u' : ↥(M ⊓ N)) : G) := by
    have h := congrArg (fun z : ↥(M ⊓ N) => (z : G)) hprod
    simpa using h.symm
  -- The `U₁`-part commutes with `k₀`, hence is trivial.
  have hCk : Commute (k₀' : G) ((k' : ↥(M ⊓ N)) : G) := hEcomm _ _ (hK₁E hk₀K₁) (hK₁E hkK₁)
  have hCc : Commute (k₀' : G) c := hEcomm _ _ (hK₁E hk₀K₁) hc.1
  have hCu : Commute (k₀' : G) ((u' : ↥(M ⊓ N)) : G) := by
    have h1 : ((u' : ↥(M ⊓ N)) : G) = ((k' : ↥(M ⊓ N)) : G)⁻¹ * c := by
      rw [hcku]; group
    rw [h1]
    exact hCk.inv_right.mul_right hCc
  have huC : ((u' : ↥(M ⊓ N)) : G) ∈ U₁ ⊓ Subgroup.centralizer ({(k₀' : G)} : Set G) :=
    ⟨huU₁, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact hCu⟩
  rw [hCU₁ _ hk₀K₁ hk₀ne] at huC
  have hu1 : ((u' : ↥(M ⊓ N)) : G) = 1 := Subgroup.mem_bot.mp huC
  rw [hcku, hu1, mul_one]
  exact hkK₁

/-- **BG Corollary 15.9(c), the suitable complement** (BG p. 123, *"We choose `E` to
contain `K₁`"*): the cyclic Frobenius complement of Corollary 15.9(b) can be re-chosen,
by Hall conjugacy in the solvable `M`, to contain the `σ(M)'`-subgroup `K₁` — keeping the
complement, cyclicity and Frobenius properties.  Combined with
`inf_eq_kappaHall_of_le_cyclic` this is BG's 15.9(c) (dropped by Coq; first formalized
here, issue 3028 WP2.5). -/
theorem e5_exists_suitable_complement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₁ E₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hK₁M : K₁ ≤ M)
    (hK₁σ' : ∀ r ∈ (Nat.card ↥K₁).primeFactors, r ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ)
    (hE₀compl : Subgroup.IsComplement'
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E₀.subgroupOf M))
    (hE₀cyc : IsCyclic ↥E₀) (hE₀M : E₀ ≤ M)
    (hE₀frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E₀.subgroupOf M)) :
    ∃ E : Subgroup G, E ≤ M ∧
      Subgroup.IsComplement'
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) ∧
      IsCyclic ↥E ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) ∧
      K₁ ≤ E := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ' : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hMσ'def
  set E₀' : Subgroup ↥M := E₀.subgroupOf M with hE₀'def
  haveI hMσ'norm : Mσ'.Normal := by
    rw [hMσ'def, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]
    infer_instance
  have hMσhall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) Mσ' :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  -- `E₀'` is Hall `σ(M)'` in `↥M`: its order is the index of `Mσ'` and vice versa.
  have hcardE₀ : Nat.card ↥E₀' = Mσ'.index := hE₀compl.symm.index_eq_card.symm
  have hidxE₀ : E₀'.index = Nat.card ↥Mσ' := hE₀compl.index_eq_card
  have hE₀hall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      (OddOrder.BG.Ch3.S10.sigma M)ᶜ E₀' := by
    constructor
    · intro r hr
      rw [hcardE₀] at hr
      exact Set.mem_compl (hMσhall.2 r hr)
    · intro r hr
      rw [hidxE₀] at hr
      exact fun hr' => hr' (hMσhall.1 r hr)
  -- `K₁` sits inside a Hall `σ(M)'`-subgroup `H` of `↥M` (Hall `D`), conjugate to `E₀'`.
  have hK₁'pi : ∀ r ∈ (Nat.card ↥(K₁.subgroupOf M)).primeFactors,
      r ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁M).toEquiv] at hr
    exact hK₁σ' r hr
  obtain ⟨H, hHhall, hK₁H⟩ := OddOrder.Isaacs.Ch03.hall_D hK₁'pi
  obtain ⟨g, hg⟩ := OddOrder.Isaacs.Ch03.hall_C hE₀hall hHhall
  set e : ↥M ≃* ↥M := (MulAut.conj g : MulAut ↥M) with hedef
  have hg' : E₀'.map e.toMonoidHom = H := hg
  -- Conjugation fixes the normal `Mσ'`.
  have hMσmap : Mσ'.map e.toMonoidHom = Mσ' := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      simpa [hedef] using hMσ'norm.conj_mem y hy g
    · intro y hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have h := hMσ'norm.conj_mem y hy g⁻¹
        simpa using h
      · simp [hedef, MulAut.conj_apply]
        group
  -- Transport the Frobenius package along `e`, landing on `H`.
  have hfrob' := OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv hE₀frob e
  rw [hMσmap, hg'] at hfrob'
  -- `H` is cyclic (isomorphic to the cyclic `E₀`).
  haveI : IsCyclic ↥E₀' := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hE₀M).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hE₀M).symm.surjective
  haveI hHcyc : IsCyclic ↥H := by
    have h1 : IsCyclic ↥(E₀'.map e.toMonoidHom) := isCyclic_of_surjective
      (e.subgroupMap E₀').toMonoidHom (e.subgroupMap E₀').surjective
    exact hg' ▸ h1
  -- Push `H` to the ambient group.
  have hEsub : (H.map M.subtype).subgroupOf M = H :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective H
  refine ⟨H.map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [hEsub]
    exact hfrob'.isComplement
  · exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective H M.subtype M.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective H M.subtype M.subtype_injective).surjective
  · rw [hEsub]
    exact hfrob'
  · calc K₁ = (K₁.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hK₁M).symm
      _ ≤ H.map M.subtype := Subgroup.map_mono hK₁H

/-- **BG `(E.29)`** (p. 165): under Corollary E.5's hypothesis block, the unique maximal
subgroup `N ⊇ C_G(x)` is of type P₂ with `C_{N_σ}(x) ≠ 1` and `M ∩ N` a complement to
`N_σ` in `N`; and `M ∩ N` carries a Hall `κ(N)`-subgroup `K₁` of prime order together
with a nontrivial abelian Hall `(κ(N) ∪ σ(N))'`-subgroup `U₁` normalized by `K₁`.

This is the opening of BG's proof (*"As in the proof of Corollary 15.9, we see that…"*),
replayed through the public pieces of the proved
`OddOrder.BG.Ch4.S16.centralizer_escape_final_local`.  The remaining `(E.29)` clause —
`R ≤ U₁` for the Sylow `p`-subgroup `R` of `M ∩ N` — is produced at the `(E.30)` stage
(issue 3028 WP2), which constructs `R`. -/
theorem e5_neighbour_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} {x : G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hord : orderOf x = p)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : N ∉ OddOrder.BG.Ch4.S14.maximalTypeFFamily G) :
    N ∈ maximalSubgroups G ∧ OddOrder.BG.Ch4.S14.IsTypeP2 N ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
      Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
        ((M ⊓ N).subgroupOf N) ∧
      ∃ K₁ U₁ : Subgroup G,
        K₁ ≤ M ⊓ N ∧ U₁ ≤ M ⊓ N ∧ U₁ ≠ ⊥ ∧
        OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa N)
          (K₁.subgroupOf N) ∧
        OddOrder.Isaacs.Ch03.IsHallSubgroup
          ((OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
          (U₁.subgroupOf N) ∧
        (Nat.card ↥K₁).Prime ∧
        IsMulCommutative ↥U₁ ∧
        K₁ ≤ Subgroup.normalizer ((U₁ : Subgroup G) : Set G) ∧
        M ⊓ N = K₁ ⊔ U₁ := by
  classical
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hord, h, orderOf_one])
  have hxsharp : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := ⟨hxM, hx1⟩
  -- The escape gives `1 < |𝓜_σ(x)|`, exactly as in Corollary 15.9.
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxM hx1 h)
  obtain ⟨N', hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hxsharp hgt
  obtain ⟨hNmax', hCN', hRne', hRhall', hxtau2', hNtype', hforall'⟩ := hNstruct
  have hxN' : x ∈ N' := hCN' (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  -- Our given `N ⊇ C_G(x)` is that unique neighbour.
  have hNeq : N = N' := Set.mem_singleton_iff.mp
    ((OddOrder.BG.Ch4.S14.maximalContaining_centralizer_eq_singleton_of_tau2_element hG
      hNmax' hxN' hx1 hxtau2' hRne') ▸ hNmem)
  subst hNeq
  -- `N` is type-P₂ (`IsTypeF N ∨ IsTypeP2 N` with `N ∉ ℳ_𝓕`).
  have hP2N : OddOrder.BG.Ch4.S14.IsTypeP2 N :=
    hNtype'.resolve_left fun hF => hNnotF ⟨hNmax', hF⟩
  -- `M ∩ N` complements `N_σ` in `N` (signalizer conjunct at `M' := M`).
  have hMσx : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x := ⟨hM, hxM⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall' M hMσx
  -- Ambient complement form, as in Corollary 15.9.
  have hEleN : M ⊓ N ≤ N := inf_le_right
  have hinf : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) = ⊥ := by
    have hd : Disjoint (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)) N := by
      rw [← Subgroup.subgroupOf_eq_bot]
      change (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)).comap N.subtype = ⊥
      rw [Subgroup.comap_inf]
      exact disjoint_iff.mp hcompl.disjoint
    have hle : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) ≤ N := inf_le_right.trans inf_le_right
    rw [← inf_of_le_left hle]
    exact disjoint_iff.mp hd
  have hsup : OddOrder.BG.Ch3.S10.Msigma N ⊔ (M ⊓ N) = N := by
    refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right) ?_
    rw [← Subgroup.subgroupOf_eq_top,
      Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right]
    exact hcompl.sup_eq_top
  -- The `E`-setup on `N` with `E := M ∩ N`, and its type-P₂ matched Hall pair.
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := subgroupESetup_of_complement hG hNmax' hEleN hinf hsup
  obtain ⟨-, hU0E, hU0ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩ :=
    typeP2_matched_kappa_hall_pair_of_esetup hG hNmax' hP2N hsetup
  -- `|K₁|` is prime (BG's *"|K₁| is prime"*, from the type-P₂ structure).
  obtain ⟨qk, hqkprime, hcardK⟩ :=
    OddOrder.BG.Ch4.S15.card_kappaHall_prime_of_isTypeP2 hG hNmax' hP2N
      (hsetup.E₁_le.trans hEleN) hK₀
  -- `M ∩ N = K₁ ⊔ U₁`, from `E = E₁ ⊔ E₂ ⊔ E₃`.
  have hsupMN : M ⊓ N = E₁ ⊔ (E₂ ⊔ E₃) := by
    have h := (subgroupE_basic hG hsetup).2.2.2.2.1.1
    rwa [sup_assoc] at h
  exact ⟨hNmax', hP2N, hCN', hRne', hcompl,
    E₁, E₂ ⊔ E₃, hsetup.E₁_le, hU0E, hU0ne, hK₀, hU₀, hcardK ▸ hqkprime, hU₀ab, hK₀NU₀,
    hsupMN⟩

end OddOrder.BG.AppE
