/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults

/-! # BG Lemma 14.13(a): a non-disjoint signalizer forces Frobenius type

**Bender–Glauberman, Lemma 14.13(a)** (LMS LNS 188, Ch. IV, mmd L4131; Coq
`non_disjoint_signalizer_Frobenius`, BGsection14:2412): for `x ∈ M_σ^#` with more than one
`σ`-maximal, if `σ(N[x])` meets `π(M)` (`N[x]` the signalizer neighbour over `C_G(x)`), then
`M` is of type `F` with no `τ₂`-primes, and `M` is a Frobenius group with kernel `M_σ`.

The proof follows the Coq script:
* a prime `q ∈ σ(N) ∩ π(M)` lies in `β(N)` (Theorem 14.4(d)), hence is ideal in `G`;
* the primes `p` of `orderOf x` lie in `σ(M) ∩ τ₂(N)` (Theorem 14.4(c)), so `N` is not
  conjugate to `M` and `q ∉ σ(M)` (Theorem 13.9);
* a rank-one `q`-subgroup `Q ≤ M` conjugates into `N` (`q ∈ σ(N)`), and Corollary 12.14
  pins `ℳ(C_G(Q)) = {N^g}`;
* **type `F`**: type `P₂` fails since `σ(M) = β(M)` (Proposition 14.2(g)) contradicts
  `p ∈ σ(M) ∖ β(M)` (Lemma 12.1(g)); type `P₁` fails since then `q ∈ κ(M)`, the dual-pair
  partner `M*` of Theorem 14.7 satisfies `ℳ(C_G(Q)) = {M*}` (so `M* = N^g`), its `κ`-Hall
  factor `K*` is a `σ(M)`-Hall subgroup of `M*` (Proposition 14.2(f)), forcing
  `p ∈ π(K*) ⊆ κ(M*) ⊆ τ₁(M*) ∪ τ₃(M*)` of rank one — against `r_p(M*) = r_p(N) = 2`;
* **no `τ₂`-primes**: a prime `p' ∈ τ₂(M)` has `r_{p'}(N) ≤ 1` (partition of `π(N)` plus
  14.4(c)/(d)), Corollary 12.9 applied to `A ∈ ℰ_{p'}²(E)`, `Q ∈ ℰ_q¹(E)` produces
  non-conjugate rank-one subgroups `[A,Q]` and `C_A(Q)`, which both land in the cyclic
  Sylow `p'`-subgroup of `N` — contradiction;
* **Frobenius**: with `κ(M) = ∅` and no `τ₂`-primes, every prime of the `σ(M)`-complement
  `E` is in `τ₁ ∪ τ₃`, so a fixed point of `e ∈ E^#` on `M_σ^#` would put the prime in
  `κ(M)`.

The `τ₂(M)`-freeness is stated for **primes** only (`∀ p, p.Prime → p ∉ tau2 M`): the repo
`tau2` does not exclude composite exponents (a `C_{15} × C_{15} ≤ M` would put `15 ∈ τ₂(M)`),
so the literal `τ₂(M) = ∅` is not faithful — same prime-restriction as Lemma 12.11
(`tau2_prime_mem_sigma_diff_beta`).
-/

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Conjugation transport for `β` and `pRank` -/

/-- `MulAut` smul is `map` along the automorphism (local copy of the S14 helper). -/
private theorem mulAut_smul_eq_map' (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- The conjugation isomorphism `↥H ≃* ↥(H^g)`. -/
private noncomputable def conjSubgroupEquiv (g : G) (H : Subgroup G) :
    ↥H ≃* ↥(MulAut.conj g • H) :=
  (Subgroup.equivMapOfInjective H (MulAut.conj g : G →* G)
    (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (mulAut_smul_eq_map' (MulAut.conj g) H).symm)

/-- `pRank` is conjugation-invariant: `r_p(M^g) = r_p(M)`. -/
theorem pRank_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) (p : ℕ) :
    pRank ↥(MulAut.conj g • M) p = pRank ↥M p :=
  (OddOrder.BG.Ch3.S13.pRank_eq_of_mulEquiv (p := p) (conjSubgroupEquiv g M)).symm

/-- `β` is conjugation-invariant: `β(M^g) = β(M)`.  `α` transports along the conjugation
isomorphism (`Nat.card` and `pRank` invariance), and `idealPrime` is a `G`-global condition. -/
theorem beta_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.beta (MulAut.conj g • M) = OddOrder.BG.Ch3.S10.beta M := by
  have e := conjSubgroupEquiv g M
  ext p
  simp only [OddOrder.BG.Ch3.S10.mem_beta_iff, OddOrder.BG.Ch3.S10.mem_alpha_iff]
  rw [Nat.card_congr e.toEquiv, OddOrder.BG.Ch3.S13.pRank_eq_of_mulEquiv (p := p) e]

/-- Transport of a conjugation from `↥N` back to `G`: for `K ≤ N` and `n : ↥N`,
`(nᶜ • (K.subgroupOf N)).map N.subtype = (↑n)ᶜ • K`.  (Replicates the `private`
`map_subtype_conj_subgroupOf` of `S13_PrimeAction`.) -/
private theorem map_subtype_conj_smul_subgroupOf {N : Subgroup G} (n : ↥N) {K : Subgroup G}
    (hKN : K ≤ N) :
    (MulAut.conj n • (K.subgroupOf N)).map N.subtype = MulAut.conj (n : G) • K := by
  have e1 : (MulAut.conj n • (K.subgroupOf N))
      = (K.subgroupOf N).map ((MulAut.conj n : ↥N →* ↥N)) := by
    rw [Subgroup.pointwise_smul_def]; rfl
  have e2 : (MulAut.conj (n : G) • K) = K.map ((MulAut.conj (n : G) : G →* G)) := by
    rw [Subgroup.pointwise_smul_def]; rfl
  rw [e1, e2, Subgroup.map_map,
    show N.subtype.comp ((MulAut.conj n : ↥N →* ↥N))
        = ((MulAut.conj (n : G) : G →* G)).comp N.subtype from by ext ⟨x, hx⟩; rfl,
    ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKN]

/-- **Order-`p` subgroups of a group with cyclic Sylow `p` are conjugate.**  If `p` is odd,
`r_p(N) ≤ 1` (so the Sylow `p`-subgroups of `↥N` are cyclic), and `A, B ≤ N` both have order
`p`, then `A` and `B` are `N`-conjugate.  Each lies in a (cyclic) Sylow `p`-subgroup of `↥N`;
the Sylows are conjugate, and a cyclic `p`-group has a unique subgroup of order `p`. -/
theorem exists_conj_smul_eq_of_le_of_card_prime [Finite G] {N : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hodd : Odd p) (hpr : pRank ↥N p ≤ 1)
    {A B : Subgroup G} (hAN : A ≤ N) (hBN : B ≤ N)
    (hAp : Nat.card ↥A = p) (hBp : Nat.card ↥B = p) :
    ∃ n : G, n ∈ N ∧ MulAut.conj n • A = B := by
  classical
  set A' : Subgroup ↥N := A.subgroupOf N with hA'def
  set B' : Subgroup ↥N := B.subgroupOf N with hB'def
  have hA'card : Nat.card ↥A' = p := by
    rw [hA'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hAp]
  have hB'card : Nat.card ↥B' = p := by
    rw [hB'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hBp]
  have hA'pg : IsPGroup p ↥A' := by rw [IsPGroup.iff_card]; exact ⟨1, by rw [hA'card, pow_one]⟩
  have hB'pg : IsPGroup p ↥B' := by rw [IsPGroup.iff_card]; exact ⟨1, by rw [hB'card, pow_one]⟩
  obtain ⟨P, hA'P⟩ := hA'pg.exists_le_sylow
  obtain ⟨Q, hB'Q⟩ := hB'pg.exists_le_sylow
  haveI : MulAction.IsPretransitive ↥N (Sylow p ↥N) := Sylow.isPretransitive_of_finite
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥N P Q
  haveI hQcyc : IsCyclic ↥(Q : Subgroup ↥N) :=
    OddOrder.BG.Ch3.S10.isCyclic_of_pRank_le_one Q.isPGroup' hodd
      (by rw [pRank_sylow_eq Q]; exact hpr)
  -- `n • A' ≤ Q`.
  have hnA'Q : (MulAut.conj n • A' : Subgroup ↥N) ≤ (Q : Subgroup ↥N) := by
    have h1 : (MulAut.conj n • A' : Subgroup ↥N) ≤ MulAut.conj n • (P : Subgroup ↥N) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hA'P
    have h2 : (MulAut.conj n • (P : Subgroup ↥N)) = (Q : Subgroup ↥N) := by
      have := congrArg (Sylow.toSubgroup) hn
      rwa [Sylow.coe_subgroup_smul] at this
    rwa [h2] at h1
  have hnA'card : Nat.card ↥(MulAut.conj n • A' : Subgroup ↥N) = p := by
    have hsm : (MulAut.conj n • A' : Subgroup ↥N) = A'.map ((MulAut.conj n : ↥N →* ↥N)) := by
      rw [Subgroup.pointwise_smul_def]; rfl
    rw [hsm, Nat.card_congr (Subgroup.equivMapOfInjective A' (MulAut.conj n : ↥N →* ↥N)
      (MulAut.conj n).injective).symm.toEquiv, hA'card]
  -- Two order-`p` subgroups of the cyclic `Q` coincide.
  have heqQ : (MulAut.conj n • A' : Subgroup ↥N).subgroupOf Q = B'.subgroupOf Q :=
    OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥(Q : Subgroup ↥N)) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnA'Q).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'Q).toEquiv, hnA'card, hB'card])
  have heq : (MulAut.conj n • A' : Subgroup ↥N) = B' := by
    have h := congrArg (Subgroup.map (Q : Subgroup ↥N).subtype) heqQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hnA'Q, Subgroup.map_subgroupOf_eq_of_le hB'Q] at h
  -- Transport to `G`.
  refine ⟨(n : G), n.2, ?_⟩
  have hmap := congrArg (Subgroup.map N.subtype) heq
  rwa [map_subtype_conj_smul_subgroupOf n hAN, hB'def,
    Subgroup.map_subgroupOf_eq_of_le hBN] at hmap

/-- **`Kstar` is a `σ(M)`-Hall of the type-`P` partner `Mstar`** (Coq `Ptype_embedding`'s
`sMhallKs`): for a type-`P` maximal `M` with `κ`-Hall `K`, `Kstar = C_{M_σ}(K)`, and its
nonconjugate type-`P` partner `Mstar` (with `K ≤ Mstar_σ`), the `σ(M)`-group `Kstar` is a
`σ(M)`-Hall subgroup of `Mstar`.

A `σ(M)`-Hall `Y ⊇ Kstar` of `Mstar` (Hall's theorem in the solvable `Mstar`) lies in `M_σ`
(Proposition 14.2(f), `typeP_sigma_subgroup_le_Msigma`, since `Kstar ≠ 1` meets `Y`), and
`⁅Y, K⁆ ≤ M_σ ⊓ Mstar_σ = 1` (`σ(M)`, `σ(Mstar)` disjoint by Theorem 13.9), so `Y ≤ C(K)`,
giving `Y ≤ M_σ ⊓ C(K) = Kstar`; hence `Y = Kstar`. -/
theorem kstar_isHall_sigmaM_of_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroups G) (hKstar_ne : Kstar ≠ ⊥)
    (hKstarMstar : Kstar ≤ Mstar)
    (hKMstarσ : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Kstar.subgroupOf Mstar) := by
  classical
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstar
  -- `Kstar ≤ M_σ` is a `σ(M)`-group.
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hKstarpi : ∀ r ∈ (Nat.card ↥(Kstar.subgroupOf Mstar)).primeFactors,
      r ∈ OddOrder.BG.Ch3.S10.sigma M := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstarMstar).toEquiv] at hr
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKstarMσ) Nat.card_pos.ne' hr)
  -- A `σ(M)`-Hall `H ⊇ Kstar` of `↥Mstar`; `Y = H` back in `G`.
  obtain ⟨H, hHhall, hKstarH⟩ := Ch03.hall_D (G := ↥Mstar)
    (π := OddOrder.BG.Ch3.S10.sigma M) hKstarpi
  set Y : Subgroup G := H.map Mstar.subtype with hYdef
  have hYMstar : Y ≤ Mstar := Subgroup.map_subtype_le _
  have hKstarY : Kstar ≤ Y := by
    rw [hYdef, ← Subgroup.map_subgroupOf_eq_of_le hKstarMstar]
    exact Subgroup.map_mono hKstarH
  have hYcard : Nat.card ↥Y = Nat.card ↥H :=
    (Nat.card_congr (Subgroup.equivMapOfInjective H Mstar.subtype
      Mstar.subtype_injective).toEquiv).symm
  have hYpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Y := by
    intro r hr; rw [hYcard] at hr; exact hHhall.1 r hr
  have hYlt : Y < ⊤ := lt_of_le_of_lt hYMstar (mem_maximalSubgroups.mp hMstar).lt_top
  have hYmeet : Y ⊓ Kstar ≠ ⊥ := by rw [inf_eq_right.mpr hKstarY]; exact hKstar_ne
  have hYMσ : Y ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    S14.typeP_sigma_subgroup_le_Msigma hG hM hP hKM hK hKstar hU hYlt hYpi hYmeet
  -- `⁅Y, K⁆ ≤ M_σ ⊓ Mstar_σ = 1`.
  have hcomm_le : ∀ {H₀ J : Subgroup G}, J ≤ Subgroup.normalizer (H₀ : Set G) →
      ⁅H₀, J⁆ ≤ H₀ := by
    intro H₀ J hJN
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbab : b * a⁻¹ * b⁻¹ ∈ H₀ :=
      (Subgroup.mem_normalizer_iff.mp (hJN hb) a⁻¹).mp (H₀.inv_mem ha)
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) from by group]
    exact H₀.mul_mem ha hbab
  have hM_normMσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    have hn : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mp hn
  have hMstar_normMσ : Mstar ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma Mstar : Set G) := by
    have hn : ((OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (OddOrder.BG.Ch3.S10.Msigma_le Mstar)).mp hn
  have hYK_MσM : ⁅Y, K⁆ ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    (Subgroup.commutator_mono hYMσ le_rfl).trans (hcomm_le (hKM.trans hM_normMσ))
  have hYK_MσMstar : ⁅Y, K⁆ ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hKMstarσ le_rfl).trans
      (hcomm_le (hYMstar.trans hMstar_normMσ))
  have hMMdisj : OddOrder.BG.Ch3.S10.Msigma M ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    refine coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M) (fun r hr => ?_)
    exact fun hrM => Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hMstar hnc) hrM
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar r hr)
  have hYcK : Y ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((le_inf hYK_MσM hYK_MσMstar).trans hMMdisj.le))
  have hYeq : Y = Kstar := le_antisymm (by rw [hKstar]; exact le_inf hYMσ hYcK) hKstarY
  have hKsub_eq : Kstar.subgroupOf Mstar = H := by
    rw [← hYeq, hYdef]
    exact Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective H
  rw [hKsub_eq]; exact hHhall

/-! ## The Frobenius consequence of type `F` with no `τ₂`-primes -/

/-- **Type `F` with no `τ₂`-primes is Frobenius over `M_σ`** (the `∃ U` conclusion of BG
Lemma 14.13(a)): if `κ(M) = ∅`, no prime lies in `τ₂(M)`, and some prime of `π(M)` is
outside `σ(M)` (so the complement is nontrivial), then `M = M_σ ⋊ E` is a Frobenius group.

A fixed point `n ∈ M_σ^#` of `e ∈ E^#` would give a prime `r` of `orderOf e` — necessarily
in `τ₁(M) ∪ τ₃(M)` by the `π(E)`-partition (Lemma 12.1) and `τ₂`-freeness — a rank-one
subgroup `X ≤ ⟨e⟩` with `C_{M_σ}(X) ≠ 1`, i.e. `r ∈ κ(M)` — contradiction. -/
theorem typeF_frobenius_of_esetup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M)
    (ht2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M)
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (hEne : E.subgroupOf M ≠ ⊥) :
    Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) := by
  classical
  have hcompl : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).IsComplement'
      (E.subgroupOf M) := hsetup.isComplement'_subgroupOf
  have hMσhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
  have hcardE : Nat.card ↥(E.subgroupOf M) =
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := (hcompl.symm.index_eq_card).symm
  -- `π(E) ⊆ σ(M)ᶜ` (the complement realizes the `σ'`-index).
  have hEpi : ∀ r ∈ (Nat.card ↥(E.subgroupOf M)).primeFactors,
      r ∉ OddOrder.BG.Ch3.S10.sigma M := by
    intro r hr
    rw [hcardE] at hr
    exact hMσhall.2 r hr
  refine ⟨hcompl, ?_⟩
  refine
    { isNormal := ?_
      isComplement := hcompl
      ne_bot_kernel := ?_
      ne_bot_complement := hEne
      conj_frobenius := ?_ }
  · rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  · intro hbot
    have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ :=
      OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    exact hMσne (by
      have := congrArg (Subgroup.map M.subtype) hbot
      rwa [Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M),
        Subgroup.map_bot] at this)
  · -- Frobenius action: no nontrivial fixed points.
    intro a haE ha1 n hnMσ hn1 hfix
    -- `n` commutes with `a` (as elements of `↥M`, hence of `G`).
    have hcomm : Commute (a : G) (n : G) := by
      have hcM : a * n = n * a := mul_inv_eq_iff_eq_mul.mp hfix
      have h2 := congrArg (fun z : ↥M => (z : G)) hcM
      simpa using h2
    -- a prime `r ∣ orderOf (a : G)`, with an order-`r` power `c` of `a`.
    have haG1 : (a : G) ≠ 1 := fun h => ha1 (by
      apply Subtype.ext
      simpa using h)
    have hordne : orderOf (a : G) ≠ 1 := fun h => haG1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr_prime, hr_dvd⟩ := (orderOf (a : G)).exists_prime_and_dvd hordne
    haveI : Fact r.Prime := ⟨hr_prime⟩
    have hrcard : r ∣ Nat.card ↥(Subgroup.zpowers (a : G)) := by
      rwa [Nat.card_zpowers]
    obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers (a : G))) r
      hrcard
    have hcz : (c : G) ∈ Subgroup.zpowers (a : G) := c.2
    have hc_ordG : orderOf (c : G) = r := by
      rw [← hc_ord]
      exact (orderOf_injective (Subgroup.zpowers (a : G)).subtype
        (Subgroup.zpowers (a : G)).subtype_injective c).symm ▸ rfl
    -- `X = ⟨c⟩ ∈ ℰ_r¹(M)`.
    set X : Subgroup G := Subgroup.zpowers (c : G) with hXdef
    have hXcard : Nat.card ↥X = r := by rw [hXdef, Nat.card_zpowers, hc_ordG]
    have hXelem : X ∈ elemAbelianOfRank G r 1 :=
      mem_elemAbelianOfRank.mpr
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    have haM : (a : G) ∈ E := by
      have := haE
      rwa [Subgroup.mem_subgroupOf] at this
    have hXE : X ≤ E := by
      rw [hXdef, Subgroup.zpowers_le]
      exact (Subgroup.zpowers_le.mpr haM) hcz
    have hXM : X ≤ M := hXE.trans hsetup.E_le
    -- `r ∈ π(E) ∖ σ(M) ∖ τ₂(M) ⊆ τ₁(M) ∪ τ₃(M)`.
    have hrE : r ∈ (Nat.card ↥E).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
      calc r = Nat.card ↥X := hXcard.symm
        _ ∣ Nat.card ↥E := Subgroup.card_dvd_of_le hXE
    have hrτ : r ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
      hsetup.mem_tau_union_of_mem_primeFactors hG hrE
    have hrτ13 : r ∈ tau1 M ∪ tau3 M := by
      rcases hrτ with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 (ht2 r hr_prime)
      · exact Or.inr h3
    -- `n` centralizes `X` and lies in `M_σ`, so `r ∈ κ(M)` — against type `F`.
    have hnG : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
      have := hnMσ
      rwa [Subgroup.mem_subgroupOf] at this
    have hcn : Commute (c : G) (n : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← hk]; exact hcomm.zpow_left k
    have hnX : (n : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hXdef] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hcn.zpow_left m).eq
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      have hnG1 : (n : G) ≠ 1 := fun h => hn1 (by
        apply Subtype.ext
        simpa using h)
      exact hnG1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hnG, hnX⟩))
    have hrκ : r ∈ S14.kappa M := ⟨hr_prime, hrτ13, X, hXelem, hXM, hne⟩
    rw [hF] at hrκ
    exact Set.notMem_empty r hrκ

/-- **BG Corollary 15.6, Frobenius form (existential)**: a type-`F` maximal `M` with `τ₂(M) = ∅` and
some prime `q ∈ π(M) ∖ σ(M)` (so its `σ(M)'`-complement is nontrivial) is a Frobenius group
`M = M_σ ⋊ E`.  Obtains an arbitrary `E`-setup, derives `E ≠ ⊥` from `q ∣ |E|`, and reads off the
Frobenius structure via `typeF_frobenius_of_esetup`.  Consumers needing the *specific* cyclic
complement (`E = E₁` when additionally `E₂ = E₃ = ⊥`, Corollary 15.9) call `_of_esetup` with their
own setup. -/
theorem typeF_frobenius_of_tau2_prime_free [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M)
    (ht2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M)
    {q : ℕ} (hqπ : q ∈ S14.piSet M) (hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M) :
    ∃ U : Subgroup G,
      Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
  have hMσhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
  have hcardE : Nat.card ↥(E.subgroupOf M) =
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    (hsetup.isComplement'_subgroupOf.symm.index_eq_card).symm
  have hEne : E.subgroupOf M ≠ ⊥ := by
    have hqE : q ∣ Nat.card ↥(E.subgroupOf M) := by
      rw [hcardE]
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqπ
      have hdvdM : q ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hqπ).2.1
      have hprod : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) *
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index = Nat.card ↥M :=
        Subgroup.card_mul_index _
      rcases (Nat.Prime.dvd_mul hq_prime).mp (hprod ▸ hdvdM) with h | h
      · exact absurd (hMσhall.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h, Nat.card_pos.ne'⟩)) hqσ
      · exact h
    intro hbot
    rw [hbot, Subgroup.card_bot, Nat.dvd_one] at hqE
    exact (Nat.prime_of_mem_primeFactors hqπ).one_lt.ne' hqE
  exact ⟨E, typeF_frobenius_of_esetup hG hM hF ht2 hsetup hEne⟩

/-! ## BG Lemma 14.13(a) -/

/-- **BG Lemma 14.13(a)** (mmd L4131; Coq `non_disjoint_signalizer_Frobenius`,
BGsection14:2412), faithful form: for `x ∈ M_σ^#` with more than one `σ`-maximal, if `σ(N[x])`
meets `π(M)` (`N[x] = FT_signalizerBase x` the signalizer neighbour), then `M` is of type `F`,
no prime lies in `τ₂(M)`, and `M` is a Frobenius group with kernel `M_σ`.

This is the faithful restatement flagged on the mis-encoded `S14.sigmaLength_one_frobenius_type`
(issue 8020, whose `M, N ∈ 𝓜_σ(x)` non-conjugate premise is vacuous): the second maximal is the
*signalizer neighbour* `N[x]` over `C_G(x)`, not a second `σ`-maximal.  The `ℓ_σ(x) = 1`
hypothesis of the Coq original is dropped as derivable (`S14.Msigma_ell1`), and the Coq
`\tau2(M)^'.-group M` conclusion is stated prime-wise (`∀ p, p.Prime → p ∉ τ₂ M`) because the
repo `tau2` admits composite exponents (module docstring). -/
theorem non_disjoint_signalizer_frobenius [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard)
    (hnd : (OddOrder.BG.Ch3.S10.sigma (FT_signalizerBase x) ∩ S14.piSet M).Nonempty) :
    S14.IsTypeF M ∧ (∀ p : ℕ, p.Prime → p ∉ tau2 M) ∧
      ∃ U : Subgroup G,
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
          (U.subgroupOf M) ∧
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) := by
  classical
  have hx1 : x ≠ 1 := hxM.2
  -- ### Part 0: the signalizer neighbour `N` and the primes `q`, `p`
  -- Escape: `C_G(x) ≰ M` (else `𝓜_σ(x) = {M}` contradicts `hgt`).
  have hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M := by
    intro hle
    rw [maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le hG hM hxM.1 hx1 hle,
      Set.ncard_singleton] at hgt
    exact lt_irrefl 1 hgt
  obtain ⟨N₀, hN₀⟩ :=
    maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape hG hM hxM hesc
  have huniq₀ : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)),
      L = N₀ := fun L hL => by rwa [hN₀, Set.mem_singleton_iff] at hL
  have hbr : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : FT_signalizerBase x = N₀ := by
    rw [show FT_signalizerBase x = hbr.2.choose from dif_pos hbr]
    exact huniq₀ _ hbr.2.choose_spec
  -- The signalizer structure at `x`; its unique maximal is `N₀`.
  obtain ⟨N, ⟨hNmax, hNC, hNRne, hNhall, hNt2, hNdichot, hNper⟩, -⟩ :=
    signalizer_structure_of_mem_sigmaSharp hG hM hxM hgt
  have hNeq : N = N₀ :=
    huniq₀ N (mem_maximalSubgroupsContaining.mpr ⟨hNmax, hNC⟩)
  rw [hbase, ← hNeq] at hnd
  -- `q ∈ σ(N) ∩ π(M)`, so `q ∈ β(N)` (Theorem 14.4(d)) and `q` is ideal in `G`.
  obtain ⟨q, hqσN, hqπM⟩ := hnd
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqπM
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hMmem : M ∈ S14.maximalSigmaSubgroupsOfElement x := ⟨hM, hxM.1⟩
  obtain ⟨hst2NsM, hspM_sbN, -, -⟩ := hNper M hMmem
  have hqβN : q ∈ OddOrder.BG.Ch3.S10.beta N := hspM_sbN ⟨hqσN, hqπM⟩
  have hqIdeal : OddOrder.BG.Ch3.S10.idealPrime q G := hqβN.2
  -- `p := minFac (orderOf x)`: `p ∈ σ(M)` and `p ∈ τ₂(N)` (Theorem 14.4(c)).
  have hp_prime : (orderOf x).minFac.Prime :=
    Nat.minFac_prime (fun h => hx1 (orderOf_eq_one_iff.mp h))
  set p : ℕ := (orderOf x).minFac with hpdef
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hox0 : orderOf x ≠ 0 := by
    rw [← Nat.card_zpowers x]; exact Nat.card_pos.ne'
  have hpordx : p ∈ (orderOf x).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, Nat.minFac_dvd _, hox0⟩
  have hpt2N : p ∈ tau2 N := by
    refine hNt2 p ?_
    change p ∈ (Nat.card ↥(Subgroup.closure ({x} : Set G))).primeFactors
    rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    S14.isPiElement_sigma_of_mem_Msigma hxM.1 p hpordx
  -- `N` is not conjugate to `M` (`p ∈ σ(M) ∖ σ(N)`), so `q ∉ σ(M)` (Theorem 13.9).
  have hnc : ¬ ∃ g : G, MulAut.conj g • M = N := by
    rintro ⟨g, hg⟩
    exact hpt2N.1 (by rw [← hg, S14.sigma_conj_smul_eq]; exact hpσM)
  have hqσM : q ∉ OddOrder.BG.Ch3.S10.sigma M := fun hq =>
    Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hNmax hnc) hq hqσN
  -- A rank-one `q`-subgroup `Q = ⟨y⟩ ≤ M`.
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) q
    (Nat.mem_primeFactors.mp hqπM).2.1
  set y : G := (y₀ : G) with hydef
  have hyM : y ∈ M := y₀.2
  have hy_ord : orderOf y = q := by
    rw [hydef, ← hy₀]
    exact (orderOf_injective M.subtype M.subtype_injective y₀).symm ▸ rfl
  set Q : Subgroup G := Subgroup.zpowers y with hQdef
  have hQcard : Nat.card ↥Q = q := by rw [hQdef, Nat.card_zpowers, hy_ord]
  have hQelem : Q ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hQcard, by rw [hQcard, pow_one]⟩
  have hQM : Q ≤ M := by rw [hQdef, Subgroup.zpowers_le]; exact hyM
  have hQq : IsPGroup q ↥Q := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hQcard, pow_one]⟩
  -- Conjugate `Q` into `N` (`q ∈ σ(N)`: a `q`-subgroup conjugates into `N_σ ≤ N`).
  obtain ⟨g, hQNg⟩ : ∃ g : G, Q ≤ MulAut.conj g • N := by
    obtain ⟨g, hg⟩ :=
      OddOrder.BG.Ch3.S13.exists_conj_smul_le_Msigma_of_pSubgroup hG hNmax hqσN hQq
    refine ⟨g⁻¹, ?_⟩
    have h1 : (MulAut.conj g • Q : Subgroup G) ≤ N :=
      hg.trans (OddOrder.BG.Ch3.S10.Msigma_le N)
    have h2 : (MulAut.conj g⁻¹ • (MulAut.conj g • Q) : Subgroup G) ≤ MulAut.conj g⁻¹ • N :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h1
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  set Ng : Subgroup G := MulAut.conj g • N with hNgdef
  have hNgmax : Ng ∈ maximalSubgroups G :=
    S14.mem_maximalSubgroups_of_isConjugateSubgroup hNmax ⟨g, rfl⟩
  have hqσNg : q ∈ OddOrder.BG.Ch3.S10.sigma Ng := by
    rw [hNgdef, S14.sigma_conj_smul_eq]; exact hqσN
  have hqβNg : q ∈ OddOrder.BG.Ch3.S10.beta Ng := by
    rw [hNgdef, beta_conj_smul_eq]; exact hqβN
  -- Corollary 12.14: `ℳ(C_G(Q)) = {N^g}`.
  have huniqNg : maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Ng} :=
    OddOrder.BG.Ch3.S12.Cor1214.maximalContaining_centralizer_eq_singleton hG hNgmax hqσNg
      hQelem hQNg (Or.inl hqβNg)
  -- `p ∉ β(M)` (Lemma 12.1(g) via the rank-two witness in `N`).
  have hpβM : p ∉ OddOrder.BG.Ch3.S10.beta M := by
    intro hβ
    obtain ⟨A', hA', hA'N⟩ :=
      OddOrder.BG.Ch3.S12.exists_mem_elemAbelianOfRank_two_le_of_tau2 hp_prime hpt2N
    exact (OddOrder.BG.Ch3.S12.isMaximalElementaryAbelian_of_mem_tau2 hG hNmax hp_prime
      hpt2N hA'N hA').2 hβ.2
  -- `r_p(N) = 2`, transported to any conjugate.
  have hrpN : pRank ↥N p = 2 := hpt2N.2
  -- ### Part 1: `M` is of type `F`
  have hFM : S14.IsTypeF M := by
    by_contra hnF
    have hP : S14.IsTypeP M := Set.nonempty_iff_ne_empty.mpr hnF
    rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
    · -- Type `P₁`: the dual-pair partner `Mstar = Nᵍ` has `Kstar` as its `κ(Mstar)`-Hall *and*
      -- `σ(M)`-Hall, so `p ∈ σ(M) ∩ π(Mstar)` forces `p ∈ κ(Mstar)` (rank ≤ 1) against
      -- `r_p(Mstar) = 2`.
      haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
      -- `q ∈ κ(M)` (type P₁: `κ(M) = π(M) ∖ σ(M)`).
      have hqκ : q ∈ S14.kappa M := by rw [hP1.2]; exact ⟨hqπM, hqσM⟩
      -- A `κ(M)`-Hall `K ⊇ Q`.
      have hQκpi : ∀ r ∈ (Nat.card ↥(Q.subgroupOf M)).primeFactors, r ∈ S14.kappa M := by
        intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv, hQcard,
          Nat.Prime.primeFactors hq_prime, Finset.mem_singleton] at hr
        rw [hr]; exact hqκ
      obtain ⟨K', hK'hall, hQK'⟩ := Ch03.hall_D (G := ↥M) (π := S14.kappa M) hQκpi
      set K : Subgroup G := K'.map M.subtype with hKdef
      have hKM : K ≤ M := Subgroup.map_subtype_le _
      have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
        have hh : K.subgroupOf M = K' :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
        rw [hh]; exact hK'hall
      have hQK : Q ≤ K := by
        rw [hKdef, ← Subgroup.map_subgroupOf_eq_of_le hQM]; exact Subgroup.map_mono hQK'
      set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        with hKstardef
      obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
        ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      set U : Subgroup G := U'.map M.subtype with hUdef
      have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          (U.subgroupOf M) := by
        have hh : U.subgroupOf M = U' :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
        rw [hh]; exact hU'
      obtain ⟨-, hKstar_ne, -, -, -, -, -⟩ := S14.typeP_structure hG hM hP hKM hK hKstardef hU
      -- The partner `Mstar` (Theorem 14.7).
      obtain ⟨Mstar, ⟨hMstarmax, hMstarP, hMstarnc, ⟨hKstarMstar, hKstarHall, hKeq⟩, -, -, -, -⟩, -⟩ :=
        (S14.typeP_duality hG hM hP hKM hK hKstardef).2.2
      have hKMstarσ : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by rw [hKeq]; exact inf_le_left
      -- `ℳ(C(Q)) = {Mstar}` (typeP_structure of `Mstar`, `Q ≤ K = C_{Mstar_σ}(Kstar)`).
      haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
      obtain ⟨Ustar', hUstar'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
        ((S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      set Ustar : Subgroup G := Ustar'.map Mstar.subtype with hUstardef
      have hUstar : Ch03.IsHallSubgroup ((S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
          (Ustar.subgroupOf Mstar) := by
        have hh : Ustar.subgroupOf Mstar = Ustar' :=
          Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Ustar'
        rw [hh]; exact hUstar'
      obtain ⟨-, -, -, -, -, hd2Mstar, -⟩ :=
        S14.typeP_structure hG hMstarmax hMstarP hKstarMstar hKstarHall hKeq hUstar
      have hMstarNg : Mstar = Ng :=
        (Set.singleton_injective (huniqNg.symm.trans (hd2Mstar q hq_prime Q hQelem hQK))).symm
      -- `Kstar` is a `σ(M)`-Hall of `Mstar`.
      have hKstarσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
          (Kstar.subgroupOf Mstar) :=
        kstar_isHall_sigmaM_of_partner hG hM hP hKM hK hKstardef hU hMstarmax hKstar_ne
          hKstarMstar hKMstarσ hMstarnc
      -- `r_p(Mstar) = 2`, so `p ∈ π(Mstar)` and (σ(M)-Hall) `p ∈ π(Kstar)`, hence `p ∈ κ(Mstar)`.
      have hrpMstar : pRank ↥Mstar p = 2 := by
        rw [hMstarNg, hNgdef, pRank_conj_smul_eq g N p]; exact hrpN
      have hpπMstar : p ∈ (Nat.card ↥Mstar).primeFactors :=
        OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (by rw [hrpMstar]; norm_num)
      have hpπKstar : p ∈ (Nat.card ↥(Kstar.subgroupOf Mstar)).primeFactors := by
        have hprod : Nat.card ↥(Kstar.subgroupOf Mstar) * (Kstar.subgroupOf Mstar).index
            = Nat.card ↥Mstar := Subgroup.card_mul_index _
        rcases (Nat.Prime.dvd_mul hp_prime).mp
          (hprod ▸ (Nat.mem_primeFactors.mp hpπMstar).2.1) with h | h
        · exact Nat.mem_primeFactors.mpr ⟨hp_prime, h, Nat.card_pos.ne'⟩
        · exact absurd hpσM (hKstarσHall.2 p (Nat.mem_primeFactors.mpr
            ⟨hp_prime, h, Subgroup.index_ne_zero_of_finite⟩))
      have hpκMstar : p ∈ S14.kappa Mstar := hKstarHall.1 p hpπKstar
      rcases S14.kappa_subset_tau1_union_tau3 hpκMstar with hτ1 | hτ3
      · have h1 := tau1_pRank_eq_one hτ1; omega
      · have h1 := tau3_pRank_eq_one hτ3; omega
    · -- Type `P₂`: `σ(M) = β(M)` (Proposition 14.2(g)) contradicts `p ∈ σ(M) ∖ β(M)`.
      haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
      obtain ⟨K₀, hK₀⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
      obtain ⟨U₀, hU₀⟩ := Ch03.hall_E_exists (G := ↥M)
        ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      have hKeq : ((K₀.map M.subtype).subgroupOf M) = K₀ :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective K₀
      have hUeq : ((U₀.map M.subtype).subgroupOf M) = U₀ :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective U₀
      obtain ⟨-, -, -, -, hg5, -, -⟩ := S14.typeP_structure hG hM hP
        (Subgroup.map_subtype_le K₀) (by rw [hKeq]; exact hK₀) rfl
        (by rw [hUeq]; exact hU₀)
      obtain ⟨hσβ, -⟩ := hg5 hP2
      exact hpβM (hσβ ▸ hpσM)
  -- ### Part 2: no prime lies in `τ₂(M)`
  have ht2M : ∀ p' : ℕ, p'.Prime → p' ∉ tau2 M := by
    intro p' hp'p hp't2
    haveI : Fact p'.Prime := ⟨hp'p⟩
    have hp'σM : p' ∉ OddOrder.BG.Ch3.S10.sigma M := hp't2.1
    -- Rank-2 witness `A0M ∈ ℰ_p'²(M)`: gives `p' ∈ π(M)`, `¬ idealPrime p'`.
    obtain ⟨A0M, hA0M, hA0leM⟩ :=
      OddOrder.BG.Ch3.S12.exists_mem_elemAbelianOfRank_two_le_of_tau2 hp'p hp't2
    have hp'πM : p' ∈ S14.piSet M := by
      refine Nat.mem_primeFactors.mpr ⟨hp'p, ?_, Nat.card_pos.ne'⟩
      calc p' ∣ p' ^ 2 := dvd_pow_self p' two_ne_zero
        _ = Nat.card ↥A0M := (mem_elemAbelianOfRank.mp hA0M).2.symm
        _ ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hA0leM
    have hp'notideal : ¬ OddOrder.BG.Ch3.S10.idealPrime p' G :=
      (OddOrder.BG.Ch3.S12.isMaximalElementaryAbelian_of_mem_tau2 hG hM hp'p hp't2 hA0leM hA0M).2
    have hp'nβN : p' ∉ OddOrder.BG.Ch3.S10.beta N := fun hβ => hp'notideal hβ.2
    have hp'odd : Odd p' := hG.odd.of_dvd_nat
      ((Nat.mem_primeFactors.mp hp'πM).2.1.trans (Subgroup.card_subgroup_dvd_card M))
    -- Step A: `r_{p'}(N) ≤ 1`.
    have hrp'N : pRank ↥N p' ≤ 1 := by
      by_contra hlt
      rw [not_le] at hlt
      have hp'πN : p' ∈ (Nat.card ↥N).primeFactors :=
        OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega)
      by_cases hτ1 : p' ∈ tau1 N
      · exact absurd (tau1_pRank_eq_one hτ1) (by omega)
      by_cases hτ2 : p' ∈ tau2 N
      · exact hp'σM (hst2NsM (Set.mem_inter hτ2 hp'πN))
      · rcases OddOrder.BG.Ch3.S13.mem_sigma_or_tau3_of_not_tau1_tau2 hG hNmax hp'πN hτ1 hτ2 with
          hσN | hτ3
        · exact hp'nβN (hspM_sbN (Set.mem_inter hσN hp'πM))
        · exact absurd (tau3_pRank_eq_one hτ3) (by omega)
    -- Step B: an `E`-setup with `Q ≤ E`.
    have hQ_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) Q := by
      intro r hr
      rw [hQcard, Nat.Prime.primeFactors hq_prime, Finset.mem_singleton] at hr
      rw [hr]; exact hqσM
    obtain ⟨E, E₁, E₂, E₃, hsetup, hQE, -⟩ :=
      OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hQM hQ_pi
    -- Step C: a rank-2 `A ∈ ℰ_p'²(E)`.
    have hA0pi : Ch03.Subgroup.IsPiGroup (tau2 M) (A0M.subgroupOf M) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0leM).toEquiv,
        (mem_elemAbelianOfRank.mp hA0M).2, Nat.primeFactors_pow p' two_ne_zero,
        Nat.Prime.primeFactors hp'p] at hr
      rw [Finset.mem_singleton.mp hr]; exact hp't2
    obtain ⟨w, -, hwle⟩ := exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le
      hsetup.E₂_hall (tau2_subset_sigma_compl M) hA0leM hA0pi
    set A : Subgroup G := MulAut.conj w • A0M with hAdef
    have hA : A ∈ elemAbelianOfRank G p' 2 := conj_smul_mem_elemAbelianOfRank w hA0M
    have hAE : A ≤ E := hwle.trans hsetup.E₂_le
    -- `C_G(Q) ≤ Nᵍ`.
    have hCQNg : Subgroup.centralizer (Q : Set G) ≤ Ng := by
      have hmem : Ng ∈ maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) := by
        rw [huniqNg]; rfl
      exact (mem_maximalSubgroupsContaining.mp hmem).2
    have hNgN : (MulAut.conj g⁻¹ • Ng : Subgroup G) = N := by
      rw [hNgdef, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    -- Step D: `[A,Q] ≠ 1` (else `A ≤ C(Q) ≤ Nᵍ` gives `r_{p'}(N) ≥ 2`).
    have hAQ : (⁅A, Q⁆ : Subgroup G) ≠ ⊥ := by
      intro hcomm
      have hAcQ : A ≤ Subgroup.centralizer (Q : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hAN : (MulAut.conj g⁻¹ • A : Subgroup G) ≤ N :=
        hNgN ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hAcQ.trans hCQNg)
      have hArank : (MulAut.conj g⁻¹ • A) ∈ elemAbelianOfRank G p' 2 :=
        conj_smul_mem_elemAbelianOfRank g⁻¹ hA
      have h2le : 2 ≤ pRank ↥N p' := by
        have hea : ((MulAut.conj g⁻¹ • A).subgroupOf N).IsElementaryAbelian p' :=
          IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAN).symm
            (mem_elemAbelianOfRank.mp hArank).1
        have hle := le_pRank ((MulAut.conj g⁻¹ • A).subgroupOf N) hea
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv,
          (mem_elemAbelianOfRank.mp hArank).2, Nat.log_pow hp'p.one_lt] at hle
      omega
    have hQncA : ¬ Q ≤ Subgroup.centralizer (A : Set G) := fun h =>
      hAQ ((Subgroup.commutator_comm A Q).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h))
    -- Step E: `q ∈ τ₁(M)` (Cor 12.10(c): `q ∣ [E : C_E(A)]`, primes of that index are `τ₁`).
    obtain ⟨-, hEN, hτ1factor⟩ :=
      (OddOrder.BG.Ch3.S12.nilpotent_sigmaComplement_abelian hG hsetup).2.2.1 p' hp'p hp't2 A hA hAE
    have hqidx : q ∈
        (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
      set c : Subgroup G := E ⊓ Subgroup.centralizer (A : Set G) with hcdef
      have hcE : c ≤ E := inf_le_left
      haveI hcnorm : (c.subgroupOf E).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hcE).mpr hEN
      have hQ'qg : IsPGroup q ↥(Q.subgroupOf E) := by
        rw [IsPGroup.iff_card]
        exact ⟨1, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQcard, pow_one]⟩
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
        ⟨hq_prime, prime_dvd_index_of_sylow_not_le_of_normal P hPnc,
          Subgroup.index_ne_zero_of_finite⟩
    have hqτ1 : q ∈ tau1 M := hτ1factor q hqidx
    -- Step F: `C_{M_σ}(Q) = 1` (else `q ∈ κ(M)`, against type F).
    have hregQ : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
      by_contra hne
      have hqκ : q ∈ S14.kappa M := ⟨hq_prime, Or.inl hqτ1, Q, hQelem, hQM, hne⟩
      rw [hFM] at hqκ; exact Set.notMem_empty q hqκ
    -- Step G: Corollary 12.9 — `A0 = [A,Q]`, `A1 = C_A(Q)`, both rank one, non-conjugate.
    obtain ⟨⟨hA0elem, -, hA0eq, -⟩, hnconj, hA1elem, -, -⟩ :=
      OddOrder.BG.Ch3.S12.commutator_decomp_of_tau1_action hG hsetup hp't2 hqτ1 hA hAE
        hQelem hQE hregQ hAQ
    -- Step H: `A0 ⊆ N`, `A1^{g⁻¹} ⊆ N`; cyclic Sylow ⟹ conjugate ⟹ contra `hnconj`.
    have hA0N : (⁅A, Q⁆ : Subgroup G) ≤ N := by
      rw [hA0eq]
      refine inf_le_right.trans ((Subgroup.centralizer_le ?_).trans hNC)
      intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hxM.1
    have hA0card : Nat.card ↥(⁅A, Q⁆ : Subgroup G) = p' := by
      rw [(mem_elemAbelianOfRank.mp hA0elem).2, pow_one]
    have hA1card : Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = p' := by
      rw [(mem_elemAbelianOfRank.mp hA1elem).2, pow_one]
    set A1g : Subgroup G := MulAut.conj g⁻¹ • (A ⊓ Subgroup.centralizer (Q : Set G)) with hA1gdef
    have hA1gN : A1g ≤ N :=
      hNgN ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (inf_le_right.trans hCQNg)
    have hA1gcard : Nat.card ↥A1g = p' := by
      rw [hA1gdef, mulAut_smul_eq_map' (MulAut.conj g⁻¹) _,
        Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj g⁻¹ : G →* G)
          (MulAut.conj g⁻¹).injective).symm.toEquiv, hA1card]
    obtain ⟨n, -, hnconj_eq⟩ :=
      exists_conj_smul_eq_of_le_of_card_prime hp'odd hrp'N hA0N hA1gN hA0card hA1gcard
    exact hnconj ⟨g * n, by
      calc MulAut.conj (g * n) • (⁅A, Q⁆ : Subgroup G)
          = MulAut.conj g • (MulAut.conj n • ⁅A, Q⁆) := by rw [map_mul, mul_smul]
        _ = MulAut.conj g • A1g := by rw [hnconj_eq]
        _ = A ⊓ Subgroup.centralizer (Q : Set G) := by
            rw [hA1gdef, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]⟩
  -- ### Part 3: the Frobenius conclusion
  exact ⟨hFM, ht2M,
    typeF_frobenius_of_tau2_prime_free hG hM hFM ht2M hqπM hqσM⟩

end OddOrder.BG.Ch4.S16
