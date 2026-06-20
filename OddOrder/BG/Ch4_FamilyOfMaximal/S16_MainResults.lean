/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_PairIntersection
import OddOrder.GroupTheory.MaximalSubgroupType

/-!
# BG §16: The Main Results

**Scope**: Bender--Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter IV §16 (pp. 123--134), mmd
`references/bg/local-analysis.mmd` L4256--4449.

This is the local-analysis endpoint. BG §16 packages the previous sections into
Theorems A--E, Proposition 16.1 (the Type I--V classification), and Theorems I--II
(the statements consumed by the character-theory half, especially Peterfalvi §10).
This scaffold gives those endpoints stable Lean names and connects the BG `kappa`/`M_F`
taxonomy to the shared Type I--V predicates in `GroupTheory.MaximalSubgroupType`.

Import boundary: this file intentionally does not import Peterfalvi modules. Peterfalvi
§10+ should consume these BG endpoints through the shared type predicates, while the BG
local-analysis spine remains independent of character-theory hypotheses.

## Lane C endpoint and proof-gate notes

- Theorems A--E are schematic packages of earlier BG results, not new Peterfalvi
  assumptions. The source proof table gives the exact gates: A uses Theorem 10.2,
  Lemma 15.1, Proposition 14.2, Theorem 15.2, Corollary 15.5, and Theorem 15.7
  (mmd L4392-L4398).
- Theorem B uses Lemma 12.1(d), Theorem 12.5(b), and Lemma 15.1(c)(d)(e)
  (mmd L4400-L4402).
- Theorem C uses Corollary 14.12, Corollary 15.6, Lemma 15.1(b), Theorem 10.1(b),
  Theorem 14.7, Proposition 14.2, Theorem A, and Theorem 15.7 (mmd L4404-L4410).
- Theorem D uses Corollary 15.3(b), Lemma 12.17, Theorem 14.4, Theorem A(8),
  and Corollary 15.9 (mmd L4412-L4414).
- Theorem E is the counting endpoint from Lemma 14.5(c), Theorem 13.9, and
  Corollary 14.9 (mmd L4416-L4418). The Lean surface below keeps the
  `\widetilde M`/representative-family partition visible here; it does not replace the
  §14 proof gates by a Peterfalvi type hypothesis.
- Proposition 16.1 is the BG-local bridge from the §14 families to the shared
  Type I--V predicates. This file may mention Peterfalvi as a consumer, but it must
  not import or assume Peterfalvi character-theory structure.
-/

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorem E notation: `hat M_sigma`, `A(M)`, and `A_0(M)` -/

/-- BG Theorem E notation: `hat M_sigma = {a in M | C_{M_sigma}(a) != 1}`. -/
def hatMsigma (M : Subgroup G) : Set G :=
  {a | a ∈ M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓
    Subgroup.centralizer ({a} : Set G) ≠ ⊥}

/-- `M_σ# ⊆ \widehat{M_σ}`: every nonidentity element `x` of `M_σ` lies in `hatMsigma M`,
since `x ∈ M_σ ≤ M` and `x` centralizes itself, so `1 ≠ x ∈ M_σ ⊓ C_G(x)`.  `§14`-independent
building block for Theorems B/E (`A(M) = hatMsigma ∩ …`). -/
theorem sigmaSharp_subset_hatMsigma (M : Subgroup G) :
    S14.sigmaSharp M ⊆ hatMsigma M := by
  intro x hx
  simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_diff, SetLike.mem_coe,
    Set.mem_singleton_iff] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_le M hxMσ, fun hbot => hx1 (Subgroup.mem_bot.mp ?_)⟩
  rw [← hbot]
  exact Subgroup.mem_inf.mpr ⟨hxMσ, Subgroup.mem_centralizer_iff.mpr
    (fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; rfl)⟩

/-- `1 ∈ \widehat{M_σ}` whenever `M_σ ≠ 1`: the identity is centralized by everything, so
`M_σ ⊓ C_G(1) = M_σ ≠ 1`.  Used by Theorem B(3) (`U_0 ∩ hatMsigma = {1}`).  `§14`-independent. -/
theorem one_mem_hatMsigma_of_Msigma_ne_bot {M : Subgroup G}
    (h : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥) : (1 : G) ∈ hatMsigma M := by
  refine ⟨Subgroup.one_mem M, ?_⟩
  have hC : Subgroup.centralizer ({1} : Set G) = ⊤ :=
    eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr
      fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; simp
  rw [hC, inf_top_eq]
  exact h

/-- BG Theorem E notation: `A(M) = hat M_sigma ∩ U M_sigma`. -/
def ASet (M U : Subgroup G) : Set G :=
  hatMsigma M ∩ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)

/-- BG Theorem E notation: `A_0(M) = hat M_sigma - C_M(K#)`, represented as the
part of `hat M_sigma` outside the `M`-conjugacy saturation of `K#`. -/
def A0Set (M K : Subgroup G) : Set G :=
  hatMsigma M \ conjClassSet (sharpSubgroup K)

/-- BG Theorem D(3) action language: `R` acts sharply transitively by conjugation on
a set of maximal subgroups. -/
def ConjSharplyTransitiveOn (R : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∃! r : G, r ∈ R ∧ B = MulAut.conj r • A

/-- The set of conjugates of `M` that contain `x`, from BG Theorem D(3). -/
def maximalConjugatesContaining (M : Subgroup G) (x : G) : Set (Subgroup G) :=
  {N | ∃ g : G, N = MulAut.conj g • M ∧ x ∈ N}

/-- BG Theorem D(3) local data for `R(x)`: `C_M(x)` is a Hall subgroup of
`C_G(x)`, and `R` is a normal complement acting sharply transitively on the
maximal conjugates that contain `x`. -/
def RData (M : Subgroup G) (x : G) (R : Subgroup G) : Prop :=
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) ((M ⊓ Cx).subgroupOf Cx) ∧
    (R.subgroupOf Cx).Normal ∧
    Subgroup.IsComplement' ((M ⊓ Cx).subgroupOf Cx) (R.subgroupOf Cx) ∧
    ConjSharplyTransitiveOn R (maximalConjugatesContaining M x)

/-- BG Theorem E notation: `xR(x)` as a left coset, represented as a set. -/
def rCoset (x : G) (R : G → Subgroup G) : Set G :=
  {y | ∃ r ∈ R x, y = x * r}

/-- BG Theorem E notation:
`\widetilde M = \bigcup_{x \in M_sigma#} x R(x)`. -/
def tildeM (M : Subgroup G) (R : G → Subgroup G) : Set G :=
  {y | ∃ x ∈ sigmaSharp M, y ∈ rCoset x R}

/-- BG's `pi*`: the primes whose Sylow subgroup is cyclic, or has the cyclic
centralizer splitting described in the type-I alternatives. -/
def piStar (G : Type*) [Group G] : Set ℕ :=
  {p | p ∈ (Nat.card G).primeFactors ∧
    ∃ P : Sylow p G,
      IsCyclic ↥(P : Subgroup G) ∨
        ∃ A B : Subgroup G,
          A ≤ (P : Subgroup G) ∧ B ≤ (P : Subgroup G) ∧ Nat.card ↥A = p ∧
          IsCyclic ↥B ∧ Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) = A ⊔ B}

/-! ## Theorems A--E -/

/-- **BG Theorem A** (mmd L4274): the basic structure of a maximal subgroup:
unique `M_sigma`, cyclic `K`, a `K`-invariant complement `U`, centralizer product
with `Kstar`, derived/Fitting layering, and the extreme case
`M_F != M_sigma`. -/
theorem theoremA_maximal_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      -- BG Thm A(3): `UM_σ ⊴ M`, i.e. `M` normalizes `UM_σ` (was a trivial self-normalizing
      -- `UM_σ ≤ N(UM_σ)`; faithfulness fix, Lane G).
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ S15.fittingInAmbient M ∧
      (S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
        U = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p) := by
  sorry

/-- **BG Theorem A — the ungated conjuncts** (mmd L4274), as a standalone `sorry`-free lemma.

Bundles the four conjuncts of `theoremA_maximal_structure` whose upstreams are all proved
transitively (mirroring `theoremB_U_sylow_abelian_rank_le_two` / `sigma_reps_pairwise_disjoint`):

* A(1) `M_σ` is a `σ(M)`-Hall subgroup (`Msigma_isHall`);
* A(5) `Kstar ≠ ⊥` — the genuinely new content, unblocked once Proposition 14.2
  (`S14.typeP_structure`) landed `sorry`-free: a `K`-case-split, with the `K ≠ ⊥` branch supplying
  `IsTypeP M` (`isTypeP_of_isHall_kappa_subgroupOf_ne_bot`) and reading off the `Kstar ≠ ⊥`
  conjunct of Proposition 14.2, and the `K = ⊥` (type-F) branch collapsing `Kstar = M_σ ≠ ⊥`;
* A(6) `M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`).

As with the Theorem B(1) precedent the explicit `hKM : K ≤ M` is added (it is part of the BG setup
`M = K U M_σ` but not forced by `hK`, a Hall condition on `K.subgroupOf M`); the monolith
`theoremA_maximal_structure` is left untouched (its other conjuncts are `§14`/`§15`-gated). -/
theorem theoremA_ungated_conjuncts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      Kstar ≠ ⊥ ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M := by
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_isHall hG hM, ?_,
    maxNilpotentNormalHall_le_Msigma hG hM, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM⟩
  by_cases hKbot : K = ⊥
  · -- type-F branch: `Kstar = M_σ ⊓ C(1) = M_σ ≠ ⊥`.
    subst hKbot
    have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
      exact Set.singleton_subset_iff.mpr (Subgroup.one_mem _)
    rw [hc, inf_top_eq] at hKstar
    rw [hKstar]
    exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  · -- type-P branch: `Kstar ≠ ⊥` is conjunct 2 of Proposition 14.2.
    have hKofne : K.subgroupOf M ≠ ⊥ := fun h =>
      hKbot (by rw [← Subgroup.map_subgroupOf_eq_of_le hKM, h, Subgroup.map_bot])
    have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
    exact (S14.typeP_structure hG hM hP hKM hK hKstar hU).2.1

/-- **BG Theorem B** (mmd L4295): restrictions on `U` and the tameness of
`A(M) - M_sigma`. -/
theorem theoremB_U_and_A_tame [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    (∀ p : ℕ, ∀ P : Subgroup G, P ≤ U → IsPGroup p ↥P →
      rank ↥P ≤ 2 ∧ IsMulCommutative ↥P) ∧
      IsMulCommutative ↥(S15.centralizerGeneratedBySigma M U) ∧
      (∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
        ∀ x ∈ U0, x ∈ hatMsigma M → x = 1) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
      IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M := by
  sorry

/-- **BG Theorem B(1)** (mmd L4373): every Sylow subgroup of `U` is abelian of rank at most two.

Standalone, `sorry`-free form of the first conjunct of `theoremB_U_and_A_tame`, mirroring
`sigma_reps_pairwise_disjoint` (the Theorem E precedent).  Two faithfulness adjustments over the
scaffold conjunct:

* the explicit hypothesis `hUM : U ≤ M` — the §12 supporting-subgroup reduction
  (`exists_subgroupESetup_with_le`) genuinely needs `U ≤ M`, and `hU` (a Hall condition on
  `U.subgroupOf M`) does not force it; in BG `U ⊆ M` is part of the setup (`M = K U M_σ`);
* the restriction to a *prime* `p` — "Sylow subgroup" means a `p`-group for prime `p`; for a
  composite `p` the bare `IsPGroup p` hypothesis is met by non-abelian `{q, r}`-groups (e.g. a
  Frobenius `7 ⋊ 3`, possible in odd order), so the unrestricted `∀ p : ℕ` form is false.

Proof (cite-only over §12): a `p`-subgroup `P ≤ U` is a `σ(M)'`-subgroup of `M`, hence lies in a
supporting subgroup `E` with `SubgroupESetup M E …` (`exists_subgroupESetup_with_le`); then
`rank P ≤ rank E ≤ 2` (`rank_le_two`) and `P`, a prime `p`-group, is nilpotent, so abelian by
`nilpotent_sigmaComplement_abelian` (a). -/
theorem theoremB_U_sylow_abelian_rank_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ U → IsPGroup p ↥P →
      rank ↥P ≤ 2 ∧ IsMulCommutative ↥P := by
  intro p hp P hPU hPp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : P ≤ M := hPU.trans hUM
  -- `P ≤ U` is a `σ(M)'`-subgroup of `M`.
  have hP_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) P := by
    intro q hq
    have hqU : q ∈ (Nat.card ↥U).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le hPU) Nat.card_pos.ne' hq
    intro hqσ
    exact hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      (Set.mem_union_right _ hqσ)
  -- §12 supporting subgroup `E ⊇ P`.
  obtain ⟨E, _E₁, _E₂, _E₃, hsetup, hPE, _hE_pi⟩ :=
    exists_subgroupESetup_with_le hG hM hPM hP_pi
  refine ⟨?_, ?_⟩
  · rw [rank_le_iff]
    intro q hq
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective hPE))
      ((rank_le_iff.mp (hsetup.rank_le_two hG)) q hq)
  · exact (nilpotent_sigmaComplement_abelian hG hsetup).1 P hPM hP_pi
      (IsPGroup.isNilpotent hPp)

/-- **BG Theorem C** (mmd L4303): when `K != 1`, `M` has a paired maximal
subgroup `Mstar`, the cyclic product `Z = K Kstar`, a TI set `Z_tilde`, and the
associated type-P duality. -/
theorem theoremC_paired_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    IsMulCommutative ↥U ∧ ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
      Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ S15.MF M ∧ ¬ IsCyclic ↥(S15.MF M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧
      (∃! Mstar : Subgroup G,
        Mstar ∈ maximalSubgroups G ∧ S14.IsTypeP Mstar ∧
          ¬ S14.IsConjugateSubgroup M Mstar ∧
          IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
          (S14.IsTypeP2 M ∨ S14.IsTypeP2 Mstar)) ∧
      IsTISubset (A0Set M K \ ASet M U) M ∧
      (U ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p ∧ S15.FittingIsTI M) ∧
      (U = ⊥ → ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q) := by
  sorry

/-- **§14/§15-independent assembly engine for BG Theorem D** (mmd L4317; the mmd L4440
schematic proof: `D(1) ← Cor 15.3(b)`, `D(2) ← Lem 12.17`, `D(3)(4) ← Thm 14.4(b) + Thm A(8)
+ Cor 15.9`).  Theorem D is a pure assembly of upstream §12/§14/§15 results, so this engine
takes each as a named hypothesis and discharges the conjunction; when those land (Lane H / Lane
F) the wrapper `theoremD_msigma_conjugacy_and_centralizers` cites them and applies this skeleton
(the gated-endpoint pattern, cf. `S15.mf_hall_centralizer_control_of_inputs`).

The one nontrivial step is `D(1)`: Corollary 15.3(b) at `H := M_σ` gives fusion control with the
realizing element in `N_G(M_σ)`; `normalizer_Msigma_eq_self` (`N_G(M_σ) = M`) upgrades this to
`M`-fusion, which is exactly Theorem D(1).  `D(2)`, `D(3)`, `D(4)` are recorded verbatim from
their sources (Lemma 12.17 / Theorem 14.4(b) / the Theorem 14.4(b)+A(8)+15.9 package). -/
theorem theoremD_msigma_conjugacy_and_centralizers_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hfusionMσ : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) →
        ∃ n ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G), y = n * x * n⁻¹)
    (hD2 : ∀ g : G, g ∉ M → IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj g • M)))
    (hD3 : ∀ x : G, x ∈ sigmaSharp M → ∃ R : Subgroup G, RData M x R)
    (hD4 : ∀ x : G, x ∈ sigmaSharp M → ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∃ R : Subgroup G,
          RData M x R ∧
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            R = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
            S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
            x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
            (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
            Subgroup.IsComplement' ((M ⊓ N).subgroupOf N)
              ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ∧
            (S14.IsTypeP2 N →
              S14.IsTypeP M ∧ ¬ S15.FittingIsTI M ∧
                ∃ E : Subgroup G,
                  E ≤ M ∧ IsCyclic ↥E ∧
                  Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
                    (E.subgroupOf M) ∧
                  OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
                    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))) :
    (∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      (∀ g : G, g ∉ M → IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj g • M))) ∧
      (∀ x : G, x ∈ sigmaSharp M → ∃ R : Subgroup G, RData M x R) ∧
      (∀ x : G, x ∈ sigmaSharp M → ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∃ R : Subgroup G,
          RData M x R ∧
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            R = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
            S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
            x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
            (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
            Subgroup.IsComplement' ((M ⊓ N).subgroupOf N)
              ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ∧
            (S14.IsTypeP2 N →
              S14.IsTypeP M ∧ ¬ S15.FittingIsTI M ∧
                ∃ E : Subgroup G,
                  E ≤ M ∧ IsCyclic ↥E ∧
                  Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
                    (E.subgroupOf M) ∧
                  OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
                    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))) := by
  refine ⟨?_, hD2, hD3, hD4⟩
  -- D(1): upgrade Corollary 15.3(b)'s `N_G(M_σ)`-fusion to `M`-fusion via `N_G(M_σ) = M`.
  intro x hx y hy hconj
  obtain ⟨n, hnN, hnconj⟩ := hfusionMσ x hx y hy hconj
  rw [normalizer_Msigma_eq_self hG hM] at hnN
  exact ⟨n, hnN, hnconj⟩

/-- **BG Theorem D** (mmd L4317, recovered tail L4368): conjugacy and centralizer
control for `M_sigma`, including the `R(x)` normal complement, its sharply transitive
action, and the unique maximal subgroup attached to escaping centralizers.

The final conjunct is the recovered BG D(4) tail: `M ∩ N` complements `N_sigma` in
`N`, and if `N` is type `P2` then `M` is type `P`, Frobenius with cyclic complement,
and `M_F` is not TI. -/
theorem theoremD_msigma_conjugacy_and_centralizers [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      (∀ g : G, g ∉ M → IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj g • M))) ∧
      (∀ x : G, x ∈ sigmaSharp M → ∃ R : Subgroup G, RData M x R) ∧
      (∀ x : G, x ∈ sigmaSharp M → ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∃ R : Subgroup G,
          RData M x R ∧
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            R = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
            S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
            x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
            (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
            Subgroup.IsComplement' ((M ⊓ N).subgroupOf N)
              ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ∧
            (S14.IsTypeP2 N →
              S14.IsTypeP M ∧ ¬ S15.FittingIsTI M ∧
                ∃ E : Subgroup G,
                  E ≤ M ∧ IsCyclic ↥E ∧
                  Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
                    (E.subgroupOf M) ∧
                  OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
                    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))) := by
  sorry

/-- **BG Theorem E, `σ(Mᵢ)`-disjointness conjunct** (mmd L4370): distinct
representatives of the conjugacy classes of maximal subgroups have disjoint
`σ`-sets.  This is the `σ(Mᵢ)` "disjoint union" piece of Theorem E, and it is
**already unconditional**: distinct class representatives are non-conjugate (forced
by the `∃!` uniqueness in `hreps` — both `Mᵢ` and `Mⱼ` would be *the* representative
of `Mᵢ`'s class), so BG Theorem 13.9
(`OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate`, landed sorry-free) applies
directly.  `hrepsMax` records that the representatives are themselves maximal
subgroups (the hypothesis Theorem 13.9 needs); it holds for any genuine set of
conjugacy-class representatives. -/
theorem sigma_reps_pairwise_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {reps : Set (Subgroup G)}
    (hrepsMax : ∀ Mi ∈ reps, Mi ∈ maximalSubgroups G)
    (hreps : ∀ H : Subgroup G, H ∈ maximalSubgroups G →
      ∃! Mi : Subgroup G, Mi ∈ reps ∧ S14.IsConjugateSubgroup H Mi)
    {Mi Mj : Subgroup G} (hMi : Mi ∈ reps) (hMj : Mj ∈ reps) (hne : Mi ≠ Mj) :
    OddOrder.BG.Ch3.S10.sigma Mi ∩ OddOrder.BG.Ch3.S10.sigma Mj = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty]
  refine OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG
    (hrepsMax Mi hMi) (hrepsMax Mj hMj) ?_
  intro hconj
  obtain ⟨Z₀, _, huniq⟩ := hreps Mi (hrepsMax Mi hMi)
  exact hne ((huniq Mi ⟨hMi, S14.IsConjugateSubgroup.refl Mi⟩).trans
    (huniq Mj ⟨hMj, hconj⟩).symm)

/-- **BG Theorem E** (mmd L4370): with `R(x)` as in Theorem D and
`\widetilde M = ⋃_{x ∈ M_sigma#} xR(x)`, the conjugacy saturation of
`\widetilde M` has the stated size, the representative maximal subgroups give a
disjoint partition of `π(G)` by the `σ(M_i)`, and the nonidentity elements of `G`
are covered by the corresponding `\widetilde M_i` pieces, with the additional
`\widehat Z` piece exactly in the type-P case.

Proof gates: Lemma 14.5(c) for the cardinal formula, Theorem 13.9 for the
`σ(M_i)` disjoint union, and Corollary 14.9 for the final covering. -/
theorem theoremE_sigma_partition_and_counting [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (R : Subgroup G → G → Subgroup G) (reps : Set (Subgroup G))
    (hreps : ∀ H : Subgroup G, H ∈ maximalSubgroups G →
      ∃! Mi : Subgroup G, Mi ∈ reps ∧ S14.IsConjugateSubgroup H Mi)
    -- `R` must be the Theorem D normal-complement data `R(x)` (the docstring's
    -- "`R(x)` as in Theorem D"); without this the conclusion would be claimed for an
    -- arbitrary `R`, which is false. Pins `R M ·` and each `R Mi ·` to `RData`.
    (hR : ∀ x ∈ sigmaSharp M, RData M x (R M x))
    (hRreps : ∀ Mi ∈ reps, ∀ x ∈ sigmaSharp Mi, RData Mi x (R Mi x)) :
    Nat.card (conjClassSet (tildeM M (R M))) =
        (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) - 1) * M.index ∧
      (∀ p : ℕ, p ∈ (Nat.card G).primeFactors ↔
        ∃ Mi : Subgroup G, Mi ∈ reps ∧ p ∈ OddOrder.BG.Ch3.S10.sigma Mi) ∧
      (∀ Mi ∈ reps, ∀ Mj ∈ reps, Mi ≠ Mj →
        OddOrder.BG.Ch3.S10.sigma Mi ∩ OddOrder.BG.Ch3.S10.sigma Mj = ∅) ∧
      (∀ Mi ∈ reps, ∀ Mj ∈ reps, Mi ≠ Mj →
        conjClassSet (tildeM Mi (R Mi)) ∩ conjClassSet (tildeM Mj (R Mj)) = ∅) ∧
      (let tildeG : Set G :=
        {g | ∃ Mi : Subgroup G, Mi ∈ reps ∧ g ∈ conjClassSet (tildeM Mi (R Mi))}
       (S14.maximalTypePFamily G = ∅ → sharpSubgroup (⊤ : Subgroup G) = tildeG) ∧
        (S14.maximalTypePFamily G ≠ ∅ → S14.IsTypeP M →
          sharpSubgroup (⊤ : Subgroup G) = tildeG ∪ conjClassSet (S14.zTilde K Kstar))) := by
  sorry

/-- **BG §16 `A(M)`/`A_0(M)` support slice**: the auxiliary sets from this section
have the TI and support properties used by the downstream character-theory interface.
This is a separate Peterfalvi-facing slice, not a replacement for BG Theorem E; the
full local counting/partition statement is `theoremE_sigma_partition_and_counting`. -/
theorem aSets_support_slice [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
      IsTISubset (A0Set M K \ ASet M U) M ∧
      Supports (ASet M U) (S14.zTilde K Kstar ∪ A0Set M K) := by
  sorry

/-! ## Proposition 16.1 forward bridges: constructing the shared type data -/

/-- The pointwise `MulAut`-action distributes over `sSup` of subgroups (it is `Subgroup.map`, a
left adjoint, so it preserves arbitrary joins). -/
private theorem mulAut_smul_sSup (a : MulAut G) (T : Set (Subgroup G)) :
    a • sSup T = ⨆ S ∈ T, a • S := by
  rw [Subgroup.pointwise_smul_def]
  exact (Subgroup.gc_map_comap _).l_sSup

/-- Conjugation by `u` carries `C_G(x)` to `C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizer_singleton (u x : G) :
    MulAut.conj u • Subgroup.centralizer ({x} : Set G)
      = Subgroup.centralizer ({u * x * u⁻¹} : Set G) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hsmul : ((MulAut.conj u)⁻¹ • g : G) = u⁻¹ * g * u := by
    rw [← map_inv]; simp [MulAut.smul_def, MulAut.conj_apply]
  rw [hsmul]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h2 := congrArg (fun t => u * t * u⁻¹) h
    simp only at h2
    calc u * x * u⁻¹ * g = u * (x * (u⁻¹ * g * u)) * u⁻¹ := by group
      _ = u * (u⁻¹ * g * u * x) * u⁻¹ := h2
      _ = g * (u * x * u⁻¹) := by group
  · intro h
    have h2 := congrArg (fun t => u⁻¹ * t * u) h
    simp only at h2
    calc x * (u⁻¹ * g * u) = u⁻¹ * (u * x * u⁻¹ * g) * u := by group
      _ = u⁻¹ * (g * (u * x * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * g * u * x := by group

/-- The generating family `{U ⊓ C_G(x) : x ∈ M_σ#}` of `centralizerGeneratedBySigma M U`. -/
private abbrev sigCentFam (M U : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ x ∈ S14.sigmaSharp M, C = U ⊓ Subgroup.centralizer ({x} : Set G)}

/-- `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩`: for `u ∈ U ≤ M` it permutes the generating set
`{U ⊓ C_G(x) : x ∈ M_σ#}`, since `M_σ ◁ M` makes `x ↦ u x u⁻¹` a bijection of `M_σ#` and
`u (U ⊓ C_G(x)) u⁻¹ = U ⊓ C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizerGeneratedBySigma {M U : Subgroup G} {u : G}
    (huM : u ∈ M) (huU : u ∈ U) :
    MulAut.conj u • S15.centralizerGeneratedBySigma M U
      = S15.centralizerGeneratedBySigma M U := by
  -- conjugation by an element of `M` preserves `M_σ#` (as `M_σ ◁ M`).
  have hsig : ∀ v : G, v ∈ M → ∀ x : G, x ∈ S14.sigmaSharp M → v * x * v⁻¹ ∈ S14.sigmaSharp M := by
    intro v hv x hx
    rw [S14.sigmaSharp, sharpSubgroup, Set.mem_diff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxMσ, hx1⟩ := hx
    refine ⟨?_, fun h => hx1 (mul_left_cancel ((mul_inv_eq_one.mp h).trans (mul_one v).symm))⟩
    have hvN : v ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hv
    exact (Subgroup.mem_normalizer_iff.mp hvN x).mp hxMσ
  -- conjugation by `v ∈ M ∩ U` maps each generator to a generator.
  have hgen : ∀ v : G, v ∈ M → v ∈ U →
      ∀ C ∈ sigCentFam M U, MulAut.conj v • C ∈ sigCentFam M U := by
    rintro v hvM hvU C ⟨x, hx, rfl⟩
    exact ⟨v * x * v⁻¹, hsig v hvM x hx, by
      rw [Subgroup.smul_inf, Subgroup.conj_smul_eq_self_of_mem hvU,
        conj_smul_centralizer_singleton]⟩
  rw [show S15.centralizerGeneratedBySigma M U = sSup (sigCentFam M U) from rfl, mulAut_smul_sSup]
  refine le_antisymm (iSup_le fun C => iSup_le fun hC => le_sSup (hgen u huM huU C hC)) ?_
  refine sSup_le fun C hC => ?_
  have hC' : (MulAut.conj u)⁻¹ • C ∈ sigCentFam M U := by
    rw [← map_inv MulAut.conj]
    exact hgen u⁻¹ (inv_mem huM) (inv_mem huU) C hC
  calc C = MulAut.conj u • ((MulAut.conj u)⁻¹ • C) := (smul_inv_smul _ _).symm
    _ ≤ ⨆ C' ∈ sigCentFam M U, MulAut.conj u • C' :=
      le_iSup₂ (f := fun C' (_ : C' ∈ sigCentFam M U) => MulAut.conj u • C')
        ((MulAut.conj u)⁻¹ • C) hC'

/-- **Prop 16.1(a) forward bridge, core** (mmd L4480): a type-`F` maximal `M` (`κ(M) = ∅`, so the
Hall `κ`-subgroup `K = ⊥`) carries the shared Peterfalvi type-`F` structure `TypeFData M`.

This is the `M ∈ ℳ_𝓕 ⟹ Type F` core feeding `proposition_type_classification`'s `hFI` (clause (a),
`mpr`).  The deep fields are read off existing §15 results: `U1_commutative` and `frobenius_HU0`
from `typeP_auxiliary_structure` (mmd 15.1(d)(e)); `H = M_F = M_σ` from Theorem A(8) (`U ≠ ⊥` rules
out the `M_F ≠ M_σ` branch); `M = U M_σ` from Theorem A(3) with `K = ⊥`; `centralizer_le_U1` is
`le_sSup` over `M_F# ⊆ M_σ#`; and `U1_normal` (`⟨C_U(x) | x ∈ M_σ#⟩ ◁ U`) is `U`-conjugation
invariance of the generating set `{U ⊓ C_G(x) : x ∈ M_σ#}` (`conj_smul_centralizerGeneratedBySigma`,
as `M_σ ◁ M`).  Sorry-free in its own body; transitively conditional on the (sorried) Theorem A and
the gated half of `typeP_auxiliary_structure`. -/
theorem typeFData_of_kappa_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  -- Theorem A: the decomposition `M = K U M_σ` (A3) and the `M_F ≠ M_σ` branch (A8).
  obtain ⟨_, _, hA3, _, _, _, _, _, _, _, hA8⟩ := theoremA_maximal_structure hG hM hK rfl hU
  -- `M_F = M_σ`: `U ≠ ⊥` excludes A(8)'s `M_F ≠ M_σ ⟹ U = ⊥` conclusion.
  have hMFMσ : S15.MF M = Mσ := by
    by_contra hne
    exact hUne (hA8 hne).1
  -- `M = U M_σ` (A3 with `K = ⊥`).
  have hMU : M = U ⊔ Mσ := by rw [hA3, hKbot, bot_sup_eq]
  -- `typeP_auxiliary_structure`: `U1` abelian (15.1(d)) + the Frobenius `U₀ M_σ` (15.1(e)).
  obtain ⟨_, _, _, _, _, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := S15.MF M
    U := U
    U1 := S15.centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := rfl
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := S15.maxNilpotentNormalHall_le M
    U_le := hUM
    U1_le := by
      apply sSup_le
      rintro C ⟨x, _, rfl⟩
      exact inf_le_left
    U0_le := hU0U
    complement := ?_
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_diff, SetLike.mem_coe,
        Set.mem_singleton_iff]
      exact ⟨S15.maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := ?_ }⟩
  · -- `complement`: `M_F = M_σ` complements `U` in `M`.  `M_σ ◁ M`, `M_σ ⊓ U = ⊥` and `M_σ ⊔ U = M`
    -- come from the `K = ⊥` `SubgroupESetup` (`subgroupESetup_of_isHall_kappa_eq_bot`).
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    rw [hMFMσ]
    haveI hMσnorm : ((Mσ).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr
        (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxMσ hxU
      rw [Subgroup.mem_subgroupOf] at hxMσ hxU
      have hx : (x : G) ∈ Mσ ⊓ U := ⟨hxMσ, hxU⟩
      rw [hsetup.E_compl_inf, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hUM,
        hsetup.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]
  · -- `U1_normal`: `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩` (it permutes the generators).
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]
  · -- `frobenius_HU0`: rewrite `M_F = M_σ`, `M_F ⊔ U₀ = U₀ ⊔ M_σ` into the Frobenius datum.
    rw [hMFMσ, sup_comm]
    exact hfrob

/-- **Type-`P` `V`-normalizer characterization** (the `normalizer_V` field of `TypePData`,
Peterfalvi (8.4); BG records it as the self-normalizing exceptional set `M = N_G(V)`): if
`W = W₁ ⊔ W₂` is cyclic and the exceptional set `V = W ∖ (W₁ ∪ W₂)` is a `TI`-subset relative to
`W`, then every nonempty `X ⊆ V` has normalizer exactly `W`.

This is the genuine reduction underlying the deep-looking `normalizer_V` field: `N_G(X) ≤ W` is the
`TI` property (a conjugate of an element of `X ⊆ V` lands back in `V`, forcing the conjugator into
`W`); `W ≤ N_G(X)` is abelianness of the cyclic `W` (every `w ∈ W` centralizes `X ⊆ W`, so fixes it
setwise).  Both inputs (`W = K ⊔ K*` cyclic and the `zTilde K K*` `TI` property) are supplied by
Theorem 14.7 (`typeP_duality`), so this lemma discharges `normalizer_V` once §14 lands. -/
theorem normalizer_eq_sup_of_isTISubset_of_isCyclic {W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2))
    {X : Set G} (hXne : X.Nonempty)
    (hXV : X ⊆ (↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) :
    Subgroup.normalizer X = W1 ⊔ W2 := by
  classical
  haveI : IsCyclic ↥(W1 ⊔ W2) := hWcyc
  letI : CommGroup ↥(W1 ⊔ W2) := IsCyclic.commGroup
  -- elements of the cyclic `W = W₁ ⊔ W₂` commute in `G`.
  have hcomm : ∀ a b : G, a ∈ W1 ⊔ W2 → b ∈ W1 ⊔ W2 → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(W1 ⊔ W2)) ⟨b, hb⟩)
  apply le_antisymm
  · -- `N_G(X) ≤ W`: a conjugate of `a ∈ X ⊆ V` lands in `V`, so the `TI` property forces `g ∈ W`.
    intro g hg
    obtain ⟨a, haX⟩ := hXne
    have h1 : g⁻¹ * a * g ∈ X := (Subgroup.mem_set_normalizer_iff''.mp hg a).mp haX
    refine hTI g ⟨g⁻¹ * a * g, hXV h1, ?_⟩
    have he : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [he]; exact hXV haX
  · -- `W ≤ N_G(X)`: `w ∈ W` centralizes `X ⊆ W` (abelian), so it fixes `X` setwise.
    intro w hw
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hhX
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw (hXV hhX).1]; group
      rw [hfix]; exact hhX
    · intro hconj
      have hhW : h ∈ W1 ⊔ W2 := by
        have hrw : h = w⁻¹ * (w * h * w⁻¹) * w := by group
        rw [hrw]
        exact mul_mem (mul_mem (inv_mem hw) (hXV hconj).1) hw
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw hhW]; group
      rwa [hfix] at hconj

/-- **Prop 16.1(b)--(d) forward bridge, shared core**: assemble the Peterfalvi type-`P` datum
`TypePData M` (mmd L4116/L4190, Peterfalvi (8.4)) from the BG-local structural facts.  This is the
single construction feeding *all three* of the `hP2II`/`hP1neIIIIV`/`hP1eqV` forward bridges of
`proposition_type_classification` (types II, III, IV, V all bundle a `TypePData`).

Following the gated-endpoint skeleton pattern (cf. `typeP_kstar_in_mf_of_inputs`), the deep
structural fields are taken as named hypotheses; their BG sources are:

* the derived-series complement `M = M' W₁`, `W = W₁ ⊔ W₂` cyclic, and the `zTilde` `TI` property
  (`hMcompl`/`hWcyc`/`hTI`) come from Theorem 14.7 (`typeP_duality`) with `W₁ = K`, `W₂ = K*`,
  `W = K ⊔ K*`;
* the Fitting decomposition `F(M) = H ⊔ (U ⊓ C_M(H))`, `M'' ≤ F(M)`, `F(M) < M'`, and `M_F`
  noncyclic (`hFiteq`/`hSDfit`/`hFitlt`/`hHncyc`) come from Theorem 15.2
  (`mf_ne_msigma_typeP1_structure`) and Corollary 15.6;
* the `M'`-internal complement `M' = H U` with `U ⊴ M'` nilpotent (`hDcompl`/`hUnorm`/`hUnilp`)
  comes from Lemma 15.1 / Theorem A.

The genuinely *derived* (not renamed) fields are `W_eq` (definitional), `W1_cyclic`/`W2_cyclic`
(subgroups of the cyclic `W`), and `normalizer_V` (the `TI` + cyclic reduction
`normalizer_eq_sup_of_isTISubset_of_isCyclic`).  Sorry-free in its own body. -/
def typePData_of_inputs {M H U W1 W2 : Subgroup G}
    (hHeq : H = maxNilpotentNormalHall M)
    (hHle : H ≤ derivedInG M)
    (hUle : U ≤ derivedInG M)
    (hW1le : W1 ≤ M)
    (hW2le : W2 ≤ H ⊓ secondDerivedInAmbient M)
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hW1ne : W1 ≠ ⊥) (hW2ne : W2 ≠ ⊥)
    (hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W1.subgroupOf M))
    (hUnorm : (U.subgroupOf (derivedInG M)).Normal)
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl :
      Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hHncyc : ¬ IsCyclic ↥H)
    (hSDfit : secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hFiteq : maxNilpotentNormalHall M = H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hFitlt : maxNilpotentNormalHall M < derivedInG M)
    (hCentW1 : ∀ x ∈ W1, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = W2)
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2)) :
    TypePData M := by
  haveI := hWcyc
  exact
    { H := H
      U := U
      W1 := W1
      W2 := W2
      W := W1 ⊔ W2
      H_eq := hHeq
      H_le := hHle
      U_le := hUle
      W1_le := hW1le
      W2_le := hW2le
      W_eq := rfl
      W_cyclic := hWcyc
      W1_nontrivial := hW1ne
      W2_nontrivial := hW2ne
      W1_cyclic := Subgroup.isCyclic_of_le (le_sup_left : W1 ≤ W1 ⊔ W2)
      W2_cyclic := Subgroup.isCyclic_of_le (le_sup_right : W2 ≤ W1 ⊔ W2)
      M_complement := hMcompl
      U_normal := hUnorm
      U_nilpotent := hUnilp
      derived_complement := hDcompl
      H_noncyclic := hHncyc
      secondDerived_le_fitting := hSDfit
      fitting_eq := hFiteq
      fitting_lt_derived := hFitlt
      centralizer_W1 := hCentW1
      normalizer_V := fun X hXne hXV =>
        normalizer_eq_sup_of_isTISubset_of_isCyclic hWcyc hTI hXne hXV }

/-- **Prop 16.1 forward bridge, type III/IV last mile** (Peterfalvi (8.7)): a type-`P` datum whose
`U`-factor has its normalizer inside `M` is of type III or IV, according as `U` is abelian or not.
This is the clean part of the `hP1neIIIIV` bridge — no deep `alternative`/`derived_typeF` content,
only the decidable `IsMulCommutative ↥U` split distinguishing III (`U` abelian) from IV. -/
theorem isTypeIII_or_IV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hnorm : Subgroup.normalizer (data.U : Set G) ≤ M) :
    IsTypeIII M ∨ IsTypeIV M := by
  classical
  by_cases hU : IsMulCommutative ↥data.U
  · exact Or.inl ⟨{ typeP := data, common := hcommon, U_commutative := hU, normalizer_le := hnorm }⟩
  · exact Or.inr
      ⟨{ typeP := data, common := hcommon, U_not_commutative := hU, normalizer_le := hnorm }⟩

/-- **Prop 16.1 forward bridge, type II last mile** (Peterfalvi (8.6)): a type-`P` datum with `U`
abelian, `N_G(U) ⊄ M`, and the derived subgroup `M'` of type `F` (with `F(M') = H`) is of type II.
The `derived_typeF` field is the genuinely deep named residual (the type-`F` structure of `M'`). -/
theorem isTypeII_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hUcomm : IsMulCommutative ↥data.U)
    (hnorm : ¬ Subgroup.normalizer (data.U : Set G) ≤ M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = data.H) :
    IsTypeII M :=
  ⟨{ typeP := data, common := hcommon, U_commutative := hUcomm,
     normalizer_not_le := hnorm, derived_typeF := hderF, derived_fitting_eq := hderfit }⟩

/-- **Prop 16.1 forward bridge, type V last mile** (Peterfalvi (8.8)): a type-`P` datum with
`U = ⊥` and the Peterfalvi (8.8) trichotomy on `H = M_F` is of type V.  The `alternative`
disjunction is the deep named residual (BG §15.7(c) / Peterfalvi (8.8)). -/
theorem isTypeV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hUbot : data.U = ⊥)
    (halt :
      IsTISubset (sharpSubgroup data.H) (Subgroup.normalizer (data.H : Set G)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥data.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ data.H)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥(opiCoreInG {p} data.H) = p ^ 3 ∧ Nat.card ↥data.W1 ∣ p + 1 ∧
        IsCyclic ↥(opiCoreInG {p}ᶜ data.H))) :
    IsTypeV M :=
  ⟨{ typeP := data, U_eq_bot := hUbot, alternative := halt }⟩

/-- **Prop 16.1(d)/(f) reverse, `M_F = M_σ` from `U = ⊥`** (the `M_F = M_σ` conjunct of `hVP1`,
mmd L4478): a type-`P` datum with trivial complement `U = ⊥` has `M_F = M_σ`.  Sandwiching:
`M' = M_F ⊔ U = M_F` (`TypePData.derivedInG_eq_fitting_sup_U` with `U = ⊥`), while always
`M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`); so `M_F = M_σ = M'`.
Axiom-clean (does *not* cite Theorem A(8), unlike the `M_F = M_σ` step of `typeFData_of_kappa_eq_bot`).
This is the structural half of clause (d): the `IsTypeP1` half is the (deeper) `κ` refinement. -/
theorem mf_eq_msigma_of_typePData_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M) (hU : data.U = ⊥) :
    S15.MF M = OddOrder.BG.Ch3.S10.Msigma M := by
  -- `M' = M_F` since `M' = M_F ⊔ U` and `U = ⊥`.
  have hderiv : derivedInG M = S15.MF M := by
    rw [data.derivedInG_eq_fitting_sup_U, hU, sup_bot_eq]
  -- `M_F ≤ M_σ` always; `M_σ ≤ M' = M_F`; hence equal.
  refine le_antisymm (S15.maxNilpotentNormalHall_le_Msigma hG hM) ?_
  exact hderiv ▸ OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM

/-- **Prop 16.1 reverse, centralizer half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `1 ⊂ C_H(W₁) ⊆
C_{M_σ}(W₁)`): for a type-`P` datum and a nonidentity `x ∈ W₁`, the `M_σ`-centralizer of `x` is
nontrivial.  Witness: `W₂ = M' ⊓ C(x)` (`centralizer_W1`) lies in both `M_σ` (`W₂ ≤ H = M_F ≤ M_σ`)
and `C(x)`, and `W₂ ≠ ⊥` (`W2_nontrivial`); so `W₂ ≤ M_σ ⊓ C(x)` is a nontrivial subgroup.

This is the `κ(M)`-membership ingredient that is **derivable from the bare `TypePData`** (it needs
no `W₁ = κ`-Hall identification).  The remaining `κ`-membership ingredients — `p ∉ σ(M)` and the
rank-one condition `r_p(M) = 1` putting `p ∈ τ₁(M) ∪ τ₃(M)` — are the carrier-gated half (the latter
genuinely needs `W₁` to be the Hall `κ(M)`-subgroup; cf. issue 8015 and
`typep-w1-kappa-carrier-not-derivable`). -/
theorem typePData_msigma_inf_centralizer_W1_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {x : G} (hx : x ∈ data.W1) (hxne : x ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  -- `W₂ ≤ M_σ ⊓ C(x)`.
  have hW2le : data.W2 ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf ?_ ?_
    · -- `W₂ ≤ H = M_F ≤ M_σ`.
      calc data.W2 ≤ data.H := data.W2_le.trans inf_le_left
        _ = maxNilpotentNormalHall M := data.H_eq
        _ ≤ _ := S15.maxNilpotentNormalHall_le_Msigma hG hM
    · -- `W₂ = M' ⊓ C(x) ≤ C(x)`.
      rw [← data.centralizer_W1 x hx hxne]; exact inf_le_right
  -- A subgroup containing the nontrivial `W₂` is nontrivial.
  exact fun hbot => data.W2_nontrivial (le_bot_iff.mp (hW2le.trans hbot.le))

/-- **Prop 16.1 reverse, `σ`-complement half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `W₁ ∩ M_σ = 1`): for a
type-`P` datum, every prime dividing `|W₁|` lies outside `σ(M)`.  If `p ∈ σ(M)`, an order-`p`
subgroup `L ≤ W₁` is a `σ(M)`-group, so it lands in the `σ`-Hall subgroup `M_σ`
(`sigma_subgroup_le_Msigma_of_isHall`, `Msigma_isHall`); but `W₁ ∩ M_σ ≤ W₁ ∩ M' = 1`
(`M_complement`), forcing `L = ⊥` and `|L| = p = 1`, a contradiction.

This is the second `κ`-membership ingredient **derivable from the bare `TypePData`** (with
`typePData_msigma_inf_centralizer_W1_ne_bot`).  Together they give `p ∉ σ(M)` and `M_σ ⊓ C(P) ≠ ⊥`;
the only carrier-gated ingredient left for `π(W₁) ⊆ κ(M)` is the rank-one condition `r_p(M) = 1`. -/
theorem typePData_W1_prime_not_mem_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {p : ℕ} (hp : p ∈ (Nat.card ↥data.W1).primeFactors) :
    p ∉ OddOrder.BG.Ch3.S10.sigma M := by
  intro hpσ
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- An order-`p` element `g ∈ W₁` and the cyclic subgroup `L = ⟨g⟩` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p (Nat.dvd_of_mem_primeFactors hp)
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  set L : Subgroup G := Subgroup.zpowers (g : G) with hLdef
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, hgord]
  have hLW1 : L ≤ data.W1 := Subgroup.zpowers_le.mpr g.2
  have hLM : L ≤ M := hLW1.trans data.W1_le
  -- `L` is a `σ(M)`-group (its only prime divisor is `p ∈ σ(M)`).
  have hLpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) L := by
    intro q hq
    rw [hLcard, (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpσ
  -- So `L ≤ M_σ ≤ M'`, while `L ≤ W₁` and `W₁ ∩ M' = ⊥` (complement); hence `L = ⊥`.
  have hLMσ : L ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hLM hLpi
  have hLsub_bot : L.subgroupOf M = ⊥ := by
    rw [eq_bot_iff, ← disjoint_iff.mp data.M_complement.disjoint]
    exact le_inf
      (Subgroup.comap_mono (hLMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)))
      (Subgroup.comap_mono hLW1)
  have hLbot : L = ⊥ :=
    (inf_eq_left.mpr hLM).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hLsub_bot))
  rw [hLbot, Subgroup.card_bot] at hLcard
  exact (Fact.out : p.Prime).ne_one hLcard.symm

/-- **Prop 16.1 reverse, `M_P` from `TypePData` modulo the rank-one input** (mmd L4478,
`π(W₁) ⊆ κ(M) ⟹ κ(M) ≠ ∅`): a type-`P` datum whose `W₁`-primes all have `M`-rank one has
`κ(M) ≠ ∅`, hence `M` is `S14.IsTypeP`.  This is the gated-endpoint assembly of the three `κ`-bridge
ingredients for a prime `p ∣ |W₁|`: `p ∉ σ(M)` (`typePData_W1_prime_not_mem_sigma`) and `r_p(M) = 1`
(the hypothesis `hrank`) put `p ∈ τ₁(M) ∪ τ₃(M)`, while `⟨g⟩` (`g ∈ W₁` of order `p`) is a rank-one
elementary abelian subgroup with `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`
(`typePData_msigma_inf_centralizer_W1_ne_bot`).  So `p ∈ κ(M)`.

The only residual hypothesis `hrank` is the carrier-gated half (the `W₁ = κ`-Hall fact forces
`r_p(M) = 1`; cf. issue 8015).  Supplies the `→ M_P` direction of the reverse classifications
`hIIP2`/`hIIIIVP1`/`hVP1` of `proposition_type_classification_of_inputs`. -/
theorem typePData_kappa_nonempty_of_rank1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M)
    (hrank : ∀ p ∈ (Nat.card ↥data.W1).primeFactors, pRank ↥M p = 1) :
    (S14.kappa M).Nonempty := by
  classical
  -- A prime `p ∣ |W₁|` (`W₁ ≠ ⊥`).
  have hW1card : Nat.card ↥data.W1 ≠ 1 := fun h => data.W1_nontrivial (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hW1card
  have hp : p ∈ (Nat.card ↥data.W1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  -- An order-`p` element `g ∈ W₁` and the rank-one subgroup `P = ⟨g⟩`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p hpdvd
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := fun hc => by
    rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers, hgord]
  refine ⟨p, hpp, ?_, Subgroup.zpowers (g : G),
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩,
    (Subgroup.zpowers_le.mpr g.2).trans data.W1_le, ?_⟩
  · -- `p ∈ τ₁(M) ∪ τ₃(M)` from `p ∉ σ(M)` and `r_p(M) = 1`.
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := typePData_W1_prime_not_mem_sigma hG hM data hp
    have hr : pRank ↥M p = 1 := hrank p hp
    by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
    · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr⟩)
    · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr⟩)
  · -- `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`.
    have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ :=
      typePData_msigma_inf_centralizer_W1_ne_bot hG hM data g.2 hgne
    have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
        Subgroup.centralizer ((Subgroup.zpowers (g : G) : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
    exact fun hbot => hCne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))

/-- **Theorem A(8) `U = ⊥` core, from type `P₁`** (mmd L4274): for a type-`P₁` maximal subgroup,
the Hall `(κ(M) ∪ σ(M))ᶜ`-complement `U` is trivial.  Type `P₁` means `κ(M) = π(M) ∖ σ(M)`
(`IsTypeP1.2`), so `π(M) ⊆ κ(M) ∪ σ(M)` and the prime set `(κ(M) ∪ σ(M))ᶜ` meets `π(M)` only in
`∅`; a Hall `(κ ∪ σ)ᶜ`-subgroup of `M` therefore has order coprime to `|M|`, i.e. trivial.

This is the `U = ⊥` conjunct of Theorem A(8) (`theoremA_maximal_structure`), now **derivable from
`Thm 15.2 (mf_ne_msigma_typeP1_structure)`** via `isTypeP1_of_mf_ne_msigma`: `M_F ≠ M_σ ⟹ IsTypeP1 ⟹
U = ⊥`.  Together with `|K| = p` (also a Thm 15.2 output) this leaves only `FittingIsTI M` for the
full A(8).  Stated for the relative `U.subgroupOf M` (which is what the Hall hypothesis constrains);
when `U ≤ M` it gives `U = ⊥`. -/
theorem isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot [Finite G] {M U : Subgroup G}
    (hP1 : S14.IsTypeP1 M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    U.subgroupOf M = ⊥ := by
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  -- `p ∈ (κ ∪ σ)ᶜ` (Hall) and `p ∈ π(M)` (`|U.subgroupOf M| ∣ |M|`).
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩)
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans (Subgroup.card_subgroup_dvd_card (U.subgroupOf M)), Nat.card_pos.ne'⟩
  -- but `π(M) ⊆ κ(M) ∪ σ(M)` for type `P₁`.
  refine hpcompl ?_
  by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
  · exact Set.mem_union_right _ hpσ
  · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hpM, hpσ⟩)

/-- **Converse: `κ(M) = π(M) ∖ σ(M)` from a trivial Hall `(κ ∪ σ)ᶜ`-complement** (the second half of
the type-`P₁` ⟺ `U = ⊥` characterization).  If the Hall `(κ(M) ∪ σ(M))ᶜ`-subgroup of `M` is trivial,
then `(κ ∪ σ)ᶜ` contains no prime dividing `|M|` (the Hall index condition `hU.2` with index `|M|`),
so `π(M) ⊆ κ(M) ∪ σ(M)`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` (every `κ`-prime is a non-`σ` divisor of
`|M|`) this gives `κ(M) = π(M) ∖ σ(M) = sigmaComplementPrimes M`.

Together with `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` this is the prime-set core of BG's
"`M ∈ M_{P₁} ⟺ U = ⊥`": modulo `IsTypeP` (`κ ≠ ∅`), `U = ⊥ ⟺ M` is type `P₁`. -/
theorem kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot [Finite G] {M U : Subgroup G}
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUbot : U.subgroupOf M = ⊥) :
    S14.kappa M = S14.sigmaComplementPrimes M := by
  refine Set.Subset.antisymm (fun p hpκ => ?_) (fun p hpσ' => ?_)
  · -- `κ ⊆ π ∖ σ`: a `κ`-prime is non-`σ` (`τ₁ ∪ τ₃`) and divides `|M|` (rank-one `P ≤ M`).
    obtain ⟨hpp, hτ, P, hPelem, hPM, _⟩ := hpκ
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      rcases hτ with h | h
      · exact ((mem_tau1_iff M p).mp h).1
      · exact ((mem_tau3_iff M p).mp h).1
    have hpπ : p ∈ S14.piSet M := by
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
      have hPcard : Nat.card ↥P = p := by rw [hPelem.2, pow_one]
      exact hPcard ▸ Subgroup.card_dvd_of_le hPM
    exact ⟨hpπ, hpσ⟩
  · -- `π ∖ σ ⊆ κ`: `U = ⊥` forces every `|M|`-prime into `κ ∪ σ`; non-`σ` ones land in `κ`.
    obtain ⟨hpπ, hpσ⟩ := hpσ'
    by_contra hpκ
    refine hU.2 p (by rw [hUbot, Subgroup.index_bot]; exact hpπ) ?_
    rintro (h | h)
    · exact hpκ h
    · exact hpσ h

/-- **Theorem A(8), the `FittingIsTI`-free part** (mmd L4274): for `M_F ≠ M_σ`, the Hall
`(κ ∪ σ)ᶜ`-complement `U` is trivial and `|K| = p` is prime.  Both follow from
`mf_ne_msigma_typeP1_structure` (Theorem 15.2): `M_F ≠ M_σ ⟹ IsTypeP1 M`
(`isTypeP1_of_mf_ne_msigma`), whence `U.subgroupOf M = ⊥`
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), while `|K| = p` prime is read off Theorem
15.2's structure conjunction directly.

This discharges two of the three conjuncts of Theorem A(8) in `theoremA_maximal_structure`; the
remaining `FittingIsTI M` (`F(M)` a TI-subgroup of `G`) is the genuinely deep §15 content (Theorem A
proper, via the §9–§10 uniqueness/fusion machinery) and is *not* supplied here. -/
theorem theoremA8_complement_eq_bot_and_kappa_prime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  refine ⟨isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot
    (isTypeP1_of_mf_ne_msigma hG hM hne) hU, ?_⟩
  obtain ⟨_, _, _, p, _, hpp, _, hKp, -⟩ :=
    (mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar).2
  exact ⟨p, hpp, hKp⟩

/-! ## Proposition 16.1: BG local taxonomy and shared Type I--V predicates -/

/-- **§14/§15-independent assembly engine for BG Proposition 16.1** (mmd L4478; the source proof
runs over Theorems A(8)/B(1)(2)(3)(4)/C(1)(2)(3)(10)/D(1), Theorem 15.2(a), and Theorem 15.7(c)).
Proposition 16.1 is the bridge from the BG-local `κ`/`σ`/`M_F` taxonomy to the shared, bundled
Type I--V predicates; the genuinely gated content is the *construction* of each `TypeXData`
structure from the local classification.  This engine isolates those constructions (and the few
structural facts the source proof uses to combine them) as named hypotheses and discharges the full
six-clause conjunction `sorry`-free; when the §15--§16 structural theory lands, the wrapper
`proposition_type_classification` cites it and applies this skeleton (the gated-endpoint pattern,
cf. `theoremD_msigma_conjugacy_and_centralizers_of_inputs`).

The named obligations, with their BG sources:

* the four **forward bridges** `hFI`/`hP2II`/`hP1neIIIIV`/`hP1eqV` — construct the Type
  I/II/III--IV/V data from the local classification (Theorem A(8)+B(1)(2)(3)+15.7(c) for I;
  C(1)(10)+B(1)(4)+A(8) for II; A(8)+Frattini for III/IV; 15.7(c) for V).  These are exactly the
  directions that `theoremI_nilpotentHall_conjugacy_and_type_dichotomy` and
  `theoremII_tame_embedding` consume;
* the four **reverse classifications** `hIF`/`hIIP2`/`hIIIIVP1`/`hVP1` — read off the local type
  from the Peterfalvi data (the `π(W₁) ⊆ κ(M)` argument for `→ M_P`, plus the `κ`/`M_F` refinement;
  Theorem C(2) for `I → M_F`);
* `hP_derived` (**Theorem C(3)**: `M' = U M_σ` for `M ∈ M_P`) and `hF_not_derived` (**Theorem
  A(3)**: `M = U M_σ ⊋ M'` for `M ∈ M_F`), which power clause (e);
* `h152a` (**Theorem 15.2(a)**: `M_F ≠ M_σ ⟹ M ∈ M_P₁`), used for clause (f).

The genuinely *derived* content (not a renamed hypothesis) is clauses (e) and (f), assembled from
the `κ`-trichotomy (`isTypeP_iff_isTypeP1_or_isTypeP2`, `isTypeF_iff_not_isTypeP`,
`not_isTypeP1_and_isTypeP2`) together with the bridges. -/
theorem proposition_type_classification_of_inputs {M : Subgroup G}
    (hFI : S14.IsTypeF M → OddOrder.GroupTheory.IsTypeI M)
    (hP2II : S14.IsTypeP2 M → OddOrder.GroupTheory.IsTypeII M)
    (hP1neIIIIV : S14.IsTypeP1 M → S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
      OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (hP1eqV : S14.IsTypeP1 M → S15.MF M = OddOrder.BG.Ch3.S10.Msigma M →
      OddOrder.GroupTheory.IsTypeV M)
    (hIF : OddOrder.GroupTheory.IsTypeI M → S14.IsTypeF M)
    (hIIP2 : OddOrder.GroupTheory.IsTypeII M → S14.IsTypeP2 M)
    (hIIIIVP1 : (OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) →
      S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hVP1 : OddOrder.GroupTheory.IsTypeV M →
      S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    (hP_derived : S14.IsTypeP M →
      ∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M)
    (hF_not_derived : S14.IsTypeF M →
      ¬ ∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M)
    (h152a : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M → S14.IsTypeP1 M) :
    (OddOrder.GroupTheory.IsTypeI M ↔ S14.IsTypeF M) ∧
      (OddOrder.GroupTheory.IsTypeII M ↔ S14.IsTypeP2 M) ∧
      ((OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) ↔
        S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) ∧
      (OddOrder.GroupTheory.IsTypeV M ↔
        S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) ∧
      ((∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ↔
          ¬ OddOrder.GroupTheory.IsTypeI M) ∧
      (S15.MF M = OddOrder.BG.Ch3.S10.Msigma M ↔
        OddOrder.GroupTheory.IsTypeI M ∨ OddOrder.GroupTheory.IsTypeII M ∨
          OddOrder.GroupTheory.IsTypeV M) := by
  -- `¬ M_P₁ ⟹ M_F = M_σ`, the contrapositive of Theorem 15.2(a).
  have mf_eq_of_not_typeP1 :
      ¬ S14.IsTypeP1 M → S15.MF M = OddOrder.BG.Ch3.S10.Msigma M := by
    intro hnP1
    by_contra hne
    exact hnP1 (h152a hne)
  refine ⟨⟨hIF, hFI⟩, ⟨hIIP2, hP2II⟩, ⟨hIIIIVP1, fun h => hP1neIIIIV h.1 h.2⟩,
    ⟨hVP1, fun h => hP1eqV h.1 h.2⟩, ?_, ?_⟩
  · -- **(e)** `M' = U M_σ ⟺ ¬ Type I`.  Via (a) (`Type I ⟺ M_F`), this is `(∃U …) ⟺ M_P`.
    constructor
    · -- `→`: a Type I `M` would be `M_F` (`hIF`), contradicting Theorem A(3) (`hF_not_derived`).
      intro hex hI
      exact hF_not_derived (hIF hI) hex
    · -- `←`: `¬ Type I ⟹ ¬ M_F ⟹ M_P`, and Theorem C(3) (`hP_derived`) supplies the decomposition.
      intro hnI
      have hnF : ¬ S14.IsTypeF M := fun hF => hnI (hFI hF)
      have hP : S14.IsTypeP M := not_not.mp (by rwa [S14.isTypeF_iff_not_isTypeP] at hnF)
      exact hP_derived hP
  · -- **(f)** `M_F = M_σ ⟺ M` is Type I, II, or V.
    constructor
    · -- `→`: case on the `κ`-trichotomy.  `M_F` (`κ = ∅`) ⟹ I; `M_P₂` ⟹ II; `M_P₁`+`M_F = M_σ` ⟹ V.
      intro heq
      by_cases hP : S14.IsTypeP M
      · rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
        · exact Or.inr (Or.inr (hP1eqV hP1 heq))
        · exact Or.inr (Or.inl (hP2II hP2))
      · exact Or.inl (hFI (S14.isTypeF_iff_not_isTypeP.mpr hP))
    · -- `←`: Type I ⟹ `M_F` ⟹ `¬ M_P₁` ⟹ `M_F = M_σ`; Type II ⟹ `M_P₂` ⟹ `¬ M_P₁` ⟹ `M_F = M_σ`;
      -- Type V carries `M_F = M_σ` directly (`hVP1`).
      rintro (hI | hII | hV)
      · have hnP : ¬ S14.IsTypeP M := S14.isTypeF_iff_not_isTypeP.mp (hIF hI)
        exact mf_eq_of_not_typeP1 (fun hP1 => hnP (S14.isTypeP_of_isTypeP1 hP1))
      · have hP2 := hIIP2 hII
        exact mf_eq_of_not_typeP1 (fun hP1 => S14.not_isTypeP1_and_isTypeP2 ⟨hP1, hP2⟩)
      · exact (hVP1 hV).2

/-- **BG Proposition 16.1** (mmd L4478): the §14--§15 local families are exactly
the shared Type I--V maximal-subgroup predicates consumed downstream by Peterfalvi.
Six clauses = mmd (a)-(f): (a) Type I ⟺ `M ∈ ℳ_𝓕`, (b) Type II ⟺ `M ∈ ℳ_𝓟₂`,
(c) Type III/IV ⟺ `M ∈ ℳ_𝓟₁ ∧ M_F ≠ M_σ`, (d) Type V ⟺ `M ∈ ℳ_𝓟₁ ∧ M_F = M_σ`,
(e) `M' = U M_σ ⟺ M` not Type I, (f) `M_F = M_σ ⟺ M` Type I/II/V. -/
theorem proposition_type_classification [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (OddOrder.GroupTheory.IsTypeI M ↔ S14.IsTypeF M) ∧
      (OddOrder.GroupTheory.IsTypeII M ↔ S14.IsTypeP2 M) ∧
      ((OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) ↔
        S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) ∧
      (OddOrder.GroupTheory.IsTypeV M ↔
        S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) ∧
      ((∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ↔
          ¬ OddOrder.GroupTheory.IsTypeI M) ∧
      (S15.MF M = OddOrder.BG.Ch3.S10.Msigma M ↔
        OddOrder.GroupTheory.IsTypeI M ∨ OddOrder.GroupTheory.IsTypeII M ∨
          OddOrder.GroupTheory.IsTypeV M) := by
  sorry

/-- **Type I and non-Type-I are mutually exclusive** (corollary of Proposition
16.1(a)–(d)).  A maximal subgroup of a minimal simple group of odd order that is
Type I cannot also be one of Types II–V.

The proof reads the type dictionary of `proposition_type_classification`: clause
(a) says Type I `⟺ M ∈ ℳ_𝓕` (`S14.IsTypeF`), while clauses (b)–(d) place each of
Types II–V in `ℳ_𝓟` (`S14.IsTypeP`) — Type II in `ℳ_𝓟₂`, Types III/IV/V in
`ℳ_𝓟₁`.  Since `ℳ_𝓕` and `ℳ_𝓟` are complementary
(`S14.isTypeF_iff_not_isTypeP`), the two cannot coincide.

Used by `OddOrder.section16MaximalPair_of_isMinimalSimpleOdd` to discharge the
all-Type-I branch of Peterfalvi (8.8): the case-(b) witness of (12.17) is a
non-Type-I maximal subgroup, contradicting "every maximal subgroup is Type I". -/
theorem not_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hNonI : OddOrder.GroupTheory.IsTypeNonI M) :
    ¬ OddOrder.GroupTheory.IsTypeI M := by
  intro hI
  obtain ⟨hIa, hIIb, hIII_IVc, hVd, _, _⟩ := proposition_type_classification hG hM
  -- Type I forces `M ∈ ℳ_𝓕`, hence `M ∉ ℳ_𝓟`.
  refine S14.isTypeF_iff_not_isTypeP.mp (hIa.mp hI) ?_
  -- but each non-Type-I alternative places `M ∈ ℳ_𝓟`.
  rcases hNonI with hII | hIII | hIV | hV
  · exact S14.isTypeP_of_isTypeP2 (hIIb.mp hII)
  · exact S14.isTypeP_of_isTypeP1 (hIII_IVc.mp (Or.inl hIII)).1
  · exact S14.isTypeP_of_isTypeP1 (hIII_IVc.mp (Or.inr hIV)).1
  · exact S14.isTypeP_of_isTypeP1 (hVd.mp hV).1

/-! ## Theorems I and II: the BG output consumed by Peterfalvi -/

/-- **§16 helper (general, §14-independent).**  A `π`-Hall subgroup `H` of `G` contained in a
subgroup `K` is a `π`-Hall subgroup of `K` (no normality needed): the order of `H.subgroupOf K`
equals `|H|` (so its prime factors are `⊆ π`), and its index `[K : H] = H.relIndex K` divides
`[G : H]` (so the index prime factors avoid `π`).  Used in Theorem I to turn the global nilpotent
Hall hypothesis on `H` into the `H.subgroupOf M_σ`-Hall hypothesis that Corollary 15.3(b)
(`mf_hall_centralizer_control`) consumes, after Corollary 15.4 places `H ≤ M_σ`. -/
theorem isHallSubgroup_subgroupOf_of_le [Finite G] {π : Set ℕ} {H K : Subgroup G}
    (hH : Ch03.IsHallSubgroup π H) (hHK : H ≤ K) :
    Ch03.IsHallSubgroup π (H.subgroupOf K) := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  refine ⟨?_, ?_⟩
  · -- `|H.subgroupOf K| = |H|`, so its prime factors are exactly those of `|H| ⊆ π`.
    intro q hq
    rw [hcard] at hq
    exact hH.1 q hq
  · -- `[K : H] = H.relIndex K ∣ [G : H]`, so its prime factors avoid `π`.
    intro q hq hqπ
    have hdvd : (H.subgroupOf K).index ∣ H.index := by
      have he : (H.subgroupOf K).index = H.relIndex K := rfl
      rw [he]
      exact Subgroup.relIndex_dvd_index_of_le hHK
    rw [Nat.mem_primeFactors] at hq
    exact hH.2 q (Nat.mem_primeFactors.mpr
      ⟨hq.1, hq.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ

/-- **BG Theorem I** (mmd L4526): nilpotent Hall conjugacy and the global maximal
subgroup dichotomy used by Peterfalvi (8.8). -/
theorem theoremI_nilpotentHall_conjugacy_and_type_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ H : Subgroup G, Group.IsNilpotent ↥H →
      Ch03.IsHallSubgroup (S14.piSet H) H →
        ∀ x ∈ H, ∀ y ∈ H,
          (∃ g : G, y = g * x * g⁻¹) ↔
            ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) ∧
      ((∀ M : Subgroup G, M ∈ maximalSubgroups G → OddOrder.GroupTheory.IsTypeI M) ∨
        ∃ S T W1 W2 W : Subgroup G,
          S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
          W = W1 ⊔ W2 ∧ IsCyclic ↥W ∧ S ⊓ T = W ∧
          OddOrder.GroupTheory.IsTypeNonI S ∧ OddOrder.GroupTheory.IsTypeNonI T ∧
          (OddOrder.GroupTheory.IsTypeII S ∨ OddOrder.GroupTheory.IsTypeII T) ∧
          ∀ M : Subgroup G, M ∈ maximalSubgroups G →
            OddOrder.GroupTheory.IsTypeI M ∨ S14.IsConjugateSubgroup M S ∨
              S14.IsConjugateSubgroup M T) := by
  classical
  refine ⟨?_, ?_⟩
  · -- **Theorem I, first assertion** (mmd L4524): nilpotent Hall fusion is `N_G(H)`-controlled.
    -- "follows directly from Corollaries 15.4 and 15.3(b)".
    intro H hHnil hHall x hx y hy
    constructor
    · -- `→`: `G`-conjugacy of `x, y ∈ H` is already `N_G(H)`-conjugacy.
      rintro ⟨g, hg⟩
      by_cases hHne : H = ⊥
      · -- `H = ⊥`: then `x = y = 1`, witnessed by `n = 1 ∈ N_G(H)`.
        subst hHne
        rw [Subgroup.mem_bot] at hx hy
        exact ⟨1, Subgroup.one_mem _, by rw [hx, hy]; group⟩
      · -- `H ≠ ⊥`: Corollary 15.4 embeds `H ≤ M_σ` for some `M ∈ ℳ(H)`.
        obtain ⟨M, hMmem, hHMσ⟩ :=
          S15.nilpotent_hall_embeds_in_msigma hG hHnil hHne hHall
        have hM : M ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMmem).1
        -- `H ≤ M_σ`, so `H.subgroupOf M_σ` is a `π(H)`-Hall subgroup of `M_σ`.
        have hHall' : Ch03.IsHallSubgroup (S14.piSet H)
            (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
          isHallSubgroup_subgroupOf_of_le hHall hHMσ
        -- Corollary 15.3(b): `N_M(H)`-fusion control; `N_M(H) ⊆ N_G(H)`.
        obtain ⟨_, hfusion⟩ := S15.mf_hall_centralizer_control hG hM hHall' hHne
        exact hfusion x hx y hy ⟨g, hg⟩
    · -- `←`: `N_G(H)`-conjugacy is in particular `G`-conjugacy.
      rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
  · -- **Theorem I, dichotomy** (mmd L4528): every maximal is Type I, or the type-P pair
    -- `S, T` covers everything.  Proposition 16.1(a) + Theorem C(4)(6)(7) + Theorem 14.7 duality.
    -- **Bridge: a non-Type-I maximal is type P.**  Proposition 16.1(a) gives `TypeI ⟺ TypeF`,
    -- and `TypeF ⟺ κ(M) = ∅`, so `¬TypeI` forces `κ(M)` nonempty, i.e. `IsTypeP`.
    have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
        ¬ OddOrder.GroupTheory.IsTypeI N → S14.IsTypeP N := by
      intro N hN hnotI
      have hiff := (proposition_type_classification hG hN).1
      have hnotF : ¬ S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
      rw [S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- **Bridge: a type-P maximal is non-Type-I (`II`/`III`/`IV`/`V`).**  Split `κ(M)` against
    -- `π(M) - σ(M)`: equal ⟹ `P₁` ⟹ Type V (`M_F = M_σ`) or III/IV (`M_F ≠ M_σ`); unequal ⟹
    -- `P₂` ⟹ Type II.  Uses Proposition 16.1(b)(c)(d).
    have typeP_imp_nonI : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
        S14.IsTypeP N → OddOrder.GroupTheory.IsTypeNonI N := by
      intro N hN hP
      obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ := proposition_type_classification hG hN
      by_cases hk : S14.kappa N = S14.sigmaComplementPrimes N
      · -- `P₁`: Type III/IV (if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).
        have hP1 : S14.IsTypeP1 N := ⟨hP, hk⟩
        by_cases hMF : S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
        · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
        · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
          · exact Or.inr (Or.inl hIII)
          · exact Or.inr (Or.inr (Or.inl hIV))
      · -- `P₂`: Type II.
        exact Or.inl (hbII.mpr ⟨hP, hk⟩)
    -- Case split: either every maximal is Type I, or some `S` is not.
    by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        OddOrder.GroupTheory.IsTypeI M
    · exact Or.inl hall
    · -- Pick a non-Type-I maximal `S`; it is type P.
      push_neg at hall
      obtain ⟨S, hS, hSnotI⟩ := hall
      have hSP : S14.IsTypeP S := notTypeI_imp_typeP S hS hSnotI
      haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
      -- Produce the `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
      obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (S14.kappa S)
      set K : Subgroup G := K'.map S.subtype with hKdef
      have hKeq : K.subgroupOf S = K' :=
        Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
      have hK : Ch03.IsHallSubgroup (S14.kappa S) (K.subgroupOf S) := by
        rw [hKeq]; exact hK'
      set Kstar : Subgroup G :=
        OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
      -- Theorem 14.7 (`typeP_duality`): the dual pair `S, T := Mstar`, with covering.
      obtain ⟨_, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
          ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, hcover⟩, _⟩ :=
        typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
      -- A Hall `(κ(S) ∪ σ(S))'`-subgroup `U` of `S` (Hall's theorem in the solvable `S`), needed
      -- to invoke `typeP_pair_inf_eq` (the reverse inclusion `S ∩ Mstar ≤ K ⊔ K*`).
      obtain ⟨U', hU'⟩ :=
        Ch03.hall_E_exists (G := ↥S) ((S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
      have hUeq : (U'.map S.subtype).subgroupOf S = U' :=
        Subgroup.comap_map_eq_self_of_injective S.subtype_injective U'
      have hU : Ch03.IsHallSubgroup ((S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
          ((U'.map S.subtype).subgroupOf S) := by rw [hUeq]; exact hU'
      refine Or.inr ⟨S, Mstar, K, Kstar, K ⊔ Kstar, hS, hMstarMem, ?_, rfl, hcyc, ?_, ?_, ?_, ?_, ?_⟩
      · -- `S ≠ Mstar`: else `S` would be conjugate to itself `= Mstar`, against `¬conj S Mstar`.
        rintro rfl
        exact hSnconjMstar (S14.IsConjugateSubgroup.refl S)
      · -- `S ∩ Mstar = W = K ⊔ K*`: **BG Theorem I clause (2)** (= Theorem 14.7(4) / C(6)).  The
        -- forward inclusion is immediate; the reverse `S ∩ Mstar ≤ K ⊔ K*` is the genuine §16
        -- structural content, proved in `S16_PairIntersection` as `typeP_pair_inf_eq`.
        exact typeP_pair_inf_eq hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef hU
          hMstarMem hMstarP hSnconjMstar hKstarMstar hKstar_hall hcyc hK_eq
      · -- `IsTypeNonI S`: `S` is type P.
        exact typeP_imp_nonI S hS hSP
      · -- `IsTypeNonI Mstar`: `Mstar` is type P.
        exact typeP_imp_nonI Mstar hMstarMem hMstarP
      · -- `IsTypeII S ∨ IsTypeII Mstar`: from `IsTypeP2 S ∨ IsTypeP2 Mstar` via Prop 16.1(b).
        rcases hP2disj with hP2S | hP2M
        · exact Or.inl ((proposition_type_classification hG hS).2.1.mpr hP2S)
        · exact Or.inr ((proposition_type_classification hG hMstarMem).2.1.mpr hP2M)
      · -- Covering: each maximal is Type I, or (being type P) conjugate to `S` or `Mstar`.
        intro M hM
        by_cases hMI : OddOrder.GroupTheory.IsTypeI M
        · exact Or.inl hMI
        · exact Or.inr (hcover M hM (notTypeI_imp_typeP M hM hMI))

/-- **Assembly for BG Theorem II (Ti)** (mmd L4546--L4550), as a `sorry`-free,
axiom-clean *gated-endpoint skeleton*.

The mmd proof decomposes `A_0(M)` into the disjoint pieces `M_σ`, `A(M) - M_σ`,
and `A_0(M) - A(M)`, observes that cross-piece elements have distinct orders (so
are never `G`-conjugate), and concludes:
* within `M_σ`, `G`-conjugacy is `M`-conjugacy by **Theorem D(1)** (`hD1`);
* within either TI piece (**Theorem B(5)**/`hTI_B`, **Theorem C(9)**/`hTI_C`),
  `G`-conjugacy forces the conjugator into `M` by the TI condition.

This bundles those three inputs plus the cross-piece exclusion `hPieceInv`
(`G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the formal
content of "distinct orders across pieces") and discharges (Ti) with no `sorry`
of its own.  The remaining gated obligation when this is applied is exactly
`hPieceInv` (BG Theorem E prime-structure of the pieces). -/
theorem theoremII_conjunct1_of_inputs {M K U : Subgroup G}
    (hD1 : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹)
    (hTI_B : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M)
    (hTI_C : IsTISubset (A0Set M K \ ASet M U) M)
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U)) :
    ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹ := by
  intro x hxX y hyX hconj
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨hMσiff, hAiff⟩ := hPieceInv x hxX y hyX ⟨g, hg⟩
  by_cases hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M
  · -- Both in `M_σ`: Theorem D(1).
    exact hD1 x hxMσ y (hMσiff.mp hxMσ) ⟨g, hg⟩
  · -- `x ∉ M_σ`, hence `y ∉ M_σ`; `x, y` lie in a common TI piece.
    have hyMσ : y ∉ OddOrder.BG.Ch3.S10.Msigma M := fun h => hxMσ (hMσiff.mpr h)
    have hxMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hyMσ' : y ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    by_cases hxA : x ∈ ASet M U
    · -- `x, y ∈ A(M) - M_σ` (TI piece, Theorem B(5)): the conjugator lies in `M`.
      have hyA : y ∈ ASet M U := hAiff.mp hxA
      exact ⟨g, hTI_B g ⟨x, ⟨hxA, hxMσ'⟩, hg ▸ ⟨hyA, hyMσ'⟩⟩, hg⟩
    · -- `x ∉ A(M)`: only possible for `X = A_0(M)`.
      rcases hX with hXA | hXA0
      · exact absurd (hXA ▸ hxX) hxA
      · -- `x, y ∈ A_0(M) - A(M)` (TI piece, Theorem C(9)).
        have hyA : y ∉ ASet M U := fun h => hxA (hAiff.mpr h)
        exact ⟨g, hTI_C g ⟨x, ⟨hXA0 ▸ hxX, hxA⟩, hg ▸ ⟨hXA0 ▸ hyX, hyA⟩⟩, hg⟩

/-- **Assembly for BG Theorem II** (mmd L4548), as a *gated-endpoint skeleton* (`sorry`-free in its
own body).  `A(M)`/`A_0(M)` are tamely embedded — the BG form of the centralizer-control input used
by Peterfalvi (8.12)--(8.13).

The body is the full Theorem II proof; it still cites the (`sorry`-bearing) §16 structure theorems
A--D and Proposition 16.1 inline, so it is *not* axiom-clean (it depends transitively on `sorryAx`
through them).  What this skeleton isolates are the two obligations *beyond* that standard A--D
suite, as named hypotheses (cf. `theoremII_conjunct1_of_inputs`):
* `hPieceInv` — the conjunct-1 cross-piece exclusion: `G`-conjugate elements of `X` share `M_σ`-
  and `A(M)`-membership (the "distinct orders across pieces" content of BG Theorem E);
* `hMaxUnique` — the conjunct-3 uniqueness `|ℳ(C_G(x))| = 1` for an escaping centralizer
  (BG §9--§10 Uniqueness), which pins the Type I/II maximal overgroup of `C_G(x)` to Theorem
  D(4)'s `N(x)`.

The wrapper `theoremII_tame_embedding` cites this with both obligations as `sorry`. -/
theorem theoremII_tame_embedding_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U))
    (hMaxUnique : ∀ x : G, x ∈ X → x ≠ 1 →
      ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∀ N₁ N₂ : Subgroup G,
          N₁ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) →
          N₂ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) → N₁ = N₂) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  classical
  -- Abbreviate the escaping set `D`.
  set D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M} with hDdef
  -- **Core gated reduction (mmd L4546-L4548).**  `A_0(M)` is the disjoint union of `M_σ`,
  -- `A(M) - M_σ`, and `A_0(M) - A(M)`; the latter two are `TI`-subsets of `G` with normalizer
  -- `M` (Theorem B(5) and Theorem C(9)), so every element of them has its `G`-centralizer inside
  -- `M`.  Hence an `x ∈ X` with `C_G(x) ⊄ M` must lie in `M_σ`, i.e. `D ⊆ M_σ#`.
  --
  -- This step needs the Hall data behind Theorem B(5)/C(9), which the *statement* of Theorem II
  -- does not carry (its `K`, `U` are free, not pinned to the `(κ ∪ σ)'`-Hall / `κ`-Hall factors).
  -- It is therefore isolated as a gated input; once it (and the dual-piece `TI` facts) land with
  -- their Hall hypotheses, `D ⊆ A(M)` (conjunct 2) becomes pure citation, as below.
  have hDsub : D ⊆ S14.sigmaSharp M := by
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    -- `x ∈ M_σ#`: it suffices to show `x ∈ M_σ` (we already have `x ≠ 1`).
    simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_diff, SetLike.mem_coe,
      Set.mem_singleton_iff]
    refine ⟨?_, hx1⟩
    by_contra hxnMσ
    -- `x ∉ M_σ`; the coerced form, and the TI piece for `A(M) - M_σ` (Theorem B(5)).
    have hxnMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hTIB : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M :=
      (theoremB_U_and_A_tame hG hM hU).2.2.2.2
    rcases hX with hXA | hXA0
    · -- `X = A(M)`: `x ∈ A(M) - M_σ`, so `C_G(x) ≤ M` (Theorem B(5)) contradicts `C_G(x) ⊄ M`.
      exact hxc (hTIB.centralizer_le ⟨hXA ▸ hxX, hxnMσ'⟩)
    · -- `X = A_0(M)`.
      have hxA0 : x ∈ A0Set M K := hXA0 ▸ hxX
      by_cases hxA : x ∈ ASet M U
      · -- `x ∈ A(M) - M_σ`: Theorem B(5) again.
        exact hxc (hTIB.centralizer_le ⟨hxA, hxnMσ'⟩)
      · -- `x ∈ A_0(M) - A(M)`.
        by_cases hKbot : K = ⊥
        · -- **Type-F** (`K = ⊥`): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Theorem A(3)),
          -- so `x ∈ A(M)`, contradicting `x ∉ A(M)`.
          refine hxA ⟨hxA0.1, ?_⟩
          have hxM : x ∈ M := hxA0.1.1
          have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
            (theoremA_maximal_structure hG hM hK rfl hU).2.2.1
          have hx' : x ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hxM
          rw [hKbot, bot_sup_eq] at hx'
          exact hx'
        · -- `K ≠ ⊥`: TI by Theorem C(9), giving `C_G(x) ≤ M`.
          obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
            theoremC_paired_structure hG hM hKbot hK rfl hU
          exact hxc (hTIC.centralizer_le ⟨hxA0, hxA⟩)
  -- **`D ⊆ A(M)` (conjunct 2).**  `D ⊆ M_σ#` and `M_σ# ⊆ A(M)`: a nonidentity `x ∈ M_σ` lies in
  -- `\widehat{M_σ}` (`sigmaSharp_subset_hatMsigma`) and in `M_σ ≤ U M_σ`, so `x ∈ A(M)`.
  have hMσsharp_sub_A : S14.sigmaSharp M ⊆ ASet M U := by
    intro x hx
    refine ⟨sigmaSharp_subset_hatMsigma M hx, ?_⟩
    have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := (Set.mem_diff _).mp hx |>.1
    exact (le_sup_right : OddOrder.BG.Ch3.S10.Msigma M ≤
      (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G)) hxMσ
  refine ⟨?_, hDsub.trans hMσsharp_sub_A, ?_⟩
  · -- **Conjunct 1 (Ti) (mmd L4546-L4550).**  Assembled from Theorem D(1) (`M_σ` fusion),
    -- Theorem B(5)/C(9) (the two TI pieces), and the cross-piece exclusion `hPieceInv`, via
    -- `theoremII_conjunct1_of_inputs`.  Only `hPieceInv` remains gated (BG Theorem E).
    have hTI_C : IsTISubset (A0Set M K \ ASet M U) M := by
      by_cases hKbot : K = ⊥
      · -- `K = ⊥` (type F): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Thm A(3)), so the diff is empty.
        intro g hex
        obtain ⟨z, ⟨hzA0, hznA⟩, _⟩ := hex
        refine absurd ⟨hzA0.1, ?_⟩ hznA
        have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
          (theoremA_maximal_structure hG hM hK rfl hU).2.2.1
        have hz' : z ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hzA0.1.1
        rw [hKbot, bot_sup_eq] at hz'
        exact hz'
      · obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
          theoremC_paired_structure hG hM hKbot hK rfl hU
        exact hTIC
    refine theoremII_conjunct1_of_inputs
      (theoremD_msigma_conjugacy_and_centralizers hG hM).1
      ((theoremB_U_and_A_tame hG hM hU).2.2.2.2) hTI_C hX ?_
    -- `hPieceInv`: `G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the
    -- "distinct orders across pieces" input of the mmd proof (BG Theorem E), a named obligation.
    exact hPieceInv
  · -- **Conjunct 3 (mmd L4552).**  For `x ∈ D ⊆ M_σ#` with `C_G(x) ⊄ M`, Theorem D(4) gives a
    -- unique maximal `N(x) ⊇ C_G(x)` that is of type `F` or `P₂`; Proposition 16.1(a)(b) rewrites
    -- this as Type I or Type II.  Existence and the type classification are pure citation; the
    -- *uniqueness* of the maximal overgroup is the residual gated input (BG §9-§10 Uniqueness).
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    have hxMσsharp : x ∈ S14.sigmaSharp M := hDsub ⟨hxX, hx1, hxc⟩
    -- Theorem D(4): the `∃! N` with the type-`F`/`P₂` data attached to escaping centralizers.
    obtain ⟨_, _, _, hD4⟩ := theoremD_msigma_conjugacy_and_centralizers hG hM
    obtain ⟨_R, _hR, N₀, hQN₀, _hQuniq⟩ := hD4 x hxMσsharp hxc
    -- Unpack what Theorem II needs from the rich Theorem D(4) predicate `Q N₀`.
    obtain ⟨hN₀mem, _, _, _, hN₀type, _⟩ := hQN₀
    -- Convert `IsTypeF N₀ ∨ IsTypeP2 N₀` to `IsTypeI N₀ ∨ IsTypeII N₀` (Proposition 16.1(a)(b)).
    have hN₀ : N₀ ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hN₀mem).1
    have htype : OddOrder.GroupTheory.IsTypeI N₀ ∨ OddOrder.GroupTheory.IsTypeII N₀ := by
      obtain ⟨hIiff, hIIiff, _⟩ := proposition_type_classification hG hN₀
      rcases hN₀type with hF | hP2
      · exact Or.inl (hIiff.mpr hF)
      · exact Or.inr (hIIiff.mpr hP2)
    refine ⟨N₀, ⟨hN₀mem, htype⟩, ?_⟩
    -- Uniqueness of the maximal overgroup of `C_G(x)`: the named obligation `hMaxUnique`.  Theorem
    -- D(4) gives uniqueness only for its *full* predicate `Q`; pinning the weaker "maximal
    -- overgroup, Type I/II" to the same `N₀` is exactly `|ℳ(C_G(x))| = 1` (BG §9--§10 Uniqueness).
    rintro N' ⟨hN'mem, _hN'type⟩
    exact hMaxUnique x hxX hx1 hxc N' N₀ hN'mem hN₀mem

/-- **BG Theorem II** (mmd L4548): `A(M)` and `A_0(M)` are tamely embedded.  The BG form of the
centralizer-control input used by Peterfalvi (8.12)--(8.13).  Cites the gated-endpoint skeleton
`theoremII_tame_embedding_of_inputs`; the two residual obligations — the BG Theorem E cross-piece
exclusion and the BG §9--§10 maximal-overgroup uniqueness — remain `sorry`. -/
theorem theoremII_tame_embedding [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) :=
  theoremII_tame_embedding_of_inputs hG hM hK hU hX
    -- `hPieceInv`: BG Theorem E cross-piece exclusion.
    (by sorry)
    -- `hMaxUnique`: BG §9--§10 maximal-overgroup uniqueness `|ℳ(C_G(x))| = 1`.
    (by sorry)

end OddOrder.BG.Ch4.S16
