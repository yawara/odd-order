/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_PairIntersection
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.AInvariantComplement

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

/-- **BG Theorem A(3) decomposition** (mmd L4276): `M = K U M_σ`.  For a maximal `M` with Hall
`κ`-subgroup `K ≤ M` and Hall `(κ ∪ σ)'`-subgroup `U ≤ M`, the three factors join to all of `M`.

Type-F (`K = ⊥`): `M = U M_σ` from the `K = ⊥` `SubgroupESetup` (`E_compl_sup`).  Type-P (`K ≠ ⊥`):
`M' = U M_σ` and `M'` complements `K` in `M` (`typeP_auxiliary_structure`, Lemma 15.1(b)/Theorem
14.7(h)), so `M = M' K = (U M_σ) K`; the complement's `H ⊔ K = ⊤` is pushed from `M` to `G` via
`Subgroup.map M.subtype`.  This is the `sorry`-free standalone form of conjunct 3 of
`theoremA_maximal_structure`. -/
theorem typeP_maximal_eq_kappaHall_sup_U_sup_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  by_cases hKbot : K = ⊥
  · -- Type-F: `M = U M_σ`.
    obtain ⟨_E₁, _E₂, _E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    rw [hKbot, bot_sup_eq, sup_comm]
    exact hsetup.E_compl_sup.symm
  · -- Type-P: `M = M' K`, `M' = U M_σ`.
    have haux := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
    obtain ⟨hM'eq, _, hcompl, _⟩ := haux.2.2.2.2.1 hKbot
    have hMle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hMM' : derivedInG M ⊔ K = M := by
      have htop : (derivedInG M ⊔ K).subgroupOf M = ⊤ := by
        rw [Subgroup.subgroupOf_sup hMle hKM]; exact hcompl.sup_eq_top
      exact le_antisymm (sup_le hMle hKM) (Subgroup.subgroupOf_eq_top.mp htop)
    -- `M = M' K = (U M_σ) K = K U M_σ` (a pure `⊔`-AC rewrite, no lattice `whnf`).
    conv_lhs => rw [← hMM']
    rw [hM'eq, sup_comm (U ⊔ OddOrder.BG.Ch3.S10.Msigma M) K, ← sup_assoc]

/-- **BG Theorem A — the ungated conjuncts** (mmd L4274), as a standalone `sorry`-free lemma.

Bundles the conjuncts of `theoremA_maximal_structure` whose upstreams are all proved transitively
(mirroring `theoremB_U_sylow_abelian_rank_le_two` / `sigma_reps_pairwise_disjoint`):

* A(1) `M_σ` is a `σ(M)`-Hall subgroup (`Msigma_isHall`);
* A(2) `K` cyclic (`typeP_auxiliary_structure`, Lemma 15.1(a)/Theorem 14.7(h));
* A(3) `M ≤ N_G(U M_σ)` (`typeP_auxiliary_structure`: `U M_σ = M` for type-F, `= M' ⊴ M` for type-P);
* A(4) `C_U(k) = 1` for `k ∈ K#` (`typeP_hall_inf_centralizer_kappaElement_eq_bot`);
* A(5) `Kstar ≠ ⊥` (`S14.typeP_structure`, with `K = ⊥` collapsing `Kstar = M_σ ≠ ⊥`) and the
  element form `C_M(k) = K ⊔ K*` for `K ≠ ⊥`, `k ∈ K#` (`typeP_centralizer_kappaElement_eq`);
* A(6) `M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`).

The remaining monolith conjuncts (`M = K U M_σ`, `M'' ≤ F(M)`, the `M_F ≠ M_σ` extreme A(8)) are
left to `theoremA_maximal_structure`/`theoremA8_structure`: A(3)-decomposition needs the
complement→join plumbing and A(7) routes through the still-`sorry` type-`P₁` chief-factor inputs.

As with the Theorem B(1) precedent the explicit `hKM : K ≤ M`, `hUM : U ≤ M` are added (part of the
BG setup `M = K U M_σ` but not forced by the Hall conditions on `K.subgroupOf M`/`U.subgroupOf M`). -/
theorem theoremA_ungated_conjuncts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M := by
  -- `IsTypeP M` from a nonempty `κ`-Hall, packaged for the type-`P` conjuncts.
  have hPofne : K ≠ ⊥ → S14.IsTypeP M := fun hKne =>
    isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK
      (fun h => hKne (by rw [← Subgroup.map_subgroupOf_eq_of_le hKM, h, Subgroup.map_bot]))
  have haux := typeP_auxiliary_structure hG hM hKM hUM hK hKstar hU
  haveI hKcyc : IsCyclic ↥K := haux.2.1
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_isHall hG hM, hKcyc, haux.1, ?_, ?_, ?_,
    maxNilpotentNormalHall_le_Msigma hG hM, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM⟩
  · -- A(4): `C_U(k) = 1`.  Vacuous for `K = ⊥`; else type-`P` element centralizer.
    intro k hk hk1
    by_cases hKbot : K = ⊥
    · rw [hKbot, Subgroup.mem_bot] at hk; exact absurd hk hk1
    · exact typeP_hall_inf_centralizer_kappaElement_eq_bot hG hM (hPofne hKbot) hKM hUM hK hKstar hU
        k hk hk1
  · -- A(5): `Kstar ≠ ⊥`.
    by_cases hKbot : K = ⊥
    · -- type-F: `Kstar = M_σ ⊓ C(1) = M_σ ≠ ⊥`.
      subst hKbot
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
        exact Set.singleton_subset_iff.mpr (Subgroup.one_mem _)
      rw [hc, inf_top_eq] at hKstar
      rw [hKstar]
      exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    · exact (S14.typeP_structure hG hM (hPofne hKbot) hKM hK hKstar hU).2.1
  · -- A(5) element form: `C_M(k) = K ⊔ K*` for `K ≠ ⊥`.
    intro hKne k hk hk1
    exact typeP_centralizer_kappaElement_eq hG hM (hPofne hKne) hKM hK hKstar hU k hk hk1

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

/-- **`κ(M) = π(M) ∖ σ(M)` from a trivial Hall `(κ ∪ σ)ᶜ`-complement** (the prime-set half of the
type-`P₁` ⟺ `U = ⊥` characterization).  If the Hall `(κ(M) ∪ σ(M))ᶜ`-subgroup of `M` is trivial,
then `(κ ∪ σ)ᶜ` contains no prime dividing `|M|` (the Hall index condition `hU.2` with index `|M|`),
so `π(M) ⊆ κ(M) ∪ σ(M)`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` (every `κ`-prime is a non-`σ` divisor of
`|M|`) this gives `κ(M) = π(M) ∖ σ(M) = sigmaComplementPrimes M`.

Hoisted above `theoremC_paired_structure` (2026-06-21, lane F) so its conjunct 12 (`U = ⊥ → |K*|`
prime) can derive `IsTypeP1 M` from `U = ⊥`.  Together with
`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (below) it is the prime-set core of BG's
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

/-- **`M` is type `P₂` from a nontrivial Hall `(κ ∪ σ)ᶜ`-complement** (the type-`P₂` side of the
`M ∈ M_{P₁} ⟺ U = ⊥` characterization): a type-`P` maximal subgroup whose Hall `(κ(M) ∪ σ(M))ᶜ`-
subgroup `U` is nontrivial has `κ(M) ≠ σ'(M)`, i.e. is type `P₂`.  Dual to
`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`: a prime `p ∣ |U|` lies in `(κ ∪ σ)ᶜ ∩ π(M)`,
so if `κ = σ' = π ∖ σ` then `p ∈ κ` (it is a non-`σ` divisor of `|M|`), contradicting `p ∉ κ`. -/
theorem isTypeP2_of_hall_subgroupOf_ne_bot [Finite G] {M U : Subgroup G}
    (hP : S14.IsTypeP M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U.subgroupOf M ≠ ⊥) :
    S14.IsTypeP2 M := by
  refine ⟨hP, fun hκσ => ?_⟩
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (by rwa [ne_eq, ← Subgroup.card_eq_one] at hUne)
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩)
  have hpπ : p ∈ S14.piSet M :=
    Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans (Subgroup.card_subgroup_dvd_card (U.subgroupOf M)), Nat.card_pos.ne'⟩
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hpcompl (Set.mem_union_right _ h)
  have hpκ : p ∈ S14.kappa M := by rw [hκσ]; exact ⟨hpπ, hpσ⟩
  exact hpcompl (Set.mem_union_left _ hpκ)

/-- **BG Theorem C(9), structural inclusion** (mmd L4385; schematic proof: Proposition 14.2(d) +
Theorem A(3),(5)): every element of `A_0(M) − A(M)` is `M`-conjugate to an element of
`Ẑ = Z − (K ∪ K*)`.  This is the `⊆` half of BG's identity `A_0(M) − A(M) = 𝒞_M(Ẑ)`, and together
with the TI-ness of `Ẑ` (Theorem 14.7(e), `N_G(Ẑ) = K ⊔ K* ≤ M`) it is exactly what the TI claim of
Theorem C(9) needs, via the transport lemma `IsTISubset.of_subset_conj_of_isTISubset`.

Proof: let `a ∈ A_0(M) − A(M)`, so `a ∈ M`, `M_σ ⊓ C_G(a) ≠ 1`, `a ∉ 𝒞_G(K#)`, and `a ∉ U M_σ`.
Take the `κ`/`κ'`-decomposition `a = a_κ · a_{κ'}` (`exists_isPiElement_mul`: commuting powers of
`a`, `a_κ` a `κ`-element, `a_{κ'}` a `κ'`-element).  Conjugate by some `w ∈ M` so that `a_κ ∈ K`
(`exists_conj_smul_le_isHall_kappa`, as `⟨a_κ⟩` is a `κ`-subgroup of `M`).  Then:

* `a_κ ≠ 1`: otherwise `a = a_{κ'}` is a `κ'`-element, hence lies in the normal Hall `κ'`-subgroup
  `M' = U M_σ` (Theorem C(3)), contradicting `a ∉ U M_σ`.
* `a_{κ'} ≠ 1`: otherwise `a` is `G`-conjugate to `a_κ ∈ K#`, contradicting `a ∉ 𝒞_G(K#)`.
* `a_{κ'} ∈ K*`: `a_{κ'} ∈ M' = U ⋊ M_σ` commutes with `a_κ ∈ K#`; writing `a_{κ'} = u·t`
  (`u ∈ U`, `t ∈ M_σ`), `K`-invariance of `U` (Proposition 14.2(a)) and of `M_σ` plus uniqueness of
  the `U ⋊ M_σ` factorization force `u ∈ C_U(a_κ) = 1` (Theorem A(4)) and `t ∈ C_{M_σ}(a_κ) = K*`
  (Theorem A(5)), so `a_{κ'} = t ∈ K*`.

Hence (after the conjugation) `a = a_κ · a_{κ'} ∈ K·K*` with both factors nontrivial, i.e.
`a ∈ Z − (K ∪ K*) = Ẑ`. -/
theorem a0_minus_a_subset_conj_zTilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ a ∈ A0Set M K \ ASet M U,
      ∃ m ∈ M, ∃ t ∈ S14.zTilde K Kstar, a = m * t * m⁻¹ := by
  classical
  haveI hsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  haveI hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM hUM hK hKstar hU).2.1
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hM'M : (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) ≤ M := sup_le hUM hMσM
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  -- `M' = U ⊔ M_σ` (Theorem C(3) / Lemma 15.1(b)).
  have hM'eq : derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  -- **Helper A**: every `κ(M)'`-element of `M` lies in the normal Hall `κ'`-subgroup `M' = U ⊔ M_σ`.
  -- (`M'` complements the Hall `κ`-subgroup `K` in `M`, so `[M : M'] = |K|` is a `κ`-number;
  -- a `κ'`-element has image of order dividing both `[M : M']` and its own order, hence trivial.)
  have hkappaComplMem : ∀ x : G, x ∈ M → IsPiElement (S14.kappa M)ᶜ x →
      x ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
    intro x hxM hxπ'
    rw [← hM'eq]
    haveI hNnorm : ((derivedInG M).subgroupOf M).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M)
    set N := (derivedInG M).subgroupOf M with hNdef
    set x' : ↥M := ⟨x, hxM⟩ with hx'def
    -- `N.index = |K|` is a `κ`-number (`M'` complements the Hall `κ`-subgroup `K`).
    have hidxκ : ∀ p ∈ N.index.primeFactors, p ∈ S14.kappa M := by
      have hcompl := (typeP_duality hG hM hP hKM hK hKstar).1
      have hidxeq : N.index = Nat.card ↥(K.subgroupOf M) := hcompl.symm.index_eq_card
      rw [hidxeq]; exact hK.1
    -- `orderOf x'` is a `κ'`-number, hence coprime to `N.index`.
    have hordx' : orderOf x' = orderOf x :=
      (orderOf_injective M.subtype M.subtype_injective x').symm
    have hcop : Nat.Coprime (orderOf x') N.index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpdvd
      have hpord : p ∈ (orderOf x).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, hordx' ▸ hpdvd.1, (orderOf_pos x).ne'⟩
      exact (hxπ' p hpord)
        (hidxκ p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.2, Subgroup.index_ne_zero_of_finite⟩))
    -- The image of `x'` in `↥M ⧸ N` has order dividing both `orderOf x'` and `N.index`, hence `1`.
    have hord1 : orderOf (QuotientGroup.mk' N x') = 1 := by
      have h1 : orderOf (QuotientGroup.mk' N x') ∣ orderOf x' :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      have h2 : orderOf (QuotientGroup.mk' N x') ∣ N.index := orderOf_dvd_natCard _
      exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
    have hx'N : x' ∈ N := by
      have h := orderOf_eq_one_iff.mp hord1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp hx'N
  -- **Helper B**: `M' ⊓ (K ⊔ K*) = K*` (direct: `x = k·k* ∈ M'`, `k* ∈ K* ≤ M'`, so `k ∈ K ⊓ M' = 1`).
  have hMeetKKstar : (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) ⊓ (K ⊔ Kstar) = Kstar := by
    refine le_antisymm ?_ (le_inf (hKstarMσ.trans le_sup_right) le_sup_right)
    -- `K` is normal in `K ⊔ K*` (`K*` centralizes it), so an element `x` of `K ⊔ K*` is `a·b`
    -- with `a ∈ K`, `b ∈ K*`.  If also `x ∈ M'`, then `a = x·b⁻¹ ∈ K ⊓ M' = ⊥`, so `x = b ∈ K*`.
    have hKstarC : Kstar ≤ Subgroup.centralizer (K : Set G) := by rw [hKstar]; exact inf_le_right
    have hKnorm : (K ⊔ Kstar : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (hKstarC.trans (Subgroup.centralizer_le_normalizer _))
    haveI : (K.subgroupOf (K ⊔ Kstar)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
    have hsuptop : (K.subgroupOf (K ⊔ Kstar)) ⊔ (Kstar.subgroupOf (K ⊔ Kstar)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hKM'bot : K ⊓ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) = ⊥ := by
      have hcompl := (typeP_duality hG hM hP hKM hK hKstar).1
      have hdisj : Disjoint ((derivedInG M).subgroupOf M) (K.subgroupOf M) := hcompl.disjoint
      rw [← hM'eq, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      have hmemMinf : (⟨y, hKM hy.1⟩ : ↥M) ∈ (K.subgroupOf M) ⊓ ((derivedInG M).subgroupOf M) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hy.1, Subgroup.mem_subgroupOf.mpr hy.2⟩
      rw [disjoint_iff.mp hdisj.symm, Subgroup.mem_bot] at hmemMinf
      rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp hmemMinf
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM', hxKK⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top (⟨x, hxKK⟩ : ↥(K ⊔ Kstar)))
    have haK : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
    have hbKstar : (b : G) ∈ Kstar := Subgroup.mem_subgroupOf.mp hb
    have hab' : (a : G) * (b : G) = x := by have := congrArg Subtype.val hab; simpa using this
    have haM' : (a : G) ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
      have heq : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
      rw [heq]
      exact Subgroup.mul_mem _ hxM'
        (Subgroup.inv_mem _ ((hKstarMσ.trans le_sup_right) hbKstar))
    have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hKM'bot ▸ Subgroup.mem_inf.mpr ⟨haK, haM'⟩)
    rw [← hab', ha1, one_mul]; exact hbKstar
  -- ## Main argument.
  intro a ha
  have haM : a ∈ M := ha.1.1.1
  have hanc : a ∉ conjClassSet (sharpSubgroup K) := ha.1.2
  have haUMσ : a ∉ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    fun hmem => ha.2 ⟨ha.1.1, hmem⟩
  -- `κ`/`κ'`-decomposition `a = a_κ · a_{κ'}`.
  obtain ⟨aκ, aκ', hmul, hcomm, hκ, hκ', hazκ, hazκ'⟩ := exists_isPiElement_mul (S14.kappa M) a
  have hzpaM : Subgroup.zpowers a ≤ M := Subgroup.zpowers_le.mpr haM
  have haκM : aκ ∈ M := hzpaM hazκ
  have haκ'M : aκ' ∈ M := hzpaM hazκ'
  -- `a_κ ≠ 1`: else `a = a_{κ'}` is a `κ'`-element, so `a ∈ M'`, contradicting `a ∉ U M_σ`.
  have haκne : aκ ≠ 1 := by
    intro h
    refine haUMσ ?_
    have : a = aκ' := by rw [← hmul, h, one_mul]
    rw [this]; exact hkappaComplMem aκ' haκ'M hκ'
  -- Conjugate `⟨a_κ⟩` into `K`.
  have hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) ((Subgroup.zpowers aκ).subgroupOf M) := by
    intro p hp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr haκM)).toEquiv,
      Nat.card_zpowers] at hp
    exact hκ p hp
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_isHall_kappa hG hM hKM hK (Subgroup.zpowers_le.mpr haκM) hXpi
  -- `b := w·a·w⁻¹ = b_κ·b_{κ'}` with `b_κ = w·a_κ·w⁻¹ ∈ K`.
  have hbκK : w * aκ * w⁻¹ ∈ K := by
    have hmem : (MulAut.conj w) • aκ ∈ MulAut.conj w • Subgroup.zpowers aκ :=
      Subgroup.smul_mem_pointwise_smul aκ (MulAut.conj w) _ (Subgroup.mem_zpowers aκ)
    have heq : (MulAut.conj w) • aκ = w * aκ * w⁻¹ := rfl
    rw [heq] at hmem; exact hwle hmem
  -- `b_κ' := w·a_{κ'}·w⁻¹ ∈ M'` (conjugate of a `κ'`-element, `M' ◁ M`, `w ∈ M`).
  have hbκ'M' : w * aκ' * w⁻¹ ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
    have hwnorm : w ∈ Subgroup.normalizer (derivedInG M) :=
      OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hwM
    have h1 : aκ' ∈ derivedInG M := by rw [hM'eq]; exact hkappaComplMem aκ' haκ'M hκ'
    have hconjM' : w * aκ' * w⁻¹ ∈ derivedInG M :=
      (Subgroup.mem_normalizer_iff.mp hwnorm aκ').mp h1
    rwa [hM'eq] at hconjM'
  -- `b_κ ≠ 1` and `b_κ' ≠ 1`.
  have hbκne : w * aκ * w⁻¹ ≠ 1 := by
    intro h
    exact haκne (by
      have := congrArg (fun y => w⁻¹ * y * w) h; simpa [mul_assoc] using this)
  have hbκ'ne : w * aκ' * w⁻¹ ≠ 1 := by
    intro h
    -- `b_κ' = 1 ⟹ a_{κ'} = 1 ⟹ a = a_κ`, and `a = w⁻¹·b_κ·w` is `G`-conjugate to `b_κ ∈ K#`.
    have haκ'1 : aκ' = 1 := by
      have h2 := congrArg (fun y => w⁻¹ * y * w) h; simpa [mul_assoc] using h2
    have haaκ : a = aκ := by rw [← hmul, haκ'1, mul_one]
    exact hanc ⟨w * aκ * w⁻¹, ⟨hbκK, hbκne⟩, w⁻¹, by rw [haaκ]; group⟩
  -- `b_κ' ∈ K*`: it lies in `M' ⊓ C_M(b_κ) = M' ⊓ (K ⊔ K*) = K*`.
  have hbκ'comm : Commute (w * aκ * w⁻¹) (w * aκ' * w⁻¹) := by
    show w * aκ * w⁻¹ * (w * aκ' * w⁻¹) = w * aκ' * w⁻¹ * (w * aκ * w⁻¹)
    calc w * aκ * w⁻¹ * (w * aκ' * w⁻¹) = w * (aκ * aκ') * w⁻¹ := by group
      _ = w * (aκ' * aκ) * w⁻¹ := by rw [hcomm.eq]
      _ = w * aκ' * w⁻¹ * (w * aκ * w⁻¹) := by group
  have hbκ'CM : w * aκ' * w⁻¹ ∈ Subgroup.centralizer ({w * aκ * w⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg; subst hg
    exact hbκ'comm.eq
  have hbκ'Kstar : w * aκ' * w⁻¹ ∈ Kstar := by
    have hCMeq : M ⊓ Subgroup.centralizer ({w * aκ * w⁻¹} : Set G) = K ⊔ Kstar :=
      typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU _ hbκK hbκne
    have hbκ'KK : w * aκ' * w⁻¹ ∈ K ⊔ Kstar := by
      rw [← hCMeq, Subgroup.mem_inf]
      exact ⟨hM'M hbκ'M', hbκ'CM⟩
    rw [← hMeetKKstar, Subgroup.mem_inf]
    exact ⟨hbκ'M', hbκ'KK⟩
  -- Assemble: `b := w·a·w⁻¹ = b_κ·b_{κ'} ∈ K·K* ⊆ K ⊔ K*`, and `b ∉ K`, `b ∉ K*`, so `b ∈ Ẑ`.
  refine ⟨w⁻¹, M.inv_mem hwM, w * a * w⁻¹, ?_, by group⟩
  have hbeq : w * a * w⁻¹ = (w * aκ * w⁻¹) * (w * aκ' * w⁻¹) := by
    rw [← hmul]; group
  refine ⟨?_, ?_⟩
  · -- `b ∈ K ⊔ K*`.
    rw [hbeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbκK) (Subgroup.mem_sup_right hbκ'Kstar)
  · -- `b ∉ K ∪ K*`.
    rw [Set.mem_union]
    push_neg
    refine ⟨fun hbK => ?_, fun hbKstar => ?_⟩
    · -- `b ∈ K ⟹ b_κ' = b_κ⁻¹·b ∈ K ⊓ K* = 1`, contra `b_κ' ≠ 1`.
      have hbκ'K : w * aκ' * w⁻¹ ∈ K := by
        have : w * aκ' * w⁻¹ = (w * aκ * w⁻¹)⁻¹ * (w * a * w⁻¹) := by rw [hbeq]; group
        rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbκK) hbK
      exact hbκ'ne (Subgroup.mem_bot.mp
        (kappaHall_inf_Kstar_eq_bot hKM hK hKstar ▸ Subgroup.mem_inf.mpr ⟨hbκ'K, hbκ'Kstar⟩))
    · -- `b ∈ K* ⟹ b_κ = b·b_κ'⁻¹ ∈ K ⊓ K* = 1`, contra `b_κ ≠ 1`.
      have hbκK' : w * aκ * w⁻¹ ∈ Kstar := by
        have : w * aκ * w⁻¹ = (w * a * w⁻¹) * (w * aκ' * w⁻¹)⁻¹ := by rw [hbeq]; group
        rw [this]; exact Subgroup.mul_mem _ hbKstar (Subgroup.inv_mem _ hbκ'Kstar)
      exact hbκne (Subgroup.mem_bot.mp
        (kappaHall_inf_Kstar_eq_bot hKM hK hKstar ▸ Subgroup.mem_inf.mpr ⟨hbκK, hbκK'⟩))

/-- **Matched `κ`-Hall / `(κ∪σ)'`-Hall pair for a type-`P₂` maximal subgroup** (BG `kappa_complement`;
the Frobenius complement `E = K ⋉ U` of Proposition 14.2(a), with `U = E₂E₃` the `M_σ`-complement's
derived subgroup).  There is a `κ(M)`-Hall `K₀` and a nontrivial abelian `(κ(M)∪σ(M))'`-Hall `U₀`,
both `≤ M`, with `K₀ ≤ N_G(U₀)` — since `U₀ = E₂E₃ ◁ E` (`E23_normal`) and `K₀ = E₁ ≤ E`.

This is exactly the matched pair consumed by Corollary 14.12 (`typeP2_neighbor_is_typeF`) via its
`hKNU : K ≤ N(U)` hypothesis.  As all `(κ∪σ)'`-Hall subgroups of `M` are `M`-conjugate, the
arbitrary `U` of Theorem C is `M`-conjugate to `U₀`, which transports `N_G(U) ⊄ M` between them.

Construction: take a §12 `E`-setup (`E = E₁E₂E₃`, `E` a `σ(M)'`-complement of `M_σ`).  Type-`P₂`
excludes the degenerate cases (`κ ∩ τ₃ ≠ ∅`, or `E₂E₃ = 1`) which both make `E` a `κ`-group, hence
`κ(M) = π(M)∖σ(M)` (`kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E`), i.e. type-`P₁`.  In the
remaining case `κ ⊆ τ₁`, `E₁` is the `κ`-Hall (`mem_kappa_of_mem_primeFactors_card_E1`) and
`E₂E₃ = [E : E₁]` is the `(κ∪σ)'`-Hall (its prime divisors avoid `κ` as the index of the `κ`-Hall
`E₁`, and `σ` as `E` is a `σ'`-group). -/
theorem typeP2_exists_matched_kappa_hall_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    ∃ K₀ U₀ : Subgroup G, K₀ ≤ M ∧ U₀ ≤ M ∧ U₀ ≠ ⊥ ∧
      Ch03.IsHallSubgroup (S14.kappa M) (K₀.subgroupOf M) ∧
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) ∧
      IsMulCommutative ↥U₀ ∧
      K₀ ≤ Subgroup.normalizer (U₀ : Set G) := by
  classical
  have hP : S14.IsTypeP M := hP2.1
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  -- `E` is a `σ(M)'`-group.
  have hEσ' : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ E :=
    hsetup.isPiGroup_sigma_compl hG
  -- `κ(M) ∩ τ₃(M) = ∅` (else `E` is a `κ`-group, giving type-`P₁`, contradicting `hP2`).
  have hτ3empty : ¬ (S14.kappa M ∩ tau3 M).Nonempty := by
    rintro ⟨p, hpκ, hpτ3⟩
    have hp : p.Prime := S14.prime_of_mem_kappa hpκ
    obtain ⟨hE3ne, hreg⟩ := S14.E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨_, _, hEprime, _⟩ := OddOrder.BG.Ch3.S13.E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon; push_neg at hcon; exact hreg fun y hy hy1 => hcon y hy hy1
    exact hP2.2 (S14.kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E hG hsetup
      (fun q hq => S14.mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq))
  have hκτ1 : ∀ p ∈ S14.kappa M, p ∈ tau1 M := fun p hpκ =>
    (S14.kappa_subset_tau1_union_tau3 hpκ).resolve_right (fun hpτ3 => hτ3empty ⟨p, hpκ, hpτ3⟩)
  -- `E₁` acts prime/non-regularly on `M_σ`; `E₁` is the `κ`-Hall of `E`, hence of `M`.
  obtain ⟨p₀, hp₀κ⟩ := hP
  obtain ⟨hE1ne, hE1nonreg⟩ := S14.E1_not_regular_of_mem_kappa_tau1 hG hsetup
    (S14.prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
  have hE1prime := OddOrder.BG.Ch3.S13.E1_actsPrime hG hsetup hE1ne
  have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
    S14.Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
  have hE1HallκE : Ch03.IsHallSubgroup (S14.kappa M) (E₁.subgroupOf E) :=
    ⟨fun p hp => S14.mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
      fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
  have hK₀ : Ch03.IsHallSubgroup (S14.kappa M) (E₁.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE S14.kappa_subset_sigmaCompl
  set U₀ : Subgroup G := E₂ ⊔ E₃ with hU₀def
  have hU₀leE : U₀ ≤ E := sup_le hsetup.E₂_le hsetup.E₃_le
  -- `|E| = |E₁| · |U₀|` (the `τ₁` vs `τ₂∪τ₃` factorisation; `E₁ ⊓ U₀ = 1` by coprimality).
  have hc1E : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv
  have hc2E : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₂_le).toEquiv
  have hc3E : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₃_le).toEquiv
  have hcardE : Nat.card ↥E = Nat.card ↥E₁ * Nat.card ↥U₀ := by
    have hEsup : E = E₁ ⊔ E₂ ⊔ E₃ := (subgroupE_basic hG hsetup).2.2.2.2.1.1
    have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG hsetup).2.1.2
    have hcop2 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have := tau1_pRank_eq_one (hsetup.E₁_hall.1 s
        (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      have := tau2_pRank_eq_two (hsetup.E₂_hall.1 s
        (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
      omega
    have hcop3 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      exact not_mem_tau3_of_mem_tau1
        (hsetup.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
        (hsetup.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
    have hE23disj : E₂ ⊓ E₃ = ⊥ := by
      have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
      have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
      have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
        by_contra hnc
        obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
        have := tau2_pRank_eq_two (hsetup.E₂_hall.1 s
          (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
        have := tau3_pRank_eq_one (hsetup.E₃_hall.1 s
          (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
        omega
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2))
    have hcard23 : Nat.card ↥U₀ = Nat.card ↥E₂ * Nat.card ↥E₃ :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint (hsetup.E₂_le.trans hEnormE3) hE23disj
    have hE1_23_disj : E₁ ⊓ U₀ = ⊥ := by
      have hd1 : Nat.card ↥(E₁ ⊓ U₀) ∣ Nat.card ↥E₁ := Subgroup.card_dvd_of_le inf_le_left
      have hd2 : Nat.card ↥(E₁ ⊓ U₀) ∣ Nat.card ↥U₀ := Subgroup.card_dvd_of_le inf_le_right
      have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥U₀) :=
        hcard23 ▸ Nat.Coprime.mul_right hcop2 hcop3
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2))
    have hE1normU0 : E₁ ≤ Subgroup.normalizer (U₀ : Set G) :=
      hsetup.E₁_le.trans (hsetup.E23_normal hG)
    have hsupEq : E₁ ⊔ U₀ = E := by rw [hU₀def, ← sup_assoc, ← hEsup]
    rw [← hsupEq, card_sup_eq_mul_of_le_normalizer_of_disjoint hE1normU0 hE1_23_disj]
  -- index facts `[E:E₁] = |U₀|`, `[E:U₀] = |E₁|`.
  have hidxE1 : (E₁.subgroupOf E).index = Nat.card ↥U₀ := by
    have hmi := Subgroup.card_mul_index (E₁.subgroupOf E)
    rw [hc1E] at hmi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmi, hcardE])
  have hidxU0 : (U₀.subgroupOf E).index = Nat.card ↥E₁ := by
    have hmi := Subgroup.card_mul_index (U₀.subgroupOf E)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀leE).toEquiv] at hmi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmi, hcardE]; ring)
  -- `U₀` is a `(κ∪σ)'`-Hall of `E`, hence of `M`.
  have hU₀HallE : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U₀.subgroupOf E) := by
    constructor
    · intro p hp
      have hpU₀ : p ∈ (Nat.card ↥U₀).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀leE).toEquiv] at hp
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      refine ⟨fun hpκ => hE1HallκE.2 p (by rw [hidxE1]; exact hpU₀) hpκ, ?_⟩
      exact hEσ' p (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hU₀leE) Nat.card_pos.ne' hpU₀)
    · intro p hp
      rw [hidxU0] at hp
      exact fun hc => hc (Set.mem_union_left _ (hE1HallκE.1 p (by rwa [hc1E])))
  have hU₀ : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hU₀leE hU₀HallE
      (fun p hp hpσ => hp (Or.inr hpσ))
  -- `U₀ ≠ ⊥` (else `E = E₁` is a `κ`-Hall covering all `σ'`-primes, giving type-`P₁`).
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hU₀bot
    refine hP2.2 (S14.kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E hG hsetup (fun q hq => ?_))
    rw [hcardE, hU₀bot, Subgroup.card_bot, mul_one] at hq
    exact hE1HallκE.1 q (by rwa [hc1E])
  -- `U₀` abelian (Lemma 15.1(b)).
  have hU₀ab : IsMulCommutative ↥U₀ :=
    (S15.typeP_hall_derived_eq_and_abelian hG hM hsetup.E1_le_M (hU₀leE.trans hsetup.E_le)
      hE1ne hK₀ hU₀).2
  have hK₀NU₀ : E₁ ≤ Subgroup.normalizer (U₀ : Set G) :=
    hsetup.E₁_le.trans (hsetup.E23_normal hG)
  exact ⟨E₁, U₀, hsetup.E1_le_M, hU₀leE.trans hsetup.E_le, hU₀ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩

/-- **BG Theorem C** (mmd L4303): when `K ≠ 1`, `M` has a paired maximal
subgroup `Mstar`, the cyclic product `Z = K Kstar`, a TI set `Z_tilde`, and the
associated type-P duality.

**Faithfulness fixes (2026-06-21, lane F).**

* **Hypotheses `hKM : K ≤ M`, `hUM : U ≤ M`.**  In BG, `K` is the cyclic Hall
  `κ(M)`-subgroup *of* `M` and `U` the Hall `(κ(M) ∪ σ(M))'`-subgroup *of* `M`
  (`M = K U M_σ`), so `K, U ≤ M`.  The `…subgroupOf M` Hall hypotheses constrain
  only `K ⊓ M`, `U ⊓ M`, so they do **not** force `K, U ≤ M`; without them conjunct 7
  (`M' = U ⊔ M_σ`) is false for `U ⊄ M`.  The landed §14/§15 lemmas
  (`typeP_duality`, `typeP_kstar_in_mf`, `typeP_hall_derived_eq_and_abelian`) all
  take these explicitly, so they are added here and threaded through the only
  callers (`theoremII_tame_embedding{,_of_inputs}`).

* **The `∃! Mstar` clause is strengthened to the faithful `typeP_duality` predicate.**
  The previous scaffold pinned `Mstar` only by `maximal ∧ type-P ∧ ¬conj M Mstar ∧
  (type-P₂ M ∨ type-P₂ Mstar)`; since every `G`-conjugate of the partner satisfies
  that predicate (and `N_G(M*) = M* ⊊ G`), the conjunction had **no unique** witness —
  the `∃!` was false as stated.  BG Theorem C(4)-(7),(11) pins `Mstar` by the dual
  Hall datum `K* ≤ M*`, `K*` Hall-`κ(M*)`, `K = M*_σ ⊓ C_G(K*)`, which is exactly
  Theorem 14.7 (`typeP_duality`); that is the predicate used here.  The sole callers
  (`theoremII_tame_embedding_of_inputs`) project out only the TI conjunct, so the
  strengthening does not affect them.

Proof: conjuncts 1,7 from Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian`),
conjuncts 3-6,8 from Corollary 15.6 (`typeP_kstar_in_mf`), conjunct 9 from
Theorem 14.7 (`typeP_duality`).  The residual conjuncts are the genuinely deep
§14/§16 endpoints not yet available as standalone lemmas: conjunct 2 (`N_G(U) ⊄ M`,
BG Theorem C(1) / Corollary 14.12), conjunct 10 (`A_0(M) - A(M)` TI, BG Theorem A(3),(5)
/ Proposition 14.2(d)), conjunct 11 (`U ≠ 1 → |K|` prime ∧ `F(M)` TI, BG Theorem C(10)
= Proposition 14.2(g) + Theorem 15.7(a)), and conjunct 12 (`U = 1 → |K*|` prime, BG
Theorem C(8), pending the `IsTypeP1`-from-`U = ⊥` bridge). -/
theorem theoremC_paired_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKne : K ≠ ⊥) (hKM : K ≤ M) (hUM : U ≤ M)
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
          (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (S14.kappa Mstar) (Kstar.subgroupOf Mstar) ∧
            K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
          IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
          (S14.IsTypeP2 M ∨ S14.IsTypeP2 Mstar) ∧
          (∀ H : Subgroup G, H ∈ maximalSubgroups G → S14.IsTypeP H →
            S14.IsConjugateSubgroup H M ∨ S14.IsConjugateSubgroup H Mstar)) ∧
      IsTISubset (A0Set M K \ ASet M U) M ∧
      (U ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p ∧ S15.FittingIsTI M) ∧
      (U = ⊥ → ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q) := by
  classical
  -- `IsTypeP M` from the nonempty `κ`-Hall factor `K`.
  have hKofne : K.subgroupOf M ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hKne (hd.eq_bot_of_le hKM)
  have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
  -- Conjuncts 1, 7 (Lemma 15.1(b)): `U` abelian and `M' = U ⊔ M_σ`.
  obtain ⟨hM'eq, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU
  -- Conjuncts 3,4,5,8,6 (Corollary 15.6): `K*` nontrivial cyclic `≤ M_F`, `K* ≤ M''`, `M_F` not cyclic.
  obtain ⟨hKsne, hKscyc, hKsMF, hKsdd, hMFnc⟩ := typeP_kstar_in_mf hG hM hP hKM hK hKstar
  -- Conjunct 9 (Theorem 14.7): the unique non-conjugate type-`P` partner `M*`.
  have hdual := (typeP_duality hG hM hP hKM hK hKstar).2.2
  refine ⟨hUab, ?_, hKsne, hKscyc, hKsMF, hMFnc, hM'eq, hKsdd, hdual, ?_, ?_, ?_⟩
  · -- Conjunct 2 (BG Theorem C(1) / Corollary 14.12): `N_G(U) ⊄ M`.
    by_cases hUbot : U = ⊥
    · -- `U = ⊥` (type-`P₁`): `N_G(⊥) = ⊤ ⊄ M` since `M` is a proper (maximal) subgroup.
      subst hUbot
      intro hle
      have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
        intro g _
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp [Subgroup.mem_bot]
      exact (mem_maximalSubgroups.mp hM).1 (top_le_iff.mp (htop.trans hle))
    · -- `U ≠ ⊥` (type-`P₂`): `N_G(U) ⊄ M` is BG Corollary 14.12.  We produce a *matched*
      -- `κ`-Hall / `(κ∪σ)'`-Hall pair `(K₀, U₀)` (with `K₀ ≤ N_G(U₀)`, the hypothesis Corollary
      -- 14.12 consumes), apply 14.12 to get `N_G(U₀) ⊄ M`, then transport along the `M`-conjugacy
      -- `U₀ ~ U` of `(κ∪σ)'`-Hall subgroups.
      have hUne' : U.subgroupOf M ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hd => hUbot (hd.eq_bot_of_le hUM)
      have hP2 : S14.IsTypeP2 M := isTypeP2_of_hall_subgroupOf_ne_bot hP hU hUne'
      obtain ⟨K₀, U₀, hK₀M, hU₀M, hU₀ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩ :=
        typeP2_exists_matched_kappa_hall_pair hG hM hP2
      haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
      haveI : IsSolvable ↥U₀ := solvable_of_solvable_injective (Subgroup.inclusion_injective hU₀M)
      -- a prime `r ∣ |U₀|` and a Sylow (= Hall `{r}`) subgroup `R₀ ≤ U₀`.
      have hU₀card : Nat.card ↥U₀ ≠ 1 := fun h => hU₀ne (Subgroup.card_eq_one.mp h)
      obtain ⟨r, hr⟩ : (Nat.card ↥U₀).primeFactors.Nonempty :=
        Nat.nonempty_primeFactors.mpr
          (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') (Ne.symm hU₀card))
      obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U₀) ({r} : Set ℕ)
      have hR₀sub : ((R'.map U₀.subtype).subgroupOf U₀) = R' :=
        Subgroup.comap_map_eq_self_of_injective U₀.subtype_injective R'
      have hR₀ : Ch03.IsHallSubgroup ({r} : Set ℕ) ((R'.map U₀.subtype).subgroupOf U₀) := by
        rw [hR₀sub]; exact hR'
      have hU₀ab' : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (isMulCommutative_iff.mp hU₀ab (⟨a, ha⟩ : ↥U₀) ⟨b, hb⟩)
      obtain ⟨H, _, _, _, _, hHNU₀⟩ :=
        S14.typeP2_neighbor_is_typeF hG hM hP2 hK₀M hU₀M hK₀ hU₀ hU₀ab' hr (Subgroup.map_subtype_le _)
          hR₀ hK₀NU₀
      -- Transport `N_G(U) ⊄ M` (assumed `≤`, for contradiction) to `N_G(U₀) ≤ M`.
      intro hle
      apply hHNU₀
      obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
        inferInstance hU₀M hUM hU₀ hU
      refine le_trans inf_le_right ?_
      intro n hn
      have hn_fix : MulAut.conj n • U₀ = U₀ := conj_smul_eq_self_of_mem_normalizer hn
      have hwinv : MulAut.conj w⁻¹ • U = U₀ := by
        rw [← hw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have hfix : MulAut.conj (w * n * w⁻¹) • U = U := by
        rw [map_mul, map_mul, mul_smul, mul_smul, hwinv, hn_fix, hw]
      have hwnwM : w * n * w⁻¹ ∈ M := hle (mem_normalizer_of_conj_smul_eq_self hfix)
      have hn' : n = w⁻¹ * (w * n * w⁻¹) * w := by group
      rw [hn']
      exact M.mul_mem (M.mul_mem (M.inv_mem hwM) hwnwM) hwM
  · -- Conjunct 10 (BG Theorem C(9)): `A_0(M) - A(M) = 𝒞_M(Ẑ)` is a TI-subset of `M`.  Reduce to the
    -- structural inclusion `A_0(M) - A(M) ⊆ 𝒞_M(Ẑ)` (`a0_minus_a_subset_conj_zTilde`) plus the
    -- TI-ness of `Ẑ` (`typeP_duality`; `N_G(Ẑ) = K ⊔ K* ≤ M`), via the transport lemma.
    obtain ⟨Mstar, hMstarP⟩ := hdual.exists
    have hZti : OddOrder.GroupTheory.IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) :=
      hMstarP.2.2.2.2.2.1
    have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
    have hZM : (K ⊔ Kstar : Subgroup G) ≤ M :=
      sup_le hKM (hKstarMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    exact hZti.of_subset_conj_of_isTISubset hZM
      (a0_minus_a_subset_conj_zTilde hG hM hP hKM hUM hK hKstar hU)
  · -- Conjunct 11 (BG Theorem C(10) = Prop 14.2(g) + Theorem 15.7(a)): `U ≠ ⊥ → |K|` prime ∧ `F(M)` TI.
    -- `U ≠ ⊥` makes `M` type-`P₂`; `|K| = q` prime is Prop 14.2's type-`P₂` clause.  The
    -- `FittingIsTI M` conjunct (BG Theorem C(10), via Theorem 15.7(a)) is the residual.
    intro hUne
    have hUne' : U.subgroupOf M ≠ ⊥ := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hd => hUne (hd.eq_bot_of_le hUM)
    have hP2 : S14.IsTypeP2 M := isTypeP2_of_hall_subgroupOf_ne_bot hP hU hUne'
    obtain ⟨q, hq, hKq, _⟩ := ((S14.typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.1 hP2).2
    -- `FittingIsTI M` for type-`P₂`: BG Theorem 15.7(a) (`fittingIsTI_of_isTypeP2`).
    exact ⟨q, hq, hKq, S15.fittingIsTI_of_isTypeP2 hG hM hP2⟩
  · -- Conjunct 12 (BG Theorem C(8) = `kstar_card_prime_of_inputs`): `U = ⊥ → |K*|` prime.
    -- `U = ⊥` makes `M` type-`P₁` (`κ(M) = σ(M)'` via the trivial Hall complement), then `|K*|` prime.
    intro hUbot
    have hUbot' : U.subgroupOf M = ⊥ := by simp [hUbot]
    have hP1 : S14.IsTypeP1 M :=
      ⟨hP, kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot hU hUbot'⟩
    exact ⟨Nat.card ↥Kstar, kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar, rfl⟩

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

/-- **General helper (§14-independent, reusable).**  A nontrivial `M`-normal subgroup `H ⊴ M` of a
maximal subgroup `M` of a minimal simple group is self-normalizing in `G`: `N_G(H) = M`.  `H ⊴ M`
gives `M ≤ N_G(H)`; if the inclusion were proper, maximality forces `N_G(H) = G`, so `H ⊴ G`, and
simplicity gives `H ∈ {⊥, ⊤}` — both excluded (`H ≠ ⊥` by hypothesis, `H ≤ M ⊊ G` rules out `⊤`).
Generalizes `normalizer_Msigma_eq_self` (the `H = M_σ` instance) to any nontrivial `M`-normal `H`. -/
theorem normalizer_eq_self_of_subgroupOf_normal_of_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hHle : H ≤ M)
    (hHnorm : (H.subgroupOf M).Normal) (hHne : H ≠ ⊥) :
    Subgroup.normalizer (H : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mp hHnorm
  refine le_antisymm ?_ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : H.Normal :=
      Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
    · exact absurd hbot hHne
    · exact absurd (top_le_iff.mp (htop ▸ hHle)) (mem_maximalSubgroups.mp hM).1

/-- **The Fitting subgroup of a maximal subgroup is self-normalizing**: `N_G(F(M)) = M` for a
maximal `M` of a minimal simple group of odd order.  `F(M)` is normal in `M`
(`fittingInG_subgroupOf_normal`) and nontrivial (`fitting_ne_bot_of_solvable_nontrivial`, as `M` is
a nontrivial — `M_σ ≠ ⊥` — solvable proper subgroup); apply the self-normalizing helper. -/
theorem normalizer_fittingInAmbient_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have hFne : S15.fittingInAmbient M ≠ ⊥ := by
    intro hbot
    refine OddOrder.Isaacs.Ch01.fitting_ne_bot_of_solvable_nontrivial ↥M ?_
    have hmap : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype
        = (⊥ : Subgroup ↥M).map M.subtype := by
      rw [Subgroup.map_bot]; exact hbot
    exact Subgroup.map_injective M.subtype_injective hmap
  exact normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG hM
    (OddOrder.BG.Ch2.S08.fittingInG_le M) (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M) hFne

/-- **Prop 16.1(a) `alternative` disjunct (i), TI case** (Peterfalvi (8.3)(a)): if the Fitting
subgroup `F(M)` of a maximal `M` is `TI` (`FittingIsTI M`), then its nilpotent normal Hall core
`M_F#` is a `TI`-subset with normalizer `N_G(M_F)`.  Since `M_F ≤ F(M)`, an overlap `a, gag⁻¹ ∈ M_F#`
is an overlap in `F(M)#`, so `FittingIsTI` forces `g ∈ N_G(F(M)) = M` (`normalizer_fittingInAmbient_eq_self`);
and `M_F ⊴ M` gives `M ≤ N_G(M_F)`, whence `g ∈ N_G(M_F)`.  This supplies the first disjunct of the
`TypeIData.alternative` field in the `F(M)`-TI case of the `hFI` bridge of `proposition_type_classification`
(the non-TI case is the deeper BG Theorem 15.7(e) trichotomy, `fitting_not_ti_cases`). -/
theorem maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTI : S15.FittingIsTI M) :
    IsTISubset (sharpSubgroup (maxNilpotentNormalHall M))
      (Subgroup.normalizer (maxNilpotentNormalHall M : Set G)) := by
  -- `M_F ≤ F(M)`.
  have hMFleF : maxNilpotentNormalHall M ≤ S15.fittingInAmbient M :=
    S15.maxNilpotentNormalHall_le_fittingInG M
  -- `M ≤ N_G(M_F)` from `M_F ⊴ M`.
  have hMnorm : M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  -- `N_G(F(M)) = M`.
  have hNF : Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M :=
    normalizer_fittingInAmbient_eq_self hG hM
  intro g hg
  obtain ⟨a, haMem, hgaMem⟩ := hg
  rw [sharpSubgroup, Set.mem_diff] at haMem hgaMem
  -- Lift the overlap from `M_F#` to `F(M)#`.
  have ha' : a ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_diff]; exact ⟨hMFleF haMem.1, haMem.2⟩
  have hga' : g * a * g⁻¹ ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_diff]; exact ⟨hMFleF hgaMem.1, hgaMem.2⟩
  -- `FittingIsTI` ⟹ `g ∈ N_G(F(M)) = M ≤ N_G(M_F)`.
  exact hMnorm (hNF ▸ hTI g ⟨a, ha', hga'⟩)

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

/-- **For a type-`P₁` maximal subgroup, `M' = M_σ`** (Coq `BGsection16` `typePfacts`: for
`M ∈ ℳ_𝓟₁`, `Ms = M^(1)`; BG Theorem C(3) collapse with the trivial `(κ ∪ σ)'`-complement).
Since `κ(M) = π(M) ∖ σ(M)` for type `P₁`, the Hall `(κ ∪ σ)'`-subgroup `U` of `M` is trivial
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), so Lemma 15.1(b)'s decomposition `M' = U M_σ`
(`typeP_auxiliary_structure` conjunct 5) collapses to `M' = M_σ`.

This is the structural fact underlying the type-`P₁` half of Proposition 16.1's forward bridges: the
`TypePData` complement `U` (`M' = M_F ⊔ U`) lives inside `M_σ = M'`, and (Coq `typePfacts`)
`U = ⊥ ⟺ M_F = M_σ` distinguishes type V (`U = ⊥`) from types III/IV (`U ≠ ⊥`). -/
theorem isTypeP1_derivedInG_eq_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` and a Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ≠ ⊥` (type `P` has nonempty `κ`).
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `U = ⊥` (type `P₁`): the `(κ ∪ σ)'`-Hall is trivial.
  have hUbot : U = ⊥ := by
    have h0 : U.subgroupOf M = ⊥ := isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot hP1 hU
    rw [← Subgroup.card_eq_one] at h0 ⊢
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h0
  -- Lemma 15.1(b): `M' = U ⊔ M_σ = ⊥ ⊔ M_σ = M_σ`.
  have haux := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  rw [(haux.2.2.2.2.1 hKne).1, hUbot, bot_sup_eq]

/-- **Type-`P₁` `M_F`-internal complement** (the `M' = M_F ⋊ U` factorisation of Peterfalvi (8.4.b)
/ Coq `of_typeP`): for a type-`P₁` maximal subgroup `M` with Hall `κ(M)`-subgroup `K`, the Fitting
kernel `M_F` has a `K`-invariant complement `U` inside `M' = M_σ` (`M_F ⊔ U = M'`, `K ≤ N_G(U)`,
`M_F ⊓ U = ⊥`).

Construction: `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`) is solvable, `M_F ◁ M` is a Hall subgroup
of `M'` (`maxNilpotentNormalHall_isHall`, transferred from `M` via index-divisibility), and `K` (a
`σ'`-group, `κ ⊆ σᶜ`) acts coprimely on the `σ`-group `M'`; the `K`-invariant Schur–Zassenhaus
complement (`exists_aInvariant_complement_within_normal`) supplies `U`.  This discharges the
`hUle`/`hKnorm`/`hDcompl`/`U ≠ ⊥` `TypePData` fields of the FT-critical `hP1neIIIIV` bridge; the
remaining `TypePData` fields (`U` nilpotent `= M'/M_F` nilpotent, the `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`
decomposition) and `N_G(U) ⊆ M` are the deeper Coq `Fcore_structure` content. -/
theorem exists_typeP1_mf_complement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) :
    ∃ U : Subgroup G, U ≤ derivedInG M ∧
      maxNilpotentNormalHall M ⊔ U = derivedInG M ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧
      maxNilpotentNormalHall M ⊓ U = ⊥ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hM'_le_M : M' ≤ M := Subgroup.map_subtype_le _
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  haveI : IsSolvable ↥M' :=
    solvable_of_solvable_injective (f := (Subgroup.inclusion hM'_le_M))
      (Subgroup.inclusion_injective hM'_le_M)
  -- `N = M_F ≤ M' = M_σ`.
  have hN_le : N ≤ M' := by rw [hM'σ]; exact maxNilpotentNormalHall_le_Msigma hG hM
  -- Normalizer facts (`M_F ◁ M`, `M' ◁ M`, `K ≤ M`).
  have hM'_norm_N : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'_le_M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hK_norm_M' : K ≤ Subgroup.normalizer (M' : Set G) :=
    hKM.trans (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M)
  have hK_norm_N : K ≤ Subgroup.normalizer (N : Set G) :=
    hKM.trans (maxNilpotentNormalHall_le_normalizer M)
  -- `M_F` is a Hall subgroup of `M'` (transfer from `M`, since `[M':M_F] ∣ [M:M_F]`).
  have hN_hall : Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M') := by
    obtain ⟨h1, h2⟩ := maxNilpotentNormalHall_isHall M
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv] at hp
    · apply h2 p
      have hmul := Subgroup.relIndex_mul_relIndex N M' M hN_le hM'_le_M
      have hdvd : (N.subgroupOf M').index ∣ (N.subgroupOf M).index :=
        ⟨M'.relIndex M, hmul.symm⟩
      exact Nat.primeFactors_mono hdvd Subgroup.index_ne_zero_of_finite hp
  -- `K` (a `σ'`-group) acts coprimely on `M' = M_σ` (a `σ`-group).
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥M') := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => ?_) (fun p hp => ?_)
    · -- `p ∈ π(K) ⊆ κ ⊆ σᶜ`.
      have hpκ : p ∈ S14.kappa M := by
        apply hK.1
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact S14.kappa_subset_sigmaCompl hpκ
    · -- `p ∈ π(M') = π(M_σ) ⊆ σ`, so `p ∉ σᶜ`.
      simp only [Set.mem_compl_iff, not_not]
      have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv,
          ← hM'σ]
        exact hp
      exact (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).1 p hpMσ
  exact OddOrder.GroupTheory.exists_aInvariant_complement_within_normal
    hN_le hM'_norm_N hK_norm_M' hK_norm_N hN_hall hCop

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-complement is nilpotent** (`M'/M_F` nilpotent, the deferred half
of Corollary 15.5(c)): any complement `U` of `M_F` in `M' = M_σ` is nilpotent.

Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) supplies `Q ⋊ D = M_σ` with `Q ≤ M_F` and `D`
nilpotent; hence `M_σ = M_F · D`, so `M_σ/M_F` is the image of the nilpotent `D` under the
quotient map (`nilpotent_of_surjective`), hence nilpotent.  The complement `U` (`U ⊓ M_F = ⊥`,
`U ⊔ M_F = M_σ`) is isomorphic to `M_σ/M_F` (the restricted quotient map is bijective), so `U` is
nilpotent.  Discharges the `hUnilp` field of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge. -/
theorem isNilpotent_complement_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Group.IsNilpotent ↥U := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hM'σ : derivedInG M = Mσ := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  rw [hM'σ] at hsup
  have hMFMσ : maxNilpotentNormalHall M ≤ Mσ := S15.maxNilpotentNormalHall_le_Msigma hG hM
  have hUMσ : U ≤ Mσ := hsup ▸ le_sup_right
  -- `M̄F = M_F.subgroupOf Mσ` is normal in `↥Mσ`.
  have hMFnormMσ : Mσ ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (OddOrder.BG.Ch3.S10.Msigma_le M).trans (S15.maxNilpotentNormalHall_le_normalizer M)
  haveI hMFbarNorm : ((maxNilpotentNormalHall M).subgroupOf Mσ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFMσ).mpr hMFnormMσ
  -- Theorem 15.2: `Q ⋊ D = M_σ`, `Q ≤ M_F`, `D` nilpotent.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨_, Q, _, D, _, _, _, _, _, _, _, _, _, hQMF, _, hQDcompl, hDnil, _⟩ :=
    S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK rfl
  -- `M̄F ⊔ D̄ = ⊤` in `↥Mσ` (`Q̄ ⊔ D̄ = ⊤`, `Q̄ ≤ M̄F`).
  have hMFDbarTop : (maxNilpotentNormalHall M).subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ :=
    top_le_iff.mp (hQDcompl.sup_eq_top ▸ sup_le_sup_right (Subgroup.subgroupOf_mono Mσ hQMF) _)
  -- `D̄ = D.subgroupOf Mσ` is nilpotent (`≅ D ⊓ Mσ ≤ D`).
  haveI hDnilI : Group.IsNilpotent ↥D := hDnil
  haveI hDbarNil : Group.IsNilpotent ↥(D.subgroupOf Mσ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact nilpotent_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ Mσ ≤ D)).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ Mσ ≤ Mσ)).symm)
  -- `M_σ/M_F` is nilpotent: the quotient map restricts to a surjection `D̄ ↠ M_σ/M_F`.
  haveI hquotNil : Group.IsNilpotent (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) := by
    have hsurj : Function.Surjective
        (((QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp
          (D.subgroupOf Mσ).subtype)) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨m, hm, d, hd, hmd⟩ :=
        Subgroup.mem_sup_of_normal_left.mp (hMFDbarTop ▸ Subgroup.mem_top g)
      refine ⟨⟨d, hd⟩, ?_⟩
      change QuotientGroup.mk (d : ↥Mσ) = QuotientGroup.mk g
      rw [← hmd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, one_mul]
    exact nilpotent_of_surjective _ hsurj
  -- `U ≅ M_σ/M_F`: the restricted quotient map `Ū → M_σ/M_F` is bijective.
  have hŪsup : U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUMσ hMFMσ, sup_comm, hsup, Subgroup.subgroupOf_self]
  set g : ↥(U.subgroupOf Mσ) →* (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) :=
    (QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp (U.subgroupOf Mσ).subtype
    with hgdef
  have hUbarInf : U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ maxNilpotentNormalHall M ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.2, Subgroup.mem_subgroupOf.mp ha.1⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]
    exact Subtype.ext hval
  have hginj : Function.Injective g := by
    intro x y hxy
    have hdiv : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      (QuotientGroup.eq.mp hxy)
    have hxinv : (x : ↥Mσ)⁻¹ ∈ U.subgroupOf Mσ := inv_mem x.2
    have hUmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ U.subgroupOf Mσ := mul_mem hxinv y.2
    have hmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈
        U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      ⟨hUmem, hdiv⟩
    rw [hUbarInf, Subgroup.mem_bot, mul_eq_one_iff_inv_eq, inv_inv] at hmem
    exact Subtype.ext hmem
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ := by
      rw [hŪsup]; exact Subgroup.mem_top z
    obtain ⟨u, hu, m, hm, hum⟩ := Subgroup.mem_sup_of_normal_right.mp hz
    refine ⟨⟨u, hu⟩, ?_⟩
    change QuotientGroup.mk (u : ↥Mσ) = QuotientGroup.mk z
    rw [← hum, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, mul_one]
  haveI : Group.IsNilpotent ↥(U.subgroupOf Mσ) :=
    nilpotent_of_mulEquiv (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩).symm
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUMσ)

/-- **Type-`P₁` `M_F`-complement is a genuine complement in `M'`** (the `hDcompl` `TypePData` field):
any `U` with `M_F ⊔ U = M'` and `M_F ⊓ U = ⊥` gives
`IsComplement' (M_F.subgroupOf M') (U.subgroupOf M')`.

`M_F ◁ M ⊇ M'`, so `M_F.subgroupOf M'` is normal in `↥M'`; with `M_F ⊓ U = ⊥` (disjoint) and
`M_F ⊔ U = M'` (codisjoint, i.e. `⊤` in `↥M'`) the internal product is the whole of `↥M'`.  Card
route: `[M':M_F] = M_F.relIndex M' = M_F.relIndex U = |U|` (second isomorphism theorem
`relIndex_sup_right`, then `M_F ⊓ U = ⊥`), so `|M_F.subgroupOf M'|·|U.subgroupOf M'| = |M'|`, and
`isComplement'_of_card_mul_and_disjoint` concludes.  Purely from `hsup`/`hinf` (no type-`P₁`
hypothesis); discharges the deepest *non*-Fitting `U`-field gated by `exists_typeP1_mf_complement`. -/
theorem isComplement'_mf_complement_of_sup_inf [Finite G] {M U : Subgroup G}
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      (U.subgroupOf (derivedInG M)) := by
  classical
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hNle : N ≤ M' := hsup ▸ le_sup_left
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `N.subgroupOf M'` is normal in `↥M'` (`M' ≤ M ≤ N_G(N)`).
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  haveI hN'norm : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNnormM'
  -- Disjointness and codisjointness in `↥M'`.
  have hdisj : Disjoint (N.subgroupOf M') (U.subgroupOf M') := by
    rw [disjoint_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ N ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]; exact Subtype.ext hval
  have hsup' : N.subgroupOf M' ⊔ U.subgroupOf M' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNle hUle, hsup, Subgroup.subgroupOf_self]
  -- `[M':M_F] = |U.subgroupOf M'|` (second iso theorem, then disjointness).
  have hidx : (N.subgroupOf M').index = Nat.card ↥(U.subgroupOf M') := by
    have key : (N.subgroupOf M').relIndex (U.subgroupOf M') = Nat.card ↥(U.subgroupOf M') := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot]
    rw [← key, ← Subgroup.relIndex_sup_right, sup_comm, hsup', Subgroup.relIndex_top_right]
  have hcard : Nat.card ↥(N.subgroupOf M') * Nat.card ↥(U.subgroupOf M') = Nat.card ↥M' := by
    rw [← hidx, Subgroup.card_mul_index]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

/-- **Coprime inner-induced conjugation is trivial**: if `x` normalizes `N`, `orderOf x` is coprime
to `|N|`, and conjugation by `x` agrees on `N` with conjugation by some `n ∈ N` (so `x` induces an
*inner* automorphism of `N`), then `x` centralizes `N`.

The induced automorphism `φ(x) ∈ Aut(N)` (via `normalizerMonoidHom`) equals `φ(n)`, an inner
automorphism by `n ∈ N`, so `orderOf (φ x)` divides both `orderOf x` and `|N|` (as
`orderOf (φ n) ∣ orderOf n ∣ |N|`); coprimality forces `orderOf (φ x) = 1`, i.e. `φ x = 1`, i.e.
`x ∈ ker (normalizerMonoidHom N) = C_G(N)`.  This is the coprime-action core of the type-`P₁`
`M_F`-internal Fitting decomposition (`F(M) ⊓ U ⊆ C(M_F)`). -/
theorem mem_centralizer_of_inner_conj_of_coprime [Finite G] {N : Subgroup G} {x n : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N)
    (hcop : Nat.Coprime (orderOf x) (Nat.card ↥N))
    (hconj : ∀ y ∈ N, x * y * x⁻¹ = n * y * n⁻¹) :
    x ∈ Subgroup.centralizer (N : Set G) := by
  classical
  have hnN : n ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hn
  set φ := N.normalizerMonoidHom with hφ
  -- `φ ⟨x⟩ = φ ⟨n⟩`: conjugation by `x` and by `n` agree on `N`.
  have hφeq : φ ⟨x, hxN⟩ = φ ⟨n, hnN⟩ := by
    ext y
    exact hconj (y : G) y.2
  -- `orderOf (φ ⟨x⟩) ∣ orderOf x`.
  have hdvd_x : orderOf (φ ⟨x, hxN⟩) ∣ orderOf x := by
    have h1 := orderOf_map_dvd φ ⟨x, hxN⟩
    rwa [Subgroup.orderOf_mk] at h1
  -- `orderOf (φ ⟨x⟩) = orderOf (φ ⟨n⟩) ∣ orderOf n ∣ |N|`.
  have hdvd_N : orderOf (φ ⟨x, hxN⟩) ∣ Nat.card ↥N := by
    rw [hφeq]
    refine (orderOf_map_dvd φ ⟨n, hnN⟩).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard N hn
  -- Coprimality forces the induced automorphism to be trivial.
  have h1 : orderOf (φ ⟨x, hxN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd_x hdvd_N
  have hker : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (N : Set G))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]; exact h1
  rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-internal Fitting decomposition** (BG Corollary 15.5, the
`M' = M_σ` form): for a type-`P₁` maximal `M` with `M_F`-complement `U` in `M' = M_σ`
(`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), the Fitting subgroup is `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.

`F(M)` is nilpotent with `M_F` a normal Hall subgroup (Hall in `M`, hence in `F(M)`) and
`F(M) ≤ M'` (`M` is not type `F`).  By the modular law `F(M) = M_F ⊔ (U ⊓ F(M))` (`M_F ≤ F(M)`,
`F(M) ≤ M' = M_F ⊔ U`).  The crux `U ⊓ F(M) ⊆ C(M_F)`: each `x ∈ U ⊓ F(M)` decomposes (Corollary
15.5, `F(M) = C_M(M_F) · M_F`) as `x = a · b` with `a ∈ C(M_F)`, `b ∈ M_F`, so conjugation by `x`
agrees on `M_F` with conjugation by `b` (inner); as `|U|` is coprime to `|M_F|` (`M_F` Hall),
`mem_centralizer_of_inner_conj_of_coprime` forces `x ∈ C(M_F)`.  Discharges the `hFiteq` (and hence
`hSDfit`, via `M'' ≤ F(M)`) residual of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge. -/
theorem fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set N := maxNilpotentNormalHall M with hNdef
  set M' := derivedInG M with hM'def
  set F := S15.fittingInAmbient M with hFdef
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_Y, -, -, -, _hM''F, hFcent, -, -, -, _hNM', hFle, -⟩ := S15.fitting_decomposition hG hM
  have hFleM' : F ≤ M' := hFle hnotF
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hFM : F ≤ M := hFleM'.trans hM'M
  have hNF : N ≤ F := S15.maxNilpotentNormalHall_le_fittingInG M
  have hNM : N ≤ M := maxNilpotentNormalHall_le M
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `coprime |U| |N|`: `|U| ∣ [M:N]` (complement card), `N` Hall in `M`.
  have hcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hcard0 := (Subgroup.isComplement'_iff_card_mul_and_disjoint.mp hcompl).1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ M' from hNF.trans hFleM')).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv] at hcard0
  -- `hcard0 : |N| * |U| = |M'|`.
  have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥N) := by
    have hHall := maxNilpotentNormalHall_isHall M
    have hci := hHall.coprime_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at hci
    -- `hci : coprime |N| (N.subgroupOf M).index`.
    have hMeq : Nat.card ↥N * (N.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
      exact Subgroup.card_mul_index (N.subgroupOf M)
    have hM'dvdM : Nat.card ↥M' ∣ Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (M'.subgroupOf M)
    have hUdvd : Nat.card ↥U ∣ (N.subgroupOf M).index := by
      have hdvd : Nat.card ↥N * Nat.card ↥U ∣ Nat.card ↥N * (N.subgroupOf M).index := by
        rw [hcard0, hMeq]; exact hM'dvdM
      exact (mul_dvd_mul_iff_left (Nat.card_pos (α := ↥N)).ne').mp hdvd
    exact (hci.coprime_dvd_right hUdvd).symm
  -- `F = N ⊔ (U ⊓ F)` (Dedekind modular law, via `M' = N ⋊ U` and `N ≤ F ≤ M'`).
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  haveI hNnorm' : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNF.trans hFleM')).mpr hNnormM'
  have hmod : F = N ⊔ (U ⊓ F) := by
    apply le_antisymm
    · intro f hf
      have hfM' : f ∈ M' := hFleM' hf
      have hmemsup : (⟨f, hfM'⟩ : ↥M') ∈ N.subgroupOf M' ⊔ U.subgroupOf M' := by
        rw [← Subgroup.subgroupOf_sup (hNF.trans hFleM') hUle, hsup, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, u, hu, hnu⟩ := Subgroup.mem_sup_of_normal_left.mp hmemsup
      have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
      have hfnu : f = (n : G) * (u : G) := by
        have h := congrArg Subtype.val hnu; simpa using h.symm
      have huF : (u : G) ∈ F := by
        rw [show (u : G) = (n : G)⁻¹ * f by rw [hfnu]; group]
        exact F.mul_mem (F.inv_mem (hNF hnN)) hf
      rw [hfnu]
      exact Subgroup.mul_mem_sup hnN (Subgroup.mem_inf.mpr ⟨huU, huF⟩)
    · exact sup_le hNF inf_le_right
  -- Crux: `U ⊓ F ≤ C(N)`.
  have hFUcent : U ⊓ F ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxF⟩ := hx
    have hxM : x ∈ M := hFM hxF
    haveI hNnorm : (N.subgroupOf M).Normal := maxNilpotentNormalHall_subgroupOf_normal M
    have hxFM : (⟨x, hxM⟩ : ↥M) ∈
        (Subgroup.centralizer (N : Set G) ⊓ M).subgroupOf M ⊔ N.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup inf_le_right hNM, Subgroup.mem_subgroupOf]
      show x ∈ Subgroup.centralizer (N : Set G) ⊓ M ⊔ N
      rw [← hFcent]; exact hxF
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hxFM
    have haC : (a : G) ∈ Subgroup.centralizer (N : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
    have hbN : (b : G) ∈ N := Subgroup.mem_subgroupOf.mp hb
    have hxab : x = (a : G) * (b : G) := by
      have h := congrArg (Subtype.val) hab
      simpa using h.symm
    have hxnorm : x ∈ Subgroup.normalizer (N : Set G) := maxNilpotentNormalHall_le_normalizer M hxM
    have hcopx : Nat.Coprime (orderOf x) (Nat.card ↥N) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard U hxU) hcop
    refine mem_centralizer_of_inner_conj_of_coprime hxnorm hbN hcopx ?_
    intro y hy
    have hbyb : (b : G) * y * (b : G)⁻¹ ∈ N := N.mul_mem (N.mul_mem hbN hy) (N.inv_mem hbN)
    have hcomm := (Subgroup.mem_centralizer_iff.mp haC) _ hbyb
    rw [hxab]
    calc (a : G) * (b : G) * y * ((a : G) * (b : G))⁻¹
        = (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (b : G) * y * (b : G)⁻¹ * (a : G) * (a : G)⁻¹ := by rw [← hcomm]
      _ = (b : G) * y * (b : G)⁻¹ := by group
  -- Assemble `F = N ⊔ (U ⊓ C(N))`.
  show F = N ⊔ (U ⊓ Subgroup.centralizer (N : Set G))
  apply le_antisymm
  · rw [hmod]
    exact sup_le_sup_left (le_inf inf_le_left hFUcent) N
  · refine sup_le hNF ?_
    have hle : U ⊓ Subgroup.centralizer (N : Set G) ≤ Subgroup.centralizer (N : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans (hUle.trans hM'M))
    exact hle.trans (le_sup_left.trans_eq hFcent.symm)

/-- **Prop 16.1(a) forward bridge, core** (mmd L4480): a type-`F` maximal `M` (`κ(M) = ∅`, so the
Hall `κ`-subgroup `K = ⊥`) carries the shared Peterfalvi type-`F` structure `TypeFData M`.

This is the `M ∈ ℳ_𝓕 ⟹ Type F` core feeding `proposition_type_classification`'s `hFI` (clause (a),
`mpr`).  The deep fields are read off existing §15 results: `U1_commutative` and `frobenius_HU0`
from `typeP_auxiliary_structure` (mmd 15.1(d)(e)); `H = M_F = M_σ` from Theorem A(8) (`U ≠ ⊥` rules
out the `M_F ≠ M_σ` branch); `M = U M_σ` from Theorem A(3) with `K = ⊥`; `centralizer_le_U1` is
`le_sSup` over `M_F# ⊆ M_σ#`; and `U1_normal` (`⟨C_U(x) | x ∈ M_σ#⟩ ◁ U`) is `U`-conjugation
invariance of the generating set `{U ⊓ C_G(x) : x ∈ M_σ#}` (`conj_smul_centralizerGeneratedBySigma`,
as `M_σ ◁ M`).  **Axiom-clean**: A(3) is `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` and the A(8)
`U = ⊥` exclusion routes through `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (Thm 15.2), not
the `sorry` standalone `theoremA_maximal_structure`; `typeP_auxiliary_structure` is itself clean. -/
theorem typeFData_of_kappa_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  -- Theorem A(3) decomposition `M = K U M_σ` (axiom-clean, via `hKM`/`hUM`; avoids the `sorry`
  -- standalone `theoremA_maximal_structure`).
  have hA3 : M = K ⊔ U ⊔ Mσ := typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU
  -- `M_F = M_σ`: `U ≠ ⊥` excludes the type-`P₁` `U = ⊥` (Theorem A(8), via Thm 15.2).
  have hMFMσ : S15.MF M = Mσ := by
    by_contra hne
    have hUsub : U.subgroupOf M = ⊥ :=
      isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot (isTypeP1_of_mf_ne_msigma hG hM hne) hU
    have h := Subgroup.map_subgroupOf_eq_of_le hUM
    rw [hUsub, Subgroup.map_bot] at h
    exact hUne h.symm
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

/-- **Prop 16.1(a) `TypeFData` construction wrapper**: a BG-local type-`F` maximal `M`
(`S14.IsTypeF M`, i.e. `κ(M) = ∅`) carries the shared Peterfalvi type-`F` structure
`GroupTheory.IsTypeF M`.  Specializes `typeFData_of_kappa_eq_bot` with `K = ⊥` (a `κ`-Hall since
`κ(M) = ∅`) and a `(κ ∪ σ)'`-Hall `U` from Hall's theorem; `U ≠ ⊥` because the `σ`-complement of a
maximal subgroup is nontrivial (`SubgroupESetup.E_ne_bot`: `E = U = ⊥` would force `M = M_σ ≤ M'`,
contradicting `M' ⊊ M`).  This is the type-`F`-structure half of the `hFI` bridge of
`proposition_type_classification`; the `alternative` trichotomy is added in `isTypeI_of_isTypeF`. -/
theorem isTypeF_groupTheory_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hκ : S14.kappa M = ∅ := hF
  -- `K = ⊥` is a `κ(M)`-Hall subgroup (`κ(M) = ∅`).
  have hKhall : Ch03.IsHallSubgroup (S14.kappa M) ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
    intro p _; rw [hκ]; exact Set.notMem_empty p
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `U ≠ ⊥`: the `σ`-complement (`= U`, as `K = ⊥`) of the maximal subgroup is nontrivial.
  obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
    subgroupESetup_of_isHall_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU
  have hUne : U ≠ ⊥ := hsetup.E_ne_bot hG
  exact typeFData_of_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU hUne

/-- **BG Theorem 15.7(e), conjunct A divisibility per prime** (Coq `regZq_dv_q1`): for a type-`F`
datum `td` and a `td.U0`-invariant order-`q` subgroup `Z` of the Frobenius kernel `td.H = M_F`, the
exponent of the complement `U` divides `q - 1`.

`td.U0` acts on `Z` by conjugation (`Subgroup.normalizerMonoidHom`, valid since `td.U0 ≤ N_G(Z)`);
the action is fixed-point-free because `td.H ⋊ td.U0` is a Frobenius group with kernel `td.H ⊇ Z`
(`td.frobenius_HU0.conj_frobenius`).  Hence `IsFrobeniusAction td.U0 Z`, giving
`|U0| ∣ |Z| - 1 = q - 1` (`card_dvd_sub_one_of_isFrobeniusAction`), and
`exp U = exp U0 ∣ |U0| ∣ q - 1` (`td.exponent_eq`, `Group.exponent_dvd_nat_card`).  This is the
divisibility engine of the exponent conjunct (c) of `isTypeI_of_isTypeF`; the per-prime witness `Z`
(order-`q` characteristic subgroup of `M_F`) is supplied separately. -/
theorem typeF_exponent_dvd_sub_one_of_invariant_card [Finite G] {M : Subgroup G}
    (td : OddOrder.GroupTheory.TypeFData M) {Z : Subgroup G} {q : ℕ}
    (hZH : Z ≤ td.H) (hZcard : Nat.card ↥Z = q)
    (hU0NZ : td.U0 ≤ Subgroup.normalizer (Z : Set G)) :
    Monoid.exponent ↥td.U ∣ q - 1 := by
  classical
  -- `G`-level fixed-point-freeness of the conjugation action of `U0` on the kernel `td.H`.
  have hfpf : ∀ u ∈ td.U0, u ≠ 1 → ∀ z ∈ td.H, z ≠ 1 → u * z * u⁻¹ ≠ z := by
    intro u hu hu1 z hz hz1 hconj
    have huK : u ∈ td.H ⊔ td.U0 := (le_sup_right : td.U0 ≤ td.H ⊔ td.U0) hu
    have hzK : z ∈ td.H ⊔ td.U0 := (le_sup_left : td.H ≤ td.H ⊔ td.U0) hz
    refine td.frobenius_HU0.conj_frobenius ⟨u, huK⟩ ((Subgroup.mem_subgroupOf).mpr hu)
      (fun h => hu1 (by simpa using Subtype.ext_iff.mp h)) ⟨z, hzK⟩
      ((Subgroup.mem_subgroupOf).mpr hz)
      (fun h => hz1 (by simpa using Subtype.ext_iff.mp h)) ?_
    exact Subtype.ext (by simpa using hconj)
  -- Conjugation action of `U0` on `Z` (`U0 ≤ N_G(Z)`).
  letI : MulDistribMulAction ↥td.U0 ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hU0NZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥td.U0 ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    refine hfpf (u : G) u.2 (fun h => hu (Subtype.ext h)) (z : G) (hZH z.2)
      (fun h => hz (Subtype.ext h)) ?_
    rw [← h1]; exact congrArg Subtype.val hfix
  have hdvd : Nat.card ↥td.U0 ∣ q - 1 :=
    hZcard ▸ OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rw [← td.exponent_eq]
  exact Group.exponent_dvd_nat_card.trans hdvd

/-- **Prop 16.1(a) forward bridge `hFI`** (Peterfalvi (8.3) / BG Theorem 15.7): a type-`F` maximal
`M` is of type I.  The shared type-`F` structure `TypeFData M` is `isTypeF_groupTheory_of_isTypeF`;
the `TypeIData.alternative` trichotomy splits on whether `F(M)` is `TI`:

* `FittingIsTI M`: disjunct (a), `M_F#` is a `TI`-subset
  (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).
* `¬FittingIsTI M`: disjuncts (b)/(c) (`M_F` abelian of rank 2, or the exponent–cyclic case) come
  from the BG Theorem 15.7(e) trichotomy (`nonTI_Fitting_structure`, Coq `BGsection15`).  This is
  the genuinely deep residual: the `(e)` clause of the landed `fitting_not_ti_cases` is currently
  weakened to the tautology `abelian M_F ∨ ¬abelian M_F`, so the structured rank-2 / exponent
  alternatives are not yet available and the non-TI case must await formalizing 15.7(e). -/
theorem isTypeI_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeI M := by
  obtain ⟨td⟩ := isTypeF_groupTheory_of_isTypeF hG hM hF
  refine ⟨{ typeF := td, alternative := ?_ }⟩
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset.
    refine Or.inl ?_
    rw [td.H_eq]
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI
  · -- `F(M)` not TI ⟹ BG Theorem 15.7(e) trichotomy.  For type `F` the type-`P₁` case (e3) is
    -- excluded, leaving disjunct (b) (`M_F` abelian of rank 2) or (c) (exponent / cyclic-`O_{p'}`).
    rw [td.H_eq]
    -- The non-TI witness: `g ∉ M`, prime `p ∈ σ(M)`, order-`p` `X₁ ≤ M_σ ⊓ M_σ^g`, `rank (M_F ⊓ C_G(X₁)) < 3`.
    obtain ⟨g, p, X₁, hgM, hp, _hpσ, hX₁card, hX₁Mσ, hX₁cMσ, _hCGnotM, hrank3⟩ :=
      exists_inf_conj_fitting_orderP_witness hG hM hTI
    haveI : Fact p.Prime := ⟨hp⟩
    have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hTI
    -- `X₁ ≤ M_F` and `X₁ ≤ M_F^g` (using `M_F = M_σ`).
    have hX₁MF : X₁ ≤ MF M := le_trans hX₁Mσ (le_of_eq hMFeq.symm)
    have hX₁cMF : X₁ ≤ MulAut.conj g • MF M := by rw [hMFeq]; exact hX₁cMσ
    -- `p` is odd (`p ∣ |X₁| ∣ |G|`, `|G|` odd).
    have hpdvdG : p ∣ Nat.card G := hX₁card ▸ Subgroup.card_subgroup_dvd_card X₁
    have hpOdd : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | h
      · exact absurd (even_iff_two_dvd.mpr hpdvdG) (Nat.not_even_iff_odd.mpr hG.odd)
      · exact h
    by_cases habel : IsMulCommutative ↥(MF M)
    · -- abelian `M_F` ⟹ disjunct (b): `rank M_F = 2`.
      refine Or.inr (Or.inl ⟨habel, ?_⟩)
      show rank ↥(MF M) = 2
      have hcommMF : ∀ a b : ↥(MF M), a * b = b * a := isMulCommutative_iff.mp habel
      -- ≤ 2: `M_F` abelian ⟹ `M_F ≤ C_G(X₁)`, so `M_F ⊓ C_G(X₁) = M_F` and `rank M_F < 3`.
      have hMFcentr : MF M ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simpa using congrArg Subtype.val (hcommMF ⟨y, hX₁MF hy⟩ ⟨a, ha⟩)
      have hle3 : rank ↥(MF M) < 3 := (inf_eq_left.mpr hMFcentr) ▸ hrank3
      -- ≥ 2: `O_p(M_F)` is abelian (`≤ M_F`) and noncyclic, so `2 ≤ pRank ≤ rank`.
      have hOpMF : opiCoreInG ({p} : Set ℕ) (MF M) ≤ MF M := opiCoreInG_le {p} (MF M)
      have hcommOp : ∀ x y : ↥(opiCoreInG ({p} : Set ℕ) (MF M)), x * y = y * x := fun x y =>
        Subtype.ext (by simpa using congrArg Subtype.val (hcommMF ⟨(x : G), hOpMF x.2⟩ ⟨(y : G), hOpMF y.2⟩))
      have hOpnc : ¬ IsCyclic ↥(opiCoreInG ({p} : Set ℕ) (MF M)) :=
        not_isCyclic_opiCore_mf_of_orderP_le_conj hG hM hp hgM hX₁card hX₁MF hX₁cMF
      have h2pRank : 2 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (MF M)) p :=
        two_le_pRank_of_comm_isPGroup_not_isCyclic hpOdd hcommOp
          (isPGroup_opiCoreInG_singleton (MF M)) hOpnc
      have hge2 : 2 ≤ rank ↥(MF M) :=
        le_trans (le_trans h2pRank (pRank_le_rank p))
          (rank_le_of_injective (Subgroup.inclusion_injective hOpMF))
      omega
    · -- non-abelian `M_F` ⟹ disjunct (c): the exponent condition (conjunct A, via the Frobenius
      -- divisibility engine + per-prime order-`q` witnesses) and cyclic `O_{p'}(M_F)` (conjunct B).
      refine Or.inr (Or.inr ⟨fun q _hq hqπ => ?_, ?_⟩)
      · -- conjunct A: `exp U ∣ q - 1` for each `q ∈ π(M_F)`.
        obtain ⟨Z, hZMF, hZcard, hMNZ, -⟩ :=
          exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF _hCGnotM
            hrank3 habel _hq hqπ
        exact typeF_exponent_dvd_sub_one_of_invariant_card td (by rw [td.H_eq]; exact hZMF)
          hZcard ((td.U0_le.trans td.U_le).trans hMNZ)
      · -- conjunct B: `∃ p ∈ π(M_F), IsCyclic O_{p'}(M_F)`.
        exact ⟨p, hp,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).1,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).2⟩

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
* the **real Fitting** decomposition `F(M) = H ⊔ (U ⊓ C_M(H))` (Peterfalvi (8.5.a), issue 7008 — the
  LHS is `F(M)`, not `M_F`) and `M'' ≤ F(M)`, with `M_F` noncyclic (`hFiteq`/`hSDfit`/`hHncyc`) come
  from Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) and Corollary 15.6;
* the `M'`-internal complement `M' = H U` with `U` nilpotent and **normalized by `W₁`** (Peterfalvi
  (8.4.b); `U ⊴ M'` would force `U = 1`, issue 7008) — `hDcompl`/`hUnilp`/`hW1norm` — comes from
  Lemma 15.1 / Theorem A.

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
    (hW1norm : W1 ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl :
      Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hHncyc : ¬ IsCyclic ↥H)
    (hSDfit : secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
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
      W1_normalizes_U := hW1norm
      U_nilpotent := hUnilp
      derived_complement := hDcompl
      H_noncyclic := hHncyc
      secondDerived_le_fitting := hSDfit
      fitting_eq := hFiteq
      centralizer_W1 := hCentW1
      normalizer_V := fun X hXne hXV =>
        normalizer_eq_sup_of_isTISubset_of_isCyclic hWcyc hTI hXne hXV }

/-- **The `W₂ = C_{M'}(W₁#)` centralizer law** (BG Theorem C / Peterfalvi (8.4), the `TypePData`
`centralizer_W1` field): for a type-`P` maximal subgroup with cyclic `κ`-Hall `K`, the `M'`-centralizer
of every `k ∈ K#` is exactly `K* = C_{M_σ}(K)`.  Sharpens Theorem A(5) (`C_M(k) = K ⊔ K*`,
`typeP_centralizer_kappaElement_eq`) by intersecting with `M'`: since `K* ≤ M'` and `K ⊓ M' = ⊥`
(the `M = M' ⋊ K` complement has coprime orders, Theorem 14.7(h)), the modular law gives
`M' ⊓ (K ⊔ K*) = K*`.  Discharges the `hCentW1` residual of `typePData_of_isTypeP_of_inputs`. -/
theorem typeP_derivedInG_inf_centralizer_kappaElement_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ K, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = Kstar := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- Theorem 14.7(h): `M = M' ⋊ K` complement (coprime orders), `K ⊔ K*` cyclic ⟹ `K` cyclic.
  obtain ⟨_hMcompl, hcop, _, ⟨_, _, _, _, hWcyc, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
  haveI : IsCyclic ↥(K ⊔ Kstar) := hWcyc
  haveI : IsCyclic ↥K := Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` (for the Theorem A(5) citation).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ⊓ M' = ⊥` (coprime `|K|`, `|M'|`).
  have hcop' : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
    rw [e1, e2] at hcop; exact hcop.symm
  have hKinfM' : K ⊓ derivedInG M = ⊥ :=
    Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop'
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- `K* ≤ M_σ ≤ M'`.
  have hKstarM' : Kstar ≤ derivedInG M := by
    rw [hKstar]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `K ≤ N(K*)`: `K* ≤ C(K)` (from `K* = M_σ ⊓ C(K)`), so `K ≤ C(K*) ≤ N(K*)`.
  have hKsubCK : Kstar ≤ Subgroup.centralizer (K : Set G) := by rw [hKstar]; exact inf_le_right
  have hKN : K ≤ Subgroup.normalizer (Kstar : Set G) := by
    refine le_trans (fun k hk => ?_) (Subgroup.centralizer_le_normalizer (Kstar : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsCK := hKsubCK hs
    rw [Subgroup.mem_centralizer_iff] at hsCK
    exact (hsCK k hk).symm
  -- `M' ⊓ C(x) = M' ⊓ (M ⊓ C(x)) = M' ⊓ (K ⊔ K*)`, then Dedekind ⟹ `= K*`.
  intro x hx hx1
  have hA5 := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU x hx hx1
  have hredux : derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = derivedInG M ⊓ (K ⊔ Kstar) := by
    rw [← hA5, ← inf_assoc, inf_eq_left.mpr hM'M]
  rw [hredux]
  -- Dedekind (`eq_sup_inf_of_le_normalizer`): `H = K* ⊔ (H ⊓ K)`, with `H ⊓ K ≤ M' ⊓ K = ⊥`.
  have hKstarH : Kstar ≤ derivedInG M ⊓ (K ⊔ Kstar) := le_inf hKstarM' le_sup_right
  have hHle : derivedInG M ⊓ (K ⊔ Kstar) ≤ Kstar ⊔ K := by rw [sup_comm]; exact inf_le_right
  have hHinfK : (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    calc (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K ≤ derivedInG M ⊓ K := inf_le_inf_right K inf_le_left
      _ = ⊥ := by rw [inf_comm]; exact hKinfM'
  rw [eq_sup_inf_of_le_normalizer hKN hKstarH hHle, hHinfK, sup_bot_eq]

/-- **Prop 16.1(b)--(d) forward bridge — `TypePData M` from BG-local `IsTypeP M`** (gated-endpoint).
Constructs the shared Peterfalvi type-`P` datum (`TypePData M`) for a type-`P` maximal subgroup with
a nontrivial `κ(M)`-Hall `K`, discharging *twelve* of the eighteen `typePData_of_inputs` fields from
the proven §14/§15 structure and gating only on the genuinely-deep **`M_F`-internal Fitting core**
(BG Corollary 15.5 / Lemma 15.1):

* discharged (`typeP_duality` = Theorem 14.7: `hMcompl`/`hWcyc`/`hTI`; `typeP_kstar_in_mf` = Corollary
  15.6: `hW2ne`/`hW2le`/`hHncyc`; the `W₂ = C_{M'}(W₁#)` centralizer law `hCentW1`
  (`typeP_derivedInG_inf_centralizer_kappaElement_eq` = Theorem A(5) + Dedekind); plus
  `hHeq`/`hHle`/`hW1le`/`hW1ne`), with `W₁ = K`, `W₂ = K*`, `W = K ⊔ K*`, `H = M_F`;
* gated (named residuals): the `M_F`-internal complement `U` (`M' = M_F ⊔ U`, `U` nilpotent and
  normalized by `W₁` — `hUle`/`hKnorm`/`hUnilp`/`hDcompl`; issue 7008: `U ⊴ M'` is unfaithful) and the
  real Fitting decomposition `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hSDfit`/`hFiteq`).

This single construction feeds all three of `hP2II`/`hP1neIIIIV`/`hP1eqV` (types II/III/IV/V bundle a
`TypePData`); the gated residuals are exactly the `M_F`-internal structure not present in
`typeP_auxiliary_structure`'s `M' = U M_σ` decomposition. -/
noncomputable def typePData_of_isTypeP_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hUle : U ≤ derivedInG M)
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G))) :
    TypePData M := by
  classical
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstar
  -- Theorem 14.7 (`typeP_duality`): the `M'`-complement (`.1`), `K ⊔ K*` cyclic and `zTilde` TI
  -- (extracted in `Prop`-valued `have` blocks — the `∃!` witness cannot be eliminated into the
  -- `def`'s `Type`).
  have hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    (typeP_duality hG hM hP hKM hK hKstar).1
  have hWcyc : IsCyclic ↥(K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, h, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  have hTI : IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, _, h, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  -- Corollary 15.6 (`typeP_kstar_in_mf`): `K* ≠ ⊥`, `K* ≤ M_F`, `K* ≤ M''`, `M_F` noncyclic.
  have hk := typeP_kstar_in_mf hG hM hP hKM hK hKstar
  exact typePData_of_inputs (H := maxNilpotentNormalHall M) (U := U) (W1 := K) (W2 := Kstar)
    rfl (maxNilpotentNormalHall_le_derived hG hM) hUle hKM (le_inf hk.2.2.1 hk.2.2.2.1)
    hWcyc hKne hk.1 hMcompl hKnorm hUnilp hDcompl hk.2.2.2.2 hSDfit hFiteq
    (typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar) hTI

open scoped IsMulCommutative in
/-- **`TypePData M` for a type-`P₂` maximal subgroup** — the carrier-constructibility milestone for
Proposition 16.1's forward bridges: *every* type-`P₂` maximal subgroup carries a Peterfalvi
type-`P` datum, `sorry`-free.

Assembled from the matched `κ`-Hall / `(κ ∪ σ)'`-Hall pair
(`typeP2_exists_matched_kappa_hall_pair`, supplying an abelian `U` with `K ≤ N_G(U)`) and the
`M_F`-internal Fitting decomposition (`typeP2_mf_internal_fitting_decomposition`, supplying the
three deep `M'`-complement/Fitting fields `hDcompl`/`hSDfit`/`hFiteq`), fed to the gated-endpoint
constructor `typePData_of_isTypeP_of_inputs`.  This closes the deep `M_F`-internal residuals that
were the linchpin of all three (`hP2II`/`hP1neIIIIV`/`hP1eqV`) forward bridges; the type-`P₂` bridge
`hP2II` now reduces to the type-`II` last mile (`isTypeII_of_typePData`: `N_G(U) ⊄ M` via
Corollary 14.12, and the type-`F` structure of `M'`). -/
noncomputable def typePData_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    TypePData M := by
  classical
  -- Extract the matched pair via `Exists.choose` (the goal `TypePData M` is `Type`-valued, so
  -- `obtain`/`rcases` on the `Prop`-existential cannot eliminate into it).
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hUcomm : IsMulCommutative ↥U := hspec.2.2.2.2.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hspec.2.2.2.2.2.2
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hM'eq := (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  haveI := hUcomm
  have hUnilp : Group.IsNilpotent ↥U := inferInstance
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  exact typePData_of_isTypeP_of_inputs hG hM hP hKM hKne hK hUle hKnorm hUnilp
    hdec.1 hdec.2.1 hdec.2.2

/-- **For a type-`P₁` maximal subgroup with `M_F = M_σ`, `F(M) = M_F`** (the type-V Fitting
collapse, Coq `BGsection16` `typePfacts` `U = 1` branch).  Corollary 15.5(d)
(`fitting_decomposition`) gives `F(M) ≤ M'` since `M` is type `P` (not type `F`); `M' = M_σ`
(`isTypeP1_derivedInG_eq_Msigma`) `= M_F` (hypothesis), and `M_F ≤ F(M)` always
(`maxNilpotentNormalHall_le_fittingInG`), so `F(M) = M_F`.  This discharges the deepest field
(`fitting_eq`) of the type-V `TypePData`, where `U = ⊥` makes `F(M) = M_F ⊔ (⊥ ⊓ C_M(M_F)) = M_F`. -/
theorem fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    S15.fittingInAmbient M = S15.MF M := by
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFle, _⟩ := S15.fitting_decomposition hG hM
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  refine le_antisymm ?_ (S15.maxNilpotentNormalHall_le_fittingInG M)
  exact (hFle hnotF).trans_eq (hM'σ.trans hmf.symm)

open scoped IsMulCommutative in
/-- **`TypePData M` for a type-`P₁` maximal subgroup with `M_F = M_σ`** — the type-V
carrier-constructibility milestone: such a maximal subgroup carries a Peterfalvi type-`P` datum with
*trivial* complement `U = ⊥`, `sorry`-free.

For type `P₁`, `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`); with `M_F = M_σ` this gives
`M' = M_F`, so the `M_F`-internal complement collapses to `U = ⊥` (Coq `typePfacts`:
`M_F = M_σ ⟺ U = 1`).  Every `U`-field of `typePData_of_isTypeP_of_inputs` then trivializes:
`U ⊴ M'` and `K ≤ N_G(U)` are vacuous (`U = ⊥` normal), `hDcompl` is `IsComplement' ⊤ ⊥`
(`M_F.subgroupOf M' = ⊤` since `M' = M_F`), `hSDfit` is `M'' ≤ M' = M_F`, and `hFiteq` is the
type-V Fitting collapse `F(M) = M_F`
(`fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma`).  Feeds the `hP1eqV` bridge:
`isTypeV_of_typePData` reduces type V to the genuinely-deep Peterfalvi (8.8) `alternative`
trichotomy on `M_F`. -/
noncomputable def typePData_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    TypePData M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` (the cyclic `W₁ = K`).  The goal `TypePData M` is `Type`-valued,
  -- so we extract via `Exists.choose` (not `obtain`, which cannot eliminate a `Prop` into `Type`).
  have hKex := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := hKex.choose.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le hKex.choose
  have hKeq : K.subgroupOf M = hKex.choose :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective hKex.choose
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
    rw [hKeq]; exact hKex.choose_spec
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `M' = M_σ = M_F`, `F(M) = M_F`.
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hM'MF : derivedInG M = maxNilpotentNormalHall M := hM'σ.trans hmf.symm
  -- Build with `U = ⊥`; every `U`-field trivializes.
  refine typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK (U := ⊥) bot_le ?_ ?_ ?_ ?_ ?_
  · -- `hKnorm`: `K ≤ N_G(⊥) = ⊤`.
    exact le_top.trans_eq (Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))).symm
  · -- `hUnilp`: `⊥` is nilpotent.
    infer_instance
  · -- `hDcompl`: `IsComplement' ⊤ ⊥` (`M_F.subgroupOf M' = ⊤` since `M' = M_F`).
    rw [Subgroup.bot_subgroupOf,
      Subgroup.subgroupOf_eq_top.mpr (le_of_eq hM'MF)]
    exact Subgroup.isComplement'_top_left.mpr rfl
  · -- `hSDfit`: `M'' ≤ M_F` (`M'' ≤ M' = M_F`).
    rw [bot_inf_eq, sup_bot_eq]
    exact (Subgroup.map_subtype_le _ : secondDerivedInAmbient M ≤ derivedInG M).trans_eq hM'MF
  · -- `hFiteq`: `F(M) = M_F` (type-V Fitting collapse).
    rw [bot_inf_eq, sup_bot_eq]
    exact fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf

/-- **`TypePData M` for a type-`P₁` maximal subgroup with `M_F ≠ M_σ`** — the type III/IV
carrier-constructibility milestone: every such maximal subgroup carries a Peterfalvi type-`P` datum,
`sorry`-free.

The `M_F`-internal complement `U` (`M' = M_σ = M_F ⊔ U`, `M_F ⊓ U = ⊥`, `K ≤ N_G(U)`) is supplied by
`exists_typeP1_mf_complement` (`K`-invariant Schur–Zassenhaus); the four deep `U`/Fitting fields are
the new BG Corollary 15.5 lemmas: `U` is nilpotent (`isNilpotent_complement_of_isTypeP1_mf_ne_msigma`,
`U ≅ M_σ/M_F`), `U` is a genuine `M'`-complement (`isComplement'_mf_complement_of_sup_inf`), and the
Fitting decomposition `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`fittingInAmbient_eq_mf_sup_inf_of_…`, whence
`M'' ≤ F(M)` gives `hSDfit`).  Fed to the gated-endpoint `typePData_of_isTypeP_of_inputs`.  Mirrors
`typePData_of_isTypeP2`; together they construct the type-`P` datum for every non-type-V type-`P`
maximal, leaving the `hP1neIIIIV` bridge gated only on the type III/IV last mile `N_G(U) ⊆ M`. -/
noncomputable def typePData_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    TypePData M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` (`Type`-valued goal: extract via `Exists.choose`).
  have hKex := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := hKex.choose.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le hKex.choose
  have hKeq : K.subgroupOf M = hKex.choose :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective hKex.choose
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hKex.choose_spec
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- The `K`-invariant `M_F`-complement `U` in `M' = M_σ` (`Type`-valued goal: `Exists.choose`).
  have hUex := exists_typeP1_mf_complement hG hM hP1 hKM hK
  set U := hUex.choose with hUdef
  have hUspec := hUex.choose_spec
  have hUle : U ≤ derivedInG M := hUspec.1
  have hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M := hUspec.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hUspec.2.2.1
  have hinf : maxNilpotentNormalHall M ⊓ U = ⊥ := hUspec.2.2.2
  -- The four deep `U`/Fitting fields (BG Corollary 15.5).
  have hUnilp : Group.IsNilpotent ↥U :=
    isNilpotent_complement_of_isTypeP1_mf_ne_msigma hG hM hP1 hne hsup hinf
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hFiteq := fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma hG hM hP1 hsup hinf
  have hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    obtain ⟨_, -, -, -, hM''F, -, -, -, -, -, -, -⟩ := S15.fitting_decomposition hG hM
    rw [← hFiteq]; exact hM''F
  exact typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK hUle hKnorm hUnilp hDcompl hSDfit hFiteq

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

open scoped IsMulCommutative in
/-- **Prop 16.1 forward bridge `hP2II`, reduced to the `M'`-type-`F` residual** — a type-`P₂`
maximal subgroup whose derived subgroup `M'` is of type `F` (with `F(M') = M_F`) is of type II.

This discharges *every* `isTypeII_of_typePData` input that is BG-local for the type-`P₂` case,
leaving exactly the genuinely-deep `M'`-type-`F` structure (`hderF`/`hderfit`, Peterfalvi (8.6)) as
hypotheses.  Notably **the whole `TypePNontrivialCore` (`hcommon`) is lane-local, not lane-b**:
`U ≠ ⊥` from the matched pair, `|W₁| = |K|` prime *and* the `M_σ`-`TI` condition both from
Proposition 14.2(g) (`typeP_structure`, proved) — `M_F = M_σ` for type `P₂`, so its `sharp`-`TI`
*is* the `σ#`-`TI`.  (Correcting the stale belief that `|W₁|` prime needs the lane-b (10.11)
`theorem88_caseB_prime_orders`; that is the *partner* primality, not the type-`P₂` `κ`-Hall's.)
`N_G(U) ⊄ M` is Corollary 14.12 (`typeP2_neighbor_is_typeF`) applied to a Sylow `r`-subgroup of the
matched `U`; the `TypePData` itself is `typePData_of_isTypeP2`.  The single remaining gate for the
`hP2II` bridge of `proposition_type_classification` is thus the type-`F` structure of `M'`. -/
theorem isTypeII_of_isTypeP2_of_derived_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hUcomm : IsMulCommutative ↥U := hspec.2.2.2.2.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hspec.2.2.2.2.2.2
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hM'eq := (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  haveI := hUcomm
  have hUnilp : Group.IsNilpotent ↥U := inferInstance
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  -- Proposition 14.2(g): `|K| = q` prime and `M_σ#` is `TI` (the `M_F#`-`TI` since `M_F = M_σ`).
  obtain ⟨_, q, hqp, hKq, hMσTI⟩ := (S14.typeP_structure hG hM hP hKM hK rfl hU).2.2.2.2.1 hP2
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥U) (⟨b, hb⟩ : ↥U))
  -- `N_G(U) ⊄ M`: Corollary 14.12 applied to a Sylow `r`-subgroup `R ≤ U` (`r ∈ π(U)`, `U ≠ ⊥`).
  have hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M := by
    obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd
      (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
    have hrπU : r ∈ S14.piSet U := Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩
    obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U) ({r} : Set ℕ)
    intro hNU
    obtain ⟨H, _, _, _, _, hHnorm⟩ := S14.typeP2_neighbor_is_typeF hG hM hP2 hKM hUM hK hU hUab
      hrπU (Subgroup.map_subtype_le R')
      (by rw [show (R'.map U.subtype).subgroupOf U = R' from
        Subgroup.comap_map_eq_self_of_injective U.subtype_injective R']; exact hR') hKnorm
    exact hHnorm (le_trans inf_le_right hNU)
  refine isTypeII_of_typePData
    (typePData_of_isTypeP_of_inputs hG hM hP hKM hKne hK hUle hKnorm hUnilp hdec.1 hdec.2.1 hdec.2.2)
    ⟨?_, ?_, ?_⟩ ?_ ?_ hderF ?_
  · show U ≠ ⊥; exact hUne
  · show (Nat.card ↥K).Prime; rw [hKq]; exact hqp
  · rw [hMFMσ]; exact hMσTI
  · show IsMulCommutative ↥U; exact hUcomm
  · show ¬ Subgroup.normalizer (U : Set G) ≤ M; exact hnorm
  · show maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M; exact hderfit

/-- **Prop 16.1 / Peterfalvi (8.6.b II), the `M'`-type-`F` residual (`hderF`), unconditional** — the
derived subgroup `M' = M^{(1)}` of a type-`P₂` maximal `M` is itself of type `F`.

Structurally `M' = M_σ ⋊ U` is the type-`F`-shaped `M_σ ⋊ (complement)` inside `M` — exactly as the
type-`F` *maximal* of `typeFData_of_kappa_eq_bot` is `M = M_σ ⋊ U` — so the *same* data assemble: the
`M_σ ⋊ U` complement (`typeP2_mf_internal_fitting_decomposition`), the abelian inertia `U₁` and the
Frobenius factor `M_σ ⋊ U₀` (Lemma 15.1(d)(e), `typeP_auxiliary_structure`), and the crucial `F`-core
identity `(M')_F = M_σ = M_F` (`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`).  This last
identity is the Coq `defM'F` step (`Fcore_max` + Hall transitivity): it needs **no** `τ₂(M) = ∅`
hypothesis (which is in fact false for some type-`P₂` `M`, cf. Corollary 15.9). -/
theorem isTypeF_derivedInG_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K]
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF (derivedInG M) := by
  classical
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hMFM' : maxNilpotentNormalHall M = maxNilpotentNormalHall (derivedInG M) :=
    hMFMσ.trans (maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK).symm
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  obtain ⟨_, _, _, _, hconj5, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := maxNilpotentNormalHall M
    U := U
    U1 := centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := hMFM'
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := maxNilpotentNormalHall_le_derived hG hM
    U_le := hUle
    U1_le := by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left
    U0_le := hU0U
    complement := hdec.1
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      exact ⟨maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := by rw [hMFMσ, sup_comm]; exact hfrob }⟩
  · -- `U1_normal`: `U`-conjugation permutes the generators `C_U(x)` of `centralizerGeneratedBySigma`.
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]

/-- **BG Proposition 16.1(b) forward bridge `hP2II`, complete and unconditional** — *every*
type-`P₂` maximal subgroup is of type II.  The two residuals of
`isTypeII_of_isTypeP2_of_derived_typeF` are discharged: `hderF` by `isTypeF_derivedInG_of_isTypeP2`,
and `hderfit` (`(M')_F = M_F`, both `= M_σ`) by
`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`.  No `τ₂(M) = ∅` gate (the earlier
reduction to BG Theorem 15.8 was unnecessary — and `τ₂(M) = ∅` is false for some type-`P₂` `M`,
cf. Corollary 15.9). -/
theorem isTypeII_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  -- `K` cyclic (Theorem A(2) / Lemma 15.1(b), `typeP_auxiliary_structure` conjunct 2).
  obtain ⟨_, hKcyc, _⟩ := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  haveI := hKcyc
  -- `hderfit`: `(M')_F = M_F` (both `= M_σ`).
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M := by
    rw [maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK, hMFMσ]
  -- `hderF`: `M'` is of type `F`.
  have hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M) :=
    isTypeF_derivedInG_of_isTypeP2 hG hM hP2 hKM hUM hKne hK hU hUne
  exact isTypeII_of_isTypeP2_of_derived_typeF hG hM hP2 hderF hderfit

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

/-- **`M_σ`-centralizer of a `κ`-element is `K*`** (the prime-action constancy of fixed points): for
a type-`P` maximal `M` with Hall `κ`-subgroup `K` and `K* = M_σ ⊓ C(K)`, every `k ∈ K#` has
`C_{M_σ}(k) = K*`.  `K` acts *primely* on `M_σ` (Proposition 14.2, `typeP_structure` conjunct 1,
`ActsPrimeOn (M_σ) K`), so the fixed subgroup `C_{M_σ}(k) = fixedByElement (M_σ) k` equals
`fixedBy (M_σ) K = M_σ ⊓ C(K) = K*` for every nonidentity `k ∈ K`. -/
theorem centralizer_msigma_kappaElement_eq_kstar [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] {k : G} (hk : k ∈ K) (hk1 : k ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({k} : Set G) = Kstar := by
  have hprime : OddOrder.BG.Ch3.S13.ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K :=
    (S14.typeP_structure hG hM hP hKM hK hKstar hU).1
  -- `fixedByElement (M_σ) k = fixedBy (M_σ) K`, both defeq to the centralizer forms.
  have heq := hprime k hk hk1
  rw [hKstar]
  exact heq

/-- **`|K| ∣ p - 1` from `K` acting Frobenius on an `M`-normal order-`p` subgroup** (the
divisibility engine for type-V disjunct (e2), Coq `regZq_dv_q1`): if the Hall `κ`-subgroup `K`
normalizes an order-`p` subgroup `Z ≤ M_σ` with `Z ⊓ K* = ⊥`, then `K` acts on `Z` as a Frobenius
group — every `k ∈ K#` centralizes only `1` in `Z`, since `C_{M_σ}(k) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`) and `Z ⊓ K* = ⊥` — so `card_dvd_sub_one_of_isFrobeniusAction`
gives `|K| ∣ |Z| - 1 = p - 1`. -/
theorem kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Z : Subgroup G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    (hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M) (hZcard : Nat.card ↥Z = p)
    (hKNZ : K ≤ Subgroup.normalizer (Z : Set G)) (hZK : Z ⊓ Kstar = ⊥) :
    Nat.card ↥K ∣ p - 1 := by
  classical
  letI : MulDistribMulAction ↥K ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hKNZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥K ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    have hconj : (u : G) * (z : G) * (u : G)⁻¹ = (z : G) := by
      rw [← h1]; exact congrArg Subtype.val hfix
    have hcomm : (u : G) * (z : G) = (z : G) * (u : G) := mul_inv_eq_iff_eq_mul.mp hconj
    have huK1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hzKstar : (z : G) ∈ Kstar := by
      rw [← centralizer_msigma_kappaElement_eq_kstar hG hM hP hKM hK hKstar hU u.2 huK1]
      exact Subgroup.mem_inf.mpr ⟨hZMσ z.2,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx; exact hcomm)⟩
    have hz1 : (z : G) = 1 := by
      have hmem : (z : G) ∈ Z ⊓ Kstar := Subgroup.mem_inf.mpr ⟨z.2, hzKstar⟩
      rw [hZK, Subgroup.mem_bot] at hmem; exact hmem
    exact hz (Subtype.ext hz1)
  have hdvd := OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rwa [hZcard] at hdvd

/-- **`K` acts faithfully on `P = O_p(M_F)` in the type-V Singer case** (Coq `defKs`/`defZP`:
`K* = Z` forces `C_K(P) = 1`).  For a type-`P₁` maximal `M` with Hall `κ`-subgroup `K`,
`K* = M_σ ⊓ C(K)`, and an order-`p` subgroup `Z ≤ K*` with `X₁ ⊄ Z` (the non-TI witness `X₁` of order
`p`, `X₁ ≤ M_F`), the centralizer of `P` in `K` is trivial.

A nonidentity `x ∈ K ⊓ C_G(P)` centralizes `P ⊇ X₁`, so `X₁ ≤ M_σ ⊓ C_G(x) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`).  But `K* = Z`: `|K*|` is prime
(`kstar_card_prime_of_inputs`), `Z ≤ K*`, and `|Z| = p`, so `|K*| = p` and `Z = K*`.  Hence
`X₁ ≤ Z`, contradicting `X₁ ⊄ Z`.  This is the faithfulness input `K ⊓ C_G(P) = ⊥` to
`pRank_opiCore_le_two_of_kappaHall` (`rPle2`) for the type-V disjunct-3 (Singer/`SL₂(p)`) case. -/
theorem kappaHall_inf_centralizer_opiCore_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    {p : ℕ} {X₁ Z : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hZKstar : Z ≤ Kstar) (hZcard : Nat.card ↥Z = p) (hX₁notZ : ¬ X₁ ≤ Z) :
    K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  -- `K* = Z`: `|K*|` prime, `Z ≤ K*`, `|Z| = p`.
  have hKstarPrime : (Nat.card ↥Kstar).Prime :=
    S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have hKstarEqZ : Kstar = Z := by
    have hdvd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
    have hcard : Nat.card ↥Kstar = p := ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hdvd).symm
    exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hcard.trans hZcard.symm))).symm
  -- `X₁ ≤ P` (`p`-subgroup of the nilpotent `M_F`).
  haveI hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- A nonidentity `x ∈ K ⊓ C_G(P)` forces `X₁ ≤ K* = Z`, contradicting `X₁ ⊄ Z`.
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxK, hxCP⟩ := Subgroup.mem_inf.mp hx
  refine hX₁notZ ?_
  rw [← hKstarEqZ,
    ← centralizer_msigma_kappaElement_eq_kstar hG hM hP1.1 hKM hK hKstar hU hxK hx1]
  refine le_inf (hX₁MF.trans (S15.maxNilpotentNormalHall_le_Msigma hG hM)) (fun g hg => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Subgroup.mem_centralizer_iff.mp hxCP g (hX₁P hg)).symm

/-- **`M_F` is non-abelian for a type-V maximal** (the abelian-`H` exclusion of Coq
`nonTI_Fitting_structure`, the `P1maxM` branch): a type-`P₁` maximal subgroup `M` with `M_F = M_σ`
has non-abelian `M_F`.  The type-`P` datum's `W₂ = C_{M'}(W₁#)` is nontrivial (`W2_nontrivial`) and
lies in `M''` (`W2_le`); but `M' = M_σ = M_F` here, so `M'' = (M_F)'`, whence `(M_F)' ⊇ W₂ ≠ ⊥`,
i.e. `M_F` is non-abelian.  (Equivalently: were `M_F` abelian, `M'' = ⊥` would force `W₂ = ⊥`.) -/
theorem not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    ¬ IsMulCommutative ↥(S15.MF M) := by
  intro hab
  haveI := hab
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  -- `M' = M_σ = M_F`, so `M'' = (M_F)' = ⊥` (were `M_F` abelian).
  have hM'MF : derivedInG M = S15.MF M :=
    (isTypeP1_derivedInG_eq_Msigma hG hM hP1).trans hmf.symm
  have hM''bot : secondDerivedInAmbient M = ⊥ := by
    rw [secondDerivedInAmbient, hM'MF,
      show derivedInG (S15.MF M) = (commutator ↥(S15.MF M)).map (S15.MF M).subtype from rfl,
      commutator_eq_bot, Subgroup.map_bot]
  exact data.W2_nontrivial (le_bot_iff.mp ((data.W2_le.trans inf_le_right).trans hM''bot.le))

/-- **Common part of the Peterfalvi (8.8) trichotomy for type V** (Coq `cycHp'` + non-TI witness):
a type-`P₁` maximal `M` with `M_F = M_σ` and `¬FittingIsTI M` has a prime `p ∈ π(M_F)` with cyclic
`p'`-core `O_{p'}(M_F)` — the shared conclusion of disjuncts `(e2)`/`(e3)` of BG Theorem 15.7(e).
`M_F` is non-abelian (`not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma`); the non-TI witness
`X₁ ≤ M_σ = M_F` with `C_G(X₁) ⊄ M` (`exists_inf_conj_fitting_orderP_witness`) then feeds the
`cycHp'` building block `typeF_nonabelian_cyclic_opiCore_compl`.  The remaining `|W₁| ∣ p ∓ 1`
divisibility (which distinguishes disjunct 2 from disjunct 3) is the genuinely-deep `W₁`-action
residual. -/
theorem exists_prime_cyclic_opiCore_compl_of_isTypeV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    (hnotTI : ¬ S15.FittingIsTI M) :
    ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥(S15.MF M)).primeFactors ∧
      IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (S15.MF M)) := by
  have hnab := not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf
  obtain ⟨g, p, X₁, -, hp, -, hX₁card, hX₁Mσ, -, hCGnotM, -⟩ :=
    S15.exists_inf_conj_fitting_orderP_witness hG hM hnotTI
  -- `X₁ ≤ M_σ = M_F` (`mf_eq_msigma_of_not_fittingIsTI`).
  have hX₁MF : X₁ ≤ S15.MF M := by
    rw [S15.mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI]; exact hX₁Mσ
  obtain ⟨hpπ, hcyc⟩ :=
    S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab
  exact ⟨p, hp, hpπ, hcyc⟩

/-- **`O_p(M_F)` is narrow once its `p`-rank reaches 3** (BG Theorem 15.7(e), the narrow input for
the `r(P) ≤ 2` step of the type-V Singer case).  For `P = O_p(M_F)` with `pRank P ≥ 3`, the order-`p`
non-TI witness `X₁ ≤ M_F` whose `M_F`-centralizer has rank `< 3` (the `E1X_facts` rank bound from
`exists_inf_conj_fitting_orderP_witness`) realizes the narrow characterization
`narrow_iff_exists_card_prime_centralizer_pRank_le_two`: `X₁ ≤ P`
(`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`) and `C_P(X₁) = (C_G(X₁)).subgroupOf P` has
`pRank ≤ rank(M_F ⊓ C_G(X₁)) < 3` (it embeds into `M_F ⊓ C_G(X₁)` as `P ≤ M_F`).  No Sylow/`β`
plumbing is needed: the `pRank ≥ 3` hypothesis is exactly the contradiction branch of `r(P) ≤ 2`. -/
theorem isNarrow_opiCore_of_three_le_pRank [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (h3 : 3 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p) :
    OddOrder.GroupTheory.IsNarrow p ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPMF : P ≤ S15.MF M := opiCoreInG_le _ _
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  haveI hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  rw [OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two hpodd hPpg h3]
  refine ⟨X₁.subgroupOf P,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁P).toEquiv).trans hX₁card, ?_⟩
  -- `C_{↥P}(X₁.subgroupOf P) = (C_G(X₁)).subgroupOf P`.
  have himg_set : (P.subtype : ↥P → G) '' (↑(X₁.subgroupOf P) : Set ↥P) = (X₁ : Set G) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hX₁P]
  have hcent : Subgroup.centralizer (↑(X₁.subgroupOf P) : Set ↥P)
      = (Subgroup.centralizer (X₁ : Set G)).subgroupOf P := by
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, himg_set]
  rw [hcent]
  -- `↥((C_G(X₁)).subgroupOf P)` embeds into `M_F ⊓ C_G(X₁)` (image is `P ⊓ C_G(X₁) ≤ M_F ⊓ C_G(X₁)`).
  have hsub : ((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype
      ≤ S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G) := by
    simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact le_inf (inf_le_left.trans hPMF) inf_le_right
  calc pRank ↥((Subgroup.centralizer (X₁ : Set G)).subgroupOf P) p
      ≤ pRank ↥(((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).injective
    _ ≤ pRank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) p :=
        pRank_le_of_injective (Subgroup.inclusion_injective hsub)
    _ ≤ rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := pRank_le_rank p
    _ ≤ 2 := by omega

/-- **`r(O_p(M_F)) ≤ 2` for the type-V Singer case** (BG Theorem 15.7(e), Coq `rPle2`).  A
`κ`-Hall `K` (cyclic, `p'`, normalizing `P = O_p(M_F)`) that acts *faithfully* on `P`
(`K ⊓ C_G(P) = ⊥`) with `|K| ∤ p − 1` forces `pRank P ≤ 2`: were `pRank P ≥ 3`, `P` would be narrow
(`isNarrow_opiCore_of_three_le_pRank`), and BG Theorem 5.5(b) (`solvableAut_of_narrow`, applied to
the faithful `φ : K → MulAut P`) would give that every `p'`-element of `K` has order dividing
`p − 1`; the cyclic generator of `K` then yields `|K| ∣ p − 1`, contradicting `|K| ∤ p − 1`.

The faithfulness `K ⊓ C_G(P) = ⊥` is the `defZP`/`Kstar = Z(P)` content of the Singer case
(supplied separately). -/
theorem pRank_opiCore_le_two_of_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ K : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    [IsCyclic ↥K] (hKp' : ¬ p ∣ Nat.card ↥K)
    (hKnormP : K ≤ Subgroup.normalizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G))
    (hKfaithful : K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥)
    (hKp1 : ¬ Nat.card ↥K ∣ p - 1) :
    pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  haveI : IsSolvable ↥K := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
    refine isSolvable_of_comm fun a b => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm]
  by_contra hcon
  rw [not_le] at hcon
  have h3 : 3 ≤ pRank ↥P p := hcon
  have hPnarrow : OddOrder.GroupTheory.IsNarrow p ↥P :=
    isNarrow_opiCore_of_three_le_pRank hG hM hp hpodd hX₁card hX₁MF hrank3 h3
  -- The faithful conjugation action `φ : ↥K → MulAut ↥P`.
  set φ : ↥K →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKnormP) with hφdef
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hφdef, MonoidHom.comp_apply] at hk
    have hkmem : (Subgroup.inclusion hKnormP k) ∈ (Subgroup.normalizerMonoidHom P).ker :=
      MonoidHom.mem_ker.mpr hk
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hkmem
    have hmem : (k : G) ∈ K ⊓ Subgroup.centralizer (↑P : Set G) :=
      Subgroup.mem_inf.mpr ⟨k.2, hkmem⟩
    rw [hKfaithful, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  haveI hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  obtain ⟨-, -, hb, -⟩ :=
    OddOrder.BG.Ch1.S05.solvableAut_of_narrow hpodd hPpg hPnarrow φ hφinj hKodd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
  have hKcard : Nat.card ↥K = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hgcop : Nat.Coprime (orderOf g) p := hKcard ▸ (hp.coprime_iff_not_dvd.mpr hKp').symm
  have hgdvd : orderOf g ∣ p - 1 := hb h3 g hgcop
  rw [← hKcard] at hgdvd
  exact hKp1 hgdvd

/-- **`|O_p(M_F)| = p³` in the type-V Singer case** (BG Theorem 15.7(e), Coq `dimP`/`oP`): the order
of `P = O_p(M_F)` is `p³`.  The inputs `r(P) ≤ 2` (`hrPle2`, the `rPle2` step, discharged via the
faithfulness brick `kappaHall_inf_centralizer_opiCore_eq_bot` + `pRank_opiCore_le_two_of_kappaHall`)
and `P` non-abelian (`hPnab`) are in hand.

The remaining content is the **Blackburn rank-2 Sylow central-product structure**
(`mFT_rank2_Sylow_cprod`, Coq §10.7b; Lean `S10.sylow_structure_b`, currently `private`):
`P = O_p(M_F)` is a Sylow `p`-subgroup of `G` (Coq `sylP_G`: `O_p(M_F)` is Sylow of the nilpotent
`M_F = M_σ`, and `M_σ` is the `σ`-Hall with `p ∈ σ`), so it is a central product `S ∘ C` of a
nonabelian `p³` `S = Ω₁` with cyclic `C`; with `Z(P) = K* = Ω₁(Z(P))` of order `p` (Coq
`defZP`/`oZ0`, needing the coprime-action fact `coprime_odd_faithful_Ohm1`) the cyclic factor `C`
collapses into `Z(P)`, leaving `|P| = |S| = p³`.  This is the genuinely-deep residual of disjunct 3
(issue 8015); `r(P) ≤ 2` and the non-abelian hypothesis are the discharged prerequisites. -/
theorem card_opiCore_eq_prime_cube_singer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    {p : ℕ} (hp : p.Prime) (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hpπ : p ∈ (Nat.card ↥(S15.MF M)).primeFactors)
    (hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2)
    (hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) :
    Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 := by
  sorry

/-- **Prop 16.1 forward bridge `hP1eqV`, reduced to the Peterfalvi (8.8) trichotomy residual** — a
type-`P₁` maximal subgroup with `M_F = M_σ` is of type V.

The type-`P` datum is the fully-constructed `typePData_of_isTypeP1_mf_eq_msigma` (`U = ⊥`,
`sorry`-free — the type-V carrier-constructibility milestone); `isTypeV_of_typePData` then reduces to
the `alternative` disjunction on `H = M_F`.  As for the type-`F` bridge `isTypeI_of_isTypeF`, the
`FittingIsTI M` case is discharged directly (disjunct (a): `M_F#` is a `TI`-subset, via
`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).

The sole remaining residual is thus the genuinely-deep **`¬FittingIsTI` case of Peterfalvi (8.8) /
BG Theorem 15.7(d)(e)** (Coq `BGsection15` `nonTI_Fitting_structure`): either `M_F` abelian of rank 2
with `|W₁| ∣ p - 1`, or `O_p(M_F)` of order `p³` with `|W₁| ∣ p + 1` (the Suzuki/`SL₂`-type
structures).  Unlike the type-`F` trichotomy (`isTypeI_of_isTypeF`, whose non-TI cases are `rank = 2`
/ `exp U ∣ p - 1`), the type-V alternatives carry the `W₁`-Frobenius divisibilities `|W₁| ∣ p ∓ 1`,
which need the `W₁`-action analysis of (8.8) not yet formalized.

(`hP1neIIIIV`, the sibling `M_F ≠ M_σ ⟹ III/IV` bridge, needs no trichotomy but instead the full
nilpotent `M_F`-complement `U ≠ ⊥`, gated on `M'/M_F` nilpotent.) -/
theorem isTypeV_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeV M := by
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  refine isTypeV_of_typePData data rfl ?_
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset (same as the type-`F` bridge).
    exact Or.inl (maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI)
  · -- `¬FittingIsTI` ⟹ disjuncts (e2)/(e3).  The non-TI witness `X₁` (order `p`, `C_G(X₁) ⊄ M`),
    -- the cyclic `O_{p'}(M_F)` (Coq `cycHp'`), and the `M`-normal order-`p` `Z = Ω₁(Z(O_p(M_F)))`
    -- (Coq `oZ`, `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`).
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    have hnab := not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf
    obtain ⟨g, p, X₁, -, hp, hpσ, hX₁card, hX₁Mσ, -, hCGnotM, hrank3⟩ :=
      S15.exists_inf_conj_fitting_orderP_witness hG hM hTI
    haveI : Fact p.Prime := ⟨hp⟩
    have hX₁MF : X₁ ≤ S15.MF M := by
      rw [S15.mf_eq_msigma_of_not_fittingIsTI hG hM hTI]; exact hX₁Mσ
    obtain ⟨hpπ, hcyc⟩ :=
      S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab
    have hHMF : data.H = S15.MF M := data.H_eq
    -- Reconstruct a Hall `κ`-subgroup `K` (cyclic), the trivial `(κ ∪ σ)'`-Hall `U = ⊥`, and `K*`.
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro q hq
      simp only [Set.mem_compl_iff, not_not]
      by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hqσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hq, hqσ⟩)
    haveI hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    -- `|W₁| = [M:M'] = |K|`.
    have hW1K : Nat.card ↥data.W1 = Nat.card ↥K :=
      (data.card_W1_eq_derived_index).trans
        (card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK).symm
    -- The `M`-normal order-`p` `Z ≤ M_F = M_σ` normalized by `K`.
    obtain ⟨Z, hZMF, hZcard, hZnorm, hX₁notZ⟩ :=
      S15.exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF hCGnotM
        hrank3 hnab (q := p) hp hpπ
    have hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M := hmf ▸ hZMF
    have hKNZ : K ≤ Subgroup.normalizer (Z : Set G) := hKM.trans hZnorm
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- (e2) vs (e3) dichotomy on the Frobenius divisibility `|W₁| ∣ p − 1` (matching Coq's
    -- `Ks = Z₀ → |K| ∣ p-1` split): if it holds, disjunct (e2) directly; otherwise the genuine
    -- Singer/`SL₂(p)` case (e3), where the `K`-action on `Z` is *not* Frobenius so `Z ⊓ K* ≠ ⊥`,
    -- i.e. `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`).
    by_cases hdvd : Nat.card ↥data.W1 ∣ p - 1
    · -- (e2): `|W₁| ∣ p − 1` directly (the cyclic `O_{p'}(M_F)` is `hcyc`).
      exact Or.inr (Or.inl ⟨p, hp, hHMF ▸ hpπ, hdvd, hHMF ▸ hcyc⟩)
    · -- (e3): `¬(|W₁| ∣ p − 1)`, the genuine Singer case.  Then `Z ⊓ K* ≠ ⊥` (else the Frobenius
      -- engine `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot` would give `|K| = |W₁| ∣ p − 1`),
      -- hence `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`/`defZP`/`rPle2`/`oZ0`, the genuinely-deep residual).
      have hZK : Z ⊓ Kstar ≠ ⊥ := fun h => hdvd
        (hW1K ▸ kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot hG hM hP1.1 hKM hK hKstardef hU
          hZMσ hZcard hKNZ h)
      -- `r(O_p(M_F)) ≤ 2` (Coq `rPle2`): faithfulness `K ⊓ C_G(P) = ⊥`
      -- (`kappaHall_inf_centralizer_opiCore_eq_bot`, brick 4) + `pRank_opiCore_le_two_of_kappaHall`.
      have hpodd : Odd p :=
        hG.odd.of_dvd_nat ((Nat.dvd_of_mem_primeFactors hpπ).trans
          (Subgroup.card_subgroup_dvd_card _))
      have hKp' : ¬ p ∣ Nat.card ↥K := by
        intro hdvdK
        have hpfK : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
          exact Nat.mem_primeFactors.mpr ⟨hp, hdvdK, Nat.card_pos.ne'⟩
        exact (S14.kappa_subset_sigmaCompl (hK.primeFactors_card_subset p hpfK)) hpσ
      have hKnormP : K ≤ Subgroup.normalizer
          (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) :=
        hKM.trans (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)
          (S15.maxNilpotentNormalHall_le_normalizer M))
      have hZKstar : Z ≤ Kstar := by
        have hd : Nat.card ↥(Z ⊓ Kstar) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime hp).mp hd with h1 | hpp
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZK
        · exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
            (le_of_eq (hZcard.trans hpp.symm)))
      have hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 :=
        pRank_opiCore_le_two_of_kappaHall hG hM hp hpodd hX₁card hX₁MF hrank3 hKp' hKnormP
          (kappaHall_inf_centralizer_opiCore_eq_bot hG hM hP1 hKM hK hKstardef hU hp hX₁card hX₁MF
            hZKstar hZcard hX₁notZ)
          (hW1K ▸ hdvd)
      -- `O_p(M_F)` is non-abelian (`opiCore_singleton_not_isMulCommutative_of_witness`).
      have hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) :=
        S15.opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
      refine Or.inr (Or.inr ⟨p, hp, hHMF ▸ hpπ, ?_, ?_, hHMF ▸ hcyc⟩)
      · -- (sorry 1) `|O_p(M_F)| = p³`.  `r(P) ≤ 2` (`hrPle2`) and `P` non-abelian (`hPnab`) are in
        -- hand; the residual is the `mFT_rank2_Sylow_cprod` central-product structure (Coq §10.7b,
        -- Lean `sylow_structure_b`) once `P = O_p(M_F)` is a Sylow `p`-subgroup of `G`, together
        -- with `|Z(P)| = p` (Coq `defZP`/`oZ0`).  Isolated in `card_opiCore_eq_prime_cube_singer`.
        exact card_opiCore_eq_prime_cube_singer hG hM hP1 hmf hp hpσ hpπ hrPle2 hPnab
      · sorry

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

/-- **Prop 16.1 reverse, cyclicity ingredient for `r_q(M) = 1`** (mmd L4478): for a type-`P`
datum and a prime `q ∤ |M'|`, every elementary abelian `q`-subgroup `A` of `↥M` is cyclic.

The abelianization `↥M ⧸ M'` is cyclic — the `M_complement` field makes the cyclic factor `W₁`
(`W1_cyclic`) a complement of `M' = [M,M]` in `M`, so `↥M ⧸ M' ≃* ↥W₁`
(`IsComplement'.QuotientMulEquiv`).  Since `q ∤ |M'|` and `A` is a `q`-group, `A ⊓ M' = ⊥`
(coprime orders), so the quotient map embeds `A` into the cyclic `↥M ⧸ M'`, forcing `A` cyclic.
This is the `q`-rank-one half of `π(W₁) ⊆ κ(M)` once `q ∤ |M'|` is in hand (Hall for type V, the
`centralizer_W1` fixed-point argument for types II–IV). -/
theorem typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M))
    {A : Subgroup ↥M} (hA : A.IsElementaryAbelian q) : IsCyclic ↥A := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclic ↥data.W1 := data.W1_cyclic
  set N : Subgroup ↥M := (derivedInG M).subgroupOf M with hNdef
  -- `N = commutator ↥M`, hence normal.
  have hN_eq : N = commutator ↥M := by
    rw [hNdef, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hNnorm : N.Normal := by rw [hN_eq]; infer_instance
  -- `↥M ⧸ N ≃* ↥(W₁.subgroupOf M)` is cyclic.
  haveI : IsCyclic ↥(data.W1.subgroupOf M) := by
    have e : ↥(data.W1.subgroupOf M) ≃* ↥data.W1 := Subgroup.subgroupOfEquivOfLe data.W1_le
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have ecyc : (↥M ⧸ N) ≃* ↥(data.W1.subgroupOf M) := (data.M_complement.symm).QuotientMulEquiv
  haveI : IsCyclic (↥M ⧸ N) := isCyclic_of_surjective ecyc.symm ecyc.symm.surjective
  -- `A ⊓ N = ⊥`: `|A|` is a `q`-power and `q ∤ |N| = |M'|`.
  have hNcard : Nat.card ↥N = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA.isPGroup
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N) := by
    rw [hk, hNcard]
    exact Nat.Coprime.pow_left k ((hq.coprime_iff_not_dvd).mpr hndvd)
  have hAN : A ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  -- `A` injects into the cyclic `↥M ⧸ N`.
  set φ : ↥A →* (↥M ⧸ N) := (QuotientGroup.mk' N).comp A.subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hmem : (a : ↥M) ∈ A ⊓ N := ⟨a.2, ha⟩
    rw [hAN, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  haveI : IsCyclic ↥φ.range := inferInstance
  exact isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm
    (MonoidHom.ofInjective hφinj).symm.surjective

/-- **Prop 16.1 reverse, `r_q(M) = 1` from `q ∤ |M'|`** (mmd L4478): for a type-`P` datum and a
prime `q ∣ |W₁|` with `q ∤ |M'|`, the `q`-rank of `M` is one.  Upper bound: every elementary
abelian `q`-subgroup is cyclic (`typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived`),
so `pRank ↥M q ≤ 1`.  Lower bound: `q ∣ |W₁| ∣ |M|` gives an order-`q` element, an elementary
abelian `q`-subgroup of order `q`, so `1 ≤ pRank ↥M q`.  This is the rank-one input that
`typePData_kappa_nonempty_of_rank1` needs to place the `W₁`-primes in `κ(M)`. -/
theorem typePData_pRank_eq_one_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hqW1 : q ∣ Nat.card ↥data.W1)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M)) :
    pRank ↥M q = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ ?_
  · exact pRank_le_one_of_forall_isElementaryAbelian_isCyclic (fun A hA =>
      typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived data hq hndvd hA)
  · have hqM : q ∣ Nat.card ↥M := hqW1.trans (Subgroup.card_dvd_of_le data.W1_le)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) q hqM
    have hcard : Nat.card ↥(Subgroup.zpowers g) = q := by rw [Nat.card_zpowers, hg]
    exact pow_le_card_of_le_pRank (Subgroup.zpowers g)
      (Subgroup.IsElementaryAbelian.of_card_prime hcard) (by rw [hcard, pow_one])

/-- **Prop 16.1 reverse, type V ⟹ type `P`** (mmd L4478, clause (d) `.mp`): a structurally
type-`V` maximal subgroup is type `P` (`κ(M) ≠ ∅`).  Type `V` has `U = ⊥`, so `M' = M_F` is the
nilpotent normal Hall subgroup `maxNilpotentNormalHall M`; Hall coprimality gives `q ∤ |M'|` for
every `q ∣ |W₁| = [M : M']`, whence `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`).  Feeding this rank-one fact to
`typePData_kappa_nonempty_of_rank1` places `π(W₁) ⊆ κ(M)`, so `κ(M) ≠ ∅`.  This is the type-V
branch of the `hVP1` reverse bridge (the `IsTypeP` half) of Proposition 16.1. -/
theorem isTypeP_of_isTypeV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hV : OddOrder.GroupTheory.IsTypeV M) : S14.IsTypeP M := by
  obtain ⟨v⟩ := hV
  -- `M' = M_F` (`U = ⊥`).
  have hM'eq : derivedInG M = maxNilpotentNormalHall M := by
    rw [v.typeP.derivedInG_eq_fitting_sup_U, v.U_eq_bot, sup_bot_eq]
  have hHall := maxNilpotentNormalHall_isHall M
  refine typePData_kappa_nonempty_of_rank1 hG hM v.typeP (fun q hq => ?_)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqW1 : q ∣ Nat.card ↥v.typeP.W1 := Nat.dvd_of_mem_primeFactors hq
  have hndvd : ¬ q ∣ Nat.card ↥(derivedInG M) := by
    rw [hM'eq]
    intro hdvd
    have hqMF : q ∈ (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
    have hidx : ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card ↥v.typeP.W1 := by
      rw [← hM'eq]; exact (v.typeP.card_W1_eq_derived_index).symm
    have hqIdx : q ∈ ((maxNilpotentNormalHall M).subgroupOf M).index.primeFactors := by
      rw [hidx]; exact Nat.mem_primeFactors.mpr ⟨hqp, hqW1, Nat.card_pos.ne'⟩
    exact (hHall.2 q hqIdx) hqMF
  exact typePData_pRank_eq_one_of_not_dvd_card_derived v.typeP hqp hqW1 hndvd

/-- Conjugation action of the cyclic group `⟨x⟩` on a subgroup `N` it normalizes. -/
def conjActionOfMemNormalizer {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    ↥(Subgroup.zpowers x) →* MulAut ↥N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hx))

theorem conjActionOfMemNormalizer_apply {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (a : ↥(Subgroup.zpowers x)) (n : ↥N) :
    ((conjActionOfMemNormalizer hx a) n : G) = (a : G) * (n : G) * (a : G)⁻¹ := rfl

/-- Fixed points of the cyclic conjugation action on `N` are the elements of `N` centralizing `x`. -/
theorem fixedPoints_conjActionOfMemNormalizer_eq {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    Subgroup.fixedPointsOfMulAut (conjActionOfMemNormalizer hx) =
      (N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf N := by
  ext n
  constructor
  · intro hn
    rw [Subgroup.mem_subgroupOf]
    refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    have hfixG := congrArg Subtype.val
      (Subgroup.mem_fixedPointsOfMulAut.mp hn ⟨y, Subgroup.mem_zpowers y⟩)
    rw [conjActionOfMemNormalizer_apply] at hfixG
    calc y * (n : G) = (y * (n : G) * y⁻¹) * y := by group
      _ = (n : G) * y := by rw [hfixG]
  · intro hn
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    apply Subtype.ext
    rw [conjActionOfMemNormalizer_apply]
    have hncent : (n : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hn).2
    have hcomm : Commute (x : G) (n : G) :=
      Subgroup.mem_centralizer_iff.mp hncent x (Set.mem_singleton x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hacomm : (a : G) * (n : G) = (n : G) * (a : G) := by
      rw [← hk]; exact (hcomm.zpow_left k)
    calc (a : G) * (n : G) * (a : G)⁻¹ = (n : G) * (a : G) * (a : G)⁻¹ := by rw [hacomm]
      _ = (n : G) := by group

/-- **`p`-element fixed-point count** (`[Finite G]`): if a `q`-element `x` normalizes `N` and
`q ∣ |N|`, then `q ∣ |C_N(x)|`.  The `q`-group `⟨x⟩` acts on `N` by conjugation, so
`|N| ≡ |C_N(x)| (mod q)` (`IsPGroup.card_modEq_card_fixedPoints`, the fixed points being
`N ⊓ C(x)`); since `q ∣ |N|`, also `q ∣ |C_N(x)|`.  Used to show `q ∤ |M'|` for the type-II–IV
reverse bridges: `C_{M'}(x) = W₂` has order coprime to `q = |W₁|`. -/
theorem prime_dvd_card_inf_centralizer_of_mem_normalizer [Finite G]
    {N : Subgroup G} {x : G} {q : ℕ} [Fact q.Prime]
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hxq : IsPGroup q ↥(Subgroup.zpowers x))
    (hdvd : q ∣ Nat.card ↥N) :
    q ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  letI : MulAction ↥(Subgroup.zpowers x) ↥N :=
    MulAction.compHom ↥N (conjActionOfMemNormalizer hx)
  have hmod := hxq.card_modEq_card_fixedPoints (α := ↥N)
  -- The fixed points of the conjugation action are `N ⊓ C(x)`.
  have hcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥N)
      = Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr (Equiv.trans (Equiv.subtypeEquivRight (fun n => ?_))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        N ⊓ Subgroup.centralizer ({x} : Set G) ≤ N)).toEquiv)
    rw [← fixedPoints_conjActionOfMemNormalizer_eq hx, Subgroup.mem_fixedPointsOfMulAut]
    exact Iff.rfl
  rw [hcard] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- **`q ∤ |W₂|` for prime `|W₁| = q`** (type II–IV): `W₁` and `W₂` are subgroups of the cyclic
`W = W₁W₂` with `W₁ ⊓ W₂ = ⊥` (`W₂ ≤ M_F ≤ M'` and `W₁ ⊓ M' = ⊥` by `M_complement`).  If `q ∣ |W₂|`,
order-`q` elements `x ∈ W₁`, `y ∈ W₂` generate the *same* order-`q` subgroup of the cyclic `W`
(`cyclic_subgroup_eq_of_card_eq`), so `x ∈ ⟨y⟩ ≤ W₂`, forcing `x ∈ W₁ ⊓ W₂ = ⊥`, contra. -/
theorem typePData_not_dvd_card_W2_of_card_W1_prime [Finite G] {M : Subgroup G}
    (data : TypePData M) (hq : (Nat.card ↥data.W1).Prime) :
    ¬ (Nat.card ↥data.W1) ∣ Nat.card ↥data.W2 := by
  intro hdvd
  haveI : Fact (Nat.card ↥data.W1).Prime := ⟨hq⟩
  haveI : IsCyclic ↥data.W := data.W_cyclic
  have hW2leM' : data.W2 ≤ derivedInG M := le_trans data.W2_le (le_trans inf_le_left data.H_le)
  have hW1W2 : data.W1 ⊓ data.W2 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, data.W1_le (Subgroup.mem_inf.mp hg).1⟩ : ↥M) ∈
        ((derivedInG M).subgroupOf M) ⊓ (data.W1.subgroupOf M) :=
      ⟨Subgroup.mem_subgroupOf.mpr (hW2leM' (Subgroup.mem_inf.mp hg).2),
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hg).1⟩
    rw [disjoint_iff.mp data.M_complement.disjoint, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W2) (Nat.card ↥data.W1) hdvd
  have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
  have hyord : orderOf ((y : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W2.subtype data.W2.subtype_injective y).trans hy
  have hxne : (x : G) ≠ 1 := fun hc => hq.ne_one (by rw [← hxord, hc, orderOf_one])
  have hW1leW : data.W1 ≤ data.W := le_sup_left.trans data.W_eq.ge
  have hW2leW : data.W2 ≤ data.W := le_sup_right.trans data.W_eq.ge
  have hxW : (x : G) ∈ data.W := hW1leW x.2
  have hyW : (y : G) ∈ data.W := hW2leW y.2
  have h1 : (Subgroup.zpowers (x : G)).subgroupOf data.W
      = (Subgroup.zpowers (y : G)).subgroupOf data.W := by
    refine OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxW)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyW)).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
  have hxin : (x : G) ∈ Subgroup.zpowers (y : G) := by
    have hm : (⟨(x : G), hxW⟩ : ↥data.W) ∈ (Subgroup.zpowers (x : G)).subgroupOf data.W :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers (x : G))
    rw [h1] at hm
    exact Subgroup.mem_subgroupOf.mp hm
  have hmem : (x : G) ∈ data.W1 ⊓ data.W2 := ⟨x.2, (Subgroup.zpowers_le.mpr y.2) hxin⟩
  rw [hW1W2, Subgroup.mem_bot] at hmem
  exact hxne hmem

/-- **Prop 16.1 reverse, type II–IV ⟹ type `P`** (mmd L4478): a type-`P` datum whose cyclic
factor `W₁` has *prime* order `q = |W₁|` (the `TypePNontrivialCore` of types II/III/IV) is BG type
`P`.  `q ∤ |M'|`: else the `q`-element `x ∈ W₁#` normalizing `M'` would give `q ∣ |C_{M'}(x)| = |W₂|`
(`prime_dvd_card_inf_centralizer_of_mem_normalizer`, `centralizer_W1`), contradicting `q ∤ |W₂|`
(`typePData_not_dvd_card_W2_of_card_W1_prime`).  Then `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`) and `κ(M) ≠ ∅`
(`typePData_kappa_nonempty_of_rank1`). -/
theorem isTypeP_of_typePData_of_card_W1_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hqprime : (Nat.card ↥data.W1).Prime) : S14.IsTypeP M := by
  haveI : Fact (Nat.card ↥data.W1).Prime := ⟨hqprime⟩
  refine typePData_kappa_nonempty_of_rank1 hG hM data (fun p hp => ?_)
  have hpq : p = Nat.card ↥data.W1 := by
    rcases hqprime.eq_one_or_self_of_dvd p (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact absurd h (Nat.prime_of_mem_primeFactors hp).ne_one
    · exact h
  subst hpq
  have hndvd : ¬ Nat.card ↥data.W1 ∣ Nat.card ↥(derivedInG M) := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
    have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
      (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
    have hxne : (x : G) ≠ 1 := fun hc => hqprime.ne_one (by rw [← hxord, hc, orderOf_one])
    have hsubeq : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    haveI hnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hsubeq]; infer_instance
    have hxnorm : (x : G) ∈ Subgroup.normalizer (derivedInG M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm (data.W1_le x.2)
    have hxpg : IsPGroup (Nat.card ↥data.W1) ↥(Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
    have hdvdW2 : Nat.card ↥data.W1 ∣ Nat.card ↥data.W2 := by
      have hd := prime_dvd_card_inf_centralizer_of_mem_normalizer hxnorm hxpg hdvd
      rwa [data.centralizer_W1 (x : G) x.2 hxne] at hd
    exact typePData_not_dvd_card_W2_of_card_W1_prime data hqprime hdvdW2
  exact typePData_pRank_eq_one_of_not_dvd_card_derived data hqprime dvd_rfl hndvd

/-- **Prop 16.1 reverse, type II ⟹ type `P`** (clause (b) `.mp`, `IsTypeP` half): immediate from
`isTypeP_of_typePData_of_card_W1_prime` and the `TypePNontrivialCore` primality of `|W₁|`. -/
theorem isTypeP_of_isTypeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hII : OddOrder.GroupTheory.IsTypeII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type III ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIII : OddOrder.GroupTheory.IsTypeIII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type IV ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIV : OddOrder.GroupTheory.IsTypeIV M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIV
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, every non-type-I maximal subgroup is type `P`** (mmd L4478): the common
`IsTypeP` half of clauses (b)–(d) `.mp`.  Types II/III/IV reduce to the prime-`|W₁|` argument
(`isTypeP_of_typePData_of_card_W1_prime`); type V to the Hall argument (`isTypeP_of_isTypeV`).
This is exactly what `not_isTypeI_of_isTypeNonI` consumes (it discards the `P₁`/`P₂` refinement),
so it closes the FT-critical content of the reverse type bridges modulo `hIF` (type I ⟹ type F). -/
theorem isTypeP_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : OddOrder.GroupTheory.IsTypeNonI M) : S14.IsTypeP M := by
  rcases h with hII | hIII | hIV | hV
  · exact isTypeP_of_isTypeII hG hM hII
  · exact isTypeP_of_isTypeIII hG hM hIII
  · exact isTypeP_of_isTypeIV hG hM hIV
  · exact isTypeP_of_isTypeV hG hM hV

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

/-- **BG Theorem A(8), in full** (mmd L4274): for `M_F ≠ M_σ`, the Hall `(κ ∪ σ)ᶜ`-complement `U`
is trivial, `F(M)` is a TI-subgroup of `G`, and `|K| = p` is prime.  Combines the
`FittingIsTI`-free part (`theoremA8_complement_eq_bot_and_kappa_prime`, via Theorem 15.2) with the
`FittingIsTI` clause (`S15.fitting_isTI_of_mf_ne_msigma`, the contrapositive of the `M_F = M_σ`
conclusion of Theorem 15.7(a)).  This is the full conjunction `theoremA_maximal_structure` carries
for the `M_F ≠ M_σ` case; it is `sorry`-free modulo the single deep §15 rank-theoretic residual
`S15.piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` (Theorem 15.7(a) core). -/
theorem theoremA8_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  obtain ⟨hUbot, hKp⟩ :=
    theoremA8_complement_eq_bot_and_kappa_prime hG hM hKM hK hKstar hU hne
  exact ⟨hUbot, S15.fitting_isTI_of_mf_ne_msigma hG hM hne, hKp⟩

/-- **Type-`P₁` (`M_F ≠ M_σ`) `TypePNontrivialCore`** (the common type II--IV hypotheses of Peterfalvi
(8.6), for the type III/IV case): a `TypePData` of a type-`P₁` maximal subgroup with `M_F ≠ M_σ` and
nontrivial complement `U` satisfies `U ≠ ⊥`, `|W₁|` prime, and `M_F#` is a `TI`-subset.

The `|W₁|` primality is Theorem A(8) (`theoremA8_structure`: `M_F ≠ M_σ ⟹ |K| = p` prime, with
`|W₁| = |K| = [M:M']`); the `M_F#`-`TI` is the `FittingIsTI M` clause of A(8)
(`fitting_isTI_of_mf_ne_msigma`) read through `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`.
Discharges the `hcommon` input of the type III/IV last mile `isTypeIII_or_IV_of_typePData`, so once
the type-`P₁` `TypePData` is constructed (`exists_typeP1_mf_complement` plus the deep
nilpotency/Fitting fields) and `N_G(U) ⊆ M` is supplied, the `hP1neIIIIV` bridge closes. -/
theorem typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (data : TypePData M) (hUne : data.U ≠ ⊥) :
    TypePNontrivialCore M data := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  refine ⟨hUne, ?_, ?_⟩
  · -- `|W₁| = [M:M'] = |K| = p` prime (Theorem A(8)).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    -- The trivial `(κ ∪ σ)'`-Hall `U = ⊥` (type `P₁`: `π(M) ⊆ κ ∪ σ`).
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro p hp
      simp only [Set.mem_compl_iff, not_not]
      by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hpσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hp, hpσ⟩)
    haveI : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    obtain ⟨_, _, p, hp, hKp⟩ := theoremA8_structure hG hM hKM hK rfl hU hne
    rw [data.card_W1_eq_derived_index, ← card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK, hKp]
    exact hp
  · -- `M_F#` is `TI` (`FittingIsTI M` from `M_F ≠ M_σ`).
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM
      (S15.fitting_isTI_of_mf_ne_msigma hG hM hne)

/-- **Normalizer of a finite nilpotent subgroup is contained in the normalizer of each of its Sylow
subgroups** (the `char_norms (pcore_char p U)` step of Coq `BGsection16` `typePfacts`): for a finite
nilpotent `U ≤ G` and a Sylow `p`-subgroup `P` of `↥U`, the `G`-normalizer of `U` lies in the
`G`-normalizer of `P̄ = P.map U.subtype`.  Since `U` is nilpotent, `P` is normal — hence the *unique*
Sylow `p`-subgroup of `↥U` (`Sylow.unique_of_normal`) — so conjugation by any `g ∈ N_G(U)` (which
permutes `U`'s Sylow `p`-subgroups) fixes `P̄`.  Reusable. -/
theorem normalizer_le_normalizer_map_sylow_of_isNilpotent [Finite G] {U : Subgroup G}
    (hUnil : Group.IsNilpotent ↥U) {p : ℕ} [Fact p.Prime] (P : Sylow p ↥U) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (((P : Subgroup ↥U).map U.subtype : Subgroup G) : Set G) := by
  classical
  haveI := hUnil
  haveI hPnormal : (P : Subgroup ↥U).Normal := Ch01.Sylow.normal_of_isNilpotent P
  letI : Unique (Sylow p ↥U) := P.unique_of_normal hPnormal
  set Pbar : Subgroup G := (P : Subgroup ↥U).map U.subtype with hPbardef
  have hPbar_le_U : Pbar ≤ U := Subgroup.map_subtype_le _
  -- `|P̄|` is the full `p`-part of `|U|`.
  have hcardPbar : Nat.card ↥Pbar = p ^ (Nat.card ↥U).factorization p := by
    rw [hPbardef, Subgroup.card_map_of_injective U.subtype_injective]
    exact P.card_eq_multiplicity
  intro g hg
  have hgU : MulAut.conj g • U = U := conj_smul_eq_self_of_mem_normalizer hg
  -- `conj g • P̄ ≤ U` (since `g` normalizes `U`).
  have hconj_le_U : MulAut.conj g • Pbar ≤ U := by
    rw [pointwise_mulAut_smul_eq_map]
    calc (Pbar.map (MulAut.conj g : G →* G))
        ≤ U.map (MulAut.conj g : G →* G) := Subgroup.map_mono hPbar_le_U
      _ = MulAut.conj g • U := (pointwise_mulAut_smul_eq_map _ _).symm
      _ = U := hgU
  -- `(conj g • P̄).subgroupOf U` is a Sylow `p` of `↥U`, hence `= P` by uniqueness.
  have hcardConj : Nat.card ↥((MulAut.conj g • Pbar).subgroupOf U)
      = p ^ (Nat.card ↥U).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj_le_U).toEquiv,
      pointwise_mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcardPbar]
  set Q : Sylow p ↥U := Sylow.ofCard ((MulAut.conj g • Pbar).subgroupOf U) hcardConj with hQdef
  have hQP : (Q : Subgroup ↥U) = (P : Subgroup ↥U) := by rw [Subsingleton.elim Q P]
  have h2 : (Q : Subgroup ↥U) = (MulAut.conj g • Pbar).subgroupOf U := Sylow.coe_ofCard _ _
  -- Transport back to `G`: `conj g • P̄ = P̄`, so `g ∈ N_G(P̄)`.
  have hfix : MulAut.conj g • Pbar = Pbar := by
    have h1 : ((MulAut.conj g • Pbar).subgroupOf U).map U.subtype = MulAut.conj g • Pbar :=
      Subgroup.map_subgroupOf_eq_of_le hconj_le_U
    rw [← h1, ← h2, hQP]
  exact mem_normalizer_of_conj_smul_eq_self hfix

/-- **A prime dividing the type-`P₁` `M_F`-complement is a `σ`-prime that `U` carries fully**
(the `sMp`/`sylP` steps of Coq `BGsection16` `typePfacts`): for a type-`P₁` maximal `M` and an
`M_F`-complement `U` in `M' = M_σ` (`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), every prime `p ∣ |U|` lies in
`σ(M)` and the `p`-part of `|U|` equals the `p`-part of `|M|`.

`p ∈ σ(M)`: `p ∣ |U| ∣ |M_σ|` and `M_σ` is the `σ`-Hall (`Msigma_subgroupOf_isHall`).
`p`-parts agree: `|M| = |U| · [M:U]` and `p ∤ [M:U] = [M':U]·[M:M']`.  Here `[M':U] = |M_F|`
(`IsComplement'.index_eq_card`) and `p ∤ |M_F|` because `M_F` is a Hall subgroup of `M`
(`maxNilpotentNormalHall_isHall`) with `|U| ∣ [M:M_F]`, while `[M:M'] = [M:M_σ]` is a `σ'`-number
(`p ∈ σ`).  Hence a Sylow `p`-subgroup of `U` is a Sylow `p`-subgroup of `M`. -/
theorem typeP1_complement_mem_sigma_and_factorization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) :
    p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
      (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpU : p ∣ Nat.card ↥U := Nat.dvd_of_mem_primeFactors hp
  set M' := derivedInG M with hM'def
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hUle' : U ≤ M' := hsup ▸ le_sup_right
  have hMFle' : maxNilpotentNormalHall M ≤ M' := hsup ▸ le_sup_left
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hUM : U ≤ M := hUle'.trans hM'M
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  -- (1) `p ∈ σ(M)`: `p ∣ |U| ∣ |M'| = |M_σ|`, and `π(M_σ) ⊆ σ`.
  have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
    exact Nat.mem_primeFactors.mpr
      ⟨hpp, hpU.trans (hM'σ ▸ Subgroup.card_dvd_of_le hUle'), Nat.card_pos.ne'⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).1 p hpMσ
  refine ⟨hpσ, ?_⟩
  -- (2) `p`-parts agree.  `[M:U] = [M':U]·[M:M']`.
  have hidx_split : (U.subgroupOf M').index * (M'.subgroupOf M).index = (U.subgroupOf M).index :=
    Subgroup.relIndex_mul_relIndex U M' M hUle' hM'M
  -- `p ∤ [M':U] = |M_F|`.
  have hp_not_UM' : ¬ p ∣ (U.subgroupOf M').index := by
    rw [hDcompl.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMFle').toEquiv]
    intro hdvd
    -- `|U| ∣ [M:M_F]` (since `[M':M_F] = |U|` and `[M:M_F] = [M':M_F]·[M:M']`).
    have hMF'idx : ((maxNilpotentNormalHall M).subgroupOf M').index = Nat.card ↥U := by
      rw [hDcompl.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle').toEquiv]
    have hsplit2 : ((maxNilpotentNormalHall M).subgroupOf M').index * (M'.subgroupOf M).index
        = ((maxNilpotentNormalHall M).subgroupOf M).index :=
      Subgroup.relIndex_mul_relIndex _ M' M hMFle' hM'M
    have hUdvd : Nat.card ↥U ∣ ((maxNilpotentNormalHall M).subgroupOf M).index :=
      ⟨(M'.subgroupOf M).index, by rw [← hsplit2, hMF'idx]⟩
    have hp_idxMF : p ∈ (((maxNilpotentNormalHall M).subgroupOf M).index).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpU.trans hUdvd, Subgroup.index_ne_zero_of_finite⟩
    exact (maxNilpotentNormalHall_isHall M).2 p hp_idxMF
      (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩)
  -- `p ∤ [M:M'] = [M:M_σ]` (`σ`-Hall, `p ∈ σ`).
  have hp_not_M'M : ¬ p ∣ (M'.subgroupOf M).index := by
    intro hdvd
    refine (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).2 p ?_ hpσ
    rw [hM'σ] at hdvd
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩
  -- `p ∤ [M:U]`.
  have hp_not_UM : ¬ p ∣ (U.subgroupOf M).index := by
    rw [← hidx_split]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h1 | h2
    · exact hp_not_UM' h1
    · exact hp_not_M'M h2
  -- conclude.  `|M| = |U| · [M:U]`, `factorization p [M:U] = 0`.
  have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
    have h := Subgroup.card_mul_index (U.subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h
  rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hp_not_UM, add_zero]

/-- **Prop 16.1 forward bridge `hP1neIIIIV`, reduced to the Peterfalvi (8.7) normalizer residual** —
a type-`P₁` maximal subgroup with `M_F ≠ M_σ` is of type III or IV.

The type-`P` datum is now fully constructed (`typePData_of_isTypeP1_mf_ne_msigma`, the type III/IV
carrier-constructibility milestone, BG Corollary 15.5): the nilpotent `M_F`-complement `U ≠ ⊥` with
`F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.  The complement is built transparently here (rather than via the
opaque constructor) so that `U ≠ ⊥` (`hcommon`) and the normalizer condition are statable for the
*specific* `U`.  `isTypeIII_or_IV_of_typePData` then splits on `IsMulCommutative ↥U` (III vs IV).

The sole remaining residual is the genuinely-deep **type III/IV last mile `N_G(U) ⊆ M`** (Peterfalvi
(8.7) / Coq `BGsection15` `Fcore_structure`): this self-normalizing property of the `M_F`-complement
is exactly what distinguishes type III/IV (`normalizer_le`) from type II (`normalizer_not_le`), and
needs the BG uniqueness analysis of the complement not yet formalized. -/
theorem isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨U, hUle, hsup, hKnorm, hinf⟩ := exists_typeP1_mf_complement hG hM hP1 hKM hK
  have hUnilp : Group.IsNilpotent ↥U :=
    isNilpotent_complement_of_isTypeP1_mf_ne_msigma hG hM hP1 hne hsup hinf
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hFiteq := fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma hG hM hP1 hsup hinf
  have hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    obtain ⟨_, -, -, -, hM''F, -, -, -, -, -, -, -⟩ := S15.fitting_decomposition hG hM
    rw [← hFiteq]; exact hM''F
  -- `U ≠ ⊥`: else `M_F = M' = M_σ`, contradicting `hne`.
  have hUne : U ≠ ⊥ := by
    rintro rfl
    refine hne ?_
    have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
      isTypeP1_derivedInG_eq_Msigma hG hM hP1
    have hMF' : maxNilpotentNormalHall M = derivedInG M := by rw [← hsup, sup_bot_eq]
    rw [hM'σ] at hMF'; exact hMF'
  set data : TypePData M :=
    typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK hUle hKnorm hUnilp hDcompl hSDfit hFiteq
    with hdata
  have hdataU : data.U = U := rfl
  have hcommon : TypePNontrivialCore M data :=
    typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma hG hM hP1 hne data (hdataU ▸ hUne)
  refine isTypeIII_or_IV_of_typePData data hcommon ?_
  rw [hdataU]
  -- `N_G(U) ⊆ M` (Peterfalvi (8.7), Coq `typePfacts`): pick a prime `p ∣ |U|` and `P = Sylow_p(U)`.
  -- `N_G(U) ≤ N_G(P̄)` (`P̄` unique in the nilpotent `U`) and `P̄` is a `σ`-Sylow of `M`, so
  -- `N_G(P̄) ≤ M` (`normalizer_sylow_map_le_of_mem_sigma`).
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
  have hpπU : p ∈ (Nat.card ↥U).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hpσ, hfact⟩ :=
    typeP1_complement_mem_sigma_and_factorization hG hM hP1 hsup hinf hpπU
  have hUM : U ≤ M := hUle.trans (Subgroup.map_subtype_le _)
  have P : Sylow p ↥U := default
  have hPbarM : ((P : Subgroup ↥U).map U.subtype) ≤ M :=
    (Subgroup.map_subtype_le _).trans hUM
  have hcardPbar : Nat.card ↥(((P : Subgroup ↥U).map U.subtype).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPbarM).toEquiv,
      Subgroup.card_map_of_injective U.subtype_injective, P.card_eq_multiplicity, hfact]
  set Q : Sylow p ↥M := Sylow.ofCard (((P : Subgroup ↥U).map U.subtype).subgroupOf M) hcardPbar
    with hQdef
  refine le_trans (normalizer_le_normalizer_map_sylow_of_isNilpotent hUnilp P) ?_
  have hQmap : (Q : Subgroup ↥M).map M.subtype = (P : Subgroup ↥U).map U.subtype := by
    rw [hQdef, Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPbarM]
  have hnorm := OddOrder.BG.Ch3.S10.normalizer_sylow_map_le_of_mem_sigma hpσ Q
  rwa [hQmap] at hnorm

/-- **BG Theorem A(7), first clause — `M'' ⊆ F(M)`** (mmd L4354), as a standalone `sorry`-free
lemma for *any* maximal `M`.  No longer `M_F ≠ M_σ`-gated: Theorem 15.2's closing (issue 8012)
supplies the type-`P₁` half, so a case split on `M_F = M_σ` discharges both branches.

* `M_F = M_σ` (`M_σ` nilpotent, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`): then
  `M'' ≤ M_σ` (`derivedDerived_le_Msigma`, always true via §12 `E'` abelian) and
  `M_σ ≤ M_F ≤ F(M)` (`Msigma_le_maxNilpotentNormalHall_of_nilpotent`,
  `maxNilpotentNormalHall_le_fittingInG`);
* `M_F ≠ M_σ` (type `P₁`): the `M'' ⊆ F(M)` conjunct of Theorem 15.2
  (`mf_ne_msigma_typeP1_structure`), where `F(M) = Q C_M(Q) ⊊ M_σ` and the containment is the
  genuinely-harder chief-factor analysis (not reducible to `M'' ≤ M_σ`, since `M_σ ⊄ F(M)` here).

The second clause of A(7) (`F(M) = C_M(M_F) M_F`, and `K ≠ 1 → F(M) ⊆ M'`) is left to the gated
`fittingInAmbient_eq_*`/`theoremC_paired_structure`; only `M'' ⊆ F(M)` enters the faithful monolith
`theoremA_maximal_structure_faithful`. -/
theorem derivedDerived_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    derivedInG (derivedInG M) ≤ S15.fittingInAmbient M := by
  by_cases hne : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
  · -- `M_σ` nilpotent: `M'' ≤ M_σ ≤ M_F ≤ F(M)`.
    have hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hne
    calc derivedInG (derivedInG M)
        ≤ OddOrder.BG.Ch3.S10.Msigma M := S15.derivedDerived_le_Msigma hG hM
      _ ≤ maxNilpotentNormalHall M :=
          S15.Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil
      _ ≤ S15.fittingInAmbient M := S15.maxNilpotentNormalHall_le_fittingInG M
  · -- type `P₁`: cite the `M'' ⊆ F(M)` conjunct (16th) of Theorem 15.2.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA7, _, _, _⟩ :=
      S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar
    exact hA7

/-- **BG Theorem A — the faithful monolith** (mmd L4346-4355), all 11 conjuncts `sorry`-free.

This is the faithfulness-corrected counterpart of `theoremA_maximal_structure`: it adds the explicit
`hKM : K ≤ M` and `hUM : U ≤ M` that the BG setup `M = K U M_σ` carries but the bare Hall
conditions on `K.subgroupOf M` / `U.subgroupOf M` do not force, so conjuncts A(3) (`M = K U M_σ`),
A(4) (`C_U(k) = 1`), and A(8) (`U = 1`) become provable.  Every conjunct is discharged by a
standalone lemma — none gated:

* A(1) `M_σ` is `σ(M)`-Hall, A(2) `K` cyclic, A(3)-normal `M ≤ N(U M_σ)`, A(4) `C_U(k) = 1`,
  A(5) `K* ≠ 1` and `C_M(k) = K K*`, A(6) `M_F ≤ M_σ ≤ M'` — all from `theoremA_ungated_conjuncts`;
* A(3)-decomposition `M = K U M_σ` — `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`;
* A(7) `M'' ⊆ F(M)` — `derivedDerived_le_fittingInAmbient` (now ungated, issue 8012);
* A(8) `M_F ≠ M_σ ⟹ U = 1 ∧ F(M)` TI `∧ |K|` prime — `theoremA8_structure` (`U.subgroupOf M = ⊥`
  upgraded to `U = ⊥` via `hUM`).

The `sorry` `theoremA_maximal_structure` is kept as-is for its existing (cross-lane) callers; new
consumers wanting a proved Theorem A cite this faithful form. -/
theorem theoremA_maximal_structure_faithful [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ S15.fittingInAmbient M ∧
      (S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
        U = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p) := by
  obtain ⟨hA1, hA2, hA3n, hA4, hA5a, hA5b, hA6a, hA6b⟩ :=
    theoremA_ungated_conjuncts hG hM hKM hUM hK hKstar hU
  refine ⟨hA1, hA2, typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU,
    hA3n, hA4, hA5a, hA5b, hA6a, hA6b,
    derivedDerived_le_fittingInAmbient hG hM hKM hK hKstar, ?_⟩
  -- A(8): `theoremA8_structure` gives `U.subgroupOf M = ⊥`; lift to `U = ⊥` via `hUM`.
  intro hne
  obtain ⟨hUsub, hTI, hp⟩ := theoremA8_structure hG hM hKM hK hKstar hU hne
  refine ⟨?_, hTI, hp⟩
  have h := Subgroup.map_subgroupOf_eq_of_le hUM
  rw [hUsub, Subgroup.map_bot] at h
  exact h.symm

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

/-- **Proposition 16.1 input `hF_not_derived` / BG Theorem A(3) contrapositive** (mmd L4290): a
type-`F` maximal subgroup `M` (`κ(M) = ∅`) has **no** `(κ ∪ σ)'`-Hall `U` with `M' = U M_σ`.
For type-`F`, `M = U M_σ` for *every* such `U` (`typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` with
`K = ⊥`: the `⊥`-`κ`-Hall witness exists since `κ(M) = ∅`), so `M' = U M_σ` would force `M' = M`,
contradicting the proper derived subgroup `M' < M` of the nontrivial solvable `M`
(`IsSolvable.commutator_lt_top_of_nontrivial`).  This is the `M ∈ ℳ_𝓕 ⟹ M' ⊊ M = U M_σ` half
powering Proposition 16.1 clause (e) (`M' = U M_σ ⟺ ¬ Type I`). -/
theorem typeF_not_exists_hall_derived_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hF : S14.IsTypeF M) :
    ¬ ∃ U : Subgroup G,
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  rintro ⟨U, hUhall, hM'eq⟩
  have hkappa : S14.kappa M = ∅ := hF
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `U ≤ M' ≤ M`.
  have hUM : U ≤ M := by
    have h : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
    exact h.trans (Subgroup.map_subtype_le _)
  -- `⊥` is a `κ(M)`-Hall subgroup of `M` (type-`F`: `κ(M) = ∅`).
  have hK_bot : Ch03.IsHallSubgroup (S14.kappa M) ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hkappa]; exact Set.notMem_empty p
  -- type-`F` decomposition `M = ⊥ ⊔ U ⊔ M_σ = U ⊔ M_σ`.
  have hMeq : M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
    have h := typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM bot_le hUM hK_bot hUhall
    rwa [bot_sup_eq] at h
  -- but `M' < M` (proper derived subgroup of the nontrivial solvable `M`).
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have hlt : derivedInG M < M := by
    rw [derivedInG]
    conv_rhs => rw [← Subgroup.range_subtype M, MonoidHom.range_eq_map]
    rw [Subgroup.map_lt_map_iff_of_injective M.subtype_injective]
    exact IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M)
  exact (ne_of_lt hlt) (hM'eq.trans hMeq.symm)

/-- **Proposition 16.1 input `hP_derived` / BG Theorem C(3)** (mmd L4307): a type-`P` maximal
subgroup `M` has a `(κ ∪ σ)'`-Hall `U` with `M' = U M_σ`.  Construct a `κ(M)`-Hall `K` and a
`(κ ∪ σ)'`-Hall `U` of the solvable `M` (Hall's theorem); `K ≠ ⊥` since `M` is type-`P`
(`isTypeF_of_isHall_kappa_eq_bot` would force `κ(M) = ∅`); then `typeP_hall_derived_eq_and_abelian`
(Theorem 14.7(h) + the three-Hall partition) gives `M' = U M_σ`.  Together with
`typeF_not_exists_hall_derived_eq` this supplies both directions of Proposition 16.1 clause (e)
(`M' = U M_σ ⟺ ¬ Type I`). -/
theorem typeP_exists_hall_derived_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : S14.IsTypeP M) :
    ∃ U : Subgroup G,
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A `κ(M)`-Hall subgroup `K` of `M` (Hall's theorem in the solvable `M`).
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `K ≠ ⊥`: else `M` would be type-`F` (`κ(M) = ∅`), contradicting `IsTypeP M`.
  have hKne : K ≠ ⊥ := fun h =>
    (S14.isTypeF_iff_not_isTypeP.mp (isTypeF_of_isHall_kappa_eq_bot hKM hK h)) hP
  exact ⟨U, hU, (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1⟩

/-- **Type-`F` Frobenius FPF against a `U₀`-element** (mmd L4486, the engine of `isTypeF_of_isTypeI`,
following the Coq `BGsection16` argument): a nontrivial `X ≤ U₀` of the Frobenius complement has
trivial `M_F`-centralizer, `M_F ⊓ C_G(X) = ⊥`.  Any `M_F`-element `y` centralizing some `x ∈ X# ⊆ U₀#`
lifts to `↥(M_F ⊔ U₀)`, where `frobenius_HU0` (kernel `M_F = H`, complement `U₀`) and
`centralizer_complement_le` place it in `U₀`; then `y ∈ M_F ⊓ U₀ = ⊥` (the `complement` field with
`U₀ ≤ U`).  This is the `C_H(K) = 1` half of the BG argument, applied to a `U₀`-element `X ⊆ K` rather
than to the `κ`-Hall `K` itself (which need not lie in `H ⊔ U₀`). -/
theorem typeFData_fitting_inf_centralizer_eq_bot [Finite G]
    {M : Subgroup G} (td : OddOrder.GroupTheory.TypeFData M) {X : Subgroup G}
    (hXU0 : X ≤ td.U0) (hXne : X ≠ ⊥) :
    td.H ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  classical
  -- `M_F ⊓ U₀ = ⊥` from the complement (`U₀ ≤ U`, `M_F.subgroupOf M ⊓ U.subgroupOf M = ⊥`).
  have hHU0 : td.H ⊓ td.U0 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzH, hzU0⟩ := Subgroup.mem_inf.mp hz
    have hzM : z ∈ M := td.H_le hzH
    have hmem : (⟨z, hzM⟩ : ↥M) ∈ (td.H.subgroupOf M) ⊓ (td.U.subgroupOf M) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_subgroupOf).mpr hzH,
        (Subgroup.mem_subgroupOf).mpr (td.U0_le hzU0)⟩
    rw [td.complement.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hmem
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hXne (eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hc z hz))
  have hxU0 : x ∈ td.U0 := hXU0 hxX
  have hyHU0 : y ∈ td.H ⊔ td.U0 := Subgroup.mem_sup_left hyH
  have hxHU0 : x ∈ td.H ⊔ td.U0 := Subgroup.mem_sup_right hxU0
  -- `y` and `x` commute in `G` (`y ∈ C_G(X)`, `x ∈ X`).
  have hcomm : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hyC x hxX).symm
  -- lift to `↥(M_F ⊔ U₀)` and apply `centralizer_complement_le`.
  have hxmem : (⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0)) ∈ (td.U0).subgroupOf (td.H ⊔ td.U0) :=
    (Subgroup.mem_subgroupOf).mpr hxU0
  have hxne' : (⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0)) ≠ 1 := by
    rw [ne_eq, Subtype.ext_iff]; simpa using hxne
  have hymem : (⟨y, hyHU0⟩ : ↥(td.H ⊔ td.U0)) ∈
      Subgroup.centralizer ({(⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0))} : Set ↥(td.H ⊔ td.U0)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcomm
  have hyU0' := td.frobenius_HU0.centralizer_complement_le _ hxmem hxne' hymem
  have hyU0 : y ∈ td.U0 := (Subgroup.mem_subgroupOf).mp hyU0'
  rw [← hHU0]
  exact Subgroup.mem_inf.mpr ⟨hyH, hyU0⟩

/-- **Type-`F` `κ`-element placement** (mmd L4486, the Coq `Hall_superset` + `kappa_pi` step; the
last residual of `isTypeF_of_isTypeI`): from `p ∈ κ(M)` and the type-`F` datum, produce a nontrivial
`p`-subgroup `X ≤ U₀` (inside the Frobenius complement, where
`typeFData_fitting_inf_centralizer_eq_bot` applies) together with a `κ(M)`-Hall `K ⊇ X`.

The construction (Coq `BGsection16.v:1031`): `p ∈ κ(M) ⟹ p ∉ σ(M)` (`kappa_subset_sigmaCompl`) and
`p ∈ π(M)`, so `p ∤ |M_F|` (`M_F ⊆ M_σ`) and `p ∣ |U| = [M : M_F]`; since `exponent U₀ = exponent U`,
`p ∈ π(U₀)`, giving a Sylow `p`-subgroup `X ≤ U₀`, `X ≠ ⊥`.  Then `X` is a `κ`-group, so Hall's
theorem in the solvable `M` (`hall_E_exists` + Hall conjugacy) places it in a `κ(M)`-Hall `K`.  This
is the only residual; the rest of `isTypeF_of_isTypeI` is `sorry`-free modulo this. -/
theorem typeFData_exists_kappaElement_le_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (td : OddOrder.GroupTheory.TypeFData M)
    {p : ℕ} (hp : p ∈ S14.kappa M) :
    ∃ X K : Subgroup G, X ≤ td.U0 ∧ X ≠ ⊥ ∧ X ≤ K ∧ K ≤ M ∧
      Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨hp_prime, hp_tau, P, hP_elem, hP_le, hP_centr⟩ := hp
  haveI : Fact p.Prime := ⟨hp_prime⟩
  -- `p ∈ π(M)`: `|P| = p` and `P ≤ M`.
  obtain ⟨_, hPcard⟩ := mem_elemAbelianOfRank.mp hP_elem
  rw [pow_one] at hPcard
  have hp_dvd_M : p ∣ Nat.card ↥M := hPcard ▸ Subgroup.card_dvd_of_le hP_le
  -- `p ∉ σ(M)`.
  have hp_not_sigma : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    hp_tau.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
  -- `p ∤ |M_F|` (`M_F ≤ M_σ`, and `M_σ` is `σ`-Hall).
  have hMFMσ : td.H ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    td.H_eq ▸ maxNilpotentNormalHall_le_Msigma hG hM
  have hp_not_dvd_MF : ¬ p ∣ Nat.card ↥td.H := fun hdvd =>
    hp_not_sigma ((OddOrder.BG.Ch3.S10.Msigma_isHall hG hM).primeFactors_card_subset p
      (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd.trans (Subgroup.card_dvd_of_le hMFMσ),
        Nat.card_pos.ne'⟩))
  -- `p ∣ |U|`: `|M_F| · |U| = |M|`.
  have hcard : Nat.card ↥td.H * Nat.card ↥td.U = Nat.card ↥M := by
    have h := td.complement.card_mul
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe td.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe td.U_le).toEquiv] at h
  have hp_dvd_U : p ∣ Nat.card ↥td.U :=
    (hp_prime.dvd_mul.mp (hcard ▸ hp_dvd_M)).resolve_left hp_not_dvd_MF
  -- `p ∣ |U₀|`: a `p`-element of `U` gives `p ∣ exponent U = exponent U₀ ∣ |U₀|`.
  have hp_dvd_U0 : p ∣ Nat.card ↥td.U0 := by
    haveI : Fintype ↥td.U := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥td.U) p
      (by rwa [Nat.card_eq_fintype_card] at hp_dvd_U)
    exact (td.exponent_eq ▸ (hg ▸ Monoid.order_dvd_exponent g : p ∣ Monoid.exponent ↥td.U)).trans
      Group.exponent_dvd_nat_card
  -- A `p`-element `g ∈ U₀` generates a nontrivial `p`-subgroup `X = ⟨g⟩ ≤ U₀`.
  haveI : Fintype ↥td.U0 := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥td.U0) p
    (by rwa [Nat.card_eq_fintype_card] at hp_dvd_U0)
  have hXMle : (Subgroup.zpowers g).map td.U0.subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans (td.U0_le.trans td.U_le)
  have hXcard : Nat.card ↥((Subgroup.zpowers g).map td.U0.subtype) = p := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ td.U0.subtype_injective).symm.toEquiv,
      Nat.card_zpowers, hg]
  -- `X` is a `κ(M)`-group (`|X| = p ∈ κ`), so Hall-D places it in a `κ(M)`-Hall `K`.
  have hX_kappa :
      ∀ q ∈ (Nat.card ↥(((Subgroup.zpowers g).map td.U0.subtype).subgroupOf M)).primeFactors,
      q ∈ S14.kappa M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXMle).toEquiv, hXcard,
      hp_prime.primeFactors, Finset.mem_singleton] at hq
    rw [hq]; exact ⟨hp_prime, hp_tau, P, hP_elem, hP_le, hP_centr⟩
  obtain ⟨K', hK'_hall, hXK'⟩ := Ch03.hall_D (G := ↥M) hX_kappa
  refine ⟨(Subgroup.zpowers g).map td.U0.subtype, K'.map M.subtype,
    Subgroup.map_subtype_le _, ?_, ?_, Subgroup.map_subtype_le _, ?_⟩
  · -- `X ≠ ⊥` (`|X| = p ≠ 1`).
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    exact hp_prime.ne_one hXcard.symm
  · -- `X ≤ K'.map subtype` from `X.subgroupOf M ≤ K'`.
    rw [← Subgroup.map_subgroupOf_eq_of_le hXMle]
    exact Subgroup.map_mono hXK'
  · -- `IsHallSubgroup κ ((K'.map subtype).subgroupOf M)` reduces to `hK'_hall` on `K'`.
    show Ch03.IsHallSubgroup (S14.kappa M) ((K'.map M.subtype).comap M.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hK'_hall

/-- **Proposition 16.1(a), reverse direction — type I ⟹ type `F`** (mmd L4486): a Type I maximal
subgroup `M` has `κ(M) = ∅`.  This is the `hIF` bridge of `proposition_type_classification`, and
together with `isTypeP_of_isTypeNonI` it is everything the FT-critical `not_isTypeI_of_isTypeNonI`
consumes (it lets a non-Type-I `M` be placed in `ℳ_𝓟`, which a Type I `M` cannot also be).

**Proof** (BG L4486, by contradiction): suppose `κ(M) ≠ ∅`, witnessed by `p ∈ κ(M)`.
`typeFData_exists_kappaElement_le_kappaHall` produces a nontrivial `p`-subgroup `X ≤ U₀` and a
`κ(M)`-Hall `K ⊇ X`.  Theorem C(2) (`theoremC_paired_structure`) gives `K* = M_σ ⊓ C_G(K) ≠ ⊥` with
`K* ≤ M_F`.  But `typeFData_fitting_inf_centralizer_eq_bot` forces `M_F ⊓ C_G(X) = ⊥`, and since
`X ≤ K`, `K* ≤ C_G(K) ≤ C_G(X)` together with `K* ≤ M_F` place `K* ≤ M_F ⊓ C_G(X) = ⊥`, contradicting
`K* ≠ ⊥`. -/
theorem isTypeF_of_isTypeI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hI : OddOrder.GroupTheory.IsTypeI M) :
    S14.IsTypeF M := by
  rw [S14.isTypeF_iff_not_isTypeP]
  intro hP
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨td⟩ := hI
  obtain ⟨p, hp⟩ := hP
  -- A nontrivial `p`-subgroup `X ≤ U₀` and a `κ(M)`-Hall `K ⊇ X`.
  obtain ⟨X, K, hXU0, hXne, hXK, hKM, hK⟩ :=
    typeFData_exists_kappaElement_le_kappaHall hG hM td.typeF hp
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `K ≠ ⊥` (since `X ≠ ⊥` and `X ≤ K`).
  have hKne : K ≠ ⊥ := fun h => hXne (le_bot_iff.mp (hXK.trans h.le))
  -- Theorem C(2): `K* = M_σ ⊓ C_G(K)` is nonempty and contained in `M_F`.
  obtain ⟨_, _, hKsne, _, hKsMF, _, _, _, _, _, _, _⟩ :=
    theoremC_paired_structure hG hM hKne hKM hUM hK rfl hU
  -- The type-`F` Frobenius structure gives `M_F ⊓ C_G(X) = ⊥`; with `X ≤ K`, `K* ≤ M_F ⊓ C_G(X)`.
  have hAX := typeFData_fitting_inf_centralizer_eq_bot td.typeF hXU0 hXne
  apply hKsne
  rw [← le_bot_iff, ← hAX, td.typeF.H_eq]
  refine le_inf hKsMF (inf_le_right.trans ?_)
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  exact fun x hx => hg x (hXK hx)

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
  -- Apply the `§14`/`§15`-independent assembly engine.  The proved inputs: `hFI` =
  -- `isTypeI_of_isTypeF` (axiom-clean), `hP2II` = `isTypeII_of_isTypeP2` (axiom-clean), `hIF` =
  -- `isTypeF_of_isTypeI` (BG L4486 reverse, modulo the Frobenius FPF crux), `hP_derived` /
  -- `hF_not_derived` = Theorem C(3)/A(3), `h152a` = Theorem 15.2(a).  The 5 residual bridges
  -- (issue 8015) bottom out on the carrier `W₁`/`U`-Hall characterization (reverse `hIIP2` /
  -- `hIIIIVP1` / `hVP1`) or the type-`P₁` data construction (`hP1neIIIIV` / `hP1eqV` = Peterfalvi
  -- (8.3)/(8.8)).
  refine proposition_type_classification_of_inputs
    ?hFI (fun hP2 => isTypeII_of_isTypeP2 hG hM hP2) ?hP1neIIIIV ?hP1eqV ?hIF ?hIIP2 ?hIIIIVP1 ?hVP1
    (typeP_exists_hall_derived_eq hG hM) (typeF_not_exists_hall_derived_eq hG hM)
    (fun hne => isTypeP1_of_mf_ne_msigma hG hM hne)
  -- `hFI` (Type F ⟹ Type I): the `TypeFData` is built (`isTypeF_groupTheory_of_isTypeF`) and the
  -- `alternative` TI case is proved; only the `¬FittingIsTI` trichotomy (BG 15.7(e)) is residual.
  case hFI => exact isTypeI_of_isTypeF hG hM
  -- `hP1neIIIIV` (Type P₁, `M_F ≠ M_σ` ⟹ Type III/IV): the `TypePData` is fully constructed
  -- (`typePData_of_isTypeP1_mf_ne_msigma`, BG Cor 15.5, `U ≠ ⊥` nilpotent); the sole residual is the
  -- Peterfalvi (8.7) normalizer `N_G(U) ⊆ M` (isolated in `isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma`).
  case hP1neIIIIV => exact isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma hG hM
  -- `hP1eqV` (Type P₁, `M_F = M_σ` ⟹ Type V): the type-V `TypePData` is fully constructed
  -- (`typePData_of_isTypeP1_mf_eq_msigma`, `U = ⊥`); the sole residual is the Peterfalvi (8.8)
  -- trichotomy on `M_F` (isolated in `isTypeV_of_isTypeP1_mf_eq_msigma`).
  case hP1eqV => exact isTypeV_of_isTypeP1_mf_eq_msigma hG hM
  -- `hIF` (Type I ⟹ Type F): `isTypeF_of_isTypeI` (BG L4486 reverse direction), modulo the
  -- type-`F` Frobenius FPF crux.
  case hIF => exact isTypeF_of_isTypeI hG hM
  -- `hIIP2` (Type II ⟹ Type P₂): `π(W₁) ⊆ κ(M)` (carrier `W₁ = κ`-Hall, issue 8015).
  case hIIP2 => sorry
  -- `hIIIIVP1` (Type III/IV ⟹ Type P₁ ∧ `M_F ≠ M_σ`): `π(W₁) ⊆ κ(M)` + `M_F ≠ M_σ` (carrier).
  case hIIIIVP1 => sorry
  -- `hVP1` (Type V ⟹ Type P₁ ∧ `M_F = M_σ`): `M_F = M_σ` proved (`mf_eq_msigma_of_typePData_U_eq_bot`),
  -- but `IsTypeP1` still needs `π(W₁) ⊆ κ(M)` (carrier `W₁ = κ`-Hall, issue 8015).
  case hVP1 => sorry

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
  -- Type I forces `κ(M) = ∅` (`isTypeF_of_isTypeI`), i.e. `M ∉ ℳ_𝓟`; but every non-Type-I `M` is
  -- type `P` (`isTypeP_of_isTypeNonI`).  This routes around the other five
  -- `proposition_type_classification` bridges, leaving the FT-critical surface gated on the single
  -- `hIF` crux (`typeF_mf_inf_centralizer_kappaHall_eq_bot`).
  exact (S14.isTypeF_iff_not_isTypeP.mp (isTypeF_of_isTypeI hG hM hI))
    (isTypeP_of_isTypeNonI hG hM hNonI)

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
        obtain ⟨_, hfusion⟩ := S15.mf_hall_centralizer_control hG hM hHMσ hHall' hHne
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
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
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
            theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
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
          theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
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
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
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
  theoremII_tame_embedding_of_inputs hG hM hKM hUM hK hU hX
    -- `hPieceInv`: BG Theorem E cross-piece exclusion.
    (by sorry)
    -- `hMaxUnique`: BG §9--§10 maximal-overgroup uniqueness `|ℳ(C_G(x))| = 1`.
    (by sorry)

end OddOrder.BG.Ch4.S16
