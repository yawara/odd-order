/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
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

/-! ## Proposition 16.1: BG local taxonomy and shared Type I--V predicates -/

/-- **BG Proposition 16.1** (mmd L4352): the §14--§15 local families are exactly
the shared Type I--V maximal-subgroup predicates consumed downstream by Peterfalvi. -/
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

/-! ## Theorems I and II: the BG output consumed by Peterfalvi -/

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
          W = W1 ⊔ W2 ∧ IsCyclic ↥W ∧
          OddOrder.GroupTheory.IsTypeNonI S ∧ OddOrder.GroupTheory.IsTypeNonI T ∧
          (OddOrder.GroupTheory.IsTypeII S ∨ OddOrder.GroupTheory.IsTypeII T) ∧
          ∀ M : Subgroup G, M ∈ maximalSubgroups G →
            OddOrder.GroupTheory.IsTypeI M ∨ S14.IsConjugateSubgroup M S ∨
              S14.IsConjugateSubgroup M T) := by
  sorry

/-- **BG Theorem II** (mmd L4416): `A(M)` and `A_0(M)` are tamely embedded.  This
is the BG form of the centralizer-control input used by Peterfalvi (8.12)--(8.13). -/
theorem theoremII_tame_embedding [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  sorry

end OddOrder.BG.Ch4.S16
