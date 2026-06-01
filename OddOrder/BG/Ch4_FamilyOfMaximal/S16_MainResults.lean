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

/-- BG Theorem E notation: `A(M) = hat M_sigma ∩ U M_sigma`. -/
def ASet (M U : Subgroup G) : Set G :=
  hatMsigma M ∩ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)

/-- BG Theorem E notation: `A_0(M) = hat M_sigma - C_M(K#)`, represented as the
part of `hat M_sigma` outside the `M`-conjugacy saturation of `K#`. -/
def A0Set (M K : Subgroup G) : Set G :=
  hatMsigma M \ conjClassSet (sharpSubgroup K)

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
      U ⊔ OddOrder.BG.Ch3.S10.Msigma M ≤
        Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
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
      Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ S15.MF M ∧
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

/-- **BG Theorem D** (mmd L4317): conjugacy and centralizer control for
`M_sigma`, including the `R(x)` subgroup and the unique maximal subgroup attached
to escaping centralizers. -/
theorem theoremD_msigma_conjugacy_and_centralizers [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      (∀ g : G, g ∉ M → IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj g • M))) ∧
      (∀ x : G, x ∈ sigmaSharp M →
        ∃ R : Subgroup G,
          R ≤ Subgroup.centralizer ({x} : Set G) ∧
          Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
            (R.subgroupOf (Subgroup.centralizer ({x} : Set G)))) ∧
      (∀ x : G, x ∈ sigmaSharp M → ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∃! N : Subgroup G,
          N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
          S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
          x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
          (S14.IsTypeF N ∨ S14.IsTypeP2 N)) := by
  sorry

/-- **BG Theorem E** (mmd L4285): the auxiliary sets from this section have the
TI and support properties used in Peterfalvi's `A(M)`/`A_0(M)` arguments. -/
theorem theoremE_A_sets [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
      IsTISubset (A0Set M K \ ASet M U) M ∧
      Supports (ASet M U) (S14.zTilde K Kstar ∪ A0Set M K) := by
  sorry

/-! ## Proposition 16.1: BG local taxonomy equals Peterfalvi type I--V -/

/-- **BG Proposition 16.1** (mmd L4352): the §14--§15 local families are exactly
Peterfalvi's Type I--V maximal subgroups. -/
theorem proposition_type_classification [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (OddOrder.GroupTheory.IsTypeI M ↔ S14.IsTypeF M) ∧
      (OddOrder.GroupTheory.IsTypeII M ↔ S14.IsTypeP2 M) ∧
      ((OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) ↔
        S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) ∧
      (OddOrder.GroupTheory.IsTypeV M ↔
        S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) ∧
      (derivedInG M =
        (⊤ : Subgroup G) ⊔ OddOrder.BG.Ch3.S10.Msigma M ↔
          ¬ OddOrder.GroupTheory.IsTypeI M) ∧
      (S15.MF M = OddOrder.BG.Ch3.S10.Msigma M ↔
        OddOrder.GroupTheory.IsTypeI M ∨ OddOrder.GroupTheory.IsTypeII M ∨
          OddOrder.GroupTheory.IsTypeV M) := by
  sorry

/-! ## Theorems I and II: the BG output consumed by Peterfalvi -/

/-- **BG Theorem I** (mmd L4402): nilpotent Hall conjugacy and the global maximal
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
      D ⊆ X ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  sorry

end OddOrder.BG.Ch4.S16
