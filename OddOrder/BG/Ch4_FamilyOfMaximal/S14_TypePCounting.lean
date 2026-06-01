/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.GroupTheory.MaximalSubgroupType

/-!
# BG §14: Maximal Subgroups of Type P and Counting

**Scope**: Bender--Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter IV §14 (pp. 105--116), mmd
`references/bg/local-analysis.mmd` L3744--4085.

This section starts BG Chapter IV.  It globalizes the prime-action analysis of
§13 by defining `kappa(M)`, the families `M_P`, `M_P1`, `M_P2`, and `M_F`, and
by introducing the sigma-decomposition / sigma-length counting framework.  Its
main outputs are the type-P duality theorem (BG 14.7) and the global bound
`ell_sigma(g) <= 2` (BG 14.10), both used by BG §§15--16 and Peterfalvi
§§10--16.

This file is intentionally a scaffold: definitions and faithful theorem surfaces
are placed now so downstream sections can import stable names.  Proofs are left
as `sorry` because they depend on the full §10--§13 local analysis and the
counting argument around the missing-page Lemma 14.6.

## Lane C interface and proof-gate notes

- BG §14 starts from Theorem 13.9: the `sigma(M)` sets partition `pi(G)`, and
  Corollary 12.16 identifies sigma-length at most one with nonempty `M_sigma(g)`.
  `SigmaDecompositionData` is explicit data so downstream files cannot assume a fake construction.
- Lemma 14.1 in BG uses `p in pi(M) \ (sigma(M) union kappa(M))`, `S in Syl_p(M)`,
  and `A = Omega_1(S)`. The Lean theorem records the clean downstream consequence for an
  ambient `A`; the exact `Omega_1(S)` binding is deferred until the subgroup-map encoding
  is settled.
- Proposition 14.2 depends on Lemma 12.1, Corollary 13.11, Theorem 13.5, Lemma
  13.12, Lemma 13.7, Lemma 13.13, Lemma 13.6, Theorem 10.1(a), Corollary
  12.16, Lemma 14.1, Theorem 3.10(a), Lemma 12.19, and Lemma 12.17 (mmd L3789-L3820).
- Theorem 14.4 gates on Theorem 13.9, Theorem 10.1(b), Proposition 12.15,
  Corollary 14.3, and Corollary 12.6(a)(b) (mmd L3837-L3861).
- Lemma 14.6 is recovered from the missing page and drives Theorem 14.7,
  Corollary 14.9, and Corollary 14.10. Its statement remains implicit in this file;
  do not replace it by Peterfalvi type assumptions.
- Theorem 14.7 is the BG source of the Type-P duality used by §§15--16; it should
  feed shared type predicates, not import Peterfalvi.
-/

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch3.S13
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Basic §14 notation: `kappa(M)`, type-P families, and sigma-length -/

/-- The set of prime divisors of a finite subgroup, used as BG's `pi(M)`. -/
def piSet (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors}

/-- BG `pi(M) - sigma(M)`, as a set of natural primes. -/
def sigmaComplementPrimes (M : Subgroup G) : Set ℕ :=
  piSet M \ OddOrder.BG.Ch3.S10.sigma M

/-- **BG `kappa(M)`** (mmd L3760): primes in `tau_1(M) ∪ tau_3(M)` for which
some rank-one elementary abelian `p`-subgroup has nontrivial centralizer in
`M_sigma`. -/
def kappa (M : Subgroup G) : Set ℕ :=
  {p | p ∈ tau1 M ∪ tau3 M ∧
    ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ M ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥}

/-- **BG `M_P`**: maximal subgroups with nonempty `kappa(M)`. -/
def IsTypeP (M : Subgroup G) : Prop :=
  (kappa M).Nonempty

/-- **BG `M_P1`**: type-P maximal subgroups with maximal `kappa(M)`. -/
def IsTypeP1 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M = sigmaComplementPrimes M

/-- **BG `M_P2`**: type-P maximal subgroups whose `kappa(M)` is a proper subset. -/
def IsTypeP2 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M ≠ sigmaComplementPrimes M

/-- **BG `M_F` family**: the Frobenius-type maximal subgroups, i.e. `kappa(M)=empty`. -/
def IsTypeF (M : Subgroup G) : Prop :=
  kappa M = ∅

/-- The family `M_P` of type-P maximal subgroups. -/
def maximalTypePFamily (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP M}

/-- The family `M_P1` of type-P1 maximal subgroups. -/
def maximalTypeP1Family (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP1 M}

/-- The family `M_P2` of type-P2 maximal subgroups. -/
def maximalTypeP2Family (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP2 M}

/-- The family `M_F` of Frobenius-type maximal subgroups. -/
def maximalTypeFFamily (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeF M}

/-- BG `M_sigma(x)`: maximal subgroups whose `M_sigma` contains the element `x`. -/
def maximalSigmaSubgroupsOfElement (x : G) : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma M}

/-- `M_tilde` in BG §14: the nonidentity part of `M_sigma`. -/
def sigmaSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)

/-- The conjugacy saturation `C_G(M_tilde)` used in the counting formulas. -/
def sigmaConjugacySaturation (M : Subgroup G) : Set G :=
  conjClassSet (sigmaSharp M)

/-- Subgroup conjugacy in the ambient group. -/
def IsConjugateSubgroup (M N : Subgroup G) : Prop :=
  ∃ g : G, MulAut.conj g • M = N

/-- `Z_tilde = Z - (K union K*)` in Theorem 14.7. -/
def zTilde (K Kstar : Subgroup G) : Set G :=
  ((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))

/-- A named carrier for the sigma-decomposition / sigma-length data of BG §14.

The actual construction comes from Theorem 13.9 and the Hall decomposition of
finite groups.  Keeping it as explicit data avoids a false placeholder
`def sigmaLength := 0` while still letting §§15--16 state their dependencies. -/
structure SigmaDecompositionData (G : Type*) [Group G] where
  length : G → ℕ
  length_one_iff : ∀ x : G,
    length x = 1 ↔ x ≠ 1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty

/-! ## Lemma 14.1 and Proposition 14.2: local structure of type-P members -/

/-- **BG Lemma 14.1** (mmd L3768): if `M` is not type `P1`, then rank-one
responses are small, `M_sigma` acts fixed-point-freely on the relevant `A`, and
`M_sigma` is nilpotent.  This is the clean scaffold form; the proof in BG uses
§13 prime action and the `E`-analysis of §12. -/
theorem not_typeP1_basic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M A : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hA : A ∈ elemAbelianOfRank G p 1) (hAM : A ≤ M) (hnot : ¬ IsTypeP1 M) :
    Nat.card ↥A ≤ p ^ 2 ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  sorry

/-- **BG Proposition 14.2** (mmd L3778): structure of a type-P maximal subgroup.

`K` is a Hall `kappa(M)`-subgroup, `Kstar = C_{M_sigma}(K)`, and `U` is the Hall
`(kappa(M) ∪ sigma(M))'`-subgroup occurring in the normal-complement statement.
The seven parts are bundled in a downstream-friendly form. -/
theorem typeP_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ Subgroup.normalizer (Kstar : Set G) ∧
      Kstar ≠ ⊥ ∧
      (∀ X : Subgroup G, X ≤ K → X ≠ ⊥ →
        Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar) ∧
      (∀ g : G, g ∉ M → Kstar ⊓ (MulAut.conj g • M) = ⊥) ∧
      (IsTypeP2 M → OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
        ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧
          IsTISubset (sigmaSharp M) (Subgroup.normalizer
            ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G))) := by
  sorry

/-- **BG Corollary 14.3** (mmd L3809): diagnostic consequences for `x ∈ M_sigma#`
and a `sigma(M)'`-element `x'`.  The conclusion records the two alternatives
used later: membership in `kappa(M)` or entry into the `tau_2(M)` branch. -/
theorem sigma_diagnostic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx' : x' ∈ M) (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}),
      p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    (∃ p ∈ kappa M, x' ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ({x} : Set G)) ∨
    (∃ p ∈ tau2 M, x' ∈ Subgroup.centralizer ({x} : Set G)) := by
  sorry

/-! ## Theorem 14.4 and Lemma 14.5: sigma-length one centralizers -/

/-- **BG Theorem 14.4** (mmd L3826): if `ell_sigma(x)=1`, then `C_G(x)` has a
normal Hall subgroup `R(x)` and a distinguished maximal subgroup `N(x)`; in the
multi-maximal case `N(x)` lies in `M_F ∪ M_P2`. -/
theorem sigmaLength_one_centralizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {x : G} (hx : x ≠ 1) (hlen : D.length x = 1) :
    (maximalSigmaSubgroupsOfElement x).Nonempty ∧
      ∃ N R : Subgroup G,
        N ∈ maximalSubgroups G ∧ R ≤ Subgroup.centralizer ({x} : Set G) ∧
        Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
          (R.subgroupOf (Subgroup.centralizer ({x} : Set G))) ∧
        (IsTypeF N ∨ IsTypeP2 N) := by
  sorry

/-- **BG Lemma 14.5** (mmd L3875): conjugacy saturations of `M_tilde` are
disjoint for nonconjugate maximal subgroups.  This is one of the counting
separation lemmas leading to Theorem 14.7 and Corollary 14.9. -/
theorem sigmaConjugacy_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hnc : ¬ IsConjugateSubgroup M N) :
    Disjoint (sigmaConjugacySaturation M) (sigmaConjugacySaturation N) := by
  sorry

/-! ## Theorem 14.7 through Lemma 14.13: type-P duality and global counting -/

/-- **BG Theorem 14.7** (mmd L3890): type-P duality and the `Z_tilde` TI-set.

For a type-P maximal subgroup `M`, there is a unique nonconjugate type-P partner
`Mstar`.  The two Hall factors `K` and `Kstar` form a cyclic subgroup `Z`,
`Z_tilde` is a TI-set, one of the two partners is type `P2`, and every type-P
maximal subgroup is conjugate to one of the pair. -/
theorem typeP_duality [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  sorry

/-- **BG Corollary 14.9** (mmd L3997): the nonidentity elements of `G` are
covered by the type-F `M_tilde` conjugacy pieces, with one extra `Z_tilde` piece
when the type-P family is nonempty. -/
theorem nonidentity_covered_by_sigma_pieces [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ x : G, x ≠ 1 → ∃ M : Subgroup G,
      M ∈ maximalSubgroups G ∧ IsTypeF M ∧ x ∈ sigmaConjugacySaturation M) ∨
    (∃ M Mstar K Kstar : Subgroup G,
      M ∈ maximalSubgroups G ∧ Mstar ∈ maximalSubgroups G ∧
      IsTypeP M ∧ IsTypeP Mstar ∧
      ∀ x : G, x ≠ 1 →
        x ∈ conjClassSet (zTilde K Kstar) ∨
        ∃ H : Subgroup G,
          H ∈ maximalSubgroups G ∧ IsTypeF H ∧ x ∈ sigmaConjugacySaturation H) := by
  sorry

/-- **BG Corollary 14.10** (mmd L4008): global sigma-length bound. -/
theorem exists_sigmaDecomposition_length_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ D : SigmaDecompositionData G, ∀ g : G, D.length g ≤ 2 := by
  sorry

/-- **BG Corollary 14.12** (mmd L4035): if `M` is type `P2`, then the maximal
subgroup attached to a Sylow subgroup of the `U`-factor lies in the Frobenius
family `M_F`, and intersections with the type-P dual pair have the prescribed
shape.  The exact Sylow-`r` and dual-pair data are deferred, but the intersection
uses the BG `U K` factor rather than the chosen subgroup `R ≤ U`. -/
theorem typeP2_neighbor_is_typeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hUle : U ≤ M) (hRle : R ≤ U) (hRne : R ≠ ⊥) :
    ∃ H : Subgroup G,
      H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) ∧
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K := by
  sorry

/-- **BG Lemma 14.13** (mmd L4059): extension of Theorem 14.4.  In the specified
multi-maximal sigma-length-one situation, `M` is Frobenius type, `tau_2(M)` is
empty, and `M` is a Frobenius group with kernel `M_sigma`. -/
theorem sigmaLength_one_frobenius_type [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {x : G} (hx : x ≠ 1) (hlen : D.length x = 1)
    {M N : Subgroup G} (hM : M ∈ maximalSigmaSubgroupsOfElement x)
    (hN : N ∈ maximalSigmaSubgroupsOfElement x)
    (hMN : ¬ IsConjugateSubgroup M N)
    (hinter : (OddOrder.BG.Ch3.S10.sigma N ∩ piSet M).Nonempty) :
    IsTypeF M ∧ tau2 M = ∅ ∧
      ∃ U : Subgroup G,
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
          (U.subgroupOf M) ∧
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) := by
  sorry

end OddOrder.BG.Ch4.S14
