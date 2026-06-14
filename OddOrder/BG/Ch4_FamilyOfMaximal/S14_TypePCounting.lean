/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem125
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
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

/-! ### Type classification: basic relations

These hold for any group purely from the definitions (no §13 input).  They record the
`M_F = ¬M_P` complementarity and the `M_P = M_P1 ⊔ M_P2` partition that §§15--16 use when
casing on the type of a maximal subgroup. -/

theorem isTypeP_of_isTypeP1 {M : Subgroup G} (h : IsTypeP1 M) : IsTypeP M := h.1

theorem isTypeP_of_isTypeP2 {M : Subgroup G} (h : IsTypeP2 M) : IsTypeP M := h.1

/-- The type-`P` maximal subgroups split as the (disjoint) union of `M_P1` and `M_P2`. -/
theorem isTypeP_iff_isTypeP1_or_isTypeP2 {M : Subgroup G} :
    IsTypeP M ↔ IsTypeP1 M ∨ IsTypeP2 M := by
  constructor
  · intro hP
    by_cases h : kappa M = sigmaComplementPrimes M
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  · rintro (h | h) <;> exact h.1

/-- `M_P1` and `M_P2` are disjoint: `kappa(M)` cannot both equal and differ from `π(M)∖σ(M)`. -/
theorem not_isTypeP1_and_isTypeP2 {M : Subgroup G} : ¬ (IsTypeP1 M ∧ IsTypeP2 M) := by
  rintro ⟨⟨_, h1⟩, _, h2⟩
  exact h2 h1

/-- `M_F` (Frobenius type) is exactly the complement of `M_P` (type `P`). -/
theorem isTypeF_iff_not_isTypeP {M : Subgroup G} : IsTypeF M ↔ ¬ IsTypeP M := by
  simp only [IsTypeF, IsTypeP, Set.not_nonempty_iff_eq_empty]

/-- A maximal subgroup is not simultaneously type `P` and Frobenius type. -/
theorem not_isTypeP_and_isTypeF {M : Subgroup G} : ¬ (IsTypeP M ∧ IsTypeF M) := by
  rintro ⟨hP, hF⟩
  exact (isTypeF_iff_not_isTypeP.mp hF) hP

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

/-- Family form of the type-`P` partition: `M_P = M_P1 ∪ M_P2`. -/
theorem maximalTypePFamily_eq_union :
    maximalTypePFamily G = maximalTypeP1Family G ∪ maximalTypeP2Family G := by
  ext M
  simp only [maximalTypePFamily, maximalTypeP1Family, maximalTypeP2Family, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · rintro ⟨hM, hP⟩
    rcases isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with h | h
    · exact Or.inl ⟨hM, h⟩
    · exact Or.inr ⟨hM, h⟩
  · rintro (⟨hM, h⟩ | ⟨hM, h⟩)
    · exact ⟨hM, isTypeP_of_isTypeP1 h⟩
    · exact ⟨hM, isTypeP_of_isTypeP2 h⟩

/-- Family form: `M_P1` and `M_P2` are disjoint. -/
theorem maximalTypeP1Family_disjoint_typeP2Family :
    Disjoint (maximalTypeP1Family G) (maximalTypeP2Family G) := by
  rw [Set.disjoint_left]
  rintro M ⟨_, h1⟩ ⟨_, h2⟩
  exact not_isTypeP1_and_isTypeP2 ⟨h1, h2⟩

/-- Family form: `M_F` is the complement of `M_P` within the maximal subgroups. -/
theorem maximalTypeFFamily_eq_diff :
    maximalTypeFFamily G = maximalSubgroups G \ maximalTypePFamily G := by
  ext M
  simp only [maximalTypeFFamily, maximalTypePFamily, Set.mem_setOf_eq, Set.mem_diff, not_and]
  constructor
  · rintro ⟨hM, hF⟩
    exact ⟨hM, fun _ => isTypeF_iff_not_isTypeP.mp hF⟩
  · rintro ⟨hM, hnP⟩
    exact ⟨hM, isTypeF_iff_not_isTypeP.mpr (hnP hM)⟩

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

/-- Subgroup conjugacy is reflexive (conjugate by `1`). -/
@[refl] theorem IsConjugateSubgroup.refl (M : Subgroup G) : IsConjugateSubgroup M M :=
  ⟨1, by rw [map_one, one_smul]⟩

/-- Subgroup conjugacy is symmetric (conjugate back by `g⁻¹`). -/
theorem IsConjugateSubgroup.symm {M N : Subgroup G} (h : IsConjugateSubgroup M N) :
    IsConjugateSubgroup N M := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

/-- Subgroup conjugacy is transitive (compose the conjugators). -/
theorem IsConjugateSubgroup.trans {M N P : Subgroup G} (h₁ : IsConjugateSubgroup M N)
    (h₂ : IsConjugateSubgroup N P) : IsConjugateSubgroup M P := by
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g', hg'⟩ := h₂
  exact ⟨g' * g, by rw [map_mul, mul_smul, hg, hg']⟩

/-- Subgroup conjugacy is an equivalence relation.  (`¬ IsConjugateSubgroup` hypotheses and the
conjugacy conclusions throughout §14 — Theorem 14.7, Lemma 14.5, Corollary 14.9 — rely on these.) -/
theorem isConjugateSubgroup_equivalence : Equivalence (IsConjugateSubgroup (G := G)) :=
  ⟨IsConjugateSubgroup.refl, IsConjugateSubgroup.symm, IsConjugateSubgroup.trans⟩

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

/-- **BG Lemma 14.1** (mmd L3811): suppose `M ∈ 𝓜` and `p ∈ π(M) - (σ(M) ∪ κ(M))`.
Let `A` be an elementary abelian `p`-subgroup of `M` of maximal rank `r_p(M)`
(realized by `A = Ω₁(S)` for `S ∈ Syl_p(M)`).  Then `|A| ≤ p²`, `C_{M_σ}(A) = 1`,
and `M_σ` is nilpotent.

BG's hypothesis `M ∉ 𝓜_{𝓟₁}` only guarantees that such a prime `p` exists; once
`p` is given (`hpπ`, `hpσ`, `hpκ`), it plays no role in the proof, so it is dropped
here.  The `A = Ω₁(S)` binding is encoded as `A ∈ ℰ_p^{r_p(M)}(M)` (the same
`Ω`-deferral used in Theorem 12.5), under which `|A| = p^{r_p(M)}`, so the
cardinality assertion `|A| ≤ p²` is the rank bound `r_p(M) ≤ 2`.

Proof: by the τ-classification `r_p(M) ∈ {1, 2}`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`
and all three assertions are Theorem 12.5(a)(d).  If `r_p(M) = 1` then
`p ∈ τ₁(M) ∪ τ₃(M)`; `C_{M_σ}(A) = 1` because `p ∉ κ(M)`, and since `A` has prime
order it then acts fixed-point-freely on `M_σ`, so `M_σ` is nilpotent by Theorem
3.7 (`isNilpotent_of_normalizing_primeOrder_fixedPointFree`). -/
theorem msigma_structure_of_notMem_sigma_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) :
    Nat.card ↥A ≤ p ^ 2 ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  have hp : p.Prime := Fact.out
  have hpM : p ∈ (Nat.card ↥M).primeFactors := hpπ
  -- Rank bounds `1 ≤ r_p(M) ≤ 2` via the §12 `E`-setup.
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hp hpM hpσ
  have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  have h2r : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
  have hcardA : Nat.card ↥A = p ^ pRank ↥M p := hA.2
  -- (1) `|A| ≤ p²` is the rank bound.
  have hbound : Nat.card ↥A ≤ p ^ 2 := by
    rw [hcardA]; exact Nat.pow_le_pow_right hp.one_le h2r
  refine ⟨hbound, ?_⟩
  have hrank12 : pRank ↥M p = 1 ∨ pRank ↥M p = 2 := by omega
  rcases hrank12 with hr1 | hr2
  · -- `r_p(M) = 1`: `p ∈ τ₁(M) ∪ τ₃(M)`, fixed-point-free action.
    have hAr1 : A ∈ elemAbelianOfRank G p 1 := by rw [← hr1]; exact hA
    have hcardp : Nat.card ↥A = p := by rw [hcardA, hr1, pow_one]
    have hpτ13 : p ∈ tau1 M ∪ tau3 M := by
      by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
      · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr1⟩)
      · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr1⟩)
    -- `C_{M_σ}(A) = 1` because `p ∉ κ(M)`.
    have hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
      by_contra hne
      exact hpκ ⟨hpτ13, A, hAr1, hAM, hne⟩
    refine ⟨hC, ?_⟩
    -- `A` is commutative, hence `A ≤ C_G(A)`.
    have hAcent : A ≤ Subgroup.centralizer (A : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hA.1.comm (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A)
      exact congrArg (Subtype.val) this
    -- Hypotheses for Theorem 3.7 (`N = M_σ`, `R = A`).
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    haveI : IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ A) :=
      solvable_of_solvable_injective
        (Subgroup.inclusion_injective (sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) hAM))
    have hAnorm : A ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      hAM.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.Msigma M) A := by
      rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ A
            ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
              inf_le_inf_left _ hAcent
        _ = ⊥ := hC
    have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    have hAne : A ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hAr1
    -- `A` acts fixed-point-freely on `M_σ`: an element fixed by `r ∈ A#` would
    -- centralize `⟨r⟩ = A` and so lie in `C_{M_σ}(A) = 1`.
    have hgen : ∀ r ∈ A, r ≠ 1 → A = Subgroup.zpowers r := by
      intro r hr hr1'
      have hle : Subgroup.zpowers r ≤ A := Subgroup.zpowers_le.mpr hr
      have hcardzp : Nat.card ↥(Subgroup.zpowers r) = p := by
        have hdvd : orderOf r ∣ p := by
          rw [← hcardp, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
        rw [Nat.card_zpowers]
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
        · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
        · exact hpp
      exact (Subgroup.eq_of_le_of_card_ge hle (hcardp.trans hcardzp.symm).le).symm
    have hFPF : ∀ r ∈ A, r ≠ 1 → ∀ n ∈ OddOrder.BG.Ch3.S10.Msigma M, n ≠ 1 →
        r * n * r⁻¹ ≠ n := by
      intro r hr hr1' n hn hn1 heq
      have hcomm : Commute r n := mul_inv_eq_iff_eq_mul.mp heq
      have hAr : A = Subgroup.zpowers r := hgen r hr hr1'
      have hncent : n ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a haA
        rw [hAr, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at haA
        obtain ⟨k, rfl⟩ := haA
        exact hcomm.zpow_left k
      have hmem : n ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
        ⟨hn, hncent⟩
      rw [hC, Subgroup.mem_bot] at hmem
      exact hn1 hmem
    exact OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      hAnorm hdisj hMσne hAne ⟨p, hp, hcardp⟩ hFPF
  · -- `r_p(M) = 2`: `p ∈ τ₂(M)`; Theorem 12.5(a),(d).
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr2⟩
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by rw [← hr2]; exact hA
    have h125 := Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 hAM
    exact ⟨h125.2.2.2.1, h125.1⟩

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
